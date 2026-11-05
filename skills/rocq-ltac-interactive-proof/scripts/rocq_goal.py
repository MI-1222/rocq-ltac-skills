#!/usr/bin/env python3
"""rocq_goal.py - Zero-dependency interactive proof state extractor and REPL controller.

Provides sentence-level lexing, stateless/stateful subshell execution (rocq top / coqtop),
goal and hypothesis parsing, inline Vernacular query execution, and soundness cheat detection.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
from dataclasses import dataclass
from enum import Enum, auto
from pathlib import Path
from typing import Any


class LexerState(Enum):
    """Lexer internal state tracking."""

    CODE = auto()
    STRING = auto()
    COMMENT = auto()


@dataclass
class Sentence:
    """Represents a single parsed sentence or tactic unit in Rocq/Coq."""

    text: str
    start_pos: int
    end_pos: int
    line_number: int
    is_bullet_or_brace: bool
    contains_admit: bool


class RocqLexer:
    """Robust lexer state machine for Rocq/Coq source code."""

    BULLET_REGEX = re.compile(r"^(\++|\-+|\*+)(?=\s|$)")

    @classmethod
    def split_sentences(cls, code: str) -> list[Sentence]:
        """Split source code into individual sentences respecting comments and strings."""
        sentences: list[Sentence] = []
        n = len(code)
        i = 0
        state = LexerState.CODE
        comment_depth = 0
        current_start = 0
        current_line = 1
        start_line = 1

        while i < n:
            char = code[i]
            next_char = code[i + 1] if i + 1 < n else ""

            if char == "\n":
                current_line += 1

            if state == LexerState.CODE:
                # Check for comment opening: (*
                if char == "(" and next_char == "*":
                    state = LexerState.COMMENT
                    comment_depth = 1
                    i += 2
                    continue

                # Check for string literal opening: "
                if char == '"':
                    state = LexerState.STRING
                    i += 1
                    continue

                # Check for single-character braces { or }
                if char in ("{", "}"):
                    prefix = code[current_start:i].strip()
                    if not prefix:
                        sent_text = char
                        sentences.append(
                            Sentence(
                                text=sent_text,
                                start_pos=i,
                                end_pos=i + 1,
                                line_number=current_line,
                                is_bullet_or_brace=True,
                                contains_admit=False,
                            )
                        )
                        i += 1
                        current_start = i
                        start_line = current_line
                        continue

                # Check for bullets (+, -, *) at word boundary
                remaining = code[i:]
                bullet_match = cls.BULLET_REGEX.match(remaining)
                if bullet_match and (i == 0 or code[i - 1].isspace()):
                    prefix = code[current_start:i].strip()
                    if not prefix:
                        b_str = bullet_match.group(1)
                        sentences.append(
                            Sentence(
                                text=b_str,
                                start_pos=i,
                                end_pos=i + len(b_str),
                                line_number=current_line,
                                is_bullet_or_brace=True,
                                contains_admit=False,
                            )
                        )
                        i += len(b_str)
                        current_start = i
                        start_line = current_line
                        continue

                # Check for terminating period followed by space, newline, EOF, or comment
                if char == ".":
                    is_term = False
                    if (
                        i + 1 == n
                        or code[i + 1].isspace()
                        or code[i + 1 : i + 3] == "(*"
                    ):
                        is_term = True

                    if is_term:
                        sent_text = code[current_start : i + 1].strip()
                        if sent_text:
                            has_admit = bool(
                                re.search(r"\b(admit|Admitted|give_up)\b", sent_text)
                            )
                            sentences.append(
                                Sentence(
                                    text=sent_text,
                                    start_pos=current_start,
                                    end_pos=i + 1,
                                    line_number=start_line,
                                    is_bullet_or_brace=False,
                                    contains_admit=has_admit,
                                )
                            )
                        i += 1
                        current_start = i
                        start_line = current_line
                        continue

            elif state == LexerState.STRING:
                if char == '"':
                    if next_char == '"':
                        # Escaped quote inside string
                        i += 2
                        continue
                    state = LexerState.CODE

            elif state == LexerState.COMMENT:
                if char == "(" and next_char == "*":
                    comment_depth += 1
                    i += 2
                    continue
                if char == "*" and next_char == ")":
                    comment_depth -= 1
                    if comment_depth == 0:
                        state = LexerState.CODE
                    i += 2
                    continue

            i += 1

        remaining_text = code[current_start:].strip()
        if remaining_text:
            has_admit = bool(re.search(r"\b(admit|Admitted|give_up)\b", remaining_text))
            sentences.append(
                Sentence(
                    text=remaining_text,
                    start_pos=current_start,
                    end_pos=n,
                    line_number=start_line,
                    is_bullet_or_brace=False,
                    contains_admit=has_admit,
                )
            )

        return sentences


def find_project_root_and_flags(
    start_path: Path | None = None,
) -> tuple[Path | None, list[str]]:
    """Traverse upward to find _RocqProject or _CoqProject and extract binding flags."""
    cur = (start_path or Path.cwd()).resolve()
    if cur.is_file():
        cur = cur.parent

    root = cur
    project_file: Path | None = None

    for p in [cur, *cur.parents]:
        rocq_proj = p / "_RocqProject"
        coq_proj = p / "_CoqProject"
        if rocq_proj.is_file():
            project_file = rocq_proj
            root = p
            break
        if coq_proj.is_file():
            project_file = coq_proj
            root = p
            break

    if not project_file:
        return None, []

    flags: list[str] = []
    try:
        content = project_file.read_text(encoding="utf-8")
        for line in content.splitlines():
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            tokens = shlex.split(line, comments=True)
            idx = 0
            while idx < len(tokens):
                tok = tokens[idx]
                if tok in ("-Q", "-R"):
                    if idx + 2 < len(tokens):
                        phys = str((root / tokens[idx + 1]).resolve())
                        logic = tokens[idx + 2]
                        flags.extend([tok, phys, logic])
                        idx += 3
                    else:
                        idx += 1
                elif tok == "-I":
                    if idx + 1 < len(tokens):
                        phys = str((root / tokens[idx + 1]).resolve())
                        flags.extend(["-I", phys])
                        idx += 2
                    else:
                        idx += 1
                elif tok == "-arg":
                    if idx + 1 < len(tokens):
                        flags.extend(shlex.split(tokens[idx + 1]))
                        idx += 2
                    else:
                        idx += 1
                else:
                    idx += 1
    except OSError:
        pass

    return root, flags


class RocqExecutor:
    """Subprocess runner for rocq top / rocq repl / coqtop."""

    def __init__(
        self,
        bin_path: str | None = None,
        extra_args: list[str] | None = None,
        cwd: Path | None = None,
    ):
        self.bin_path = bin_path or self._resolve_binary()
        self.extra_args = extra_args or []
        self.cwd = cwd or Path.cwd()

    def _resolve_binary(self) -> str:
        """Resolve available binary path preferring rocq over coqtop."""
        for candidate in ("rocq", "coqtop"):
            path = shutil.which(candidate)
            if path:
                return path
        return "rocq"

    def run_stateless(
        self, script_sentences: list[str], timeout: int = 15
    ) -> tuple[int, str, str]:
        """Execute a batch of sentences in a fresh subshell and capture stdout/stderr."""
        cmd: list[str]
        bin_name = Path(self.bin_path).name.lower()

        if "rocq" in bin_name:
            cmd = [self.bin_path, "top", "-q", "-color", "no", *self.extra_args]
        else:
            cmd = [self.bin_path, "-q", "-color", "no", *self.extra_args]

        env = os.environ.copy()
        env["TERM"] = "dumb"
        env["COQ_COLORS"] = "no"

        input_data = "\n".join(script_sentences) + "\n"

        proc = subprocess.Popen(
            cmd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            cwd=str(self.cwd),
            env=env,
        )

        try:
            stdout, stderr = proc.communicate(input=input_data, timeout=timeout)
            return proc.returncode, stdout, stderr
        except subprocess.TimeoutExpired:
            proc.kill()
            stdout, stderr = proc.communicate()
            return -1, stdout, f"Timeout expired after {timeout} seconds."


class ProofStateParser:
    """Parses terminal output into structured proof goals, hypotheses, and errors."""

    RE_GOAL_SEP = re.compile(r"^\s*={10,}\s*$", re.MULTILINE)
    RE_SUBGOAL_COUNT = re.compile(r"(\d+)\s+(?:sub)?goals?", re.IGNORECASE)
    RE_ERROR = re.compile(
        r"^(Error:|Syntax error:|User error:)(.*)", re.MULTILINE | re.DOTALL
    )
    RE_EVAR = re.compile(
        r"(uninstantiated existential variables|has been shelved|shelved)",
        re.IGNORECASE,
    )

    @classmethod
    def parse_goals(cls, output: str) -> dict[str, Any]:
        """Extract structured proof state from raw terminal text."""
        result: dict[str, Any] = {
            "is_done": False,
            "has_error": False,
            "error_message": None,
            "subgoal_count": 0,
            "hypotheses": [],
            "target": None,
            "has_evar_warning": False,
            "raw_state": "",
        }

        err_match = cls.RE_ERROR.search(output)
        if err_match:
            result["has_error"] = True
            result["error_message"] = err_match.group(0).strip()
            result["raw_state"] = output.strip()
            return result

        if (
            "No more goals." in output
            or "No more subgoals." in output
            or "Proof completed." in output
        ):
            result["is_done"] = True
            result["subgoal_count"] = 0
            result["raw_state"] = output.strip()
            return result

        if cls.RE_EVAR.search(output):
            result["has_evar_warning"] = True

        # Match the last occurrence of subgoal/goal count
        count_matches = list(cls.RE_SUBGOAL_COUNT.finditer(output))
        if count_matches:
            result["subgoal_count"] = int(count_matches[-1].group(1))
        elif "1 subgoal" in output.lower() or "1 goal" in output.lower():
            result["subgoal_count"] = 1

        parts = cls.RE_GOAL_SEP.split(output)
        if len(parts) >= 2:
            pre_context = parts[-2]
            post_context = parts[-1]

            # Find starting index after "N goal(s)" or "N subgoal(s)" if present
            raw_pre_lines = pre_context.strip().splitlines()
            start_idx = 0
            for idx, line in enumerate(raw_pre_lines):
                if re.search(r"\b\d+\s+(?:sub)?goals?\b", line, re.IGNORECASE):
                    start_idx = idx + 1

            hypo_lines: list[str] = []
            for line in raw_pre_lines[start_idx:]:
                line_str = line.strip()
                if not line_str:
                    continue
                if line_str.endswith("<") or line_str.startswith(("Coq <", "Rocq <")):
                    continue
                if line_str.startswith(
                    ("[Loading ML", "Welcome to", "Skipping rcfile")
                ):
                    continue
                if re.search(r"^\S+\s+is (defined|assumed)\b", line_str):
                    continue
                if "subgoal" in line_str.lower() and "is:" not in line_str:
                    continue
                hypo_lines.append(line_str)
            result["hypotheses"] = hypo_lines

            target_lines: list[str] = []
            for line in post_context.strip().splitlines():
                line_str = line.strip()
                if not line_str:
                    continue
                if line_str.endswith("<") or line_str.startswith(("Coq <", "Rocq <")):
                    break
                if re.match(r"^(?:sub)?goal \d+ is:", line_str, re.IGNORECASE):
                    break
                if (
                    "no more goals" in line_str.lower()
                    or "there are some goals you gave up" in line_str.lower()
                ):
                    break
                target_lines.append(line_str)
            result["target"] = "\n".join(target_lines).strip()

        result["raw_state"] = output.strip()
        return result

    @classmethod
    def parse_search_results(
        cls, output: str, max_results: int = 30
    ) -> list[dict[str, str]]:
        """Parse Vernacular Search query outputs into identifier-statement pairs."""
        results: list[dict[str, str]] = []
        current_ident: str | None = None
        current_stmt: list[str] = []

        # Find where Search output starts (after Rocq < Search ...)
        lines = output.splitlines()
        in_search = False

        for line in lines:
            line_str = line.strip()
            if not line_str:
                continue

            if not in_search:
                if re.search(r"(?:Rocq|Coq)\s*<\s*Search\b", line):
                    in_search = True
                continue

            # Check for return to prompt
            if re.match(r"^[a-zA-Z0-9_\-\'\.]*\s*<\s*$", line_str):
                break

            if line_str.startswith(("Error:", "Syntax error:")):
                continue

            # New lemma identifier typically starts at column 0 or has format "ident: stmt"
            ident_match = re.match(r"^([a-zA-Z0-9_\'\.]+)\s*:\s*(.*)$", line_str)
            if ident_match:
                if current_ident:
                    results.append(
                        {
                            "identifier": current_ident,
                            "statement": " ".join(current_stmt).strip(),
                        }
                    )
                    if len(results) >= max_results:
                        current_ident = None
                        break
                current_ident = ident_match.group(1).strip()
                stmt_part = ident_match.group(2).strip()
                current_stmt = [stmt_part] if stmt_part else []
            elif current_ident:
                # Continuation of multiline statement
                current_stmt.append(line_str)

        if current_ident and len(results) < max_results:
            results.append(
                {
                    "identifier": current_ident,
                    "statement": " ".join(current_stmt).strip(),
                }
            )

        # Fallback if no Search marker was detected but search lines exist
        if not results:
            for line in lines:
                line_str = line.strip()
                if (
                    not line_str
                    or line_str.endswith("<")
                    or line_str.startswith(("Coq <", "Rocq <"))
                ):
                    continue
                if line_str.startswith(("Error:", "Syntax error:", "[Loading ML")):
                    continue
                m = re.match(r"^([a-zA-Z0-9_\'\.]+)\s*:\s*(.+)$", line_str)
                if m:
                    results.append(
                        {
                            "identifier": m.group(1).strip(),
                            "statement": m.group(2).strip(),
                        }
                    )
                    if len(results) >= max_results:
                        break

        return results


def main() -> None:
    """CLI entry point for rocq_goal.py."""
    parser = argparse.ArgumentParser(
        description="Rocq/Coq Interactive Proof State Extractor & Vernacular Search"
    )
    parser.add_argument("--file", type=str, help="Source .v file to evaluate")
    parser.add_argument("--code", type=str, help="Raw Rocq code passed inline")
    parser.add_argument(
        "--line",
        type=int,
        help="Target line number (1-indexed). Evaluates code up to this line.",
    )
    parser.add_argument(
        "--search",
        type=str,
        help="Inline Vernacular Search query to evaluate at target state.",
    )
    parser.add_argument(
        "--max-search",
        type=int,
        default=25,
        help="Maximum search results to return (default: 25).",
    )
    parser.add_argument(
        "--project-dir",
        type=str,
        help="Project root directory containing _CoqProject or _RocqProject.",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=15,
        help="Subprocess timeout in seconds (default: 15).",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output structured JSON response.",
    )

    args = parser.parse_args()

    source_code = ""
    file_path: Path | None = None

    if args.file:
        file_path = Path(args.file).resolve()
        try:
            source_code = file_path.read_text(encoding="utf-8")
        except OSError as e:
            err_dict = {
                "is_done": False,
                "has_error": True,
                "error_message": f"Cannot read source file '{args.file}': {e}",
                "subgoal_count": 0,
                "hypotheses": [],
            }
            if args.json:
                print(json.dumps(err_dict, indent=2))
            else:
                print(f"[ERROR] {err_dict['error_message']}", file=sys.stderr)
            sys.exit(1)
    elif args.code:
        source_code = args.code
    else:
        source_code = sys.stdin.read()

    # Discover project root and flags
    start_dir = (
        Path(args.project_dir).resolve()
        if args.project_dir
        else (file_path.parent if file_path else Path.cwd())
    )
    root_dir, project_flags = find_project_root_and_flags(start_dir)
    effective_cwd = root_dir or start_dir

    sentences = RocqLexer.split_sentences(source_code)
    eval_sentences: list[Sentence] = []
    has_tainted_admit = False

    for s in sentences:
        if args.line and s.line_number > args.line:
            break
        eval_sentences.append(s)
        if s.contains_admit:
            has_tainted_admit = True

    command_texts = [s.text for s in eval_sentences]

    if args.search:
        clean_search = args.search.strip()
        if not clean_search.endswith("."):
            clean_search += "."
        # If user did not prefix with Search / Locate / About / Check, default to Search
        if not re.match(r"^(Search|Locate|About|Check|Print)\b", clean_search):
            clean_search = f"Search {clean_search}"
        command_texts.append(clean_search)

    executor = RocqExecutor(extra_args=project_flags, cwd=effective_cwd)
    exit_code, stdout, stderr = executor.run_stateless(
        command_texts, timeout=args.timeout
    )

    state_res = ProofStateParser.parse_goals(stdout)
    if exit_code != 0 and not state_res["has_error"]:
        state_res["has_error"] = True
        state_res["error_message"] = stderr.strip() or stdout.strip()

    # Soundness guard: if admitted tokens exist in evaluated prefix, reject completion
    if has_tainted_admit:
        if state_res["is_done"]:
            state_res["is_done"] = False
        state_res["soundness_violation"] = (
            "Detected 'admit', 'Admitted', or 'give_up' in executed proof prefix. "
            "Proof cannot be certified complete."
        )

    if args.search:
        state_res["search_results"] = ProofStateParser.parse_search_results(
            stdout, max_results=args.max_search
        )

    if args.json:
        print(json.dumps(state_res, indent=2, ensure_ascii=False))
    else:
        if state_res.get("soundness_violation"):
            print(
                f"[SOUNDNESS VIOLATION] {state_res['soundness_violation']}",
                file=sys.stderr,
            )
        if state_res["has_error"]:
            print(f"[ERROR] {state_res['error_message']}")
        elif state_res["is_done"]:
            print("[SUCCESS] Proof complete (No more goals).")
        else:
            print(f"Subgoals remaining: {state_res['subgoal_count']}")
            if state_res.get("has_evar_warning"):
                print("[WARNING] Existential variables / shelved goals detected!")
            print("--- Hypotheses ---")
            for h in state_res["hypotheses"]:
                print(f"  {h}")
            print("--- Target ---")
            print(f"  {state_res['target']}")
            if args.search and "search_results" in state_res:
                print(f"--- Search Results ({len(state_res['search_results'])}) ---")
                for r in state_res["search_results"]:
                    print(f"  {r['identifier']} : {r['statement']}")


if __name__ == "__main__":
    main()
