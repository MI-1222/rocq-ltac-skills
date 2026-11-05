#!/usr/bin/env python3
"""rocq_goal.py - Zero-dependency interactive proof state extractor and REPL controller.

Provides sentence-level lexing, stateless subshell execution (rocq top / coqtop),
goal and hypothesis parsing with multiline normalization, inline Vernacular query
execution with native output limits, and soundness cheat detection.
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
    """Robust lexer state machine for Rocq 9.0+ syntax."""

    BULLET_CHARS = ("-", "+", "*")

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
                # Comment opening: (*
                if char == "(" and next_char == "*":
                    state = LexerState.COMMENT
                    comment_depth = 1
                    i += 2
                    continue

                # String literal opening: "
                if char == '"':
                    state = LexerState.STRING
                    i += 1
                    continue

                # Single-character braces { or } as standalone vernacular statements
                if char in ("{", "}"):
                    prefix = code[current_start:i].strip()
                    if not prefix:
                        sentences.append(
                            Sentence(
                                text=char,
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

                # Bullet sequences (-, +, *) as standalone vernacular statements
                if char in cls.BULLET_CHARS:
                    prefix = code[current_start:i].strip()
                    if not prefix:
                        b_char = char
                        bullet_end = i
                        while bullet_end < n and code[bullet_end] == b_char:
                            bullet_end += 1
                        b_str = code[i:bullet_end]
                        sentences.append(
                            Sentence(
                                text=b_str,
                                start_pos=i,
                                end_pos=bullet_end,
                                line_number=current_line,
                                is_bullet_or_brace=True,
                                contains_admit=False,
                            )
                        )
                        i = bullet_end
                        current_start = i
                        start_line = current_line
                        continue

                # Terminating period: must be followed by whitespace, EOF, or comment start
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
                        # Escaped quote inside string literal ("")
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

    # Rocq defines the goal separator bar as exactly 28 equals signs
    RE_GOAL_SEP = re.compile(r"^\s*={28}\s*$", re.MULTILINE)
    RE_GOAL_SEP_FALLBACK = re.compile(r"^\s*={10,}\s*$", re.MULTILINE)

    # Standard header format: "No more goals." or "N goals"
    RE_SUBGOAL_COUNT = re.compile(r"(\d+)\s+(?:sub)?goals?", re.IGNORECASE)
    RE_BG_GOAL = re.compile(
        r"^(?:sub)?goal\s+(\d+)\s+is:", re.MULTILINE | re.IGNORECASE
    )

    # Error prefixes routed to stderr or echoed in stdout
    RE_ERROR = re.compile(
        r"^(Error:|Syntax error:|User error:)(.*)", re.MULTILINE | re.DOTALL
    )

    # Special warnings and uninstantiated evars
    RE_EVAR = re.compile(
        r"(dependent evars:|uninstantiated existential variables)", re.IGNORECASE
    )
    RE_SHELVED = re.compile(r"\(shelved:\s*(\d+)\)", re.IGNORECASE)
    RE_GIVEN_UP = re.compile(r"there are some goals you gave up", re.IGNORECASE)

    # Prompt line matching toplevel or proofmode prompts
    RE_PROMPT = re.compile(
        r"^(?:Rocq|Coq|[A-Za-z_][A-Za-z0-9_']*(?:\s+\(focused\))?)\s*<\s*",
        re.MULTILINE,
    )

    @classmethod
    def parse_goals(cls, stdout_output: str, stderr_output: str = "") -> dict[str, Any]:
        """Extract structured proof state from raw terminal text."""
        result: dict[str, Any] = {
            "is_done": False,
            "has_error": False,
            "error_message": None,
            "subgoal_count": 0,
            "background_goals": [],
            "hypotheses": [],
            "target": None,
            "has_evar_warning": False,
            "shelved_count": 0,
            "has_given_up_warning": False,
            "raw_state": "",
        }

        # Check stderr and stdout for errors
        combined_output = f"{stdout_output}\n{stderr_output}".strip()
        err_match = cls.RE_ERROR.search(stderr_output) or cls.RE_ERROR.search(
            stdout_output
        )
        if err_match:
            result["has_error"] = True
            result["error_message"] = err_match.group(0).strip()
            result["raw_state"] = combined_output
            return result

        if (
            "No more goals." in stdout_output
            or "No more subgoals." in stdout_output
            or "Proof completed." in stdout_output
        ):
            result["is_done"] = True
            result["subgoal_count"] = 0
            result["raw_state"] = combined_output
            return result

        # Check for Evars and shelved goals
        if cls.RE_EVAR.search(stdout_output) or cls.RE_EVAR.search(stderr_output):
            result["has_evar_warning"] = True

        shelved_match = cls.RE_SHELVED.search(stdout_output)
        if shelved_match:
            result["shelved_count"] = int(shelved_match.group(1))

        if cls.RE_GIVEN_UP.search(stdout_output):
            result["has_given_up_warning"] = True

        # Extract latest subgoal count
        count_matches = list(cls.RE_SUBGOAL_COUNT.finditer(stdout_output))
        if count_matches:
            result["subgoal_count"] = int(count_matches[-1].group(1))
        elif "1 subgoal" in stdout_output.lower() or "1 goal" in stdout_output.lower():
            result["subgoal_count"] = 1

        # Extract background goals (e.g. goal 2 is:, goal 3 is:)
        bg_matches = list(cls.RE_BG_GOAL.finditer(stdout_output))
        result["background_goals"] = [int(m.group(1)) for m in bg_matches]

        # Locate goal separator line (28 equals signs or fallback)
        sep_matches = list(cls.RE_GOAL_SEP.finditer(stdout_output))
        if not sep_matches:
            sep_matches = list(cls.RE_GOAL_SEP_FALLBACK.finditer(stdout_output))

        if sep_matches:
            last_sep = sep_matches[-1]
            pre_context = stdout_output[: last_sep.start()]
            post_context = stdout_output[last_sep.end() :]

            # Find starting index after the latest "N goal(s)" header in pre_context
            raw_pre_lines = pre_context.strip().splitlines()
            start_idx = 0
            for idx, line in enumerate(raw_pre_lines):
                if cls.RE_SUBGOAL_COUNT.search(line):
                    start_idx = idx + 1

            # Normalize hypotheses (stitch multiline wrapped types)
            hyps: list[str] = []
            cur_hyp = ""
            # Regex for start of a new hypothesis: "H : Type" or "x, y : nat" or "x := val : Type"
            hyp_start_pattern = re.compile(
                r"^[A-Za-z_][A-Za-z0-9_']*(?:\s*,\s*[A-Za-z_][A-Za-z0-9_']*)*\s*(?::=|:)\s*"
            )

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

                if hyp_start_pattern.match(line_str):
                    if cur_hyp:
                        hyps.append(cur_hyp)
                    cur_hyp = line_str
                elif cur_hyp:
                    cur_hyp += " " + line_str
                else:
                    cur_hyp = line_str

            if cur_hyp:
                hyps.append(cur_hyp)
            result["hypotheses"] = hyps

            # Extract target conclusion up to the next background goal header or prompt
            target_lines: list[str] = []
            for line in post_context.strip().splitlines():
                line_str = line.strip()
                if not line_str:
                    continue
                if line_str.endswith("<") or line_str.startswith(("Coq <", "Rocq <")):
                    break
                if cls.RE_BG_GOAL.match(line_str):
                    break
                if (
                    "no more goals" in line_str.lower()
                    or "goals you gave up" in line_str.lower()
                ):
                    break
                target_lines.append(line_str)
            result["target"] = "\n".join(target_lines).strip()

        result["raw_state"] = combined_output
        return result

    @classmethod
    def parse_search_results(
        cls, output: str, max_results: int = 30
    ) -> list[dict[str, str]]:
        """Parse Vernacular Search query outputs into identifier-statement pairs.

        Restricts parsing exclusively to output following the final goal state or
        final 'No more goals.' declaration to prevent hypothesis pollution.
        """
        results: list[dict[str, str]] = []
        current_ident: str | None = None
        current_stmt: list[str] = []

        # Find position after the final goal separator or 'No more goals'
        search_start_char = 0
        sep_matches = list(cls.RE_GOAL_SEP.finditer(output)) or list(
            cls.RE_GOAL_SEP_FALLBACK.finditer(output)
        )
        if sep_matches:
            search_start_char = sep_matches[-1].end()

        no_more_goals_idx = output.rfind("No more goals.")
        if (
            no_more_goals_idx != -1
            and no_more_goals_idx + len("No more goals.") > search_start_char
        ):
            search_start_char = no_more_goals_idx + len("No more goals.")

        search_slice = output[search_start_char:]
        lines = search_slice.splitlines()

        for line in lines:
            line_str = line.strip()
            if not line_str:
                continue

            # Skip REPL prompts or loading messages
            if cls.RE_PROMPT.match(line_str) or line_str.endswith("<"):
                continue
            if line_str.startswith(
                ("Error:", "Syntax error:", "Warning:", "[Loading ML")
            ):
                continue
            if cls.RE_GOAL_SEP_FALLBACK.match(line_str) or cls.RE_SUBGOAL_COUNT.search(
                line_str
            ):
                continue

            # New lemma identifier: ident: statement
            ident_match = re.match(
                r"^([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\s*:\s*(.*)$",
                line_str,
            )
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
                # Continuation line of multi-line statement (indented)
                current_stmt.append(line_str)

        if current_ident and len(results) < max_results:
            results.append(
                {
                    "identifier": current_ident,
                    "statement": " ".join(current_stmt).strip(),
                }
            )

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

    state_res = ProofStateParser.parse_goals(stdout, stderr)
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
            if state_res.get("background_goals"):
                print(f"Background subgoals: {state_res['background_goals']}")
            if state_res.get("has_evar_warning"):
                print("[WARNING] Existential variables / evars detected!")
            if state_res.get("shelved_count", 0) > 0:
                print(f"[WARNING] Shelved goals detected: {state_res['shelved_count']}")
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
