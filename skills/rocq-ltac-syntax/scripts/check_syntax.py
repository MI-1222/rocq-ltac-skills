#!/usr/bin/env python3
"""check_syntax.py - Fast Static Syntax & Soundness Checker for Rocq (Vanilla Ltac).

Zero external dependencies (Python 3.10+ standard library only).
Performs Tier 0 static linting on Rocq (.v) files or code snippets.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any


def get_line_col(text: str, pos: int) -> tuple[int, int]:
    """Calculate 1-indexed line and column numbers from a character index."""
    line = text.count("\n", 0, pos) + 1
    last_nl = text.rfind("\n", 0, pos)
    col = pos + 1 if last_nl == -1 else pos - last_nl
    return line, col


def sanitize_rocq_code(code: str) -> tuple[str, list[dict[str, Any]]]:
    """Mask strings ("...") and nested comments (*...*) with spaces.

    Preserves exact character offsets, line counts, and column positions.
    Returns the sanitized buffer and any lexer diagnostics (unterminated
    delimiters).
    """
    sanitized: list[str] = []
    diagnostics: list[dict[str, Any]] = []
    n = len(code)
    i = 0
    depth = 0
    comment_starts: list[int] = []

    while i < n:
        c = code[i]
        c_next = code[i + 1] if i + 1 < n else ""

        # String literal (outside comments)
        if depth == 0 and c == '"':
            start_pos = i
            sanitized.append(" ")
            i += 1
            closed = False
            while i < n:
                if code[i] == '"':
                    if i + 1 < n and code[i + 1] == '"':
                        # Escaped quote ("")
                        sanitized.append("  ")
                        i += 2
                    else:
                        sanitized.append(" ")
                        i += 1
                        closed = True
                        break
                elif code[i] == "\n":
                    sanitized.append("\n")
                    i += 1
                else:
                    sanitized.append(" ")
                    i += 1
            if not closed:
                line, col = get_line_col(code, start_pos)
                diagnostics.append(
                    {
                        "line": line,
                        "column": col,
                        "rule": "LEXER_UNTERMINATED_STRING",
                        "severity": "error",
                        "message": "String literal is not closed before EOF.",
                    }
                )
            continue

        # Comment opening: (*
        if c == "(" and c_next == "*":
            depth += 1
            comment_starts.append(i)
            sanitized.append("  ")
            i += 2
            continue

        # Comment closing: *)
        if depth > 0 and c == "*" and c_next == ")":
            depth -= 1
            if comment_starts:
                comment_starts.pop()
            sanitized.append("  ")
            i += 2
            continue

        # Inside comment
        if depth > 0:
            sanitized.append("\n" if c == "\n" else " ")
            i += 1
        else:
            sanitized.append(c)
            i += 1

    if depth > 0 and comment_starts:
        last_start = comment_starts[-1]
        line, col = get_line_col(code, last_start)
        diagnostics.append(
            {
                "line": line,
                "column": col,
                "rule": "LEXER_UNTERMINATED_COMMENT",
                "severity": "error",
                "message": f"Unterminated comment detected (nesting depth: {depth}).",
            }
        )

    return "".join(sanitized), diagnostics


def lint_code(
    raw_code: str,
    strict_mode: bool = False,
    file_name: str = "<snippet>",
) -> list[dict[str, Any]]:
    """Runs all Tier 0 static rules against the sanitized buffer."""
    sanitized, lexer_diags = sanitize_rocq_code(raw_code)
    diagnostics: list[dict[str, Any]] = list(lexer_diags)

    # 1. FORBIDDEN_SSREFLECT
    ssreflect_patterns = [
        (
            re.compile(r"\bmove\s*=>"),
            "SSReflect 'move=>' syntax is forbidden. Use Vanilla Ltac 'intros'.",
        ),
        (
            re.compile(r"\bby\s*(\[\s*\]|done\b)"),
            "SSReflect 'by []' / 'done' is forbidden. Use 'now auto.', 'reflexivity.', or 'easy.'.",
        ),
        (
            re.compile(r"\bhave\s*(?:[A-Za-z0-9_']+\s*)?:"),
            "SSReflect 'have:' is forbidden. Use 'assert (H : P) by ...'.",
        ),
        (
            re.compile(r"\bsuff\s*(?:[A-Za-z0-9_']+\s*)?:"),
            "SSReflect 'suff:' is forbidden. Use 'enough (H : P) by ...'.",
        ),
        (
            re.compile(r"(?<![A-Za-z0-9_/\*])//(?![A-Za-z0-9_/\*])"),
            "SSReflect '//' branch discharge is forbidden. Use '; try easy.' or '; auto.'.",
        ),
        (
            re.compile(r"\bcongr\b"),
            "SSReflect 'congr' is forbidden. Use Vanilla Ltac 'f_equal.'.",
        ),
    ]
    for pattern, msg in ssreflect_patterns:
        for match in pattern.finditer(sanitized):
            line, col = get_line_col(raw_code, match.start())
            diagnostics.append(
                {
                    "line": line,
                    "column": col,
                    "rule": "FORBIDDEN_SSREFLECT",
                    "severity": "error",
                    "message": msg,
                }
            )

    # 2. SYNTAX_INVALID_BULLET_DOT (-., +., *., etc.)
    bullet_dot_re = re.compile(r"^[ \t]*(-+|\++|\*+)\.", re.MULTILINE)
    for match in bullet_dot_re.finditer(sanitized):
        dot_idx = match.end() - 1
        line, col = get_line_col(raw_code, dot_idx)
        bullet_sym = match.group(1)
        diagnostics.append(
            {
                "line": line,
                "column": col,
                "rule": "SYNTAX_INVALID_BULLET_DOT",
                "severity": "error",
                "message": f"Focus bullet must not be followed by a period. Change '{bullet_sym}.' to '{bullet_sym}'.",
            }
        )

    # 3. SYNTAX_PERIOD_NO_SPACE
    # Checks periods that collide with following keywords/tactics without whitespace
    period_keyword_re = re.compile(
        r"\.(?=(?:Proof|Qed|Defined|Abort|intros|induction|destruct|apply|rewrite|reflexivity|exact|simpl|cbn|lia|auto|eauto|inv)\b)"
    )
    for match in period_keyword_re.finditer(sanitized):
        line, col = get_line_col(raw_code, match.start())
        diagnostics.append(
            {
                "line": line,
                "column": col,
                "rule": "SYNTAX_PERIOD_NO_SPACE",
                "severity": "error",
                "message": "Sentence terminator period ('.') must be followed by whitespace or newline.",
            }
        )

    non_qualid_dot_re = re.compile(r"[\)\]\}\"0-9]\.(?=[A-Za-z])")
    for match in non_qualid_dot_re.finditer(sanitized):
        dot_idx = match.start() + 1
        line, col = get_line_col(raw_code, dot_idx)
        diagnostics.append(
            {
                "line": line,
                "column": col,
                "rule": "SYNTAX_PERIOD_NO_SPACE",
                "severity": "error",
                "message": "Period following closing delimiter must be separated from next token by whitespace.",
            }
        )

    # 4. DEPRECATED_TACTICS (omega, romega, sos)
    deprecated_tactics_re = re.compile(r"\b(omega|romega|sos)\b")
    for match in deprecated_tactics_re.finditer(sanitized):
        line, col = get_line_col(raw_code, match.start())
        tactic_name = match.group(1)
        diagnostics.append(
            {
                "line": line,
                "column": col,
                "rule": "DEPRECATED_TACTICS",
                "severity": "error",
                "message": f"Tactic '{tactic_name}' was removed in modern Rocq. Use 'lia.' (or 'nia.') instead.",
            }
        )

    # 5. DEPRECATED_BARE_ATTRIBUTES
    bare_attrib_re = re.compile(
        r"^[ \t]*(Local|Global|Export)\s+(Hint|Instance|Definition|Theorem|Lemma|Set|Unset)\b",
        re.MULTILINE,
    )
    for match in bare_attrib_re.finditer(sanitized):
        line, col = get_line_col(raw_code, match.start())
        modifier = match.group(1)
        target = match.group(2)
        diagnostics.append(
            {
                "line": line,
                "column": col,
                "rule": "DEPRECATED_BARE_ATTRIBUTES",
                "severity": "warning",
                "message": f"Bare attribute '{modifier} {target}' is deprecated. Use '#[{modifier.lower()}] {target}'.",
            }
        )

    # 6. LEGACY_NAMESPACE
    legacy_ns_re = re.compile(r"\bFrom\s+Coq\b")
    for match in legacy_ns_re.finditer(sanitized):
        line, col = get_line_col(raw_code, match.start())
        diagnostics.append(
            {
                "line": line,
                "column": col,
                "rule": "LEGACY_NAMESPACE",
                "severity": "warning",
                "message": "Use of 'From Coq' is deprecated. In Rocq 9.0+, use 'From Corelib' or 'From Stdlib'.",
            }
        )

    # 7. DEPRECATED_UNIV_SYNTAX
    deprecated_univ_re = re.compile(r"\bType@\{")
    for match in deprecated_univ_re.finditer(sanitized):
        line, col = get_line_col(raw_code, match.start())
        diagnostics.append(
            {
                "line": line,
                "column": col,
                "rule": "DEPRECATED_UNIV_SYNTAX",
                "severity": "warning",
                "message": "Universe syntax 'Type@{...}' is deprecated in Rocq 9.0+. Use 'Univ@{...}'.",
            }
        )

    # 8. LINT_BARE_INVERSION
    bare_inv_re = re.compile(r"\binversion\s+[A-Za-z0-9_']+\s*\.")
    for match in bare_inv_re.finditer(sanitized):
        line, col = get_line_col(raw_code, match.start())
        diagnostics.append(
            {
                "line": line,
                "column": col,
                "rule": "LINT_BARE_INVERSION",
                "severity": "warning",
                "message": "Bare 'inversion H.' causes context pollution. Use 'inv H.' (inversion H; subst; clear H).",
            }
        )

    # 9. SOUNDNESS_AXIOM_DETECTED
    axiom_re = re.compile(r"\b(Axioms?|Conjectures?|Parameters?)\s+([A-Za-z0-9_']+)")
    for match in axiom_re.finditer(sanitized):
        line, col = get_line_col(raw_code, match.start())
        kind = match.group(1)
        name = match.group(2)
        diagnostics.append(
            {
                "line": line,
                "column": col,
                "rule": "SOUNDNESS_AXIOM_DETECTED",
                "severity": "error",
                "message": f"Unapproved {kind} '{name}' declared. Axiom introduction is strictly forbidden.",
            }
        )

    # 10. SOUNDNESS_ADMIT_DETECTED
    admit_re = re.compile(r"\b(admit|Admitted)\b")
    for match in admit_re.finditer(sanitized):
        line, col = get_line_col(raw_code, match.start())
        word = match.group(1)
        severity = "error" if strict_mode else "warning"
        diagnostics.append(
            {
                "line": line,
                "column": col,
                "rule": "SOUNDNESS_ADMIT_DETECTED",
                "severity": severity,
                "message": f"Residual unproven hole '{word}' detected.",
            }
        )

    # 11. BLOCK_MISMATCH_MATCH_END
    match_end_re = re.compile(r"\b(match|lazymatch|multimatch|end)\b")
    match_stack: list[int] = []
    for match in match_end_re.finditer(sanitized):
        token = match.group(1)
        if token in ("match", "lazymatch", "multimatch"):
            match_stack.append(match.start())
        elif token == "end":
            if match_stack:
                match_stack.pop()
            else:
                line, col = get_line_col(raw_code, match.start())
                diagnostics.append(
                    {
                        "line": line,
                        "column": col,
                        "rule": "BLOCK_MISMATCH_MATCH_END",
                        "severity": "error",
                        "message": "Unmatched 'end' keyword detected without corresponding 'match'.",
                    }
                )
    for start_pos in match_stack:
        line, col = get_line_col(raw_code, start_pos)
        diagnostics.append(
            {
                "line": line,
                "column": col,
                "rule": "BLOCK_MISMATCH_MATCH_END",
                "severity": "error",
                "message": "Unclosed 'match' block reaching EOF without 'end'.",
            }
        )

    # 12. BLOCK_MISMATCH_SECTION
    block_re = re.compile(r"\b(Section|Module(?:\s+Type)?|End)\s+([A-Za-z0-9_']+)")
    block_stack: list[tuple[str, int]] = []
    for match in block_re.finditer(sanitized):
        token = match.group(1)
        name = match.group(2)
        if token in ("Section", "Module") or token.startswith("Module"):
            block_stack.append((name, match.start()))
        elif token == "End":
            if block_stack:
                expected_name, _start_idx = block_stack.pop()
                if expected_name != name:
                    line, col = get_line_col(raw_code, match.start())
                    diagnostics.append(
                        {
                            "line": line,
                            "column": col,
                            "rule": "BLOCK_MISMATCH_SECTION",
                            "severity": "error",
                            "message": f"Block delimiter mismatch: Expected 'End {expected_name}', but found 'End {name}'.",
                        }
                    )
            else:
                line, col = get_line_col(raw_code, match.start())
                diagnostics.append(
                    {
                        "line": line,
                        "column": col,
                        "rule": "BLOCK_MISMATCH_SECTION",
                        "severity": "error",
                        "message": f"Unmatched 'End {name}' statement without an opening Section or Module.",
                    }
                )
    for unclosed_name, start_pos in block_stack:
        line, col = get_line_col(raw_code, start_pos)
        diagnostics.append(
            {
                "line": line,
                "column": col,
                "rule": "BLOCK_MISMATCH_SECTION",
                "severity": "error",
                "message": f"Unclosed Section or Module '{unclosed_name}' at EOF.",
            }
        )

    # Sort diagnostics by line, then column
    diagnostics.sort(key=lambda d: (d["line"], d["column"]))
    return diagnostics


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Fast Static Syntax & Soundness Checker for Rocq (Pure Vanilla Ltac)."
    )
    parser.add_argument("file", nargs="?", help="Target .v file to check")
    parser.add_argument("-s", "--snippet", help="Inline Rocq code snippet to check")
    parser.add_argument(
        "--stdin",
        action="store_true",
        help="Read Rocq source code from standard input",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output diagnostics in structured JSON format",
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        help="Strict submission mode: Treat 'admit' and 'Admitted' as errors",
    )

    args = parser.parse_args()

    if args.snippet is not None:
        source_code = args.snippet
        file_name = "<snippet>"
    elif args.stdin:
        source_code = sys.stdin.read()
        file_name = "<stdin>"
    elif args.file:
        path = Path(args.file)
        if not path.is_file():
            print(f"Error: File '{args.file}' not found.", file=sys.stderr)
            sys.exit(2)
        source_code = path.read_text(encoding="utf-8")
        file_name = str(path)
    else:
        parser.print_help(sys.stderr)
        sys.exit(2)

    diagnostics = lint_code(source_code, strict_mode=args.strict, file_name=file_name)
    error_count = sum(1 for d in diagnostics if d["severity"] == "error")
    warning_count = sum(1 for d in diagnostics if d["severity"] == "warning")
    is_valid = error_count == 0

    if args.json:
        payload = {
            "file": file_name,
            "status": "pass" if is_valid else "fail",
            "error_count": error_count,
            "warning_count": warning_count,
            "diagnostics": diagnostics,
        }
        print(json.dumps(payload, indent=2))
    else:
        if diagnostics:
            for diag in diagnostics:
                sev_tag = "ERROR" if diag["severity"] == "error" else "WARNING"
                print(
                    f"{file_name}:{diag['line']}:{diag['column']}: "
                    f"{sev_tag}: [{diag['rule']}] {diag['message']}"
                )
            status_text = "FAILED" if error_count > 0 else "PASSED (with warnings)"
            print(
                f"\n{status_text}: {error_count} error(s), {warning_count} warning(s) found.",
                file=sys.stderr if error_count > 0 else sys.stdout,
            )
        else:
            print(f"PASSED: '{file_name}' is syntactically sound and clean.")

    sys.exit(1 if error_count > 0 else 0)


if __name__ == "__main__":
    main()
