#!/usr/bin/env python3
"""lint_proof_contract.py - Rocq Proof Contract & Header Fence Linter.

Enforces declaration immutability, docstring freezing, and admit lifecycle rules.
Zero external dependencies (Standard Python 3.10+ only).
"""

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

# Matches all 8 standard theorem-introducing vernacular keywords with optional attributes
DECLARATION_START_RE = re.compile(
    r"^\s*(?:#\[[^\]]*\]\s*)*(?:Theorem|Lemma|Fact|Remark|Corollary|Proposition|Property|Example)\s+([A-Za-z0-9_']+)",
    re.MULTILINE,
)
DOCSTRING_SPEC_RE = re.compile(r"\(\*\*\s*\[SPEC\].*?\*\)", re.DOTALL)


def extract_declarations(content: str) -> dict[str, dict[str, Any]]:
    """Extracts theorem declarations, capturing their exact signature header

    from the start keyword to the closing period before Proof.
    """
    declarations: dict[str, dict[str, Any]] = {}
    lines = content.splitlines(keepends=True)
    n = len(lines)
    i = 0

    while i < n:
        line = lines[i]
        match = DECLARATION_START_RE.search(line)
        if match:
            lemma_name = match.group(1)
            start_line = i
            sig_tokens: list[str] = []

            found_dot = False
            while i < n:
                cur = lines[i]
                sig_tokens.append(cur)
                # Check for terminating dot followed by optional comments/whitespace at line end
                if re.search(r"\.\s*(?:\(\*.*?\*\)\s*)*$", cur):
                    found_dot = True
                    i += 1
                    break
                i += 1

            if found_dot:
                raw_sig = "".join(sig_tokens)
                norm_sig = " ".join(raw_sig.split())
                declarations[lemma_name] = {
                    "raw": raw_sig,
                    "normalized": norm_sig,
                    "start_line": start_line + 1,
                }
            continue
        i += 1
    return declarations


def extract_spec_docstrings(content: str) -> list[str]:
    """Extracts all (** [SPEC] ... *) docstrings in normalized form."""
    return [" ".join(m.group(0).split()) for m in DOCSTRING_SPEC_RE.finditer(content)]


def lint_contract(
    original_text: str, modified_text: str, strict_mode: bool
) -> list[str]:
    """Compares original vs modified file content to verify Header Fence and Docstrings."""
    errors: list[str] = []

    orig_decls = extract_declarations(original_text)
    mod_decls = extract_declarations(modified_text)

    # 1. Header Fence Verification: Existing declarations must not be modified or deleted
    for name, orig_data in orig_decls.items():
        if name not in mod_decls:
            errors.append(
                f"[FENCE_VIOLATION] Existing declaration '{name}' was deleted or renamed."
            )
            continue

        mod_data = mod_decls[name]
        if orig_data["normalized"] != mod_data["normalized"]:
            errors.append(
                f"[FENCE_VIOLATION] Signature of declaration '{name}' was modified!\n"
                f"  Original: {orig_data['normalized']}\n"
                f"  Modified: {mod_data['normalized']}"
            )

    # 2. Spec Docstring Tampering Verification (Rule A)
    orig_specs = extract_spec_docstrings(original_text)
    mod_specs = extract_spec_docstrings(modified_text)

    if orig_specs != mod_specs:
        errors.append(
            "[SPEC_TAMPERING] (** [SPEC] ... *) docstrings were modified, removed, or added improperly."
        )

    # 3. Admit / Admitted checks in modified file
    admit_matches = re.findall(r"\b(?:admit|Admitted)\b", modified_text)
    if strict_mode and admit_matches:
        errors.append(
            f"[SOUNDNESS_LEAK] Strict check failed: Found {len(admit_matches)} "
            f"instance(s) of 'admit' / 'Admitted' in submitted proof."
        )

    return errors


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Rocq Header Fence and Contract Verification Linter"
    )
    parser.add_argument(
        "--original",
        required=True,
        type=Path,
        help="Path to reference original .v file",
    )
    parser.add_argument(
        "--modified",
        required=True,
        type=Path,
        help="Path to modified .v file to check",
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        help="Reject any remaining 'admit' or 'Admitted' (submission mode)",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output structured JSON payload for autonomous agent pipelines",
    )

    args = parser.parse_args()

    if not args.original.is_file() or not args.modified.is_file():
        err_msg = "Error: Input files do not exist."
        if args.json:
            print(
                json.dumps(
                    {
                        "success": False,
                        "errors": [err_msg],
                        "strict": args.strict,
                    }
                )
            )
        else:
            print(err_msg, file=sys.stderr)
        sys.exit(2)

    with open(args.original, encoding="utf-8") as f:
        orig_text = f.read()
    with open(args.modified, encoding="utf-8") as f:
        mod_text = f.read()

    errors = lint_contract(orig_text, mod_text, args.strict)

    if args.json:
        result = {
            "success": len(errors) == 0,
            "strict": args.strict,
            "errors": errors,
            "violation_count": len(errors),
        }
        print(json.dumps(result, indent=2))
        sys.exit(0 if len(errors) == 0 else 1)

    if errors:
        print(
            f"FAILED: Found {len(errors)} contract violation(s):",
            file=sys.stderr,
        )
        for err in errors:
            print(f" - {err}", file=sys.stderr)
        sys.exit(1)
    else:
        status_msg = (
            "STRICT PASSED (Clean of admits)"
            if args.strict
            else "PASSED (Intermediate contract intact)"
        )
        print(f"SUCCESS: Proof contract verification: {status_msg}")
        sys.exit(0)


if __name__ == "__main__":
    main()
