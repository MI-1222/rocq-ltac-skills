#!/usr/bin/env python3
"""lint_proof_contract.py - Rocq Proof Contract & Header Fence Linter.

Enforces declaration immutability, docstring freezing, and admit lifecycle rules.
Zero external dependencies (Standard Python 3.10+ only).
"""

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

# Matches all 8 standard theorem-introducing vernacular keywords with optional attributes
DECLARATION_START_RE = re.compile(
    r"^\s*(?:#\[[^\]]*\]\s*)*(?:Theorem|Lemma|Fact|Remark|Corollary|Proposition|Property|Example)\s+([A-Za-z0-9_']+)",
    re.MULTILINE,
)

# Matches model definitions (Record, Inductive, Fixpoint, Definition, etc.)
MODEL_DECLARATION_START_RE = re.compile(
    r"^\s*(?:#\[[^\]]*\]\s*)*(?:Record|Inductive|CoInductive|Fixpoint|CoFixpoint|Definition)\s+([A-Za-z0-9_']+)",
    re.MULTILINE,
)

DOCSTRING_SPEC_RE = re.compile(r"\(\*\*\s*\[SPEC\].*?\*\)", re.DOTALL)
DOCSTRING_MODEL_RE = re.compile(r"\(\*\*\s*\[MODEL\].*?\*\)", re.DOTALL)
DOCSTRING_CONTRACT_RE = re.compile(r"\(\*\*\s*\[(?:SPEC|MODEL)\].*?\*\)", re.DOTALL)


def extract_declarations(
    content: str, include_models: bool = True
) -> dict[str, dict[str, Any]]:
    """Extracts theorem and model declarations, capturing their exact signature header

    from the start keyword to the closing period before Proof or definition end.
    """
    declarations: dict[str, dict[str, Any]] = {}
    lines = content.splitlines(keepends=True)
    n = len(lines)
    i = 0

    while i < n:
        line = lines[i]
        thm_match = DECLARATION_START_RE.search(line)
        model_match = (
            MODEL_DECLARATION_START_RE.search(line) if include_models else None
        )

        if thm_match or model_match:
            match = thm_match or model_match
            assert match is not None
            name = match.group(1)
            is_model = model_match is not None and not thm_match
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
                declarations[name] = {
                    "raw": raw_sig,
                    "normalized": norm_sig,
                    "start_line": start_line + 1,
                    "is_model": is_model,
                }
            continue
        i += 1
    return declarations


def extract_spec_docstrings(content: str) -> list[str]:
    """Extracts all (** [SPEC] ... *) docstrings in normalized form."""
    return [" ".join(m.group(0).split()) for m in DOCSTRING_SPEC_RE.finditer(content)]


def extract_contract_docstrings(content: str) -> list[str]:
    """Extracts all contract docstrings (** [SPEC] ... *) and (** [MODEL] ... *) in normalized form."""
    return [
        " ".join(m.group(0).split()) for m in DOCSTRING_CONTRACT_RE.finditer(content)
    ]


def is_subsequence(sub: list[str], full: list[str]) -> bool:
    """Checks whether sub is a subsequence of full, preserving relative order."""
    it = iter(full)
    return all(item in it for item in sub)


def lint_contract(
    original_text: str,
    modified_text: str,
    strict_mode: bool,
    allow_new_specs: bool = False,
    include_models: bool = True,
) -> list[str]:
    """Compares original vs modified file content to verify Header Fence and Docstrings."""
    errors: list[str] = []

    orig_decls = extract_declarations(original_text, include_models=include_models)
    mod_decls = extract_declarations(modified_text, include_models=include_models)

    # 1. Header/Model Fence Verification: Existing declarations must not be modified or deleted
    for name, orig_data in orig_decls.items():
        is_model = orig_data.get("is_model", False)
        fence_name = "Model definition" if is_model else "Declaration"
        tag = "[MODEL_FENCE_VIOLATION]" if is_model else "[FENCE_VIOLATION]"

        if name not in mod_decls:
            errors.append(
                f"{tag} Existing {fence_name.lower()} '{name}' was deleted or renamed."
            )
            continue

        mod_data = mod_decls[name]
        if orig_data["normalized"] != mod_data["normalized"]:
            errors.append(
                f"{tag} Signature of {fence_name.lower()} '{name}' was modified!\n"
                f"  Original: {orig_data['normalized']}\n"
                f"  Modified: {mod_data['normalized']}"
            )

    # 2. Spec & Model Docstring Tampering Verification (Rule A)
    orig_specs = extract_contract_docstrings(original_text)
    mod_specs = extract_contract_docstrings(modified_text)

    if allow_new_specs:
        # In incremental / open development mode, existing docstrings must be preserved
        # in their original relative order (monotonic extension).
        if not is_subsequence(orig_specs, mod_specs):
            errors.append(
                "[CONTRACT_TAMPERING] Existing (** [SPEC] ... *) or (** [MODEL] ... *) docstrings were modified, "
                "reordered, or removed improperly."
            )
    else:
        # Strict equality check for exercise / frozen assignment settings
        if orig_specs != mod_specs:
            errors.append(
                "[CONTRACT_TAMPERING] (** [SPEC] ... *) or (** [MODEL] ... *) docstrings were modified, removed, or added improperly.\n"
                "  >>> NOTICE: In incremental task workflows (adding new lemmas/models across commits),\n"
                "  >>> rerun with: --allow-new-specs (or --incremental) to permit new specifications."
            )

    # 3. Admit / Admitted checks in modified file
    admit_matches = re.findall(r"\b(?:admit|Admitted)\b", modified_text)
    if strict_mode and admit_matches:
        errors.append(
            f"[SOUNDNESS_LEAK] Strict check failed: Found {len(admit_matches)} "
            f"instance(s) of 'admit' / 'Admitted' in submitted proof."
        )

    return errors


def get_git_file_content(file_path: Path, git_ref: str = "HEAD") -> tuple[bool, str]:
    """Retrieve historical file content from git repository at specified ref (default: HEAD)."""
    resolved = file_path.resolve()
    file_dir = resolved.parent if resolved.is_file() else resolved
    try:
        rev_proc = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            cwd=str(file_dir),
            capture_output=True,
            text=True,
            check=True,
        )
        repo_root = Path(rev_proc.stdout.strip()).resolve()
        rel_path = resolved.relative_to(repo_root)
        show_proc = subprocess.run(
            ["git", "show", f"{git_ref}:{rel_path}"],
            cwd=str(repo_root),
            capture_output=True,
            text=True,
            check=True,
        )
        return True, show_proc.stdout
    except (subprocess.CalledProcessError, ValueError, OSError) as e:
        return False, f"Failed to retrieve '{file_path}' from git ref '{git_ref}': {e}"


def run_self_tests() -> int:
    """Run internal test suite covering contract fences and docstrings."""
    orig = (
        "(** [MODEL]\n    Original model definition. *)\n"
        "Record Point : Type := mkPoint { pt_x : nat; pt_y : nat }.\n\n"
        "(** [SPEC]\n    Addition commutativity. *)\n"
        "Lemma add_comm : forall n m, n + m = m + n.\n"
        "Proof. intros. lia. Qed.\n"
    )

    # 1. Exact match pass
    errs = lint_contract(orig, orig, strict_mode=True, allow_new_specs=False)
    assert not errs, f"Expected clean pass, got: {errs}"

    # 2. Incremental addition with allow_new_specs
    mod_inc = (
        orig
        + "\n(** [SPEC]\n    New lemma added. *)\n"
        + "Lemma add_0_r : forall n, n + 0 = n.\nProof. intros. lia. Qed.\n"
    )
    errs_no_inc = lint_contract(orig, mod_inc, strict_mode=True, allow_new_specs=False)
    assert len(errs_no_inc) > 0, "Expected failure without --allow-new-specs"
    assert "--allow-new-specs" in errs_no_inc[0]

    errs_inc = lint_contract(orig, mod_inc, strict_mode=True, allow_new_specs=True)
    assert not errs_inc, f"Expected pass with allow_new_specs, got: {errs_inc}"

    # 3. Model tampering detection
    mod_tamper_model = orig.replace("pt_y : nat", "pt_y : bool")
    errs_tamper = lint_contract(
        orig, mod_tamper_model, strict_mode=True, allow_new_specs=True
    )
    assert any("[MODEL_FENCE_VIOLATION]" in e for e in errs_tamper)

    print("All lint_proof_contract self-tests passed successfully.")
    return 0


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Rocq Header Fence and Contract Verification Linter"
    )
    parser.add_argument(
        "--file",
        "-f",
        type=Path,
        help="Path to .v file to check against git HEAD (or reference specified by --git-ref)",
    )
    parser.add_argument(
        "--original",
        "-o",
        type=Path,
        help="Path to reference original .v file (if omitted, falls back to git HEAD)",
    )
    parser.add_argument(
        "--modified",
        "-m",
        type=Path,
        help="Path to modified .v file to check (alias for --file)",
    )
    parser.add_argument(
        "--git-ref",
        "--git-head",
        dest="git_ref",
        default="HEAD",
        help="Git commit/branch reference to compare against when --original is omitted (default: HEAD)",
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        help="Reject any remaining 'admit' or 'Admitted' (submission mode)",
    )
    parser.add_argument(
        "--allow-new-specs",
        "--incremental",
        dest="allow_new_specs",
        action="store_true",
        help="Allow incremental additions of new (** [SPEC] ... *) and (** [MODEL] ... *) docstrings while strictly preserving existing ones (essential for multi-commit incremental tasks)",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output structured JSON payload for autonomous agent pipelines",
    )
    parser.add_argument(
        "--test",
        action="store_true",
        help="Run internal self-tests and exit",
    )

    args = parser.parse_args()

    if args.test:
        sys.exit(run_self_tests())

    target_path = args.modified or args.file
    if not target_path:
        err_msg = "Error: Either --file, --modified, or both --original and --modified must be provided."
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

    if not target_path.is_file():
        err_msg = f"Error: Modified target file '{target_path}' does not exist."
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

    with open(target_path, encoding="utf-8") as f:
        mod_text = f.read()

    orig_text = ""
    if args.original:
        if not args.original.is_file():
            err_msg = (
                f"Error: Reference original file '{args.original}' does not exist."
            )
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
    else:
        ok, git_content = get_git_file_content(target_path, git_ref=args.git_ref)
        if not ok:
            err_msg = f"Error resolving baseline from git: {git_content}"
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
        orig_text = git_content

    errors = lint_contract(orig_text, mod_text, args.strict, args.allow_new_specs)

    if args.json:
        result = {
            "success": len(errors) == 0,
            "strict": args.strict,
            "allow_new_specs": args.allow_new_specs,
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
