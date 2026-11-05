#!/usr/bin/env python3
"""Axiom soundness and kernel assumption auditor for Rocq theorems.

Executes Print Assumptions in an isolated REPL process and verifies that the
kernel CONTEXT SUMMARY output adheres strictly to soundness invariants,
ensuring zero unauthorized axioms, admits, or disabled safety checkers.
"""

import argparse
import json
import os
import shlex
import subprocess
import sys
from typing import Any

DEFAULT_APPROVED_AXIOMS: set[str] = {
    "Coq.Logic.FunctionalExtensionality.functional_extensionality_dep",
    "Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep",
    "Coq.Logic.ProofIrrelevance.proof_irrelevance",
    "Stdlib.Logic.ProofIrrelevance.proof_irrelevance",
    "Coq.Logic.Classical_Prop.classic",
    "Stdlib.Logic.Classical_Prop.classic",
}


def load_project_arguments(project_dir: str) -> list[str]:
    """Parse compiler options and path bindings from _CoqProject.

    Args:
        project_dir: Root directory of the project.

    Returns:
        List of CLI arguments to pass to the REPL.
    """
    project_file_path = os.path.join(project_dir, "_CoqProject")
    if not os.path.isfile(project_file_path):
        return []

    collected_arguments: list[str] = []
    try:
        with open(project_file_path, "r", encoding="utf-8") as file_handle:
            lines = file_handle.readlines()
    except OSError:
        return []

    for line in lines:
        stripped_line = line.strip()
        if not stripped_line or stripped_line.startswith("#"):
            continue

        tokens = shlex.split(stripped_line, comments=True)
        idx = 0
        while idx < len(tokens):
            token = tokens[idx]
            if token in ("-Q", "-R"):
                if idx + 2 < len(tokens):
                    physical_path = os.path.join(project_dir, tokens[idx + 1])
                    logical_prefix = tokens[idx + 2]
                    collected_arguments.extend([token, physical_path, logical_prefix])
                    idx += 3
                else:
                    idx += 1
            elif token == "-I":
                if idx + 1 < len(tokens):
                    include_path = os.path.join(project_dir, tokens[idx + 1])
                    collected_arguments.extend(["-I", include_path])
                    idx += 2
                else:
                    idx += 1
            elif token == "-arg":
                if idx + 1 < len(tokens):
                    extra_flag = tokens[idx + 1]
                    collected_arguments.extend(shlex.split(extra_flag))
                    idx += 2
                else:
                    idx += 1
            else:
                idx += 1

    return collected_arguments


def find_repl_executable() -> list[str] | None:
    """Discover available Rocq or Coq REPL binaries.

    Returns:
        Command token list, or None if no suitable binary found.
    """
    candidates = [
        ["rocq", "repl"],
        ["rocq", "top"],
        ["coqtop"],
    ]
    for cmd in candidates:
        try:
            res = subprocess.run(
                cmd + ["-v"],
                capture_output=True,
                text=True,
                timeout=5,
                check=False,
            )
            if res.returncode == 0:
                return cmd
        except (FileNotFoundError, subprocess.TimeoutExpired):
            continue
    return None


def execute_print_assumptions(
    repl_command: list[str],
    module_path: str,
    theorem_name: str,
    project_arguments: list[str],
    working_directory: str,
    timeout_seconds: float,
) -> tuple[int, str, str]:
    """Execute Print Assumptions in an isolated REPL subprocess.

    Args:
        repl_command: Base REPL command tokens.
        module_path: Logical module name containing the theorem.
        theorem_name: Identifier of the theorem to audit.
        project_arguments: Include flags parsed from _CoqProject.
        working_directory: Execution directory path.
        timeout_seconds: Execution deadline timeout.

    Returns:
        Tuple of (returncode, stdout, stderr).
    """
    full_command = (
        list(repl_command) + ["-batch", "-quiet", "-color", "no"] + project_arguments
    )
    input_script = (
        f"Require Import {module_path}.\nPrint Assumptions {theorem_name}.\nQuit.\n"
    )

    try:
        proc = subprocess.Popen(
            full_command,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            cwd=working_directory,
        )
        stdout_text, stderr_text = proc.communicate(
            input=input_script, timeout=timeout_seconds
        )
        return proc.returncode, stdout_text, stderr_text
    except subprocess.TimeoutExpired:
        proc.kill()
        out, err = proc.communicate()
        return 124, out, err + "\nError: Print Assumptions execution timed out."
    except OSError as err:
        return 1, "", f"Subprocess execution error: {err}."


def parse_context_summary(output_text: str) -> dict[str, Any]:
    """Parse Print Assumptions CONTEXT SUMMARY output block.

    Args:
        output_text: Combined stdout and stderr text from the REPL.

    Returns:
        Structured dictionary of kernel check items.
    """
    axioms: list[str] = []
    type_in_type_items: list[str] = []
    unsafe_fixpoints: list[str] = []
    nonpositive_inductives: list[str] = []
    unchecked_eliminations: list[str] = []
    indices_not_mattering: list[str] = []

    if "Closed under the global context" in output_text:
        return {
            "has_context_summary": True,
            "axioms": [],
            "type_in_type": [],
            "unsafe_fixpoints": [],
            "nonpositive_inductives": [],
            "unchecked_eliminations": [],
            "indices_not_mattering": [],
            "raw_output": output_text.strip(),
        }

    lines = output_text.splitlines()
    current_section: str | None = None

    for line in lines:
        stripped = line.strip()
        if stripped.startswith("* Axioms:"):
            if stripped.endswith("<none>"):
                current_section = None
            else:
                current_section = "axioms"
            continue
        elif stripped.startswith("* Constants/Inductives relying on type-in-type:"):
            if stripped.endswith("<none>"):
                current_section = None
            else:
                current_section = "type_in_type"
            continue
        elif stripped.startswith(
            "* Constants/Inductives relying on unsafe (co)fixpoints:"
        ):
            if stripped.endswith("<none>"):
                current_section = None
            else:
                current_section = "unsafe_fixpoints"
            continue
        elif stripped.startswith("* Inductives whose positivity is assumed:"):
            if stripped.endswith("<none>"):
                current_section = None
            else:
                current_section = "nonpositive"
            continue
        elif stripped.startswith("* Inductives relying on indices not mattering:"):
            if stripped.endswith("<none>"):
                current_section = None
            else:
                current_section = "indices_not_mattering"
            continue
        elif stripped.startswith(
            "* Constants/Inductives relying on unchecked sort eliminations:"
        ):
            current_section = "unchecked_eliminations"
            if not stripped.endswith("<none>"):
                val = stripped.split(":", 1)[1].strip()
                if val:
                    unchecked_eliminations.append(val)
            continue
        elif stripped.startswith("* Theory:"):
            current_section = None
            continue

        if current_section and stripped:
            if stripped.startswith("*"):
                current_section = None
                continue
            item = stripped.split(":")[0].strip()
            if item:
                if current_section == "axioms":
                    axioms.append(item)
                elif current_section == "type_in_type":
                    type_in_type_items.append(item)
                elif current_section == "unsafe_fixpoints":
                    unsafe_fixpoints.append(item)
                elif current_section == "nonpositive":
                    nonpositive_inductives.append(item)
                elif current_section == "indices_not_mattering":
                    indices_not_mattering.append(item)
                elif current_section == "unchecked_eliminations":
                    unchecked_eliminations.append(item)

    return {
        "has_context_summary": ("CONTEXT SUMMARY" in output_text),
        "axioms": axioms,
        "type_in_type": type_in_type_items,
        "unsafe_fixpoints": unsafe_fixpoints,
        "nonpositive_inductives": nonpositive_inductives,
        "unchecked_eliminations": unchecked_eliminations,
        "indices_not_mattering": indices_not_mattering,
        "raw_output": output_text.strip(),
    }


def parse_arguments() -> argparse.Namespace:
    """Parse command line arguments.

    Returns:
        Parsed arguments namespace.
    """
    parser = argparse.ArgumentParser(
        description="Axiom soundness and kernel assumption auditor for Rocq theorems.",
    )
    parser.add_argument(
        "--module",
        required=True,
        help="Logical module path containing the theorem (e.g., MyProject.Semantics).",
    )
    parser.add_argument(
        "--theorem",
        required=True,
        help="Identifier of the theorem to audit (e.g., progress_theorem).",
    )
    parser.add_argument(
        "--project-dir",
        default=".",
        help="Project root directory containing _CoqProject (default: .).",
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=30.0,
        help="Audit execution deadline in seconds (default: 30.0).",
    )
    parser.add_argument(
        "--allow-standard-axioms",
        action="store_true",
        help="Allow verified standard axioms (functional extensionality, proof irrelevance, excluded middle).",
    )
    return parser.parse_args()


def main() -> None:
    """Main CLI entrypoint."""
    args = parse_arguments()

    repl_cmd = find_repl_executable()
    if not repl_cmd:
        error_result = {
            "sound": False,
            "module": args.module,
            "theorem": args.theorem,
            "error": "No rocq or coqtop executable found in PATH.",
        }
        print(json.dumps(error_result, indent=2, ensure_ascii=False))
        sys.exit(1)

    project_args = load_project_arguments(args.project_dir)

    returncode, stdout_text, stderr_text = execute_print_assumptions(
        repl_command=repl_cmd,
        module_path=args.module,
        theorem_name=args.theorem,
        project_arguments=project_args,
        working_directory=args.project_dir,
        timeout_seconds=args.timeout,
    )

    combined_output = f"{stdout_text}\n{stderr_text}"
    summary = parse_context_summary(combined_output)

    unapproved_axioms: list[str] = []
    allowed_set = DEFAULT_APPROVED_AXIOMS if args.allow_standard_axioms else set()

    for ax in summary["axioms"]:
        if ax not in allowed_set:
            unapproved_axioms.append(ax)

    has_safety_violations = (
        len(summary["type_in_type"]) > 0
        or len(summary["unsafe_fixpoints"]) > 0
        or len(summary["nonpositive_inductives"]) > 0
        or len(summary["unchecked_eliminations"]) > 0
    )

    is_sound = (
        returncode == 0
        and summary["has_context_summary"]
        and len(unapproved_axioms) == 0
        and not has_safety_violations
    )

    audit_result = {
        "sound": is_sound,
        "module": args.module,
        "theorem": args.theorem,
        "all_axioms": summary["axioms"],
        "unapproved_axioms": unapproved_axioms,
        "type_in_type": summary["type_in_type"],
        "unsafe_fixpoints": summary["unsafe_fixpoints"],
        "nonpositive_inductives": summary["nonpositive_inductives"],
        "unchecked_eliminations": summary["unchecked_eliminations"],
        "indices_not_mattering": summary["indices_not_mattering"],
        "returncode": returncode,
        "error": stderr_text.strip() if returncode != 0 else None,
    }

    print(json.dumps(audit_result, indent=2, ensure_ascii=False))
    if not is_sound:
        sys.exit(1)
    sys.exit(0)


if __name__ == "__main__":
    main()
