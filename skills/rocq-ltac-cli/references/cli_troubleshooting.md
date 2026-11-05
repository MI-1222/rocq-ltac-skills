# Rocq CLI & Build Troubleshooting Guide

This document provides error diagnostics, root-cause analyses, and concrete recovery steps for common failure modes encountered during Rocq (formerly Coq) CLI compilation, build execution, and Software Foundations testing pipelines.

---

## 1. Exit Code Conventions

| Exit Code | Source                               | Meaning & Root Cause                                                                             |
| :-------: | :----------------------------------- | :----------------------------------------------------------------------------------------------- |
|  **`0`**  | Rocq / Dune / Make                   | Successful execution.                                                                            |
|  **`1`**  | `rocq compile` / `CErrors.exit_code` | User error, syntax error, type unification failure, multiple input files, or QuickChick failure. |
| **`124`** | `scripts/run_build.py`               | Command execution timed out. Process group terminated with `SIGKILL`.                            |
| **`127`** | OS / Shell                           | Command binary (`rocq`, `dune`, `ocamlfind`, `quickChick`) not found on system PATH.             |
| **`129`** | Rocq Kernel (`cErrors.ml`)           | **Anomaly**. Internal compiler bug, unhandled exception, or stack overflow.                      |

---

## 2. Common Build Failures & Remedies

### 2.1. `More than one file to compile: ... and ...`

- **Source**: `toplevel/coqcargs.ml` (`add_compile`)
- **Cause**: Multiple `.v` source files were passed to a single `rocq compile` or `coqc` invocation.
- **Remedy**:
  - `rocq compile` accepts **strictly one** target file per execution.
  - Compile files individually, or execute project builds via `dune build` or `make -f Makefile.coq`.

### 2.2. `Cannot find a physical path bound to logical path ... with prefix Stdlib`

- **Cause**: Dune project targeting Rocq 9.0+ lacks `Stdlib` in its theory dependencies.
- **Remedy**:
  - Add `(theories Stdlib Corelib)` to the `(coq.theory ...)` stanza in the relevant `dune` file:
  ```lisp
  (coq.theory
   (name MyProject)
   (theories Stdlib Corelib))
  ```

### 2.3. `Cannot find a physical path bound to logical path ...`

- **Cause**: Mismatch between `_CoqProject` bindings (`-Q` / `-R`) and import statements (`From Prefix Require Import ...`), or build executed outside the project root.
- **Remedy**:
  - Ensure working directory is the project root containing `_CoqProject`.
  - If `theories/` is mapped via `-Q theories MyProject`, import modules with `From MyProject Require Import Core.`.
  - For Software Foundations sibling volumes (e.g., building PLF that imports LF), verify that `-Q ../lf LF` is declared in `_CoqProject`.

### 2.4. Tactic Timeout or Process Hang (Exit Code 124)

- **Cause**: Backtracking search in `lia`, `nia`, `auto 10`, `eauto with *`, `repeat`, or heavy unification in `dependent destruction` exceeded execution deadlines.
- **Remedy**:
  - `scripts/run_build.py` terminates the entire process group with `SIGKILL`.
  - Isolate the stalling tactic by stepping through proofs interactively via `rocq-ltac-interactive-proof` (`rocq_goal.py`).
  - Constrain search depth (e.g., `auto 3` instead of `auto 10`) or supply explicit intermediate lemmas with `assert` and `apply`.

### 2.5. Compiler Anomaly (Exit Code 129: `Anomaly: ... Please report`)

- **Cause**: Kernel stack overflow, cyclic type definitions, or internal compiler defects.
- **Remedy**:
  - Expand recursion stack limit: `ulimit -s unlimited`.
  - Simplify deeply nested recursive functions or compute tactics (`vm_compute`, `native_compute`).
  - Revert recent changes and isolate the offending vernac command.

### 2.6. `_CoqProject` Tokenization Errors

- **Error**: `Parsing_error ("Invalid value for -arg, unpaired single quote...")`
- **Cause**: Mismatched or unclosed single quote in an `-arg` line.
- **Remedy**:
  - Verify that quotes in `_CoqProject` are properly balanced:
  ```text
  # Valid format
  -arg "-w -deprecated-from-Coq -color no"
  ```

---

## 3. Software Foundations Specific Failure Modes

### 3.1. `Type: wrong - expected ...` or `Missing: <ident>` in `*Test.v`

- **Cause**: In SF exercises, `*Test.v` uses `unify` via `check_type` to verify that the student did not alter lemma signatures or omit exercises.
- **Remedy**:
  - Compare your theorem header with the clean textbook template.
  - Never modify binders, parameter names, or return types (Goal Drift).
  - If `Missing:` is reported, ensure the definition or lemma identifier is spelled exactly as specified.

### 3.2. QuickChick Property Failure (`*** Failed!`)

- **Cause**: In the QC volume, `QuickCheck <prop>.` is evaluated during `coqc` compilation. If a randomized counterexample is found:
  ```text
  QuickChecking prop_bad_reverse...
  *** Failed!
  [0; 1]
  (after 4 tests and 2 shrinks)
  ```
  `coqc` immediately terminates with exit code `1`.
- **Remedy**:
  - Examine the shrunk counterexample printed in stdout (e.g., `[0; 1]`).
  - Correct the underlying definition or refine the proposition's precondition (e.g., using conditional implication `==>`).
  - Use `quickChick -color <file.v>` to re-test locally without running the entire proof suite.

### 3.3. OCaml Extraction Compilation Errors (LF & VFA)

- **Symptom 1: Unused Variable Warnings Treated as Errors**
  - **Cause**: Coq's extraction erasure pass generates auxiliary variables that OCaml's compiler warns against (`Error (warning 20): this argument will not be used`).
  - **Remedy**: Ensure `ocamlc` / `ocamlopt` invocations include `-w -20 -w -26`.
- **Symptom 2: Unbound value or type mismatch with driver**
  - **Cause**: `Extract Inductive` mapping does not match the external driver's expectations (e.g., extracting `nat` to `int` vs `Big_int`).
  - **Remedy**: Check `Extract.v` to ensure inductive mappings match the driver's interface types.

### 3.4. TLC / VST Path Resolution Failures (SLF & VC)

- **Symptom: `Cannot find a physical path bound to logical path TLC`**
  - **Cause**: `coq-tlc` is not installed via opam, and the local `./tlc` folder is missing or uncompiled.
  - **Remedy**: Run `opam install coq-tlc`, or ensure the fallback `-Q ./tlc TLC` is configured in `Makefile` and that `./tlc` contains compiled `.vo` files.
- **Symptom: `Cannot find a physical path bound to logical path VST`**
  - **Cause**: Environment variable `VST_LOC` is unset.
  - **Remedy**: Set `export VST_LOC=$(opam var coq-vst:lib)` before invoking `make`.
