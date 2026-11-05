# Rocq Ltac Skills

English | [日本語](README.md)

A suite of skills designed for AI coding agents to autonomously perform formal verification in computer science (programming language semantics, type systems, compiler correctness, and error repair) using Rocq (formerly Coq) and Pure Vanilla Ltac.

## Features

- **Specialized in Formal Proving & Computer Science**: Focused on programming language semantics (Operational Semantics), type safety proofs (Progress / Preservation), step-indexing, and compiler verification (Software Foundations, CompCert, Iris styles) rather than general mathematics.
- **100% Strict Pure Vanilla Ltac Compliance**: Actively prevents dialect confusion and SSReflect contamination (`move=>`, `by []`, etc.) or Ltac2 constructs via static linting and strict conventions.
- **Rocq REPL Interaction Loop**: Interacts with `rocq repl` / `coqtop` subprocesses via standard I/O to inspect proof goals (Tactic State) and local hypotheses step-by-step. Supports QuickChick counterexample search and type signature queries (`Search`).
- **Zero External Dependencies**: All bundled scripts rely exclusively on the Python 3 standard library (`subprocess`, `json`, `argparse`). No third-party packages required.
- **Contract Invariance & Soundness Gates**: Mechanically prevents unauthorized alterations of theorem statements, stray `admit` / `Admitted` tactics, or introduction of unapproved axioms.

## Prerequisites & Compatibility

| Component                | Target / Supported             | Verified / Tested Version              | Notes                                                                                     |
| :----------------------- | :----------------------------- | :------------------------------------- | :---------------------------------------------------------------------------------------- |
| **Rocq Prover / Coq**    | `Rocq 9.0+` / `Coq 8.20+`      | `The Rocq Prover 9.1.0` (OCaml 4.14.2) | Supports both modern Rocq 9.0+ namespaces (`From Stdlib`) and legacy Coq 8.x (`From Coq`) |
| **Build Systems / Dune** | `dune` (`>=3.10`), `rocq make` | Dune `3.21.0`                          | Automatically resolves `_RocqProject` and `_CoqProject`                                   |
| **Python**               | `>=3.10`                       | `3.14.7`                               | Standard library only (required for script-bundled skills)                                |

## Skills Overview

| Skill                                                               | Description                                                                                                                                             | Bundled Scripts / References                                                      |
| :------------------------------------------------------------------ | :------------------------------------------------------------------------------------------------------------------------------------------------------ | :-------------------------------------------------------------------------------- |
| [`rocq-ltac-interactive-proof`](skills/rocq-ltac-interactive-proof) | Interacts with `rocq repl` / `coqtop` to fetch proof goals (Tactic State) and hypotheses                                                                | `scripts/rocq_goal.py`, `references/*.md` (3 guides)                              |
| [`rocq-ltac-proof-repair`](skills/rocq-ltac-proof-repair)           | Diagnoses and repairs common compiler errors (inversion equality conflicts, inductive index loss via `remember`, termination, universe inconsistencies) | `references/*.md` (9 diagnostic guides)                                           |
| [`rocq-ltac-syntax`](skills/rocq-ltac-syntax)                       | Proof syntax reference and fast static syntax check (prevents SSReflect contamination)                                                                  | `scripts/check_syntax.py`, `references/*.md` (5 guides)                           |
| [`rocq-ltac-cli`](skills/rocq-ltac-cli)                             | Automates `rocq` / `coqc` / `dune` commands, parses build logs into structured JSON, and audits axioms (Soundness Gate)                                 | `scripts/run_build.py`, `scripts/parse_diagnostics.py`, `scripts/audit_axioms.py` |
| [`rocq-ltac-best-practice`](skills/rocq-ltac-best-practice)         | Top-down proof workflow, destructive inversion macro (`inv`), contract invariance (header fences), and tactic automation hierarchies                    | `scripts/lint_proof_contract.py`, `references/*.md` (7 guides)                    |

## Installation

Download the latest `rocq-ltac-skills.zip` from [Releases](https://github.com/MI-1222/rocq-ltac-skills/releases), and extract it into your project or agent workspace's `skills/` directory.

Each skill folder (`skills/<skill-name>/`) contains a standardized agent specification file (`SKILL.md`).

## Directory Structure

```text
skills/
├── rocq-ltac-interactive-proof/  # Interactive goal inspection & REPL integration
├── rocq-ltac-proof-repair/       # Error triage and fix prescriptions
├── rocq-ltac-syntax/             # Syntax checking & dialect conventions
├── rocq-ltac-cli/                # Build commands, log parsing & axiom auditing
└── rocq-ltac-best-practice/      # Proving methodology & contract invariance
```

## License

[MIT License](LICENSE)
