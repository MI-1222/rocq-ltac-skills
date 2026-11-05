---
name: rocq-ltac-proof-repair
description: Deterministic error triage, goal state recovery, and minimal surgical proof repair for Rocq (formerly Coq) formal verification in Pure Vanilla Ltac. Use whenever a compilation, elaboration, or tactic fails (e.g., `Unable to unify`, `The term ... has type ... expected ...`, `Cannot guess decreasing argument of fix`, `inversion` hypothesis explosion, lost induction indices, `Cannot solve goal with lia`, `Wrong bullet`, `No matching clauses for match goal`, `Universe inconsistency`, `The reference ... was not found`), when proofs fail with unsolved goals or desynchronized bullets, when encountering suspected false lemmas needing falsification/disproof, or when recovering from tactic thrashing without breaking theorem header fences or admitting proofs.
compatibility: Target Rocq 9.0+ (Backward compatible with Coq 8.20).
metadata:
  target-prover: "Rocq 9.0+ / Coq 8.20"
  subsystem: "Error Triage & Proof Repair"
  language-dialect: "Pure Vanilla Ltac (100%)"
  version: "0.0.1"
---

# Rocq Ltac Proof Repair & Error Triage

This skill provides a deterministic 4-step repair protocol, a comprehensive error triage matrix, and specialized domain prescriptions for diagnosing and repairing broken proofs in Rocq (formerly Coq) using **Pure Vanilla Ltac**.

Autonomous theorem proving agents must never engage in blind trial-and-error or speculative tactic thrashing. When a vernacular command, tactic, or elaboration step fails, follow this protocol to isolate the exact error signature, inspect the active proof state, consult the relevant domain reference, and apply a surgical, minimally invasive patch while strictly preserving the theorem signature and kernel soundness.

---

## 0. Environment & Version Compatibility

| Component            | Target / Supported              | Notes                                                                                        |
| :------------------- | :------------------------------ | :------------------------------------------------------------------------------------------- |
| **Rocq Prover**      | `9.0+` (Default target)         | Uses unified `rocq` CLI, `From Corelib` / `From Stdlib Require Import ...`.                  |
| **Coq (Legacy)**     | `8.20` (Compatibility baseline) | Uses `From Coq Require Import ...`. Versions $\le 8.17$ are unsupported.                     |
| **Language Dialect** | **Pure Vanilla Ltac 100%**      | **SSReflect/MathComp syntax is strictly prohibited.** Dynamic Ltac2 generation is forbidden. |
| **Diagnostics Tool** | `parse_diagnostics.py`          | Provided by `rocq-ltac-cli` (`scripts/parse_diagnostics.py`) to parse build logs into JSON.  |
| **REPL Goal Tool**   | `rocq_goal.py`                  | Provided by `rocq-ltac-interactive-proof` (`scripts/rocq_goal.py`) to inspect subgoals.      |
| **Soundness Gate**   | `audit_axioms.py`               | Provided by `rocq-ltac-cli` (`scripts/audit_axioms.py`) to verify `Print Assumptions`.       |

---

## 1. Deterministic 4-Step Repair Protocol

```mermaid
graph TD
  A["Build/Tactic Failure"] --> B["Step 1: Parse & Match Signature"]
  B --> C["Step 2: Inspect Context via rocq_goal.py --line N"]
  C --> D{"Tactic Thrashing Check"}
  D -- "Goal Unchanged >= 2 Steps" --> E["Halt Thrashing: Consult falsification_and_disproof.md"]
  D -- "Fresh Failure" --> F["Step 3: Consult Triage Matrix & references/*.md"]
  F --> G["Step 4: Formulate Minimal Surgical Patch"]
  G --> H["Apply Patch & Run Tier 0 check_syntax.py"]
  H --> I["Compile & Verify Tier 1 rocq compile / Tier 2 dune"]
  I -- "Success (Qed)" --> J["Soundness Gate Tier 3: audit_axioms.py"]
  I -- "Fail" --> B
```

### Step 1: Parse & Match Error Signature

1. Run the build or extract the compiler error log via [`scripts/parse_diagnostics.py`](../rocq-ltac-cli/scripts/parse_diagnostics.py:1) in `rocq-ltac-cli`.
2. Identify:
   - The failing source file and exact line number ($N$).
   - The raw compiler error message and normalized error code.
3. Match the raw error text against the [Core Triage Matrix](#2-core-triage-matrix).

### Step 2: Context & Goal State Inspection

Before modifying the script, obtain the precise proof state immediately prior to the failing command:

```bash
python3 skills/rocq-ltac-interactive-proof/scripts/rocq_goal.py --file <file.v> --line <N-1> --json
```

Examine:

- **Focused Goal Target**: What term or equality must be established?
- **Hypotheses & Types**: Are hypotheses transparent or folded? Are inductive indices abstracted or specialized?
- **Unification Roadblocks**: Do types match definitionally ($\beta\iota\zeta\delta$-reduction) or only propositionally?

### Step 3: Reference Consultation

Read the specialized reference document mapped to the diagnosed error category in `references/`:

- Do not invent speculative tactics.
- Adopt the canonical Before / After prescription patterns detailed in the respective reference file.

### Step 4: Minimal Invasive Patching & Verification Ladder

1. **Surgical Scope**: Replace only the failing tactic or focused subproof block. Keep surrounding proofs intact.
2. **Tier 0 Syntax Gate**: Run `check_syntax.py` to ensure no SSReflect tokens, bad terminators, or broken comments were introduced.
3. **Tier 1 Fast File Gate**: Recompile the single file (`rocq compile -color no <file.v>` or `coqc`).
4. **Tier 3 Soundness Gate**: When `Qed` is reached, verify proof soundness using `audit_axioms.py` to ensure no unapproved axioms (e.g., Axiom K / `Eqdep.Eq_rect_eq.eq_rect_eq`) or `Admitted` proofs exist.

---

## 2. Core Triage Matrix

| Error Signature Pattern                                                    | Category            | Root Cause                                                                            | Immediate Vanilla Ltac Action                                                                      | Specialized Reference                                                                  |
| :------------------------------------------------------------------------- | :------------------ | :------------------------------------------------------------------------------------ | :------------------------------------------------------------------------------------------------- | :------------------------------------------------------------------------------------- |
| `Unable to unify "(.*)" with "(.*)"`                                       | Unification         | Definitional mismatch; unreduced definitions; `Prop` vs `bool` confusion              | Run `cbn`, `unfold def in *`, `change`, or use reflection lemma (`apply Nat.eqb_eq in H`)          | [`references/unification_and_types.md`](references/unification_and_types.md)           |
| `The term "(.*)" has type "(.*)" while it is expected to have type "(.*)"` | Type Mismatch       | Mismatched sorts; implicit argument deduction failure                                 | Explicitly supply type parameters with `@lemma` or bridge with equivalence/reflection lemma        | [`references/unification_and_types.md`](references/unification_and_types.md)           |
| `Found no subterm matching "(.*)" in "(.*)"`                               | Rewrite Failure     | Subterm not syntactically or definitionally present in target/hypothesis              | `unfold` target symbols first; use `setoid_rewrite` or `remember` to align terms                   | [`references/unification_and_types.md`](references/unification_and_types.md)           |
| `Cannot guess decreasing argument of fix`                                  | Termination         | Non-syntactic recursion; nested calls or accumulator parameters                       | Add explicit `{struct arg}` annotation or switch to `Program Fixpoint ... {measure ...}`           | [`references/termination_and_wf.md`](references/termination_and_wf.md)                 |
| `Recursive call .* has argument .* which is not structurally smaller`      | Termination         | Argument modified by function (e.g., `div`, `tail`) before recursive call             | Formulate well-founded induction via `well_founded_induction` or `Program Fixpoint`                | [`references/termination_and_wf.md`](references/termination_and_wf.md)                 |
| Context cluttered with `H0, H1, H2...` after `inversion`                   | Inversion Explosion | Bare `inversion H.` leaves redundant equalities and stale hypotheses                  | Replace bare `inversion H.` with `inversion H; subst; clear H.`                                    | [`references/inversion_and_equality.md`](references/inversion_and_equality.md)         |
| `dependent destruction` introduced Axiom K                                 | Axiom Contamination | Dependent inversion quietly introduced `Eqdep.Eq_rect_eq.eq_rect_eq`                  | Replace `dependent destruction` with `remember ... as x eqn:E` + `revert` + `induction`            | [`references/inversion_and_equality.md`](references/inversion_and_equality.md)         |
| Induction on indexed type lost index values                                | Induction Drift     | Applying `induction` directly on complex inductive relations (e.g., `step (EIf ...)`) | Apply `remember <term> as x eqn:Heqx` and `revert` dependencies before `induction`                 | [`references/induction_and_remember.md`](references/induction_and_remember.md)         |
| `Cannot solve goal with lia`                                               | Arithmetic Failure  | Truncated `nat` subtraction (`a - b = 0`), non-linear terms, or uncast `Z`            | Introduce case split (`Nat.le_gt_cases a b`), normalize with `zify`, or isolate non-linear factors | [`references/tactic_failures.md`](references/tactic_failures.md)                       |
| `congruence failed` / `tauto failed`                                       | Tactic Failure      | Constructor distinctness requires explicit inversion; unexpanded logical connectives  | Use `destruct ... eqn:...`, `discriminate`, or `injection ... as ...`                              | [`references/tactic_failures.md`](references/tactic_failures.md)                       |
| `No matching clauses for match goal`                                       | Ltac Automation     | Match pattern missed a goal form; strict pattern failure raised level                 | Add wildcard fallback `\| _ => idtac` or use `try` / `lazymatch` appropriately                     | [`references/tactic_failures.md`](references/tactic_failures.md)                       |
| `The reference (.*) was not found in the current environment`              | Namespace & Scope   | Rocq 9.0+ split (`Corelib`/`Stdlib`); missing `Require Import`; missing scope         | Use `From Stdlib Require Import ...`; open required scope (`Open Scope Z_scope.`)                  | [`references/namespace_and_imports.md`](references/namespace_and_imports.md)           |
| `Universe inconsistency: Cannot enforce (.*)`                              | Universe            | Self-referential quantification; pushing high-order types into `Set`                  | Promote sort to `Type`, declare `Polymorphic Definition`, or stratify data representation          | [`references/universe_inconsistencies.md`](references/universe_inconsistencies.md)     |
| `Wrong bullet (.*): Bullet (.*) is mandatory here`                         | Bullet Focus        | Desynchronized bullet depth (`-`, `+`, `*`); unclosed sibling goal                    | Realign bullet nesting level or isolate subgoals within `{ ... }` curly braces                     | [`references/bullet_and_focus.md`](references/bullet_and_focus.md)                     |
| Same goal persists after 2 consecutive edits                               | Tactic Thrashing    | Agent trapped in trial-and-error; goal might be logically unprovable (false)          | **HALT edits immediately.** Trigger the 3-phase Falsification Protocol                             | [`references/falsification_and_disproof.md`](references/falsification_and_disproof.md) |

---

## 3. Strict Soundness Invariants & Anti-Cheating Gates

To guarantee that repaired proofs are valid, robust, and mechanically trustworthy, enforce the following non-negotiable invariants:

1. **Header Fence Immutability (Zero Goal Drift)**:
   - The theorem signature, premise sequence, argument names, and return type MUST NOT be altered under any circumstances.
   - Inserting `False ->`, trivializing the conclusion to `True`, or adding ad-hoc hypothesis assumptions constitutes fatal Goal Drift and is rejected by the Tier 0 checker.
2. **Zero Cheat Tactics**:
   - `admit`, `Admitted.`, `give_up`, and placeholder macros like `FILL_IN_HERE` are strictly forbidden in final code.
   - Introducing external `Axiom` or `Parameter` declarations to bypass intermediate lemmas is prohibited.
3. **Pure Vanilla Ltac (Zero Dialect Contamination)**:
   - Never introduce SSReflect syntax (`move=>`, `by []`, `have:`, `//`, `congr`) or dynamic Ltac2 expressions during repair. All repair patches must be 100% Vanilla Ltac.
4. **Tactic Thrashing Budget (Max 2 Attempts)**:
   - If two consecutive tactic modifications produce the identical goal state (hypotheses and conclusion fingerprint unchanged), the agent must stop guessing tactics.
   - Check if an intermediate helper lemma is false using concrete execution (`Compute`) or refutation before spending further tokens.
5. **Kernel Soundness Audit (Tier 3 Gate)**:
   - Every completed repair must be validated with `audit_axioms.py` (`Print Assumptions <Thm>`).
   - The proof must resolve to `Closed under the global context` (or only approved project axioms such as `functional_extensionality_dep`). Any detection of `Eqdep.Eq_rect_eq.eq_rect_eq` (Axiom K) from careless dependent inversion causes immediate rejection.

---

## 4. Specialized Reference Guides

Consult these dedicated documents for detailed explanations, failure mechanisms, and full Before / After examples:

- [`references/unification_and_types.md`](references/unification_and_types.md): Resolving definitional mismatches, $\beta\iota\zeta\delta$-reduction (`cbn`, `unfold`, `change`), `bool` vs `Prop` reflection, and implicit arguments (`@lemma`).
- [`references/induction_and_remember.md`](references/induction_and_remember.md): Preventing index loss on inductive relations with `remember ... as x eqn:Heqx`, `revert` dependencies, and mutual induction schemes.
- [`references/inversion_and_equality.md`](references/inversion_and_equality.md): Preventing context explosion (`inversion; subst; clear`), avoiding Axiom K from `dependent destruction`, and manual constructor decomposition (`injection`, `discriminate`).
- [`references/termination_and_wf.md`](references/termination_and_wf.md): Resolving `Cannot guess decreasing argument`, `{struct}` annotations, well-founded recursion, and `Program Fixpoint` with `measure`.
- [`references/tactic_failures.md`](references/tactic_failures.md): Fixing `lia` arithmetic failures on `nat` subtraction, `zify` normalization, `congruence`/`tauto` breakdowns, and Ltac `match goal` failure level handling.
- [`references/namespace_and_imports.md`](references/namespace_and_imports.md): Migrating namespaces from `Coq` to `Stdlib` in Rocq 9.0+, managing missing scopes (`Z_scope`), and resolving undefined identifiers.
- [`references/falsification_and_disproof.md`](references/falsification_and_disproof.md): Breaking tactic thrashing loops through 3-phase falsification: `Compute` boundary testing, explicit refutation (`Lemma counter : ~ Target`), and precondition strengthening.
- [`references/universe_inconsistencies.md`](references/universe_inconsistencies.md): Diagnosing `Universe inconsistency`, handling universe levels, applying `Polymorphic` attributes, and stratifying higher-order structures.
- [`references/bullet_and_focus.md`](references/bullet_and_focus.md): Fixing `Wrong bullet` errors, mastering bullet hierarchies (`-`, `+`, `*`), and isolating proof branches with `{ ... }` blocks.
