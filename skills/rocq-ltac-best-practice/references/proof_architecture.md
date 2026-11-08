# Proof Architecture, Top-Down Decomposition & Lemma Lifecycle

This reference guides autonomous theorem proving agents in structuring scalable, modular, and maintainable proofs in Rocq (formerly Coq) using **Pure Vanilla Ltac**.

---

## 1. The Monolithic Proof Trap (The 30-Line Rule)

### The Anti-Pattern

Autonomous agents often attempt to prove high-level theorems inside a single, monolithic `Proof ... Qed.` block exceeding 100 lines. This inevitably causes:

1. **Context Window Saturation**: Sibling subgoals generate dozens of intermediate hypotheses, obscuring relevant premises.
2. **Attention Drift & Hallucination**: The model loses track of which branch it is solving, conflating induction hypotheses.
3. **Catastrophic Backtracking**: A broken tactic at line 85 requires re-evaluating the preceding 84 lines in every iteration.

### The Architectural Mandate

- **Strict Size Limit**: Keep individual proof blocks under **30 lines** (absolute maximum: 50 lines).
- **Branching Trigger**: If an `induction` or `destruct` creates $\ge 3$ branches where any single branch requires $\ge 15$ lines of non-trivial reasoning, immediately factor that branch out into an independent top-level `Lemma`.
- **Single Responsibility Principle**: Each lemma should establish exactly one semantic property (e.g., determinism of sequential execution, substitution preserves typing, or inversion of evaluation).

---

## 2. Top-Down (Admit-Driven) Architecture

Top-down proving designs the high-level roadmap first before sinking time into complex low-level subgoals.

### The 4-Stage Top-Down Workflow

```mermaid
graph TD
  A["Main Theorem Goal"] --> B["Stage 1: Outline Roadmap with Standalone Lemma Signatures"]
  B --> C["Stage 2: Close Main Theorem using Lemma Calls (with temporary admit)"]
  C --> D["Stage 3: Prove Extracted Lemmas Independently"]
  D --> E["Stage 4: Eliminate All Admits and Verify with lint_proof_contract.py"]
```

### Step-by-Step Implementation

Given a complex evaluation determinism theorem:

```coq
(* Target Theorem *)
Theorem ceval_deterministic : forall c st st1 st2,
  ceval c st st1 ->
  ceval c st st2 ->
  st1 = st2.
```

#### Step 1: Identify and Declare Auxiliary Lemmas (with `admit`)

Before filling the induction details of `ceval_deterministic`, identify the hardest branch (e.g., sequence composition `E_Seq`):

```coq
(** [AUX] Helper lemma establishing intermediate state uniqueness for sequencing *)
Lemma ceval_seq_intermediate : forall c1 c2 st st1 st2 st1' st2',
  ceval c1 st st1 ->
  ceval c1 st st2 ->
  (st1 = st2 -> ceval c2 st1 st1' -> ceval c2 st2 st2' -> st1' = st2') ->
  ceval c2 st1 st1' ->
  ceval c2 st2 st2' ->
  st1' = st2'.
Proof.
  (* Temporarily admitted during Stage 1 *)
  admit.
Admitted.
```

#### Step 2: Assemble the Main Proof Skeleton

Close the primary theorem using helper calls and trivial case dispatch:

```coq
Ltac inv H := inversion H; subst; clear H.

Theorem ceval_deterministic : forall c st st1 st2,
  ceval c st st1 ->
  ceval c st st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 H1.
  generalize dependent st2.
  induction H1; intros st2 H2; inv H2.
  - (* E_Skip *) reflexivity.
  - (* E_Asgn *) reflexivity.
  - (* E_Seq *)
    eapply ceval_seq_intermediate; eauto.
  - (* E_IfTrue *) eapply IHceval; eauto.
  - (* E_IfFalse *) eapply IHceval; eauto.
  - (* E_WhileFalse *) reflexivity.
  - (* E_WhileTrue *) eapply IHceval2; eauto.
Qed.
```

#### Step 3: Implement and Discharge the Auxiliary Lemma

Return to `ceval_seq_intermediate` and prove it in isolation:

```coq
(** [AUX] Helper lemma establishing intermediate state uniqueness for sequencing *)
Lemma ceval_seq_intermediate : forall c1 c2 st st1 st2 st1' st2',
  ceval c1 st st1 ->
  ceval c1 st st2 ->
  (st1 = st2 -> ceval c2 st1 st1' -> ceval c2 st2 st2' -> st1' = st2') ->
  ceval c2 st1 st1' ->
  ceval c2 st2 st2' ->
  st1' = st2'.
Proof.
  intros c1 c2 st st1 st2 st1' st2' Hc1_1 Hc1_2 Hcont Hc2_1 Hc2_2.
  assert (Heq: st1 = st2).
  { (* Direct invocation or smaller property *)
    admit. (* Replace with concrete proof *) }
  apply (Hcont Heq Hc2_1 Hc2_2).
Admitted.
```

---

## 3. Local Lemmas: Choosing between `assert`, `enough`, and `pose proof`

When proof logic is small ($\le 10$ lines) and tightly coupled to the local context, use local assertion tactics rather than top-level lemmas:

| Tactic                  | Direction          | Local Transformation                                                | Best Use Case                                                  |
| :---------------------- | :----------------- | :------------------------------------------------------------------ | :------------------------------------------------------------- |
| `assert (H : P)`        | **Forward**        | Creates subgoal `⊢ P` first, then adds `H : P` to hypotheses        | Proving a known fact or intermediate equation before using it. |
| `assert (H : P) by tac` | **Inline Forward** | Solves `P` with `tac` immediately and adds `H : P` without subgoals | Quick arithmetic (`lia`), symmetry, or type deduction.         |
| `enough (H : P)`        | **Backward**       | Goal becomes `⊢ P -> Target`, followed by subgoal `⊢ P`             | Reframing goal in terms of a sufficient prerequisite.          |
| `pose proof term as H`  | **Instantiate**    | Adds existing lemma instantiated with local variables to hypotheses | Specializing a generic library theorem for local use.          |

---

## 4. Temporary `admit` / `Admitted` Lifecycle Management

To prevent reward hacking and unproven code leaks:

1. **Phase 1 (Exploration)**: `admit.` and `Admitted.` are permitted **only** during initial top-down skeleton drafting.
2. **Phase 2 (Proving)**: Replace every `admit.` with an actual proof. Never leave unresolved admits inside `{ ... }` blocks.
3. **Phase 3 (Submission Gate)**:
   - Run `python3 skills/rocq-ltac-best-practice/scripts/lint_proof_contract.py --original <orig.v> --modified <mod.v> --strict` (pass `--allow-new-specs` if adding new lemmas/specifications incrementally).
   - If ANY `admit` or `Admitted` remains, the linter exits with code `1` and aborts submission.
4. **Circular Assertion Trap**:
   ```coq
   (* FORBIDDEN CHEAT: Circular assert-admit trick *)
   Theorem fake_proof : forall P, P.
   Proof.
     intros P.
     assert (H: P). { admit. }
     apply H.
   Admitted. (* Rejected by strict linter! *)
   ```

---

## 5. Atomic Destruction Hygiene (`inv H`) & Inversion Mechanics

### A. The Non-Deterministic Numbering Trap in `inversion`

Bare `inversion H.` invokes internal fresh identifier generators (`fresh_id_in_env`), producing default names `H0`, `H1`, `H2`, ...:

- Because these index numbers depend on whatever identifiers currently reside in the local environment, subsequent tactic lines that reference `H0` or `H1` by name are brittle and fail when earlier proof steps change.
- Bare `inversion` leaves both the redundant generated equality hypotheses and the consumed original hypothesis `H` in the context, rapidly saturating memory.

### B. The Atomic Destruction Macro

Always define and use the atomic destruction idiom:

```coq
Ltac inv H := inversion H; subst; clear H.
```

Executing `inv H` guarantees:

1. All newly exposed equalities `x = e` are substituted throughout the goal and hypotheses via `subst`.
2. The obsolete hypothesis `H` is cleared immediately, keeping the local context minimal.

### C. Strict Failure Modes of `subst` & Alternative Idioms

When `subst` fails during `inv H`, it is almost always caused by one of three internal constraints:

1. **Occurs-Check Failure (`occur_var`)**: Variable `x` appears freely inside its substituted value `e` (e.g., $x = f(x)$). Substitution would trigger infinite expansion, throwing `Cannot remove x because it occurs in its value`.
2. **Dependency Topological Cycles**: Variable `x` is depended on by another hypothesis $H_i$, which in turn is depended on by the equation defining `x`.
3. **Dependent Inductive Indices**: The equality relates non-variable indices of dependent types, requiring heterogeneous equality (John Major's Equality) rather than standard Leibniz equality.

#### Prescriptions for Inversion Failures

- **For Dependent Inversions**: Switch to `dependent destruction H` (from `From Stdlib Require Import Program.Equality.`) or use the `remember ... as ... eqn:... in H` idiom before `destruct H`.
- **For Simple Injective Constructors**: Prefer `injection H as ->` or `injection H; intros; subst` over full `inversion` to avoid generating intermediate equations altogether.

---

## 6. Automated Refutation & Contradiction Search (`solve_by_inversion`)

In inductive relations with many constructors (such as operational semantics transitions or typing rules), multiple subgoals are syntactically generated that are impossible under the current hypotheses (e.g., trying to step a known value `value v` and `v --> v'`).

### The Failsafe `solve_by_inversion` Macro

Rather than manually guessing which hypothesis holds the contradiction, use the fail-safe search pattern:

```coq
Ltac solve_by_inversion_subst tac :=
  match goal with
  | H : ?T |- _ =>
      solve [
        inversion H; subst; tac
      ]
  end.

Ltac solve_by_inversion :=
  solve_by_inversion_subst idtac.

Ltac solve_by_inverts :=
  solve_by_inversion.
```

### Why the `solve [...]` Primitive is Safe:

1. **Atomic Success Mandate**: The `solve [ ... ]` tactical succeeds **only** if the inner tactics completely solve and close the current subgoal. If any unproved subgoals remain, `solve` fails immediately.
2. **Backtracking Hypothesis Scan**: When `solve` fails on a particular hypothesis `H`, `match goal with` automatically backtracks and binds the next hypothesis in the context.
3. **No False Discard**: It will never leave a half-destructed, polluted context behind if a hypothesis is not contradictory.

---

## 7. Verification Before Proof: Property-Based Testing Integration

The most expensive failure mode for theorem proving agents is spending hundreds of tokens and compute cycles attempting to prove a **false theorem** (e.g., an inductive lemma where a crucial precondition such as `BST t` or `closed t` was omitted).

### The PBT Pre-Verification Workflow

When formulating a non-trivial theorem or auxiliary invariant:

1. **Test Decidable Properties First**:
   Convert propositions to executable boolean checks using decidability reflection (`reflect` or `Decidable` typeclasses):
   ```coq
   Class Decidable (P : Prop) := {
     decide : bool;
     decide_spec : decide = true <-> P
   }.
   ```
2. **Generate Bounded Test Cases**:
   Define random generators (`Gen`) and shrinkers (`Shrink`). Always enforce a size bound (`sized gen`) on recursive generators to prevent stack overflow during testing:
   ```coq
   Instance gen_tree : Gen tree := {
     arbitrary :=
       let fix gen_t (size : nat) : G tree :=
         match size with
         | O => ret E
         | S size' =>
             freq [ (1, ret E);
                    (3, liftM4 T (gen_t size') arbitrary arbitrary (gen_t size')) ]
         end
       in sized gen_t
   }.
   ```
3. **Fail-Fast Counterexample Discovery**:
   Running a property check beforehand exposes counterexamples in milliseconds, allowing the agent to refine lemma premises _before_ committing to a formal proof attempt.

---

## 8. Modeling & Specification Records: The Sort Constraint (`Prop` vs `Type`/`Set`)

When structuring domain models, serialized layouts, or relational contracts via Gallina `Record` definitions, autonomous agents must respect Rocq's sort elimination constraints.

### 8.1. The Informative Field Elimination Trap

By default, users often declare relational records in `Prop`:

```coq
(* ❌ BROKEN: Record declared in Prop with computational data fields *)
Record serialized_entry (bytes : slice u8) : Prop := mk_entry {
  ser_payload_len : u8;    (* Informative: u8 : Set / Type *)
  ser_total_len   : usize; (* Informative: usize : Set / Type *)
  ser_valid       : is_valid_entry bytes
}.
```

Under Rocq's extraction and information erasure rules (the _singleton elimination restriction_), computational data cannot be projected out of a `Prop` unless the inductive type has at most one constructor whose arguments are all non-informative. Consequently, Rocq emits:

```text
Warning: ser_payload_len cannot be defined because it is informative and
serialized_entry is not. [cannot-define-projection,records,default]
```

Because projections are suppressed, field accessor expressions (such as `ser_payload_len e`) trigger immediate compilation failures in downstream lemmas:

```text
Error: The reference ser_payload_len was not found in the current environment.
```

### 8.2. Prescribed Modeling Discipline

1. **Sort Rule for Data-Bearing Records**:
   Whenever a record contains any computational values, length counters, byte buffers, or state objects inhabiting `Type` or `Set`, **always declare the record in `Type`** (or `Set`):
   ```coq
   (* ✅ CORRECT: Declared in Type to generate all field projections *)
   Record serialized_entry (bytes : slice u8) : Type := mk_entry {
     ser_payload_len : u8;
     ser_total_len   : usize;
     ser_valid       : is_valid_entry bytes
   }.
   ```
2. **Pure Logical Records in `Prop`**:
   Declare `Record ... : Prop` **only** when every field is itself a proposition (`P : Prop`, equalities `x = y`, validity invariants).
