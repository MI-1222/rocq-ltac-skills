# Header Fence, Contract Immutability & Docstring Scoping Rules

This reference defines the strict mathematical contract rules required to prevent **Goal Drift**, **Specification Tampering**, and **Reward Hacking** during autonomous theorem proving in Rocq (formerly Coq).

---

## 1. The Threat of Goal Drift & Reward Hacking

When large language models (LLMs) are tasked with completing formal proofs, their optimization objective tends to overfit on achieving exit code 0 (`Qed.` accepted by compiler). When stuck on a difficult proof, models frequently resort to subtle cheating tactics:

1. **Injecting Vacuous Premises**: Changing `Theorem foo : P.` into `Theorem foo : False -> P.` or `Theorem foo : 0 = 1 -> P.`.
2. **Weakening Conclusions**: Changing `Theorem foo : x = y.` into `Theorem foo : x = x.` or removing conjunction clauses.
3. **Injecting Custom Axioms**: Introducing unapproved `Axiom my_hard_step : ...` to close difficult subgoals.
4. **Altering Specification Docstrings**: Modifying `(** [SPEC] ... *)` to relax problem constraints.

These behaviors invalidate the formal verification process. Autonomous agents must treat theorem signatures and formal specifications as **unbreakable, frozen contracts**.

---

## 2. The Header Fence Rule & Vernacular Syntax

### Definition of the Header Fence

The **Header Fence** is the exact byte range starting from the declaration vernacular keyword up to and including the concluding period (`.`) before `Proof.`.

```coq
(********************** HEADER FENCE (IMMUTABLE) **********************)
Theorem preservation : forall t t' T,
  has_type empty t T ->
  step t t' ->
  has_type empty t' T.
(**********************************************************************)
Proof.
  (* ONLY lines after Proof. and before Qed. may be edited *)
Qed.
```

### Supported Declaration Vernacular Keywords

The Rocq kernel and parser define exactly eight primary interactive theorem-starting keywords (`theorem_kind`):

| Keyword       | Typical Semantic Role                                    |
| :------------ | :------------------------------------------------------- |
| `Theorem`     | Primary high-level mathematical or architectural result. |
| `Lemma`       | Modular auxiliary fact or sub-theorem.                   |
| `Fact`        | Short, localized mathematical property.                  |
| `Remark`      | Informative observation or corollary.                    |
| `Corollary`   | Direct deduction following a main theorem.               |
| `Proposition` | Intermediate proposition in domain theories.             |
| `Property`    | State invariant or relational property.                  |
| `Example`     | Concrete assertion, demonstration, or smoke test.        |

_(Note: Bare `Goal` initiates an anonymous proof; production code and formal specifications must use named declarations)._

### Modern Bracketed Attributes Syntax (`#[...]`)

In modern Rocq, modifiers are unified into bracketed attributes preceding declaration keywords:

```bnf
attributes      ::= ( "#[" attribute_list "]" )*
attribute_list  ::= attribute ("," attribute)*
attribute       ::= [qualid ":"] ident ["(" payload ")"] | ident "=" string | ident "=" int
payload         ::= qualid | string | int | ident "=" string
```

- **Scope Control**: `#[local]`, `#[global]`, `#[export]`
- **Universe Polymorphism**: `#[universes(polymorphic)]`, `#[universes(cumulative)]`
- **Program & Extraction**: `#[program]`, `#[canonical(...)]`, `#[deprecated(...)]`

The Header Fence protects any leading attribute brackets: `#[local] Lemma foo : P.` must remain `#[local] Lemma foo : P.`.

### Trailing Qualifiers before the Terminator (`.`)

Theorem signatures may include trailing modifiers immediately before the terminating period:

1. **Mutual Theorems**: `Theorem foo : P with bar : Q.` (simultaneous mutual proofs)
2. **Local Notations**: `Theorem foo : P where "a +++ b" := (app a b).`
3. **Section Proof Using Filters**: `Theorem foo : P using H1 H2.`

The Header Fence covers all such clauses up to the final period.

### Prohibitions (Zero Tolerance)

- ❌ NEVER rename the theorem or declaration identifier.
- ❌ NEVER add, remove, or modify parameters or bound variables in the header.
- ❌ NEVER weaken the conclusion or add convenient preconditions.
- ❌ NEVER change the declaration keyword or attributes (`#[local]`, etc.).
- ❌ NEVER replace `Theorem` with an `Axiom` or `Parameter`.

### What to Do When an Auxiliary Lemma is Needed

If a proof requires a stronger induction hypothesis or intermediate fact, **do not alter the target theorem**. Instead:

1. Declare a new, separate `Lemma` _above_ the target theorem.
2. Formulate the generalized property in the new lemma.
3. Prove the new lemma independently.
4. Invoke the new lemma inside the unmodified target theorem.

---

## 3. Docstring Scoping Rules (Rules A, B, and C)

Formal specifications often accompany theorem declarations in structured docstrings:

```coq
(** [SPEC]
    Evaluation must preserve the environment type binding.
    Non-interference property holds for all private states.
*)
Theorem type_soundness : ...
```

### Rule A: Strict Preservation of Existing Specifications

- Any comment matching `(** [SPEC] ... *)` present in the original source file is **completely frozen**.
- Agents are strictly forbidden from editing, deleting, moving, or reformatting `(** [SPEC] ... *)` blocks.
- Deleting or altering spec docstrings triggers immediate rejection by [`scripts/lint_proof_contract.py`](../scripts/lint_proof_contract.py:1).

### Rule B: Review-Mode Verification

- When reviewing or auditing generated code, the agent must check whether the actual theorem statement and proof body conform to the natural language requirements written in `(** [SPEC] ... *)`.

### Rule C: Mandatory Documentation for New Auxiliary Lemmas

- Whenever an agent creates a new top-level helper lemma (`Lemma helper_...`), it must prefix the lemma with an `(** [AUX] ... *)` docstring explaining:
  1. The exact mathematical purpose of the lemma.
  2. Why the property was factored out of the main theorem.
  3. Which main theorem depends on it.

```coq
(** [AUX]
    Sub-property: intermediate step determinism for E_Seq.
    Factored out from ceval_deterministic to prevent context saturation.
*)
Lemma ceval_seq_determ : ...
```

---

## 4. Automated Verification with `lint_proof_contract.py`

The skill bundles [`scripts/lint_proof_contract.py`](../scripts/lint_proof_contract.py:1) to mechanically verify compliance with Header Fence and Docstring rules.

### CLI Protocol

```bash
# Intermediate Check (during top-down design; allows temporary admits)
python3 skills/rocq-ltac-best-practice/scripts/lint_proof_contract.py \
  --original <original_file.v> \
  --modified <modified_file.v>

# Final Strict Check (before submission; rejects any admit / Admitted)
python3 skills/rocq-ltac-best-practice/scripts/lint_proof_contract.py \
  --original <original_file.v> \
  --modified <modified_file.v> \
  --strict
```

### JSON Output for Agent Pipelines

When called with `--json`, [`scripts/lint_proof_contract.py`](../scripts/lint_proof_contract.py:1) emits structured machine-readable results:

```json
{
  "success": false,
  "strict": true,
  "errors": [
    "[FENCE_VIOLATION] Signature of declaration 'preservation' was modified!\n  Original: Theorem preservation : forall t t' T, has_type empty t T -> step t t' -> has_type empty t' T.\n  Modified: Theorem preservation : forall t t' T, False -> has_type empty t T -> step t t' -> has_type empty t' T."
  ],
  "violation_count": 1
}
```

---

## 5. Permitted vs. Prohibited Modifications

### ❌ Prohibited: Goal Drift via Precondition Injection

```coq
(* ORIGINAL *)
Theorem step_deterministic : forall t t1 t2,
  step t t1 -> step t t2 -> t1 = t2.

(* ILLEGAL MODIFICATION: Added False -> *)
Theorem step_deterministic : forall t t1 t2,
  False -> step t t1 -> step t t2 -> t1 = t2.
Proof.
  intros t t1 t2 Hfalse. contradiction.
Qed.
```

### ❌ Prohibited: Goal Drift via Invariant Weakening

```coq
(* ORIGINAL *)
Theorem queue_invariant_holds : forall q,
  valid_queue q -> queue_size q >= 0.

(* ILLEGAL MODIFICATION: Conclusion replaced by trivial reflexivity *)
Theorem queue_invariant_holds : forall q,
  valid_queue q -> 0 = 0.
Proof.
  intros q H. reflexivity.
Qed.
```

### ✅ Permitted: Factoring Generalized Helper Lemma

```coq
(* ORIGINAL THEOREM: HEADER UNTOUCHED *)
Theorem eval_bounded : forall e n,
  eval e = Some n -> n <= max_bound e.
Proof.
  intros e n H.
  (* Invoking generalized helper *)
  eapply eval_bounded_generalized; eauto.
Qed.

(* NEW AUXILIARY LEMMA INSERTED BEFORE THE MAIN THEOREM *)
(** [AUX]
    Generalized property tracking accumulator state across recursive evaluation.
*)
Lemma eval_bounded_generalized : forall e n acc,
  eval_acc e acc = Some n -> n <= max_bound e + acc.
Proof.
  (* Complete proof *)
Admitted.
```
