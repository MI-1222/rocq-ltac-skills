# Unification, Type Mismatches & Reduction

This reference guides the diagnosis and repair of unification failures, sort mismatches (`Prop` vs `bool`), unreduced transparent definitions, and missing explicit arguments in Rocq 9.0+ and Coq 8.20.

---

## 1. Error Signatures

### Signature A: Definitional Unification Failure

```text
Error: In environment
n : nat
H : double n = 0
Unable to unify "0" with "n + n".
```

or with an explicit elaboration reason:

```text
Error: Unable to unify "x + y" with "y + x" because CannotUnify.
```

- **Polarity Rule**: In `Unable to unify "actual" with "expected".`, the left-hand term `"actual"` is the term or lemma conclusion supplied by the applied tactic, while the right-hand term `"expected"` is the target type expected by the active goal or binding.

### Signature B: Sort / Type Mismatch

```text
Error: In environment
x, y : nat
H : (x =? y) = true
The term "H" has type "(x =? y) = true" while it is expected to have type "x = y".
```

or sort violations:

```text
Error: The term "x" has type "nat" which is not a sort.
```

### Signature C: Subterm Not Found in Rewrite

```text
Error: Found no subterm matching "double ?n" in the current goal.
```

or in a targeted hypothesis:

```text
Error: Found no subterm matching "double ?n" in H.
```

---

## 2. Root Cause & Theoretical Background

1. **Definitional vs. Propositional Equality**:
   Rocq's type-checker evaluates equality modulo conversion ($\beta$-reduction for function application, $\iota$-reduction for match elimination, $\zeta$-reduction for `let`-bindings, and $\delta$-reduction for transparent constant expansion).
   - If a definition is not unfolded, syntactic pattern matching and tactics like `reflexivity` or `apply` cannot see inside it.
   - Propositional equality ($a = b$) requires a formal proof object, whereas definitional equality ($a \equiv b$) is verified automatically by the kernel.
2. **Sort Separation (`Prop` vs `bool`)**:
   - `bool : Set` is an inductive two-valued datatype (`true`, `false`) evaluated computationally.
   - `Prop` is the sort of logical propositions whose truth requires evidence (proof terms).
   - Equalities like `(x =? y) = true` (boolean equality) and `x = y` (`Prop` identity) are logically related but not definitionally equivalent. They require reflection lemmas to bridge.
3. **Implicit Argument Deduction**:
   When higher-order lemmas or polymorphic constants are applied without sufficient typing constraints, Rocq's bidirectional elaboration algorithm fails to synthesize unconstrained type arguments or implicit parameters.
4. **Syntactic Redex Requirements in `rewrite`**:
   `rewrite` searches for an exact syntactic match in the target clause before attempting unification. If the redex is hidden inside an unexpanded constant, `Found no subterm matching` is raised.

---

## 3. Anti-Patterns to Avoid

- ❌ **Blindly repeating `auto`, `reflexivity`, or `easy`**: If two terms are not definitionally convertible, `reflexivity` will fail indefinitely.
- ❌ **Inverting terms in unification diagnostics**: Treating the left-hand term as the goal and right-hand term as the lemma; always inspect the polarity (`actual` vs `expected`).
- ❌ **Tweaking `exact H` without type conversion**: Passing a boolean equality directly where a propositional proof is expected without a reflection bridge.
- ❌ **Indiscriminate `simpl`**: `simpl` can unfold library internals uncontrollably, creating massive, unreadable ASTs that break subsequent lemma matches. Use targeted `unfold`, `cbn`, or `change`.

---

## 4. Concrete Prescriptions (Before & After)

### Case 1: Unfolding Transparent Definitions

**Failing Code (Before):**

```Coq
From Stdlib Require Import Arith.

Definition double (n : nat) : nat := n + n.

Lemma double_zero : forall n, double n = 0 -> n = 0.
Proof.
  intros n H.
  (* Fails: The term "H" has type "double n = 0" while it is expected to have type "n + n = 0" *)
  apply Nat.eq_add_0 in H.
  destruct H as [H1 _]; exact H1.
Qed.
```

**Repaired Code (After):**

```Coq
From Stdlib Require Import Arith.

Definition double (n : nat) : nat := n + n.

Lemma double_zero : forall n, double n = 0 -> n = 0.
Proof.
  intros n H.
  unfold double in H. (* Explicitly delta-reduces the transparent definition *)
  apply Nat.eq_add_0 in H.
  destruct H as [H1 _]; exact H1.
Qed.
```

---

### Case 2: Bridging `bool` and `Prop` with Reflection Lemmas

**Failing Code (Before):**

```Coq
From Stdlib Require Import Arith.

Lemma test_beq_eq : forall x y : nat, (x =? y) = true -> x = y.
Proof.
  intros x y H.
  (* Fails: Unable to unify "(x =? y) = true" with "x = y" *)
  exact H.
Qed.
```

**Repaired Code (After):**

```Coq
From Stdlib Require Import Arith.

Lemma test_beq_eq : forall x y : nat, (x =? y) = true -> x = y.
Proof.
  intros x y H.
  apply Nat.eqb_eq in H. (* Transforms boolean test into propositional equality *)
  exact H.
Qed.
```

Common reflection bridges in `Stdlib`:

- Natural numbers: `apply Nat.eqb_eq in H` ($=? \leftrightarrow =$) or `apply Nat.eqb_neq in H` ($=? \text{ false} \leftrightarrow \neq$).
- Booleans: `destruct (andb_prop _ _ H)` for `a && b = true`, `apply orb_prop in H` for `a || b = true`.
- Decidable comparisons: `destruct (Nat.eqb_spec x y)` or `destruct (Nat.leb_spec x y)`.

---

### Case 3: Explicit Parameter Instantiation with `@`

**Failing Code (Before):**

```Coq
From Stdlib Require Import List.
Import ListNotations.

Lemma app_nil_inv : forall (A : Type) (l1 l2 : list A),
  l1 ++ l2 = [] -> l1 = [] /\ l2 = [].
Proof.
  intros A l1 l2 H.
  (* Fails: Unable to find an instance for the variable A in app_eq_nil *)
  apply app_eq_nil.
  exact H.
Qed.
```

**Repaired Code (After):**

```Coq
From Stdlib Require Import List.
Import ListNotations.

Lemma app_nil_inv : forall (A : Type) (l1 l2 : list A),
  l1 ++ l2 = [] -> l1 = [] /\ l2 = [].
Proof.
  intros A l1 l2 H.
  (* Prefix with @ to supply all implicit arguments explicitly *)
  apply (@app_eq_nil A l1 l2).
  exact H.
Qed.
```

---

### Case 4: Aligning Subterms for `rewrite`

**Failing Code (Before):**

```Coq
From Stdlib Require Import Arith.

Definition add1 (n : nat) : nat := n + 1.

Lemma add1_comm : forall n m, add1 n + m = m + add1 n.
Proof.
  intros n m.
  (* Fails: Found no subterm matching "add1 n + m" when searching without unfolding *)
  rewrite Nat.add_comm.
  reflexivity.
Qed.
```

**Repaired Code (After):**

```Coq
From Stdlib Require Import Arith.

Definition add1 (n : nat) : nat := n + 1.

Lemma add1_comm : forall n m, add1 n + m = m + add1 n.
Proof.
  intros n m.
  apply Nat.add_comm. (* Direct application unifying modulo computation *)
Qed.
```

Alternatively, expose the redex via `unfold`, `change`, or `setoid_rewrite`:

```Coq
Proof.
  intros n m.
  unfold add1.
  rewrite Nat.add_comm.
  reflexivity.
Qed.
```

---

## 5. Fallback Procedures

1. **Use `change` or `replace` for Definitional Alignment**:
   When `unfold` exposes too much internal definition, manually replace the target term:
   ```Coq
   change (n + n) with (double n) in H.
   ```
2. **Inspect with `Set Printing All`**:
   Hidden implicit arguments, coercions, or universe levels often cause seemingly identical terms to reject unification:
   ```Coq
   Set Printing All.
   (* Inspect the exact elaborated AST of hypotheses and goal *)
   Unset Printing All.
   ```
3. **Assert Intermediate Steps**:
   If `apply` fails on complex terms, state the exact instantiated lemma as an assertion:
   ```Coq
   assert (Hstep : double n = n + n) by reflexivity.
   rewrite Hstep in H; clear Hstep.
   ```
