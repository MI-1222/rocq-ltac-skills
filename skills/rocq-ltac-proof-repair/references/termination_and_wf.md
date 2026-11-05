# Termination, Guard Checking & Well-Founded Recursion

This reference provides techniques for diagnosing and repairing `Fixpoint` guard-checker failures, specifying structural arguments, and transitioning to well-founded recursion using `Program Fixpoint` with `measure` in Rocq 9.0+ and Coq 8.20.

---

## 1. Error Signatures

### Signature A: Unspecified Decreasing Argument

```text
Error: Cannot guess decreasing argument of fix.
```

Rocq cannot automatically determine which of several arguments structurally decreases in all recursive calls.

### Signature B: Non-Structural Recursive Call

```text
Error: Recursive call to half_list has argument "tl" which is not structurally smaller.
```

or

```text
Error: Recursive call to gcd has argument "b" which is not structurally smaller.
```

The recursive argument is mathematically smaller, but not a direct syntactic subterm (e.g., produced by an arithmetic operation like `n - m`, a list function like `tl`, or integer division).

---

## 2. Root Cause & Theoretical Background

1. **The Syntactic Guard Condition**:
   Rocq's kernel enforces strong normalization via a syntactic **Guard Checker**.
   - Recursive calls in a `Fixpoint` must be applied to an **immediate syntactic subterm** exposed by pattern matching on a single designated decreasing argument.
   - Any intervening computation—even an identity function or transparent alias—breaks syntactic subterm tracking.
2. **Multiple Arguments**:
   When a `Fixpoint` takes multiple arguments, the decreasing argument must be uniquely identified. If multiple arguments decrease alternately, Rocq's default heuristic fails unless annotated with `{struct x}`.
3. **Well-Founded Relations & Measures**:
   When a function terminates by decreasing a non-structural quantity (e.g., list length, integer value, tree depth), it must be framed using a well-founded relation:
   - A relation $R$ on $A$ is well-founded if there are no infinite decreasing chains $x_0 \mathrel{R} x_1 \mathrel{R} x_2 \dots$.
   - The `Program Fixpoint ... {measure f x}` construct automatically generates proof obligations verifying that the measure strictly decreases at every recursive step according to `lt` on `nat`.

---

## 3. Anti-Patterns to Avoid

- ❌ **Shuffling argument order randomly**: Swapping argument positions without understanding which argument is being structurally unwrapped.
- ❌ **Introducing bogus pattern matches**: Adding dummy `match` layers that obfuscate the code without satisfying the syntactic subterm criterion.
- ❌ **Ad-hoc fuel arguments everywhere**: Adding a `fuel : nat` parameter to every non-trivial function. While acceptable as a temporary prototype, well-founded recursion is cleaner and does not alter the function's external signature.

---

## 4. Concrete Prescriptions (Before & After)

### Case 1: Multiple Arguments and `{struct}` Annotation

**Failing Code (Before):**

```Coq
Fixpoint ack (m n : nat) : nat :=
  match m, n with
  | 0, _ => S n
  | S m', 0 => ack m' 1
  | S m', S n' => ack m' (ack (S m') n')
  end.
(* Error: Cannot guess decreasing argument of fix *)
```

**Repaired Code (After):**

```Coq
(* Explicitly designate 'm' as the primary structural decreasing argument *)
Fixpoint ack (m : nat) : nat -> nat :=
  match m with
  | 0 => fun n => S n
  | S m' =>
      fix ack_m (n : nat) : nat :=
        match n with
        | 0 => ack m' 1
        | S n' => ack m' (ack_m n')
        end
  end.
```

For simpler functions where Rocq just needs guidance on which argument to track, use `{struct ...}` directly:

```Coq
Fixpoint plus_custom (n m : nat) {struct n} : nat :=
  match n with
  | 0 => m
  | S n' => S (plus_custom n' m)
  end.
```

---

### Case 2: Non-Structural Decrease with `Program Fixpoint {measure ...}`

**Failing Code (Before):**

```Coq
From Stdlib Require Import List.
Import ListNotations.

Fixpoint half_list (l : list nat) : list nat :=
  match l with
  | [] => []
  | [x] => [x]
  | x :: y :: tl => x :: half_list tl
  end.
(* Error: Cannot guess decreasing argument of fix.
   tl is extracted from nested pattern, which confuses standard struct detection. *)
```

**Repaired Code (Option A: Explicit Struct on Flattened Match):**

```Coq
Fixpoint half_list (l : list nat) {struct l} : list nat :=
  match l with
  | [] => []
  | x :: rest =>
      match rest with
      | [] => [x]
      | _ :: tl => x :: half_list tl
      end
  end.
```

**Repaired Code (Option B: `Program Fixpoint` with Measure):**

```Coq
From Stdlib Require Import List.
From Stdlib Require Import Program.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Import ListNotations.

Program Fixpoint half_list_meas (l : list nat) {measure (length l)} : list nat :=
  match l with
  | x :: y :: tl => x :: half_list_meas tl
  | other => other
  end.
Next Obligation.
  simpl. lia. (* Obligation discharged: length tl < length (x :: y :: tl) *)
Qed.
```

---

### Case 3: Division or GCD (Arithmetic Well-Founded Recursion)

Functions that divide or take modulo do not decrease structurally on `nat`. Use `Program Fixpoint` with `{measure n}`:

```Coq
From Stdlib Require Import Arith.
From Stdlib Require Import Program.
From Stdlib Require Import Lia.

Program Fixpoint div2_meas (n : nat) {measure n} : nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | S (S n') => S (div2_meas n')
  end.
Next Obligation.
  lia.
Qed.
```

When obligations generate multiple subgoals or require non-trivial bounds:

```Coq
Program Fixpoint gcd (a b : nat) {measure b} : nat :=
  if Nat.eqb b 0 then a
  else gcd b (a mod b).
Next Obligation.
  apply Nat.mod_upper_bound.
  intro Hzero; apply (Nat.eqb_neq b 0); [assumption | symmetry; exact Hzero].
Qed.
```

---

## 5. Fallback Procedures

1. **Using `Function` with `measure` or `wf`**:
   The legacy `Function` vernacular generates dedicated induction principles (`<func>_ind`):

   ```Coq
   From Stdlib Require Import Recdef.

   Function div2_fn (n : nat) {measure id n} : nat :=
     match n with
     | 0 => 0
     | 1 => 0
     | S (S n') => S (div2_fn n')
     end.
   Proof.
     intros; unfold id; lia.
   Qed.
   ```

2. **Explicit `well_founded_induction`**:
   For complex semantic interpreters or step reductions where `Program Fixpoint` produces unwieldy proof obligations:
   ```Coq
   Lemma my_eval_wf : forall (fuel : nat) (e : expr), ...
   ```
   or instantiate `well_founded_induction` on `lt_wf`:
   ```Coq
   apply (well_founded_induction lt_wf (fun n => ...)).
   ```
