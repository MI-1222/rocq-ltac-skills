# Termination, Guard Checking & Well-Founded Recursion

This reference provides techniques for diagnosing and repairing `Fixpoint` guard-checker failures, understanding structurally smaller subterms, specifying structural arguments with `{struct}`, and transitioning to well-founded recursion using `Program Fixpoint` with `measure` in Rocq 9.0+ and Coq 8.20.

---

## 1. Error Signatures

### Signature A: Unspecified Decreasing Argument

```text
Error: Cannot guess decreasing argument of fix.
```

Rocq scans inductive arguments from left to right, but cannot find an argument that syntactically decreases across all recursive branches.

### Signature B: Non-Structural Recursive Call

```text
Error: Recursive call to "half_list" has argument "tl" which is not structurally smaller.
```

or

```text
Error: Recursive definition of "gcd" is ill-formed.
In environment
...
Recursive call to "gcd" has argument "a mod b" which is not structurally smaller.
Recursive calls are only allowed on immediate subterms of "b".
```

The recursive argument is mathematically smaller, but not an immediate syntactic subterm (e.g., produced by an arithmetic operation like `a mod b`, a projection like `fst x`, or an intervening function call).

---

## 2. Root Cause & Theoretical Background

1. **The Syntactic Guard Condition**:
   Rocq's kernel enforces strong normalization via a syntactic **Guard Checker** (`kernel/inductive.ml`).
   - Recursive calls in a `Fixpoint` must be applied to an **immediate syntactic subterm** exposed by pattern matching on a designated decreasing argument.
   - For an argument $x$, matching `match x with C p1 ... pn => ... end` registers each constructor argument variable $p_i$ as an immediate subterm of $x$. Subsequent pattern matching on $p_i$ transitively extends subterm status.
2. **Patterns That Destroy Structural Subterm Tracking**:
   - **Tuple Projections**: If $x$ is a pair or record, matching `match x with (a, b) => f a end` is valid, but calling `f (fst x)` is invalid because `fst` is a projection function, not a pattern binder.
   - **Intervening Function Calls**: Expressions like `f (tl l)` or `f (match l with x :: xs => g xs end)` fail because passing a subterm through an arbitrary function $g$ invalidates subterm tracking.
   - **Higher-Order Functions**: Passing a subterm inside a lambda to `List.map` fails because the guard checker cannot inspect termination properties of higher-order iterators.
   - **Let-Aliases**: `let y := x in f y` fails unless $y$ is transparently inlined before guard inspection.
3. **Automatic Decreasing Argument Inference**:
   When `{struct ...}` is omitted, Rocq scans arguments from index 0 upward. Only arguments with inductive types are tested. The first argument that satisfies the guard condition across all recursive calls is selected. If no single argument qualifies, `Cannot guess decreasing argument of fix` is raised.
4. **Well-Founded Measures**:
   When a function terminates by decreasing a non-structural quantity (e.g., list length, integer value, tree depth), it must be framed using a well-founded relation. `Program Fixpoint ... {measure f x}` generates proof obligations verifying that the measure strictly decreases at each recursive call.

---

## 3. Anti-Patterns to Avoid

- ❌ **Shuffling argument order blindly**: Swapping parameter positions without understanding which argument is being structurally unwrapped by pattern matching.
- ❌ **Introducing bogus pattern matches**: Adding dummy `match` layers that obfuscate the code without satisfying the syntactic subterm criterion.
- ❌ **Calling projections instead of destructuring**: Writing `f (fst p)` instead of matching `destruct p as [a b]` and calling `f a`.

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

For multi-argument functions where a single argument decreases structurally throughout:

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
(* Error: Recursive call to "half_list" has argument "tl" which is not structurally smaller. *)
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
  simpl. lia. (* Discharges obligation: length tl < length (x :: y :: tl) *)
Qed.
```

---

### Case 3: Arithmetic Well-Founded Recursion (Division / GCD)

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

---

## 5. Fallback Procedures

1. **Using `Function` with `measure` or `wf`**:
   The `Function` vernacular automatically generates dedicated induction principles (`<func>_ind`):

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

2. **Explicit Fuel Parameterization**:
   When obligation proofs cannot be settled or in restricted environments:
   ```Coq
   Fixpoint eval_fuel (fuel : nat) (e : expr) : option val :=
     match fuel with
     | 0 => None
     | S fuel' => ... (recursive calls pass fuel') ...
     end.
   ```
