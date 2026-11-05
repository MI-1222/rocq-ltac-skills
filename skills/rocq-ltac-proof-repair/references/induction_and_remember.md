# Induction, Index Preservation & the `remember` Idiom

This reference provides techniques for avoiding index evaporation during induction on dependent inductive relations, managing induction hypothesis generalization, and handling mutual induction schemes in Rocq 9.0+ and Coq 8.20.

---

## 1. Error Signatures

### Signature A: Lost Index Information (Unprovable Subgoal)

```text
(* After applying 'induction H': *)
1 subgoal
______________________________________(1/1)
ev n
(* The compound index (n + 2) was replaced by an arbitrary variable,
   breaking the connection to n and making the goal unprovable. *)
```

### Signature B: Prematurely Specialized Induction Hypothesis

```text
IHn : P n m0
______________________________________(1/1)
P (S n) m1
(* The IH quantified over fixed 'm0' instead of arbitrary 'forall m, P n m',
   because 'm' was introduced into the context before 'induction n'. *)
```

---

## 2. Root Cause & Theoretical Background

1. **Index Generalization in CIC**:
   When `induction H` is applied to an inductive hypothesis `H : R e1 ... en`, Rocq replaces all complex index terms $e_i$ with fresh arbitrary variables $x_i$ to instantiate the inductive elimination scheme:
   $$\text{elim}_R : \forall x_1 \dots x_n, R\ x_1 \dots x_n \to P\ x_1 \dots x_n$$
   If an index is a compound expression (e.g., `n + 2`, `EIf e1 e2 e3`, `t_arrow T1 T2`), the fact that the term had this specific structure is forgotten in all generated branches.
2. **The `remember` Preservation Idiom**:
   By replacing the compound expression with a fresh variable and recording an explicit equality hypothesis:
   ```Coq
   remember (n + 2) as k eqn:Heqk.
   ```
   the equality `Heqk : k = n + 2` is preserved across all inductive cases. Cases that contradict the shape of $k$ are dismissed via `discriminate` or `inversion Heqk`.
3. **Quantifier Scope in Induction Hypotheses**:
   If variable $m$ occurs in the goal alongside inductive variable $n$, introducing $m$ via `intros n m` before `induction n` fixes $m$ in the local context. The generated induction hypothesis will be `IH : P n m` rather than `IH : forall m, P n m`. Use `generalize dependent m` before `induction n`.

---

## 3. Anti-Patterns to Avoid

- ❌ **Direct induction on parameterized/indexed relations without `remember`**: Inducting directly on `step (EIf e1 e2 e3) e'` or `typing (t_app e1 e2) T` discards the constructor context.
- ❌ **Neglecting to `revert` dependent variables**: Inducting on $n$ while leaving dependent indices fixed in the context, resulting in weak, non-applicable induction hypotheses.
- ❌ **Over-remembering**: Using `remember` on simple variables or constructor arguments that are already distinct identifiers. Only use `remember` on compound expressions or non-variable indices.

---

## 4. Concrete Prescriptions (Before & After)

### Case 1: Preserving Compound Indices with `remember`

**Failing Code (Before):**

```Coq
Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall n, ev n -> ev (S (S n)).

Lemma ev_even_plus_2 : forall n, ev (n + 2) -> ev n.
Proof.
  intros n H.
  induction H.
  (* Goal breaks:
     Base case: ev n is unprovable because 0 = n + 2 was lost.
     Step case: ev (S (S n0)) does not connect with n. *)
Abort.
```

**Repaired Code (After):**

```Coq
Lemma ev_even_plus_2 : forall n, ev (n + 2) -> ev n.
Proof.
  intros n H.
  remember (n + 2) as k eqn:Heqk.
  revert n Heqk.
  induction H as [| m Hm IH]; intros n Heqk.
  - (* Base: 0 = n + 2 *)
    discriminate Heqk.
  - (* Step: S (S m) = n + 2 *)
    destruct n as [| [| n']].
    + simpl in Heqk. injection Heqk as Heqk'. subst. exact Hm.
    + simpl in Heqk. injection Heqk as Heqk'. subst. exact Hm.
    + simpl in Heqk. injection Heqk as Heqk'.
      apply IH. rewrite Heqk'. reflexivity.
Qed.
```

---

### Case 2: Transition Semantics Induction in Programming Languages

**Failing Code (Before):**

```Coq
Inductive tm : Type :=
| t_const : nat -> tm
| t_if : tm -> tm -> tm -> tm.

Inductive step : tm -> tm -> Prop :=
| step_if_true : forall t2 t3, step (t_if (t_const 1) t2 t3) t2
| step_if_false : forall t2 t3, step (t_if (t_const 0) t2 t3) t3.

Lemma if_step_deterministic : forall t2 t3 t',
  step (t_if (t_const 1) t2 t3) t' -> t' = t2.
Proof.
  intros t2 t3 t' H.
  induction H.
  (* Unsound explosion: induction treats the subject as an arbitrary term,
     generating subgoals for every possible step constructor. *)
Abort.
```

**Repaired Code (After):**

```Coq
Lemma if_step_deterministic : forall t2 t3 t',
  step (t_if (t_const 1) t2 t3) t' -> t' = t2.
Proof.
  intros t2 t3 t' H.
  remember (t_if (t_const 1) t2 t3) as t eqn:Heqt.
  induction H as [t2' t3' | t2' t3'].
  - (* step_if_true *)
    injection Heqt as H1 H2 H3. subst. reflexivity.
  - (* step_if_false *)
    discriminate Heqt.
Qed.
```

---

### Case 3: Generalizing Dependencies Before Induction

**Failing Code (Before):**

```Coq
Lemma plus_assoc : forall n m p : nat, n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
    (* If 'm' or 'p' had needed to vary, IHn' would be fixed to this particular m, p *)
    rewrite IHn'. reflexivity.
Qed.
```

When $m$ or $p$ must vary across inductive steps (e.g., list reversal or accumulator-based operations):

**Repaired Code (After):**

```Coq
Lemma rev_acc_correct : forall (A : Type) (l acc : list A),
  (* Inducting on l requires acc to be quantified for all acc *)
  True.
Proof.
  (* General pattern: *)
  intros A l.
  induction l as [| x l' IHl']; intros acc.
  (* Now IHl' has type: forall acc, ... *)
Admitted.
```

Use `generalize dependent <var>` explicitly when variables are already in the context:

```Coq
intros n m H.
generalize dependent m.
induction n as [| n' IHn']; intros m H.
```

---

### Case 4: Mutual Inductive Relations (`Scheme ... Minimality`)

For mutually inductive types/predicates, default `induction` produces incomplete induction hypotheses. Generate and apply mutual induction schemes:

```Coq
Inductive even : nat -> Prop :=
| even_O : even 0
| even_S : forall n, odd n -> even (S n)
with odd : nat -> Prop :=
| odd_S : forall n, even n -> odd (S n).

Scheme even_mut := Minimality for even Sort Prop
with odd_mut := Minimality for odd Sort Prop.

Combined Scheme even_odd_mut from even_mut, odd_mut.
```

Then invoke the scheme in proofs:

```Coq
apply (even_mut (fun n => P n) (fun n => Q n)); intros.
```

---

## 5. Fallback Procedures

1. **Prefer Inversion for Non-Recursive Hypotheses**:
   If the inductive hypothesis is not applied recursively in subgoals, do not use `induction`. Use destructive inversion instead:
   ```Coq
   inversion H; subst; clear H.
   ```
2. **Induction on a Derived Measure**:
   If structural induction on the hypothesis fails due to complex indices, induct on a natural number measure (such as term size or evaluation depth):
   ```Coq
   remember (size t) as n eqn:Heqn.
   generalize dependent t.
   induction n as [| n' IH]; intros t Heqn.
   ```
