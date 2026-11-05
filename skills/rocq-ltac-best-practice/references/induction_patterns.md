# Induction Patterns, Index Preservation & Remember Idioms

This reference guides autonomous agents in applying induction safely to inductive types and relations in Rocq, specifically addressing the critical **Premature Induction Trap** on indexed predicates.

---

## 1. The Indexed Inductive Predicate Problem

In type theory, when an inductive family has non-variable index terms (e.g., `Inductive ev : nat -> Prop` with constructors targeting `0` and `S (S n)`), applying `induction` directly on a derivation hypothesis discards the concrete shape of the index expression, replacing it with an arbitrary unconstrained variable.

### ❌ The Premature Induction Trap

Consider proving that `ev n -> ev (n - 2)`:

```coq
Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall n, ev n -> ev (S (S n)).

Lemma ev_minus2_bad : forall n, ev n -> ev (n - 2).
Proof.
  intros n H.
  induction H.
  (* DISASTER:
     Subgoal 1: ev (0 - 2)
     Subgoal 2: ev (S (S n) - 2)
     Notice that n in the target became unlinked from the constructor indices!
     The connection n = 0 and n = S (S n') was erased. *)
Abort.
```

---

## 2. The Universal `remember` Idiom

To retain the equality between a compound term and an inductive predicate's index, execute the **`remember ... as ... eqn:...`** idiom before invoking `induction`.

### The 4-Step Recipe

1. **Remember**: `remember <compound_term> as x eqn:Heqx.`
2. **Revert dependent hypotheses**: `revert Heqx.` (and any hypotheses referencing variables in `<compound_term>`).
3. **Induct**: `induction H; intros Heqx; subst.`
4. **Solve**: Use constructor inversion or equations preserved by `Heqx`.

### ✅ Correct Idiom Application

```coq
Lemma ev_minus2_good : forall n, ev n -> ev (n - 2).
Proof.
  intros n H.
  remember n as m eqn:Heqm.
  revert Heqm.
  induction H; intros Heqm; subst.
  - (* Case ev_0: m = 0 *)
    simpl. constructor.
  - (* Case ev_SS: m = S (S n0) *)
    simpl.
    destruct n as [| [| n']].
    + simpl. constructor.
    + (* Impossible: ev 1 *)
      inversion H.
    + simpl in *. assumption.
Qed.
```

---

## 3. Dependent Hypothesis Protection: `revert` vs `generalize dependent`

When inducting over a term or derivation $H$ upon which other hypotheses or variables depend, those dependencies must be abstracted into universal quantifiers in the goal target. Otherwise, the induction hypothesis (`IH`) will be insufficiently general and unprovable.

| Tactic                    | Action                                                                                 | When to Use                                                                    |
| :------------------------ | :------------------------------------------------------------------------------------- | :----------------------------------------------------------------------------- |
| `generalize dependent x.` | Automatically reverts `x` and **all hypotheses depending on `x`** in topological order | **Recommended standard** when abstracting variables before induction.          |
| `revert x.`               | Reverts `x` only. Fails if other hypotheses still depend on `x`                        | When only an isolated hypothesis or equation needs to be pushed into the goal. |

### Idiomatic Demonstration

```coq
Theorem eval_deterministic_gen_dep : forall c st st1 st2,
  ceval c st st1 ->
  ceval c st st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 H1.
  (* st2 must vary across inductive steps *)
  generalize dependent st2.
  induction H1; intros st2 H2.
  (* IHceval will now universally quantify over st2 *)
Admitted.
```

---

## 4. Well-Founded Induction on Measures (`lt_wf_ind`)

When induction cannot follow the structural recursion of an inductive datatype (e.g., in divide-and-conquer algorithms, collatz sequences, or tree traversals with variable branching), use **well-founded induction** on the natural number order:

```coq
From Stdlib Require Import Arith Lia.

Theorem lt_wf_ind : forall (n : nat) (P : nat -> Prop),
  (forall n0, (forall m, m < n0 -> P m) -> P n0) -> P n.
```

### Application Recipe

```coq
Lemma well_founded_measure_example : forall n, P n.
Proof.
  intros n.
  remember (f n) as len eqn:Hlen.
  revert n Hlen.
  induction len as [len IH] using lt_wf_ind.
  intros n Hlen.
  (* We now have: IH : forall m, m < len -> forall n0, m = f n0 -> P n0 *)
Admitted.
```

---

## 5. Mutual Induction Schemes

When types are mutually defined (e.g., expressions and boolean expressions in an AST), Rocq does not automatically generate a combined induction principle.

### Generating the Mutual Scheme

```coq
Inductive exp : Type :=
| EConst : nat -> exp
| EIf : bexp -> exp -> exp -> exp
with bexp : Type :=
| BTrue : bexp
| BNot : bexp -> bexp.

(* Generate mutual induction scheme *)
Scheme exp_mut := Induction for exp Sort Prop
with bexp_mut := Induction for bexp Sort Prop.
```

### Applying the Combined Scheme

Use `apply exp_mut with (P := ...) (P0 := ...)`:

```coq
Theorem exp_bexp_property :
  (forall e : exp, P_exp e) /\ (forall b : bexp, P_bexp b).
Proof.
  apply exp_mut.
  - (* Case EConst *) (* ... *)
  - (* Case EIf *) (* ... *)
  - (* Case BTrue *) (* ... *)
  - (* Case BNot *) (* ... *)
Admitted.
```
