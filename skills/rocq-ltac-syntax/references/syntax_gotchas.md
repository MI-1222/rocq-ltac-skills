# Rocq & Vanilla Ltac Syntax Gotchas & Pitfalls Reference

This reference catalog details subtle lexical edge cases, grammar traps, parser quirks, and dialect contamination anti-patterns encountered when writing formal proofs in Rocq (formerly Coq) using Pure Vanilla Ltac.

## 1. Sentence Terminator & Lexical Traps

### 1.1. The Sentence Terminator Rule (`.` + Whitespace)

In Rocq, a period (`.`) functions as a sentence terminator **if and only if** it is followed immediately by whitespace (space, tab `\t`, newline `\n`, carriage return `\r`) or the end of the file (EOF).

```Coq
(* ❌ BROKEN: Missing whitespace after the dot *)
intros x.induction x.
Theorem add_0_r : forall n, n + 0 = n.Proof.

(* Compiler Error:
   Syntax error: '.' expected after [vernac:command]
   (The parser treats "x.induction" and "n.Proof" as single qualified identifiers) *)

(* ✅ CORRECT: Explicit whitespace or linebreaks after every terminator *)
intros x. induction x.

Theorem add_0_r : forall n, n + 0 = n.
Proof.
```

- Periods appearing inside qualified identifiers (`Module.submodule`, `List.map`), record projections (`state.pc`), or floating-point literals are followed by alphanumeric characters without whitespace and are never parsed as sentence terminators.
- Periods following closing delimiters (`)`, `]`, `}`, `"`) must still be separated from the subsequent token by a space or newline.

### 1.2. Comment Nesting (`(* ... *)`)

Rocq comments are delimited by `(*` and `*)` and support arbitrary recursive nesting via depth counters.

- Opening `(*` increments the nesting depth; closing `*)` decrements it.
- Periods inside comments are completely ignored by the lexer and do not terminate commands.
- Leaving an unmatched `(*` anywhere in the file causes the lexer to consume the remainder of the file, raising `Syntax Error: Lexer: Unterminated comment`.

```Coq
(* ❌ BROKEN: Unmatched comment delimiter at EOF *)
Definition answer : nat := 42.
(* Note to self: (* nested detail *) forgot to close outer...

(* Compiler Error:
   Syntax Error: Lexer: Unterminated comment *)

(* ✅ CORRECT: Balanced comment delimiters *)
Definition answer : nat := 42.
(* Note to self: (* nested detail *) properly closed *)
```

### 1.3. String Literal Escaping (`"..."`)

Gallina and Vernacular strings are enclosed in double quotes `"..."` and can span multiple lines.

- To include a double quote inside a string, **double it (`""`)**. Escaping via backslash (`\"`) is invalid in standard Gallina and will leave trailing escape characters or unclosed strings.
- Periods inside string literals are treated as literal characters and do not split sentences.
- Failing to terminate a string raises `Syntax Error: Lexer: Unterminated string` at EOF.

```Coq
(* ❌ BROKEN: C-style backslash escape *)
Definition greeting : string := "He said \"hello\" to everyone.".

(* ✅ CORRECT: Rocq doubled-quote escape *)
Definition greeting : string := "He said ""hello"" to everyone.".
```

## 2. Bullet Hierarchy & Focus Pitfalls

### 2.1. The Trailing Dot on Focus Bullets

Bullets (`-`, `+`, `*`, `--`, `++`, `**`) are proof-engine subgoal selectors, not Vernacular commands.

- Never append a period directly to a bullet (e.g., `-.` or `+.`). The parser treats this as an invalid custom operator or unknown tactic.

```Coq
(* ❌ BROKEN: Trailing period attached to focus bullet *)
Proof.
  induction n.
  -. reflexivity.
  +. simpl. rewrite IHn. reflexivity.
Qed.

(* Compiler Error:
   Syntax error: [tactic] expected after [bullet] *)

(* ✅ CORRECT: Bare bullet tokens *)
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.
```

### 2.2. The `Wrong bullet` Sibling Conflict

When multiple subgoals are generated (e.g., via `induction`, `destruct`, or `split`), entering a bullet branch focuses exclusively on that subgoal until it is fully closed.

- Attempting to declare a sibling bullet before the active subgoal is resolved triggers a parser and engine halt.

```Coq
(* ❌ BROKEN: Transitioning to sibling bullet while current branch is open *)
Proof.
  intros [h1 | h2].
  - (* Left branch started *)
    simpl.
  - (* Attempting sibling branch prematurely *)
    right. assumption.

(* Compiler Error:
   Error: Wrong bullet -: Current bullet - is not finished. *)

(* ✅ CORRECT: Fully resolve the branch before proceeding *)
Proof.
  intros [h1 | h2].
  - left. assumption.
  - right. assumption.
Qed.
```

### 2.3. Nesting Depth & Curly Braces `{ ... }`

Standard bullet hierarchy progresses in order: `-` (depth 1) $\to$ `+` (depth 2) $\to$ `*` (depth 3) $\to$ `--` (depth 4).

- For branches nested deeper than 3 levels, replace complex bullet combinations with explicit curly braces `{ ... }`.
- Curly braces must not have trailing periods. The closing brace `}` enforces that all subgoals generated inside the block are closed.

```Coq
(* ✅ RECOMMENDED: Using curly braces for deep subgoal isolation *)
Proof.
  induction H; intros.
  - (* Base case *) reflexivity.
  - (* Inductive step with deep splits *)
    destruct (x <=? a) eqn:Heq.
    + reflexivity.
    + {
        (* Enclosed sub-proof block *)
        eapply Permutation_trans.
        * apply Permutation_swap.
        * apply Permutation_cons; assumption.
      }
Qed.
```

## 3. Gallina & Ltac Structural Gotchas

### 3.1. Unclosed `match ... with ... end` Blocks

Both Gallina pattern matches and Ltac `match goal with` expressions require an explicit `end` keyword.

- Because Rocq does not use indentation-based scoping (offside rule), omitting `end` causes the parser to consume subsequent commands (including `Theorem` or `Definition`) as pattern branches.

```Coq
(* ❌ BROKEN: Missing 'end' keyword *)
Definition pred (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => n'

Theorem pred_0 : pred 0 = 0.
Proof. reflexivity. Qed.

(* Compiler Error:
   Syntax error: 'end' expected after [match branches] (at line of Theorem) *)

(* ✅ CORRECT: Explicit 'end' termination *)
Definition pred (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => n'
  end.
```

### 3.2. Dependent Pattern Matching (`as ... in ... return ...`)

When matching over an inductive term whose indices determine the return type, a simple `match` expression fails type checking with `The reference ... was not found` or `Type mismatch`.

- Use the full `match e as x in (T y) return (P x y) with` syntax to explicitly abstract indices in the return predicate.

```Coq
Inductive vec (A : Type) : nat -> Type :=
| vnil : vec A 0
| vcons : forall n, A -> vec A n -> vec A (S n).

(* ❌ BROKEN: Naive match without dependent return annotation *)
Definition vhead {A : Type} {n : nat} (v : vec A (S n)) : A :=
  match v with
  | vcons _ h _ => h
  end.
(* Type error: Cannot unify "0" with "S n" *)

(* ✅ CORRECT: Dependent return annotation *)
Definition vhead {A : Type} {n : nat} (v : vec A (S n)) : A :=
  match v as v' in vec _ m return (match m with 0 => unit | S _ => A end) with
  | vnil _ => tt
  | vcons _ h _ => h
  end.
```

### 3.3. `Fixpoint` Decreasing Argument Annotations

Calculus of Inductive Constructions (CIC) requires all recursive definitions to structurally terminate.

- When a `Fixpoint` takes multiple arguments and recursion does not happen on the very first argument, the termination checker often fails with `Cannot guess decreasing argument of fix`.
- Always declare `{struct <arg>}` explicitly.

```Coq
(* ❌ BROKEN: Ambiguous decreasing argument *)
Fixpoint merge (l1 l2 : list nat) : list nat :=
  match l1 with
  | [] => l2
  | x :: l1' =>
      match l2 with
      | [] => l1
      | y :: l2' =>
          if x <=? y then x :: merge l1' l2
          else y :: merge l1 l2'
      end
  end.
(* Compiler Error: Cannot guess decreasing argument of fix *)

(* ✅ CORRECT: Explicit nested structural recursion or measure *)
Fixpoint merge (l1 : list nat) : list nat -> list nat :=
  fix merge_aux (l2 : list nat) : list nat :=
    match l1, l2 with
    | [], _ => l2
    | _, [] => l1
    | x :: l1', y :: l2' =>
        if x <=? y then x :: merge l1' l2
        else y :: merge_aux l2'
    end.
```

### 3.4. Mixing Term Mode (`:=`) and Tactic Mode (`Proof. ... Qed.`)

Gallina values and Ltac proof scripts operate in distinct parser modes.

- Do not place Ltac commands inside a `Definition` assignment (`:=`) without an enclosing `ltac:(...)` or `exact (...)` bridge.
- Do not use `Proof. ... Qed.` for computational data meant to compute inside the kernel unless using `Defined.`.

```Coq
(* ❌ BROKEN: Tactic syntax placed inside Gallina assignment *)
Definition my_id (n : nat) : nat :=
  intros n; exact n.

(* ✅ CORRECT: Gallina expression *)
Definition my_id (n : nat) : nat := n.

(* ✅ CORRECT: Interactive tactic definition *)
Definition my_id_tactic (n : nat) : nat.
Proof.
  exact n.
Defined. (* Use Defined for transparent computational values *)
```

## 4. SSReflect Dialect Contamination Antipatterns

Autonomous agents trained on general theorem-proving corpora frequently mix SSReflect syntax into Vanilla Ltac. Unless `Require Import ssreflect.` is active, SSReflect keywords trigger immediate parse errors.

| **Operation**      | **❌ SSReflect Antipattern** | **Fatal Parse Error**               | **✅ Vanilla Ltac Equivalent**         |
| ------------------ | ---------------------------- | ----------------------------------- | -------------------------------------- |
| **Intro**          | `move=> x y H.`              | `Syntax error: [ident] expected`    | `intros x y H.`                        |
| **Destruct Intro** | `move=> [x [y H]].`          | `Syntax error: [ident] expected`    | `intros [x [y H]].`                    |
| **Terminal**       | `by [].` / `done.`           | `The reference by was not found`    | `now auto.` / `reflexivity.` / `easy.` |
| **Local Lemma**    | `have H: P by ...`           | `The reference have was not found`  | `assert (H : P) by ...`                |
| **Sufficiency**    | `suff: P by ...`             | `The reference suff was not found`  | `enough (H : P) by ...`                |
| **Trivial Branch** | `//`                         | `Syntax error: [tactic] expected`   | `; try easy.` / `; auto.`              |
| **Simplification** | `/=`                         | `Syntax error: [tactic] expected`   | `simpl.` / `cbn.`                      |
| **Congruence**     | `congr f.`                   | `The reference congr was not found` | `f_equal.`                             |
| **Induction**      | `elim: n => [\| n' IH].`     | `The reference elim was not found`  | `induction n as [\| n' IH].`           |
| **Revert**         | `move: x.`                   | `The reference move was not found`  | `revert x.`                            |

## 5. Software Foundations & Proof Engineering Gotchas

### 5.1. Context Explosion from Bare `inversion`

Using bare `inversion H.` generates excessive synthetic equality hypotheses (`H0 : x = y`), introduces unneeded meta-variables, and leaves the consumed hypothesis `H` in scope.

- Standardize the Software Foundations / CompCert destructive inversion macro:
  ```Coq
  Ltac inv H := inversion H; subst; clear H.
  ```

```Coq
(* ❌ BROKEN: Context polluted with un-substituted equalities and dead assumptions *)
Lemma eval_step_inv : forall t1 t2 T,
  has_type empty (t_app t1 t2) T -> False.
Proof.
  intros t1 t2 T H.
  inversion H.
  (* Local context is now filled with Gamma0, t0, t3, T1, H1, H2, H3, H4, H.
     The agent is easily distracted by stale hypotheses. *)
Abort.

(* ✅ CORRECT: Destructive inversion cleans equalities and consumed hypotheses *)
Ltac inv H := inversion H; subst; clear H.

Lemma eval_step_inv : forall t1 t2 T,
  has_type empty (t_app t1 t2) T -> False.
Proof.
  intros t1 t2 T H.
  inv H.
  (* Only genuine premises remain; all trivial equations are substituted out. *)
Abort.
```

### 5.2. Premature `induction` on Indexed Inductive Relations

Applying `induction` directly to an inductive predicate whose parameters contain compound expressions (e.g., `step (t_app t1 t2) t'` or `has_type empty t T`) causes Rocq to generalize away the index, destroying the specific term equality in the inductive hypotheses.

- Always isolate compound terms using `remember ... as ... eqn:...` and generalize dependent parameters using `revert` before calling `induction`.

```Coq
(* ❌ BROKEN: Direct induction over an indexed relation *)
Theorem progress : forall t T,
  has_type empty t T ->
  value t \/ (exists t', t --> t').
Proof.
  intros t T Ht.
  induction Ht.
  (* Fails: "empty" was generalized to an arbitrary context Gamma in all branches.
     In T_Var, we can no longer deduce a contradiction from (empty x = Some T). *)
Abort.

(* ✅ CORRECT: Protecting indices via remember and revert *)
Theorem progress : forall t T,
  has_type empty t T ->
  value t \/ (exists t', t --> t').
Proof.
  intros t T Ht.
  remember empty as Gamma eqn:HeqGamma.
  induction Ht; subst.
  - (* T_Var: HeqGamma proves Gamma = empty, immediately resolving contradiction *)
    discriminate HeqGamma.
  - (* T_Abs *) left. apply v_abs.
  - (* T_App *)
    right.
    destruct (IHHt1 eq_refl) as [HV1 | [t1' Hstep1]].
    + (* ... proceed with clean hypotheses ... *)
Abort.
```

### 5.3. Uncontrolled Simplification (`compute` on Symbolic Terms)

`compute` and unrestricted `simpl.` aggressively unfold definitions, abstract data structures, and inductive fixpoints. On symbolic expressions containing free variables, this can expand ASTs into multi-megabyte lambda terms that freeze the prover.

- Restrict reductions to targeted functions using `cbn [f g]`, `unfold f`, or `change`.
- Reserve `compute` and `vm_compute` strictly for closed ground terms (e.g., evaluating concrete arithmetic or reflection proofs).

```Coq
(* ❌ BROKEN: Global expansion of complex string and map implementations *)
Lemma lookup_state_update : forall st x v,
  (x |-> v ; st) x = v.
Proof.
  intros st x v.
  compute. (* Expands ASCII comparison trees into thousands of lines of AST *)
Abort.

(* ✅ CORRECT: Targeted unfolding and simplification *)
Lemma lookup_state_update : forall st x v,
  (x |-> v ; st) x = v.
Proof.
  intros st x v.
  unfold update.
  destruct (String.eqb_spec x x) as [Heq | Hneq].
  - reflexivity.
  - contradiction Hneq; reflexivity.
Qed.
```

### 5.4. Sibling Verification via Specialized Solvers

Do not invoke unconstrained `auto` or `eauto` with large search depths on arithmetic or uninterpreted functions; this leads to exponential backtracking and timeouts.

| **Goal Domain**                                  | **❌ Fragile / Slow**             | **✅ Idiomatic Decision Procedure** |
| ------------------------------------------------ | --------------------------------- | ----------------------------------- |
| **Linear Arithmetic ($\mathbb{N}, \mathbb{Z}$)** | `auto`, `omega` (removed in 8.14) | `lia.`                              |
| **Non-Linear Arithmetic ($\mathbb{Z}$)**         | Unbounded manual rewrites         | `nia.` or `zify; lia.`              |
| **Uninterpreted Equality & Inversion**           | Repeated `inversion; subst`       | `congruence.`                       |
| **Pure Propositional Logic**                     | Deep `eauto 10`                   | `tauto.` or `intuition.`            |
| **Contradictory Hypothesis Types**               | `inversion H`                     | `discriminate.` or `congruence.`    |

## 6. Sort Constraints on Records with Informative Fields (`cannot-define-projection`)

### 6.1. The Informative Field in `Prop` Record Pitfall

When defining Gallina `Record` or `Structure` types to encapsulate specifications, parsing relations, or invariants, placing the record in sort `Prop` while including computational data fields (`u8`, `usize`, `nat`, slices, or abstract types in `Type` / `Set`) triggers Rocq's information erasure restrictions.

```Coq
(* ❌ BROKEN: Record in Prop containing informative fields *)
Record tlv_entry : Prop := mk_entry {
  entry_tag : u8;       (* Informative field: u8 is in Set / Type *)
  entry_len : usize;    (* Informative field: usize is in Set / Type *)
  entry_valid : True
}.

(* Compiler Warning:
   Warning: entry_tag cannot be defined because it is informative and
   tlv_entry is not. [cannot-define-projection,records,default] *)
```

### 6.2. Consequence and Fix

When this warning is emitted, Rocq **suppresses generation of the field projection functions** (`entry_tag`, `entry_len`). Downstream references fail with:

```text
Error: The reference entry_tag was not found in the current environment.
```

**Resolution Rule**:

- Any `Record` containing fields whose types inhabit `Set` or `Type` **must** be declared with sort `: Type := ...` (or `: Set := ...`).
- Reserve `Record ... : Prop := ...` strictly for records where **all** fields are propositions (`P : Prop`, equalities `x = y`, etc.).

```Coq
(* ✅ CORRECT: Record declared in Type generates all projections *)
Record tlv_entry : Type := mk_entry {
  entry_tag : u8;
  entry_len : usize;
  entry_valid : True
}.
```
