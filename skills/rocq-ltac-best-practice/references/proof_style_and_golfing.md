# Proof Style, Bullet Discipline & Proof Golfing

This reference defines formatting rules, bullet hierarchy disciplines, and proof golfing strategies for producing clean, idiomatic, and maintainable proofs in Rocq using **Pure Vanilla Ltac**.

---

## 1. Strict Bullet Hierarchy Disciplines

When tactics branch into multiple subgoals (e.g., `destruct`, `induction`, `inversion`, `constructor`), agents must strictly structure and isolate each branch. Failing to use bullets allows unresolved side goals to leak into subsequent cases, obscuring proof boundaries.

### The Standard 3-Level Bullet Hierarchy

Rocq supports three primary bullet characters in strict cyclical order:

1. Level 1: Hyphen (`-`)
2. Level 2: Plus (`+`)
3. Level 3: Asterisk (`*`)
4. Beyond Level 3: Repeated bullets (`--`, `++`, `**`) or curly braces (`{ ... }`)

```coq
Theorem bullet_hierarchy_example : forall (b1 b2 b3 : bool),
  b1 = true \/ b2 = true \/ b3 = true \/ (b1 = false /\ b2 = false /\ b3 = false).
Proof.
  intros b1 b2 b3.
  destruct b1.
  - (* Level 1: b1 = true *)
    left. reflexivity.
  - (* Level 1: b1 = false *)
    destruct b2.
    + (* Level 2: b2 = true *)
      right. left. reflexivity.
    + (* Level 2: b2 = false *)
      destruct b3.
      * (* Level 3: b3 = true *)
        right. right. left. reflexivity.
      * (* Level 3: b3 = false *)
        right. right. right. split; reflexivity.
Qed.
```

### Bullet Spacing Rule

Always follow bullets with a space and place the tactic on the same line or indented on the next line:

- ✅ `- reflexivity.` or `-\n  reflexivity.`
- ❌ `-reflexivity.` (Syntax error)

---

## 2. Explicit Subgoal Isolation with Curly Braces `{ ... }`

For large or non-trivial subgoals (especially those containing intermediate `assert` lemmas), enclose the branch in curly braces `{ ... }`.

### Advantages of Curly Braces

- **Complete Subgoal Isolation**: Within `{ ... }`, only the focused subgoal is visible. Sibling goals cannot be accidentally targeted.
- **Enforced Closure**: Rocq requires the enclosed block to close the goal completely before exiting `}`. If goals remain, it immediately reports `Error: This proof is not finished`.

```coq
Lemma braces_example : forall (P Q : Prop), P /\ Q -> Q /\ P.
Proof.
  intros P Q H.
  destruct H as [HP HQ].
  split.
  { (* Subgoal 1: ⊢ Q *)
    assumption. }
  { (* Subgoal 2: ⊢ P *)
    assumption. }
Qed.
```

---

## 3. High-Reliability Tactic Idioms

The core Rocq test-suite demonstrates several robust patterns that avoid fragile proof scripts:

### A. Immediate Goal Closure with `now`

`now <tac>` is a standard shorthand for `solve [ tac; easy ]`:

- It requires that `<tac>` completely discharges the goal.
- If `<tac>` leaves intermediate subgoals, `now` immediately fails at that point, preventing unproven goals from leaking downstream.

```coq
Lemma now_example : forall n, n + 0 = n.
Proof.
  intro n.
  now rewrite Nat.add_0_r.
Qed.
```

### B. Safe Subgoal Dispatch with `all: try solve [ ... ]`

When applying a tactic across multiple generated subgoals:

- Bare `; try <tac>` partially reduces subgoals, potentially leaving them in an awkward intermediate state (Goal Pollution).
- `all: try solve [ trivial | lia | reflexivity ]` attempts to completely solve each branch. Branches that cannot be fully closed are left **completely untouched**, preserving clean goals for specialized tactics.

```coq
Theorem solve_all_example : forall (b : bool), ...
Proof.
  destruct b;
  all: try solve [ reflexivity | lia ].
  - (* Handle remaining non-trivial branch cleanly *)
    admit.
Admitted.
```

### C. Guarding Loops with `progress`

Unbounded repetition via `repeat <tac>` can enter infinite loops if `<tac>` matches symmetrically (e.g., `repeat rewrite Nat.add_comm` swaps $a + b$ back and forth indefinitely).

- Always guard iterative constructors or rewrites with `progress`:
  ```coq
  repeat progress econstructor.
  ```
- If `<tac>` executes without transforming the goal term or context, `progress` throws an exception that safely terminates the `repeat` loop.

---

## 4. Regression Hazards & Anti-Patterns

### ❌ Anti-Pattern 1: Context-Accumulating `repeat match`

```coq
(* DANGEROUS: Loops forever and exhausts memory *)
Ltac bad_match_loop :=
  repeat match goal with
  | [ H : ?P -> ?Q, H' : ?P |- _ ] =>
      pose proof (H H')
  end.
```

- **Hazard**: Each iteration adds a new hypothesis without removing or clearing the original `H`. The match continually triggers on the same premises until an Out of Memory (OOM) crash occurs.
- **Remedy**: Always consume or clear the matched hypothesis, or wrap the match in `progress`:

  ```coq
  Ltac good_match_step :=
    match goal with
    | [ H : ?P -> ?Q, H' : ?P |- _ ] =>
        let H'' := fresh "H" in
        pose proof (H H') as H''; clear H
    end.

  (** Safe non-diverging normalizer guarded by progress *)
  Ltac safe_simplify :=
    repeat progress (
      match goal with
      | H : True |- _ => clear H
      | H : _ /\ _ |- _ => destruct H
      | H : exists _, _ |- _ => destruct H
      | H : ?x = ?x |- _ => clear H
      end
    ).
  ```

### ❌ Anti-Pattern 2: Unconstrained `simpl in *`

Running `simpl in *` across a context containing large dependent records, typeclass dictionaries, or abstract functions traverses every hypothesis, triggering exponential unification slowdowns and freezing compilation.

- **Remedy**: Target specific hypotheses with `cbn [f] in H` or `unfold def in H`.

---

## 5. Proof Golfing: Compacting Redundant Steps

### Technique A: Semicolon `;` Tactic Chaining

```coq
(* VERBOSE: 2 identical branches *)
Lemma or_comm_verbose : forall (P Q : Prop), P \/ Q -> Q \/ P.
Proof.
  intros P Q H.
  destruct H.
  - right. assumption.
  - left. assumption.
Qed.

(* GOLFED: Semicolon handles both cases cleanly *)
Lemma or_comm_golfed : forall (P Q : Prop), P \/ Q -> Q \/ P.
Proof.
  intros P Q [HP | HQ]; [right | left]; assumption.
Qed.
```

### Technique B: Combining Destruction into `intros`

Pattern-match structured hypotheses directly inside `intros`:

- Conjunction: `intros [H1 H2].` instead of `intros H. destruct H as [H1 H2].`
- Disjunction: `intros [H1 | H2].` instead of `intros H. destruct H as [H1 | H2].`
- Existential: `intros [x Hx].` instead of `intros H. destruct H as [x Hx].`
