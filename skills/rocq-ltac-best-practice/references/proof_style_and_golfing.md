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

## 3. Proof Golfing: Compacting Redundant Proof Steps

**Proof golfing** eliminates redundant boilerplate without sacrificing clarity or kernel soundness.

### Technique A: Semicolon `;` Tactic Chaining

When a tactic generates multiple subgoals that can all be resolved by the same trailing tactic, chain them using `;`:

```coq
(* VERBOSE: 4 identical branches *)
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

### Technique B: Semicolon with `try` for Heterogeneous Branches

When most branches can be closed by a simple decision procedure but one or two require custom work:

```coq
Theorem eval_cases_golfed : forall c st st',
  ceval c st st' -> ...
Proof.
  induction 1; intros; inv H; try solve [ reflexivity | lia ].
  - (* Custom treatment for remaining non-trivial branch *)
    eapply ceval_seq_intermediate; eauto.
Qed.
```

### Technique C: Combining Destruction into `intros`

Pattern-match structured hypotheses directly inside `intros`:

- Conjunction: `intros [H1 H2].` instead of `intros H. destruct H as [H1 H2].`
- Disjunction: `intros [H1 | H2].` instead of `intros H. destruct H as [H1 | H2].`
- Existential: `intros [x Hx].` instead of `intros H. destruct H as [x Hx].`

---

## 4. Performance Tuning & Profiling

If compiling a proof script is sluggish:

1. **Profile Tactic Execution Time**:
   ```coq
   Set Ltac Profiling.
   (* Run proof *)
   Show Ltac Profile.
   ```
2. **Replace Slow `auto` with Explicit Steps**: If `auto` spends seconds backtracking, replace it with the exact `apply <lemma>; assumption` sequence discovered.
3. **Limit Decision Procedure Scopes**:
   - For `lia`, clear irrelevant hypotheses beforehand: `clear H1 H2. lia.`
   - For `congruence`, avoid unfolding definitions: `congruence` operates fastest on raw uninterpreted symbols.
