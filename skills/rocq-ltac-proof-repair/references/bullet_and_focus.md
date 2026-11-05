# Bullet Hierarchies, Goal Focusing & Proof Structuring

This reference provides techniques to diagnose and repair subgoal tree desynchronization, `Wrong bullet` errors, and scope isolation using bullets (`-`, `+`, `*`) and curly braces (`{ ... }`) in Rocq 9.0+ and Coq 8.20.

---

## 1. Error Signatures

### Signature A: Wrong Bullet Level

```text
Error: Wrong bullet '-': Bullet '+' is mandatory here.
```

A bullet character was used that does not match the active hierarchical depth expected by the proof engine.

### Signature B: Unfinished Subgoal

```text
Error: Current bullet '-' is not finished.
```

A sibling or parent bullet was encountered before the preceding focused subgoal was completely discharged.

### Signature C: Syntax Error on Bullet Terminator

```text
Syntax error: [tactic] expected after '-' (in [tactic_expr]).
```

A period was erroneously attached to a bullet or brace (e.g., `-.` or `{.`).

---

## 2. Root Cause & Theoretical Background

1. **Subgoal Stack Management in Rocq**:
   When a tactic generates multiple subgoals (e.g., `split`, `destruct`, `induction`), Rocq arranges them in an ordered stack.
   - Bullets enforce structured programming by focusing the proof engine strictly on the topmost subgoal.
   - While focused on a bullet, all other subgoals are temporarily masked until the current goal is solved or closed.
2. **Standard Bullet Hierarchy**:
   Rocq recognizes a recurring cyclical hierarchy of bullets:
   $$\text{Level 1: } - \quad \longrightarrow \quad \text{Level 2: } + \quad \longrightarrow \quad \text{Level 3: } * \quad \longrightarrow \quad \text{Level 4: } -- \quad \longrightarrow \quad \text{Level 5: } ++ \quad \longrightarrow \quad \text{Level 6: } **$$
   - All siblings at the same branch depth must use the **exact same bullet symbol**.
   - Descending into a child subgoal requires switching to the next symbol in the hierarchy.
   - Returning to an outer parent branch requires reverting to the parent's bullet symbol.
3. **Curly Brace Scoping (`{ ... }`)**:
   Curly braces focus on the first subgoal and introduce an isolated lexical block.
   - Braces reset the internal bullet hierarchy: inside `{ ... }`, the bullet cycle starts over at `-`.
   - Braces do not require trailing periods and cannot have dots attached.

---

## 3. Anti-Patterns to Avoid

- ❌ **Attaching periods to bullets (`-.`, `+.`, `*.`)**: Bullets are delimiters, not vernacular sentences. Never append a period to `-`, `+`, `*`, `{`, or `}`.
- ❌ **Flattening proof scripts by removing all bullets**: Deleting bullets when a bullet error occurs leads to unstructured, fragile scripts that break on minor goal order changes.
- ❌ **Skipping unproven branches**: Advancing to the next bullet while open subgoals remain in the current branch.

---

## 4. Concrete Prescriptions (Before & After)

### Case 1: Fixing Desynchronized Bullet Levels

**Failing Code (Before):**

```Coq
Lemma and_comm_faulty : forall p q : Prop, p /\ q -> q /\ p.
Proof.
  intros p q [Hp Hq].
  split.
  - exact Hq.
  + exact Hp. (* Error: Wrong bullet '+': Bullet '-' is mandatory here *)
Qed.
```

**Repaired Code (After):**

```Coq
Lemma and_comm_repaired : forall p q : Prop, p /\ q -> q /\ p.
Proof.
  intros p q [Hp Hq].
  split.
  - exact Hq.
  - exact Hp. (* Both subgoals are at the same depth: use identical bullet '-' *)
Qed.
```

---

### Case 2: Multi-Level Branching Hierarchy

When nested tactics produce child subgoals inside an active branch:

```Coq
Lemma nested_branch_example : forall (n m : nat),
  n = 0 \/ n = 1 -> m = 0 \/ m = 1 -> n + m <= 2.
Proof.
  intros n m Hn Hm.
  destruct Hn as [Hn0 | Hn1].
  - (* Outer branch 1: Level 1 bullet '-' *)
    destruct Hm as [Hm0 | Hm1].
    + (* Child branch 1: Level 2 bullet '+' *)
      subst; simpl; lia.
    + (* Child branch 2: Level 2 bullet '+' *)
      subst; simpl; lia.
  - (* Outer branch 2: Return to Level 1 bullet '-' *)
    destruct Hm as [Hm0 | Hm1].
    + subst; simpl; lia.
    + subst; simpl; lia.
Qed.
```

---

### Case 3: Isolating Deep Proof Branches with Braces (`{ ... }`)

For complex proofs where tracking bullet depths ($--$, $++$, $**$) is error-prone, encapsulate subproofs in curly braces:

```Coq
Lemma braces_scoping_example : forall (p q r : Prop),
  (p /\ q) \/ (p /\ r) -> p /\ (q \/ r).
Proof.
  intros p q r [Hpq | Hpr].
  { (* Isolate Subgoal 1 *)
    destruct Hpq as [Hp Hq].
    split.
    - exact Hp.
    - left; exact Hq.
  }
  { (* Isolate Subgoal 2 *)
    destruct Hpr as [Hp Hr].
    split.
    - exact Hp.
    - right; exact Hr.
  }
Qed.
```

---

## 5. Fallback Procedures

1. **Query Active Goal State via `rocq_goal.py`**:
   If uncertain which subgoals remain open or which bullet level is required, query the state before the failing bullet:
   ```bash
   python3 skills/rocq-ltac-interactive-proof/scripts/rocq_goal.py --file <file.v> --line <N-1> --json
   ```
   Check the `subgoals` field and whether the focused goal has completed.
2. **Temporary Semicolon Compaction**:
   For simple branches where the same tactic solves all child goals, use the tactical combination operator `;`:
   ```Coq
   split; [exact Hq | exact Hp].
   ```
   or if a single tactic solves all generated branches:
   ```Coq
   destruct H; subst; auto.
   ```
