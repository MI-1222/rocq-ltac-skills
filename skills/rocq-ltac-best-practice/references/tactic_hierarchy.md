# Deterministic Tactic Hierarchy & Automation Discipline

This reference defines the deterministic tactic hierarchy, automation boundaries, and hint database rules for autonomous theorem proving in Rocq using **Pure Vanilla Ltac**.

---

## 1. The 6-Tier Tactic Automation Hierarchy

Autonomous agents must not guess automated tactics at random. Apply automation strictly according to the **6-Tier Priority Hierarchy**, progressing from deterministic syntactic checks to bounded searches:

```mermaid
graph TD
  T1["Tier 1: Syntactic Closers<br/>reflexivity, discriminate, contradiction, assumption"]
  T2["Tier 2: Equational Solvers<br/>subst, congruence, f_equal"]
  T3["Tier 3: Propositional Solvers<br/>tauto, intuition idtac"]
  T4["Tier 4: Linear Arithmetic<br/>lia (paired with zify when needed)"]
  T5["Tier 5: Forward Search<br/>auto, auto with db"]
  T6["Tier 6: Bounded Backtracking<br/>eauto n (depth n <= 5)"]

  T1 --> T2
  T2 --> T3
  T3 --> T4
  T4 --> T5
  T5 --> T6
```

### Hierarchy Breakdown

| Tier       | Tactics                                                            | Target Domain                                                                  | Performance      | Guarantees                                                                                 |
| :--------- | :----------------------------------------------------------------- | :----------------------------------------------------------------------------- | :--------------- | :----------------------------------------------------------------------------------------- |
| **Tier 1** | `reflexivity`<br>`discriminate`<br>`contradiction`<br>`assumption` | Definitional equality, constructor collision, absurd hypotheses                | $O(1)$ syntactic | Guaranteed to terminate instantly. Never pollutes context.                                 |
| **Tier 2** | `subst`<br>`congruence`<br>`f_equal`                               | Uninterpreted function symbols, equality elimination, transitive chains        | Polynomial       | Solves uninterpreted equational logic without unfolding definitions.                       |
| **Tier 3** | `tauto`<br>`intuition idtac`                                       | Intuitionistic propositional logic ($\land, \lor, \to, \neg, \leftrightarrow$) | Fast SAT         | Decides propositional validity. `intuition idtac` simplifies without expanding predicates. |
| **Tier 4** | `lia`                                                              | Presburger linear integer arithmetic ($\mathbb{Z}, \mathbb{N}$)                | Fast decision    | Completes linear relations. Beware of truncation subtraction on `nat`.                     |
| **Tier 5** | `auto`<br>`auto with db`                                           | Safe forward breadth-first derivation without metavariables                    | Linear / bounded | Applies registered hints up to default depth 5. Never creates existentials.                |
| **Tier 6** | `eauto n` ($n \le 5$)                                              | Backward backtracking search involving existential quantifiers                 | Exponential      | Allows `eapply`. MUST be bounded by an explicit depth parameter.                           |
| **BANNED** | `firstorder`<br>Unbounded `eauto`                                  | First-order predicate calculus, unconstrained unification                      | **Divergent**    | Causes catastrophic timeouts and metavariable leaks. Strictly forbidden.                   |

---

## 2. Bounded Search: `eauto n` and Metavariable Leak Prevention

### The Danger of Unbounded `eauto`

Running bare `eauto.` allows depth-first backtracking search that can:

1. Loop indefinitely on recursive constructors.
2. Instantiate existential metavariables (`?X`) with incorrect temporary terms, rendering sibling subgoals permanently unprovable.

### The Explicit Depth Mandate

Always specify the search depth explicitly:

```coq
(* GOOD: Depth explicitly bounded *)
eapply step_beta; eauto 2.
eapply T_App; eauto 3.

(* MAXIMUM PERMISSIBLE DEPTH *)
eauto 5.

(* STRICTLY FORBIDDEN *)
eauto.         (* No depth limit! *)
firstorder.    (* Non-deterministic predicate search! *)
```

### Eliminating Remaining Evars

If an `eapply` or `eauto` creates existential metavariables (visible in the goal as `?X`), resolve them immediately using `instantiate` or explicit binding:

```coq
(* Explicit witness instantiation *)
eapply lemma_with_domain with (T := nat); eauto 2.
```

---

## 3. Linear Arithmetic (`lia`) Caveats & Truncation Subtraction

The `lia` tactic decides linear integer arithmetic for `nat` and `Z`. However, natural number subtraction is **truncated** ($n - m = 0$ when $n < m$).

### The Truncation Subtraction Trap

In `nat`, `a - b + b = a` is **false** if $a < b$ (since $0 + b = b \ne a$). `lia` fails when an equality relies on negative intermediate results.

### Prevention Protocol

1. **Precondition Case Splitting**: Destruct the comparison before invoking `lia`:
   ```coq
   destruct (Nat.le_ge_cases b a) as [Hle | Hgt].
   - (* Case b <= a: lia succeeds *) lia.
   - (* Case b > a: handle truncation explicitly *) lia.
   ```
2. **Lifting to $\mathbb{Z}$ via `zify`**: Run `zify.` before arithmetic simplification to convert `nat` terms into true mathematical integers:
   ```coq
   zify. lia.
   ```

---

## 4. Hint Database Discipline (`#[local] Hint Resolve`)

Hints registered into hint databases alter the behavior of `auto` and `eauto`. Unrestricted hints pollute downstream proofs.

### Strict Scoping Rules

1. **Always Use `#[local]`**: Never declare bare `Hint Resolve` or `Global Hint`. Always scope to the current module:
   ```coq
   #[local] Hint Resolve my_sound_step : core.
   #[local] Hint Constructors has_type : core.
   ```
2. **Dedicated Domain Databases**: For large theories, isolate hints in custom databases rather than polluting `core`:

   ```coq
   Create HintDb semantics_db.
   #[local] Hint Resolve step_app1 step_app2 : semantics_db.

   (* In proofs, invoke explicitly *)
   eauto with semantics_db.
   ```

3. **Avoid Transitivity in Hints**: Never add transitive lemmas (e.g., `rtc_step`, `le_trans`) to `Hint Resolve`. They create infinite cycles in `eauto` search trees.
