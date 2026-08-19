# lean-portfolio

Lean 4 / Mathlib formalization portfolio.

Targets are chosen from the [missing undergraduate mathematics in Mathlib](https://leanprover-community.github.io/undergrad_todo.html) list, each verified against current Mathlib source before starting (see [TARGETS.md](TARGETS.md)).

## Current target

**Simultaneous diagonalization of two real quadratic forms** — for matrices, if `A` is positive definite and `B` is symmetric, there is an invertible `P` with `Pᵀ A P = 1` and `Pᵀ B P` diagonal.

- [`LeanPortfolio/SimultaneousDiagonalization.lean`](LeanPortfolio/SimultaneousDiagonalization.lean)
- Status: **fully proved** — no `sorry`; `#print axioms` reports only
  `propext`, `Classical.choice`, `Quot.sound`.
- **Submitted to Mathlib:** [leanprover-community/mathlib4#42931](https://github.com/leanprover-community/mathlib4/pull/42931)
- Also proved: the quadratic-form phrasing (one change of variables sends `A` to `∑ xᵢ ^ 2`
  and `B` to `∑ dᵢ * xᵢ ^ 2`), and positivity of the `dᵢ` when `B` is positive definite too.
- Proof route: conjugating by the inverse of `CFC.sqrt A` reduces `A` to the identity,
  then the real spectral theorem diagonalizes the transformed `B`.
- Intended endpoint: a Mathlib pull request.

## Building

```
lake exe cache get
lake build
```

Toolchain: Lean 4.33.0 (pinned in `lean-toolchain`).
