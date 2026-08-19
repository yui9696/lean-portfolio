# lean-portfolio

Lean 4 / Mathlib formalization portfolio.

Targets are chosen from the [missing undergraduate mathematics in Mathlib](https://leanprover-community.github.io/undergrad_todo.html) list, each verified against current Mathlib source before starting (see [TARGETS.md](TARGETS.md)).

## Current target

**Simultaneous diagonalization of two real quadratic forms** — for matrices, if `A` is positive definite and `B` is symmetric, there is an invertible `P` with `Pᵀ A P = 1` and `Pᵀ B P` diagonal.

- [`LeanPortfolio/SimultaneousDiagonalization.lean`](LeanPortfolio/SimultaneousDiagonalization.lean)
- Status: statement compiles, proof in progress.
- Intended endpoint: a Mathlib pull request.

## Building

```
lake exe cache get
lake build
```

Toolchain: Lean 4.33.0 (pinned in `lean-toolchain`).
