# lean-portfolio

Lean 4 / Mathlib formalization portfolio.

Targets are chosen from the [missing undergraduate mathematics in Mathlib](https://leanprover-community.github.io/undergrad_todo.html) list, each verified against current Mathlib source before starting (see [TARGETS.md](TARGETS.md)).

## Second target

**Probability generating function** — for an `ℕ`-valued random variable `X`, the function
`pgf X μ t = μ[t ^ X]`, mirroring Mathlib's `mgf` API. Absent from Mathlib as of 2026-08-30
(re-verified against the current source under several names).

- [`LeanPortfolio/ProbabilityGeneratingFunction.lean`](LeanPortfolio/ProbabilityGeneratingFunction.lean)
- Status: **fully proved** — no `sorry`; `#print axioms` on every main theorem reports only
  `propext`, `Classical.choice`, `Quot.sound`.
- **Submitted to Mathlib:** [leanprover-community/mathlib4#43229](https://github.com/leanprover-community/mathlib4/pull/43229)
- API: values at `0` and `1`, nonnegativity, monotonicity and boundedness on `[0, 1]`,
  integrability of the integrand on `[-1, 1]`, congruence lemmas (a.e. equality and
  `IdentDistrib`), the power-series form `pgf X μ t = ∑' n, μ.real (X ⁻¹' {n}) * t ^ n`.
- Main theorems: `hasFPowerSeriesAt_pgf` / `analyticAt_pgf` (near `0` the generating function
  *is* the power series whose coefficients are the point masses),
  `iteratedDeriv_pgf_zero` (**the `n`-th derivative at `0` is `n ! * P(X = n)`**, so the
  derivatives recover the distribution), **the generating function determines the law**
  (`map_eq_map_of_pgf_eq`, by the uniqueness of power-series coefficients), the product
  formula for sums of independent variables
  (`IndepFun.pgf_add`, `iIndepFun.pgf_sum`), and the bridge to the moment-generating
  function (`pgf_exp_eq_mgf`: `pgf X μ (exp s) = mgf X μ s`).
- Worked examples in
  [`LeanPortfolio/ProbabilityGeneratingFunctionExamples.lean`](LeanPortfolio/ProbabilityGeneratingFunctionExamples.lean):
  closed forms for Mathlib's Poisson distribution (`pgf id Po(r) t = exp (r * (t - 1))`,
  valid for every real `t`) and geometric distribution
  (`pgf id (geometricMeasure p) t = p / (1 - (1 - p) * t)` on `[-1, 1]`).

## First target

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
