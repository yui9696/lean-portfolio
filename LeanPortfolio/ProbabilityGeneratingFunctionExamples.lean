/-
Copyright (c) 2026 Moe Tabei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moe Tabei
-/
import LeanPortfolio.ProbabilityGeneratingFunction
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Distributions.Geometric

/-!
# Generating functions of classical distributions

Closed forms of the probability generating function for distributions on `ℕ` in Mathlib.

## Main results

* `ProbabilityTheory.pgf_poissonMeasure`: `pgf id Po(r) t = exp (r * (t - 1))`, for every
  real `t` (the Poisson generating function converges everywhere).
* `ProbabilityTheory.pgf_geometricMeasure`: `pgf id (geometricMeasure p) t
  = p / (1 - (1 - p) * t)` for `|t| ≤ 1`.
-/

open MeasureTheory Real Nat

noncomputable section

open scoped MeasureTheory ProbabilityTheory ENNReal NNReal

namespace ProbabilityTheory

/-- The generating function of the Poisson distribution: `E[t ^ N] = exp (r * (t - 1))`.
This holds for every real `t`, not only on `[-1, 1]`. -/
theorem pgf_poissonMeasure (r : ℝ≥0) (t : ℝ) :
    pgf id Po(r) t = exp (r * (t - 1)) := by
  have h_int : Integrable (fun n : ℕ => t ^ n) Po(r) := by
    rw [integrable_poissonMeasure_iff]
    refine ((NormedSpace.expSeries_div_hasSum_exp ((r : ℝ) * |t|)).summable.mul_left
      (exp (-(r : ℝ)))).congr fun n => ?_
    rw [norm_pow, Real.norm_eq_abs, mul_pow]
    ring
  simp only [pgf_def, id_eq]
  rw [integral_poissonMeasure' h_int,
    show (fun n : ℕ => (exp (-(r : ℝ)) * (r : ℝ) ^ n / n !) • t ^ n) = fun n : ℕ =>
        exp (-(r : ℝ)) * (((r : ℝ) * t) ^ n / n !) from
      funext fun n => by rw [smul_eq_mul, mul_pow]; ring,
    ((NormedSpace.expSeries_div_hasSum_exp ((r : ℝ) * t)).mul_left (exp (-(r : ℝ)))).tsum_eq,
    ← Real.exp_eq_exp_ℝ, ← Real.exp_add]
  congr 1
  ring

/-- The generating function of the geometric distribution (number of failures before the
first success): `E[t ^ N] = p / (1 - (1 - p) * t)` for `|t| ≤ 1`. -/
theorem pgf_geometricMeasure {p : unitInterval} (hp : p ≠ 0) {t : ℝ} (ht : |t| ≤ 1) :
    pgf id (geometricMeasure p) t = p / (1 - (1 - p) * t) := by
  have hp0 : (0 : ℝ) < p := by grind
  have habs : |(1 - (p : ℝ)) * t| < 1 := by
    rw [abs_mul, abs_of_nonneg (by linarith [p.2.2] : (0 : ℝ) ≤ 1 - p)]
    calc (1 - (p : ℝ)) * |t| ≤ (1 - (p : ℝ)) * 1 :=
          mul_le_mul_of_nonneg_left ht (by linarith [p.2.2])
      _ < 1 := by linarith
  rw [pgf_eq_tsum measurable_id ht]
  simp only [Set.preimage_id, geometricMeasure_real_singleton hp]
  rw [show (fun n : ℕ => ((1 - (p : ℝ)) ^ n * p) * t ^ n) = fun n : ℕ =>
        (p : ℝ) * ((1 - (p : ℝ)) * t) ^ n from funext fun n => by rw [mul_pow]; ring,
    tsum_mul_left, tsum_geometric_of_abs_lt_one habs, div_eq_mul_inv]

end ProbabilityTheory
