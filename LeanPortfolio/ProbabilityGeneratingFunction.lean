/-
Copyright (c) 2026 Moe Tabei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moe Tabei
-/
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Probability generating function

For an `ℕ`-valued random variable `X`, the probability generating function is
`pgf X μ t = μ[t ^ X]`, the analogue for discrete variables of the moment-generating
function `mgf`.

## Main definitions

* `ProbabilityTheory.pgf X μ t`: probability generating function of `X` with respect to
  measure `μ`, `μ[t ^ X]`.

## Main results

* `ProbabilityTheory.integrable_pow_pgf`: for `|t| ≤ 1` and a finite measure the defining
  integrand is integrable, so the generating function is defined on `[-1, 1]`.
* `ProbabilityTheory.hasSum_pgf` and `ProbabilityTheory.pgf_eq_tsum`: the usual power-series
  form `pgf X μ t = ∑' n, μ.real (X ⁻¹' {n}) * t ^ n`.
* `ProbabilityTheory.hasFPowerSeriesAt_pgf` and `ProbabilityTheory.analyticAt_pgf`: near `0`
  the generating function *is* the power series whose coefficients are the point masses.
* `ProbabilityTheory.iteratedDeriv_pgf_zero`: the `n`-th derivative at `0` is
  `n ! * μ.real (X ⁻¹' {n})`, so the derivatives at `0` recover the distribution.
* `ProbabilityTheory.map_eq_map_of_pgf_eq`: the generating function determines the law —
  if two generating functions agree on `[-1, 1]`, the distributions coincide.
* `ProbabilityTheory.IndepFun.pgf_add`: if `X` and `Y` are independent then
  `pgf (X + Y) μ t = pgf X μ t * pgf Y μ t`; `ProbabilityTheory.iIndepFun.pgf_sum` is the
  version for finitely many independent variables.
-/

open MeasureTheory Filter Finset Real Nat

noncomputable section

open scoped MeasureTheory ProbabilityTheory ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {m : MeasurableSpace Ω} {X : Ω → ℕ} {μ : Measure Ω} {t s : ℝ}

/-- Probability generating function of an `ℕ`-valued random variable `X`:
`fun t => μ[t ^ X]`. -/
def pgf (X : Ω → ℕ) (μ : Measure Ω) (t : ℝ) : ℝ :=
  μ[fun ω => t ^ X ω]

lemma pgf_def (X : Ω → ℕ) (μ : Measure Ω) (t : ℝ) : pgf X μ t = μ[fun ω => t ^ X ω] := rfl

@[simp]
lemma pgf_zero_measure : pgf X (0 : Measure Ω) t = 0 := by simp [pgf]

/-- The value at `0` of the generating function is the mass of `{X = 0}`. -/
lemma pgf_zero (hX : Measurable X) : pgf X μ 0 = μ.real (X ⁻¹' {0}) := by
  have h_eq : (fun ω => (0 : ℝ) ^ X ω) = (X ⁻¹' {0}).indicator fun _ => (1 : ℝ) := by
    ext ω
    by_cases h : X ω = 0 <;> simp [h]
  rw [pgf, h_eq, integral_indicator_const _ (hX (measurableSet_singleton 0)), smul_eq_mul, mul_one]

@[simp]
lemma pgf_one [IsProbabilityMeasure μ] : pgf X μ 1 = 1 := by simp [pgf]

/-- Without a probability assumption, the value at `1` is the total mass. -/
lemma pgf_one' : pgf X μ 1 = μ.real Set.univ := by simp [pgf]

lemma pgf_const [IsProbabilityMeasure μ] (c : ℕ) : pgf (fun _ => c) μ t = t ^ c := by
  simp [pgf]

@[simp]
lemma pgf_zero_fun [IsProbabilityMeasure μ] : pgf (0 : Ω → ℕ) μ t = 1 := by simp [pgf]

lemma pgf_nonneg (ht : 0 ≤ t) : 0 ≤ pgf X μ t :=
  integral_nonneg fun _ => pow_nonneg ht _

lemma pgf_congr {Y : Ω → ℕ} (h : X =ᵐ[μ] Y) : pgf X μ t = pgf Y μ t :=
  integral_congr_ae <| by filter_upwards [h] with ω hω using by rw [hω]

lemma pgf_id_map (hX : AEMeasurable X μ) : pgf id (μ.map X) = pgf X μ := by
  ext t
  rw [pgf, pgf, integral_map hX Measurable.of_discrete.aestronglyMeasurable]
  rfl

/-- Identically distributed random variables have the same generating function. -/
lemma pgf_congr_identDistrib {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'}
    {Y : Ω' → ℕ} (h : IdentDistrib X Y μ μ') :
    pgf X μ = pgf Y μ' := by
  rw [← pgf_id_map h.aemeasurable_fst, ← pgf_id_map h.aemeasurable_snd, h.map_eq]

/-- The generating function evaluated at `exp s` is the moment-generating function of `X`
viewed as a real random variable. -/
lemma pgf_exp_eq_mgf (s : ℝ) : pgf X μ (exp s) = mgf (fun ω => (X ω : ℝ)) μ s := by
  simp only [pgf, mgf, ← Real.exp_nat_mul, mul_comm s]

/-- For `|t| ≤ 1` the integrand defining `pgf` is integrable with respect to any finite
measure: the generating function of an `ℕ`-valued variable is always defined on `[-1, 1]`. -/
lemma integrable_pow_pgf [IsFiniteMeasure μ] (hX : Measurable X) (ht : |t| ≤ 1) :
    Integrable (fun ω => t ^ X ω) μ := by
  refine Integrable.mono' (integrable_const 1)
    (((Measurable.of_discrete (f := fun n : ℕ => t ^ n)).comp hX).aestronglyMeasurable) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_one₀ (abs_nonneg t) ht

/-- The generating function is monotone on `[0, 1]`. -/
lemma pgf_mono [IsFiniteMeasure μ] (hX : Measurable X) (ht : 0 ≤ t) (hts : t ≤ s) (hs : s ≤ 1) :
    pgf X μ t ≤ pgf X μ s :=
  integral_mono (integrable_pow_pgf hX (abs_le.2 ⟨by linarith, by linarith⟩))
    (integrable_pow_pgf hX (abs_le.2 ⟨by linarith, hs⟩))
    fun ω => pow_le_pow_left₀ ht hts _

lemma pgf_le_one [IsProbabilityMeasure μ] (hX : Measurable X) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    pgf X μ t ≤ 1 :=
  calc pgf X μ t ≤ pgf X μ 1 := pgf_mono hX ht₀ ht₁ le_rfl
    _ = 1 := pgf_one

/-- Power-series form of the generating function: the point masses of `X` are the
coefficients of the series summing to `pgf X μ t`. -/
lemma hasSum_pgf [IsFiniteMeasure μ] (hX : Measurable X) (ht : |t| ≤ 1) :
    HasSum (fun n => μ.real (X ⁻¹' {n}) * t ^ n) (pgf X μ t) := by
  have h_int : Integrable (fun n : ℕ => t ^ n) (μ.map X) := by
    refine Integrable.mono' (integrable_const 1) Measurable.of_discrete.aestronglyMeasurable ?_
    filter_upwards with n
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_one₀ (abs_nonneg t) ht
  rw [pgf, ← integral_map hX.aemeasurable Measurable.of_discrete.aestronglyMeasurable]
  rw [← Measure.sum_smul_dirac (μ.map X)] at h_int ⊢
  refine (hasSum_integral_measure h_int).congr_fun fun n => ?_
  rw [integral_smul_measure, integral_dirac, smul_eq_mul,
    Measure.real, Measure.map_apply hX (measurableSet_singleton n)]

/-- Power-series form of the generating function:
`pgf X μ t = ∑' n, μ.real (X ⁻¹' {n}) * t ^ n`. -/
lemma pgf_eq_tsum [IsFiniteMeasure μ] (hX : Measurable X) (ht : |t| ≤ 1) :
    pgf X μ t = ∑' n, μ.real (X ⁻¹' {n}) * t ^ n :=
  (hasSum_pgf hX ht).tsum_eq.symm

lemma summable_pgf [IsFiniteMeasure μ] (hX : Measurable X) (ht : |t| ≤ 1) :
    Summable fun n => μ.real (X ⁻¹' {n}) * t ^ n :=
  (hasSum_pgf hX ht).summable

/-- The point masses of an `ℕ`-valued random variable sum to the total mass. -/
lemma hasSum_measureReal_preimage_singleton [IsFiniteMeasure μ] (hX : Measurable X) :
    HasSum (fun n => μ.real (X ⁻¹' {n})) (μ.real Set.univ) := by
  simpa [pgf_one'] using hasSum_pgf (μ := μ) (t := 1) hX (by norm_num)

/-- **Abel's limit theorem for generating functions.** `pgf X μ` is continuous at `1` from the
left; the limit is the total mass, which is `1` for a probability measure. -/
theorem tendsto_pgf_nhdsLT_one [IsFiniteMeasure μ] (hX : Measurable X) :
    Tendsto (pgf X μ) (𝓝[<] (1 : ℝ)) (𝓝 (μ.real Set.univ)) := by
  refine (Real.tendsto_tsum_powerSeries_nhdsWithin_lt
    (f := fun n => μ.real (X ⁻¹' {n}))
    (hasSum_measureReal_preimage_singleton hX).tendsto_sum_nat).congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with t ht
  exact (pgf_eq_tsum hX (abs_le.2 ⟨by linarith [ht.1], ht.2.le⟩)).symm

/-- Inside the open unit interval the generating function may be differentiated term by term:
`(pgf X μ)' t = ∑' n, μ.real (X ⁻¹' {n}) * n * t ^ (n - 1)`. -/
theorem hasDerivAt_pgf [IsFiniteMeasure μ] (hX : Measurable X) (ht : |t| < 1) :
    HasDerivAt (pgf X μ)
      (∑' n : ℕ, μ.real (X ⁻¹' {n}) * ((n : ℝ) * t ^ (n - 1))) t := by
  set p : ℕ → ℝ := fun n => μ.real (X ⁻¹' {n}) with hp
  set M : ℝ := μ.real Set.univ with hM
  -- work on a ball of radius `r` with `|t| < r < 1`
  set r : ℝ := (|t| + 1) / 2 with hr
  have hrpos : 0 < r := by rw [hr]; positivity
  have htr : |t| < r := by rw [hr]; linarith
  have hr1 : r < 1 := by rw [hr]; linarith
  have hM0 : 0 ≤ M := measureReal_nonneg
  have hpM : ∀ n, |p n| ≤ M := fun n => by
    rw [hp, abs_of_nonneg measureReal_nonneg]
    exact measureReal_mono (Set.subset_univ _)
  -- the bounding series `M * n * r ^ (n - 1)` is summable
  have hgeo : Summable fun n : ℕ => (n : ℝ) * r ^ n := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
      (by rwa [Real.norm_eq_abs, abs_of_nonneg hrpos.le])
  have key : ∀ n : ℕ, M * ((n : ℝ) * r ^ (n - 1)) = M * r⁻¹ * ((n : ℝ) * r ^ n) := by
    rintro (_ | m)
    · simp
    · rw [Nat.add_sub_cancel, pow_succ]
      field_simp
  have hsum : Summable fun n : ℕ => M * ((n : ℝ) * r ^ (n - 1)) := by
    simp_rw [key]
    exact hgeo.mul_left _
  have h0r : (0 : ℝ) ∈ Metric.ball (0 : ℝ) r := Metric.mem_ball_self hrpos
  have hderiv := hasDerivAt_tsum_of_isPreconnected (u := fun n : ℕ => M * ((n : ℝ) * r ^ (n - 1)))
    (g := fun n z => p n * z ^ n) (g' := fun n z => p n * ((n : ℝ) * z ^ (n - 1)))
    hsum Metric.isOpen_ball (convex_ball (0 : ℝ) r).isPreconnected
    (fun n y _ => (hasDerivAt_pow n y).const_mul (p n))
    (fun n y hy => by
      have hy' : |y| ≤ r := by
        simpa [Real.dist_eq, abs_sub_comm] using (Metric.mem_ball.1 hy).le
      rw [Real.norm_eq_abs, abs_mul]
      refine mul_le_mul (hpM n) ?_ (abs_nonneg _) hM0
      rw [abs_mul, Nat.abs_cast, abs_pow]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg y) hy' _) (Nat.cast_nonneg n))
    h0r
    (summable_of_ne_finset_zero (s := {0}) (fun n hn => by
      simp only [Finset.mem_singleton] at hn
      simp [zero_pow hn]))
    (by simpa [Real.dist_eq] using htr)
  refine hderiv.congr_of_eventuallyEq ?_
  have htball : t ∈ Metric.ball (0 : ℝ) r := by simpa [Real.dist_eq] using htr
  filter_upwards [Metric.isOpen_ball.mem_nhds htball] with z hz
  have hz' : |z| ≤ r := by
    simpa [Real.dist_eq, abs_sub_comm] using (Metric.mem_ball.1 hz).le
  exact pgf_eq_tsum (μ := μ) hX (hz'.trans hr1.le)

section Uniqueness

open FormalMultilinearSeries

/-- Auxiliary: a real power series with bounded coefficients has radius of convergence at
least `1`, hence represents its sum at `0`. -/
private lemma hasFPowerSeriesAt_ofScalarsSum {c : ℕ → ℝ} {C : ℝ} (hc : ∀ n, |c n| ≤ C) :
    HasFPowerSeriesAt (ofScalarsSum c) (ofScalars ℝ c) 0 := by
  have h_rad : (1 : ℝ≥0∞) ≤ (ofScalars ℝ c).radius := by
    simpa using (ofScalars ℝ c).le_radius_of_bound C (r := 1) fun n => by
      rw [ofScalars_norm]
      simpa [Real.norm_eq_abs] using hc n
  exact ((ofScalars ℝ c).hasFPowerSeriesOnBall
    (lt_of_lt_of_le zero_lt_one h_rad)).hasFPowerSeriesAt

/-- Near `0`, the generating function is the power series whose coefficients are the point
masses of `X`. -/
theorem hasFPowerSeriesAt_pgf [IsFiniteMeasure μ] (hX : Measurable X) :
    HasFPowerSeriesAt (pgf X μ) (ofScalars ℝ fun n => μ.real (X ⁻¹' {n})) 0 := by
  refine (hasFPowerSeriesAt_ofScalarsSum (C := μ.real Set.univ) fun n => ?_).congr ?_
  · rw [abs_of_nonneg measureReal_nonneg]
    exact measureReal_mono (Set.subset_univ _)
  · filter_upwards [Metric.ball_mem_nhds (0 : ℝ) zero_lt_one] with t ht
    rw [mem_ball_zero_iff, Real.norm_eq_abs] at ht
    rw [ofScalars_sum_eq]
    simp_rw [smul_eq_mul]
    exact (pgf_eq_tsum hX ht.le).symm

/-- The generating function of a finite measure is analytic at `0`; this is the entry point
towards derivatives of `pgf`, i.e. the factorial moments. -/
lemma analyticAt_pgf [IsFiniteMeasure μ] (hX : Measurable X) : AnalyticAt ℝ (pgf X μ) 0 :=
  (hasFPowerSeriesAt_pgf hX).analyticAt

/-- **The derivatives at `0` recover the distribution**: the `n`-th derivative of the
generating function at `0` is `n !` times the mass of `{X = n}`. -/
theorem iteratedDeriv_pgf_zero [IsFiniteMeasure μ] (hX : Measurable X) (n : ℕ) :
    iteratedDeriv n (pgf X μ) 0 = n ! * μ.real (X ⁻¹' {n}) := by
  obtain ⟨r, hr⟩ := hasFPowerSeriesAt_pgf (μ := μ) hX
  rw [iteratedDeriv_eq_iteratedFDeriv, ← hr.factorial_smul 1 n, nsmul_eq_mul]
  congr 1
  simp [coeff_ofScalars (𝕜 := ℝ) (p := fun n => μ.real (X ⁻¹' {n})) (n := n)]

/-- **The probability generating function determines the law.** If the generating functions
of two `ℕ`-valued random variables with respect to finite measures agree on `[-1, 1]`, then
the two distributions agree. -/
theorem map_eq_map_of_pgf_eq {Ω' : Type*} {m' : MeasurableSpace Ω'} {ν : Measure Ω'}
    {Y : Ω' → ℕ} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hX : Measurable X) (hY : Measurable Y)
    (h : ∀ t : ℝ, |t| ≤ 1 → pgf X μ t = pgf Y ν t) :
    μ.map X = ν.map Y := by
  have h_eq : pgf X μ =ᶠ[nhds (0 : ℝ)] pgf Y ν := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) zero_lt_one] with t ht
    rw [mem_ball_zero_iff, Real.norm_eq_abs] at ht
    exact h t ht.le
  have h_coeff := ofScalars_series_injective ℝ ℝ
    ((hasFPowerSeriesAt_pgf hX).eq_formalMultilinearSeries_of_eventually
      (hasFPowerSeriesAt_pgf hY) h_eq)
  refine Measure.ext_of_singleton fun n => ?_
  rw [Measure.map_apply hX (measurableSet_singleton n),
    Measure.map_apply hY (measurableSet_singleton n)]
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (measure_ne_top ν _)).mp
    (congrFun h_coeff n)

end Uniqueness

section IndepFun

/-- This is a trivial application of `IndepFun.comp` but it will come up frequently: if `X`
and `Y` are independent, so are `t ^ X` and `s ^ Y`. -/
theorem IndepFun.pow_nat {Y : Ω → ℕ} (h_indep : X ⟂ᵢ[μ] Y) (t s : ℝ) :
    (fun ω => t ^ X ω) ⟂ᵢ[μ] fun ω => s ^ Y ω :=
  h_indep.comp (Measurable.of_discrete (f := fun n : ℕ => t ^ n))
    (Measurable.of_discrete (f := fun n : ℕ => s ^ n))

/-- The generating function of a sum of independent variables is the product of the
generating functions. -/
theorem IndepFun.pgf_add {Y : Ω → ℕ} (h_indep : X ⟂ᵢ[μ] Y)
    (hX : Measurable X) (hY : Measurable Y) :
    pgf (X + Y) μ t = pgf X μ t * pgf Y μ t := by
  simp_rw [pgf, Pi.add_apply, pow_add]
  exact (h_indep.pow_nat t t).integral_mul_eq_mul_integral
    (((Measurable.of_discrete (f := fun n : ℕ => t ^ n)).comp hX).aestronglyMeasurable)
    (((Measurable.of_discrete (f := fun n : ℕ => t ^ n)).comp hY).aestronglyMeasurable)

/-- The generating function of a sum of finitely many independent variables is the product of
the generating functions. -/
theorem iIndepFun.pgf_sum {ι : Type*} {X : ι → Ω → ℕ}
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
    (s : Finset ι) : pgf (∑ i ∈ s, X i) μ t = ∏ i ∈ s, pgf (X i) μ t := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi_notin_s h_rec =>
    rw [sum_insert hi_notin_s,
      IndepFun.pgf_add (h_indep.indepFun_finsetSum_of_notMem h_meas hi_notin_s).symm
        (h_meas i) (by fun_prop),
      h_rec, prod_insert hi_notin_s]

end IndepFun

end ProbabilityTheory
