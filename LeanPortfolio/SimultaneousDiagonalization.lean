/-
Simultaneous diagonalization of two real quadratic forms
(one of them positive definite) — an item on Mathlib's
"missing undergraduate mathematics" list as of 2026-08.

Statement (matrix form): if `A` is positive definite and `B` is
symmetric, there is an invertible `P` with `Pᵀ A P = 1` and `Pᵀ B P` diagonal.

Route: the LDL decomposition of `A` gives an invertible `L` with
`L A Lᴴ` positive diagonal; rescaling rows by `1/√dᵢ` gives `W` with
`W A Wᵀ = 1`.  Then `W B Wᵀ` is symmetric, so the real spectral theorem
diagonalizes it by an orthogonal `V`, and `P = Wᵀ V` works for both forms.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.LDL
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Real.Sqrt

open Matrix Unitary

variable {n : ℕ}

/-- The scalar identity behind the rescaling step. -/
private lemma inv_sqrt_mul_mul_inv_sqrt {x : ℝ} (hx : 0 < x) :
    (Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹ = 1 := by
  have h : Real.sqrt x ≠ 0 := Real.sqrt_ne_zero'.mpr hx
  field_simp
  exact (Real.sq_sqrt hx.le).symm

/-- **Simultaneous diagonalization of two real quadratic forms.**
If `A` is positive definite and `B` is symmetric, some invertible `P`
takes `A` to the identity and `B` to a diagonal matrix by congruence. -/
theorem exists_simultaneous_diagonalization
    (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (hB : B.IsSymm) :
    ∃ P : Matrix (Fin n) (Fin n) ℝ, IsUnit P.det ∧
      Pᵀ * A * P = 1 ∧ ∃ d : Fin n → ℝ, Pᵀ * B * P = diagonal d := by
  classical
  -- Step 1: LDL decomposition: `L A Lᴴ` is diagonal with positive entries.
  set L : Matrix (Fin n) (Fin n) ℝ := LDL.lowerInv hA with hLdef
  have hLunit : IsUnit L := isUnit_of_invertible L
  have hdiag : L * A * Lᴴ = diagonal (LDL.diagEntries hA) :=
    (LDL.diag_eq_lowerInv_conj hA).symm
  have hDpos : (diagonal (LDL.diagEntries hA)).PosDef := by
    rw [← hdiag]
    exact hA.mul_mul_conjTranspose_same (vecMul_injective_iff_isUnit.mpr hLunit)
  have hd : ∀ i, 0 < LDL.diagEntries hA i := posDef_diagonal_iff.mp hDpos
  have hsq : ∀ i, Real.sqrt (LDL.diagEntries hA i) ≠ 0 := fun i =>
    Real.sqrt_ne_zero'.mpr (hd i)
  -- Step 2: rescale rows by `1/√dᵢ`: `W A Wᵀ = 1`.
  set e : Fin n → ℝ := fun i => (Real.sqrt (LDL.diagEntries hA i))⁻¹ with hedef
  set W : Matrix (Fin n) (Fin n) ℝ := diagonal e * L with hWdef
  have hLt : Lᵀ = Lᴴ := (conjTranspose_eq_transpose_of_trivial L).symm
  have hWt : Wᵀ = Wᴴ := (conjTranspose_eq_transpose_of_trivial W).symm
  have hone : (fun i => e i * LDL.diagEntries hA i * e i) = fun _ => (1 : ℝ) := by
    funext i
    simp only [hedef]
    exact inv_sqrt_mul_mul_inv_sqrt (hd i)
  have hWA : W * A * Wᵀ = 1 := by
    rw [hWdef, transpose_mul, diagonal_transpose, hLt,
      show diagonal e * L * A * (Lᴴ * diagonal e)
        = diagonal e * (L * A * Lᴴ) * diagonal e by simp only [mul_assoc],
      hdiag, diagonal_mul_diagonal, diagonal_mul_diagonal, hone, diagonal_one]
  -- Step 3: `W B Wᵀ` is symmetric; diagonalize it by an orthogonal matrix.
  have hBher : B.IsHermitian := by
    change Bᴴ = B
    rw [conjTranspose_eq_transpose_of_trivial]
    exact hB
  have hC : (W * B * Wᴴ).IsHermitian := isHermitian_mul_mul_conjTranspose W hBher
  have hspec := hC.spectral_theorem
  rw [conjStarAlgAut_apply] at hspec
  set V : Matrix (Fin n) (Fin n) ℝ := ↑(hC.eigenvectorUnitary) with hVdef
  have hstar : star V = Vᵀ := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  rw [hstar] at hspec
  have hV1 : Vᵀ * V = 1 := by
    have h := Unitary.coe_star_mul_self hC.eigenvectorUnitary
    rwa [← hVdef, hstar] at h
  -- Step 4: `P = Wᵀ V` diagonalizes both forms at once.
  refine ⟨Wᵀ * V, ?_, ?_, RCLike.ofReal ∘ hC.eigenvalues, ?_⟩
  · -- invertibility, via determinants
    have hdetV : IsUnit V.det := by
      have h : Vᵀ.det * V.det = 1 := by rw [← det_mul, hV1, det_one]
      exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul_eq_one h)
    have hLdet : IsUnit L.det :=
      letI : Invertible L := LDL.invertibleLowerInv hA
      isUnit_det_of_invertible L
    have hEdet : IsUnit (diagonal e).det := by
      rw [det_diagonal]
      refine isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => ?_)
      simp only [hedef]
      exact inv_ne_zero (hsq i)
    have hdetW : IsUnit W.det := by
      rw [hWdef, det_mul]
      exact hEdet.mul hLdet
    rw [det_mul, det_transpose]
    exact hdetW.mul hdetV
  · -- `Pᵀ A P = 1`
    rw [transpose_mul, transpose_transpose,
      show Vᵀ * W * A * (Wᵀ * V) = Vᵀ * (W * A * Wᵀ) * V by simp only [mul_assoc],
      hWA, mul_one, hV1]
  · -- `Pᵀ B P` is the diagonal matrix of eigenvalues
    rw [transpose_mul, transpose_transpose,
      show Vᵀ * W * B * (Wᵀ * V) = Vᵀ * (W * B * Wᵀ) * V by simp only [mul_assoc], hWt]
    conv_lhs => rw [hspec]
    rw [show Vᵀ * (V * diagonal (RCLike.ofReal ∘ hC.eigenvalues) * Vᵀ) * V
        = (Vᵀ * V) * diagonal (RCLike.ofReal ∘ hC.eigenvalues) * (Vᵀ * V) by
          simp only [mul_assoc],
      hV1, one_mul, mul_one]
