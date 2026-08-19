/-
Simultaneous diagonalization of two real quadratic forms
(one of them positive definite) — an item on Mathlib's
"missing undergraduate mathematics" list as of 2026-08.

Target statement (matrix form): if `A` is positive definite and `B` is
symmetric, there is an invertible `P` with `Pᵀ A P = 1` and `Pᵀ B P` diagonal.

Route: turn `A` into an inner product, apply the real spectral theorem
(`Matrix.IsHermitian.spectral_theorem`) to `B` viewed in the `A`-inner-product,
transport back.
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum

open Matrix

variable {n : ℕ}

/-- Smoke test: the environment and imports work. -/
example (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) : A.IsHermitian := hA.1

/-- Main target (stub). -/
theorem exists_simultaneous_diagonalization
    (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (hB : B.IsSymm) :
    ∃ P : Matrix (Fin n) (Fin n) ℝ, IsUnit P.det ∧
      Pᵀ * A * P = 1 ∧ ∃ d : Fin n → ℝ, Pᵀ * B * P = diagonal d := by
  sorry
