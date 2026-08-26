import ErdosProblems.Erdos67b.MRGSRiemannZetaUpper
import ErdosProblems.Erdos67b.MRMultiplicativeEuler

/-!
# Explicit left-line bound for the GS A.9 maximum-modulus step

The arithmetic input on the left side of the A.9 rectangle is the ordinary
Euler bound at `1 + 1 / log X`.  This file removes the logarithm of zeta from
that bound using the elementary real-axis pole estimate.
-/

namespace Erdos67b.MRHalaszBands

noncomputable section

/-- Explicit left-edge estimate for the full L-series in A.9. -/
theorem norm_LSeries_halaszPoint_le_one_add_log_mul_exp
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {A X : ℕ} (hX : 1 < X)
    (hnonpret : MRArchimedeanNonpretentious f A X)
    {t : ℝ} (ht : |t| ≤ X) :
    ‖LSeries f (Erdos67b.MRHalaszEuler.halaszPoint X t)‖ ≤
      (1 + Real.log (X : ℝ)) *
        Real.exp
          (-Real.exp (-1) * (A : ℝ) +
            3 * Erdos67b.EulerQuantitative.primeQuadraticConstant) := by
  let u : ℝ := Erdos67b.EulerResidue.taoExponent X
  let Z : ℝ := (riemannZeta (u : ℂ)).re
  have hu : 1 < u := by
    dsimp only [u]
    exact Erdos67b.EulerResidue.one_lt_taoExponent hX
  have hZpos : 0 < Z := by
    dsimp only [Z]
    exact (Complex.lt_def.mp (riemannZeta_pos_of_one_lt hu)).1
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast hX)
  have hZnorm : ‖riemannZeta (u : ℂ)‖ ≤ 1 + Real.log (X : ℝ) := by
    have hbase := Erdos67b.norm_riemannZeta_real_le_one_add_inv
      (sigma := (Real.log (X : ℝ))⁻¹) (inv_pos.mpr hlogX)
    dsimp only [u, Erdos67b.EulerResidue.taoExponent]
    simpa [inv_inv] using hbase
  have hZ : Z ≤ 1 + Real.log (X : ℝ) := by
    exact (le_abs_self Z).trans
      ((Complex.abs_re_le_norm _).trans hZnorm)
  have hbase :=
    Erdos67b.MRMultiplicativeEuler.norm_LSeries_halaszPoint_le_of_archimedeanNonpretentious
      hmul hbound hX hnonpret ht
  calc
    ‖LSeries f (Erdos67b.MRHalaszEuler.halaszPoint X t)‖ ≤
        Real.exp
          (Real.log Z - Real.exp (-1) * (A : ℝ) +
            3 * Erdos67b.EulerQuantitative.primeQuadraticConstant) := by
      simpa only [u, Z] using hbase
    _ = Z * Real.exp
          (-Real.exp (-1) * (A : ℝ) +
            3 * Erdos67b.EulerQuantitative.primeQuadraticConstant) := by
      rw [show Real.log Z - Real.exp (-1) * (A : ℝ) +
          3 * Erdos67b.EulerQuantitative.primeQuadraticConstant =
        Real.log Z +
          (-Real.exp (-1) * (A : ℝ) +
            3 * Erdos67b.EulerQuantitative.primeQuadraticConstant) by ring,
        Real.exp_add, Real.exp_log hZpos]
    _ ≤ (1 + Real.log (X : ℝ)) *
        Real.exp
          (-Real.exp (-1) * (A : ℝ) +
            3 * Erdos67b.EulerQuantitative.primeQuadraticConstant) := by
      exact mul_le_mul_of_nonneg_right hZ (Real.exp_pos _).le

/-- Square-root form used after the A.13--A.14 composition. -/
theorem sqrt_norm_LSeries_halaszPoint_le_sqrt_one_add_log_mul_exp
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {A X : ℕ} (hX : 1 < X)
    (hnonpret : MRArchimedeanNonpretentious f A X)
    {t : ℝ} (ht : |t| ≤ X) :
    Real.sqrt ‖LSeries f (Erdos67b.MRHalaszEuler.halaszPoint X t)‖ ≤
      Real.sqrt (1 + Real.log (X : ℝ)) *
        Real.exp
          ((-Real.exp (-1) * (A : ℝ) +
            3 * Erdos67b.EulerQuantitative.primeQuadraticConstant) / 2) := by
  have hlog : 0 ≤ 1 + Real.log (X : ℝ) := by
    have : 0 < Real.log (X : ℝ) :=
      Real.log_pos (by exact_mod_cast hX)
    linarith
  have hbase := Real.sqrt_le_sqrt
    (norm_LSeries_halaszPoint_le_one_add_log_mul_exp
      hmul hbound hX hnonpret ht)
  rw [Real.sqrt_mul hlog, ← Real.exp_half] at hbase
  exact hbase

end

end Erdos67b.MRHalaszBands
