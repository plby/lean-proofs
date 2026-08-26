/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Disk bounds from polynomial Parseval for the endpoint analysis in Erdős 521.
Formal proof: Codex.
-/
import Mathlib.Analysis.Polynomial.Fourier
import Mathlib

namespace Erdos521

open MeasureTheory
open scoped BigOperators

/-- The squared modulus on the half unit disk is bounded by twice the boundary
mean square. Only finite Cauchy–Schwarz and polynomial Parseval are used. -/
theorem polynomial_norm_sq_le_circleAverage (p : Polynomial ℂ) {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖p.eval w‖ ^ 2 ≤ 2 * Real.circleAverage (fun z ↦ ‖p.eval z‖ ^ 2) 0 1 := by
  have hnorm : ‖p.eval w‖ ≤ ∑ i ∈ p.support, ‖p.coeff i‖ * ‖w‖ ^ i := by
    rw [Polynomial.eval_eq_sum]
    exact (norm_sum_le _ _).trans_eq (by simp [norm_pow])
  have hq₀ : 0 ≤ ‖w‖ ^ 2 := sq_nonneg _
  have hq : ‖w‖ ^ 2 ≤ 1 / 4 := by nlinarith [norm_nonneg w]
  have hq₁ : ‖w‖ ^ 2 < 1 := by linarith
  have hgeom : (∑ i ∈ p.support, (‖w‖ ^ i) ^ 2) ≤ 2 := by
    calc
      (∑ i ∈ p.support, (‖w‖ ^ i) ^ 2) = ∑ i ∈ p.support, (‖w‖ ^ 2) ^ i := by
        simp only [← pow_mul, Nat.mul_comm]
      _ ≤ ∑' i : ℕ, (‖w‖ ^ 2) ^ i :=
        Summable.sum_le_tsum _ (fun _ _ ↦ pow_nonneg hq₀ _) (summable_geometric_of_lt_one hq₀ hq₁)
      _ = (1 - ‖w‖ ^ 2)⁻¹ := tsum_geometric_of_lt_one hq₀ hq₁
      _ ≤ 2 := by
        rw [inv_eq_one_div]
        apply (div_le_iff₀ (sub_pos.mpr hq₁)).mpr
        linarith
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq p.support
    (fun i ↦ ‖p.coeff i‖) (fun i ↦ ‖w‖ ^ i)
  calc
    ‖p.eval w‖ ^ 2 ≤ (∑ i ∈ p.support, ‖p.coeff i‖ * ‖w‖ ^ i) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ _ := hcs
    _ ≤ (∑ i ∈ p.support, ‖p.coeff i‖ ^ 2) * 2 :=
      mul_le_mul_of_nonneg_left hgeom (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
    _ = _ := by rw [p.sum_sq_norm_coeff_eq_circleAverage, mul_comm]

/-- The same estimate on a translated disk of arbitrary positive radius. -/
theorem polynomial_norm_sq_le_circleAverage_disk (p : Polynomial ℂ) (c : ℂ)
    {R : ℝ} (hR : 0 < R) {w : ℂ} (hw : ‖w - c‖ ≤ R / 2) :
    ‖p.eval w‖ ^ 2 ≤ 2 * Real.circleAverage (fun z ↦ ‖p.eval z‖ ^ 2) c R := by
  let q := p.comp (Polynomial.C c + Polynomial.C (R : ℂ) * Polynomial.X)
  have hw' : ‖(w - c) / (R : ℂ)‖ ≤ 1 / 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    apply (div_le_iff₀ hR).mpr
    linarith
  have heval (z : ℂ) : q.eval z = p.eval ((R : ℂ) * z + c) := by
    simp [q, Polynomial.eval_comp, add_comm]
  have hvalue : q.eval ((w - c) / (R : ℂ)) = p.eval w := by
    rw [heval]
    congr 1
    have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
    field_simp [hR']
    ring
  have h := polynomial_norm_sq_le_circleAverage q hw'
  rw [hvalue] at h
  simp_rw [heval] at h
  rw [Real.circleAverage_eq_circleAverage_zero_one
    (f := fun z ↦ ‖p.eval z‖ ^ 2) (c := c) (R := R)]
  exact h

end Erdos521
