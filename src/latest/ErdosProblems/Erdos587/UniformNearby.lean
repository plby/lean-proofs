import ErdosProblems.Erdos587.LatticeBounds

/-!
# A uniform pointwise bound for the nearby remainder

Absolute values discard every phase. The lattice and integral masses of
the fixed weight are both `O(L)`, uniformly in all arithmetic frequencies.
-/

open MeasureTheory
open scoped BigOperators SchwartzMap

namespace Erdos587

lemma norm_chirp_integral_le_scaled_l1 (f : 𝓢(ℝ, ℂ)) {L : ℝ} (hL : 0 < L) (A : ℝ) :
    ‖∫ x : ℝ, phase (A * x ^ 2) * f (L⁻¹ * x)‖ ≤ L * ∫ x : ℝ, ‖f x‖ := by
  calc
    _ ≤ ∫ x : ℝ, ‖phase (A * x ^ 2) * f (L⁻¹ * x)‖ := norm_integral_le_integral_norm _
    _ = ∫ x : ℝ, ‖f (L⁻¹ * x)‖ := by simp only [norm_mul, norm_phase, one_mul]
    _ = L * ∫ x : ℝ, ‖f x‖ := by
      simpa only [inv_inv, abs_of_pos hL, smul_eq_mul] using
        Measure.integral_comp_mul_left (fun x : ℝ => ‖f x‖) L⁻¹

theorem exists_uniform_nearby_pointwise_bound (f : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ q r v : ℕ, 0 < q → ∀ b : ℤ, ∀ L : ℝ, 1 ≤ L →
      ‖nearbyQuadraticRemainder f q r v b L‖ ≤ C * L := by
  obtain ⟨C, hC, hlattice⟩ := exists_schwartz_lattice_norm_bound f
  let I := ∫ x : ℝ, ‖f x‖
  have hI : 0 ≤ I := integral_nonneg (fun x => norm_nonneg _)
  refine ⟨C + I, by positivity, ?_⟩
  intro q r v hq b L hL
  have hLpos : 0 < L := by linarith
  let S : ℤ → ℂ := fun z => quadraticResiduePhase q ((r : ℤ) * b) z *
    (phase (((r : ℝ) / (q * v)) * (z : ℝ) ^ 2) * f (L⁻¹ * z))
  have hnorm (z : ℤ) : ‖S z‖ = ‖f (L⁻¹ * z)‖ := by
    simp only [S, quadraticResiduePhase, norm_mul, norm_phase, one_mul]
  have hsample : Summable (fun z : ℤ => ‖f (L⁻¹ * z)‖) := by
    simpa only [dilateSchwartz_apply] using
      (summable_schwartz_int (dilateSchwartz f L⁻¹ (inv_ne_zero hLpos.ne'))).norm
  have hsumnorm : Summable (fun z => ‖S z‖) := hsample.congr (fun z => (hnorm z).symm)
  have hdiscrete : ‖∑' z : ℤ, S z‖ ≤ C * L := by
    apply (norm_tsum_le_tsum_norm hsumnorm).trans
    simpa only [hnorm] using hlattice L hL
  have hgauss : ‖(q : ℂ)⁻¹ * completeQuadraticGaussSum q ((r : ℤ) * b) 0‖ ≤ 1 := by
    simpa only [div_eq_mul_inv, mul_comm] using
      norm_complete_quadratic_mean_le_one hq ((r : ℤ) * b)
  have hint := norm_chirp_integral_le_scaled_l1 f hLpos ((r : ℝ) / (q * v))
  unfold nearbyQuadraticRemainder
  calc
    _ ≤ ‖∑' z : ℤ, S z‖ + ‖(q : ℂ)⁻¹ * completeQuadraticGaussSum q ((r : ℤ) * b) 0 *
        (∫ x : ℝ, phase (((r : ℝ) / (q * v)) * x ^ 2) * f (L⁻¹ * x))‖ := norm_sub_le _ _
    _ ≤ C * L + 1 * (L * I) := by
      apply add_le_add hdiscrete
      rw [norm_mul]
      exact mul_le_mul hgauss hint (norm_nonneg _) (by norm_num)
    _ = (C + I) * L := by ring

end Erdos587
