import ErdosProblems.Erdos587.HooleySmoothConjugate
import ErdosProblems.Erdos587.LatticeBounds

/-! # Uniform centered tails and the negative-frequency symmetry -/

open scoped SchwartzMap FourierTransform ComplexConjugate

namespace Erdos587

theorem exists_delta_centered_pointwise_bound (f : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 0 < q → ∀ a : ℤ, ∀ L : ℝ, 1 ≤ L →
      ‖deltaSmoothCenteredQuadratic f L q a‖ ≤ C * L := by
  obtain ⟨C, hC, hlattice⟩ := exists_schwartz_lattice_norm_bound f
  refine ⟨C + ‖𝓕 f 0‖, by positivity, ?_⟩
  intro q hq a L hL
  have hLpos : 0 < L := by linarith
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast hq
  have hsample : Summable (fun n : ℤ => ‖f (L⁻¹ * n)‖) := by
    simpa only [dilateSchwartz_apply] using
      (summable_schwartz_int (dilateSchwartz f L⁻¹ (inv_ne_zero hLpos.ne'))).norm
  have hnorm : Summable (fun n : ℤ =>
      ‖phase (((a : ℝ) / q) * (n : ℝ) ^ 2 + 0 * n) * f (L⁻¹ * n)‖) := by
    simpa only [norm_mul, norm_phase, one_mul] using hsample
  have hsum : ‖deltaSmoothQuadraticSum f L ((a : ℝ) / q) 0‖ ≤ C * L := by
    apply (norm_tsum_le_tsum_norm hnorm).trans
    simpa only [norm_mul, norm_phase, one_mul] using hlattice L hL
  have hmean : ‖deltaSmoothQuadraticMean f L q a‖ ≤ L * ‖𝓕 f 0‖ := by
    rw [deltaSmoothQuadraticMean, norm_mul, norm_mul, norm_div,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hLpos, Complex.norm_natCast]
    calc
      _ ≤ (L / q) * q * ‖𝓕 f 0‖ := by
        gcongr
        exact norm_completeQuadraticGaussSum_le q a 0
      _ = _ := by field_simp
  apply (norm_sub_le _ _).trans
  exact (add_le_add hsum hmean).trans_eq (by ring)

lemma deltaSmoothQuadraticMean_conjugate (f : 𝓢(ℝ, ℂ)) (L : ℝ)
    {q : ℕ} (hq : 0 < q) (a : ℤ) :
    deltaSmoothQuadraticMean (conjugateSchwartz f) L q (-a) =
      conj (deltaSmoothQuadraticMean f L q a) := by
  simp only [deltaSmoothQuadraticMean, map_mul, map_div₀, Complex.conj_ofReal, map_natCast,
    delta_fourier_conjugateSchwartz, neg_zero, completeQuadraticGaussSum_neg_zero hq a]

lemma deltaSmoothCenteredQuadratic_conjugate (f : 𝓢(ℝ, ℂ)) (L : ℝ)
    {q : ℕ} (hq : 0 < q) (a : ℤ) :
    deltaSmoothCenteredQuadratic (conjugateSchwartz f) L q (-a) =
      conj (deltaSmoothCenteredQuadratic f L q a) := by
  have hsum := deltaSmoothQuadraticSum_conjugate f L ((a : ℝ) / q) 0
  simp only [neg_zero] at hsum
  unfold deltaSmoothCenteredQuadratic
  rw [Int.cast_neg, neg_div, hsum,
    deltaSmoothQuadraticMean_conjugate f L hq a, map_sub]

lemma deltaSmoothCenteredQuadratic_norm_negative (f : 𝓢(ℝ, ℂ)) (L : ℝ)
    {q : ℕ} (hq : 0 < q) (a : ℤ) :
    ‖deltaSmoothCenteredQuadratic f L q (-a)‖ =
      ‖deltaSmoothCenteredQuadratic (conjugateSchwartz f) L q a‖ := by
  have hh := deltaSmoothCenteredQuadratic_conjugate f L hq (-a)
  rw [neg_neg] at hh
  rw [hh, Complex.norm_conj]

end Erdos587
