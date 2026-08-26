import ErdosProblems.Erdos421.LogFrequencyBoxes
import ErdosProblems.Erdos421.PolynomialPrefixMoments

/-! # Comparing a logarithmic short sum to polynomial moments inside its box -/

namespace Erdos421

noncomputable def localLogSum (M : ℕ) (t z : ℝ) : ℂ :=
  ∑ n ∈ Finset.range M, oscillatoryPhase 1 (t * (Real.log (z + ((n : ℝ) + 1)) - Real.log z))

theorem localLogSum_box_bound {k M : ℕ} (hk : 0 < k) (hM : 0 < M)
    {t z : ℝ} (hz : 0 < z) (hscale : |t| * (M : ℝ) ^ (k + 1) ≤ z ^ (k + 1))
    (a : UnitAddTorus (Fin k)) (ha : a ∈ logFrequencyBox k t M z) (p : ℕ) :
    ‖localLogSum M t z‖ ^ p ≤ (3 : ℝ) ^ p * polynomialPrefixMoment k M p a := by
  obtain ⟨b, hba, hb⟩ := exists_real_lift_of_mem_torusBox
    (logTaylorCoefficients k t z) (polynomialBoxRadius k M) a ha
  have hMR : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  let P : ℕ → ℝ := fun n ↦ 2 * Real.pi * powerPhase b ((n : ℝ) + 1)
  let d : ℕ → ℝ := fun n ↦ logPhaseRemainder t z b ((n : ℝ) + 1)
  have hd : ∀ n, n + 1 < M → |d (n + 1) - d n| ≤ 2 / (M : ℝ) := by
    intro n hn
    have hx : (n : ℝ) + 1 ∈ Set.Icc 0 (M : ℝ) := by
      constructor
      · positivity
      · exact_mod_cast (by omega : n + 1 ≤ M)
    have hy : ((n + 1 : ℕ) : ℝ) + 1 ∈ Set.Icc 0 (M : ℝ) := by
      constructor
      · positivity
      · exact_mod_cast (by omega : n + 1 + 1 ≤ M)
    have h := logPhaseRemainder_lipschitz hk hz hMR hscale b hb hx hy
    have he : (((n + 1 : ℕ) : ℝ) + 1) - ((n : ℝ) + 1) = 1 := by push_cast; ring
    rw [he, abs_one, mul_one] at h
    exact h
  have h := phase_sum_perturbation_power_le P d M p (by positivity : 0 ≤ 2 / (M : ℝ)) hd
  have hphase (n : ℕ) : P n + d n = t * (Real.log (z + ((n : ℝ) + 1)) - Real.log z) := by
    dsimp [P, d, logPhaseRemainder]
    ring
  have hfreq : (fun j ↦ (b j : UnitAddCircle)) = a := funext hba
  have hprefix (m : ℕ) : (∑ n ∈ Finset.range m, oscillatoryPhase 1 (P n)) =
      torusVinogradovWeylSum k m a := by
    change (∑ n ∈ Finset.range m, oscillatoryPhase 1 (2 * Real.pi * powerPhase b ((n : ℝ) + 1))) = _
    rw [← realVinogradovWeylSum_eq_phase_sum, ← torusVinogradovWeylSum_real, hfreq]
  have hfactor : 1 + (M : ℝ) * (2 / M) = 3 := by field_simp; norm_num
  simpa only [hphase, hprefix, hfactor, localLogSum, polynomialPrefixMoment] using h

end Erdos421
