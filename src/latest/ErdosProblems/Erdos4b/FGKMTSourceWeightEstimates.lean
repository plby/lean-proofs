/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSourceScales
import ErdosProblems.Erdos4b.FGKMTJointWeightEstimates

/-! # Joint weight estimates at the actual FGKMT source parameters -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

theorem exists_sourceWeightEstimates {c e : ℝ} (hc : 0 < c) (he : 0 < e) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ x : ℕ in atTop, ∃ B m : ℕ, ∃ h : Fin (m + 1) → ℕ,
      1 ≤ B ∧ (B : ℝ) ≤ Real.exp (a * Real.sqrt (Real.log (x : ℝ))) ∧
      (B = 1 ∨ B.Prime) ∧ 1 ≤ m ∧ m + 1 = growingSieveDimension x ∧
      Function.Injective h ∧ BoundedGaps.IsAdmissible (Finset.univ.image h) ∧
      (∀ i, (h i).Prime ∧ m + 1 < h i ∧ h i < 2 * (m + 1) ^ 2) ∧
      CommonWeightEstimates x m B (sourceIntervalLength c x) h e := by
  obtain ⟨a, ha, X0, _hX0, hweights⟩ := exists_commonWeightEstimates he
  refine ⟨a, ha, ?_⟩
  filter_upwards [eventually_ge_atTop X0, eventually_growingSieveDimension_profile_range,
    eventually_exists_growing_admissible_tuple, eventually_sourceIntervalLength_bounds hc] with
      x hx hprofile htuple hinterval
  obtain ⟨B, hB1, hBsize, hB, hweight⟩ := hweights x hx
  let m := growingSieveDimension x - 1
  have hm : 1 ≤ m := by dsimp only [m]; omega
  have hmk : m + 1 = growingSieveDimension x := by dsimp only [m]; omega
  have hlog : 10000 ≤ Real.log (m + 1 : ℕ) := by simpa only [hmk] using hprofile.2
  have hdim : (m + 1 : ℕ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ) := by
    simpa only [hmk] using growingSieveDimension_le x
  have htuple' : ∃ h : Fin (m + 1) → ℕ,
      Function.Injective h ∧ BoundedGaps.IsAdmissible (Finset.univ.image h) ∧
      (∀ i, (h i).Prime ∧ m + 1 < h i ∧ h i < 2 * (m + 1) ^ 2) := by
    rw [hmk]
    exact htuple
  obtain ⟨h, hinj, hadm, hshift⟩ := htuple'
  refine ⟨B, m, h, hB1, hBsize, hB, hm, hmk, hinj, hadm, hshift, ?_⟩
  exact hweight m hm hlog hdim h hinj hadm (fun i => (hshift i).2.2)
    (sourceIntervalLength c x) hinterval.1 (hinterval.2.2 (m + 1) hdim)

theorem eventually_sourceWeightGain_loglog_bounds :
    ∀ᶠ x : ℕ in atTop, ∀ m B : ℕ,
      m + 1 = growingSieveDimension x → (B = 1 ∨ B.Prime) →
      Real.log (Real.log (x : ℝ)) / 368640 ≤
        commonWeightGain m B (dimensionPreSieveModulus (m + 1) B) (dimensionSieveRadius x) x ∧
      commonWeightGain m B (dimensionPreSieveModulus (m + 1) B) (dimensionSieveRadius x) x ≤
        (6 / 5 : ℝ) * Real.exp 24 * Real.log (Real.log (x : ℝ)) := by
  filter_upwards [eventually_chosenWeightGain_bounds,
    eventually_growingSieveDimension_profile_range,
    eventually_growingSieveDimension_log_bounds] with x hgain hprofile hlog
  intro m B hmk hB
  have hm : 1 ≤ m := by omega
  have hlogk : 10000 ≤ Real.log (m + 1 : ℕ) := by simpa only [hmk] using hprofile.2
  have hg := hgain m B hm hlogk hB
  rw [← hmk] at hlog
  constructor
  · linarith [hg.1, hlog.1]
  · have hp := mul_le_mul_of_nonneg_left hlog.2 (by positivity : 0 ≤ 12 * Real.exp 24)
    nlinarith [hg.2]

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_sourceWeightEstimates
#print axioms Erdos4b.FGKMT.eventually_sourceWeightGain_loglog_bounds
