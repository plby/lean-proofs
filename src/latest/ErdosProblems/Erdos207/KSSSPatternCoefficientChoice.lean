/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSPatternPowerRequirements
import ErdosProblems.Erdos207.KSSSCoefficientChoice

/-! # One finite threshold supplies every bounded-pattern coefficient budget -/

namespace Erdos207

noncomputable section

theorem exists_ksss_pattern_power_threshold
    (q b B H Rmin Nmin : ℕ) (coeff : ℕ → ℝ) (hb : 1 ≤ b)
    (hRmin : b * H + H ^ 2 + ksssPowerErrorExponent b B + 3 * b + 2 ≤ Rmin) :
    ∃ T : ℕ, Nmin ≤ T ∧ ∀ t, T ≤ t → ∀ k h m, h ≤ H → m ≤ H ^ 2 →
      KSSSPatternPowerRequirements q b B k Rmin h m t coeff := by
  let c : ℝ := 6 * ((B + 2 : ℕ) : ℝ) * 2 ^ (B + 2)
  let f := fun i : Fin (H + 1) × Fin (H ^ 2 + 1) ↦
    max (3 * (i.2.val : ℝ))
      (max (ksssPatternTaylorCoefficient q coeff i.1.val i.2.val)
        (max ((patternHazardErrorCoefficient q i.1.val i.2.val : ℝ) +
            2 * ksssPatternHazardCoefficient q coeff i.1.val i.2.val)
          (max (2 * ksssPatternStepCoefficient q coeff i.1.val i.2.val)
            (max (ksssPatternJumpCoefficient q coeff i.1.val i.2.val)
              (ksssPatternVarianceCoefficient q coeff i.1.val i.2.val)))))
  obtain ⟨T, hTmin, hc, hf⟩ := exists_nat_uniform_finite_bound c f Nmin
  refine ⟨T, hTmin, ?_⟩
  intro t htt k h m hh hm
  have httR : (T : ℝ) ≤ t := by exact_mod_cast htt
  have hbound := (hf (⟨h, by omega⟩, ⟨m, by omega⟩)).trans httR
  dsimp only [f] at hbound
  obtain ⟨hselector, hrest⟩ := max_le_iff.mp hbound
  obtain ⟨hTaylor, hrest⟩ := max_le_iff.mp hrest
  obtain ⟨hdrift, hrest⟩ := max_le_iff.mp hrest
  obtain ⟨hstep, hrest⟩ := max_le_iff.mp hrest
  obtain ⟨hjump, hvariance⟩ := max_le_iff.mp hrest
  have hR : Rmin ≤ ksssPowerDenominatorExponent q b B k Rmin := by
    dsimp only [ksssPowerDenominatorExponent]
    omega
  have hbh := Nat.mul_le_mul_left b hh
  exact ⟨hb, by omega, by omega, by omega, hselector, hTaylor, hdrift, hstep,
    hc.trans httR, hjump, hvariance⟩

end

end Erdos207
