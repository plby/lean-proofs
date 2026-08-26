/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourcePrimeIntervalLowerBound

/-!
# Prime counts proportional to the actual allocated interval length

The threshold depends only on the fixed minimum relative length. The
conclusion retains the actual length, which can be much larger.
-/

namespace Erdos4b

noncomputable section

open Filter
open scoped Topology

theorem eventually_primeInterval_card_ge_half_length (J : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ X : ℕ in atTop, ∀ A B : ℕ, X ≤ 2 * A → A ≤ B → B ≤ X →
      δ * (X : ℝ) / Real.log X ^ J ≤ (B : ℝ) - A →
      ((B : ℝ) - A) / (2 * Real.log X) ≤ (auxiliaryPrimeInterval A B).card := by
  obtain ⟨C, hC, X₀, hX₀, htheta⟩ := exists_chebyshevTheta_nat_logSaving (J + 1)
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (max 8 (4 * X₀)), hlogTop.eventually_ge_atTop 1,
    hlogTop.eventually_ge_atTop (2 * Real.log 4),
    hlogTop.eventually_ge_atTop (4 * C * 2 ^ (J + 1) / δ)] with X hX hlog hlog4 hsave
  intro A B hhalf hAB hBX hlength
  have hA : 0 < A := by omega
  have hXA : X₀ ≤ A - 1 := by omega
  have hXB : X₀ ≤ B - 1 := by omega
  have hfourA : X ≤ 4 * (A - 1) := by omega
  have hfourB : X ≤ 4 * (B - 1) := by omega
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hV : 0 < Real.log X := by linarith
  let δ' : ℝ := ((B : ℝ) - A) * Real.log X ^ J / X
  have hδle : δ ≤ δ' := (le_div_iff₀ hXpos).mpr
    ((div_le_iff₀ (pow_pos hV J)).mp hlength)
  have hlength' : δ' * (X : ℝ) / Real.log X ^ J = (B : ℝ) - A := by
    dsimp only [δ']
    field_simp
  have hsmall : 4 * C * 2 ^ (J + 1) ≤ δ' * Real.log X := by
    have hs : 4 * C * 2 ^ (J + 1) ≤ δ * Real.log X := by
      simpa only [mul_comm] using (div_le_iff₀ hδ).mp hsave
    exact hs.trans (mul_le_mul_of_nonneg_right hδle hV.le)
  have hcount := primeInterval_card_lower_of_logSaving J hC hA hAB hBX hV htheta hXA hXB
    (half_log_le_log_of_four_mul_ge (by omega) hfourA hlog4)
    (half_log_le_log_of_four_mul_ge (by omega) hfourB hlog4) hsmall hlength'.le
  calc
    _ = δ' * (X : ℝ) / (2 * Real.log X ^ (J + 1)) := by
      dsimp only [δ']
      rw [pow_succ]
      field_simp
    _ ≤ _ := hcount

end

end Erdos4b
