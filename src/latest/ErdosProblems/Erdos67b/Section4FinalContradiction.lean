import ErdosProblems.Erdos67b.Section4FinalBudget
import ErdosProblems.Erdos67b.Section4FinalWindowBounds

/-! # The concrete weighted window gives the final Euler/BCC contradiction -/

open scoped BigOperators
open Finset

namespace Erdos67b

noncomputable section

theorem Section4CharacterData.primitive_contradiction_of_finalWindow
    {C : ℝ} {S : Section4Selection C} (W : Section4CharacterData S)
    {X N : ℕ} {c : ℝ} (hc : 0 < c)
    (P : EulerResidueBounds.TaoTransferReady W.primitiveCorrectionHom W.primitiveQ S.k X
      (2 * S.A) (1 / (2 * S.H)))
    (hlog : 2 ≤ Real.log (X : ℝ))
    (hYN : (4 ^ S.K) ^ 2 ≤ N)
    (hrY : 2 * W.primitiveQ ^ S.k ≤ (4 ^ S.K) ^ 2)
    (hhigh : taoHighTailMass X N ≤ 1)
    (hselected : compactMediumWeightedLocalEnergy
      (taoWindowCenters (4 ^ S.K) N) (taoWindowWeight X) S.H S.sample ≤
        section4B C * taoWindowMass X (4 ^ S.K) N)
    (hsingular : c * Real.log X ≤ ‖EulerResidue.singularSeries W.primitiveCorrectionHom X‖)
    (hphase : 8 * (S.H : ℝ) * (4 * S.H / ((2 ^ S.K : ℕ) : ℝ)) ≤ c)
    (hquad : 4 * (S.H : ℝ) * (1 + 2 * Real.log ((4 ^ S.K : ℕ) : ℝ)) ≤ c * Real.log X)
    (hlinear : 8 * ((W.primitiveQ ^ S.k : ℕ) : ℝ) * S.H ≤ c * Real.log X)
    (htail : 4 * ((W.primitiveQ ^ S.k : ℕ) : ℝ) * S.H * (1 + 4 * S.H) ≤ c * Real.log X)
    (hbudget : 2 * (16 * section4B C / c ^ 2 + 4) + 2 ≤ S.B) : False := by
  let Y := 4 ^ S.K
  let r := W.primitiveQ ^ S.k
  let ℓ : ℝ := Real.log X
  let ℓ₀ : ℝ := 1 + 2 * Real.log (Y : ℝ)
  let V : ℝ := taoWindowMass X Y N
  let M : ℝ := 2 * ℓ / r
  let LowSq : ℝ := ℓ₀ ^ 2 / r + 2 * ℓ₀
  let Kbound : ℝ := 16 * section4B C / c ^ 2 + 4
  let Main : ℂ := EulerResidue.singularSeries W.primitiveCorrectionHom X / (r : ℂ)
  have hX : 1 < X := lt_of_lt_of_le one_lt_two P.two_le
  have hY : 2 ≤ Y := by
    have hh := Nat.pow_le_pow_right (by norm_num : 1 ≤ 4) S.K_pos
    simpa only [pow_one] using (show 2 ≤ 4 by norm_num).trans hh
  have hYpos : 0 < Y := by omega
  have hH : (0 : ℝ) < S.H := Nat.cast_pos.2 S.H_pos
  have hr : (0 : ℝ) < r := Nat.cast_pos.2 (pow_pos
    (Nat.pos_of_ne_zero (NeZero.ne W.primitiveQ)) _)
  have hℓ : 0 < ℓ := by dsimp [ℓ]; linarith
  have hℓ₀ : 0 ≤ ℓ₀ := by
    have hh : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Y))
    dsimp [ℓ₀]
    positivity
  have hmain : c * ℓ / r ≤ ‖Main‖ := by
    dsimp only [Main, ℓ]
    rw [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_right hsingular hr.le
  have hphaseActual : 8 * (S.H : ℝ) * S.phaseError ≤ c :=
    (mul_le_mul_of_nonneg_left S.phaseError_le_four_mul_div_two_pow (by positivity)).trans hphase
  have hconvBudget :
      4 * M * section4B C * V * S.H + 16 * M * (S.H : ℝ) ^ 3 * S.phaseError ^ 2 * V +
        16 * (S.H : ℝ) ^ 3 * LowSq + 16 * (r : ℝ) * (S.H : ℝ) ^ 3 * (1 + 4 * S.H) ^ 2 ≤
      Kbound * ‖Main‖ ^ 2 * r * S.H := by
    apply section4FinalConvolutionBudget Main hH hr hc hℓ (section4B_pos C).le
      (taoWindowMass_nonneg X Y N) S.phaseError_nonneg (by norm_num) le_rfl hℓ₀ le_rfl
      (taoWindowMass_le_two_log hX (by linarith)) le_rfl hphaseActual hquad hlinear htail hmain
  apply W.primitive_contradiction_of_taoTransferReady_of_selectedEnergy P
    (taoWindowCenters Y N) (taoWindowWeight X) (section4B C) V M 1 LowSq Kbound 1
    (by dsimp [M]; positivity) (by norm_num)
    (taoLowCutoffResidueMass X Y)
    (fun a _ ↦ taoLowCutoffResidueMass_nonneg X Y a)
    (fun n _ ↦ taoWindowWeight_nonneg X n)
    rfl (fun n hn ↦ taoWindowCenter_lower hn) hselected
  · intro a _
    exact taoWindowResidueMass_le_two_log_div hX hYpos hYN hlog hrY a
  · exact sum_sq_taoLowCutoffResidueMass_le_log_bound _ hX hY
  · intro a _ m _
    exact (norm_finiteShiftedResidueSeries_taoWindow_sub_le
      W.primitiveCorrectionHom_hasUnitNorm a m hX (hYN.trans (Nat.le_succ N))).trans
        (add_le_add le_rfl hhigh)
  · exact hconvBudget
  · field_simp
    norm_num
  · simpa only [Kbound, mul_one] using hbudget

end

end Erdos67b
