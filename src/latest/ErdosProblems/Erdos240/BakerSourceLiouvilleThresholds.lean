/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerLemma3Instantiation

/-!
# Elementary bounds for the source Liouville thresholds

This file records the positivity and normalization bounds for the two
explicit Liouville thresholds used in the source construction.  The common
Delta denominator has complex norm at least one, and the automatic rational
target conjugate bound is at least one.  Consequently both thresholds lie in
the interval `(0, 1 / 2]`.
-/

open scoped BigOperators NumberField Polynomial

noncomputable section

namespace Erdos240.BakerSourceLiouvilleThresholds

open BakerLemma3
open BakerLemma3Instantiation
open BakerSourceState

/-! ## Exact certificate fields -/

@[simp] theorem stateIntegralTargetCertificate_scale {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (l : ℕ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    (stateIntegralTargetCertificate P state b bLast l m).scale =
      (commonDeltaDenominator P.h P.LzeroPlusOne (P.q ^ J) m : ℂ) :=
  rfl

@[simp] theorem stateIntegralTargetCertificate_conjugateBound
    {oldRank : ℕ} (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (l : ℕ) (m : VDPLMultiIndex (oldRank + 1)) :
    (stateIntegralTargetCertificate P state b bLast l m).conjugateBound = 1 :=
  rfl

@[simp] theorem stateRationalTargetCertificate_scale {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (l : ℕ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    (stateRationalTargetCertificate P state b bLast l m).scale =
      (commonDeltaDenominator P.h P.LzeroPlusOne (P.q ^ (J + 1)) m : ℂ) :=
  rfl

@[simp] theorem stateRationalTargetCertificate_conjugateBound
    {oldRank : ℕ} (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (l : ℕ) (m : VDPLMultiIndex (oldRank + 1)) :
    (stateRationalTargetCertificate P state b bLast l m).conjugateBound =
      rationalTargetConjugateBound P (coordinatesForState state)
        state.support state.coeff P.h P.LzeroPlusOne b bLast J l m :=
  rfl

/-- The norm of every nonzero common Delta denominator is at least one. -/
theorem one_le_norm_commonDeltaDenominator {oldRank : ℕ}
    (h deltaPowerBound den : ℕ) (hden : den ≠ 0)
    (m : VDPLMultiIndex (oldRank + 1)) :
    1 ≤ ‖(commonDeltaDenominator h deltaPowerBound den m : ℂ)‖ := by
  have hdenQ : (1 : ℚ) ≤ den := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hden)
  have hlcmQ : (1 : ℚ) ≤ Nat.lcmUpto h := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.lcmUpto_ne_zero h))
  have hcommonQ : (1 : ℚ) ≤
      commonDeltaDenominator h deltaPowerBound den m := by
    rw [commonDeltaDenominator]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_pow₀ hdenQ) (one_le_pow₀ hlcmQ)
  have hcommonR : (1 : ℝ) ≤
      (commonDeltaDenominator h deltaPowerBound den m : ℚ) := by
    exact_mod_cast hcommonQ
  rw [Complex.norm_ratCast, abs_of_nonneg (le_trans zero_le_one hcommonR)]
  exact hcommonR

/-- The finite-sum conjugate bound at a rational target is at least one. -/
theorem one_le_rationalTargetConjugateBound
    {oldRank : ℕ} {I : Type*} [DecidableEq I]
    (P : VDPLParameters (Fin oldRank))
    (coord : SourceCoordinates oldRank I) (support : Finset I) (p : I → ℤ)
    (h deltaPowerBound : ℕ) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (N l : ℕ) (m : VDPLMultiIndex (oldRank + 1)) :
    1 ≤ rationalTargetConjugateBound P coord support p h deltaPowerBound
      b bLast N l m := by
  unfold rationalTargetConjugateBound
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)

/-- The integral-target Liouville threshold is strictly positive. -/
theorem stateIntegralLiouvilleThreshold_pos {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J : ℕ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    0 < stateIntegralLiouvilleThreshold P J m := by
  let D : ℝ :=
    ‖(commonDeltaDenominator P.h P.LzeroPlusOne (P.q ^ J) m : ℂ)‖
  have hq : P.q ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt P.one_lt_q)
  have hD : 0 < D := by
    dsimp only [D]
    rw [norm_pos_iff]
    exact_mod_cast commonDeltaDenominator_ne_zero P.h P.LzeroPlusOne
      (P.q ^ J) (pow_ne_zero J hq) m
  have hthreshold : 0 < (1 / D) / 2 :=
    div_pos (one_div_pos.mpr hD) (by norm_num)
  simpa [stateIntegralLiouvilleThreshold, D] using hthreshold

/-- The integral-target Liouville threshold is at most one half. -/
theorem stateIntegralLiouvilleThreshold_le_half {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J : ℕ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    stateIntegralLiouvilleThreshold P J m ≤ (1 : ℝ) / 2 := by
  let D : ℝ :=
    ‖(commonDeltaDenominator P.h P.LzeroPlusOne (P.q ^ J) m : ℂ)‖
  have hq : P.q ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt P.one_lt_q)
  have hD : 1 ≤ D := by
    dsimp only [D]
    exact one_le_norm_commonDeltaDenominator P.h P.LzeroPlusOne
      (P.q ^ J) (pow_ne_zero J hq) m
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hinv : 1 / D ≤ (1 : ℝ) := by
    rw [div_le_iff₀ hDpos]
    simpa using hD
  have hthreshold : (1 / D) / 2 ≤ (1 : ℝ) / 2 :=
    div_le_div_of_nonneg_right hinv (by norm_num)
  simpa [stateIntegralLiouvilleThreshold, D] using hthreshold

/-- A coarser unit upper bound for the integral-target threshold. -/
theorem stateIntegralLiouvilleThreshold_le_one {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J : ℕ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    stateIntegralLiouvilleThreshold P J m ≤ 1 :=
  (stateIntegralLiouvilleThreshold_le_half P J m).trans (by norm_num)

/-- The rational-target Liouville threshold is strictly positive. -/
theorem stateRationalLiouvilleThreshold_pos {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J : ℕ)
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ) (l : ℕ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    0 < stateRationalLiouvilleThreshold P J state b bLast l m := by
  let H : ℝ := rationalTargetConjugateBound P (coordinatesForState state)
    state.support state.coeff P.h P.LzeroPlusOne b bLast J l m
  let D : ℝ := ‖(commonDeltaDenominator P.h P.LzeroPlusOne
    (P.q ^ (J + 1)) m : ℂ)‖
  have hH : 1 ≤ H := by
    dsimp only [H]
    exact one_le_rationalTargetConjugateBound P (coordinatesForState state)
      state.support state.coeff P.h P.LzeroPlusOne b bLast J l m
  have hHpow : 0 < H ^ (13 ^ (oldRank + 1) - 1) := by
    exact pow_pos (lt_of_lt_of_le zero_lt_one hH) _
  have hq : P.q ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt P.one_lt_q)
  have hD : 0 < D := by
    dsimp only [D]
    rw [norm_pos_iff]
    exact_mod_cast commonDeltaDenominator_ne_zero P.h P.LzeroPlusOne
      (P.q ^ (J + 1)) (pow_ne_zero (J + 1) hq) m
  change 0 < ((H ^ (13 ^ (oldRank + 1) - 1))⁻¹ / D) / 2
  exact div_pos (div_pos (inv_pos.mpr hHpow) hD) (by norm_num)

/-- The rational-target Liouville threshold is at most one half. -/
theorem stateRationalLiouvilleThreshold_le_half {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J : ℕ)
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ) (l : ℕ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    stateRationalLiouvilleThreshold P J state b bLast l m ≤ (1 : ℝ) / 2 := by
  let H : ℝ := rationalTargetConjugateBound P (coordinatesForState state)
    state.support state.coeff P.h P.LzeroPlusOne b bLast J l m
  let D : ℝ := ‖(commonDeltaDenominator P.h P.LzeroPlusOne
    (P.q ^ (J + 1)) m : ℂ)‖
  have hH : 1 ≤ H := by
    dsimp only [H]
    exact one_le_rationalTargetConjugateBound P (coordinatesForState state)
      state.support state.coeff P.h P.LzeroPlusOne b bLast J l m
  have hHpow : 1 ≤ H ^ (13 ^ (oldRank + 1) - 1) := one_le_pow₀ hH
  have hHpowPos : 0 < H ^ (13 ^ (oldRank + 1) - 1) :=
    lt_of_lt_of_le zero_lt_one hHpow
  have hinv : (H ^ (13 ^ (oldRank + 1) - 1))⁻¹ ≤ (1 : ℝ) := by
    rw [inv_eq_one_div, div_le_iff₀ hHpowPos]
    simpa using hHpow
  have hq : P.q ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt P.one_lt_q)
  have hD : 1 ≤ D := by
    dsimp only [D]
    exact one_le_norm_commonDeltaDenominator P.h P.LzeroPlusOne
      (P.q ^ (J + 1)) (pow_ne_zero (J + 1) hq) m
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hquot : (H ^ (13 ^ (oldRank + 1) - 1))⁻¹ / D ≤ (1 : ℝ) := by
    rw [div_le_iff₀ hDpos]
    simpa only [one_mul] using hinv.trans hD
  change ((H ^ (13 ^ (oldRank + 1) - 1))⁻¹ / D) / 2 ≤ (1 : ℝ) / 2
  exact div_le_div_of_nonneg_right hquot (by norm_num)

/-- A coarser unit upper bound for the rational-target threshold. -/
theorem stateRationalLiouvilleThreshold_le_one {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J : ℕ)
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ) (l : ℕ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    stateRationalLiouvilleThreshold P J state b bLast l m ≤ 1 :=
  (stateRationalLiouvilleThreshold_le_half P J state b bLast l m).trans
    (by norm_num)

end Erdos240.BakerSourceLiouvilleThresholds

#print axioms Erdos240.BakerSourceLiouvilleThresholds.one_le_norm_commonDeltaDenominator
#print axioms Erdos240.BakerSourceLiouvilleThresholds.one_le_rationalTargetConjugateBound
#print axioms Erdos240.BakerSourceLiouvilleThresholds.stateIntegralLiouvilleThreshold_pos
#print axioms Erdos240.BakerSourceLiouvilleThresholds.stateIntegralLiouvilleThreshold_le_half
#print axioms Erdos240.BakerSourceLiouvilleThresholds.stateRationalLiouvilleThreshold_pos
#print axioms Erdos240.BakerSourceLiouvilleThresholds.stateRationalLiouvilleThreshold_le_half
