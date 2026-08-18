/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section8Synthesis
import ErdosProblems.Erdos186.CFP.Bilu.Section4TerminalConstants
import ErdosProblems.Erdos186.CFP.Bilu.Section8PresentationNormalization

/-!
# Algebra for the Proposition 7.5 volume decay

This module isolates the real-power calculation used after the geometric
replacement has been constructed.  If the replacement has volume at most
`L * v / epsilon^(1/Q)` and `epsilon = c * v / card`, raising to the
integer power `Q` gives precisely the Section 4 decay inequality.
-/

namespace Erdos186.CFP.Bilu.Section4DecayAlgebra

open Section4ScaledDecay Section4TerminalConstants
open Section92PresentationDescent Section92WeightedRankRepair
open Section8PresentationNormalization MinkowskiUpper MeasureTheory

noncomputable section

set_option autoImplicit false

/-- Cancellation of Bilu's reciprocal real exponent after raising to its
positive natural denominator. -/
theorem rpow_inv_nat_pow {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {Q : ℕ} (hQ : 0 < Q) :
    (epsilon ^ ((Q : ℝ)⁻¹)) ^ Q = epsilon := by
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hepsilon.le]
  rw [inv_mul_cancel₀ (by exact_mod_cast hQ.ne')]
  exact Real.rpow_one epsilon

/-- On a base at least one, increasing the real exponent decreases the
reciprocal power. -/
theorem inv_rpow_le_inv_rpow_of_exponent_le
    {epsilon smallExponent largeExponent : ℝ}
    (hepsilon : 1 ≤ epsilon)
    (hexponents : smallExponent ≤ largeExponent) :
    (epsilon ^ largeExponent)⁻¹ ≤ (epsilon ^ smallExponent)⁻¹ := by
  have hpow : epsilon ^ smallExponent ≤ epsilon ^ largeExponent :=
    Real.rpow_le_rpow_of_exponent_le hepsilon hexponents
  have hsmall : 0 < epsilon ^ smallExponent :=
    Real.rpow_pos_of_pos (zero_lt_one.trans_le hepsilon) _
  have hlarge : 0 < epsilon ^ largeExponent :=
    Real.rpow_pos_of_pos (zero_lt_one.trans_le hepsilon) _
  exact (inv_le_inv₀ hlarge hsmall).2 hpow

/-- A rank bound compares the reciprocal Proposition 8.3 exponents. -/
theorem inv_uniformDenominator_le_proposition83Exponent
    {m rankBound r : ℕ} (hm : m ≤ rankBound) (hr : 0 < r) :
    (((2 * (2 * rankBound + r) : ℕ) : ℝ))⁻¹ ≤
      Section8Synthesis.proposition83Exponent m r := by
  unfold Section8Synthesis.proposition83Exponent
  rw [one_div]
  have hdenPos : (0 : ℝ) < ((2 * (2 * m + r) : ℕ) : ℝ) := by
    positivity
  have hdenLe : ((2 * (2 * m + r) : ℕ) : ℝ) ≤
      ((2 * (2 * rankBound + r) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_le_mul_left 2
      (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hm) r)
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    ((inv_le_inv₀ (lt_of_lt_of_le hdenPos hdenLe)
      hdenPos).2 hdenLe)

/-- The uniform choice `epsilon = 4^(-rankBound) * volume / card`
satisfies the polar-volume largeness inequality at every positive rank below
`rankBound`. -/
theorem polar_large_numeric_of_rank_le
    {m rankBound : ℕ} (hm : m ≤ rankBound)
    {oldVolume card : ℝ} (hold : 0 < oldVolume) (hcard : 0 < card) :
    (((16 : ℝ) * m) ^ m) *
          (((((4 : ℝ) ^ rankBound)⁻¹ * oldVolume) / card)) * card ≤
      (4 : ℝ) ^ m * (((m : ℝ) ^ m) * oldVolume) := by
  have hfour : (1 : ℝ) ≤ 4 := by norm_num
  have hpow : (4 : ℝ) ^ m ≤ 4 ^ rankBound :=
    pow_le_pow_right₀ hfour hm
  have hpowPos : 0 < (4 : ℝ) ^ rankBound := by positivity
  have hinvMul : ((4 : ℝ) ^ rankBound)⁻¹ * (4 ^ m) ≤ 1 := by
    rw [inv_mul_le_one₀ hpowPos]
    exact hpow
  have hmNonneg : (0 : ℝ) ≤ m := by positivity
  have hcore : (((16 : ℝ) * m) ^ m) *
        (((4 : ℝ) ^ rankBound)⁻¹ * oldVolume) ≤
      (4 : ℝ) ^ m * (((m : ℝ) ^ m) * oldVolume) := by
    rw [mul_pow, show (16 : ℝ) = 4 * 4 by norm_num, mul_pow]
    have hnonneg : 0 ≤ (4 : ℝ) ^ m * (m : ℝ) ^ m * oldVolume := by
      positivity
    calc
      (4 ^ m * 4 ^ m * m ^ m) *
          ((4 ^ rankBound)⁻¹ * oldVolume) =
          ((4 ^ rankBound)⁻¹ * 4 ^ m) *
            (4 ^ m * m ^ m * oldVolume) := by ring
      _ ≤ 1 * (4 ^ m * m ^ m * oldVolume) :=
        mul_le_mul_of_nonneg_right hinvMul hnonneg
      _ = 4 ^ m * (m ^ m * oldVolume) := by ring
  calc
    (((16 : ℝ) * m) ^ m) *
          (((((4 : ℝ) ^ rankBound)⁻¹ * oldVolume) / card)) * card =
        (((16 : ℝ) * m) ^ m) *
          (((4 : ℝ) ^ rankBound)⁻¹ * oldVolume) := by
      field_simp
    _ ≤ (4 : ℝ) ^ m * (((m : ℝ) ^ m) * oldVolume) := hcore

/-- Real form of the exact normalized Mahler unit-ball volume identity. -/
theorem normalizedMahlerUnitBall_volumeReal
    {A : Finset ℤ} (X : RankedBodyPresentation A) :
    volume.real (unitBall (normalizedMahlerSeminorm X)) =
      (X.1 : ℝ) ^ X.1 * bodyVolume X := by
  rw [Measure.real, volume_normalizedMahlerUnitBall,
    ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg (Nat.cast_nonneg X.1) _)]
  rfl

/-- The terminal scaled-volume threshold implies the unscaled raw linear
threshold.  This is the strict inequality used to make the selected
`epsilon` exceed every Proposition 8.3 dimension constant. -/
theorem bodyVolume_gt_rawConstant_mul_of_terminal_lt
    {A : Finset ℤ} (s rankBound cardinalityThreshold rawConstant : ℕ)
    (hthreshold : 1 ≤ cardinalityThreshold)
    (hA : A.Nonempty) (X : RankedBodyPresentation A)
    (hlarge :
      ((terminalVolumeConstant s rankBound cardinalityThreshold
          rawConstant * A.card : ℕ) : ℝ) <
        uniformTerminalBodyVolume s rankBound X) :
    (((rawConstant * A.card : ℕ) : ℝ)) < bodyVolume X := by
  have hscale := uniformTerminalScale_pos s rankBound
  have hbound :=
    uniformTerminalScale_mul_rawConstant_mul_le_terminalVolumeConstant_mul
      s rankBound cardinalityThreshold rawConstant A.card hthreshold
        hA.card_pos
  have hstrict : uniformTerminalScale s rankBound *
      (((rawConstant * A.card : ℕ) : ℝ)) <
        uniformTerminalScale s rankBound * bodyVolume X := by
    apply hbound.trans_lt
    simpa only [uniformTerminalBodyVolume, uniformTerminalScale,
      mul_assoc] using hlarge
  exact lt_of_mul_lt_mul_left hstrict hscale.le

/-- If the rank-repaired presentation does not already satisfy the desired
decay, its volume is linearly large.  The only loss is the fixed factor by
which rank repair may enlarge ordinary volume. -/
theorem linear_large_of_not_pow_decay
    {oldVolume repairedVolume card rawConstant repairFactor : ℝ}
    {Q : ℕ} (hQ : 0 < Q)
    (hold : 0 < oldVolume) (hrepaired : 0 < repairedVolume)
    (hrepair : repairedVolume ≤ repairFactor * oldVolume)
    (hnot : ¬ (2 * repairedVolume) ^ Q ≤
      rawConstant * card * oldVolume ^ (Q - 1)) :
    rawConstant * card <
      2 ^ Q * repairFactor ^ (Q - 1) * repairedVolume := by
  have hpowOld : 0 < oldVolume ^ (Q - 1) := pow_pos hold _
  have hpowRepair : repairedVolume ^ (Q - 1) ≤
      (repairFactor * oldVolume) ^ (Q - 1) :=
    pow_le_pow_left₀ hrepaired.le hrepair _
  have hupper : (2 * repairedVolume) ^ Q ≤
      (2 ^ Q * repairFactor ^ (Q - 1) * repairedVolume) *
        oldVolume ^ (Q - 1) := by
    have hQeq : Q = (Q - 1) + 1 := by omega
    have hnonneg : 0 ≤ 2 ^ Q * repairedVolume := by positivity
    calc
      (2 * repairedVolume) ^ Q =
          (2 ^ Q * repairedVolume) * repairedVolume ^ (Q - 1) := by
        rw [mul_pow]
        nth_rewrite 2 [hQeq]
        rw [pow_succ]
        ring
      _ ≤ (2 ^ Q * repairedVolume) *
          ((repairFactor * oldVolume) ^ (Q - 1)) :=
        mul_le_mul_of_nonneg_left hpowRepair hnonneg
      _ = (2 ^ Q * repairFactor ^ (Q - 1) * repairedVolume) *
          oldVolume ^ (Q - 1) := by
        rw [mul_pow]
        ring
  have hstrict : (rawConstant * card) * oldVolume ^ (Q - 1) <
      (2 ^ Q * repairFactor ^ (Q - 1) * repairedVolume) *
        oldVolume ^ (Q - 1) :=
    (lt_of_not_ge hnot).trans_le hupper
  exact lt_of_mul_lt_mul_right hstrict hpowOld.le

/-- Forgetting the rank weights costs at most the ceiling-rank power of the
fixed repair factor. -/
theorem bodyVolume_le_factor_pow_rankBound_of_weighted_le
    {A : Finset ℤ} {repairFactor : ℝ} {rankBound : ℕ}
    (hfactor : 1 ≤ repairFactor)
    (old repaired : RankedBodyPresentation A)
    (holdRank : old.1 ≤ rankBound)
    (hweighted : rankWeightedBodyVolume repairFactor repaired ≤
      rankWeightedBodyVolume repairFactor old) :
    bodyVolume repaired ≤
      repairFactor ^ rankBound * bodyVolume old := by
  have hleft := bodyVolume_le_rankWeightedBodyVolume hfactor repaired
  have hpow : repairFactor ^ old.1 ≤ repairFactor ^ rankBound :=
    pow_le_pow_right₀ hfactor holdRank
  have hright : rankWeightedBodyVolume repairFactor old ≤
      repairFactor ^ rankBound * bodyVolume old := by
    exact mul_le_mul_of_nonneg_right hpow (bodyVolume_pos old).le
  exact hleft.trans (hweighted.trans hright)

/-- Converting the linear largeness conclusion into the expansion
parameter required by Proposition 8.3. -/
theorem threshold_lt_coefficient_mul_div_of_linear_large
    {threshold coefficient rawConstant card factor volume : ℝ}
    (hcoefficient : 0 < coefficient) (hcard : 0 < card)
    (hfactor : 0 < factor)
    (hconstant : factor * threshold / coefficient ≤ rawConstant)
    (hlinear : rawConstant * card < factor * volume) :
    threshold < coefficient * volume / card := by
  have hscaled : (factor * threshold / coefficient) * card <
      factor * volume :=
    (mul_le_mul_of_nonneg_right hconstant hcard.le).trans_lt hlinear
  have hcancelFactor : threshold / coefficient * card < volume := by
    apply (mul_lt_mul_iff_of_pos_left hfactor).mp
    simpa only [div_eq_mul_inv, mul_assoc] using hscaled
  have hcancelCoefficient : threshold * card < coefficient * volume := by
    calc
      threshold * card =
          coefficient * (threshold / coefficient * card) := by
        field_simp
      _ < coefficient * volume :=
        mul_lt_mul_of_pos_left hcancelFactor hcoefficient
  exact (lt_div_iff₀ hcard).2 hcancelCoefficient

/-- The exact volume-decay calculation underlying the Section 4 iteration.
All geometry is compressed into the single upper bound `hnew`. -/
theorem pow_decay_of_replacement_bound
    {oldVolume newVolume card coefficient loss : ℝ} {Q : ℕ}
    (hQ : 0 < Q)
    (hold : 0 < oldVolume) (hnewNonneg : 0 ≤ newVolume)
    (hcard : 0 < card) (hcoefficient : 0 < coefficient)
    (hloss : 0 ≤ loss)
    (hnew : newVolume ≤
      loss * oldVolume *
        ((coefficient * oldVolume / card) ^ ((Q : ℝ)⁻¹))⁻¹) :
    (2 * newVolume) ^ Q ≤
      (2 ^ Q * loss ^ Q / coefficient) * card *
        oldVolume ^ (Q - 1) := by
  let epsilon : ℝ := coefficient * oldVolume / card
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    positivity
  have hroot : 0 < epsilon ^ ((Q : ℝ)⁻¹) :=
    Real.rpow_pos_of_pos hepsilon _
  have hrightNonneg : 0 ≤
      loss * oldVolume * (epsilon ^ ((Q : ℝ)⁻¹))⁻¹ := by positivity
  have hpow := pow_le_pow_left₀ hnewNonneg hnew Q
  have hrootPow : (epsilon ^ ((Q : ℝ)⁻¹)) ^ Q = epsilon :=
    rpow_inv_nat_pow hepsilon hQ
  have holdPow : oldVolume ^ Q = oldVolume ^ (Q - 1) * oldVolume := by
    have hQeq : Q = (Q - 1) + 1 := by omega
    nth_rewrite 1 [hQeq]
    rw [pow_succ]
  calc
    (2 * newVolume) ^ Q = 2 ^ Q * newVolume ^ Q := mul_pow _ _ _
    _ ≤ 2 ^ Q *
        (loss * oldVolume * (epsilon ^ ((Q : ℝ)⁻¹))⁻¹) ^ Q := by
      gcongr
    _ = (2 ^ Q * loss ^ Q / coefficient) * card *
          oldVolume ^ (Q - 1) := by
      rw [mul_pow, mul_pow, inv_pow, hrootPow, holdPow]
      dsimp only [epsilon]
      field_simp

end

end Erdos186.CFP.Bilu.Section4DecayAlgebra

#print axioms
  Erdos186.CFP.Bilu.Section4DecayAlgebra.rpow_inv_nat_pow
#print axioms
  Erdos186.CFP.Bilu.Section4DecayAlgebra.pow_decay_of_replacement_bound
