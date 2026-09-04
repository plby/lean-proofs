import ErdosProblems.Erdos520.HarperCentralMomentIteration
import ErdosProblems.Erdos520.HarperEntropyLossArithmetic
import ErdosProblems.Erdos520.HarperUnconditionalFinalAssembly

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos
namespace Problem520

/-!
# Economical assembly on the complete central unit

The positive-log recursion is uniform on each shrinking central band after
an explicit depth shift.  This file chooses the economical path at every
depth, sums the resulting volume-preserving budgets, disposes of the final
tiny core by Jensen, and joins the two outer half-unit pieces.  The result is
the central local-moment interface used by the unconditional final assembly.
-/

theorem volume_real_harperOuterCentralBand (positive : Bool) :
    volume.real (harperOuterCentralBand positive) = 1 / 2 := by
  cases positive <;>
    simp only [harperOuterCentralBand, Bool.false_eq_true, if_false, if_true,
      Measure.real, Real.volume_Ioc, Real.volume_Ico] <;>
    rw [ENNReal.toReal_ofReal] <;> norm_num

theorem volume_real_harperSignedDyadicBand_eq_half_pow
    (positive : Bool) (d : ℕ) :
    volume.real (harperSignedDyadicBand positive d) =
      (1 / 2 : ℝ) ^ (d + 2) := by
  rw [volume_real_harperSignedDyadicBand]
  unfold harperDyadicRadius
  rw [one_div_pow]

noncomputable def harperCentralEconomicalAffineSlope (J : ℕ) : ℝ :=
  harperCentralEntropyLinearConstant J + Real.log 2 / 2 + Real.log 4

noncomputable def harperCentralEconomicalAffineIntercept
    (E D : ℝ) : ℝ :=
  E / 2 + D + 5

theorem harperCentralEconomicalAffineSlope_nonneg (J : ℕ) :
    0 ≤ harperCentralEconomicalAffineSlope J := by
  have hcentral := harperCentralEntropyLinearConstant_nonneg J
  have hlog2 : 0 ≤ Real.log 2 / 2 := by positivity
  have hlog4 : 0 ≤ Real.log 4 := by positivity
  unfold harperCentralEconomicalAffineSlope
  linarith

theorem harperCentralEconomicalAffineIntercept_nonneg
    {E D : ℝ} (hE : 0 ≤ E) (hD : 0 ≤ D) :
    0 ≤ harperCentralEconomicalAffineIntercept E D := by
  unfold harperCentralEconomicalAffineIntercept
  positivity

/-- The complete positive-log intercept at a central economical start is
affine in the dyadic depth. -/
theorem harperCentralEconomical_offset_add_height_le_affine
    (J d : ℕ) (E D : ℝ) :
    harperExplicitPrefixPositiveLogOffset
          (harperEconomicalCentralStart J d) 1 0 E D + 3 +
        (((d + 1 : ℕ) : ℝ) * Real.log 4) ≤
      harperCentralEconomicalAffineSlope J * ((d : ℝ) + 1) +
        harperCentralEconomicalAffineIntercept E D := by
  have hbase :=
    harperExplicitPrefixEntropyBase_economicalCentralStart_le_depth J d
  have htaylor :=
    harperScheduledLogTaylorAllowance_le_four_thirds
      (harperEconomicalCentralStart J d)
  unfold harperExplicitPrefixPositiveLogOffset
    harperCentralEconomicalAffineSlope
    harperCentralEconomicalAffineIntercept
  push_cast at hbase ⊢
  nlinarith

/-- The exponentially suppressed bad branch at depth `d` is dominated by
the same geometric sequence already used by the dyadic decomposition. -/
theorem exp_neg_centralHeight_le_half_pow (d : ℕ) :
    Real.exp (-(((d + 1 : ℕ) : ℝ) * Real.log 4)) ≤
      (1 / 2 : ℝ) ^ d := by
  have hexp :
      Real.exp (-(((d + 1 : ℕ) : ℝ) * Real.log 4)) =
        (1 / 4 : ℝ) ^ (d + 1) := by
    calc
      Real.exp (-(((d + 1 : ℕ) : ℝ) * Real.log 4)) =
          Real.exp (((d + 1 : ℕ) : ℝ) * (-Real.log 4)) := by ring_nf
      _ = Real.exp (-Real.log 4) ^ (d + 1) := by
        rw [Real.exp_nat_mul]
      _ = (1 / 4 : ℝ) ^ (d + 1) := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
        simp only [one_div]
  rw [hexp, pow_succ]
  have hpow : (1 / 4 : ℝ) ^ d ≤ (1 / 2 : ℝ) ^ d := by
    gcongr <;> norm_num
  nlinarith [show 0 ≤ (1 / 4 : ℝ) ^ d by positivity]

private theorem centralSmallBracket_le_of_base_le
    {Q T z bad geometric : ℝ}
    (hQ0 : 0 ≤ Q) (hT0 : 0 ≤ T) (hz0 : 0 ≤ z)
    (hQ : Q ≤ z) (hT : T ≤ z) (hbad : bad ≤ geometric) :
    2 * ((Q ^ harperTwoThird + Q) + 2 * bad) +
        2 * (T ^ harperTwoThird + T) ≤
      4 * (z ^ harperTwoThird + z) + 4 * geometric := by
  have hq : 0 ≤ harperTwoThird := by norm_num [harperTwoThird]
  have hQpow : Q ^ harperTwoThird ≤ z ^ harperTwoThird :=
    Real.rpow_le_rpow hQ0 hQ hq
  have hTpow : T ^ harperTwoThird ≤ z ^ harperTwoThird :=
    Real.rpow_le_rpow hT0 hT hq
  nlinarith

noncomputable def harperCentralEconomicalBudgetSlope (J : ℕ) : ℝ :=
  harperExplicitMertensConstant * harperTiltedPositiveLogSlope *
    harperCentralEconomicalAffineSlope J

noncomputable def harperCentralEconomicalBudgetIntercept
    (E D : ℝ) : ℝ :=
  harperExplicitMertensConstant * harperTiltedPositiveLogSlope *
      harperCentralEconomicalAffineIntercept E D +
    harperExplicitMertensConstant

theorem harperCentralEconomicalBudgetSlope_nonneg (J : ℕ) :
    0 ≤ harperCentralEconomicalBudgetSlope J := by
  unfold harperCentralEconomicalBudgetSlope
  exact mul_nonneg
    (mul_nonneg harperExplicitMertensConstant_pos.le
      harperTiltedPositiveLogSlope_nonneg)
    (harperCentralEconomicalAffineSlope_nonneg J)

theorem harperCentralEconomicalBudgetIntercept_nonneg
    {E D : ℝ} (hE : 0 ≤ E) (hD : 0 ≤ D) :
    0 ≤ harperCentralEconomicalBudgetIntercept E D := by
  unfold harperCentralEconomicalBudgetIntercept
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg harperExplicitMertensConstant_pos.le
        harperTiltedPositiveLogSlope_nonneg)
      (harperCentralEconomicalAffineIntercept_nonneg hE hD))
    harperExplicitMertensConstant_pos.le

/-- Pointwise numerical envelope for the complete output of the central
band iterator.  The first term is summable by the volume-preserving budget
lemma; the second is an elementary geometric sequence. -/
theorem harperCentralEconomical_iteratedBracket_le
    (J d : ℕ) {E D : ℝ} (hE : 0 ≤ E) (hD : 0 ≤ D) :
    let V := volume.real (harperSignedDyadicBand true d)
    let X := harperExplicitPrefixPositiveLogOffset
      (harperEconomicalCentralStart J d) 1 0 E D + 3
    let C := (((d + 1 : ℕ) : ℝ) * Real.log 4)
    2 *
          (harperPositiveLogDyadicSmallGoodConstant V
              harperTiltedPositiveLogSlope X C +
            2 * Real.exp (-C)) +
        2 *
          ((harperExplicitMertensConstant * V) ^ harperTwoThird +
            harperExplicitMertensConstant * V) ≤
      4 * harperCentralDyadicBudgetTerm
          (harperCentralEconomicalBudgetSlope J)
          (harperCentralEconomicalBudgetIntercept E D) d +
        4 * (1 / 2 : ℝ) ^ d := by
  dsimp only
  let V : ℝ := (1 / 2 : ℝ) ^ (d + 2)
  let X : ℝ := harperExplicitPrefixPositiveLogOffset
    (harperEconomicalCentralStart J d) 1 0 E D + 3
  let C : ℝ := (((d + 1 : ℕ) : ℝ) * Real.log 4)
  let Q : ℝ := harperExplicitMertensConstant * V *
    harperTiltedPositiveLogSlope * (X + C)
  let T : ℝ := harperExplicitMertensConstant * V
  let z : ℝ := V *
    (harperCentralEconomicalBudgetSlope J * ((d : ℝ) + 1) +
      harperCentralEconomicalBudgetIntercept E D)
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hX : 0 ≤ X := by
    dsimp only [X]
    have h := harperExplicitPrefixPositiveLogOffset_nonneg
      (harperEconomicalCentralStart J d) 1
      (B := 0) (E := E) (D := D) (by norm_num) hE hD
    linarith
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hQ0 : 0 ≤ Q := by
    dsimp only [Q]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg harperExplicitMertensConstant_pos.le hV)
        harperTiltedPositiveLogSlope_nonneg)
      (add_nonneg hX hC)
  have hT0 : 0 ≤ T := by
    dsimp only [T]
    exact mul_nonneg harperExplicitMertensConstant_pos.le hV
  have hz0 : 0 ≤ z := by
    dsimp only [z]
    exact mul_nonneg hV (add_nonneg
      (mul_nonneg (harperCentralEconomicalBudgetSlope_nonneg J)
        (by positivity))
      (harperCentralEconomicalBudgetIntercept_nonneg hE hD))
  have haff : X + C ≤
      harperCentralEconomicalAffineSlope J * ((d : ℝ) + 1) +
        harperCentralEconomicalAffineIntercept E D := by
    simpa only [X, C, Nat.cast_add, Nat.cast_one] using!
      harperCentralEconomical_offset_add_height_le_affine J d E D
  have hcoefficient : 0 ≤ harperExplicitMertensConstant * V *
      harperTiltedPositiveLogSlope := by
    exact mul_nonneg
      (mul_nonneg harperExplicitMertensConstant_pos.le hV)
      harperTiltedPositiveLogSlope_nonneg
  have hQmain : Q ≤
      harperExplicitMertensConstant * V * harperTiltedPositiveLogSlope *
        (harperCentralEconomicalAffineSlope J * ((d : ℝ) + 1) +
          harperCentralEconomicalAffineIntercept E D) := by
    exact mul_le_mul_of_nonneg_left haff hcoefficient
  have hzSplit : z =
      harperExplicitMertensConstant * V * harperTiltedPositiveLogSlope *
          (harperCentralEconomicalAffineSlope J * ((d : ℝ) + 1) +
            harperCentralEconomicalAffineIntercept E D) + T := by
    dsimp only [z, T, harperCentralEconomicalBudgetSlope,
      harperCentralEconomicalBudgetIntercept]
    ring
  have hQ : Q ≤ z := by
    rw [hzSplit]
    exact hQmain.trans (le_add_of_nonneg_right hT0)
  have hT : T ≤ z := by
    rw [hzSplit]
    exact le_add_of_nonneg_left (mul_nonneg hcoefficient
      (add_nonneg
        (mul_nonneg (harperCentralEconomicalAffineSlope_nonneg J)
          (by positivity))
        (harperCentralEconomicalAffineIntercept_nonneg hE hD)))
  have hbad : Real.exp (-C) ≤ (1 / 2 : ℝ) ^ d := by
    simpa only [C] using! exp_neg_centralHeight_le_half_pow d
  have hmain := centralSmallBracket_le_of_base_le
    hQ0 hT0 hz0 hQ hT hbad
  rw [volume_real_harperSignedDyadicBand_eq_half_pow true d]
  unfold harperPositiveLogDyadicSmallGoodConstant
  change 2 * ((Q ^ harperTwoThird + Q) + 2 * Real.exp (-C)) +
      2 * (T ^ harperTwoThird + T) ≤
    4 * harperCentralDyadicBudgetTerm
        (harperCentralEconomicalBudgetSlope J)
        (harperCentralEconomicalBudgetIntercept E D) d +
      4 * (1 / 2 : ℝ) ^ d
  have hzEq : z =
      (1 / 2 : ℝ) ^ (d + 2) *
        (harperCentralEconomicalBudgetSlope J * ((d : ℝ) + 1) +
          harperCentralEconomicalBudgetIntercept E D) := rfl
  rw [show harperCentralDyadicBudgetTerm
      (harperCentralEconomicalBudgetSlope J)
      (harperCentralEconomicalBudgetIntercept E D) d =
        z ^ harperTwoThird + z by
    unfold harperCentralDyadicBudgetTerm
    rw [hzEq]]
  exact hmain

/-- The complete shrinking-band assembly, with one absolute cutoff and one
absolute moment constant. -/
theorem exists_harperEconomicalCentralUnitMomentBound :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ J : ℕ,
      HarperEconomicalCentralUnitMomentBound C J := by
  obtain ⟨E, hE, D, hD, J0, hiter⟩ :=
    exists_integral_harperCentralBand_twoThird_le_iterated
  let J : ℕ := J0 + 1
  let a : ℝ := harperCentralEconomicalBudgetSlope J
  let b : ℝ := harperCentralEconomicalBudgetIntercept E D
  have ha : 0 ≤ a := by
    dsimp only [a]
    exact harperCentralEconomicalBudgetSlope_nonneg J
  have hb : 0 ≤ b := by
    dsimp only [b]
    exact harperCentralEconomicalBudgetIntercept_nonneg hE hD
  obtain ⟨Kbudget, hKbudget, hbudgetSum⟩ :=
    exists_pos_bound_finset_sum_harperCentralDyadicBudgetTerm ha hb
  let W : ℝ := (3 : ℝ) ^ (2 / 3 : ℝ) * 4 ^ ((1 : ℝ) / 3)
  let Vouter : ℝ := 1 / 2
  let Xouter : ℝ := harperExplicitPrefixPositiveLogOffset
    (harperEconomicalCentralStart J0 0) 1 0 E D + 3
  let Couter : ℝ := Real.log 4
  let Bouter : ℝ :=
    2 *
        (harperPositiveLogDyadicSmallGoodConstant Vouter
            harperTiltedPositiveLogSlope Xouter Couter +
          2 * Real.exp (-Couter)) +
      2 *
        ((harperExplicitMertensConstant * Vouter) ^ harperTwoThird +
          harperExplicitMertensConstant * Vouter)
  let Ctail : ℝ := harperExplicitMertensConstant ^ harperTwoThird *
    16 ^ ((1 : ℝ) / 3)
  let Ccore : ℝ := Ctail + 2 * W * (4 * Kbudget + 8)
  let Cfinal : ℝ := 2 * W * Bouter + Ccore
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hVouter : 0 ≤ Vouter := by dsimp only [Vouter]; norm_num
  have hXouter : 0 ≤ Xouter := by
    dsimp only [Xouter]
    have h := harperExplicitPrefixPositiveLogOffset_nonneg
      (harperEconomicalCentralStart J0 0) 1
      (B := 0) (E := E) (D := D) (by norm_num) hE hD
    linarith
  have hCouter : 0 ≤ Couter := by dsimp only [Couter]; positivity
  have hBouter : 0 ≤ Bouter := by
    have hQ : 0 ≤ harperExplicitMertensConstant * Vouter *
        harperTiltedPositiveLogSlope * (Xouter + Couter) := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg harperExplicitMertensConstant_pos.le hVouter)
          harperTiltedPositiveLogSlope_nonneg)
        (add_nonneg hXouter hCouter)
    unfold Bouter harperPositiveLogDyadicSmallGoodConstant
    exact add_nonneg
      (mul_nonneg (by norm_num)
        (add_nonneg
          (add_nonneg (Real.rpow_nonneg hQ _ ) hQ)
          (mul_nonneg (by norm_num) (Real.exp_nonneg _))))
      (mul_nonneg (by norm_num)
        (add_nonneg
          (Real.rpow_nonneg
            (mul_nonneg harperExplicitMertensConstant_pos.le hVouter) _)
          (mul_nonneg harperExplicitMertensConstant_pos.le hVouter)))
  have hCtail : 0 ≤ Ctail := by
    dsimp only [Ctail]
    exact mul_nonneg
      (Real.rpow_nonneg harperExplicitMertensConstant_pos.le _)
      (Real.rpow_nonneg (by norm_num) _)
  have hCcore : 0 ≤ Ccore := by
    dsimp only [Ccore]
    exact add_nonneg hCtail
      (mul_nonneg (mul_nonneg (by norm_num) hW)
        (by nlinarith [hKbudget]))
  have hCfinal : 0 ≤ Cfinal := by
    dsimp only [Cfinal]
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hW) hBouter)
      hCcore
  refine ⟨Cfinal, hCfinal, J, ?_⟩
  intro y hlarge hy
  let scale : ℝ := 1 + logLogNat y
  let N : ℕ := harperEconomicalCentralDepth y
  let m : ℕ := Nat.clog 2 N
  let scaleWeight : ℝ := scale ^ (-(1 : ℝ) / 3)
  have hscale : 0 < scale := by
    simpa only [scale] using! one_add_logLogNat_pos_of_four_le hy
  have hscaleWeight : 0 ≤ scaleWeight := by
    dsimp only [scaleWeight]
    exact Real.rpow_nonneg hscale.le _
  have hlargeJ0 :
      8 * (J0 + 2) ≤ harperAvailableLogScale y := by
    dsimp only [J] at hlarge
    omega
  have hN : 1 ≤ N := by
    dsimp only [N, harperEconomicalCentralDepth]
    dsimp only [J] at hlarge
    omega
  have hmN : m ≤ N := by
    dsimp only [m]
    exact harper_clog_two_le_self N
  have hy0 : y ≠ 0 := by omega
  have hscaleN : scale ≤ 16 * (N : ℝ) := by
    have havail : 16 ≤ harperAvailableLogScale y := by
      dsimp only [J] at hlarge
      omega
    have h := one_add_logLogNat_le_sixteen_mul_economicalVerticalTruncation
      havail
    simpa only [scale, N, harperEconomicalCentralDepth,
      harperEconomicalVerticalTruncation] using! h
  have hcoreRaw := integral_harperEulerSetEnergy_clogCore_twoThird_le
    (y := y) (n := N) (by omega) hN
  have hcoreScale := rpow_div_nat_twoThird_le_of_scale_le_mul
    (A := harperExplicitMertensConstant) (scale := scale)
    (factor := 16) (n := N)
    harperExplicitMertensConstant_pos.le hscale (by norm_num) hN hscaleN
  have hcore :
      (∫ omega,
        harperEulerSetEnergy y (harperDyadicCore m) omega ^
          harperTwoThird ∂μ) ≤ Ctail * scaleWeight := by
    have h := hcoreRaw.trans hcoreScale
    simpa only [m, Ctail, scaleWeight] using! h
  have hband : ∀ positive d, d < m →
      (∫ omega,
        harperEulerSetEnergy y (harperSignedDyadicBand positive d) omega ^
          harperTwoThird ∂μ) ≤
        (W * scaleWeight) *
          (4 * harperCentralDyadicBudgetTerm a b d +
            4 * (1 / 2 : ℝ) ^ d) := by
    intro positive d hd
    have hdN : d < N := lt_of_lt_of_le hd hmN
    let start : ℕ := harperEconomicalCentralStart J d
    let path : ℕ := harperEconomicalCentralPathLength y J d
    let Cd : ℝ := (((d + 1 : ℕ) : ℝ) * Real.log 4)
    have hpath : 0 < path := by
      dsimp only [path]
      exact harperEconomicalCentralPathLength_pos hlarge hdN
    have hendpoint : harperBlockEndpoint (start + path) ≤ y := by
      dsimp only [start, path]
      exact harperBlockEndpoint_economicalCentralStart_add_path_le
        hy0 hlarge hdN
    have hstart : J0 + (d + 1) ≤ start := by
      dsimp only [start, J, harperEconomicalCentralStart,
        harperEconomicalStart]
      omega
    have hCd : Real.log 4 ≤ Cd := by
      dsimp only [Cd]
      have hlog : 0 ≤ Real.log 4 := by positivity
      push_cast
      nlinarith
    have hstop : harperDyadicMomentGap path *
        Real.sqrt (path : ℝ) ≤ 2 :=
      harperDyadicMomentGap_mul_sqrt_nat_le_two_at_length (by omega)
    have hraw := hiter (d + 1) start path y hstart hpath
      hendpoint (by omega)
      (harperSignedDyadicBand positive d)
      (measurableSet_harperSignedDyadicBand positive d)
      (harperSignedDyadicBand_finite positive d)
      (fun t ht ↦ (abs_bounds_of_mem_harperSignedDyadicBand
        positive d ht).1)
      (fun t ht ↦ (abs_bounds_of_mem_harperSignedDyadicBand
        positive d ht).2)
      Cd hCd path hstop
    have hbracket := harperCentralEconomical_iteratedBracket_le
      J d hE hD
    have hraw' :
        (∫ omega,
          harperEulerSetEnergy y (harperSignedDyadicBand positive d) omega ^
            harperTwoThird ∂μ) ≤
          harperDyadicMomentWeight (Real.sqrt (path : ℝ)) 0 *
            (2 *
                (harperPositiveLogDyadicSmallGoodConstant
                    (volume.real (harperSignedDyadicBand positive d))
                    harperTiltedPositiveLogSlope
                    (harperExplicitPrefixPositiveLogOffset
                      start 1 0 E D + 3) Cd +
                  2 * Real.exp (-Cd)) +
              2 *
                ((harperExplicitMertensConstant *
                    volume.real (harperSignedDyadicBand positive d)) ^
                    harperTwoThird +
                  harperExplicitMertensConstant *
                    volume.real (harperSignedDyadicBand positive d))) := by
      simpa only [start, path, Cd] using! hraw
    have hbracket' :
        2 *
              (harperPositiveLogDyadicSmallGoodConstant
                  (volume.real (harperSignedDyadicBand positive d))
                  harperTiltedPositiveLogSlope
                  (harperExplicitPrefixPositiveLogOffset
                    start 1 0 E D + 3) Cd +
                2 * Real.exp (-Cd)) +
            2 *
              ((harperExplicitMertensConstant *
                  volume.real (harperSignedDyadicBand positive d)) ^
                  harperTwoThird +
                harperExplicitMertensConstant *
                  volume.real (harperSignedDyadicBand positive d)) ≤
          4 * harperCentralDyadicBudgetTerm a b d +
            4 * (1 / 2 : ℝ) ^ d := by
      rw [volume_real_harperSignedDyadicBand_eq_half_pow positive d]
      simpa only [start, Cd, J, a, b,
        volume_real_harperSignedDyadicBand_eq_half_pow] using! hbracket
    have hweight := harperDyadicMomentWeight_sqrt_nat_initial_le_of_scale
      hscale (show 1 ≤ path by omega)
      (one_add_logLogNat_le_four_mul_economicalCentralPathLength
        hlarge hdN)
    have hwalkPos : 0 < Real.sqrt (path : ℝ) := by
      exact Real.sqrt_pos.2 (by exact_mod_cast hpath)
    have hweight0 : 0 ≤
        harperDyadicMomentWeight (Real.sqrt (path : ℝ)) 0 :=
      (harperDyadicMomentWeight_pos hwalkPos 0).le
    have hbudget0 : 0 ≤ harperCentralDyadicBudgetTerm a b d := by
      unfold harperCentralDyadicBudgetTerm
      have hz : 0 ≤ (1 / 2 : ℝ) ^ (d + 2) *
          (a * ((d : ℝ) + 1) + b) := by positivity
      exact add_nonneg (Real.rpow_nonneg hz _) hz
    have henv0 : 0 ≤
        4 * harperCentralDyadicBudgetTerm a b d +
          4 * (1 / 2 : ℝ) ^ d := by positivity
    calc
      (∫ omega,
          harperEulerSetEnergy y (harperSignedDyadicBand positive d) omega ^
            harperTwoThird ∂μ) ≤
          harperDyadicMomentWeight (Real.sqrt (path : ℝ)) 0 *
            (2 *
                (harperPositiveLogDyadicSmallGoodConstant
                    (volume.real (harperSignedDyadicBand positive d))
                    harperTiltedPositiveLogSlope
                    (harperExplicitPrefixPositiveLogOffset
                      start 1 0 E D + 3) Cd +
                  2 * Real.exp (-Cd)) +
              2 *
                ((harperExplicitMertensConstant *
                    volume.real (harperSignedDyadicBand positive d)) ^
                    harperTwoThird +
                  harperExplicitMertensConstant *
                    volume.real (harperSignedDyadicBand positive d))) := hraw'
      _ ≤ harperDyadicMomentWeight (Real.sqrt (path : ℝ)) 0 *
          (4 * harperCentralDyadicBudgetTerm a b d +
            4 * (1 / 2 : ℝ) ^ d) :=
        mul_le_mul_of_nonneg_left hbracket' hweight0
      _ ≤ (W * scaleWeight) *
          (4 * harperCentralDyadicBudgetTerm a b d +
            4 * (1 / 2 : ℝ) ^ d) := by
        exact mul_le_mul_of_nonneg_right
          (by simpa only [W, scaleWeight] using! hweight) henv0
  have hsumEnvelope :
      (∑ d ∈ Finset.range m,
        (4 * harperCentralDyadicBudgetTerm a b d +
          4 * (1 / 2 : ℝ) ^ d)) ≤ 4 * Kbudget + 8 := by
    calc
      (∑ d ∈ Finset.range m,
          (4 * harperCentralDyadicBudgetTerm a b d +
            4 * (1 / 2 : ℝ) ^ d)) =
          4 * (∑ d ∈ Finset.range m,
            harperCentralDyadicBudgetTerm a b d) +
            4 * (∑ d ∈ Finset.range m, (1 / 2 : ℝ) ^ d) := by
        simp only [Finset.sum_add_distrib]
        rw [Finset.mul_sum, Finset.mul_sum]
      _ ≤ 4 * Kbudget + 4 * 2 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (hbudgetSum m) (by norm_num))
          (mul_le_mul_of_nonneg_left (sum_range_inv_two_pow_le_two m)
            (by norm_num))
      _ = 4 * Kbudget + 8 := by ring
  have hcoreZero := integral_harperEulerSetEnergy_core_zero_twoThird_le
    (y := y) (m := m) (by omega) hcore hband
  have hpairSum :
      (∑ d ∈ Finset.range m,
        (((W * scaleWeight) *
            (4 * harperCentralDyadicBudgetTerm a b d +
              4 * (1 / 2 : ℝ) ^ d)) +
          ((W * scaleWeight) *
            (4 * harperCentralDyadicBudgetTerm a b d +
              4 * (1 / 2 : ℝ) ^ d)))) ≤
        2 * W * (4 * Kbudget + 8) * scaleWeight := by
    calc
      (∑ d ∈ Finset.range m,
          (((W * scaleWeight) *
              (4 * harperCentralDyadicBudgetTerm a b d +
                4 * (1 / 2 : ℝ) ^ d)) +
            ((W * scaleWeight) *
              (4 * harperCentralDyadicBudgetTerm a b d +
                4 * (1 / 2 : ℝ) ^ d)))) =
          (2 * W * scaleWeight) *
            (∑ d ∈ Finset.range m,
              (4 * harperCentralDyadicBudgetTerm a b d +
                4 * (1 / 2 : ℝ) ^ d)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        ring
      _ ≤ (2 * W * scaleWeight) * (4 * Kbudget + 8) := by
        exact mul_le_mul_of_nonneg_left hsumEnvelope (by positivity)
      _ = 2 * W * (4 * Kbudget + 8) * scaleWeight := by ring
  have hcoreZero' :
      (∫ omega,
        harperEulerSetEnergy y (harperDyadicCore 0) omega ^
          harperTwoThird ∂μ) ≤ Ccore * scaleWeight := by
    calc
      (∫ omega,
          harperEulerSetEnergy y (harperDyadicCore 0) omega ^
            harperTwoThird ∂μ) ≤
          Ctail * scaleWeight +
            ∑ d ∈ Finset.range m,
              (((W * scaleWeight) *
                  (4 * harperCentralDyadicBudgetTerm a b d +
                    4 * (1 / 2 : ℝ) ^ d)) +
                ((W * scaleWeight) *
                  (4 * harperCentralDyadicBudgetTerm a b d +
                    4 * (1 / 2 : ℝ) ^ d))) := hcoreZero
      _ ≤ Ctail * scaleWeight +
          2 * W * (4 * Kbudget + 8) * scaleWeight :=
        add_le_add le_rfl hpairSum
      _ = Ccore * scaleWeight := by
        dsimp only [Ccore]
        ring
  have houter : ∀ positive,
      (∫ omega,
        harperEulerSetEnergy y (harperOuterCentralBand positive) omega ^
          harperTwoThird ∂μ) ≤ (W * Bouter) * scaleWeight := by
    intro positive
    let start : ℕ := harperEconomicalCentralStart J0 0
    let path : ℕ := harperEconomicalCentralPathLength y J0 0
    have hdepth : 0 < harperEconomicalCentralDepth y := by
      simpa only [N] using! hN
    have hpath : 0 < path := by
      dsimp only [path]
      exact harperEconomicalCentralPathLength_pos hlargeJ0 hdepth
    have hendpoint : harperBlockEndpoint (start + path) ≤ y := by
      dsimp only [start, path]
      exact harperBlockEndpoint_economicalCentralStart_add_path_le
        hy0 hlargeJ0 hdepth
    have hstart : J0 + 0 ≤ start := by
      dsimp only [start, harperEconomicalCentralStart,
        harperEconomicalStart]
      omega
    have hstop : harperDyadicMomentGap path *
        Real.sqrt (path : ℝ) ≤ 2 :=
      harperDyadicMomentGap_mul_sqrt_nat_le_two_at_length (by omega)
    have hraw := hiter 0 start path y hstart hpath hendpoint (by omega)
      (harperOuterCentralBand positive)
      (measurableSet_harperOuterCentralBand positive)
      (harperOuterCentralBand_finite positive)
      (fun t ht ↦ by
        simpa only [zero_add, pow_one] using!
          (abs_bounds_of_mem_harperOuterCentralBand positive ht).1)
      (fun t ht ↦ by
        simpa only [pow_zero] using!
          (abs_bounds_of_mem_harperOuterCentralBand positive ht).2)
      (Real.log 4) (le_rfl) path hstop
    have hraw' :
        (∫ omega,
          harperEulerSetEnergy y (harperOuterCentralBand positive) omega ^
            harperTwoThird ∂μ) ≤
          harperDyadicMomentWeight (Real.sqrt (path : ℝ)) 0 * Bouter := by
      rw [volume_real_harperOuterCentralBand positive] at hraw
      simpa only [start, path, Vouter, Xouter, Couter, Bouter] using! hraw
    have hweight := harperDyadicMomentWeight_sqrt_nat_initial_le_of_scale
      hscale (show 1 ≤ path by omega)
      (one_add_logLogNat_le_four_mul_economicalCentralPathLength
        hlargeJ0 hdepth)
    calc
      (∫ omega,
          harperEulerSetEnergy y (harperOuterCentralBand positive) omega ^
            harperTwoThird ∂μ) ≤
          harperDyadicMomentWeight (Real.sqrt (path : ℝ)) 0 * Bouter := hraw'
      _ ≤ (W * scaleWeight) * Bouter :=
        mul_le_mul_of_nonneg_right
          (by simpa only [W, scaleWeight] using! hweight) hBouter
      _ = (W * Bouter) * scaleWeight := by ring
  have hcentral := integral_harperEulerSetEnergy_centralUnit_twoThird_le
    (y := y) (by omega)
    (outerBudget := fun _ ↦ (W * Bouter) * scaleWeight)
    (coreBudget := Ccore * scaleWeight) houter hcoreZero'
  calc
    (∫ omega,
      harperEulerSetEnergy y harperCentralUnitSet omega ^
        harperTwoThird ∂μ) ≤
        (W * Bouter) * scaleWeight + Ccore * scaleWeight +
          (W * Bouter) * scaleWeight := hcentral
    _ = Cfinal * (1 + logLogNat y) ^ (-(1 : ℝ) / 3) := by
      dsimp only [Cfinal, scaleWeight, scale]
      ring

end Problem520
end Erdos

#print axioms Erdos.Problem520.harperCentralEconomical_iteratedBracket_le
#print axioms Erdos.Problem520.exists_harperEconomicalCentralUnitMomentBound
