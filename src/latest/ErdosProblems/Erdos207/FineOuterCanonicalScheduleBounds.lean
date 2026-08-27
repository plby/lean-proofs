/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FineOuterCanonicalCorridor

/-!
# Uniform bounds from the canonical coupled corridor

The centre is at least `outside / (4 t²)`, while the complete window and
rounding budget uses less than half of that amount.  Thus the recursive lower
pair schedule stays above the floor of `outside / (8 t²)`.  The upper schedule
is bounded by the ceiling of `5 outside`.  Multiplying the former by the
reserved eligible-pair clock gives a uniform availability floor.
-/

namespace Erdos207

open scoped NNReal

noncomputable section

def fineOuterDegreeFloor (outside t : ℕ) : ℕ :=
  nonnegativeNatFloor ((outside : ℝ) / (8 * (t : ℝ) ^ 2))

def fineOuterDegreeCeil (outside : ℕ) : ℕ :=
  nonnegativeNatCeil (5 * (outside : ℝ))

def fineOuterAvailabilityFloor (outside t : ℕ) : ℕ :=
  fineOuterReserve outside t * fineOuterDegreeFloor outside t / 3

/-- The analytic sandwiches imply the two natural-valued endpoint bounds at
any clock before the canonical stop. -/
theorem fineOuterCanonical_pointwise_schedule_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (lower₀ outside t K i : ℕ)
    (houtside : 0 < outside) (ht : 0 < t)
    (hreservePos : 0 < fineOuterReserve outside t)
    (hreserveInitial : fineOuterReserve outside t ≤
      outerSharpEligiblePairs H X 0)
    (hpairUpper : 2 * (outerSharpEligiblePairs H X 0 : ℕ) ≤
      (outside : ℝ) ^ 2)
    (hsmallPower : 12800 ≤ t ^ 31)
    (hoffsetPower : t ^ fineOuterCorridorExponent ≤ 16 * outside)
    (hclockPower : 50 * t ^ 101 ≤ outside ^ 2)
    (haggregatePower : t ^ 102 * K ≤ 8 * outside ^ 2)
    (hinitialOrder : lower₀ ≤ outside)
    (hinitial :
      (outside : ℝ) ≤
          quadraticPairBarrier (outside : ℝ≥0)
            (fineOffsetUpperCoefficient t)
            (outerSharpEligiblePairs H X 0 : ℝ≥0) 3 0 +
              fineOuterInitialOffset outside t ∧
        quadraticPairBarrier (outside : ℝ≥0)
            (fineOffsetLowerCoefficient t)
            (outerSharpEligiblePairs H X 0 : ℝ≥0) 3 0 -
              fineOuterInitialOffset outside t ≤ (lower₀ : ℝ))
    (hfour : 4 ≤ fineOuterReserve outside t)
    (hi : i ≤ outerSharpStopFuel H X (fineOuterReserve outside t)) :
    fineOuterDegreeFloor outside t ≤
        outerSharpLowerSchedule H X
          (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) K i ∧
      outerSharpUpperSchedule H X
          (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) K i ≤
        fineOuterDegreeCeil outside := by
  let A := fineOuterInitialOffset outside t *
    (outerSharpEligiblePairs H X 0 : ℝ) ^ coupledOuterExponent
  have hschedules :=
    outerSharpRecursiveSchedules_between_fineCanonicalBarriers H X
      lower₀ outside t K houtside ht hreservePos hreserveInitial hpairUpper
      hsmallPower hoffsetPower hclockPower haggregatePower hinitialOrder
      hinitial hfour i hi
  have hclockFacts := fineOuterCanonicalClockFacts H X outside t i ht
    hreservePos hreserveInitial hi hpairUpper
  have hsandwich := coupledOuter_power_sandwich H X outside t
    coupledOuterExponent i (t : ℝ) houtside (by positivity)
    hclockFacts.current_pos hclockFacts.current_le_initial
    hclockFacts.compare hclockFacts.lower_clock hclockFacts.upper_clock
  have hscalars := fineOuterCanonicalScalars H X outside t K i
    houtside ht hclockFacts.lower_clock hsmallPower hoffsetPower
    hclockPower haggregatePower
  let centerLower : ℝ := (outside : ℝ) / (4 * (t : ℝ) ^ 2)
  let windowUpper : ℝ :=
    fineOuterInitialOffset outside t * (t : ℝ) ^ coupledOuterExponent
  have htReal : (1 : ℝ) ≤ t := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr ht.ne')
  have hcenterLowerNonneg : 0 ≤ centerLower := by
    dsimp only [centerLower]
    positivity
  have hcenterLowerLe : centerLower ≤ (outside : ℝ) := by
    dsimp only [centerLower]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (t : ℝ) ^ 2)).2
    nlinarith [sq_nonneg ((t : ℝ) - 1)]
  have hbufferLe : fineOuterBuffer outside t ≤ windowUpper := by
    have hoffsetLe : fineOuterInitialOffset outside t ≤ windowUpper := by
      dsimp only [windowUpper]
      have hpow : (1 : ℝ) ≤ (t : ℝ) ^ coupledOuterExponent :=
        one_le_pow₀ htReal
      exact (by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow
          (show 0 ≤ fineOuterInitialOffset outside t by
            unfold fineOuterInitialOffset
            positivity))
    unfold fineOuterBuffer
    have hoffsetNonneg : 0 ≤ fineOuterInitialOffset outside t := by
      unfold fineOuterInitialOffset
      positivity
    linarith
  have hwindowBudget : windowUpper + fineOuterBuffer outside t ≤
      (outside : ℝ) := by
    have hsmall : 100 * windowUpper ≤ centerLower := by
      simpa only [windowUpper, centerLower] using hscalars.small
    nlinarith
  have hlowerReal : (outside : ℝ) / (8 * (t : ℝ) ^ 2) ≤
      outerCoupledLowerBarrier H X outside A coupledOuterExponent i -
        fineOuterBuffer outside t := by
    have hcenter : centerLower ≤ outerCoupledCenter H X outside i := by
      simpa only [A, centerLower] using hsandwich.2.2.1
    have hwindow : outerCoupledWindow H X A coupledOuterExponent i ≤
        windowUpper := by
      simpa only [A, windowUpper] using hsandwich.2.1
    have hsmall : 100 * windowUpper ≤ centerLower := by
      simpa only [windowUpper, centerLower] using hscalars.small
    have hhalf : (outside : ℝ) / (8 * (t : ℝ) ^ 2) =
        centerLower / 2 := by
      dsimp only [centerLower]
      ring
    rw [hhalf]
    unfold outerCoupledLowerBarrier
    nlinarith
  have hupperReal :
      outerCoupledUpperBarrier H X outside A coupledOuterExponent i +
          fineOuterBuffer outside t ≤ 5 * (outside : ℝ) := by
    have hcenter : outerCoupledCenter H X outside i ≤ 4 * outside := by
      simpa only [A] using hsandwich.2.2.2
    have hwindow : outerCoupledWindow H X A coupledOuterExponent i ≤
        windowUpper := by
      simpa only [A, windowUpper] using hsandwich.2.1
    unfold outerCoupledUpperBarrier
    linarith
  constructor
  · apply hschedules.2.1.trans'
    unfold fineOuterDegreeFloor nonnegativeNatFloor
    apply Nat.floor_mono
    apply max_le_max_left
    exact hlowerReal
  · apply hschedules.1.trans
    unfold fineOuterDegreeCeil nonnegativeNatCeil
    apply Nat.ceil_mono
    apply max_le_max_left
    exact hupperReal

/-- The canonical schedules have both the rounding margin used by the
upper-deletion rate and a sharper ratio for the tracked-edge survival law. -/
theorem fineOuterCanonical_schedule_ratio_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (lower₀ outside t K i : ℕ)
    (houtside : 0 < outside) (ht : 0 < t)
    (hreservePos : 0 < fineOuterReserve outside t)
    (hreserveInitial : fineOuterReserve outside t ≤
      outerSharpEligiblePairs H X 0)
    (hpairUpper : 2 * (outerSharpEligiblePairs H X 0 : ℕ) ≤
      (outside : ℝ) ^ 2)
    (hsmallPower : 12800 ≤ t ^ 31)
    (hoffsetPower : t ^ fineOuterCorridorExponent ≤ 16 * outside)
    (hclockPower : 50 * t ^ 101 ≤ outside ^ 2)
    (haggregatePower : t ^ 102 * K ≤ 8 * outside ^ 2)
    (hinitialOrder : lower₀ ≤ outside)
    (hinitial :
      (outside : ℝ) ≤
          quadraticPairBarrier (outside : ℝ≥0)
            (fineOffsetUpperCoefficient t)
            (outerSharpEligiblePairs H X 0 : ℝ≥0) 3 0 +
              fineOuterInitialOffset outside t ∧
        quadraticPairBarrier (outside : ℝ≥0)
            (fineOffsetLowerCoefficient t)
            (outerSharpEligiblePairs H X 0 : ℝ≥0) 3 0 -
              fineOuterInitialOffset outside t ≤ (lower₀ : ℝ))
    (hfour : 4 ≤ fineOuterReserve outside t)
    (hi : i ≤ outerSharpStopFuel H X (fineOuterReserve outside t)) :
    outerSharpUpperSchedule H X
          (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) K i + 2 ≤
      3 * outerSharpLowerSchedule H X
          (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) K i ∧
    4 * outerSharpUpperSchedule H X
          (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) K i ≤
      5 * outerSharpLowerSchedule H X
          (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) K i := by
  let A := fineOuterInitialOffset outside t *
    (outerSharpEligiblePairs H X 0 : ℝ) ^ coupledOuterExponent
  let centerLower : ℝ := (outside : ℝ) / (4 * (t : ℝ) ^ 2)
  let windowUpper : ℝ :=
    fineOuterInitialOffset outside t * (t : ℝ) ^ coupledOuterExponent
  let y := outerCoupledCenter H X outside i
  let w := outerCoupledWindow H X A coupledOuterExponent i
  let b := fineOuterBuffer outside t
  let u := outerSharpUpperSchedule H X
    (outside : ℝ) (lower₀ : ℝ) b K i
  let d := outerSharpLowerSchedule H X
    (outside : ℝ) (lower₀ : ℝ) b K i
  have hschedules :=
    outerSharpRecursiveSchedules_between_fineCanonicalBarriers H X
      lower₀ outside t K houtside ht hreservePos hreserveInitial hpairUpper
      hsmallPower hoffsetPower hclockPower haggregatePower hinitialOrder
      hinitial hfour i hi
  have hclockFacts := fineOuterCanonicalClockFacts H X outside t i ht
    hreservePos hreserveInitial hi hpairUpper
  have hsandwich := coupledOuter_power_sandwich H X outside t
    coupledOuterExponent i (t : ℝ) houtside (by positivity)
    hclockFacts.current_pos hclockFacts.current_le_initial
    hclockFacts.compare hclockFacts.lower_clock hclockFacts.upper_clock
  have hscalars := fineOuterCanonicalScalars H X outside t K i
    houtside ht hclockFacts.lower_clock hsmallPower hoffsetPower
    hclockPower haggregatePower
  have hy : 0 < y := by
    dsimp only [y, outerCoupledCenter]
    exact coupledOuterCenter_pos (by exact_mod_cast houtside)
      (by exact_mod_cast hclockFacts.current_pos)
  have hoffsetNonneg : 0 ≤ fineOuterInitialOffset outside t := by
    unfold fineOuterInitialOffset
    exact NNReal.coe_nonneg _
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg hoffsetNonneg (by positivity)
  have hw : 0 ≤ w := by
    dsimp only [w, outerCoupledWindow]
    unfold coupledOuterWindow
    exact div_nonneg hA (by positivity)
  have hb : 0 ≤ b := by
    dsimp only [b]
    unfold fineOuterBuffer fineOuterInitialOffset
    positivity
  have hcenterLower : centerLower ≤ y := by
    simpa only [A, centerLower, y] using hsandwich.2.2.1
  have hwindow : w ≤ windowUpper := by
    simpa only [A, windowUpper, w] using hsandwich.2.1
  have hsmall : 100 * windowUpper ≤ centerLower := by
    simpa only [windowUpper, centerLower] using hscalars.small
  have htReal : (1 : ℝ) ≤ t := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr ht.ne')
  have hoffsetLe : fineOuterInitialOffset outside t ≤ windowUpper := by
    dsimp only [windowUpper]
    have hpow : (1 : ℝ) ≤ (t : ℝ) ^ coupledOuterExponent :=
      one_le_pow₀ htReal
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow
      (show 0 ≤ fineOuterInitialOffset outside t by
        unfold fineOuterInitialOffset
        positivity)
  have hbOffset : b + 1 ≤ fineOuterInitialOffset outside t := by
    simpa only [b] using hscalars.round_buffer
  have hbOne : b + 1 ≤ windowUpper := hbOffset.trans hoffsetLe
  have hwindowTwo : 2 ≤ windowUpper := hscalars.round_two.trans hoffsetLe
  have hupperArg : 0 ≤ y + w + b := by positivity
  have hlowerOne : 1 ≤ y - w - b := by
    nlinarith
  have huCast : (u : ℝ) ≤
      (nonnegativeNatCeil (y + w + b) : ℕ) := by
    exact_mod_cast (show u ≤ nonnegativeNatCeil (y + w + b) by
      simpa only [u, b, y, w, outerCoupledUpperBarrier, A] using hschedules.1)
  have hdCast : (nonnegativeNatFloor (y - w - b) : ℕ) ≤
      (d : ℝ) := by
    exact_mod_cast (show nonnegativeNatFloor (y - w - b) ≤ d by
      simpa only [d, b, y, w, outerCoupledLowerBarrier, A] using hschedules.2.1)
  have huReal : (u : ℝ) < y + w + b + 1 :=
    huCast.trans_lt (nonnegativeNatCeil_lt_add_one hupperArg)
  have hdReal : y - w - b - 1 < (d : ℝ) :=
    (sub_one_lt_nonnegativeNatFloor hlowerOne).trans_le hdCast
  have hratioReal : (u : ℝ) + 2 ≤ 3 * d := by
    nlinarith
  have hsharpRatioReal : 4 * (u : ℝ) ≤ 5 * d := by
    nlinarith
  constructor
  · exact_mod_cast hratioReal
  · exact_mod_cast hsharpRatioReal

/-- Uniform schedule and availability bounds in the exact format consumed by
the recursive initial product law. -/
theorem fineOuterCanonical_uniform_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (lower₀ outside t K : ℕ)
    (houtside : 0 < outside) (ht : 0 < t)
    (hreservePos : 0 < fineOuterReserve outside t)
    (hreserveInitial : fineOuterReserve outside t ≤
      outerSharpEligiblePairs H X 0)
    (hpairUpper : 2 * (outerSharpEligiblePairs H X 0 : ℕ) ≤
      (outside : ℝ) ^ 2)
    (hsmallPower : 12800 ≤ t ^ 31)
    (hoffsetPower : t ^ fineOuterCorridorExponent ≤ 16 * outside)
    (hclockPower : 50 * t ^ 101 ≤ outside ^ 2)
    (haggregatePower : t ^ 102 * K ≤ 8 * outside ^ 2)
    (hinitialOrder : lower₀ ≤ outside)
    (hinitial :
      (outside : ℝ) ≤
          quadraticPairBarrier (outside : ℝ≥0)
            (fineOffsetUpperCoefficient t)
            (outerSharpEligiblePairs H X 0 : ℝ≥0) 3 0 +
              fineOuterInitialOffset outside t ∧
        quadraticPairBarrier (outside : ℝ≥0)
            (fineOffsetLowerCoefficient t)
            (outerSharpEligiblePairs H X 0 : ℝ≥0) 3 0 -
              fineOuterInitialOffset outside t ≤ (lower₀ : ℝ))
    (hfour : 4 ≤ fineOuterReserve outside t)
    (hdegreePos : 0 < fineOuterDegreeFloor outside t) :
    let fuel := outerSharpStopFuel H X (fineOuterReserve outside t)
    ∀ i, i ≤ fuel →
      fineOuterDegreeFloor outside t ≤
          outerSharpLowerSchedule H X
            (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) K i ∧
      outerSharpUpperSchedule H X
          (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) K i ≤
          fineOuterDegreeCeil outside ∧
      fineOuterAvailabilityFloor outside t ≤
          outerSharpLowerAvailability H X
            (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) K i ∧
      0 ≤ (outerSharpEnvelope H X
          (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) K i).2 -
            fineOuterBuffer outside t := by
  dsimp only
  intro i hi
  have hs := fineOuterCanonical_pointwise_schedule_bounds H X lower₀
    outside t K i houtside ht hreservePos hreserveInitial hpairUpper
    hsmallPower hoffsetPower hclockPower haggregatePower hinitialOrder
    hinitial hfour hi
  have hreserve := outerSharpEligiblePairs_stopFuel_floor H X
    hreserveInitial hi
  have havailability : fineOuterAvailabilityFloor outside t ≤
      outerSharpLowerAvailability H X
        (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) K i := by
    rw [fineOuterAvailabilityFloor, outerSharpLowerAvailability_eq]
    exact Nat.div_le_div_right (Nat.mul_le_mul hreserve hs.1)
  have hlowerPos : 0 < outerSharpLowerSchedule H X
      (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) K i :=
    hdegreePos.trans_le hs.1
  have henvelope :=
    sharpPairEnvelope_lower_sub_buffer_nonneg_of_lowerSchedule_pos
      (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) K
      (outerSharpLowerFormula H X) (outerSharpUpperFormula H X) i hlowerPos
  exact ⟨hs.1, hs.2, havailability, henvelope⟩

end

end Erdos207
