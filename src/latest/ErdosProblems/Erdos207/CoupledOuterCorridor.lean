/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CoupledOuterBarrierAlgebra
import ErdosProblems.Erdos207.OuterQuadraticSharpBarrier
import ErdosProblems.Erdos207.OuterSharpStopFuel

/-!
# A widening corridor for the recursive outer schedules

This file connects the real coupled-rate estimates to the natural-valued
recursive schedules.  The upper and lower barriers have a common quadratic
centre and an inverse-clock window.  Rounding, division by three, and the
aggregate two-away term are all charged to the same relative window `z`.
-/

namespace Erdos207

noncomputable section

/-- The four pointwise conclusions needed at one clock value of the ordered
barrier induction. -/
structure CoupledOuterEndpointFacts
    (E d u K : ℕ) (y z : ℝ) : Prop where
  upperAvailabilityPos : 0 < E * u / 3
  lowerGap : u < E * d / 3
  upperRate : (6 - 100 * z) * y / E ≤
    sharpScheduledPairUpperRate (E * u / 3) d u
  lowerRate : sharpScheduledPairLowerRate (E * d / 3) u K ≤
    (6 + 100 * z) * y / E

/-- Floor/ceiling endpoint bounds imply the two coupled rate estimates.

The hypotheses have been arranged so that later asymptotic arithmetic only
has to show six transparent scale inequalities: the relative window is at
most one percent, pays for rounding and the reciprocal clock, and dominates
the aggregate incidence cutoff. -/
theorem coupledOuterEndpointFacts
    {E d u K : ℕ} {y z buffer : ℝ}
    (hy : 0 < y) (hz : 0 ≤ z) (hzsmall : z ≤ 1 / 100)
    (hbuffer : 0 ≤ buffer)
    (hroundBuffer : buffer + 1 ≤ z * y)
    (hroundTwo : 2 ≤ z * y)
    (hlowerOne : 1 ≤ y - z * y - buffer)
    (hclockScale : 100 ≤ z * E)
    (hK : (K : ℝ) ≤ z * y ^ 2)
    (huBox : u ≤ nonnegativeNatCeil (y + z * y + buffer))
    (hdBox : nonnegativeNatFloor (y - z * y - buffer) ≤ d)
    (hdu : d ≤ u) :
    CoupledOuterEndpointFacts E d u K y z := by
  have hy0 : 0 ≤ y := hy.le
  have hzy0 : 0 ≤ z * y := mul_nonneg hz hy0
  have hupperArg : 0 ≤ y + z * y + buffer := by positivity
  have huCast : (u : ℝ) ≤
      (nonnegativeNatCeil (y + z * y + buffer) : ℕ) := by
    exact_mod_cast huBox
  have huReal : (u : ℝ) ≤ y * (1 + 2 * z) := by
    have hceil := nonnegativeNatCeil_lt_add_one hupperArg
    calc
      (u : ℝ) ≤
          (nonnegativeNatCeil (y + z * y + buffer) : ℕ) := huCast
      _ ≤ y + z * y + buffer + 1 := hceil.le
      _ ≤ y * (1 + 2 * z) := by nlinarith
  have hdCast : (nonnegativeNatFloor (y - z * y - buffer) : ℕ) ≤
      (d : ℝ) := by
    exact_mod_cast hdBox
  have hdReal : y * (1 - 2 * z) ≤ (d : ℝ) := by
    have hfloor := sub_one_lt_nonnegativeNatFloor hlowerOne
    nlinarith
  have hzySmall : 100 * (z * y) ≤ y := by
    nlinarith
  have hdPosReal : (0 : ℝ) < d := by
    have hfloor := sub_one_lt_nonnegativeNatFloor hlowerOne
    nlinarith
  have hdPos : 0 < d := by exact_mod_cast hdPosReal
  have huPos : 0 < u := hdPos.trans_le hdu
  have hElargeReal : (10000 : ℝ) ≤ E := by
    have hmul : z * (E : ℝ) ≤ (1 / 100) * E := by
      gcongr
    nlinarith
  have hElarge : 10000 ≤ E := by exact_mod_cast hElargeReal
  have hEpos : 0 < E := by omega
  have hsubReal : (u : ℝ) + 2 ≤ 3 * d := by
    nlinarith [hzySmall, hroundTwo]
  have hsub : u + 2 ≤ 3 * d := by exact_mod_cast hsubReal
  have hMpos : 0 < E * u / 3 := by
    apply Nat.div_pos
    · have hEu : 3 ≤ E * u := by
        have hEthree : 3 ≤ E := by omega
        calc
          3 = 3 * 1 := by omega
          _ ≤ E * u := Nat.mul_le_mul hEthree (Nat.one_le_iff_ne_zero.mpr huPos.ne')
      omega
    · norm_num
  let D := E * d / 3
  have hgap : u < D := by
    have hnine : 9 ≤ E := by omega
    have hthreeD : 3 * d ≤ D := by
      apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).2
      calc
        3 * d * 3 = 9 * d := by ring
        _ ≤ E * d := Nat.mul_le_mul_right d hnine
    omega
  have hleft : (2 : ℝ) + 3 * u ≤ y * (3 + 7 * z) := by
    nlinarith [hroundBuffer]
  have hone : 0 ≤ 1 - 2 * z := by nlinarith
  have hrightCoefficient : y * (3 + 7 * z) ≤
      100 * y * (1 - 2 * z) := by
    nlinarith
  have hclockScaled : (100 : ℝ) ≤ z * (E : ℝ) := by
    simpa only [Nat.cast_ofNat, Nat.cast_mul] using hclockScale
  have hrightClock : 100 * y * (1 - 2 * z) ≤
      (z * E) * (y * (1 - 2 * z)) := by
    have hfactor : 0 ≤ y * (1 - 2 * z) := mul_nonneg hy0 hone
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right hclockScaled hfactor
  have hrightDegree : (z * E) * (y * (1 - 2 * z)) ≤
      z * E * d := by
    have hzE : 0 ≤ z * (E : ℝ) := mul_nonneg hz (by positivity)
    exact mul_le_mul_of_nonneg_left hdReal hzE
  have hdenRound : (2 : ℝ) + 3 * u ≤ z * E * d :=
    hleft.trans (hrightCoefficient.trans (hrightClock.trans hrightDegree))
  have hdivNat : E * d ≤ 3 * D + 2 := by
    dsimp only [D]
    omega
  have hdivReal : (E : ℝ) * d ≤ 3 * D + 2 := by
    exact_mod_cast hdivNat
  have hdenom : (1 - z) * E * d ≤ 3 * (D - u : ℕ) := by
    rw [Nat.cast_sub hgap.le]
    push_cast
    nlinarith
  have hupper := sharpScheduledPairUpperRate_ge_coupled
    (E := E) (d := d) (u := u) (y := y) (z := z)
    hEpos hMpos hy0 hz hzsmall hdReal huReal
    hroundTwo hsub
  have hlower := sharpScheduledPairLowerRate_le_coupled
    (E := E) (D := D) (d := d) (u := u) (K := K)
    hEpos hgap hy hz hzsmall hdenom hdReal huReal hK
  exact ⟨hMpos, hgap, hupper, by simpa only [D] using hlower⟩

/-- The central trajectory evaluated on the exact outer eligible-pair
clock. -/
def outerCoupledCenter
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (outside i : ℕ) : ℝ :=
  coupledOuterCenter outside (outerSharpEligiblePairs H X i)

/-- The widening window evaluated on the exact outer eligible-pair clock. -/
def outerCoupledWindow
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (A : ℝ) (k i : ℕ) : ℝ :=
  coupledOuterWindow A k (outerSharpEligiblePairs H X i)

def outerCoupledUpperBarrier
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (outside : ℕ)
    (A : ℝ) (k i : ℕ) : ℝ :=
  outerCoupledCenter H X outside i + outerCoupledWindow H X A k i

def outerCoupledLowerBarrier
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (outside : ℕ)
    (A : ℝ) (k i : ℕ) : ℝ :=
  outerCoupledCenter H X outside i - outerCoupledWindow H X A k i

/-- Pointwise scale data for a widening coupled corridor. -/
structure CoupledOuterScaleFacts
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (outside K : ℕ)
    (A : ℝ) (k i : ℕ) (buffer z : ℝ) : Prop where
  z_nonneg : 0 ≤ z
  z_small : z ≤ 1 / 100
  window_eq : outerCoupledWindow H X A k i =
    z * outerCoupledCenter H X outside i
  round_buffer : buffer + 1 ≤ outerCoupledWindow H X A k i
  round_two : 2 ≤ outerCoupledWindow H X A k i
  lower_one : 1 ≤ outerCoupledLowerBarrier H X outside A k i - buffer
  clock_scale : 100 ≤ z * outerSharpEligiblePairs H X i
  aggregate : (K : ℝ) ≤ z * outerCoupledCenter H X outside i ^ 2

lemma outerSharpEligiblePairs_succ_eq_sub_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) {i : ℕ}
    (hi : 3 * (i + 1) ≤ outerSharpEligiblePairs H X 0) :
    outerSharpEligiblePairs H X (i + 1) =
      outerSharpEligiblePairs H X i - 3 := by
  have hi' : 3 * i ≤ outerSharpEligiblePairs H X 0 := by omega
  rw [outerSharpEligiblePairs_eq_zero_sub H X hi,
    outerSharpEligiblePairs_eq_zero_sub H X hi']
  omega

/-- The ordered recursive schedules are trapped by the widening barriers.
This is the corrected replacement for an independent constant-offset
corridor: the same inverse-clock window controls both coupled trajectories. -/
theorem outerSharpRecursiveSchedules_between_coupledBarriers
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (upper₀ lower₀ outside K fuel k : ℕ) (buffer A : ℝ)
    (z : ℕ → ℝ)
    (houtside : 0 < outside)
    (hA : 0 ≤ A) (hk : 200 ≤ 3 * k)
    (hbuffer : 0 ≤ buffer) (hinitialOrder : lower₀ ≤ upper₀)
    (hupperInitial : (upper₀ : ℝ) ≤
      outerCoupledUpperBarrier H X outside A k 0)
    (hlowerInitial : outerCoupledLowerBarrier H X outside A k 0 ≤
      (lower₀ : ℝ))
    (hclock : 3 * (fuel + 1) < outerSharpEligiblePairs H X 0)
    (hscale : ∀ i, i < fuel →
      CoupledOuterScaleFacts H X outside K A k i buffer (z i)) :
    ∀ i, i ≤ fuel →
      outerSharpUpperSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer K i ≤
        nonnegativeNatCeil
          (outerCoupledUpperBarrier H X outside A k i + buffer) ∧
      nonnegativeNatFloor
          (outerCoupledLowerBarrier H X outside A k i - buffer) ≤
        outerSharpLowerSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer K i ∧
      outerSharpLowerSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer K i ≤
        outerSharpUpperSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer K i := by
  let upperBarrier : ℕ → ℝ := outerCoupledUpperBarrier H X outside A k
  let lowerBarrier : ℕ → ℝ := outerCoupledLowerBarrier H X outside A k
  have hstepFacts : ∀ i, i < fuel →
      outerSharpUpperSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer K i ≤
        nonnegativeNatCeil (upperBarrier i + buffer) →
      nonnegativeNatFloor (lowerBarrier i - buffer) ≤
        outerSharpLowerSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer K i →
      outerSharpLowerSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer K i ≤
        outerSharpUpperSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer K i →
      CoupledOuterEndpointFacts
        (outerSharpEligiblePairs H X i)
        (outerSharpLowerSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer K i)
        (outerSharpUpperSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer K i)
        K (outerCoupledCenter H X outside i) (z i) := by
    intro i hi hu hd hdu
    have hs := hscale i hi
    have hy : 0 < outerCoupledCenter H X outside i := by
      apply coupledOuterCenter_pos
      · exact_mod_cast houtside
      · have hiClock : 3 * i ≤ outerSharpEligiblePairs H X 0 := by omega
        change 0 < (outerSharpEligiblePairs H X i : ℝ)
        rw [outerSharpEligiblePairs_eq_zero_sub H X hiClock]
        exact_mod_cast (show 0 < outerSharpEligiblePairs H X 0 - 3 * i by omega)
    apply coupledOuterEndpointFacts hy hs.z_nonneg hs.z_small hbuffer
    · simpa only [hs.window_eq] using hs.round_buffer
    · simpa only [hs.window_eq] using hs.round_two
    · simpa only [lowerBarrier, outerCoupledLowerBarrier,
        hs.window_eq] using hs.lower_one
    · exact hs.clock_scale
    · exact hs.aggregate
    · simpa only [upperBarrier, outerCoupledUpperBarrier,
        hs.window_eq] using hu
    · simpa only [lowerBarrier, outerCoupledLowerBarrier,
        hs.window_eq] using hd
    · exact hdu
  have hbarrierStep : ∀ i, i < fuel →
      outerSharpUpperSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer K i ≤
        nonnegativeNatCeil (upperBarrier i + buffer) →
      nonnegativeNatFloor (lowerBarrier i - buffer) ≤
        outerSharpLowerSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer K i →
      outerSharpLowerSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer K i ≤
        outerSharpUpperSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer K i →
      upperBarrier i - upperBarrier (i + 1) ≤
          sharpScheduledPairUpperRate
            (outerSharpUpperAvailability H X
              (upper₀ : ℝ) (lower₀ : ℝ) buffer K i)
            (outerSharpLowerSchedule H X
              (upper₀ : ℝ) (lower₀ : ℝ) buffer K i)
            (outerSharpUpperSchedule H X
              (upper₀ : ℝ) (lower₀ : ℝ) buffer K i) ∧
        sharpScheduledPairLowerRate
            (outerSharpLowerAvailability H X
              (upper₀ : ℝ) (lower₀ : ℝ) buffer K i)
            (outerSharpUpperSchedule H X
              (upper₀ : ℝ) (lower₀ : ℝ) buffer K i) K ≤
          lowerBarrier i - lowerBarrier (i + 1) := by
    intro i hi hu hd hdu
    let E : ℕ := outerSharpEligiblePairs H X i
    let y : ℝ := outerCoupledCenter H X outside i
    let w : ℝ := outerCoupledWindow H X A k i
    let y' : ℝ := outerCoupledCenter H X outside (i + 1)
    let w' : ℝ := outerCoupledWindow H X A k (i + 1)
    have hiClock : 3 * (i + 1) ≤ outerSharpEligiblePairs H X 0 := by omega
    have hEsuccNat := outerSharpEligiblePairs_succ_eq_sub_three H X hiClock
    have hEthree : 3 ≤ E := by
      dsimp only [E]
      rw [outerSharpEligiblePairs_eq_zero_sub H X (by omega)]
      omega
    have hEsucc : (outerSharpEligiblePairs H X (i + 1) : ℝ) = E - 3 := by
      rw [hEsuccNat, Nat.cast_sub hEthree]
      norm_num
    have hEgt : (3 : ℝ) < E := by
      dsimp only [E]
      rw [outerSharpEligiblePairs_eq_zero_sub H X (by omega)]
      push_cast
      exact_mod_cast (show 3 < outerSharpEligiblePairs H X 0 - 3 * i by omega)
    have hEpos : (0 : ℝ) < E := by linarith
    have hypos : 0 < y := by
      dsimp only [y, outerCoupledCenter]
      exact coupledOuterCenter_pos (by exact_mod_cast houtside) hEpos
    have hs := hscale i hi
    have hwy : w = z i * y := by
      simpa only [w, y] using hs.window_eq
    have hinv : (E : ℝ)⁻¹ ≤ z i := by
      rw [inv_eq_one_div]
      apply (div_le_iff₀ hEpos).2
      have hc : (100 : ℝ) ≤ z i * E := by
        simpa only [E] using hs.clock_scale
      nlinarith
    have hySucc : y' = coupledOuterCenter outside (E - 3) := by
      dsimp only [y', outerCoupledCenter, E]
      rw [hEsucc]
    have hwSucc : w' = coupledOuterWindow A k (E - 3) := by
      dsimp only [w', outerCoupledWindow, E]
      rw [hEsucc]
    have hcenterUpper : y - y' ≤ 6 * y / E := by
      rw [hySucc]
      exact coupledOuterCenter_decrement_le
        (by exact_mod_cast houtside) hEpos
    have hcenterLower : (6 - 10 * z i) * y / E ≤ y - y' := by
      rw [hySucc]
      exact coupledOuterCenter_decrement_ge
        (by exact_mod_cast houtside) hEpos hs.z_nonneg hinv
    have hwiden : 200 * z i * y / E ≤ w' - w := by
      rw [hwSucc]
      exact coupledOuterWindow_growth_two_hundred hA hEgt hwy hk
    have hfacts := hstepFacts i hi hu hd hdu
    have hstep := coupledOuter_barrier_step hEpos hypos.le hs.z_nonneg
      hcenterUpper hcenterLower hwiden hfacts.upperRate hfacts.lowerRate
    constructor
    · simpa only [upperBarrier, outerCoupledUpperBarrier, y, y', w, w',
        outerSharpUpperAvailability_eq, outerSharpEligiblePairs]
        using hstep.1
    · simpa only [lowerBarrier, outerCoupledLowerBarrier, y, y', w, w',
        outerSharpLowerAvailability_eq, outerSharpEligiblePairs]
        using hstep.2
  apply sharpRecursiveSchedules_between_barriers_until_of_box_ordered
    (upper₀ : ℝ) (lower₀ : ℝ) buffer K fuel
    (outerSharpLowerFormula H X) (outerSharpUpperFormula H X)
    upperBarrier lowerBarrier hbuffer (by exact_mod_cast hinitialOrder)
    (by simpa only [upperBarrier] using hupperInitial)
    (by simpa only [lowerBarrier] using hlowerInitial)
  · intro i hi hu hd hdu
    exact (hbarrierStep i hi hu hd hdu).1
  · intro i hi hu hd hdu
    exact (hbarrierStep i hi hu hd hdu).2
  · intro i hi hu hd hdu
    have hfacts := hstepFacts i hi hu hd hdu
    apply outerSharpScheduledPairUpperRate_le_lowerRate H X
      (upper₀ : ℝ) (lower₀ : ℝ) buffer K i
    · rw [outerSharpUpperAvailability_eq]
      exact hfacts.upperAvailabilityPos
    · rw [outerSharpLowerAvailability_eq]
      exact hfacts.lowerGap
    · exact hdu

end

end Erdos207
