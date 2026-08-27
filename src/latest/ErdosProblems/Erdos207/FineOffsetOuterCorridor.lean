/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FineOffsetOuterRateAlgebra

/-!
# The fine exact-clock outer corridor

This file discharges every endpoint and rate hypothesis of the generic
constant-offset comparison theorem.  Only transparent scale conditions
remain at each time.  The common calculations are collected in a single
endpoint certificate so that the recursive comparison does not duplicate
the coercion and rounding argument eight times.
-/

namespace Erdos207

open scoped NNReal

noncomputable section

/-- The eight pointwise hypotheses needed by the constant-offset recursive
barrier theorem, specialized to the fine coefficients and slopes. -/
structure FineOffsetOuterEndpointFacts
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (outside t Kinc i : ℕ) (buffer : ℝ) : Prop where
  lowerPos : 0 < offsetQuadraticLower (outside : ℝ≥0)
    (fineOffsetLowerCoefficient t)
    (outerSharpEligiblePairs H X 0 : ℝ≥0) 3
    (fineOuterInitialOffset outside t) buffer i
  upperAvailability : 3 ≤ outerSharpEligiblePairs H X i *
    offsetQuadraticLower (outside : ℝ≥0)
      (fineOffsetLowerCoefficient t)
      (outerSharpEligiblePairs H X 0 : ℝ≥0) 3
      (fineOuterInitialOffset outside t) buffer i
  upperLoss : 2 * offsetQuadraticUpper (outside : ℝ≥0)
      (fineOffsetUpperCoefficient t)
      (outerSharpEligiblePairs H X 0 : ℝ≥0) 3
      (fineOuterInitialOffset outside t) buffer i ≤
    3 * offsetQuadraticLower (outside : ℝ≥0)
      (fineOffsetLowerCoefficient t)
      (outerSharpEligiblePairs H X 0 : ℝ≥0) 3
      (fineOuterInitialOffset outside t) buffer i - 2 -
        offsetQuadraticUpper (outside : ℝ≥0)
          (fineOffsetUpperCoefficient t)
          (outerSharpEligiblePairs H X 0 : ℝ≥0) 3
          (fineOuterInitialOffset outside t) buffer i
  upperRate :
    ((fineOffsetUpperCoefficient t * 3 *
        (2 * affineSurvivalEnvelope
          (outerSharpEligiblePairs H X 0 : ℝ≥0) 3 i - 3) *
        (outside : ℝ≥0)⁻¹ ^ 3 : ℝ≥0) : ℝ) ≤
      ((6 * offsetQuadraticLower (outside : ℝ≥0)
        (fineOffsetLowerCoefficient t)
        (outerSharpEligiblePairs H X 0 : ℝ≥0) 3
        (fineOuterInitialOffset outside t) buffer i : ℕ) : ℝ) /
          outerSharpEligiblePairs H X i
  eligiblePos : 0 < outerSharpEligiblePairs H X i
  lowerGap : offsetQuadraticUpper (outside : ℝ≥0)
      (fineOffsetUpperCoefficient t)
      (outerSharpEligiblePairs H X 0 : ℝ≥0) 3
      (fineOuterInitialOffset outside t) buffer i <
    outerSharpEligiblePairs H X i *
      offsetQuadraticLower (outside : ℝ≥0)
        (fineOffsetLowerCoefficient t)
        (outerSharpEligiblePairs H X 0 : ℝ≥0) 3
        (fineOuterInitialOffset outside t) buffer i / 3
  lowerScalar : outerSharpEligiblePairs H X i *
      (offsetQuadraticUpper (outside : ℝ≥0)
          (fineOffsetUpperCoefficient t)
          (outerSharpEligiblePairs H X 0 : ℝ≥0) 3
          (fineOuterInitialOffset outside t) buffer i *
        (2 * offsetQuadraticUpper (outside : ℝ≥0)
          (fineOffsetUpperCoefficient t)
          (outerSharpEligiblePairs H X 0 : ℝ≥0) 3
          (fineOuterInitialOffset outside t) buffer i) + Kinc) ≤
    6 * offsetQuadraticLower (outside : ℝ≥0)
      (fineOffsetLowerCoefficient t)
      (outerSharpEligiblePairs H X 0 : ℝ≥0) 3
      (fineOuterInitialOffset outside t) buffer i *
        (outerSharpEligiblePairs H X i *
          offsetQuadraticLower (outside : ℝ≥0)
            (fineOffsetLowerCoefficient t)
            (outerSharpEligiblePairs H X 0 : ℝ≥0) 3
            (fineOuterInitialOffset outside t) buffer i / 3 -
          offsetQuadraticUpper (outside : ℝ≥0)
            (fineOffsetUpperCoefficient t)
            (outerSharpEligiblePairs H X 0 : ℝ≥0) 3
            (fineOuterInitialOffset outside t) buffer i)
  lowerRate :
    ((6 * offsetQuadraticUpper (outside : ℝ≥0)
      (fineOffsetUpperCoefficient t)
      (outerSharpEligiblePairs H X 0 : ℝ≥0) 3
      (fineOuterInitialOffset outside t) buffer i : ℕ) : ℝ) /
        outerSharpEligiblePairs H X i ≤
      ((fineOffsetLowerCoefficient t * 3 *
        (2 * affineSurvivalEnvelope
          (outerSharpEligiblePairs H X 0 : ℝ≥0) 3 i - 3) *
        (outside : ℝ≥0)⁻¹ ^ 3 : ℝ≥0) : ℝ)

/-- All pointwise corridor obligations follow from the five scale
inequalities. -/
theorem fineOffsetOuterEndpointFacts
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (outside t Kinc i : ℕ) (buffer : ℝ)
    (hsmall : ((fineOuterCorridorError t : ℝ≥0) : ℝ) ≤ 1 / 100)
    (hbuffer : 0 ≤ buffer)
    (hclocki : 3 * i ≤ outerSharpEligiblePairs H X 0)
    (hscale :
      let E : ℝ := outerSharpEligiblePairs H X i
      let x : ℝ := ((outerSharpEligiblePairs H X i : ℕ) : ℝ≥0) ^ 2 *
        (outside : ℝ≥0)⁻¹ ^ 3
      let s : ℝ := fineOuterInitialOffset outside t + buffer + 1
      1 ≤ x ∧ 4 * s ≤ (fineOuterCorridorError t : ℝ≥0) * x ∧
        2 ≤ (fineOuterCorridorError t : ℝ≥0) * x ∧
        100 ≤ (fineOuterCorridorError t : ℝ≥0) * E ∧
        (Kinc : ℝ) ≤ (fineOuterCorridorError t : ℝ≥0) * x ^ 2) :
    FineOffsetOuterEndpointFacts H X outside t Kinc i buffer := by
  let epsilon : ℝ := fineOuterCorridorError t
  let N : ℝ≥0 := outside
  let R0 : ℝ≥0 := outerSharpEligiblePairs H X 0
  let offset : ℝ := fineOuterInitialOffset outside t
  let E : ℕ := outerSharpEligiblePairs H X i
  let x : ℝ := ((E : ℕ) : ℝ≥0) ^ 2 * N⁻¹ ^ 3
  let s : ℝ := offset + buffer + 1
  let U : ℕ := offsetQuadraticUpper N (fineOffsetUpperCoefficient t) R0 3
    offset buffer i
  let L : ℕ := offsetQuadraticLower N (fineOffsetLowerCoefficient t) R0 3
    offset buffer i
  let D : ℕ := E * L / 3
  have hepsilon : 0 ≤ epsilon := by positivity
  have hepsilonOne : epsilon ≤ 1 := by
    dsimp only [epsilon]
    linarith
  have hepsilonFourNN : fineOuterCorridorError t ≤ (4 : ℝ≥0) := by
    rw [← NNReal.coe_le_coe]
    change epsilon ≤ 4
    linarith
  have hoffset : 0 ≤ offset := by
    dsimp only [offset, fineOuterInitialOffset]
    positivity
  have hs : 1 ≤ x ∧ 4 * s ≤ epsilon * x ∧
      2 ≤ epsilon * x ∧ 100 ≤ epsilon * (E : ℝ) ∧
      (Kinc : ℝ) ≤ epsilon * x ^ 2 := by
    simpa only [epsilon, N, offset, E, x, s] using hscale
  have hlowerExact :
      ((fineOffsetLowerCoefficient t * (E : ℝ≥0) ^ 2 *
        N⁻¹ ^ 3 : ℝ≥0) : ℝ) = (4 + epsilon) * x := by
    rw [fineOffsetLower_liveQuadratic_eq]
    simp only [NNReal.coe_mul, NNReal.coe_pow]
    rfl
  have hupperExact :
      ((fineOffsetUpperCoefficient t * (E : ℝ≥0) ^ 2 *
        N⁻¹ ^ 3 : ℝ≥0) : ℝ) = (4 - epsilon) * x := by
    rw [fineOffsetUpper_liveQuadratic_eq hepsilonFourNN]
    simp only [NNReal.coe_mul, NNReal.coe_pow]
    rfl
  have hlowerOne : 1 ≤ quadraticPairBarrier N
      (fineOffsetLowerCoefficient t) R0 3 i - offset - buffer := by
    rw [exactClockQuadraticPairBarrier_eq H X N
      (fineOffsetLowerCoefficient t) i hclocki]
    rw [hlowerExact]
    nlinarith [hs.1, hs.2.1]
  have hLpos : 0 < L := by
    dsimp only [L]
    exact offsetQuadraticLower_pos_of_one hlowerOne
  have hr := offsetQuadratic_rounded_exactClock_bounds H X N
    (fineOffsetUpperCoefficient t) (fineOffsetLowerCoefficient t)
    offset buffer i hclocki (add_nonneg hoffset hbuffer) hlowerOne
  have hU : (U : ℝ) ≤ (4 - epsilon) * x + s := by
    have h := hr.1.le
    rw [hupperExact] at h
    dsimp only [U, s, R0]
    linarith
  have hL : (4 + epsilon) * x - s ≤ (L : ℝ) := by
    have h := hr.2.le
    rw [hlowerExact] at h
    dsimp only [L, s, R0]
    linarith
  have hLupper : (L : ℝ) ≤ (4 + epsilon) * x := by
    have hfloor : (nonnegativeNatFloor
        (quadraticPairBarrier N (fineOffsetLowerCoefficient t) R0 3 i -
          offset - buffer) : ℝ) ≤
        quadraticPairBarrier N (fineOffsetLowerCoefficient t) R0 3 i -
          offset - buffer := by
      unfold nonnegativeNatFloor
      rw [max_eq_right (zero_le_one.trans hlowerOne)]
      exact Nat.floor_le (zero_le_one.trans hlowerOne)
    have hbar : quadraticPairBarrier N (fineOffsetLowerCoefficient t) R0 3 i =
        (4 + epsilon) * x := by
      rw [exactClockQuadraticPairBarrier_eq H X N
        (fineOffsetLowerCoefficient t) i hclocki]
      exact hlowerExact
    rw [hbar] at hfloor
    dsimp only [L, offsetQuadraticLower]
    rw [hbar]
    linarith
  have hbands := fineOffset_endpoint_bands hepsilon hepsilonOne
    (show 0 ≤ x by positivity) (show 0 ≤ s by
      dsimp only [s, offset]
      positivity) hs.2.1 hU hL hLupper
  have hgapReal : (U : ℝ) < (L : ℝ) := by
    nlinarith [hs.2.2.1]
  have hgapNat : U < L := by exact_mod_cast hgapReal
  have hE6 : 6 ≤ E := by
    have h : (6 : ℝ) ≤ E := by nlinarith [hs.2.2.2.1]
    exact_mod_cast h
  have hEpos : 0 < E := by omega
  have htwoL : 2 * L ≤ D := by
    dsimp only [D]
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).2
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      Nat.mul_le_mul_right L hE6
  have hUD : U ≤ D := by
    have hLtwoL : L ≤ 2 * L := by omega
    exact hgapNat.le.trans (hLtwoL.trans htwoL)
  have hLD : L ≤ D := by
    have hLtwoL : L ≤ 2 * L := by omega
    exact hLtwoL.trans htwoL
  have hdivNat : E * L ≤ 3 * D + 2 := by
    dsimp only [D]
    omega
  have hupperRate :
      ((fineOffsetUpperCoefficient t * 3 *
          (2 * affineSurvivalEnvelope R0 3 i - 3) * N⁻¹ ^ 3 : ℝ≥0) : ℝ) ≤
        ((6 * L : ℕ) : ℝ) / E := by
    rw [exactOuterEnvelope_eq_eligiblePairs H X i hclocki]
    have hthree : (3 : ℝ≥0) ≤ 2 * (E : ℝ≥0) := by
      exact_mod_cast (show 3 ≤ 2 * E by omega)
    have hderivative :
        ((fineOffsetUpperCoefficient t * 3 *
          (2 * (E : ℝ≥0) - 3) * N⁻¹ ^ 3 : ℝ≥0) : ℝ) =
          3 * (4 - epsilon) * (2 * (E : ℝ) - 3) *
            ((N⁻¹ ^ 3 : ℝ≥0) : ℝ) := by
      simp only [NNReal.coe_mul, NNReal.coe_ofNat,
        NNReal.coe_sub hthree, NNReal.coe_pow,
        NNReal.coe_natCast, fineOffsetUpperCoefficient_coe hepsilonFourNN,
        epsilon]
      ring_nf
    rw [hderivative]
    rw [le_div_iff₀ (by exact_mod_cast hEpos : (0 : ℝ) < E)]
    apply (mul_le_mul_iff_of_pos_left
      (by exact_mod_cast hEpos : (0 : ℝ) < E)).mp
    have halg := fineOffset_upper_rate_crossmul hepsilon
      (by linarith : epsilon ≤ 4) (show 0 ≤ x by positivity)
      (show (0 : ℝ) ≤ E by positivity) hbands.2.1
    dsimp only [x] at halg
    simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast] at halg ⊢
    convert halg using 1
    · rfl
    · ring
    · norm_num
      ring
  have hlowerRate :
      ((6 * U : ℕ) : ℝ) / E ≤
        ((fineOffsetLowerCoefficient t * 3 *
          (2 * affineSurvivalEnvelope R0 3 i - 3) * N⁻¹ ^ 3 : ℝ≥0) : ℝ) := by
    rw [exactOuterEnvelope_eq_eligiblePairs H X i hclocki]
    have hthree : (3 : ℝ≥0) ≤ 2 * (E : ℝ≥0) := by
      exact_mod_cast (show 3 ≤ 2 * E by omega)
    have hderivative :
        ((fineOffsetLowerCoefficient t * 3 *
          (2 * (E : ℝ≥0) - 3) * N⁻¹ ^ 3 : ℝ≥0) : ℝ) =
          3 * (4 + epsilon) * (2 * (E : ℝ) - 3) *
            ((N⁻¹ ^ 3 : ℝ≥0) : ℝ) := by
      simp only [fineOffsetLowerCoefficient, NNReal.coe_mul,
        NNReal.coe_add, NNReal.coe_ofNat, NNReal.coe_sub hthree,
        NNReal.coe_pow, NNReal.coe_natCast, epsilon]
      ring_nf
    rw [hderivative]
    rw [div_le_iff₀ (by exact_mod_cast hEpos : (0 : ℝ) < E)]
    apply (mul_le_mul_iff_of_pos_left
      (by exact_mod_cast hEpos : (0 : ℝ) < E)).mp
    have halg := fineOffset_lower_rate_crossmul hepsilon hepsilonOne
      (show 0 ≤ x by positivity) (show (0 : ℝ) ≤ E by positivity)
      (show (0 : ℝ) ≤ U by positivity) hbands.1 hs.2.2.2.1
    dsimp only [x] at halg
    simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast] at halg ⊢
    convert halg using 1
    · rfl
    · norm_num
      ring
    · ring
  have hlowerScalar : E * (U * (2 * U) + Kinc) ≤
      6 * L * (D - U) := by
    have hdivReal : (E : ℝ) * (L : ℝ) ≤ 3 * (D : ℝ) + 2 := by
      exact_mod_cast hdivNat
    have hUDReal : (U : ℝ) ≤ (D : ℝ) := by exact_mod_cast hUD
    have halg := fineOffset_lower_scalar_crossmul hepsilon hs.1
      (show (0 : ℝ) ≤ E by positivity) (show (0 : ℝ) ≤ U by positivity)
      (show (0 : ℝ) ≤ L by positivity) (show (0 : ℝ) ≤ Kinc by positivity)
      hbands.1 hbands.2.1 hbands.2.2.1 hbands.2.2.2
      hs.2.2.2.1 hs.2.2.2.2
      hdivReal hUDReal
    exact_mod_cast halg
  constructor
  · simpa only [N, R0, offset, L] using hLpos
  · change 3 ≤ E * L
    omega
  · change 2 * U ≤ 3 * L - 2 - U
    omega
  · simpa only [N, R0, offset, L] using hupperRate
  · simpa only [E] using hEpos
  · simpa only [N, R0, offset, E, U, L, D] using hgapNat.trans_le hLD
  · simpa only [N, R0, offset, E, U, L, D] using hlowerScalar
  · simpa only [N, R0, offset, E, U] using hlowerRate

/-- The exact recursive outer schedules remain between the fine
constant-offset quadratic barriers. -/
theorem outerSharpRecursiveSchedules_between_fineOffsetBarriers
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (upper₀ lower₀ outside t Kinc fuel : ℕ) (buffer : ℝ)
    (houtside : 0 < outside)
    (hsmall : ((fineOuterCorridorError t : ℝ≥0) : ℝ) ≤ 1 / 100)
    (hbuffer : 0 ≤ buffer)
    (hinitialOrder : lower₀ ≤ upper₀)
    (hupperInitial : (upper₀ : ℝ) ≤
      quadraticPairBarrier (outside : ℝ≥0)
        (fineOffsetUpperCoefficient t)
        (outerSharpEligiblePairs H X 0 : ℝ≥0) 3 0 +
          fineOuterInitialOffset outside t)
    (hlowerInitial :
      quadraticPairBarrier (outside : ℝ≥0)
        (fineOffsetLowerCoefficient t)
        (outerSharpEligiblePairs H X 0 : ℝ≥0) 3 0 -
          fineOuterInitialOffset outside t ≤ (lower₀ : ℝ))
    (hclock : 3 * fuel < outerSharpEligiblePairs H X 0)
    (hscale : ∀ i, i < fuel →
      let E : ℝ := outerSharpEligiblePairs H X i
      let x : ℝ := ((outerSharpEligiblePairs H X i : ℕ) : ℝ≥0) ^ 2 *
        (outside : ℝ≥0)⁻¹ ^ 3
      let s : ℝ := fineOuterInitialOffset outside t + buffer + 1
      1 ≤ x ∧ 4 * s ≤ (fineOuterCorridorError t : ℝ≥0) * x ∧
        2 ≤ (fineOuterCorridorError t : ℝ≥0) * x ∧
        100 ≤ (fineOuterCorridorError t : ℝ≥0) * E ∧
        (Kinc : ℝ) ≤ (fineOuterCorridorError t : ℝ≥0) * x ^ 2) :
    ∀ i, i ≤ fuel →
      outerSharpUpperSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ≤
        offsetQuadraticUpper (outside : ℝ≥0)
          (fineOffsetUpperCoefficient t)
          (outerSharpEligiblePairs H X 0 : ℝ≥0) 3
          (fineOuterInitialOffset outside t) buffer i ∧
      offsetQuadraticLower (outside : ℝ≥0)
          (fineOffsetLowerCoefficient t)
          (outerSharpEligiblePairs H X 0 : ℝ≥0) 3
          (fineOuterInitialOffset outside t) buffer i ≤
        outerSharpLowerSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ∧
      outerSharpLowerSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i ≤
        outerSharpUpperSchedule H X
          (upper₀ : ℝ) (lower₀ : ℝ) buffer Kinc i := by
  have hclockNN : (fuel : ℝ≥0) * 3 <
      (outerSharpEligiblePairs H X 0 : ℝ≥0) := by
    exact_mod_cast (show fuel * 3 < outerSharpEligiblePairs H X 0 by omega)
  have hfacts : ∀ i, i < fuel →
      FineOffsetOuterEndpointFacts H X outside t Kinc i buffer := by
    intro i hi
    exact fineOffsetOuterEndpointFacts H X outside t Kinc i buffer
      hsmall hbuffer (by omega) (hscale i hi)
  apply outerSharpRecursiveSchedules_between_offsetQuadraticBarriers
    H X upper₀ lower₀ (fineOuterInitialOffset outside t) buffer Kinc fuel
      (outside : ℝ≥0) (fineOffsetUpperCoefficient t)
      (fineOffsetLowerCoefficient t)
      (outerSharpEligiblePairs H X 0 : ℝ≥0) 3 3 2 1 6 1
      hbuffer hinitialOrder hupperInitial hlowerInitial hclockNN hclockNN
      (by norm_num) (by norm_num)
  · intro i hi
    exact (hfacts i hi).lowerPos
  · intro i hi
    exact (hfacts i hi).upperAvailability
  · intro i hi
    simpa only [one_mul] using (hfacts i hi).upperLoss
  · intro i hi
    simpa only [Nat.mul_one, one_mul, Nat.one_mul, Nat.mul_assoc,
      show 3 * 2 = 6 by norm_num] using
      (hfacts i hi).upperRate
  · intro i hi
    exact (hfacts i hi).eligiblePos
  · intro i hi
    exact (hfacts i hi).lowerGap
  · intro i hi
    simpa only [Nat.one_mul] using (hfacts i hi).lowerScalar
  · intro i hi
    simpa only [Nat.one_mul] using (hfacts i hi).lowerRate

end

end Erdos207
