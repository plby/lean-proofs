/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FineOuterCanonicalCertificates
import ErdosProblems.Erdos207.OuterOnlyVertexStarRate
import ErdosProblems.Erdos207.OuterSharpClockHarmonic

/-!
# Vertex-star drift supplied by a canonical outer corridor

The coupled degree corridor keeps the upper schedule within three times the
lower schedule.  Since the upper availability is the floor of `E*u/3`, the
selection rate of any vertex whose residual degree is at least `R` dominates
`R/(2E)`.  Summing over the exact clock gives a logarithmic drift budget.
-/

namespace Erdos207

open Finset
open scoped BigOperators

noncomputable section

def fineOuterCanonicalVertexRate
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (lower₀ outside t Kinc R : ℕ) : ℕ → ℝ :=
  outerOnlyVertexSelectionRate R
    (outerSharpLowerSchedule H X
      (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) Kinc)
    (outerSharpUpperAvailability H X
      (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) Kinc)

/-- Pointwise reciprocal-clock lower bound for the canonical vertex rate. -/
theorem fineOuterCanonicalVertexRate_reciprocal_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (lower₀ outside t Kinc K Kpair Kglobal R i : ℕ)
    (hc : FineOuterCanonicalCertificates H X lower₀ outside t
      Kinc K Kpair Kglobal)
    (hi : i < outerSharpStopFuel H X (fineOuterReserve outside t)) :
    (R : ℝ) / (2 * outerSharpEligiblePairs H X i) ≤
      fineOuterCanonicalVertexRate H X lower₀ outside t Kinc R i := by
  let d := outerSharpLowerSchedule H X
    (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) Kinc i
  let u := outerSharpUpperSchedule H X
    (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) Kinc i
  let M := outerSharpUpperAvailability H X
    (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) Kinc i
  let E := outerSharpEligiblePairs H X i
  have hE : 0 < E := by
    have hSix : 6 ≤ E := hc.reserve_six.trans
      (outerSharpEligiblePairs_stopFuel_floor H X hc.input.reserve_initial
        hi.le)
    omega
  have hM : 0 < M := by
    simpa only [M] using hc.process.upper_availability_pos i hi
  have hratio : u + 2 ≤ 3 * d := by
    simpa only [u, d] using
      (fineOuterCanonical_schedule_ratio_bounds H X lower₀ outside t
        Kinc i hc.input.outside_pos hc.input.t_pos
        (by
          have hsix := hc.reserve_six
          omega)
        hc.input.reserve_initial hc.input.pair_upper hc.input.small_power
        hc.input.offset_power hc.input.clock_power hc.input.aggregate_power
        hc.input.initial_order hc.input.initial hc.input.reserve_four hi.le).1
  have hthreeM : 3 * M ≤ E * u := by
    simpa only [M, E, u] using
      three_mul_outerSharpUpperAvailability_le H X
        (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) Kinc i
  have hME : M ≤ E * d := by
    have hu : u ≤ 3 * d := (Nat.le_add_right u 2).trans hratio
    have hthree : 3 * M ≤ 3 * (E * d) := by
      calc
        3 * M ≤ E * u := hthreeM
        _ ≤ E * (3 * d) := Nat.mul_le_mul_left E hu
        _ = 3 * (E * d) := by ring
    omega
  simpa only [fineOuterCanonicalVertexRate, d, M, E] using
    reciprocalClockRate_le_outerOnlyVertexSelectionRate R
      (outerSharpLowerSchedule H X
        (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) Kinc)
      (outerSharpUpperAvailability H X
        (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) Kinc)
      i E hE hM hME

/-- The cumulative canonical vertex rate contains a fixed fraction of the
logarithmic drop in the eligible-pair clock. -/
theorem fineOuterCanonicalVertexRate_log_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (lower₀ outside t Kinc K Kpair Kglobal R : ℕ)
    (hc : FineOuterCanonicalCertificates H X lower₀ outside t
      Kinc K Kpair Kglobal) :
    let fuel := outerSharpStopFuel H X (fineOuterReserve outside t)
    (R : ℝ) / 12 *
        (Real.log (outerSharpEligiblePairs H X 0) -
          Real.log (outerSharpEligiblePairs H X fuel)) ≤
      cumulativeGreedyRate
        (fineOuterCanonicalVertexRate H X lower₀ outside t Kinc R) fuel := by
  dsimp only
  let reserve := fineOuterReserve outside t
  let fuel := outerSharpStopFuel H X reserve
  let rate := fineOuterCanonicalVertexRate H X lower₀ outside t Kinc R
  let S : ℝ := ∑ i ∈ range fuel,
    ((outerSharpEligiblePairs H X i : ℕ) : ℝ)⁻¹
  have hlog : Real.log (outerSharpEligiblePairs H X 0) -
        Real.log (outerSharpEligiblePairs H X fuel) ≤ 6 * S := by
    simpa only [fuel, reserve, S] using
      outerSharpClock_log_ratio_le_six_mul_sum_inv H X reserve
        hc.input.reserve_initial hc.reserve_six
  have hfactor : 0 ≤ (R : ℝ) / 12 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hlog hfactor
  have hsum : (R : ℝ) / 2 * S ≤ cumulativeGreedyRate rate fuel := by
    unfold cumulativeGreedyRate
    rw [Finset.mul_sum]
    apply sum_le_sum
    intro i hi
    have hiFuel : i < fuel := mem_range.mp hi
    have hpoint := fineOuterCanonicalVertexRate_reciprocal_lower H X lower₀
      outside t Kinc K Kpair Kglobal R i hc
      (by simpa only [fuel, reserve] using hiFuel)
    have hE : (0 : ℝ) < outerSharpEligiblePairs H X i := by
      have hSix : 6 ≤ outerSharpEligiblePairs H X i := hc.reserve_six.trans
        (outerSharpEligiblePairs_stopFuel_floor H X hc.input.reserve_initial
          (by simpa only [fuel, reserve] using hiFuel.le))
      exact_mod_cast (show 0 < outerSharpEligiblePairs H X i by omega)
    calc
      (R : ℝ) / 2 *
          ((outerSharpEligiblePairs H X i : ℕ) : ℝ)⁻¹ =
          (R : ℝ) / (2 * outerSharpEligiblePairs H X i) := by
        field_simp
      _ ≤ rate i := by simpa only [rate] using hpoint
  calc
    (R : ℝ) / 12 *
        (Real.log (outerSharpEligiblePairs H X 0) -
          Real.log (outerSharpEligiblePairs H X fuel)) ≤
        (R : ℝ) / 12 * (6 * S) := hscaled
    _ = (R : ℝ) / 2 * S := by ring
    _ ≤ cumulativeGreedyRate rate fuel := hsum

end

end Erdos207
