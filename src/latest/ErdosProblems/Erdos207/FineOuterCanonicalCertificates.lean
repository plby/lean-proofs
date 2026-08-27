/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FineOuterCanonicalCoarseBounds

/-!
# Complete deterministic certificate for the canonical outer phase

This module is the final deterministic boundary before the probabilistic
initial-product theorem.  It combines the analytic corridor, its coarse
integer bounds, the sharp rate/variance estimates, and the zero-slope cubic
envelope.  The eventual hierarchy is left with only explicit scalar
inequalities in natural numbers and nonnegative reals.
-/

namespace Erdos207

open scoped NNReal

noncomputable section

structure FineOuterCanonicalInput
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (lower₀ outside t K : ℕ) : Prop where
  outside_pos : 0 < outside
  t_pos : 0 < t
  reserve_initial : fineOuterReserve outside t ≤
    outerSharpEligiblePairs H X 0
  pair_upper : 2 * (outerSharpEligiblePairs H X 0 : ℕ) ≤
    (outside : ℝ) ^ 2
  small_power : 12800 ≤ t ^ 31
  offset_power : t ^ fineOuterCorridorExponent ≤ 16 * outside
  clock_power : 50 * t ^ 101 ≤ outside ^ 2
  aggregate_power : t ^ 102 * K ≤ 8 * outside ^ 2
  initial_order : lower₀ ≤ outside
  initial :
    (outside : ℝ) ≤
        quadraticPairBarrier (outside : ℝ≥0)
          (fineOffsetUpperCoefficient t)
          (outerSharpEligiblePairs H X 0 : ℝ≥0) 3 0 +
            fineOuterInitialOffset outside t ∧
      quadraticPairBarrier (outside : ℝ≥0)
          (fineOffsetLowerCoefficient t)
          (outerSharpEligiblePairs H X 0 : ℝ≥0) 3 0 -
            fineOuterInitialOffset outside t ≤ (lower₀ : ℝ)
  reserve_four : 4 ≤ fineOuterReserve outside t
  degree_pos : 0 < fineOuterCoarseDegreeFloor outside t

structure FineOuterCanonicalCertificates
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (lower₀ outside t Kinc K Kpair Kglobal : ℕ) : Prop where
  input : FineOuterCanonicalInput H X lower₀ outside t Kinc
  reserve_six : 6 ≤ fineOuterReserve outside t
  bounds : let fuel := outerSharpStopFuel H X (fineOuterReserve outside t)
    ∀ i, i ≤ fuel →
      fineOuterCoarseDegreeFloor outside t ≤
          outerSharpLowerSchedule H X
            (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) Kinc i ∧
      outerSharpUpperSchedule H X
          (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) Kinc i ≤
          5 * outside ∧
      fineOuterCoarseAvailabilityFloor outside t ≤
          outerSharpLowerAvailability H X
            (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) Kinc i ∧
      0 ≤ (outerSharpEnvelope H X
          (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t) Kinc i).2 -
            fineOuterBuffer outside t
  process : FineOuterProcessBounds H X
    (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t)
    Kinc K (outerSharpStopFuel H X (fineOuterReserve outside t))
    (fineOuterCoarseDegreeFloor outside t) (5 * outside)
    (fineOuterCoarseAvailabilityFloor outside t) Kpair Kglobal
    (fineOuterReserve outside t)
  envelope : FineOuterZeroEnvelopeBounds H X
    (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t)
    Kinc K (outerSharpStopFuel H X (fineOuterReserve outside t))
    (fineOuterCoarseDegreeFloor outside t)
    (t : ℝ≥0) (64 * t ^ 2 : ℕ) 20

theorem fineOuterCanonicalCertificates
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (lower₀ outside t Kinc K Kpair Kglobal : ℕ)
    (hinput : FineOuterCanonicalInput H X lower₀ outside t Kinc)
    (hgap : 5 * outside < fineOuterCoarseAvailabilityFloor outside t)
    (hupper : 12 * (5 * outside) ≤ fineOuterReserve outside t)
    (hlower : 2 * (5 * outside) ^ 2 + Kinc ≤
      fineOuterCoarseDegreeFloor outside t *
        (fineOuterCoarseAvailabilityFloor outside t - 5 * outside))
    (hpairScalar :
      ((outerSharpEligiblePairs H X 0 : ℕ) : ℝ≥0) ^ 2 ≤
        (64 * t ^ 2 : ℕ) * (Fintype.card V : ℝ≥0) ^ 3 *
          fineOuterCoarseDegreeFloor outside t)
    (hquadratic : (Fintype.card V : ℝ≥0) ^ 2 ≤
      20 * (outerSharpEligiblePairs H X 0 : ℕ)) :
    FineOuterCanonicalCertificates H X lower₀ outside t Kinc K Kpair Kglobal := by
  let reserve := fineOuterReserve outside t
  let fuel := outerSharpStopFuel H X reserve
  let dmin := fineOuterCoarseDegreeFloor outside t
  let Umax := 5 * outside
  let Dcut := fineOuterCoarseAvailabilityFloor outside t
  have hreservePos : 0 < reserve := by
    have houtsidePos := hinput.outside_pos
    have hreserveLarge := hupper
    dsimp only [reserve]
    omega
  have hbounds := fineOuterCanonical_coarse_uniform_bounds H X lower₀
    outside t Kinc hinput.outside_pos hinput.t_pos hreservePos
    hinput.reserve_initial hinput.pair_upper hinput.small_power
    hinput.offset_power hinput.clock_power hinput.aggregate_power
    hinput.initial_order hinput.initial hinput.reserve_four hinput.degree_pos
  have hcorridor := outerSharpRecursiveSchedules_between_fineCanonicalBarriers
    H X lower₀ outside t Kinc hinput.outside_pos hinput.t_pos hreservePos
    hinput.reserve_initial hinput.pair_upper hinput.small_power
    hinput.offset_power hinput.clock_power hinput.aggregate_power
    hinput.initial_order hinput.initial hinput.reserve_four
  have horder : ∀ i, i ≤ fuel →
      outerSharpLowerSchedule H X (outside : ℝ) (lower₀ : ℝ)
          (fineOuterBuffer outside t) Kinc i ≤
        outerSharpUpperSchedule H X (outside : ℝ) (lower₀ : ℝ)
          (fineOuterBuffer outside t) Kinc i := by
    intro i hi
    simpa only [fuel, reserve] using (hcorridor i (by simpa only [fuel, reserve] using hi)).2.2
  have hreserve : ∀ i, i ≤ fuel →
      reserve ≤ outerSharpEligiblePairs H X i := by
    intro i hi
    exact outerSharpEligiblePairs_stopFuel_floor H X hinput.reserve_initial
      (by simpa only [fuel, reserve] using hi)
  have hprocess : FineOuterProcessBounds H X
      (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t)
      Kinc K fuel dmin Umax Dcut Kpair Kglobal reserve := by
    apply fineOuterProcessBounds_of_uniform H X
      (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t)
      Kinc K fuel dmin Umax Dcut Kpair Kglobal reserve
    · dsimp only [reserve]
      have houtsidePos := hinput.outside_pos
      have hreserveLarge := hupper
      omega
    · simpa only [dmin] using hinput.degree_pos
    · dsimp only [Dcut, Umax]
      omega
    · simpa only [Dcut, Umax] using hgap
    · simpa only [reserve, Umax] using hupper
    · simpa only [dmin, Dcut, Umax] using hlower
    · intro i hi
      have hb := hbounds i (by simpa only [fuel, reserve] using hi)
      simpa only [fuel, reserve, dmin, Umax, Dcut] using
        And.intro hb.1 (And.intro hb.2.1 hb.2.2.1)
    · exact horder
    · exact hreserve
  have hE0 : 0 < outerSharpEligiblePairs H X 0 :=
    hreservePos.trans_le hinput.reserve_initial
  have hclock : ∀ i, i ≤ fuel →
      (outerSharpEligiblePairs H X 0 : ℝ≥0) ≤
        (t : ℝ≥0) * (outerSharpEligiblePairs H X i : ℕ) := by
    intro i hi
    exact_mod_cast initialEligible_le_t_mul_current H X outside t i
      hinput.t_pos hreservePos hinput.reserve_initial
      (by simpa only [fuel, reserve] using hi) hinput.pair_upper
  have henvelope : FineOuterZeroEnvelopeBounds H X
      (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t)
      Kinc K fuel dmin (t : ℝ≥0) (64 * t ^ 2 : ℕ) 20 := by
    apply fineOuterZeroEnvelopeBounds_of_uniform H X
      (outside : ℝ) (lower₀ : ℝ) (fineOuterBuffer outside t)
      Kinc K fuel dmin (t : ℝ≥0) (64 * t ^ 2 : ℕ) 20 hE0
    · intro i hi
      exact (hbounds i (by simpa only [fuel, reserve] using hi)).1
    · exact hclock
    · simpa only [dmin] using hpairScalar
    · exact hquadratic
  refine ⟨hinput, ?_, ?_, ?_, ?_⟩
  · have houtsidePos := hinput.outside_pos
    have hreserveLarge := hupper
    omega
  · simpa only [fuel, reserve] using hbounds
  · simpa only [fuel, reserve, dmin, Umax, Dcut] using hprocess
  · simpa only [fuel, reserve, dmin] using henvelope

end

end Erdos207
