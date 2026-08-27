/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.UncoveredNeighborVariance

/-! # Actual centered degree jump and variance bounds on the coupled event -/

namespace Erdos207

open Finset

noncomputable section

theorem KSSSOnTrajectories.uncovered_neighbor_jump_variance
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {Q₀ : Finset (Finset V)}
    {q b B k : ℕ} {a : ℕ → ℝ} {E A time N t : ℝ}
    (h : KSSSOnTrajectories F S q (ksssResidualPairs Q₀ S) a E A
      (N / t ^ ksssPowerErrorExponent b B) B time)
    (hgeometry : KSSSResidualGeometry Q₀ S E time)
    (hscalar : KSSSScalarPowerBounds q b B k a E A time N t)
    (hE : 0 < E) (hN : 0 < N) (ht : 0 < t) (htime : 0 ≤ time)
    (hfloor : 1 / t ^ b ≤ ksssEdgeDensity E time)
    (hcoefficient : 6 * ((B + 2 : ℕ) : ℝ) * 2 ^ (B + 2) ≤ t)
    (U : Finset V) (v : V) (sigma : ℝ) (hsigma : |sigma| = 1)
    (hsmall : 19 * (U.card : ℝ) / (E * ksssEdgeDensity E time) ≤ 1) :
    (greedyKernel F S).SupportedOn (fun S' ↦
      |uncoveredNeighborCenteredObservable Q₀ U v E t (ksssPowerErrorExponent b B) B sigma (time + 1) S' -
        uncoveredNeighborCenteredObservable Q₀ U v E t (ksssPowerErrorExponent b B) B sigma time S| ≤ 3) ∧
    (greedyKernel F S).expectationReal (fun S' ↦
      (uncoveredNeighborCenteredObservable Q₀ U v E t (ksssPowerErrorExponent b B) B sigma (time + 1) S' -
        uncoveredNeighborCenteredObservable Q₀ U v E t (ksssPowerErrorExponent b B) B sigma time S) ^ 2) ≤
      64 * (U.card : ℝ) / (E * ksssEdgeDensity E time) := by
  let s := ksssPowerErrorExponent b B
  let L := E * ksssEdgeDensity E time
  let x := ksssPairTrajectory (ksssOrders q) a E A time
  let e := ksssErrorEnvelope E (N / t ^ s) B time
  let M : ℝ := U.card
  let X := fun S' ↦ ((uncoveredNeighbors Q₀ U v S').card : ℝ) - (uncoveredNeighbors Q₀ U v S).card
  let df := -3 * M / E
  let de := uncoveredNeighborErrorEnvelope E M t s B (time + 1) - uncoveredNeighborErrorEnvelope E M t s B time
  have hp := ksssEdgeDensity_pos hE hscalar.clock_strict
  have hL : 0 < L := mul_pos hE hp
  have hx : 0 < x := (by positivity : 0 < N / t ^ (3 * b + 1)).trans_le hscalar.pair_lower
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have hglobal := h.availability_error hgeometry.pair_card hgeometry.cover
  rw [hgeometry.count] at hglobal
  change |(S.available.card : ℝ) - L * x / 3| ≤ L * e / 3 at hglobal
  have hr : L * x / 4 ≤ (S.available.card : ℝ) := by
    have hlo := (abs_le.mp hglobal).1
    have herror := mul_le_mul_of_nonneg_left hscalar.error_small hL.le
    change L * e ≤ L * (x / 4) at herror
    nlinarith only [hlo, herror]
  have hApos : (0 : ℝ) < S.available.card := (by positivity : 0 < L * x / 4).trans_le hr
  have hA : S.available.Nonempty := card_pos.mp (by exact_mod_cast hApos)
  have hpair : ∀ u ∈ uncoveredNeighbors Q₀ U v S,
      ((availableTrianglesContainingPair S {v, u}).card : ℝ) ≤ 5 * x / 4 := by
    intro u hu
    have hQ : {v, u} ∈ ksssResidualPairs Q₀ S := mem_sdiff.mpr (mem_filter.mp hu).2.2
    have hbnd := (abs_le.mp (h.1 {v, u} hQ)).2
    have herror := hscalar.error_small
    change e ≤ x / 4 at herror
    change ((availableTrianglesContainingPair S {v, u}).card : ℝ) - x ≤ e at hbnd
    linarith only [hbnd, herror]
  have hraw : (greedyKernel F S).expectationReal (fun S' ↦ X S' ^ 2) ≤ 10 * M / L :=
    greedyKernel_uncoveredNeighbor_secondMoment_le_clock F Q₀ U v S hA L x hL hx hr hpair
  have hdet : |df| + |de| ≤ 19 * M / L := by
    have hd := uncoveredNeighbor_deterministic_increment_le_clock E M t time b B hE hM ht htime
      hscalar.unit_clock hfloor hcoefficient
    rw [uncoveredNeighborTarget_step] at hd
    exact hd
  constructor
  · intro S' hmass
    have hinterval := greedyKernel_uncoveredNeighbor_increment_interval F Q₀ U v S S' hmass
    have habs : |X S'| ≤ 2 := abs_le.mpr ⟨hinterval.1, hinterval.2.trans (by norm_num)⟩
    rw [uncoveredNeighborCenteredObservable_increment]
    have hc := centered_step_abs_le sigma (X S') df de hsigma
    change |sigma * (X S' - df) - de| ≤ 3
    linarith only [hc, habs, hdet, hsmall]
  · have hc := neighbor_centered_secondMoment_clock_budget (greedyKernel F S) X M L sigma df de
      hM hL hsigma hraw hdet hsmall
    simpa only [uncoveredNeighborCenteredObservable_increment] using hc

end

end Erdos207
