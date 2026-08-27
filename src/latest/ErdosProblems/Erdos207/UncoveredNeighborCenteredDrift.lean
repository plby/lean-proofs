/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.UncoveredNeighborEnvelope
import ErdosProblems.Erdos207.KSSSPowerActive
import ErdosProblems.Erdos207.CenteredStepBounds

/-! # The actual auxiliary degree observable is a supermartingale on its active band -/

namespace Erdos207

open Finset

noncomputable section

def uncoveredNeighborCenteredObservable
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finset (Finset V)) (U : Finset V) (v : V) (E t : ℝ) (s B : ℕ)
    (sigma time : ℝ) (S : GreedyStateOn V) : ℝ :=
  sigma * (((uncoveredNeighbors Q U v S).card : ℝ) - uncoveredNeighborTarget E U.card time) -
    uncoveredNeighborErrorEnvelope E U.card t s B time

theorem uncoveredNeighborCenteredObservable_increment
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finset (Finset V)) (U : Finset V) (v : V) (E t : ℝ) (s B : ℕ)
    (sigma time : ℝ) (S S' : GreedyStateOn V) :
    uncoveredNeighborCenteredObservable Q U v E t s B sigma (time + 1) S' -
      uncoveredNeighborCenteredObservable Q U v E t s B sigma time S =
    sigma * ((((uncoveredNeighbors Q U v S').card : ℝ) - (uncoveredNeighbors Q U v S).card) -
      (-3 * (U.card : ℝ) / E)) -
      (uncoveredNeighborErrorEnvelope E U.card t s B (time + 1) -
        uncoveredNeighborErrorEnvelope E U.card t s B time) := by
  have hstep := uncoveredNeighborTarget_step E U.card time
  unfold uncoveredNeighborCenteredObservable
  rw [← hstep]
  ring

theorem KSSSOnTrajectories.uncovered_neighbor_centered_drift
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {Q₀ : Finset (Finset V)}
    {q b B k : ℕ} {a coeff : ℕ → ℝ} {E A time N t : ℝ}
    (h : KSSSOnTrajectories F S q (ksssResidualPairs Q₀ S) a E A
      (N / t ^ ksssPowerErrorExponent b B) B time)
    (hgeometry : KSSSResidualGeometry Q₀ S E time)
    (hscalar : KSSSScalarPowerBounds q b B k a E A time N t)
    (hE : 0 < E) (hN : 0 < N) (ht : 0 < t) (htime : 0 ≤ time)
    (ha : ∀ d ∈ ksssOrders q, 0 ≤ a d)
    (hab : ∀ d ∈ ksssOrders q, a d * E ^ d ≤ coeff d)
    (hratio : N / 6 ≤ A / E) (hexp : Real.exp (∑ d ∈ ksssOrders q, coeff d) ≤ t)
    (U : Finset V) (v : V) (sigma : ℝ) (hsigma : |sigma| = 1)
    (hband : |((uncoveredNeighbors Q₀ U v S).card : ℝ) - uncoveredNeighborTarget E U.card time| ≤
      uncoveredNeighborErrorEnvelope E U.card t (ksssPowerErrorExponent b B) B time) :
    (greedyKernel F S).expectationReal (fun S' ↦
      uncoveredNeighborCenteredObservable Q₀ U v E t (ksssPowerErrorExponent b B) B sigma (time + 1) S' -
        uncoveredNeighborCenteredObservable Q₀ U v E t (ksssPowerErrorExponent b B) B sigma time S) ≤ 0 := by
  let s := ksssPowerErrorExponent b B
  let p := ksssEdgeDensity E time
  let L := E * p
  let x := ksssPairTrajectory (ksssOrders q) a E A time
  let e := ksssErrorEnvelope E (N / t ^ s) B time
  let M : ℝ := U.card
  let Y : ℝ := (uncoveredNeighbors Q₀ U v S).card
  let r : ℝ := S.available.card
  let z := uncoveredNeighborErrorEnvelope E M t s B time
  let X := fun S' ↦ ((uncoveredNeighbors Q₀ U v S').card : ℝ) - Y
  let D := (greedyKernel F S).expectationReal X
  have hp : 0 < p := ksssEdgeDensity_pos hE hscalar.clock_strict
  have hL : 0 < L := mul_pos hE hp
  have hx : 0 < x := (by positivity : 0 < N / t ^ (3 * b + 1)).trans_le hscalar.pair_lower
  have he : 0 ≤ e := by dsimp only [e, ksssErrorEnvelope]; positivity
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have hY : 0 ≤ Y := Nat.cast_nonneg _
  have hYM : Y ≤ M := by
    have hsub : uncoveredNeighbors Q₀ U v S ⊆ U := filter_subset _ _
    dsimp only [Y, M]
    exact_mod_cast card_le_card hsub
  have hglobal := h.availability_error hgeometry.pair_card hgeometry.cover
  rw [hgeometry.count] at hglobal
  change |r - L * x / 3| ≤ L * e / 3 at hglobal
  have hr : L * x / 4 ≤ r := by
    have hlo := (abs_le.mp hglobal).1
    have hsmall := mul_le_mul_of_nonneg_left hscalar.error_small hL.le
    change L * e ≤ L * (x / 4) at hsmall
    nlinarith only [hlo, hsmall]
  have hrpos : 0 < r := (by positivity : 0 < L * x / 4).trans_le hr
  have hAcard : (0 : ℝ) < S.available.card := hrpos
  have hA : S.available.Nonempty := card_pos.mp (by exact_mod_cast hAcard)
  have hQpos : 0 < (ksssResidualPairs Q₀ S).card := by
    have hQposR : (0 : ℝ) < (ksssResidualPairs Q₀ S).card := by rw [hgeometry.count]; exact hL
    exact_mod_cast hQposR
  have hraw := greedyKernel_uncoveredNeighbor_clock_drift_error F Q₀ U v S x e hA
    hgeometry.pair_card hgeometry.cover hQpos h.1
  rw [hgeometry.count] at hraw
  have htarget : |D - (-3 * M / E)| ≤ 2 * Y * e / r + 3 * z / L :=
    neighbor_clock_target_drift_error D Y M E p r e z hE hp hraw hband
  have hxlower := ksssPairTrajectory_lower_fixed_initial_ratio (ksssOrders q) a coeff E A time N t
    hE hN ht htime hscalar.clock_strict ha hab hratio hexp
  have hz : 8 * M * e / x ≤ z :=
    pair_error_le_neighbor_envelope N M t p x s B hN hM ht hp hxlower
  have hpairError := neighbor_pair_drift_error_le_envelope Y M e r L x z hY hYM he hL hx hr hz
  have hrawFinal : |D - (-3 * M / E)| ≤ 4 * z / L := by
    calc
      _ ≤ 2 * Y * e / r + 3 * z / L := htarget
      _ ≤ z / L + 3 * z / L := add_le_add hpairError le_rfl
      _ = _ := by ring
  have hg := uncoveredNeighborErrorEnvelope_growth_dominates E M t time s B hE hM ht
    (by linarith [hscalar.unit_clock])
  have hcenter := centered_step_drift_nonpos (greedyKernel F S) X sigma (-3 * M / E)
    (uncoveredNeighborErrorEnvelope E M t s B (time + 1) - z) (-3 * M / E) (4 * z / L) 0
    hsigma hrawFinal (by simp) (by simpa only [add_zero] using hg)
  simpa only [uncoveredNeighborCenteredObservable_increment] using hcenter

end

end Erdos207
