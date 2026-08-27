/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.UncoveredNeighborMoments
import ErdosProblems.Erdos207.InitialPairAverage
import ErdosProblems.Erdos207.KSSSIndexedSelectors

/-! # Exact residual-clock normalization for the auxiliary degree drift -/

namespace Erdos207

open Finset

noncomputable section

theorem pair_average_error_of_uniform_errors
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : GreedyStateOn V) (Q : Finset (Finset V)) (x e : ℝ)
    (hQ : ∀ P ∈ Q, P.card = 2)
    (hcover : ∀ P : Finset V, P.card = 2 → (availableTrianglesContainingPair S P).Nonempty → P ∈ Q)
    (hQpos : 0 < Q.card)
    (hpair : ∀ P ∈ Q, |((availableTrianglesContainingPair S P).card : ℝ) - x| ≤ e) :
    ∀ P ∈ Q, |((availableTrianglesContainingPair S P).card : ℝ) -
      3 * (S.available.card : ℝ) / Q.card| ≤ 2 * e := by
  have hinterval := initial_pair_average_interval S Q (x + e) (2 * e) hQ hcover hQpos
    (fun P hP ↦ by
      have hp := abs_le.mp (hpair P hP)
      constructor <;> linarith only [hp.1, hp.2])
  exact hinterval.2

theorem greedyKernel_uncoveredNeighbor_clock_drift_error
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q₀ : Finset (Finset V)) (U : Finset V) (v : V)
    (S : GreedyStateOn V) (x e : ℝ) (hA : S.available.Nonempty)
    (hQ : ∀ P ∈ ksssResidualPairs Q₀ S, P.card = 2)
    (hcover : ∀ P : Finset V, P.card = 2 →
      (availableTrianglesContainingPair S P).Nonempty → P ∈ ksssResidualPairs Q₀ S)
    (hQpos : 0 < (ksssResidualPairs Q₀ S).card)
    (hpair : ∀ P ∈ ksssResidualPairs Q₀ S, |((availableTrianglesContainingPair S P).card : ℝ) - x| ≤ e) :
    |(greedyKernel F S).expectationReal (fun S' ↦
      ((uncoveredNeighbors Q₀ U v S').card : ℝ) - (uncoveredNeighbors Q₀ U v S).card) -
      (-3 * ((uncoveredNeighbors Q₀ U v S).card : ℝ) / (ksssResidualPairs Q₀ S).card)| ≤
      2 * ((uncoveredNeighbors Q₀ U v S).card : ℝ) * e / S.available.card := by
  have hmean := pair_average_error_of_uniform_errors S (ksssResidualPairs Q₀ S) x e hQ hcover hQpos hpair
  have hraw := greedyKernel_uncoveredNeighbor_drift_error F Q₀ U v S hA
    (3 * (S.available.card : ℝ) / (ksssResidualPairs Q₀ S).card) (2 * e)
    (fun u hu ↦ hmean {v, u} (mem_sdiff.mpr (mem_filter.mp hu).2.2))
  have hApos : (0 : ℝ) < S.available.card := by exact_mod_cast card_pos.mpr hA
  have hQposR : (0 : ℝ) < (ksssResidualPairs Q₀ S).card := by exact_mod_cast hQpos
  have hid : -((uncoveredNeighbors Q₀ U v S).card : ℝ) *
      (3 * (S.available.card : ℝ) / (ksssResidualPairs Q₀ S).card) / S.available.card =
      -3 * ((uncoveredNeighbors Q₀ U v S).card : ℝ) / (ksssResidualPairs Q₀ S).card := by
    field_simp
  rw [hid] at hraw
  convert hraw using 1 <;> ring

def uncoveredNeighborTarget (E M time : ℝ) : ℝ := M * ksssEdgeDensity E time

theorem uncoveredNeighborTarget_step (E M time : ℝ) :
    uncoveredNeighborTarget E M (time + 1) - uncoveredNeighborTarget E M time = -3 * M / E := by
  unfold uncoveredNeighborTarget ksssEdgeDensity
  ring

theorem neighbor_clock_target_drift_error
    (D Y M E p r e z : ℝ) (hE : 0 < E) (hp : 0 < p)
    (hraw : |D - (-3 * Y / (E * p))| ≤ 2 * Y * e / r)
    (hband : |Y - M * p| ≤ z) :
    |D - (-3 * M / E)| ≤ 2 * Y * e / r + 3 * z / (E * p) := by
  have hshift : |(-3 * Y / (E * p)) - (-3 * M / E)| ≤ 3 * z / (E * p) := by
    have hid : (-3 * Y / (E * p)) - (-3 * M / E) = -3 * (Y - M * p) / (E * p) := by
      field_simp
      ring
    rw [hid, abs_div, abs_mul, abs_of_pos (mul_pos hE hp)]
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hband (by norm_num)) (mul_pos hE hp).le
  calc
    _ ≤ |D - (-3 * Y / (E * p))| + |(-3 * Y / (E * p)) - (-3 * M / E)| :=
      abs_sub_le _ _ _
    _ ≤ _ := add_le_add hraw hshift

end

end Erdos207
