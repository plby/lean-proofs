/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.UncoveredNeighborGraph
import ErdosProblems.Erdos207.InitialPowerCoupledRegularity

/-! # Actual initial degree errors and margins on every power-vortex level -/

namespace Erdos207

open Finset
open scoped Classical

noncomputable section

theorem abs_card_sub_eq_card_sdiff_of_subset
    {V : Type*} [DecidableEq V] (A U : Finset V) (hAU : A ⊆ U) :
    |(A.card : ℝ) - U.card| = ((U \ A).card : ℝ) := by
  have hcard := card_le_card hAU
  have hcardR : (A.card : ℝ) ≤ U.card := by exact_mod_cast hcard
  rw [abs_of_nonpos (sub_nonpos.mpr hcardR), card_sdiff_of_subset hAU, Nat.cast_sub hcard]
  ring

theorem initial_uncoveredNeighbor_error_eq_loss
    {V : Type*} [Fintype V] [DecidableEq V] (q : ℕ) (H : SimpleGraph V)
    (bank : TripleSystemOn V) (U : Finset V) (v : V) :
    |((uncoveredNeighbors (initialResidualPairs H) U v (absorberGreedyInitialState
      (absorberErdosForbiddenConfigurationsOn q bank) (outsideAvailableTriangles H bank))).card : ℝ) - U.card| =
    ((U \ neighborsIn (graphDifference (SimpleGraph.completeGraph V) H) U v).card : ℝ) := by
  rw [uncoveredNeighbors_initialResidualPairs_eq_graph_neighbors]
  have hgraph : graphDifference (graphDifference (SimpleGraph.completeGraph V) H)
      (coveredGraph (∅ : TripleSystemOn V)) = graphDifference (SimpleGraph.completeGraph V) H := by
    rw [coveredGraph_empty]
    simp [graphDifference]
  change |((neighborsIn (graphDifference (graphDifference (SimpleGraph.completeGraph V) H)
    (coveredGraph (∅ : TripleSystemOn V))) U v).card : ℝ) - U.card| = _
  rw [hgraph]
  exact abs_card_sub_eq_card_sdiff_of_subset _ U (fun _ hw ↦ (mem_neighborsIn_iff.mp hw).1)

theorem InitialPowerVortexPackage.level_card_lower
    {q h n ell t rootPower step : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step) (i : Fin (ell + 1)) :
    t ^ rootPower ≤ (P.W.U i).card := by
  have hsub : P.X ⊆ P.W.U i := by
    rw [← P.terminal]
    exact P.W.antitone i (Fin.last ell) (Fin.le_last i)
  simpa only [P.rootCard] using card_le_card hsub

theorem initial_inner_neighbor_margin
    (M t : ℝ) (s : ℕ) (ht : 2 ≤ t) (hM : t ^ s ≤ M) : 15 ≤ 8 * M * t / t ^ s := by
  have htpos : 0 < t := by linarith
  calc
    15 ≤ 8 * t := by linarith
    _ = 8 * t ^ s * t / t ^ s := by field_simp
    _ ≤ _ := by gcongr

theorem initial_outer_neighbor_margin
    (N C t : ℝ) (v s : ℕ) (ht : 2 ≤ t) (hC : C ≤ t ^ v)
    (hscale : t ^ (v + s) ≤ N) : C + 1 ≤ 8 * N * t / t ^ s := by
  have htpos : 0 < t := by linarith
  have hp : 1 ≤ t ^ v := one_le_pow₀ (by linarith)
  have hN : 0 ≤ N := (pow_nonneg htpos.le _).trans hscale
  calc
    _ ≤ 2 * t ^ v := by linarith only [hC, hp]
    _ = 2 * t ^ (v + s) / t ^ s := by rw [pow_add]; field_simp
    _ ≤ 2 * N / t ^ s := div_le_div_of_nonneg_right (by linarith only [hscale]) (pow_nonneg htpos.le _)
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg htpos.le _)
      have hx := mul_nonneg hN (show 0 ≤ 8 * t - 2 by linarith)
      nlinarith only [hx]

theorem InitialPowerVortexPackage.initial_neighbor_margins
    {q h n ell t rootPower step : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step) (s R : ℕ)
    (ht : 2 ≤ t) (hc : powerAbsorberCoefficient q ≤ t) (hroot : s ≤ rootPower)
    (hscale : t ^ R ≤ n) (hgap : initialSupportPower rootPower + s ≤ R) :
    let S₀ := absorberGreedyInitialState (absorberErdosForbiddenConfigurationsOn q P.B)
      (outsideAvailableTriangles P.H P.B)
    ∀ i : Fin (ell + 1), ∀ v : Fin n,
      |((uncoveredNeighbors (initialResidualPairs P.H) (P.W.U i) v S₀).card : ℝ) - (P.W.U i).card| ≤
        8 * ((P.W.U i).card : ℝ) * t / (t : ℝ) ^ s := by
  dsimp only
  intro i v
  rw [initial_uncoveredNeighbor_error_eq_loss]
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  by_cases hi : i = 0
  · subst i
    rw [P.W.root, card_univ, Fintype.card_fin]
    have hdegree := (P.support_power_bounds hc).1
    have hloss : (((univ : Finset (Fin n)) \ neighborsIn
        (graphDifference (SimpleGraph.completeGraph (Fin n)) P.H) univ v).card : ℝ) ≤
        ((t ^ initialSupportPower rootPower + 1 : ℕ) : ℝ) := by
      exact_mod_cast card_initial_ambient_degree_loss_le hdegree v
    have hpower : (t : ℝ) ^ (initialSupportPower rootPower + s) ≤ n := by
      exact_mod_cast (Nat.pow_le_pow_right (by omega : 0 < t) hgap).trans hscale
    have hm := initial_outer_neighbor_margin (n : ℝ) (t ^ initialSupportPower rootPower : ℕ) t
      (initialSupportPower rootPower) s htR (by simp only [Nat.cast_pow]; exact le_rfl) hpower
    exact hloss.trans (by simpa only [Nat.cast_add, Nat.cast_one] using hm)
  · have hsep : AbsorberSeparatedLevel P.H P.X P.B (P.W.U i) := by
      rw [P.vortex_eq]
      exact separatedCardinalVortex_separated _ _ _ _ _ hi
    have hloss : (((P.W.U i) \ neighborsIn
        (graphDifference (SimpleGraph.completeGraph (Fin n)) P.H) (P.W.U i) v).card : ℝ) ≤ 15 := by
      exact_mod_cast card_initial_separated_degree_loss_le_fifteen hsep P.rootBounds v
    have hM : (t : ℝ) ^ s ≤ ((P.W.U i).card : ℝ) := by
      exact_mod_cast (Nat.pow_le_pow_right (by omega : 0 < t) hroot).trans (P.level_card_lower i)
    exact hloss.trans (initial_inner_neighbor_margin (P.W.U i).card t s htR hM)

end

end Erdos207
