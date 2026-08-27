/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.BoundedGraphInitialLaw

/-! # The sharp mixed recurrence before choosing either probability scale -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem timedStoppedGreedyProcess_boundedSharp_graph_compatible
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (G : SimpleGraph V)
    (active : ℕ → GreedyStateOn V → Prop) (Inv : GreedyStateOn V → Prop)
    (D d M : ℕ → ℕ) (K : ℕ) (S₀ : GreedyStateOn V)
    (hchosen₀ : S₀.chosen = ∅) (hInv₀ : Inv S₀) (hactive₀ : active 0 S₀)
    (hInv : ∀ i, i < n → ∀ S, Inv S → active i S → (greedyKernel F S).SupportedOn Inv)
    (hstructInv : ∀ S, Inv S → GreedyInvariant F S ∧ S.available ⊆ S₀.available ∧ S.chosen ⊆ S₀.available)
    (hambient : ∀ T ∈ S₀.available, tripleEdgeFinset T ⊆ graphEdges G)
    (hD : ∀ i, i < n → 0 < D i)
    (hfloor : ∀ i S, i < n → Inv S → active i S → D i ≤ S.available.card)
    (hpairFloor : ∀ i S, i < n → Inv S → active i S →
      ∀ e ∈ graphEdges G, e ∉ (coveredGraph S.chosen).edgeSet → d i ≤ (greedyChoicesCoveringEdge S e).card)
    (hupper : ∀ i S, i < n → Inv S → active i S → S.available.card ≤ M i)
    (hdM : ∀ i, i < n → d i ≤ M i) (heffective : ∀ i, i < n → d i - 3 * K < M i)
    (error : ℝ≥0)
    (hinactive : (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ ¬ active z.1.1 z.2) ≤ error)
    (Q : TripleSystemOn V) (edges : Finset (Sym2 V))
    (hQpacking : IsPackingOn Q) (hQavailable : Q ⊆ S₀.available)
    (hQE : Disjoint (Q.biUnion tripleEdgeFinset) edges) (hedge : edges ⊆ graphEdges G)
    (hcard : Q.card + edges.card ≤ K) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ Q ⊆ z.2.chosen ∧ ∀ e ∈ edges, e ∉ (coveredGraph z.2.chosen).edgeSet) ≤
      cumulativeSurvival (boundedSharpSurvivalSchedule n M d (3 * K)) n ^ edges.card *
        transferPointWeight (boundedSharpSurvivalSchedule n M d (3 * K))
          (boundedSharpTransferSchedule n D M d (3 * K)) n ^ Q.card + error := by
  let theta := boundedSharpSurvivalSchedule n M d (3 * K)
  let rho := boundedSharpTransferSchedule n D M d (3 * K)
  have hEoff : edges ⊆ offdiagPart edges := by rw [offdiagPart_eq_of_subset_graphEdges hedge]
  have hE₀ : ∀ e ∈ edges, e ∉ (coveredGraph S₀.chosen).edgeSet := by
    intro e _
    simp only [hchosen₀, coveredGraph_empty, SimpleGraph.edgeSet_bot, Set.mem_empty_iff_false, not_false_eq_true]
  have hsupply : ∀ i S R, i < n → Inv S → active i S → R ⊆ Q → Q \ R ⊆ S.available →
      edges ⊆ greedyUncoveredEdges (graphEdges (SimpleGraph.completeGraph V)) S →
      ∀ e ∈ pendingSurvivalEdges (Q \ R) edges, d i ≤ (greedyChoicesCoveringEdge S e).card := by
    intro i S R hi hIS hact _ hpending hEuncovered
    exact pendingSurvivalEdges_supply_of_graph_floor (hstructInv S hIS).1 hpending
      (fun T hT ↦ hambient T ((hstructInv S hIS).2.1 hT)) hedge hEuncovered (hpairFloor i S hi hIS hact)
  have hscalar : ∀ i S R, i < n → Inv S → active i S → R ⊆ Q →
      ((S.available.card - ((3 * (Q \ R).card + edges.card) * d i -
        (3 * (Q \ R).card + edges.card).choose 2) : ℕ) : ℝ≥0) * (S.available.card : ℝ≥0)⁻¹ ≤
      theta i ^ (3 * (Q \ R).card + edges.card) := by
    intro i S R hi hIS hact hRQ
    have hk := pending_edge_count_le_three_mul_patternCutoff hRQ (Subset.refl edges) hcard
    simpa only [theta, boundedSharpSurvivalSchedule, if_pos hi, boundedSharpSurvivalTheta] using
      sharp_survival_scalar_of_card_le S.available.card (M i) (d i) (3 * K) _
        ((hD i hi).trans_le (hfloor i S hi hIS hact)) (hupper i S hi hIS hact) (hdM i hi) hk
  have htheta : ∀ i, theta i ≤ 1 := by
    intro i
    by_cases hi : i < n
    · simpa only [theta, boundedSharpSurvivalSchedule, if_pos hi] using
        boundedSharpSurvivalTheta_le_one (M i) (d i) (3 * K)
          (lt_of_le_of_lt (Nat.zero_le _) (heffective i hi))
    · simp [theta, boundedSharpSurvivalSchedule, if_neg hi]
  have hadjust : ∀ i, (D i : ℝ≥0)⁻¹ ≤ theta i ^ (3 * Q.card + edges.card) * rho i := by
    intro i
    have hk : 3 * Q.card + edges.card ≤ 3 * K := by omega
    by_cases hi : i < n
    · simpa only [theta, rho, boundedSharpSurvivalSchedule, boundedSharpTransferSchedule, if_pos hi] using
        inv_le_pow_mul_boundedSharpTransferRho (D i) (M i) (d i) (3 * K) _ hk
          (lt_of_le_of_lt (Nat.zero_le _) (heffective i hi))
          (boundedSharpSurvivalTheta_pos (M i) (d i) (3 * K) (heffective i hi))
    · simp [theta, rho, boundedSharpSurvivalSchedule, boundedSharpTransferSchedule, if_neg hi]
  have hraw := timedStoppedGreedyProcess_probability_initialEvent_le_trackedProduct n F active Inv D d theta rho
    S₀ hInv₀ hactive₀ hInv hD hfloor Q edges edges hEoff hQpacking hQE hsupply hscalar htheta hadjust
    (by simp [hchosen₀]) hQavailable hE₀
  exact hraw.trans (add_le_add le_rfl hinactive)

end

end Erdos207
