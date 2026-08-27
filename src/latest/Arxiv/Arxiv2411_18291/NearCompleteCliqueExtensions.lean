import Arxiv.Arxiv2411_18291.GraphBoundedness
import Arxiv.Arxiv2411_18291.RootedCliqueBounds
import Arxiv.Arxiv2411_18291.ShiftedChooseBounds

/-!
# Clique extension counts in a graph with bounded complement

An unavailable next vertex is either already used or completes a missing
edge from one of the current faces. The union bound therefore gives a
uniform lower bound for every clique extension, without typicality.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {r k : ℕ}

theorem cliqueNextVertices_complement_subset (G : Hypergraph V (r + 1)) (U : Block V k) :
    univ \ cliqueNextVertices G U ⊆
      U.val ∪ (cliqueEdges r U).biUnion (fun S => neighbors (complete V (r + 1) \ G) S) := by
  intro v hv
  by_cases hvU : v ∈ U.val
  · exact mem_union_left _ hvU
  · by_contra h
    have hnot : ∀ S ∈ cliqueEdges r U, v ∉ neighbors (complete V (r + 1) \ G) S := by
      intro S hS hvS
      exact h (mem_union_right _ (mem_biUnion.mpr ⟨S, hS, hvS⟩))
    apply (mem_sdiff.mp hv).2
    apply (mem_cliqueNextVertices G U v).mpr
    refine ⟨(mem_commonNeighbors _ _ _).mpr ?_, hvU⟩
    intro S hS
    have hvS : v ∉ S.val := fun hs => hvU (((mem_cliqueEdges _ _).mp hS) hs)
    apply (mem_neighbors _ _ _).mpr
    refine ⟨hvS, ?_⟩
    by_contra he
    exact hnot S hS ((mem_neighbors _ _ _).mpr ⟨hvS, mem_sdiff.mpr ⟨mem_univ _, he⟩⟩)

theorem cliqueNextVertices_lower_of_complement_bounded {G : Hypergraph V (r + 1)}
    {θ : ℝ} (hG : IsGraphBounded (complete V (r + 1) \ G) θ) (U : Block V k) :
    (Fintype.card V : ℝ) - k - (k.choose r : ℝ) * θ * Fintype.card V ≤
      (cliqueNextVertices G U).card := by
  have hc := (card_le_card (cliqueNextVertices_complement_subset G U)).trans
    ((card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le U.val.card))
  have hpartition := card_sdiff_add_card_eq_card (subset_univ (cliqueNextVertices G U))
  rw [card_univ] at hpartition
  rw [U.property] at hc
  have hsum : (∑ S ∈ cliqueEdges r U,
      ((neighbors (complete V (r + 1) \ G) S).card : ℝ)) ≤
        (k.choose r : ℝ) * (θ * Fintype.card V) := by
    calc
      _ ≤ ∑ _S ∈ cliqueEdges r U, θ * Fintype.card V := by
        apply sum_le_sum
        intro S _
        simpa only [card_neighbors_eq_degree] using (hG S).le
      _ = _ := by simp only [sum_const, nsmul_eq_mul, card_cliqueEdges]
  have hc' : ((univ \ cliqueNextVertices G U).card : ℝ) ≤
      k + ∑ S ∈ cliqueEdges r U, ((neighbors (complete V (r + 1) \ G) S).card : ℝ) := by
    exact_mod_cast hc
  have hp' : ((univ \ cliqueNextVertices G U).card : ℝ) +
      (cliqueNextVertices G U).card = Fintype.card V := by exact_mod_cast hpartition
  nlinarith only [hsum, hc', hp']

end Arxiv2411_18291
