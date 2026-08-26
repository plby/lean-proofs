import ErdosProblems.Erdos547.PartialEmbedding
import ErdosProblems.Erdos547.Potential

/-!
# Finishing from an exposed connected seed

A small potential ensures that every low-degree host vertex already has many
used nonneighbours. Those occupied nonneighbours provide the exact slack
needed to complete the embedding greedily.
-/

namespace Erdos547

open Finset SimpleGraph
open scoped SimpleGraph

variable {U V I : Type*}

theorem count_gt_of_exposurePotential_lt (indices : Finset I) (count : I → ℕ) (d : ℕ)
    (hsmall : exposurePotential indices count < (1 / 2 : ℝ) ^ d) {i : I} (hi : i ∈ indices) :
    d < count i := by
  have hterm : (1 / 2 : ℝ) ^ count i ≤ exposurePotential indices count := by
    change (1 / 2 : ℝ) ^ count i ≤ ∑ j ∈ indices, (1 / 2 : ℝ) ^ count j
    exact Finset.single_le_sum (f := fun j ↦ (1 / 2 : ℝ) ^ count j)
      (fun j _ ↦ by positivity) hi
  by_contra h
  have hd : count i ≤ d := by omega
  have hpow : (1 / 2 : ℝ) ^ d ≤ (1 / 2 : ℝ) ^ count i :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hd
  exact (not_lt_of_ge (hpow.trans hterm)) hsmall

/-- Used nonneighbours do not consume the neighbourhood available for the
next tree vertex. -/
theorem exists_unused_neighbor_of_nonneighbors [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (used : Finset V) (z : V)
    (hcount : used.card < G.degree z + (used.filter fun w ↦ ¬ G.Adj z w).card) :
    ∃ w, G.Adj z w ∧ w ∉ used := by
  classical
  by_contra h
  have hsub : G.neighborFinset z ⊆ used := by
    intro w hw
    by_contra hwu
    exact h ⟨w, (G.mem_neighborFinset z w).mp hw, hwu⟩
  have heq : used.filter (G.Adj z) = G.neighborFinset z := by
    ext w
    simp only [Finset.mem_filter, G.mem_neighborFinset]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨hsub ((G.mem_neighborFinset z w).mpr h), h⟩⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := used) (p := G.Adj z)
  rw [heq, G.card_neighborFinset_eq_degree] at hsplit
  omega

open scoped Classical in
/-- Complete a connected tree seed whose nonneighbour-exposure potential is
below the threshold dictated by the host's minimum-degree deficit. -/
theorem extend_of_small_exposurePotential [Fintype U] [Fintype V]
    (T : SimpleGraph U) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hT : T.IsTree) (m d : ℕ) (horder : Fintype.card U = m + 1)
    (hdegree : ∀ z, m ≤ G.degree z + d)
    (S : Finset U) (hS : (T.induce (S : Set U)).Connected)
    (e : (T.induce (S : Set U)).Copy G)
    (hpotential : exposurePotential (Finset.univ.filter fun z ↦ G.degree z ≤ m)
      (fun z ↦ ((Finset.univ.image e).filter fun w ↦ ¬ G.Adj z w).card) < (1 / 2 : ℝ) ^ d) :
    ∃ f : T.Copy G, ∀ x : (S : Set U), f x.val = e x := by
  classical
  obtain ⟨f, hfe, _⟩ := extend_connected_copy hT S hS e (fun _ _ ↦ True) (fun _ ↦ trivial) (by
    intro Q hSQ hconn f hfe _ hQlt p v hv hpv
    let used : Finset V := Finset.univ.image f
    let seed : Finset V := Finset.univ.image e
    have hused : used.card = Q.card := by
      simpa [used] using Finset.card_image_of_injective
        (Finset.univ : Finset (Q : Set U)) f.injective
    have hseed : seed ⊆ used := by
      intro w hw
      obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hw
      exact Finset.mem_image.mpr
        ⟨⟨x.val, hSQ x.property⟩, Finset.mem_univ _, (hfe x).trans hx⟩
    have hcount : used.card < G.degree (f p) + (used.filter fun w ↦ ¬ G.Adj (f p) w).card := by
      by_cases hlow : G.degree (f p) ≤ m
      · have hfp : f p ∈ Finset.univ.filter (fun z ↦ G.degree z ≤ m) := by simp [hlow]
        have hlarge := count_gt_of_exposurePotential_lt _ _ d hpotential hfp
        have hlarge' : d < (seed.filter fun w ↦ ¬ G.Adj (f p) w).card := by
          convert hlarge using 1
        have hmono : (seed.filter fun w ↦ ¬ G.Adj (f p) w).card ≤
            (used.filter fun w ↦ ¬ G.Adj (f p) w).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ hseed)
        have hd := hdegree (f p)
        omega
      · omega
    obtain ⟨w, hw, hwu⟩ := exists_unused_neighbor_of_nonneighbors G used (f p) hcount
    refine ⟨w, hw, ?_, trivial⟩
    intro x hx
    exact hwu (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, hx⟩))
  exact ⟨f, hfe⟩

end Erdos547

#print axioms Erdos547.extend_of_small_exposurePotential
