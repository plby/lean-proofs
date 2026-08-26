import ErdosProblems.Erdos547.NeighbourhoodPairing
import ErdosProblems.Erdos547.WeightedHall
import ErdosProblems.Erdos547.LeafExtension

/-!
# Restoring many leaves after an escape-compatible core embedding
-/

namespace Erdos547

open Finset SimpleGraph
open scoped SimpleGraph

open scoped Classical in
theorem isContained_of_small_core_and_escape {U V : Type*} [Fintype U] [Fintype V]
    [Nonempty V] (T : SimpleGraph U) (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Set U) [Fintype S] (hS : (T.induce S).IsTree)
    (parent : (Sᶜ : Set U) → S)
    (hp : ∀ x : (Sᶜ : Set U), ∀ y, T.Adj x.val y → y = (parent x).val)
    (m d k b : ℕ) (horder : Fintype.card U = m + 1)
    (hsize : Fintype.card S ≤ k) (hdk : d < k) (hroom : k + d ≤ m)
    (hcore : 4 * (Fintype.card S + d) ≤ m) (hb : 4 * b ≤ m)
    (hweights : ∀ u : S, parentWeight parent u ≤ b)
    (hdegree : ∀ z, m ≤ G.degree z + d)
    (hescape : ∀ x, G.degree x ≤ m → ∀ a, k ≤ ((G.neighborFinset a).filter
      fun z ↦ k ≤ (G.neighborFinset z \ G.neighborFinset x).card).card) : T ⊑ G := by
  classical
  obtain ⟨P, hP, hPweight⟩ := exists_weighted_vertex_pairing (Finset.univ : Finset S)
    (parentWeight parent) b (fun u _ ↦ hweights u)
  obtain ⟨e, hepair⟩ := exists_copy_with_paired_neighbourhoods G (T.induce S) hS P hP
    m d k hsize hdk hroom hdegree hescape
  let used : Finset V := Finset.univ.image e
  let candidates (u : S) := G.neighborFinset (e u) \ used
  have hused : used.card = Fintype.card S := by
    simpa [used] using Finset.card_image_of_injective
      (Finset.univ : Finset S) e.injective
  have hparts : Fintype.card S + Fintype.card (Sᶜ : Set U) = m + 1 := by
    rw [← horder, ← Fintype.card_sum]
    exact Fintype.card_congr (Equiv.Set.sumCompl S)
  have hsingle : ∀ u : S, Fintype.card (Sᶜ : Set U) + b ≤ 2 * (candidates u).card := by
    intro u
    have hdeg := hdegree (e u)
    have hbound := degree_add_one_le_unused_add_used (G := G) used (e u)
      (Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩)
    change G.degree (e u) + 1 ≤ (candidates u).card + used.card at hbound
    omega
  have hpair : ∀ u v : S, P.Adj u v →
      Fintype.card (Sᶜ : Set U) ≤ (candidates u ∪ candidates v).card := by
    intro u v huv
    have hlarge := hepair u v huv
    let N := G.neighborFinset (e u) ∪ G.neighborFinset (e v)
    have hcard := Finset.card_sdiff_add_card_inter N used
    have hinter : (N ∩ used).card ≤ used.card := Finset.card_le_card Finset.inter_subset_right
    have hdiff : N \ used = candidates u ∪ candidates v := by
      ext z
      simp only [N, candidates, Finset.mem_sdiff, Finset.mem_union]
      tauto
    rw [hdiff] at hcard
    change m < N.card at hlarge
    omega
  have hweight : ∀ J : Finset S, (∀ u ∈ J, ∀ v ∈ J, ¬ P.Adj u v) →
      2 * (∑ u ∈ J, parentWeight parent u) ≤ Fintype.card (Sᶜ : Set U) + b := by
    intro J hJ
    have h := hPweight J (Finset.subset_univ J) hJ
    rwa [sum_parentWeight] at h
  obtain ⟨f, hf, hmem⟩ := exists_leaf_assignment_of_pairing parent P b candidates
    hweight hsingle hpair
  obtain ⟨g, _⟩ := extend_copy_of_leaf_assignment S parent hp e f hf (by
    intro x y hxy
    have hnot := (Finset.mem_sdiff.mp (hmem x)).2
    exact hnot (Finset.mem_image.mpr ⟨y, Finset.mem_univ _, hxy.symm⟩)) (by
    intro x
    exact (G.mem_neighborFinset _ _).mp (Finset.mem_sdiff.mp (hmem x)).1)
  exact ⟨g⟩

end Erdos547

#print axioms Erdos547.isContained_of_small_core_and_escape
