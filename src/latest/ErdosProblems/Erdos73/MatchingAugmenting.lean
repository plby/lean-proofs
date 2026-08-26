import ErdosProblems.Erdos73.MatchingComponents

/-! Augmenting paths as simple paths whose internal vertices are matched along the path. -/

namespace Erdos73

open SimpleGraph Finset Erdos556
open Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [DecidableEq V] {G H : SimpleGraph V}

structure IsMatchingAugmentingPath (M : Finset (Sym2 V)) (P : GraphPath G) : Prop where
  endpoints_ne : P.source ≠ P.target
  source_uncovered : P.source ∉ matchingSupport M
  target_uncovered : P.target ∉ matchingSupport M
  internal_matched : ∀ v ∈ P.vertexSet, v ≠ P.source → v ≠ P.target →
    ∃ w, s(v, w) ∈ M ∧ s(v, w) ∈ P.edgeSet

theorem IsMatchingAugmentingPath.mapLe {M : Finset (Sym2 V)} {P : GraphPath G}
    (hP : IsMatchingAugmentingPath M P) (hGH : G ≤ H) :
    IsMatchingAugmentingPath M (P.mapLe hGH) := by
  refine ⟨hP.endpoints_ne, hP.source_uncovered, hP.target_uncovered, ?_⟩
  intro v hv hs ht
  rw [GraphPath.mapLe_vertexSet] at hv
  obtain ⟨w, hwM, hwP⟩ := hP.internal_matched v hv hs ht
  exact ⟨w, hwM, by simpa only [GraphPath.mapLe_edgeSet] using hwP⟩

theorem internal_matched_in_union {M N : Finset (Sym2 V)}
    (hM : EdgeMatching G M) (hN : EdgeMatching G N)
    (P : GraphPath (matchingUnion hM hN)) {v : V} (hv : v ∈ P.vertexSet)
    (hs : v ≠ P.source) (ht : v ≠ P.target) :
    (∃ w, s(v, w) ∈ M ∧ s(v, w) ∈ P.edgeSet) ∧
      (∃ w, s(v, w) ∈ N ∧ s(v, w) ∈ P.edgeSet) := by
  obtain ⟨a, b, hab, ha, hb⟩ := P.internal_neighbors hv hs ht
  have haU : s(v, a) ∈ M ∨ s(v, a) ∈ N := P.edgeSet_subset_edgeSet ha
  have hbU : s(v, b) ∈ M ∨ s(v, b) ∈ N := P.edgeSet_subset_edgeSet hb
  rcases haU with haM | haN <;> rcases hbU with hbM | hbN
  · exact (hab (matching_neighbors_unique hM haM hbM)).elim
  · exact ⟨⟨a, haM, ha⟩, ⟨b, hbN, hb⟩⟩
  · exact ⟨⟨b, hbM, hb⟩, ⟨a, haN, ha⟩⟩
  · exact (hab (matching_neighbors_unique hN haN hbN)).elim

theorem IsMatchingAugmentingPath.matched_support {M : Finset (Sym2 V)}
    {P : GraphPath G} (hP : IsMatchingAugmentingPath M P) :
    matchingSupport (M ∩ P.edgeSet) = P.vertexSet \ {P.source, P.target} := by
  ext v
  constructor
  · intro hv
    obtain ⟨e, he, hve⟩ := matchingSupport_mem.mp hv
    obtain ⟨heM, heP⟩ := Finset.mem_inter.mp he
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hve
    have hvM := matchingSupport_mem.mpr ⟨s(v, w), heM, Sym2.mem_mk_left _ _⟩
    refine Finset.mem_sdiff.mpr ⟨(P.endpoints_mem_vertexSet_of_edgeSet heP).1, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl)
    · exact hP.source_uncovered hvM
    · exact hP.target_uncovered hvM
  · intro hv
    obtain ⟨hvP, hve⟩ := Finset.mem_sdiff.mp hv
    have hs : v ≠ P.source := fun h => hve (by simp [h])
    have ht : v ≠ P.target := fun h => hve (by simp [h])
    obtain ⟨w, hwM, hwP⟩ := hP.internal_matched v hvP hs ht
    exact matchingSupport_mem.mpr ⟨s(v, w), Finset.mem_inter.mpr ⟨hwM, hwP⟩,
      Sym2.mem_mk_left _ _⟩

theorem IsMatchingAugmentingPath.odd_length {M : Finset (Sym2 V)}
    (hM : EdgeMatching G M) {P : GraphPath G} (hP : IsMatchingAugmentingPath M P) :
    Odd P.walk.length := by
  have hmatch := hM.mono (show M ∩ P.edgeSet ⊆ M from Finset.inter_subset_left)
  have hcard := hmatch.card_support
  rw [hP.matched_support] at hcard
  have hend : ({P.source, P.target} : Finset V) ⊆ P.vertexSet := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨P.source_mem_vertexSet, P.target_mem_vertexSet⟩
  have hh := Finset.card_sdiff_add_card_eq_card hend
  rw [Finset.card_pair hP.endpoints_ne, hcard] at hh
  have hvcard : P.vertexSet.card = P.walk.length + 1 := by
    exact (List.toFinset_card_of_nodup P.isPath.support_nodup).trans P.walk.length_support
  refine ⟨(M ∩ P.edgeSet).card, ?_⟩
  omega

end Erdos73
