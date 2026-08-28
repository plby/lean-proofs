import ErdosProblems.Erdos577.FullLeafEqualitySets

/-! Sparse coverage avoids the matching endpoints; uniqueness counts every incidence once. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}
variable (h : Configuration c p s a y)

include h

lemma Configuration.matched_sets_disjoint :
    Disjoint (FullLeafEquality.matchedFirst p s a y) (FullLeafEquality.matchedSecond p s a y) :=
  h.triple_second_disjoint.mono (filter_subset _ _) (filter_subset _ _)

lemma Configuration.matched_union_card {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k) :
    (FullLeafEquality.matchedFirst p s a y ∪ FullLeafEquality.matchedSecond p s a y).card =
      2 * contacts G (s.erase y) (insert (p.vertices 3) a) := by
  rw [card_union_of_disjoint h.matched_sets_disjoint,
    h.matched_first_card hcard hn, h.matched_second_card hcard hn, two_mul]

lemma Configuration.covered_subset_unmatched {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k) :
    FullLeafEquality.covered c p s a y ⊆
      ((s.erase y) ∪ insert (p.vertices 3) a) \
        (FullLeafEquality.matchedFirst p s a y ∪ FullLeafEquality.matchedSecond p s a y) := by
  intro v hv
  obtain ⟨j, hj, hvj⟩ := FullLeafEquality.mem_covered.mp hv
  obtain ⟨⟨hj, hjs, hja⟩, hheavy⟩ := FullLeafEquality.mem_heavy.mp hj
  refine mem_sdiff.mpr ⟨hvj.1.elim (fun hh ↦ mem_union_left _ hh.1)
    (fun hh ↦ mem_union_right _ hh.1), ?_⟩
  intro hmatch
  rcases mem_union.mp hmatch with hfirst | hsecond
  · obtain ⟨hvFirst, hpos⟩ := mem_filter.mp hfirst
    obtain ⟨u, hu⟩ := card_pos.mp hpos
    obtain ⟨huSecond, hvu⟩ := mem_filter.mp hu
    exact (h.matching_endpoints_not_sparse hcard hn hj hjs hja hheavy
      hvFirst huSecond hvu).1 hvj
  · obtain ⟨hvSecond, hpos⟩ := mem_filter.mp hsecond
    obtain ⟨u, hu⟩ := card_pos.mp hpos
    obtain ⟨huFirst, hvu⟩ := mem_filter.mp hu
    exact (h.matching_endpoints_not_sparse hcard hn hj hjs hja hheavy
      huFirst hvSecond hvu.symm).2 hvj

lemma Configuration.unmatched_card {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k) :
    (((s.erase y) ∪ insert (p.vertices 3) a) \
      (FullLeafEquality.matchedFirst p s a y ∪ FullLeafEquality.matchedSecond p s a y)).card =
      8 - 2 * contacts G (s.erase y) (insert (p.vertices 3) a) := by
  have hs : FullLeafEquality.matchedFirst p s a y ∪ FullLeafEquality.matchedSecond p s a y ⊆
      (s.erase y) ∪ insert (p.vertices 3) a :=
    union_subset_union (filter_subset _ _) (filter_subset _ _)
  rw [card_sdiff_of_subset hs, h.sparse_pool_card, h.matched_union_card hcard hn]

theorem Configuration.sparse_coverage_bound {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k) :
    (FullLeafEquality.covered c p s a y).card +
      2 * contacts G (s.erase y) (insert (p.vertices 3) a) ≤ 8 := by
  have hb := card_le_card (h.covered_subset_unmatched hcard hn)
  rw [h.unmatched_card hcard hn] at hb
  have hrho := h.matching_contacts_le_three hcard hn
  omega

theorem Configuration.covered_eq_unmatched {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (heq : (FullLeafEquality.covered c p s a y).card +
      2 * contacts G (s.erase y) (insert (p.vertices 3) a) = 8) :
    FullLeafEquality.covered c p s a y =
      ((s.erase y) ∪ insert (p.vertices 3) a) \
        (FullLeafEquality.matchedFirst p s a y ∪ FullLeafEquality.matchedSecond p s a y) := by
  apply eq_of_subset_of_card_le (h.covered_subset_unmatched hcard hn)
  rw [h.unmatched_card hcard hn]
  omega

omit h in
theorem Maximal.covered_card (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k) :
    (FullLeafEquality.covered c p s a y).card =
      ∑ j ∈ FullLeafEquality.heavy c p s a, (FullLeafEquality.attachedVertices p s a y j).card := by
  classical
  apply card_biUnion
  intro j hj l hl hjl
  obtain ⟨⟨hj, hjs, hja⟩, hjheavy⟩ := FullLeafEquality.mem_heavy.mp hj
  obtain ⟨⟨hl, hls, hla⟩, hlheavy⟩ := FullLeafEquality.mem_heavy.mp hl
  apply disjoint_left.mpr
  intro v hvj hvl
  exact hjl (hm.sparse_attachment_unique hcard hn hj hjs hja hl hls hla hjheavy hlheavy
    (FullLeafEquality.mem_attachedVertices.mp hvj) (FullLeafEquality.mem_attachedVertices.mp hvl))

end Erdos577.FullLeafCore
