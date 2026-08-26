import ErdosProblems.Erdos73.OddPathAuxiliary
import ErdosProblems.Erdos73.MatchingAugmenting

/-! An augmenting path in the doubled graph uses both copies of every nonterminal. -/

namespace Erdos73

open SimpleGraph Finset Erdos556 OddPathVertex
open Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {A : Finset V}
variable {P Q : GraphPath (oddPathAuxiliary G A)}

theorem oddPathAuxiliary_adj_of_not_matching {x y : OddPathVertex A}
    (hxy : (oddPathAuxiliary G A).Adj x y) (hM : s(x, y) ∉ oddPathBaseMatching A) :
    layer x = layer y ∧ G.Adj (projection x) (projection y) := by
  apply oddPathAuxiliary_adj_nonmate hxy
  intro he
  have hm : y = mate x := by rw [he, mate_mate]
  have hx : projection x ∉ A := by
    intro hx
    have hfix := (mate_eq_self_iff x).mpr hx
    exact hxy.ne (hm.trans hfix).symm
  exact hM ((mem_oddPathBaseMatching_iff x y).mpr ⟨hm, hx⟩)

theorem oddPathAugmenting_source_terminal
    (hP : IsMatchingAugmentingPath (oddPathBaseMatching A) P) : projection P.source ∈ A := by
  by_contra hs
  exact hP.source_uncovered ((mem_oddPathBaseMatching_support A P.source).mpr hs)

theorem oddPathAugmenting_target_terminal
    (hP : IsMatchingAugmentingPath (oddPathBaseMatching A) P) : projection P.target ∈ A := by
  by_contra ht
  exact hP.target_uncovered ((mem_oddPathBaseMatching_support A P.target).mpr ht)

theorem oddPathAugmenting_mate_edge
    (hP : IsMatchingAugmentingPath (oddPathBaseMatching A) P)
    {x : OddPathVertex A} (hx : x ∈ P.vertexSet) (hxt : projection x ∉ A) :
    s(x, mate x) ∈ P.edgeSet := by
  have hs : x ≠ P.source := fun he => hxt (he ▸ oddPathAugmenting_source_terminal hP)
  have ht : x ≠ P.target := fun he => hxt (he ▸ oddPathAugmenting_target_terminal hP)
  obtain ⟨w, hwM, hwP⟩ := hP.internal_matched x hx hs ht
  have hw := (mem_oddPathBaseMatching_iff x w).mp hwM
  simpa only [hw.1] using hwP

theorem oddPathAugmenting_mate_closed
    (hP : IsMatchingAugmentingPath (oddPathBaseMatching A) P)
    {x : OddPathVertex A} (hx : x ∈ P.vertexSet) : mate x ∈ P.vertexSet := by
  by_cases hxt : projection x ∈ A
  · simpa only [(mate_eq_self_iff x).mpr hxt] using hx
  · exact (P.endpoints_mem_vertexSet_of_edgeSet (oddPathAugmenting_mate_edge hP hx hxt)).2

theorem oddPathAugmenting_internal_nonterminal
    (hP : IsMatchingAugmentingPath (oddPathBaseMatching A) P)
    {x : OddPathVertex A} (hx : x ∈ P.vertexSet) (hs : x ≠ P.source) (ht : x ≠ P.target) :
    projection x ∉ A := by
  obtain ⟨w, hw, _⟩ := hP.internal_matched x hx hs ht
  exact ((mem_oddPathBaseMatching_iff x w).mp hw).2

theorem oddPathAugmenting_endpoints_projection_ne
    (hP : IsMatchingAugmentingPath (oddPathBaseMatching A) P) :
    projection P.source ≠ projection P.target := by
  intro he
  apply hP.endpoints_ne
  rw [eq_original_of_terminal (oddPathAugmenting_source_terminal hP),
    eq_original_of_terminal (oddPathAugmenting_target_terminal hP)]
  exact congrArg Sum.inl he

theorem oddPathAugmenting_projection_disjoint
    (hQ : IsMatchingAugmentingPath (oddPathBaseMatching A) Q)
    (hPQ : Disjoint P.vertexSet Q.vertexSet) :
    Disjoint (P.vertexSet.image projection) (Q.vertexSet.image projection) := by
  apply Finset.disjoint_left.mpr
  intro v hvP hvQ
  obtain ⟨x, hx, hxv⟩ := Finset.mem_image.mp hvP
  obtain ⟨y, hy, hyv⟩ := Finset.mem_image.mp hvQ
  rcases projection_eq_iff.mp (hxv.trans hyv.symm) with hxy | hxy
  · exact Finset.disjoint_left.mp hPQ hx (hxy ▸ hy)
  · have hm := oddPathAugmenting_mate_closed hQ hy
    exact Finset.disjoint_left.mp hPQ hx (hxy ▸ hm)

end Erdos73
