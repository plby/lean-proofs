import ErdosProblems.Erdos73.OddPathBarrierSurvivors
import ErdosProblems.Erdos73.PathCliqueCut

/-! Surviving augmenting paths cannot enter the interiors of deleted components. -/

namespace Erdos73.OddPathBarrierWitness

open SimpleGraph Finset Erdos556 OddPathVertex
open Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {A : Finset V} {k : ℕ}

open scoped Classical in
theorem componentCut_distinct_mates (B : OddPathBarrierWitness G A k)
    (C : (vertexDeletedGraph (oddPathAuxiliary G A) B.removed).ConnectedComponent)
    {x y : OddPathVertex A} (hx : x ∈ B.componentCut C) (hy : y ∈ B.componentCut C)
    (hxy : x ≠ y) : y = mate x := by
  have hrep (a : OddPathVertex A) (ha : a ∈ B.componentCut C) :
      ∃ z ∈ B.representatives ∩ deletedComponentVertices C, a = z ∨ a = mate z := by
    rcases Finset.mem_union.mp ha with ha | ha
    · exact ⟨a, ha, Or.inl rfl⟩
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ha
      exact ⟨z, hz, Or.inr rfl⟩
  obtain ⟨z, hz, hxz⟩ := hrep x hx
  obtain ⟨w, hw, hyw⟩ := hrep y hy
  have hzw := B.unique C z (Finset.mem_inter.mp hz).1 w (Finset.mem_inter.mp hw).1
    (Finset.mem_inter.mp hz).2 (Finset.mem_inter.mp hw).2
  subst w
  rcases hxz with rfl | rfl <;> rcases hyw with rfl | rfl
  · exact (hxy rfl).elim
  · rfl
  · exact (mate_mate _).symm
  · exact (hxy rfl).elim

open scoped Classical in
theorem surviving_augmentingPath_supported (B : OddPathBarrierWitness G A k)
    {P : GraphPath (oddPathAuxiliary G A)}
    (hP : IsMatchingAugmentingPath (oddPathBaseMatching A) P)
    (hsurv : ∀ x ∈ P.vertexSet, projection x ∉ B.deletion) :
    P.vertexSet ⊆ B.representatives ∪ B.removed := by
  intro x hxP
  by_cases hxW : x ∈ B.removed
  · exact Finset.mem_union_right _ hxW
  · by_cases hxZ : x ∈ B.representatives
    · exact Finset.mem_union_left _ hxZ
    · obtain ⟨C, hxC⟩ := exists_deletedComponent_containing (G := oddPathAuxiliary G A) x hxW
      have hdis := P.disjoint_region_of_pathClique_cut
        (deletedComponentVertices C \ B.representatives) (B.componentCut C)
        (by
          intro hh
          exact (Finset.mem_sdiff.mp hh).2 (B.survives_terminal_mem_representatives
            (hsurv _ P.source_mem_vertexSet) (oddPathAugmenting_source_terminal hP)))
        (by
          intro hh
          exact (Finset.mem_sdiff.mp hh).2 (B.survives_terminal_mem_representatives
            (hsurv _ P.target_mem_vertexSet) (oddPathAugmenting_target_terminal hP)))
        (by
          intro a haP haS b hbP hbS hab
          exact B.component_interior_boundary C (hsurv a haP) (hsurv b hbP) haS hbS hab)
        (by
          intro a haC haP b hbC _ hab
          have hm := B.componentCut_distinct_mates C haC hbC hab
          have hat : projection a ∉ A := by
            intro ht
            exact hab (hm.trans ((mate_eq_self_iff a).mpr ht)).symm
          simpa only [hm] using oddPathAugmenting_mate_edge hP haP hat)
      exact (Finset.disjoint_left.mp hdis hxP (Finset.mem_sdiff.mpr ⟨hxC, hxZ⟩)).elim

end Erdos73.OddPathBarrierWitness
