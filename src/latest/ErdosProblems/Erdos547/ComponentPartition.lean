import ErdosProblems.Erdos547.RootedPieces

/-!
# The finite partition into induced connected components
-/

namespace Erdos547

open Finset SimpleGraph

open scoped Classical in
theorem exists_component_partition {U : Type*} [Fintype U] [DecidableEq U] (T : SimpleGraph U)
    (A : Finset U) :
    ∃ F : Finset (Finset U), F.biUnion id = A ∧
      (∀ B ∈ F, ∀ C ∈ F, B ≠ C → Disjoint B C) ∧
      ∀ B ∈ F, B ⊆ A ∧ (T.induce (B : Set U)).Connected ∧
        ∀ u ∈ B, ∀ v ∈ A, T.Adj u v → v ∈ B := by
  classical
  let piece (C : (T.induce (A : Set U)).ConnectedComponent) : Finset U :=
    (inducedComponentSet T (A : Set U) C).toFinset
  have hsub (C : (T.induce (A : Set U)).ConnectedComponent) : piece C ⊆ A :=
    fun u hu ↦ inducedComponentSet_subset T _ C (Set.mem_toFinset.mp hu)
  have hconn (C : (T.induce (A : Set U)).ConnectedComponent) :
      (T.induce (↑(piece C) : Set U)).Connected := by
    have he : (piece C : Set U) = inducedComponentSet T (A : Set U) C := Set.coe_toFinset _
    rw [he]
    exact inducedComponentSet_connected T _ C
  let F := (Finset.univ : Finset (T.induce (A : Set U)).ConnectedComponent).image piece
  refine ⟨F, ?_, ?_, ?_⟩
  · ext u
    constructor
    · intro hu
      obtain ⟨B, hB, huB⟩ := Finset.mem_biUnion.mp hu
      obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp hB
      exact hsub C huB
    · intro hu
      let v : (A : Set U) := ⟨u, hu⟩
      let C := (T.induce (A : Set U)).connectedComponentMk v
      apply Finset.mem_biUnion.mpr
      refine ⟨piece C, Finset.mem_image.mpr ⟨C, Finset.mem_univ _, rfl⟩, ?_⟩
      exact Set.mem_toFinset.mpr ⟨v, ConnectedComponent.connectedComponentMk_mem, rfl⟩
  · intro B hB D hD hBD
    obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨E, _, rfl⟩ := Finset.mem_image.mp hD
    have hCE : C ≠ E := fun he ↦ hBD (congrArg piece he)
    apply Finset.disjoint_left.mpr
    intro u huC huE
    obtain ⟨v, hvC, hvu⟩ := Set.mem_toFinset.mp huC
    obtain ⟨w, hwE, hwu⟩ := Set.mem_toFinset.mp huE
    have hvw : v = w := Subtype.ext (hvu.trans hwu.symm)
    have hdis := (T.induce (A : Set U)).pairwise_disjoint_supp_connectedComponent hCE
    exact Set.disjoint_left.mp hdis hvC (hvw.symm ▸ hwE)
  · intro B hB
    obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp hB
    refine ⟨hsub C, hconn C, ?_⟩
    intro u hu v hv huv
    exact Set.mem_toFinset.mpr (inducedComponentSet_closed T _ C
      (Set.mem_toFinset.mp hu) hv huv)

end Erdos547

#print axioms Erdos547.exists_component_partition
