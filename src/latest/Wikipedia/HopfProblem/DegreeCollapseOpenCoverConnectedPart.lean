import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# Each part of a connected open cover with connected overlap is path connected

In a locally path-connected ambient space, the path components of an open
part are open. The component meeting the connected overlap, together with
the other cover part, is separated from all the remaining components.
Ambient connectedness rules out those remaining components.
-/

noncomputable section

open Set Function Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.OpenCoverConnectivity

variable {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
  [LocallyPathConnectedSpace X] {U V : Set X}

theorem right_pathConnected (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) (hI : IsPathConnected (U ∩ V)) : PathConnectedSpace V := by
  classical
  let _ : LocallyPathConnectedSpace V := hV.locallyPathConnectedSpace
  obtain ⟨o, ho⟩ := hI.nonempty
  let v₀ : V := ⟨o, ho.2⟩
  let K : Set V := pathComponent v₀
  let A : Set X := Subtype.val '' K
  let D : Set X := Subtype.val '' Kᶜ
  have hA : IsOpen A := hV.isOpenEmbedding_subtypeVal.isOpenMap _ (IsClopen.pathComponent v₀).isOpen
  have hD : IsOpen D :=
    hV.isOpenEmbedding_subtypeVal.isOpenMap _ (IsClopen.pathComponent v₀).compl.isOpen
  have hdis : Disjoint (U ∪ A) D := by
    apply disjoint_left.mpr
    rintro z hz ⟨b, hb, rfl⟩
    rcases hz with hz | hz
    · have hj : JoinedIn V o b.val :=
        (hI.joinedIn o ho b.val ⟨hz, b.property⟩).mono inter_subset_right
      exact hb hj.joined_subtype
    · obtain ⟨a, ha, hab⟩ := hz
      exact hb ((Subtype.ext hab : a = b) ▸ ha)
  have hcov : (U ∪ A) ∪ D = univ := by
    apply eq_univ_of_forall
    intro z
    have hz : z ∈ U ∪ V := by rw [hcover]; trivial
    rcases hz with hz | hz
    · exact Or.inl (Or.inl hz)
    · let w : V := ⟨z, hz⟩
      by_cases hw : w ∈ K
      · exact Or.inl (Or.inr ⟨w, hw, rfl⟩)
      · exact Or.inr ⟨w, hw, rfl⟩
  have hleft : (univ : Set X) ⊆ U ∪ A :=
    isPreconnected_univ.subset_left_of_subset_union (hU.union hA) hD hdis
      (by rw [hcov]) ⟨o, mem_univ o, Or.inl ho.1⟩
  have hjoined (v : V) : Joined v₀ v := by
    by_contra hv
    have hvD : v.val ∈ D := ⟨v, hv, rfl⟩
    exact (disjoint_left.mp hdis) (hleft (mem_univ v.val)) hvD
  exact ⟨⟨v₀⟩, fun a b => (hjoined a).symm.trans (hjoined b)⟩

end Wikipedia.HopfProblem.DegreeCollapse.OpenCoverConnectivity
