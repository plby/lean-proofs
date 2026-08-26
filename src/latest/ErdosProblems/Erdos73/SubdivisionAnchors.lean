import ErdosProblems.Erdos73.SubdivisionSupports

/-! Every subdivision vertex has one pattern anchor valid in every region containing it. -/

namespace Erdos73.GraphSubdivisionModel
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

open SimpleGraph Finset

variable {W V : Type*} [Fintype W] [LinearOrder W]
variable {H : SimpleGraph W} {G : SimpleGraph V}

theorem supportOver_mono (S : GraphSubdivisionModel H G) {T R : Finset W} (hTR : T ⊆ R) :
    S.supportOver T ⊆ S.supportOver R := by
  intro x hx
  rcases (S.mem_supportOver T x).mp hx with ⟨w, hw, he⟩ | ⟨e, he, he', hx⟩
  · exact (S.mem_supportOver R x).mpr (Or.inl ⟨w, hTR hw, he⟩)
  · exact (S.mem_supportOver R x).mpr (Or.inr ⟨e, hTR he, hTR he', hx⟩)

theorem restrictCopy_vertexSet_subset_vertexSet {U : Type*} [Fintype U] [LinearOrder U]
    {F : SimpleGraph U} (S : GraphSubdivisionModel H G) (f : F.Copy H) :
    (S.restrictCopy f).vertexSet ⊆ S.vertexSet :=
  (S.restrictCopy_vertexSet_subset f).trans (S.supportOver_mono (subset_univ _))

theorem exists_support_anchor (S : GraphSubdivisionModel H G) (x : V) (hx : x ∈ S.vertexSet) :
    ∃ u : W, (∀ w, S.branchVertex w = x → w = u) ∧
      ∀ T : Finset W, x ∈ S.supportOver T → u ∈ T := by
  by_cases hb : ∃ u, S.branchVertex u = x
  · obtain ⟨u, hu⟩ := hb
    refine ⟨u, fun w hw => S.injective (hw.trans hu.symm), ?_⟩
    intro T hxT
    rcases (S.mem_supportOver T x).mp hxT with ⟨w, hw, he⟩ | ⟨e, he, he', hxe⟩
    · exact S.injective (he.trans hu.symm) ▸ hw
    · have hh := S.branch_on_path e u (hu ▸ hxe)
      exact hh.elim (fun hh => hh ▸ he) (fun hh => hh ▸ he')
  · obtain ⟨e, hxe⟩ := ((S.mem_vertexSet x).mp hx).resolve_left hb
    refine ⟨e.lo, fun w hw => (hb ⟨w, hw⟩).elim, ?_⟩
    intro T hxT
    rcases (S.mem_supportOver T x).mp hxT with ⟨w, _, hw⟩ | ⟨d, hd, hd', hxd⟩
    · exact (hb ⟨w, hw⟩).elim
    · by_cases hed : e = d
      · exact hed ▸ hd
      · obtain ⟨w, hxw, _, _⟩ := S.intersection hed x hxe hxd
        exact (hb ⟨w, hxw.symm⟩).elim

def supportAnchor (S : GraphSubdivisionModel H G) (x : {v : V // v ∈ S.vertexSet}) : W :=
  (S.exists_support_anchor x.val x.property).choose

theorem supportAnchor_mem (S : GraphSubdivisionModel H G) (x : {v : V // v ∈ S.vertexSet})
    (T : Finset W) (hx : x.val ∈ S.supportOver T) : S.supportAnchor x ∈ T :=
  (S.exists_support_anchor x.val x.property).choose_spec.2 T hx

theorem supportAnchor_branch (S : GraphSubdivisionModel H G) (w : W) :
    S.supportAnchor ⟨S.branchVertex w, (S.mem_vertexSet _).mpr (Or.inl ⟨w, rfl⟩)⟩ = w := by
  exact ((S.exists_support_anchor (S.branchVertex w)
    ((S.mem_vertexSet _).mpr (Or.inl ⟨w, rfl⟩))).choose_spec.1 w rfl).symm

theorem supportAnchor_mem_restrict_range {U : Type*} [Fintype U] [LinearOrder U]
    {F : SimpleGraph U} (S : GraphSubdivisionModel H G) (f : F.Copy H)
    (x : {v : V // v ∈ S.vertexSet}) (hx : x.val ∈ (S.restrictCopy f).vertexSet) :
    S.supportAnchor x ∈ Finset.univ.image f :=
  S.supportAnchor_mem x _ (S.restrictCopy_vertexSet_subset f hx)

theorem exists_supportAnchor_restrict_preimage {U : Type*} [Fintype U] [LinearOrder U]
    {F : SimpleGraph U} (S : GraphSubdivisionModel H G) (f : F.Copy H)
    (x : {v : V // v ∈ S.vertexSet}) (hx : x.val ∈ (S.restrictCopy f).vertexSet) :
    ∃ u : U, f u = S.supportAnchor x := by
  obtain ⟨u, _, hu⟩ := mem_image.mp (S.supportAnchor_mem_restrict_range f x hx)
  exact ⟨u, hu⟩

end
end Erdos73.GraphSubdivisionModel
