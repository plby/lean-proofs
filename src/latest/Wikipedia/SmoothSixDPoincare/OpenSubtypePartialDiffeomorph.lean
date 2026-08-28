import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphProduct

/-!
# Native open-submanifold inclusions and exact smooth open embeddings

The inclusion of an open submanifold is a partial diffeomorphism on its
entire domain. A smooth realization of an open embedding also gives the
original topological partial homeomorphism its native smooth structure,
without changing either of its total point maps.
-/

noncomputable section

open Set Function Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.PartialChart

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace X] [ChartedSpace H X]

def openInclusion (U : Opens X) [Nonempty U] : PartialDiffeomorph I I U X ∞ := by
  let h : OpenPartialHomeomorph U X := U.isOpen.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
  refine {
    toPartialEquiv := h.toPartialEquiv
    open_source := h.open_source
    open_target := h.open_target
    contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
    contMDiffOn_invFun := ?_ }
  change ContMDiffOn I I ∞ h.symm h.target
  intro x hx
  apply (ContMDiffWithinAt.subtypeVal_comp_iff U h.symm h.target x).mp
  apply contMDiffWithinAt_id.congr_of_mem (fun y hy => ?_) hx
  exact h.right_inv hy

theorem openInclusion_apply (U : Opens X) [Nonempty U] (x : U) :
    openInclusion (I := I) U x = x.val := rfl

theorem openInclusion_source (U : Opens X) [Nonempty U] :
    (openInclusion (I := I) U).source = univ := rfl

theorem openInclusion_target (U : Opens X) [Nonempty U] :
    (openInclusion (I := I) U).target = U := by
  change U.isOpen.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph.target = U
  rw [IsOpenEmbedding.toOpenPartialHomeomorph_target]
  exact Subtype.range_coe

theorem openInclusion_symm_coe (U : Opens X) [Nonempty U] {x : X} (hx : x ∈ U) :
    ((openInclusion (I := I) U).symm x).val = x := by
  have h := (openInclusion (I := I) U).right_inv
    (show x ∈ (openInclusion (I := I) U).target by rw [openInclusion_target]; exact hx)
  exact h

variable {F K Y : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  [TopologicalSpace Y] [ChartedSpace K Y] [Nonempty X]

def fromOpenEmbedding {i : X → Y} (hi : IsOpenEmbedding i)
    (p : PartialDiffeomorph I J X Y ∞) (hsource : p.source = univ)
    (hpoint : ∀ x, p x = i x) : PartialDiffeomorph I J X Y ∞ := by
  let h := hi.toOpenPartialHomeomorph
  refine {
    toPartialEquiv := h.toPartialEquiv
    open_source := h.open_source
    open_target := h.open_target
    contMDiffOn_toFun := ?_
    contMDiffOn_invFun := ?_ }
  · change ContMDiffOn I J ∞ i univ
    rw [← hsource]
    exact p.contMDiffOn.congr (fun x _ => (hpoint x).symm)
  · change ContMDiffOn J I ∞ h.symm h.target
    have ht : p.target = range i := by
      change p.toOpenPartialHomeomorph.target = range i
      rw [← p.toOpenPartialHomeomorph.image_source_eq_target]
      change p '' p.source = range i
      rw [hsource, image_univ]
      exact congrArg range (funext hpoint)
    rw [IsOpenEmbedding.toOpenPartialHomeomorph_target, ← ht]
    apply p.symm.contMDiffOn.congr
    intro y hy
    obtain ⟨x, rfl⟩ := show y ∈ range i from ht ▸ hy
    change hi.toOpenPartialHomeomorph.symm (i x) = p.symm (i x)
    rw [hi.toOpenPartialHomeomorph_left_inv, ← hpoint x]
    exact (p.left_inv (hsource.symm ▸ mem_univ x)).symm

theorem fromOpenEmbedding_toOpenPartialHomeomorph {i : X → Y} (hi : IsOpenEmbedding i)
    (p : PartialDiffeomorph I J X Y ∞) (hsource : p.source = univ)
    (hpoint : ∀ x, p x = i x) :
    (fromOpenEmbedding hi p hsource hpoint).toOpenPartialHomeomorph =
      hi.toOpenPartialHomeomorph := rfl

end Wikipedia.SmoothSixDPoincare.PartialChart
