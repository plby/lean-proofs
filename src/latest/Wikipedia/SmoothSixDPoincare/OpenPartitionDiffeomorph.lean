import Wikipedia.SmoothSixDPoincare.OpenSubtypePartialDiffeomorph

/-! # A disjoint open partition is a native smooth disjoint-sum decomposition -/

noncomputable section

open Set Function Topology TopologicalSpace Filter
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.OpenPartition

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace X] [ChartedSpace H X]
  (U V : Opens X) (hdisjoint : Disjoint (U : Set X) V) (hcover : (U : Set X) ∪ V = univ)

include hdisjoint hcover

theorem sumVal_bijective : Bijective (Sum.elim (Subtype.val : U → X) (Subtype.val : V → X)) := by
  constructor
  · intro x y h
    cases x with
    | inl x =>
        cases y with
        | inl y => exact congrArg Sum.inl (Subtype.ext h)
        | inr y =>
            change x.val = y.val at h
            exact False.elim (disjoint_left.mp hdisjoint x.property (h.symm ▸ y.property))
    | inr x =>
        cases y with
        | inl y =>
            change x.val = y.val at h
            exact False.elim (disjoint_left.mp hdisjoint y.property (h ▸ x.property))
        | inr y => exact congrArg Sum.inr (Subtype.ext h)
  · intro x
    have hx : x ∈ (U : Set X) ∪ V := hcover ▸ mem_univ x
    rcases hx with h | h
    · exact ⟨Sum.inl ⟨x, h⟩, rfl⟩
    · exact ⟨Sum.inr ⟨x, h⟩, rfl⟩

def diffeomorph : Diffeomorph I I (U ⊕ V) X ∞ := by
  let e := Equiv.ofBijective (Sum.elim (Subtype.val : U → X) (Subtype.val : V → X))
    (sumVal_bijective U V hdisjoint hcover)
  refine {
    toEquiv := e
    contMDiff_toFun := contMDiff_subtype_val.sumElim contMDiff_subtype_val
    contMDiff_invFun := ?_ }
  intro x
  have hx : x ∈ (U : Set X) ∪ V := hcover ▸ mem_univ x
  rcases hx with hx | hx
  · let _ : Nonempty U := ⟨⟨x, hx⟩⟩
    let p := PartialChart.openInclusion (I := I) U
    have hp : x ∈ p.target := by rw [PartialChart.openInclusion_target]; exact hx
    have hs : ContMDiffAt I I ∞ (fun y => Sum.inl (p.symm y) : X → U ⊕ V) x :=
      ContMDiff.inl.contMDiffAt.comp x
        (p.symm.contMDiffOn.contMDiffAt (p.open_target.mem_nhds hp))
    apply hs.congr_of_eventuallyEq
    filter_upwards [U.isOpen.mem_nhds hx] with y hy
    apply e.injective
    exact (e.apply_symm_apply y).trans (PartialChart.openInclusion_symm_coe (I := I) U hy).symm
  · let _ : Nonempty V := ⟨⟨x, hx⟩⟩
    let p := PartialChart.openInclusion (I := I) V
    have hp : x ∈ p.target := by rw [PartialChart.openInclusion_target]; exact hx
    have hs : ContMDiffAt I I ∞ (fun y => Sum.inr (p.symm y) : X → U ⊕ V) x :=
      ContMDiff.inr.contMDiffAt.comp x
        (p.symm.contMDiffOn.contMDiffAt (p.open_target.mem_nhds hp))
    apply hs.congr_of_eventuallyEq
    filter_upwards [V.isOpen.mem_nhds hx] with y hy
    apply e.injective
    exact (e.apply_symm_apply y).trans (PartialChart.openInclusion_symm_coe (I := I) V hy).symm

theorem diffeomorph_inl (x : U) :
    diffeomorph (I := I) U V hdisjoint hcover (Sum.inl x) = x.val := rfl

theorem diffeomorph_inr (x : V) :
    diffeomorph (I := I) U V hdisjoint hcover (Sum.inr x) = x.val := rfl

end Wikipedia.SmoothSixDPoincare.OpenPartition
