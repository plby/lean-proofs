import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyOpenRestrictionExact
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyBiholomorphBasic

/-!
# Literal flattening of nested open holomorphic domains

An actual open `W` in an actual open submanifold `U` has the same points
as its actual image open in the ambient manifold. Dropping the two nested
subtype tags and restoring them give inverse analytic maps in the actual
induced charts. Composition with these maps identifies the genuine
holomorphic section rings, without an analytic or sheaf-isomorphism premise.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.HolomorphicRestriction

section Opens

variable {M : Type} [TopologicalSpace M]

/-- The literal image open used by the actual open-restriction functor. -/
abbrev imageOpen (U : Opens M) (W : Opens U) : Opens M :=
  (OpenRestriction.openImage (X := TopCat.of M) U).obj W

theorem mem_imageOpen_iff (U : Opens M) (W : Opens U) (x : U) :
    (x : M) ∈ imageOpen U W ↔ x ∈ W := by
  constructor
  · rintro ⟨y, hy, he⟩
    have hyx : y = x := Subtype.ext he
    exact hyx ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The actual equivalence of nested-open points and ambient-image points. -/
def flattenEquiv (U : Opens M) (W : Opens U) : W ≃ imageOpen U W where
  toFun x := ⟨x.val.val, ⟨x.val, x.property, rfl⟩⟩
  invFun x :=
    ⟨⟨x, OpenRestriction.openImage_obj_le (X := TopCat.of M) U W x.property⟩,
      (mem_imageOpen_iff U W _).mp x.property⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

@[simp] theorem flattenEquiv_apply (U : Opens M) (W : Opens U) (x : W) :
    (flattenEquiv U W x : M) = x.val.val := rfl

@[simp] theorem flattenEquiv_symm_apply (U : Opens M) (W : Opens U) (x : imageOpen U W) :
    ((flattenEquiv U W).symm x).val.val = (x : M) := rfl

end Opens

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  {M : Type} [TopologicalSpace M] [ChartedSpace H M]

/-- The literal nested-subtype equivalence is genuinely analytic in both
directions for the actual induced manifold charts. -/
def flattenBiholomorph (U : Opens M) (W : Opens U) :
    Diffeomorph I I W (imageOpen U W) ω where
  toEquiv := flattenEquiv U W
  contMDiff_toFun x := by
    apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp
    exact (contMDiff_subtype_val (I := I) (U := U)).contMDiffAt.comp x
      (contMDiff_subtype_val (I := I) (U := W)).contMDiffAt
  contMDiff_invFun x := by
    apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp
    apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp
    exact (contMDiff_subtype_val (I := I) (U := imageOpen U W)).contMDiffAt

@[simp] theorem flattenBiholomorph_apply (U : Opens M) (W : Opens U) (x : W) :
    (flattenBiholomorph I U W x : M) = x.val.val := rfl

@[simp] theorem flattenBiholomorph_symm_apply (U : Opens M) (W : Opens U)
    (x : imageOpen U W) : ((flattenBiholomorph I U W).symm x).val.val = (x : M) := rfl

/-- Literal composition gives the actual complex-algebra identification
of holomorphic functions on the two actual open submanifolds. -/
def sectionEquiv (U : Opens M) (W : Opens U) :
    HolomorphicFunctionSheaf.Section I M (imageOpen U W) ≃ₐ[ℂ]
      HolomorphicFunctionSheaf.Section I U W where
  toFun f := ⟨fun x => f (flattenBiholomorph I U W x),
    f.contMDiff.comp (flattenBiholomorph I U W).contMDiff⟩
  invFun f := ⟨fun x => f ((flattenBiholomorph I U W).symm x),
    f.contMDiff.comp (flattenBiholomorph I U W).symm.contMDiff⟩
  left_inv f := ContMDiffMap.ext fun x =>
    congrArg f ((flattenBiholomorph I U W).apply_symm_apply x)
  right_inv f := ContMDiffMap.ext fun x =>
    congrArg f ((flattenBiholomorph I U W).symm_apply_apply x)
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp] theorem sectionEquiv_apply (U : Opens M) (W : Opens U)
    (f : HolomorphicFunctionSheaf.Section I M (imageOpen U W)) (x : W) :
    sectionEquiv I U W f x = f (flattenBiholomorph I U W x) := rfl

@[simp] theorem sectionEquiv_symm_apply (U : Opens M) (W : Opens U)
    (f : HolomorphicFunctionSheaf.Section I U W) (x : imageOpen U W) :
    (sectionEquiv I U W).symm f x = f ((flattenBiholomorph I U W).symm x) := rfl

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.HolomorphicRestriction
