import Wikipedia.HopfProblem.HolomorphicFunctionSheafCohomologyZeroBasic
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Actual holomorphic sections under a biholomorphism

An actual biholomorphism restricts to a biholomorphism between the
inverse image of any actual open set and that open set. Composition with
these genuine inverse maps gives the complex-algebra equivalence of
actual holomorphic section rings. No local-function identification is
supplied as a premise.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.Biholomorph

variable {E E' H H' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℂ E H} {J : ModelWithCorners ℂ E' H'}
  {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace H' N]
  (e : Diffeomorph I J M N ω)

/-- The genuine inverse image open set. -/
def preimageOpen (U : Opens N) : Opens M :=
  ⟨e ⁻¹' (U : Set N), U.isOpen.preimage e.continuous⟩

/-- The actual given biholomorphism on the two corresponding open
submanifolds, with the actual inverse restricted to the same sets. -/
def restricted (U : Opens N) : Diffeomorph I J (preimageOpen e U) U ω where
  toEquiv :=
    { toFun x := ⟨e x, x.property⟩
      invFun y := ⟨e.symm y, by
        change e (e.symm y) ∈ U
        simpa only [e.apply_symm_apply] using y.property⟩
      left_inv x := Subtype.ext (e.symm_apply_apply x)
      right_inv y := Subtype.ext (e.apply_symm_apply y) }
  contMDiff_toFun x := by
    apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp
    exact e.contMDiffAt.comp x contMDiff_subtype_val.contMDiffAt
  contMDiff_invFun y := by
    apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp
    exact e.symm.contMDiffAt.comp y contMDiff_subtype_val.contMDiffAt

@[simp] theorem restricted_apply (U : Opens N) (x : preimageOpen e U) :
    (restricted e U x : N) = e x := rfl

@[simp] theorem restricted_symm_apply (U : Opens N) (y : U) :
    ((restricted e U).symm y : M) = e.symm y := rfl

/-- Literal composition gives the actual complex-algebra equivalence
of holomorphic functions on the corresponding open sets. -/
def sectionPullback (U : Opens N) :
    HolomorphicFunctionSheaf.Section J N U ≃ₐ[ℂ]
      HolomorphicFunctionSheaf.Section I M (preimageOpen e U) where
  toFun f := ⟨fun x => f (restricted e U x), f.contMDiff.comp (restricted e U).contMDiff⟩
  invFun f := ⟨fun y => f ((restricted e U).symm y),
    f.contMDiff.comp (restricted e U).symm.contMDiff⟩
  left_inv f := ContMDiffMap.ext fun y => congrArg f ((restricted e U).apply_symm_apply y)
  right_inv f := ContMDiffMap.ext fun x => congrArg f ((restricted e U).symm_apply_apply x)
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp] theorem sectionPullback_apply (U : Opens N)
    (f : HolomorphicFunctionSheaf.Section J N U) (x : preimageOpen e U) :
    sectionPullback e U f x = f (restricted e U x) := rfl

@[simp] theorem sectionPullback_symm_apply (U : Opens N)
    (f : HolomorphicFunctionSheaf.Section I M (preimageOpen e U)) (y : U) :
    (sectionPullback e U).symm f y = f ((restricted e U).symm y) := rfl

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.Biholomorph
