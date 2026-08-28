import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyScalars
import Wikipedia.HopfProblem.CuspNormalizationSheafReducedSheaf
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Pointwise scalar endomorphisms of actual sheaves

The scalar ring homomorphisms below act on existing section groups.
Restriction compatibility is proved for the original section maps.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyScalarResolution

section Pointwise

variable {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X)
  [∀ U, Module ℂ (F.presheaf.obj U)]
  (hres : ∀ {U V} (h : U ⟶ V) (c : ℂ) (s : F.presheaf.obj U),
    F.presheaf.map h (c • s) = c • F.presheaf.map h s)

/-- Actual multiplication of sections by a complex constant, as a sheaf map. -/
def pointwiseScalarMap (c : ℂ) : F ⟶ F where
  hom :=
    { app U := (ModuleCat.of ℂ (F.presheaf.obj U)).smul c
      naturality U V h := by
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro s
        exact (hres h c s).symm }

@[simp] theorem pointwiseScalarMap_apply (c : ℂ) (U) (s : F.presheaf.obj U) :
    (pointwiseScalarMap F hres c).hom.app U s = c • s := rfl

/-- The actual scalar maps form a ring homomorphism to the sheaf endomorphisms. -/
def pointwiseScalarEnd : ℂ →+* End F where
  toFun := pointwiseScalarMap F hres
  map_one' := by
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    exact (ModuleCat.of ℂ (F.presheaf.obj U)).smul.map_one
  map_mul' c d := by
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    exact (ModuleCat.of ℂ (F.presheaf.obj U)).smul.map_mul c d
  map_zero' := by
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    exact (ModuleCat.of ℂ (F.presheaf.obj U)).smul.map_zero
  map_add' c d := by
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    exact (ModuleCat.of ℂ (F.presheaf.obj U)).smul.map_add c d

end Pointwise

section Reduced

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℂ E H) (S : Set M)

/-- Restriction of actual reduced holomorphic functions is pointwise complex linear. -/
theorem reduced_restriction_smul {U V} (h : U ⟶ V) (c : ℂ)
    (s : (SheafReduced.additiveSheaf I S).presheaf.obj U) :
    (SheafReduced.additiveSheaf I S).presheaf.map h (c • s) =
      c • (SheafReduced.additiveSheaf I S).presheaf.map h s :=
  (SheafReduced.restrictionAlgHom I S (leOfHom h.unop)).toLinearMap.map_smul c s

/-- Actual pointwise scalars on the independently defined reduced sheaf. -/
def reducedScalarEnd : ℂ →+* End (SheafReduced.additiveSheaf I S) :=
  pointwiseScalarEnd (SheafReduced.additiveSheaf I S) (reduced_restriction_smul I S)

@[simp] theorem reducedScalarEnd_apply (c : ℂ) (U)
    (s : (SheafReduced.additiveSheaf I S).presheaf.obj U) :
    (reducedScalarEnd I S c).hom.app U s = c • s := rfl

end Reduced

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyScalarResolution
