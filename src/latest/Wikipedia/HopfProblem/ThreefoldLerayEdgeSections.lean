import Wikipedia.HopfProblem.ThreefoldLerayEdgeBasic
import Wikipedia.HopfProblem.ThreefoldLerayEdgeGlobalSections

/-!
# The actual threefold Leray edge into literal global sections

The target is the section group of the genuine first higher direct image
on the top open set of the actual base. Its scalar multiplication is
literal evaluation of the genuinely derived scalar sheaf endomorphisms.
The forward comparison is the original Leray edge followed by Mathlib's
native degree-zero/global-section comparison.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.LerayEdge

open HolomorphicPushforward

attribute [local instance] chartedSpace

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- Literal global sections of the actual derived sheaf `R¹ f_* O_X`. -/
abbrev HigherGlobalSections : Type := firstHigherDirectImage.obj.obj (op ⊤)

/-- The actual derived scalar sheaf maps, evaluated on global sections. -/
instance higherGlobalSectionsModule : Module ℂ HigherGlobalSections :=
  GlobalSections.sectionsModule firstHigherDirectImage firstHigherScalarEnd

/-- Scalar multiplication is exactly the original derived scalar sheaf
endomorphism on the top open set. -/
theorem higherGlobalSections_smul (c : ℂ) (s : HigherGlobalSections) :
    c • s = ((SheafHigherDirectImage.functor sphereProjectionMap 1).map
      (HolomorphicFunctionSheaf.scalarSheafEnd IF Space c)).hom.app (op ⊤) s := rfl

/-- Native degree-zero cohomology and literal global sections have their
original scalar-compatible comparison. -/
def higherH0GlobalLinearEquiv : HigherH0 ≃ₗ[ℂ] HigherGlobalSections :=
  GlobalSections.cohomologyZeroLinearEquiv firstHigherDirectImage firstHigherScalarEnd

@[simp] theorem higherH0GlobalLinearEquiv_apply (x : HigherH0) :
    higherH0GlobalLinearEquiv x = CategoryTheory.Sheaf.H.equiv₀ firstHigherDirectImage
      (show IsTerminal (⊤ : Opens RiemannSphere) from isTerminalTop) x := rfl

/-- The native Leray edge, read as a literal global section. -/
def globalEdge : HolomorphicH1 →+ HigherGlobalSections :=
  (CategoryTheory.Sheaf.H.equiv₀ firstHigherDirectImage
    (show IsTerminal (⊤ : Opens RiemannSphere) from isTerminalTop)).toAddMonoidHom.comp
      (SheafLerayLowDegrees.edge sphereProjectionMap totalAdditiveSheaf)

@[simp] theorem globalEdge_apply (x : HolomorphicH1) :
    globalEdge x = CategoryTheory.Sheaf.H.equiv₀ firstHigherDirectImage
      (show IsTerminal (⊤ : Opens RiemannSphere) from isTerminalTop)
        (SheafLerayLowDegrees.edge sphereProjectionMap totalAdditiveSheaf x) := rfl

/-- Unconditionally, the original degree-one holomorphic cohomology of
the threefold is complex-linearly equivalent to global sections of its
genuine first higher direct image, by the original Leray edge. -/
def edgeGlobalSectionsLinearEquiv : HolomorphicH1 ≃ₗ[ℂ] HigherGlobalSections :=
  nativeEdgeLinearEquiv.trans higherH0GlobalLinearEquiv

/-- The forward map is exactly the native Leray edge followed by the
original native `H⁰` comparison, with no replacement target or map. -/
@[simp] theorem edgeGlobalSectionsLinearEquiv_apply (x : HolomorphicH1) :
    edgeGlobalSectionsLinearEquiv x = CategoryTheory.Sheaf.H.equiv₀ firstHigherDirectImage
      (show IsTerminal (⊤ : Opens RiemannSphere) from isTerminalTop)
        (SheafLerayLowDegrees.edge sphereProjectionMap totalAdditiveSheaf x) := rfl

@[simp] theorem edgeGlobalSectionsLinearEquiv_toAddMonoidHom :
    edgeGlobalSectionsLinearEquiv.toAddEquiv.toAddMonoidHom = globalEdge := rfl

/-- Inverting the native global-section comparison recovers precisely
the original cohomological edge map. -/
theorem edgeGlobalSectionsLinearEquiv_nativeEdge (x : HolomorphicH1) :
    higherH0GlobalLinearEquiv.symm (edgeGlobalSectionsLinearEquiv x) =
      SheafLerayLowDegrees.edge sphereProjectionMap totalAdditiveSheaf x :=
  higherH0GlobalLinearEquiv.symm_apply_apply _

@[simp] theorem edgeGlobalSectionsLinearEquiv_symm_apply (s : HigherGlobalSections) :
    edgeGlobalSectionsLinearEquiv.symm s = nativeEdgeLinearEquiv.symm
      ((CategoryTheory.Sheaf.H.equiv₀ firstHigherDirectImage
        (show IsTerminal (⊤ : Opens RiemannSphere) from isTerminalTop)).symm s) := rfl

theorem globalEdge_bijective : Function.Bijective globalEdge :=
  edgeGlobalSectionsLinearEquiv.bijective

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.LerayEdge
