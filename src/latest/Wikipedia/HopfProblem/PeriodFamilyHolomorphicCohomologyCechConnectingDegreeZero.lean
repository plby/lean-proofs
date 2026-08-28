import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCechFibreInteger
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionSections

/-!
# The original global-section morphism and its degree-zero Ext class

The actual constant-sheaf adjunction represents each global section by
a sheaf morphism. Its local degree-one sections are literal restrictions,
and its degree-zero Ext class is exactly the inverse of the original
global-section comparison used by the Dolbeault resolution.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.CechConnecting

open HolomorphicFunctionSheaf.SphereH1 HolomorphicPicard.CechExtension
open CuspNormalization.SheafCohomologyFinitePushforward
open CuspNormalization.SheafCohomologyResolution

variable {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X)

/-- The actual representing morphism of a global section under the
native constant-sheaf adjunction. -/
def globalSectionMorphism (s : Section F (⊤ : Opens X)) : degreeSheaf X ⟶ F :=
  (homGlobalEquiv X F).symm s

/-- The representing morphism sends the original global degree-one
section to the prescribed global section. -/
theorem globalSectionMorphism_degreeOne_top (s : Section F (⊤ : Opens X)) :
    (globalSectionMorphism F s).hom.app (op (⊤ : Opens X))
        ((degreeUnit X).app (op (⊤ : Opens X)) (ULift.up (1 : ℤ))) = s :=
  (CechFibre.homGlobalEquiv_degreeUnit X F (globalSectionMorphism F s)).symm.trans
    ((homGlobalEquiv X F).apply_symm_apply s)

/-- On each actual open set, the representing morphism sends its
original degree-one section to the literal restriction of the global section. -/
theorem globalSectionMorphism_degreeOne (s : Section F (⊤ : Opens X)) (V : Opens X) :
    (globalSectionMorphism F s).hom.app (op V)
        ((degreeUnit X).app (op V) (ULift.up (1 : ℤ))) = res F le_top s := by
  let r : V ⟶ (⊤ : Opens X) := homOfLE le_top
  have hX := ConcreteCategory.congr_hom ((degreeUnit X).naturality r.op)
    (ULift.up (1 : ℤ))
  have hf := ConcreteCategory.congr_hom ((globalSectionMorphism F s).hom.naturality r.op)
    ((degreeUnit X).app (op (⊤ : Opens X)) (ULift.up (1 : ℤ)))
  change (degreeUnit X).app (op V) (ULift.up (1 : ℤ)) =
    (integerSheaf X).obj.map r.op
      ((degreeUnit X).app (op (⊤ : Opens X)) (ULift.up (1 : ℤ))) at hX
  rw [hX]
  exact hf.trans (congrArg (F.obj.map r.op) (globalSectionMorphism_degreeOne_top F s))

/-- The original degree-zero Ext comparison evaluates an actual sheaf
morphism by the native global-section adjunction. -/
theorem h0GlobalIso_hom_mk₀ (h : degreeSheaf X ⟶ F) :
    (h0GlobalIso F).hom (Ext.mk₀ h) = homGlobalEquiv X F h :=
  congrArg (homGlobalEquiv X F)
    ((Ext.addEquiv₀ (X := integerSheaf X) (Y := F)).apply_symm_apply h)

/-- The inverse of the actual degree-zero global-section comparison
is the native Ext class of the genuine representing morphism. -/
theorem h0GlobalIso_inv_eq_mk₀ (s : Section F (⊤ : Opens X)) :
    (h0GlobalIso F).inv s = Ext.mk₀ (globalSectionMorphism F s) := by
  rfl

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.CechConnecting
