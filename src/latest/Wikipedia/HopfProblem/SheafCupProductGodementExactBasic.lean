import Wikipedia.HopfProblem.SheafCupProductGodementCofaces
import Wikipedia.HopfProblem.SheafCupProductGodementForgetBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafBiproduct
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# The actual additive complex of multiplicative Godement terms

The objects are the underlying additive sheaves of the actual iterated
ring-valued product-of-stalks construction. The arrows are the literal
alternating sums of the actual germ-insertion cofaces. Their consecutive
composites vanish by the proved coface identities.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.SheafCupProduct.GodementExact

open GodementRing

variable {X : TopCat.{0}}

/-- Forget only the multiplication in the original ring sheaf. -/
abbrev additiveSheaf (F : RingSheaf X) := (forgetSheaf X).obj F

abbrev I0 (F : RingSheaf X) := additiveSheaf (term0 F)
abbrev I1 (F : RingSheaf X) := additiveSheaf (term1 F)
abbrev I2 (F : RingSheaf X) := additiveSheaf (term2 F)
abbrev I3 (F : RingSheaf X) := additiveSheaf (term3 F)

/-- The augmentation is the original section-to-germs map. -/
def augmentation (F : RingSheaf X) : additiveSheaf F ⟶ I0 F :=
  (forgetSheaf X).map (inclusion F)

def d0 (F : RingSheaf X) : I0 F ⟶ I1 F :=
  (forgetSheaf X).map (face0 F 0) - (forgetSheaf X).map (face0 F 1)

def d1 (F : RingSheaf X) : I1 F ⟶ I2 F :=
  (forgetSheaf X).map (face1 F 0) - (forgetSheaf X).map (face1 F 1) +
    (forgetSheaf X).map (face1 F 2)

def d2 (F : RingSheaf X) : I2 F ⟶ I3 F :=
  (forgetSheaf X).map (face2 F 0) - (forgetSheaf X).map (face2 F 1) +
    (forgetSheaf X).map (face2 F 2) - (forgetSheaf X).map (face2 F 3)

/-- Actual sections on an open, still retaining their ring structure. -/
abbrev sections (U : (Opens X)ᵒᵖ) : RingSheaf X ⥤ CommRingCat.{0} :=
  TopCat.Sheaf.forget CommRingCat X ⋙
    (evaluation (Opens X)ᵒᵖ CommRingCat).obj U

/-- On every actual open the differential is the original coface differential. -/
theorem d0_sections (F : RingSheaf X) (U : (Opens X)ᵒᵖ) :
    (d0 F).hom.app U = AddCommGrpCat.ofHom (cofaceData F (sections U)).d0 := rfl

theorem d1_sections (F : RingSheaf X) (U : (Opens X)ᵒᵖ) :
    (d1 F).hom.app U = AddCommGrpCat.ofHom (cofaceData F (sections U)).d1 := rfl

theorem d2_sections (F : RingSheaf X) (U : (Opens X)ᵒᵖ) :
    (d2 F).hom.app U = AddCommGrpCat.ofHom (cofaceData F (sections U)).d2 := rfl

theorem augmentation_d0 (F : RingSheaf X) : augmentation F ≫ d0 F = 0 := by
  change (forgetSheaf X).map (inclusion F) ≫
    ((forgetSheaf X).map (inclusion (term0 F)) -
      (forgetSheaf X).map (map (inclusion F))) = 0
  rw [Preadditive.comp_sub, ← Functor.map_comp, ← Functor.map_comp,
    inclusion_naturality, sub_self]

theorem d0_d1 (F : RingSheaf X) : d0 F ≫ d1 F = 0 := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U s
  exact (cofaceData F (sections U)).d1_d0 s

theorem d1_d2 (F : RingSheaf X) : d1 F ≫ d2 F = 0 := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U s
  exact (cofaceData F (sections U)).d2_d1 s

/-- The three genuine consecutive short complexes of additive sheaves. -/
abbrev complex0 (F : RingSheaf X) :=
  ShortComplex.mk (augmentation F) (d0 F) (augmentation_d0 F)

abbrev complex1 (F : RingSheaf X) := ShortComplex.mk (d0 F) (d1 F) (d0_d1 F)

abbrev complex2 (F : RingSheaf X) := ShortComplex.mk (d1 F) (d2 F) (d1_d2 F)

end Wikipedia.HopfProblem.SheafCupProduct.GodementExact
