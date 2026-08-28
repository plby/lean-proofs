import Wikipedia.HopfProblem.SheafCupProductScalarsGodement
import Wikipedia.HopfProblem.SheafCupProductGodementExact

/-!
# Multiplication on the actual Godement partial resolution

The same original complex constant acts by literal multiplication at
each term. The proved preservation of constants by every coface makes
the alternating differentials commute with these maps. This is an
actual morphism of the original partial resolution, not a presumed map
on its cohomology.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafCupProduct.Scalars

open GodementRing GodementExact

variable {X : TopCat.{0}} {F : RingSheaf X}

theorem scalar_augmentation (c : Coefficients F) (z : ℂ) :
    (scalarEnd c z).asHom ≫ augmentation F =
      augmentation F ≫ (scalarEnd (coefficients0 c) z).asHom :=
  scalarEnd_naturality (inclusion F) c z

theorem scalar_d0 (c : Coefficients F) (z : ℂ) :
    (scalarEnd (coefficients0 c) z).asHom ≫ d0 F =
      d0 F ≫ (scalarEnd (coefficients1 c) z).asHom := by
  simp only [d0, Preadditive.comp_sub, Preadditive.sub_comp, face0_scalar]

theorem scalar_d1 (c : Coefficients F) (z : ℂ) :
    (scalarEnd (coefficients1 c) z).asHom ≫ d1 F =
      d1 F ≫ (scalarEnd (coefficients2 c) z).asHom := by
  simp only [d1, Preadditive.comp_sub, Preadditive.sub_comp,
    Preadditive.comp_add, Preadditive.add_comp, face1_scalar]

theorem scalar_d2 (c : Coefficients F) (z : ℂ) :
    (scalarEnd (coefficients2 c) z).asHom ≫ d2 F =
      d2 F ≫ (scalarEnd (coefficients3 c) z).asHom := by
  simp only [d2, Preadditive.comp_sub, Preadditive.sub_comp,
    Preadditive.comp_add, Preadditive.add_comp, face2_scalar]

/-- Multiplication at every original term is a genuine partial-resolution map. -/
def scalarPartialResolutionMap (c : Coefficients F) (z : ℂ) :
    (partialResolution F).Hom (partialResolution F) where
  augmentation := (scalarEnd c z).asHom
  τ₀ := (scalarEnd (coefficients0 c) z).asHom
  τ₁ := (scalarEnd (coefficients1 c) z).asHom
  τ₂ := (scalarEnd (coefficients2 c) z).asHom
  τ₃ := (scalarEnd (coefficients3 c) z).asHom
  commι := scalar_augmentation c z
  comm₀ := scalar_d0 c z
  comm₁ := scalar_d1 c z
  comm₂ := scalar_d2 c z

end Wikipedia.HopfProblem.SheafCupProduct.Scalars
