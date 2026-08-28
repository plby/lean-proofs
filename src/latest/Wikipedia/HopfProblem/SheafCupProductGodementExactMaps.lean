import Wikipedia.HopfProblem.SheafCupProductGodementExactSheaf
import Wikipedia.HopfProblem.SheafCupProductGodementCofaceNaturality
import Wikipedia.HopfProblem.SheafCupProductResolutionMaps

/-!
# Actual coefficient maps of Godement partial resolutions

Each component is obtained by iterating the actual ring-Godement
functor on the original coefficient morphism and forgetting only its
multiplication. Germ naturality proves the augmentation square, and the
actual coface squares prove compatibility with all three differentials.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafCupProduct.GodementExact

open GodementRing

variable {X : TopCat.{0}} {F G : RingSheaf X}

abbrev I0Map (f : F ⟶ G) : I0 F ⟶ I0 G := (forgetSheaf X).map (term0Map f)
abbrev I1Map (f : F ⟶ G) : I1 F ⟶ I1 G := (forgetSheaf X).map (term1Map f)
abbrev I2Map (f : F ⟶ G) : I2 F ⟶ I2 G := (forgetSheaf X).map (term2Map f)
abbrev I3Map (f : F ⟶ G) : I3 F ⟶ I3 G := (forgetSheaf X).map (term3Map f)

theorem augmentation_naturality (f : F ⟶ G) :
    (forgetSheaf X).map f ≫ augmentation G = augmentation F ≫ I0Map f := by
  change (forgetSheaf X).map f ≫ (forgetSheaf X).map (inclusion G) =
    (forgetSheaf X).map (inclusion F) ≫ (forgetSheaf X).map (map f)
  rw [← Functor.map_comp, ← Functor.map_comp, inclusion_naturality]

theorem d0_naturality (f : F ⟶ G) : I0Map f ≫ d0 G = d0 F ≫ I1Map f := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U s
  exact ((cofaceMap f (sections U)).d0_comm s).symm

theorem d1_naturality (f : F ⟶ G) : I1Map f ≫ d1 G = d1 F ≫ I2Map f := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U s
  exact ((cofaceMap f (sections U)).d1_comm s).symm

theorem d2_naturality (f : F ⟶ G) : I2Map f ≫ d2 G = d2 F ≫ I3Map f := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U s
  exact ((cofaceMap f (sections U)).d2_comm s).symm

/-- The actual coefficient morphism induces a map of the proved
partial resolutions, with the original forgotten morphism at the augmentation. -/
def partialResolutionMap (f : F ⟶ G) :
    (partialResolution F).Hom (partialResolution G) where
  augmentation := (forgetSheaf X).map f
  τ₀ := I0Map f
  τ₁ := I1Map f
  τ₂ := I2Map f
  τ₃ := I3Map f
  commι := augmentation_naturality f
  comm₀ := d0_naturality f
  comm₁ := d1_naturality f
  comm₂ := d2_naturality f

end Wikipedia.HopfProblem.SheafCupProduct.GodementExact
