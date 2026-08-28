import Wikipedia.HopfProblem.SheafCupProductScalarsBasic
import Mathlib.Algebra.Module.RingHom
import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# Scalar multiplication under actual coefficient morphisms

The global constants are sent by the actual map on global sections.
Restriction and multiplication commute with this original ring-sheaf
map. The resulting section maps are genuinely complex-linear for the
module structures obtained from those restricted constants.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.SheafCupProduct.Scalars

open GodementRing

variable {X : TopCat.{0}} {F G H : RingSheaf X}

/-- Send the actual global constants by the original global ring map. -/
def pushCoefficients (f : F ⟶ G) (c : Coefficients F) : Coefficients G :=
  (f.hom.app (op ⊤)).hom.comp c

@[simp] theorem pushCoefficients_apply (f : F ⟶ G) (c : Coefficients F) (z : ℂ) :
    pushCoefficients f c z = f.hom.app (op ⊤) (c z) := rfl

@[simp] theorem pushCoefficients_id (c : Coefficients F) :
    pushCoefficients (𝟙 F) c = c := by ext z; rfl

theorem pushCoefficients_comp (f : F ⟶ G) (g : G ⟶ H) (c : Coefficients F) :
    pushCoefficients (f ≫ g) c = pushCoefficients g (pushCoefficients f c) := by
  ext z
  rfl

theorem restricted_push (f : F ⟶ G) (c : Coefficients F)
    (U : (Opens X)ᵒᵖ) (z : ℂ) :
    restricted (pushCoefficients f c) U z = f.hom.app U (restricted c U z) :=
  (ConcreteCategory.congr_hom
    (f.hom.naturality (homOfLE (show U.unop ≤ ⊤ from le_top)).op) (c z)).symm

/-- Ring-sheaf maps intertwine literal multiplication by their global constants. -/
theorem scalarEnd_naturality (f : F ⟶ G) (c : Coefficients F) (z : ℂ) :
    (scalarEnd c z).asHom ≫ (forgetSheaf X).map f =
      (forgetSheaf X).map f ≫ (scalarEnd (pushCoefficients f c) z).asHom := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U s
  change F.presheaf.obj U at s
  change f.hom.app U (restricted c U z * (s : F.presheaf.obj U)) =
    restricted (pushCoefficients f c) U z * f.hom.app U s
  rw [map_mul, restricted_push]

theorem scalarEnd_naturality_of_compatible (f : F ⟶ G)
    (c : Coefficients F) (d : Coefficients G) (h : pushCoefficients f c = d) (z : ℂ) :
    (scalarEnd c z).asHom ≫ (forgetSheaf X).map f =
      (forgetSheaf X).map f ≫ (scalarEnd d z).asHom := by
  simpa only [h] using scalarEnd_naturality f c z

/-- The section module is defined by the actual restricted ring homomorphism. -/
@[instance_reducible] def sectionModule (c : Coefficients F) (U : (Opens X)ᵒᵖ) :
    Module ℂ (F.presheaf.obj U) := (restricted c U).toModule

theorem sectionModule_smul (c : Coefficients F) (U : (Opens X)ᵒᵖ)
    (z : ℂ) (s : F.presheaf.obj U) :
    letI := sectionModule c U
    z • s = restricted c U z * s := rfl

/-- The original section map, with its proved complex-linearity. -/
def sectionMapLinear (f : F ⟶ G) (c : Coefficients F) (d : Coefficients G)
    (h : pushCoefficients f c = d) (U : (Opens X)ᵒᵖ) :
    letI := sectionModule c U
    letI := sectionModule d U
    F.presheaf.obj U →ₗ[ℂ] G.presheaf.obj U := by
  letI := sectionModule c U
  letI := sectionModule d U
  exact
    { toFun := f.hom.app U
      map_add' := (f.hom.app U).hom.map_add
      map_smul' := fun z s => by
        change f.hom.app U (restricted c U z * s) =
          restricted d U z * f.hom.app U s
        rw [map_mul, ← restricted_push, h] }

end Wikipedia.HopfProblem.SheafCupProduct.Scalars
