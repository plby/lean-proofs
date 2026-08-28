import Wikipedia.HopfProblem.SheafCupProductGodementForgetBasic

/-!
# Actual scalar multiplication from global ring sections

A ring homomorphism from the complex numbers into the original global
sections restricts to every open. Multiplication by these restricted
sections is an actual endomorphism of the underlying additive sheaf.
The resulting endomorphisms form the original scalar action, before any
cohomology group or quotient comparison is considered.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.SheafCupProduct.Scalars

open GodementRing

variable {X : TopCat.{0}}

/-- Actual global complex constants in the original ring sheaf. -/
abbrev Coefficients (F : RingSheaf X) := ℂ →+* F.presheaf.obj (op ⊤)

variable {F : RingSheaf X}

/-- Restrict the given global constants along the original restriction map. -/
def restricted (c : Coefficients F) (U : (Opens X)ᵒᵖ) : ℂ →+* F.presheaf.obj U :=
  (F.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op).hom.comp c

theorem restricted_naturality (c : Coefficients F) {U V : (Opens X)ᵒᵖ}
    (i : U ⟶ V) (z : ℂ) : F.presheaf.map i (restricted c U z) = restricted c V z := by
  exact (ConcreteCategory.congr_hom
    (F.presheaf.map_comp (homOfLE (show U.unop ≤ ⊤ from le_top)).op i) (c z)).symm

@[simp] theorem restricted_top (c : Coefficients F) (z : ℂ) :
    restricted c (op ⊤) z = c z := by
  change F.presheaf.map (𝟙 (op ⊤)) (c z) = c z
  rw [F.presheaf.map_id]
  rfl

/-- Literal multiplication by the restricted global constant on each open. -/
def scalarMap (c : Coefficients F) (z : ℂ) :
    (forgetSheaf X).obj F ⟶ (forgetSheaf X).obj F where
  hom :=
    { app := fun U => AddCommGrpCat.ofHom (AddMonoidHom.mulLeft (restricted c U z))
      naturality := fun U V i => by
        ext s
        change F.presheaf.obj U at s
        change restricted c V z * F.presheaf.map i s =
          F.presheaf.map i (restricted c U z * (s : F.presheaf.obj U))
        rw [map_mul, restricted_naturality] }

@[simp] theorem scalarMap_apply (c : Coefficients F) (z : ℂ)
    (U : (Opens X)ᵒᵖ) (s : F.presheaf.obj U) :
    (scalarMap c z).hom.app U s = restricted c U z * s := rfl

/-- The genuine complex action on the original additive sheaf. -/
def scalarEnd (c : Coefficients F) : ℂ →+* End ((forgetSheaf X).obj F) where
  toFun := scalarMap c
  map_one' := by
    apply CategoryTheory.Sheaf.hom_ext
    ext U s
    change F.presheaf.obj U at s
    change restricted c U 1 * (s : F.presheaf.obj U) = s
    rw [map_one, one_mul]
  map_mul' z w := by
    apply CategoryTheory.Sheaf.hom_ext
    ext U s
    change F.presheaf.obj U at s
    change restricted c U (z * w) * (s : F.presheaf.obj U) =
      restricted c U z * (restricted c U w * (s : F.presheaf.obj U))
    rw [map_mul, mul_assoc]
  map_zero' := by
    apply CategoryTheory.Sheaf.hom_ext
    ext U s
    change F.presheaf.obj U at s
    change restricted c U 0 * (s : F.presheaf.obj U) = 0
    rw [map_zero, zero_mul]
  map_add' z w := by
    apply CategoryTheory.Sheaf.hom_ext
    ext U s
    change F.presheaf.obj U at s
    change restricted c U (z + w) * (s : F.presheaf.obj U) =
      restricted c U z * (s : F.presheaf.obj U) + restricted c U w * (s : F.presheaf.obj U)
    rw [map_add, add_mul]

@[simp] theorem scalarEnd_apply (c : Coefficients F) (z : ℂ)
    (U : (Opens X)ᵒᵖ) (s : F.presheaf.obj U) :
    (scalarEnd c z).hom.app U s = restricted c U z * s := rfl

end Wikipedia.HopfProblem.SheafCupProduct.Scalars
