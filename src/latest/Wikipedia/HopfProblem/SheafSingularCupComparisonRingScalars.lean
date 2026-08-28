import Wikipedia.HopfProblem.SheafSingularCupComparisonRingAugmentation
import Wikipedia.HopfProblem.SheafCupProductCoefficients

/-!
# Literal complex coefficients in the ring singular-cochain sheaves

The coefficients are the sheafification germs of actual constant
functions on singular simplices. The cofaces and the original constant
augmentation preserve these coefficients, hence their original section
maps are genuinely complex-linear.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.RingCochains

open SheafCupProduct

variable (X : TopCat.{0})

/-- The actual global constant cochains, passed through the original unit. -/
def coefficients (n : ℕ) : Scalars.Coefficients (sheaf X n) :=
  ((unit X n).app (op ⊤)).hom.comp
    { toFun := fun z _ => z
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

@[simp] theorem coefficients_apply (n : ℕ) (z : ℂ) :
    coefficients X n z = (unit X n).app (op ⊤) (fun _ => z) := rfl

/-- Every restricted coefficient is the same literal constant cochain. -/
theorem restricted_coefficients (n : ℕ) (U : (Opens X)ᵒᵖ) (z : ℂ) :
    Scalars.restricted (coefficients X n) U z = (unit X n).app U (fun _ => z) := by
  exact (ConcreteCategory.congr_hom
    ((unit X n).naturality (homOfLE (show U.unop ≤ ⊤ from le_top)).op)
      (fun _ => z)).symm

/-- The actual face pullbacks preserve literal global complex constants. -/
theorem coface_coefficients (n : ℕ) (i : Fin (n + 2)) :
    Scalars.pushCoefficients (coface X n i) (coefficients X n) =
      coefficients X (n + 1) := by
  apply RingHom.ext
  intro z
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (unit_coface X n i) (op ⊤)) (fun _ => z)

/-- The original constant-sheaf augmentation preserves the original constants. -/
theorem augmentation_coefficients :
    Scalars.pushCoefficients (augmentation X) (constantCoefficients X) =
      coefficients X 0 := by
  apply RingHom.ext
  intro z
  exact augmentation_app_unit X ⊤ z

/-- Actual additive scalar multiplication commutes with every actual coface. -/
theorem coface_scalar (n : ℕ) (i : Fin (n + 2)) (z : ℂ) :
    (Scalars.scalarEnd (coefficients X n) z).asHom ≫ (forgetSheaf X).map (coface X n i) =
      (forgetSheaf X).map (coface X n i) ≫
        (Scalars.scalarEnd (coefficients X (n + 1)) z).asHom :=
  Scalars.scalarEnd_naturality_of_compatible (coface X n i)
    (coefficients X n) (coefficients X (n + 1)) (coface_coefficients X n i) z

/-- The actual section map of a singular coface, with its proved complex-linearity. -/
def cofaceLinear (n : ℕ) (i : Fin (n + 2)) (U : (Opens X)ᵒᵖ) :
    letI := Scalars.sectionModule (coefficients X n) U
    letI := Scalars.sectionModule (coefficients X (n + 1)) U
    (sheaf X n).obj.obj U →ₗ[ℂ] (sheaf X (n + 1)).obj.obj U :=
  Scalars.sectionMapLinear (coface X n i) (coefficients X n) (coefficients X (n + 1))
    (coface_coefficients X n i) U

end Wikipedia.HopfProblem.SheafSingularCupComparison.RingCochains
