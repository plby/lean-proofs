import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyScalarResolutionBasic
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-!
# Componentwise scalar endomorphisms of actual finite direct sums
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyScalarResolution

universe v u

variable {D : Type u} [Category.{v} D] [Preadditive D]
  {ι : Type} (A : ι → D) [HasBiproduct A] (ρ : ∀ i, ℂ →+* End (A i))

/-- The actual biproduct map of the scalar endomorphisms on its components. -/
def biproductScalarEnd : ℂ →+* End (⨁ A) where
  toFun c := biproduct.map (fun i => ρ i c)
  map_one' := by
    apply biproduct.hom_ext
    intro i
    simp only [biproduct.map_π, map_one, End.one_def, Category.comp_id, Category.id_comp]
  map_mul' c d := by
    apply biproduct.hom_ext
    intro i
    change biproduct.map (fun j => ρ j (c * d)) ≫ biproduct.π A i =
      (biproduct.map (fun j => ρ j d) ≫ biproduct.map (fun j => ρ j c)) ≫ biproduct.π A i
    simp only [biproduct.map_π, map_mul, End.mul_def, Category.assoc,
      biproduct.map_π_assoc]
  map_zero' := by
    apply biproduct.hom_ext
    intro i
    simp only [biproduct.map_π, map_zero, comp_zero, zero_comp]
  map_add' c d := by
    change biproduct.map (fun j => ρ j (c + d)) =
      biproduct.map (fun j => ρ j c) + biproduct.map (fun j => ρ j d)
    apply biproduct.hom_ext
    intro i
    have hadd : (ρ i (c + d)).asHom = (ρ i c).asHom + (ρ i d).asHom :=
      (ρ i).map_add c d
    simp only [Preadditive.add_comp, biproduct.map_π]
    exact (congrArg (fun f : A i ⟶ A i => biproduct.π A i ≫ f) hadd).trans
      (Preadditive.comp_add _ _ _ _ _ _)

@[reassoc] theorem biproductScalarEnd_π (c : ℂ) (i : ι) :
    biproductScalarEnd A ρ c ≫ biproduct.π A i = biproduct.π A i ≫ ρ i c := by
  change biproduct.map (fun j => (ρ j c).asHom) ≫ biproduct.π A i =
    biproduct.π A i ≫ (ρ i c).asHom
  exact biproduct.map_π (f := A) (g := A) (fun j => (ρ j c).asHom) i

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyScalarResolution
