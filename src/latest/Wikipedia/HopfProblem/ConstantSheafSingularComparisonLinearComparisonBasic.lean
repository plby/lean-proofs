import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyScalars

/-!
# Linear equivalences for actual scalar endomorphism actions

An additive-group isomorphism that commutes with two specified scalar
endomorphism actions is linear for exactly the modules defined by those
actions.  This construction does not transport a module through the
isomorphism: both module actions are already fixed.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.LinearComparison

open CuspNormalization.SheafCohomology

/-- Two consecutive intertwining maps intertwine the original endomorphisms. -/
theorem comp_intertwines {C : Type*} [Category C] {A B D : C}
    (a : A ⟶ A) (b : B ⟶ B) (d : D ⟶ D) (u : A ⟶ B) (v : B ⟶ D)
    (hu : a ≫ u = u ≫ b) (hv : b ≫ v = v ≫ d) :
    a ≫ (u ≫ v) = (u ≫ v) ≫ d := by
  rw [← Category.assoc, hu, Category.assoc, hv, ← Category.assoc]

/-- An additive isomorphism commuting with the actual scalar
endomorphisms is linear for the two independently specified actions. -/
def linearEquivOfScalarEnd {R : Type} [Semiring R]
    (A B : AddCommGrpCat.{0}) (ρ : R →+* End A) (σ : R →+* End B)
    (e : A ≅ B) (h : ∀ r, (ρ r).asHom ≫ e.hom = e.hom ≫ (σ r).asHom) :
    letI := moduleOfScalarEnd A ρ
    letI := moduleOfScalarEnd B σ
    A ≃ₗ[R] B := by
  letI := moduleOfScalarEnd A ρ
  letI := moduleOfScalarEnd B σ
  exact
    { e.addCommGroupIsoToAddEquiv with
      map_smul' := fun r a => ConcreteCategory.congr_hom (h r) a }

/-- The linear upgrade retains the original additive equivalence literally. -/
@[simp]
theorem linearEquivOfScalarEnd_toAddEquiv {R : Type} [Semiring R]
    (A B : AddCommGrpCat.{0}) (ρ : R →+* End A) (σ : R →+* End B)
    (e : A ≅ B) (h : ∀ r, (ρ r).asHom ≫ e.hom = e.hom ≫ (σ r).asHom) :
    letI := moduleOfScalarEnd A ρ
    letI := moduleOfScalarEnd B σ
    (linearEquivOfScalarEnd A B ρ σ e h).toAddEquiv = e.addCommGroupIsoToAddEquiv := rfl

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.LinearComparison
