import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyGlobalSectionsBiproduct

/-!
# Actual finite-biproduct comparisons on global sections

The comparison commutes with the literal component maps. Consequently,
isomorphisms on the actual component sections give an isomorphism on
the actual finite-sum sections, without replacing the sheaf complex.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyConstantEdge

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C]
  (F : C ⥤ D) [F.Additive] {J : Type} [Finite J]
  (A B : J → C) (f : ∀ j, A j ⟶ B j)

/-- The actual functorial biproduct comparison commutes with component maps. -/
theorem mapBiproduct_comparison :
    F.map (biproduct.map f) ≫ (F.mapBiproduct B).hom =
      (F.mapBiproduct A).hom ≫ biproduct.map (fun j => F.map (f j)) := by
  apply biproduct.hom_ext
  intro j
  simp only [Functor.mapBiproduct_hom, Category.assoc]
  rw [biproduct.lift_π (f := F.obj ∘ B),
    biproduct.map_π (f := F.obj ∘ A) (g := F.obj ∘ B),
    ← Category.assoc, biproduct.lift_π (f := F.obj ∘ A),
    ← F.map_comp, biproduct.map_π, F.map_comp]

/-- Isomorphisms of the actual component images imply an isomorphism
of the image of their actual finite-sum map. -/
theorem mapBiproduct_isIso [∀ j, IsIso (F.map (f j))] :
    IsIso (F.map (biproduct.map f)) := by
  let e : (⨁ (F.obj ∘ A)) ≅ ⨁ (F.obj ∘ B) :=
    biproduct.mapIso (fun j => asIso (F.map (f j)))
  have h : F.map (biproduct.map f) ≫ (F.mapBiproduct B).hom =
      (F.mapBiproduct A).hom ≫ e.hom := mapBiproduct_comparison F A B f
  have : IsIso (F.map (biproduct.map f) ≫ (F.mapBiproduct B).hom) :=
    h.symm ▸ inferInstance
  exact IsIso.of_isIso_comp_right (F.map (biproduct.map f)) (F.mapBiproduct B).hom

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyConstantEdge
