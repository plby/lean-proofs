import Wikipedia.HopfProblem.SheafLerayLowDegreesTransport

/-!
# Naturality through the canonical term isomorphisms

These categorical identities transfer commuting squares through the
actual Ext and resolution-homology comparisons used in Leray's low
degrees.  They do not impose a new naturality condition on the resulting
cohomology maps: the input squares are proved for the original maps.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafLerayLowDegrees

variable {C : Type*} [Category C]

/-- Inverting the horizontal isomorphisms preserves a commuting square. -/
theorem inverse_naturality {X Y A B : C} (e : X ≅ A) (e' : Y ≅ B)
    (u : X ⟶ Y) (v : A ⟶ B) (h : u ≫ e'.hom = e.hom ≫ v) :
    v ≫ e'.inv = e.inv ≫ u := by
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc] using
    (congrArg (fun k => e.inv ≫ k ≫ e'.inv) h).symm

/-- A square remains commutative after replacing all four terms by
their canonically isomorphic native cohomology groups. -/
theorem transported_map_naturality {X Y X' Y' A B A' B' : C}
    (eX : X ≅ A) (eY : Y ≅ B) (eX' : X' ≅ A') (eY' : Y' ≅ B')
    (a : X ⟶ Y) (b : X' ⟶ Y') (u : X ⟶ X') (v : Y ⟶ Y')
    (u' : A ⟶ A') (v' : B ⟶ B')
    (hX : u ≫ eX'.hom = eX.hom ≫ u')
    (hY : v ≫ eY'.hom = eY.hom ≫ v') (h : u ≫ b = a ≫ v) :
    u' ≫ (eX'.inv ≫ b ≫ eY'.hom) = (eX.inv ≫ a ≫ eY.hom) ≫ v' := by
  have hi := inverse_naturality eX eX' u u' hX
  calc
    _ = (u' ≫ eX'.inv) ≫ (b ≫ eY'.hom) := (Category.assoc _ _ _).symm
    _ = (eX.inv ≫ u) ≫ (b ≫ eY'.hom) := congrArg (fun k => k ≫ (b ≫ eY'.hom)) hi
    _ = eX.inv ≫ ((u ≫ b) ≫ eY'.hom) := by simp only [Category.assoc]
    _ = eX.inv ≫ ((a ≫ v) ≫ eY'.hom) :=
      congrArg (fun k => eX.inv ≫ (k ≫ eY'.hom)) h
    _ = (eX.inv ≫ a) ≫ (v ≫ eY'.hom) := by simp only [Category.assoc]
    _ = (eX.inv ≫ a) ≫ (eY.hom ≫ v') := congrArg (fun k => (eX.inv ≫ a) ≫ k) hY
    _ = _ := by simp only [Category.assoc]

end Wikipedia.HopfProblem.SheafLerayLowDegrees
