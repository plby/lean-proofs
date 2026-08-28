import Wikipedia.HopfProblem.CuspNormalizationSheafFiniteStalkEquivalence

/-!
# Naturality of the finite-fibre pushforward stalk formula

The canonical finite-fibre equivalence commutes with every morphism of
actual sheaves. This is checked on actual section representatives, using
the defining formula for the stalk functor on morphisms.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped AlgebraicGeometry

namespace Wikipedia.HopfProblem.CuspNormalization.SheafFiniteStalk

variable {X Y : TopCat.{0}}

/-- The canonical map to the fibre stalks is natural in the presheaf;
no closedness, finiteness or separation hypothesis is needed here. -/
theorem pushforwardStalkHom_naturality (f : X ⟶ Y)
    {F G : TopCat.Presheaf AddCommGrpCat.{0} X} (α : F ⟶ G)
    (y : Y) (s : (f _* F).stalk y) (x : f ⁻¹' {y}) :
    pushforwardStalkHom f G y
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
          ((TopCat.Presheaf.pushforward AddCommGrpCat f).map α) s) x =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x.val).map α
        (pushforwardStalkHom f F y s x) := by
  obtain ⟨U, hyU, u, rfl⟩ := (f _* F).exists_germ_eq s
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
    pushforwardStalkHom_germ, pushforwardStalkHom_germ,
    TopCat.Presheaf.stalkFunctor_map_germ_apply]
  rfl

/-- The genuine stalk equivalence intertwines the pushforward of a
sheaf morphism with its stalk maps at the actual fibre points. -/
theorem pushforwardStalkEquiv_naturality [T2Space X]
    (f : X ⟶ Y) (hf : IsClosedMap f)
    {F G : TopCat.Sheaf AddCommGrpCat.{0} X} (α : F ⟶ G)
    (y : Y) (hfinite : (f ⁻¹' {y}).Finite)
    (s : (f _* F.presheaf).stalk y) (x : f ⁻¹' {y}) :
    pushforwardStalkEquiv f hf G y hfinite
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
          ((TopCat.Presheaf.pushforward AddCommGrpCat f).map α.hom) s) x =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x.val).map α.hom
        (pushforwardStalkEquiv f hf F y hfinite s x) :=
  pushforwardStalkHom_naturality f α.hom y s x

end Wikipedia.HopfProblem.CuspNormalization.SheafFiniteStalk
