import Wikipedia.HopfProblem.CuspNormalizationSheafForgetStalkNaturality
import Wikipedia.HopfProblem.CuspNormalizationSheafForgetStalkSheaf

/-!
# Actual additive and ring stalks for finite normalization maps

This package identifies the actual additive stalk of a forgotten
commutative-ring sheaf with the underlying additive group of its actual
ring-valued stalk. The equivalence is the inverse of the proved
filtered-colimit-preservation comparison. It preserves actual section
germs and is natural in morphisms and canonical pushforward stalk maps.

Combining this with the closed finite-fibre stalk theorem gives an
equivalence from the actual additive pushforward stalk to the product of
the actual ring stalks in the fibre. All comparisons are proved, including
their formulas on actual representatives.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory
open scoped AlgebraicGeometry

namespace Wikipedia.HopfProblem.CuspNormalization.SheafForgetStalk

variable {X Y : TopCat.{0}} [T2Space X]

/-- The combined finite-fibre comparison is natural in actual ring-sheaf
morphisms: its right-hand components are the actual ring-valued stalk
maps, while its left-hand map is the actual forgotten pushforward map. -/
theorem pushforwardStalkAddEquiv_naturality (f : X ⟶ Y) (hf : IsClosedMap f)
    {F G : TopCat.Sheaf CommRingCat.{0} X} (α : F ⟶ G)
    (y : Y) (hfinite : (f ⁻¹' {y}).Finite)
    (s : (f _* (additiveSheaf F).presheaf).stalk y) (x : f ⁻¹' {y}) :
    pushforwardStalkAddEquiv f hf G y hfinite
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
          ((TopCat.Presheaf.pushforward AddCommGrpCat f).map
            (Functor.whiskerRight α.hom forgetToAdd)) s) x =
      (TopCat.Presheaf.stalkFunctor CommRingCat x.val).map α.hom
        (pushforwardStalkAddEquiv f hf F y hfinite s x) := by
  exact (congrArg (sheafStalkAddEquiv G x.val)
    (SheafFiniteStalk.pushforwardStalkHom_naturality f
      (Functor.whiskerRight α.hom forgetToAdd) y s x)).trans
    (stalkAddEquiv_naturality α.hom x.val
      (SheafFiniteStalk.pushforwardStalkHom f (additiveSheaf F).presheaf y s x))

end Wikipedia.HopfProblem.CuspNormalization.SheafForgetStalk
