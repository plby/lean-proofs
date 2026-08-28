import Wikipedia.HopfProblem.CuspNormalizationSheafForgetStalkBasic

/-!
# Naturality of the actual additive/ring stalk comparison

Forgetting the ring structure commutes with the stalk map of every
presheaf morphism and with the canonical stalk map for every continuous
pushforward. Both identities are proved on actual section germs.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open CategoryTheory.Functor
open scoped AlgebraicGeometry

namespace Wikipedia.HopfProblem.CuspNormalization.SheafForgetStalk

variable {X Y : TopCat.{0}}

/-- The actual additive/ring stalk comparison is natural in all
commutative-ring presheaf morphisms. -/
theorem stalkAddEquiv_naturality
    {F G : TopCat.Presheaf CommRingCat.{0} X} (α : F ⟶ G)
    (x : X) (s : (additivePresheaf F).stalk x) :
    stalkAddEquiv G x
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (whiskerRight α forgetToAdd) s) =
      (TopCat.Presheaf.stalkFunctor CommRingCat x).map α (stalkAddEquiv F x s) := by
  obtain ⟨U, hxU, u, rfl⟩ := (additivePresheaf F).exists_germ_eq s
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, stalkAddEquiv_germ,
    stalkAddEquiv_germ, TopCat.Presheaf.stalkFunctor_map_germ_apply]
  rfl

/-- The same naturality as an equality of actual categorical additive
maps, suitable for transport of short complexes of sheaves. -/
theorem stalkIso_naturality
    {F G : TopCat.Presheaf CommRingCat.{0} X} (α : F ⟶ G) (x : X) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (whiskerRight α forgetToAdd) ≫ (stalkIso G x).hom =
      (stalkIso F x).hom ≫
        forgetToAdd.map ((TopCat.Presheaf.stalkFunctor CommRingCat x).map α) := by
  ext s
  exact stalkAddEquiv_naturality α x s

/-- Forgetting commutes with the actual canonical pushforward stalk
map. No closedness, finite-fibre or sheaf condition is needed. -/
theorem stalkAddEquiv_stalkPushforward (f : X ⟶ Y)
    (F : TopCat.Presheaf CommRingCat.{0} X) (x : X)
    (s : (f _* additivePresheaf F).stalk (f x)) :
    stalkAddEquiv F x ((additivePresheaf F).stalkPushforward AddCommGrpCat f x s) =
      F.stalkPushforward CommRingCat f x (stalkAddEquiv (f _* F) (f x) s) := by
  obtain ⟨U, hxU, u, rfl⟩ := (f _* additivePresheaf F).exists_germ_eq s
  calc
    stalkAddEquiv F x ((additivePresheaf F).stalkPushforward AddCommGrpCat f x
        ((f _* additivePresheaf F).germ U (f x) hxU u)) =
        stalkAddEquiv F x
          ((additivePresheaf F).germ ((Opens.map f).obj U) x hxU u) :=
      congrArg (stalkAddEquiv F x)
        (TopCat.Presheaf.stalkPushforward_germ_apply AddCommGrpCat f
          (additivePresheaf F) U x hxU u)
    _ = F.germ ((Opens.map f).obj U) x hxU u :=
      stalkAddEquiv_germ F ((Opens.map f).obj U) x hxU u
    _ = F.stalkPushforward CommRingCat f x ((f _* F).germ U (f x) hxU u) :=
      (TopCat.Presheaf.stalkPushforward_germ_apply CommRingCat f F U x hxU u).symm
    _ = F.stalkPushforward CommRingCat f x
        (stalkAddEquiv (f _* F) (f x)
          ((f _* additivePresheaf F).germ U (f x) hxU u)) :=
      congrArg (F.stalkPushforward CommRingCat f x)
        (stalkAddEquiv_germ (f _* F) U (f x) hxU u).symm

end Wikipedia.HopfProblem.CuspNormalization.SheafForgetStalk
