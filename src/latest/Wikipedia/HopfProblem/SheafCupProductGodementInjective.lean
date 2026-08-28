import Wikipedia.HopfProblem.SheafCupProductGodementForgetBasic
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyGodementScalars

/-!
# Genuine injectivity of the multiplicative Godement terms

Forgetting the actual multiplicative Godement construction is canonically
isomorphic to the previously constructed additive product of stalks.
An actual complex scalar action therefore makes its first two terms
injective abelian sheaves.  Injectivity is proved by actual stalk
divisibility and skyscraper adjunctions, not assumed as acyclicity data.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopCat

namespace Wikipedia.HopfProblem.SheafCupProduct.GodementRing

open CuspNormalization.SheafForgetStalk CuspNormalization.SheafCohomology

attribute [local instance] Classical.propDecidable

variable {X : TopCat.{0}}

/-- Forgetting a single ring skyscraper also commutes with its actual
stalk coefficient, through the proved filtered-colimit comparison. -/
def pointForgetIso (F : RingSheaf X) (x : X) :
    (forgetSheaf X).obj (pointTerm F x) ≅
      HolomorphicSheafCohomology.Godement.pointTerm ((forgetSheaf X).obj F) x :=
  skyscraperForgetIso x (F.presheaf.stalk x) ≪≫
    (skyscraperSheafFunctor (C := AddCommGrpCat.{0}) x).mapIso
      (stalkIso F.presheaf x).symm

/-- The actual multiplicative and additive product-of-stalks terms
agree after forgetting multiplication. -/
def additiveGodementIso (F : RingSheaf X) :
    (forgetSheaf X).obj (sheaf F) ≅
      HolomorphicSheafCohomology.Godement.sheaf ((forgetSheaf X).obj F) :=
  PreservesProduct.iso (forgetSheaf X) (pointTerm F) ≪≫
    Pi.mapIso (pointForgetIso F)

section Endomorphisms

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] {M N : A}

/-- Conjugating actual endomorphisms along an actual isomorphism. -/
def conjugateEnd (e : M ≅ N) : End N →+* End M where
  toFun f := e.hom ≫ f ≫ e.inv
  map_one' := by simp
  map_mul' f g := by
    simp only [End.mul_def, Category.assoc, Iso.inv_hom_id_assoc]
  map_zero' := by simp
  map_add' f g := by
    change e.hom ≫ (f.asHom + g.asHom) ≫ e.inv =
      (e.hom ≫ f.asHom ≫ e.inv) + (e.hom ≫ g.asHom ≫ e.inv)
    simp only [Preadditive.comp_add, Preadditive.add_comp]

end Endomorphisms

/-- The actual additive Godement functor carries the scalar action;
the canonical comparison puts it on the actual multiplicative term. -/
def godementScalarEnd (F : RingSheaf X) (ρ : ℂ →+* End ((forgetSheaf X).obj F)) :
    ℂ →+* End ((forgetSheaf X).obj (sheaf F)) :=
  (conjugateEnd (additiveGodementIso F)).comp
    ((mapEndRingHom (HolomorphicSheafCohomology.Godement.functor (X := X))
      ((forgetSheaf X).obj F)).comp ρ)

/-- The first actual multiplicative term is injective as an abelian
sheaf whenever the original sheaf has its actual complex scalar action. -/
theorem godement_injective_of_scalarEnd (F : RingSheaf X)
    (ρ : ℂ →+* End ((forgetSheaf X).obj F)) :
    Injective ((forgetSheaf X).obj (sheaf F)) :=
  Injective.of_iso (additiveGodementIso F).symm
    (HolomorphicSheafCohomology.Godement.sheaf_injective ((forgetSheaf X).obj F)
      (HolomorphicSheafCohomology.Godement.stalk_injective_of_scalarEnd
        ((forgetSheaf X).obj F) ρ))

/-- The next actual multiplicative term is injective for the same
proved reason; no higher-sheaf-cohomology hypothesis is introduced. -/
theorem doubleGodement_injective_of_scalarEnd (F : RingSheaf X)
    (ρ : ℂ →+* End ((forgetSheaf X).obj F)) :
    Injective ((forgetSheaf X).obj (sheaf (sheaf F))) :=
  godement_injective_of_scalarEnd (sheaf F) (godementScalarEnd F ρ)

end Wikipedia.HopfProblem.SheafCupProduct.GodementRing
