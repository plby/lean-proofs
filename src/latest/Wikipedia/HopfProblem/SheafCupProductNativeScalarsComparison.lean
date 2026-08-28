import Wikipedia.HopfProblem.SheafCupProductScalarQuotient
import Wikipedia.HopfProblem.SheafCupProductNativeBasic

/-!
# Native Ext comparisons preserve the actual scalar endomorphisms

The two squares are composed from the genuine partial-resolution Ext
comparison and the literal multiplication maps on actual Godement
cocycle quotients.  Thus the original sheaf scalar endomorphism, not a
chosen quotient action, is the scalar map retained by the comparison.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafCupProduct

open GodementRing

private theorem composeScalarSquares {A B D : AddCommGrpCat.{0}}
    (a : A ⟶ B) (b : B ⟶ D) (x : A ⟶ A) (y : B ⟶ B) (z : D ⟶ D)
    (h₁ : x ≫ a = a ≫ y) (h₂ : y ≫ b = b ≫ z) :
    x ≫ (a ≫ b) = (a ≫ b) ≫ z := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]

private theorem scalarIso_apply {A B : AddCommGrpCat.{0}}
    (e : A ≅ B) (f : A ⟶ A) (g : B ⟶ B)
    (h : f ≫ e.hom = e.hom ≫ g) (a : A) :
    e.addCommGroupIsoToAddEquiv (f a) = g (e.addCommGroupIsoToAddEquiv a) :=
  ConcreteCategory.congr_hom h a

variable {X : TopCat.{0}} {F : RingSheaf X} (c : Scalars.Coefficients F) (z : ℂ)

/-- The genuine first Ext comparison intertwines original scalar multiplication. -/
theorem h1CofaceIso_scalar :
    (CategoryTheory.Sheaf.functorH _ 1).map (Scalars.scalarEnd c z).asHom ≫
        (h1CofaceIso F (Scalars.scalarEnd c)).hom =
      (h1CofaceIso F (Scalars.scalarEnd c)).hom ≫
        AddCommGrpCat.ofHom (ScalarQuotient.scalarOne c z) := by
  let : Injective (GodementExact.partialResolution F).I₀ :=
    godement_injective_of_scalarEnd F (Scalars.scalarEnd c)
  exact composeScalarSquares
    (GodementExact.partialResolution F).h1Iso.hom
    (SheafCupProductResolution.Coface.oneHomologyIso (globalData F)).hom
    ((CategoryTheory.Sheaf.functorH _ 1).map (Scalars.scalarEnd c z).asHom)
    (ShortComplex.homologyMap (Scalars.scalarPartialResolutionMap c z).globalOneMap)
    (AddCommGrpCat.ofHom (ScalarQuotient.scalarOne c z))
    (Scalars.h1Iso_scalar c z) (ScalarQuotient.oneHomologyIso_scalar c z)

/-- The genuine degree-two comparison retains the same original scalar action. -/
theorem h2CofaceIso_scalar :
    (CategoryTheory.Sheaf.functorH _ 2).map (Scalars.scalarEnd c z).asHom ≫
        (h2CofaceIso F (Scalars.scalarEnd c)).hom =
      (h2CofaceIso F (Scalars.scalarEnd c)).hom ≫
        AddCommGrpCat.ofHom (ScalarQuotient.scalarTwo c z) := by
  let : Injective (GodementExact.partialResolution F).I₀ :=
    godement_injective_of_scalarEnd F (Scalars.scalarEnd c)
  let : Injective (GodementExact.partialResolution F).I₁ :=
    doubleGodement_injective_of_scalarEnd F (Scalars.scalarEnd c)
  exact composeScalarSquares
    (GodementExact.partialResolution F).h2Iso.hom
    (SheafCupProductResolution.Coface.twoHomologyIso (globalData F)).hom
    ((CategoryTheory.Sheaf.functorH _ 2).map (Scalars.scalarEnd c z).asHom)
    (ShortComplex.homologyMap (Scalars.scalarPartialResolutionMap c z).globalTwoMap)
    (AddCommGrpCat.ofHom (ScalarQuotient.scalarTwo c z))
    (Scalars.h2Iso_scalar c z) (ScalarQuotient.twoHomologyIso_scalar c z)

theorem h1CofaceEquiv_scalar (a : H F 1) :
    h1CofaceEquiv F (Scalars.scalarEnd c)
        (CategoryTheory.Sheaf.H.map (Scalars.scalarEnd c z).asHom 1 a) =
      ScalarQuotient.scalarOne c z (h1CofaceEquiv F (Scalars.scalarEnd c) a) :=
  scalarIso_apply (h1CofaceIso F (Scalars.scalarEnd c))
    ((CategoryTheory.Sheaf.functorH _ 1).map (Scalars.scalarEnd c z).asHom)
    (AddCommGrpCat.ofHom (ScalarQuotient.scalarOne c z)) (h1CofaceIso_scalar c z) a

theorem h2CofaceEquiv_scalar (a : H F 2) :
    h2CofaceEquiv F (Scalars.scalarEnd c)
        (CategoryTheory.Sheaf.H.map (Scalars.scalarEnd c z).asHom 2 a) =
      ScalarQuotient.scalarTwo c z (h2CofaceEquiv F (Scalars.scalarEnd c) a) :=
  scalarIso_apply (h2CofaceIso F (Scalars.scalarEnd c))
    ((CategoryTheory.Sheaf.functorH _ 2).map (Scalars.scalarEnd c z).asHom)
    (AddCommGrpCat.ofHom (ScalarQuotient.scalarTwo c z)) (h2CofaceIso_scalar c z) a

end Wikipedia.HopfProblem.SheafCupProduct
