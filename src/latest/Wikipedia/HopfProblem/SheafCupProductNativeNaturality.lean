import Wikipedia.HopfProblem.SheafCupProductNative

/-!
# Coefficient naturality of the native sheaf cup product

The actual ring-sheaf morphism gives the actual map of Godement partial
resolutions. The already proved Ext-comparison squares and coface
quotient squares therefore identify its native cohomology maps with the
literal coefficient maps. Consequently the original map preserves the
native degree-one cup product.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafCupProduct

open GodementRing

private theorem composeSquares {A B D A' B' D' : AddCommGrpCat.{0}}
    (a : A ⟶ B) (b : B ⟶ D) (a' : A' ⟶ B') (b' : B' ⟶ D')
    (x : A ⟶ A') (y : B ⟶ B') (z : D ⟶ D')
    (h₁ : x ≫ a' = a ≫ y) (h₂ : y ≫ b' = b ≫ z) :
    x ≫ (a' ≫ b') = (a ≫ b) ≫ z := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]

private theorem equivSquare_apply {A B A' B' : AddCommGrpCat.{0}}
    (e : A ≅ B) (e' : A' ≅ B') (f : A ⟶ A') (g : B ⟶ B')
    (h : f ≫ e'.hom = e.hom ≫ g) (a : A) :
    e'.addCommGroupIsoToAddEquiv (f a) = g (e.addCommGroupIsoToAddEquiv a) :=
  ConcreteCategory.congr_hom h a

variable {X : TopCat.{0}} {F G : RingSheaf X} (f : F ⟶ G)

/-- The original map on genuine Ext-defined sheaf cohomology. -/
def cohomologyMap (n : ℕ) : H F n →+ H G n :=
  CategoryTheory.Sheaf.H.map ((forgetSheaf X).map f) n

theorem globalOneMap_eq :
    (GodementExact.partialResolutionMap f).globalOneMap =
      SheafCupProductResolution.Coface.oneMap (cofaceMap f (sections ⊤)) := rfl

theorem globalTwoMap_eq :
    (GodementExact.partialResolutionMap f).globalTwoMap =
      SheafCupProductResolution.Coface.twoMap (cofaceMap f (sections ⊤)) := rfl

variable (ρ : ℂ →+* End ((forgetSheaf X).obj F))
  (σ : ℂ →+* End ((forgetSheaf X).obj G))

/-- The native degree-one comparison is natural for the original ring-sheaf map. -/
theorem h1CofaceIso_naturality :
    (CategoryTheory.Sheaf.functorH _ 1).map ((forgetSheaf X).map f) ≫
        (h1CofaceIso G σ).hom =
      (h1CofaceIso F ρ).hom ≫
        AddCommGrpCat.ofHom (cofaceMap f (sections ⊤)).cohomologyOneMap := by
  let : Injective (GodementExact.partialResolution F).I₀ :=
    godement_injective_of_scalarEnd F ρ
  let : Injective (GodementExact.partialResolution G).I₀ :=
    godement_injective_of_scalarEnd G σ
  exact composeSquares
    (GodementExact.partialResolution F).h1Iso.hom
    (SheafCupProductResolution.Coface.oneHomologyIso (globalData F)).hom
    (GodementExact.partialResolution G).h1Iso.hom
    (SheafCupProductResolution.Coface.oneHomologyIso (globalData G)).hom
    ((CategoryTheory.Sheaf.functorH _ 1).map ((forgetSheaf X).map f))
    (ShortComplex.homologyMap (GodementExact.partialResolutionMap f).globalOneMap)
    (AddCommGrpCat.ofHom (cofaceMap f (sections ⊤)).cohomologyOneMap)
    (GodementExact.partialResolutionMap f).h1Iso_naturality
    (SheafCupProductResolution.Coface.oneHomologyIso_naturality
      (cofaceMap f (sections ⊤)))

/-- The native degree-two comparison is likewise coefficient-natural. -/
theorem h2CofaceIso_naturality :
    (CategoryTheory.Sheaf.functorH _ 2).map ((forgetSheaf X).map f) ≫
        (h2CofaceIso G σ).hom =
      (h2CofaceIso F ρ).hom ≫
        AddCommGrpCat.ofHom (cofaceMap f (sections ⊤)).cohomologyTwoMap := by
  let : Injective (GodementExact.partialResolution F).I₀ :=
    godement_injective_of_scalarEnd F ρ
  let : Injective (GodementExact.partialResolution F).I₁ :=
    doubleGodement_injective_of_scalarEnd F ρ
  let : Injective (GodementExact.partialResolution G).I₀ :=
    godement_injective_of_scalarEnd G σ
  let : Injective (GodementExact.partialResolution G).I₁ :=
    doubleGodement_injective_of_scalarEnd G σ
  exact composeSquares
    (GodementExact.partialResolution F).h2Iso.hom
    (SheafCupProductResolution.Coface.twoHomologyIso (globalData F)).hom
    (GodementExact.partialResolution G).h2Iso.hom
    (SheafCupProductResolution.Coface.twoHomologyIso (globalData G)).hom
    ((CategoryTheory.Sheaf.functorH _ 2).map ((forgetSheaf X).map f))
    (ShortComplex.homologyMap (GodementExact.partialResolutionMap f).globalTwoMap)
    (AddCommGrpCat.ofHom (cofaceMap f (sections ⊤)).cohomologyTwoMap)
    (GodementExact.partialResolutionMap f).h2Iso_naturality
    (SheafCupProductResolution.Coface.twoHomologyIso_naturality
      (cofaceMap f (sections ⊤)))

theorem h1CofaceEquiv_naturality (a : H F 1) :
    h1CofaceEquiv G σ (cohomologyMap f 1 a) =
      (cofaceMap f (sections ⊤)).cohomologyOneMap (h1CofaceEquiv F ρ a) :=
  equivSquare_apply (h1CofaceIso F ρ) (h1CofaceIso G σ)
    ((CategoryTheory.Sheaf.functorH _ 1).map ((forgetSheaf X).map f))
    (AddCommGrpCat.ofHom (cofaceMap f (sections ⊤)).cohomologyOneMap)
    (h1CofaceIso_naturality f ρ σ) a

theorem h2CofaceEquiv_naturality (a : H F 2) :
    h2CofaceEquiv G σ (cohomologyMap f 2 a) =
      (cofaceMap f (sections ⊤)).cohomologyTwoMap (h2CofaceEquiv F ρ a) :=
  equivSquare_apply (h2CofaceIso F ρ) (h2CofaceIso G σ)
    ((CategoryTheory.Sheaf.functorH _ 2).map ((forgetSheaf X).map f))
    (AddCommGrpCat.ofHom (cofaceMap f (sections ⊤)).cohomologyTwoMap)
    (h2CofaceIso_naturality f ρ σ) a

/-- The actual native cohomology map of any ring-sheaf morphism
preserves the genuine low-degree cup product. -/
theorem cup_naturality (a b : H F 1) :
    cohomologyMap f 2 (cup F ρ a b) =
      cup G σ (cohomologyMap f 1 a) (cohomologyMap f 1 b) :=
  transportPairing_naturality
    (h1CofaceEquiv F ρ) (h2CofaceEquiv F ρ)
    (h1CofaceEquiv G σ) (h2CofaceEquiv G σ)
    (globalData F).cup (globalData G).cup
    (cofaceMap f (sections ⊤)).cohomologyOneMap
    (cofaceMap f (sections ⊤)).cohomologyTwoMap
    (cohomologyMap f 1) (cohomologyMap f 2)
    (h1CofaceEquiv_naturality f ρ σ) (h2CofaceEquiv_naturality f ρ σ)
    (cofaceMap f (sections ⊤)).map_cup a b

end Wikipedia.HopfProblem.SheafCupProduct
