import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyOpenRestriction

/-!
# Actual top-open cohomology is actual sheaf cohomology

The free abelian sheaf represented by the top open and the actual
constant integer sheaf represent the same global-section functor.
Their canonical representing maps are inverse by naturality. Applying
the genuine contravariant Ext functor gives the comparison in every
degree, without a comparison or vanishing hypothesis.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.OpenRestriction

open CuspNormalization.SheafCohomologyFinitePushforward

variable (X : TopCat.{0})

/-- The two actual representations of the same global-section group. -/
def topHomEquiv (F : TopCat.Sheaf AddCommGrpCat.{0} X) :
    (freeOpen (⊤ : Opens X) ⟶ F) ≃+ (integerSheaf X ⟶ F) :=
  (freeHomAddEquiv ⊤ F).trans (homGlobalEquiv X F).symm

theorem topHomEquiv_sections (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (h : freeOpen (⊤ : Opens X) ⟶ F) :
    homGlobalEquiv X F (topHomEquiv X F h) = freeHomEquiv ⊤ F h :=
  (homGlobalEquiv X F).apply_symm_apply _

theorem topHomEquiv_naturality {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
    (h : freeOpen (⊤ : Opens X) ⟶ F) (g : F ⟶ G) :
    topHomEquiv X G (h ≫ g) = topHomEquiv X F h ≫ g := by
  apply (homGlobalEquiv X G).injective
  exact Eq.trans (topHomEquiv_sections X G (h ≫ g))
    (Eq.trans (freeHomEquiv_naturality ⊤ h g)
      (Eq.trans (congrArg (g.hom.app (op ⊤)) (topHomEquiv_sections X F h).symm)
        (homGlobalEquiv_naturality X (topHomEquiv X F h) g).symm))

/-- The universal top-open section gives an actual map from the integer sheaf. -/
def integerToFreeTop : integerSheaf X ⟶ freeOpen (⊤ : Opens X) :=
  topHomEquiv X (freeOpen (⊤ : Opens X)) (𝟙 _)

/-- The universal integer-sheaf section gives the inverse representing map. -/
def freeTopToInteger : freeOpen (⊤ : Opens X) ⟶ integerSheaf X :=
  (topHomEquiv X (integerSheaf X)).symm (𝟙 _)

theorem integerToFreeTop_comp {F : TopCat.Sheaf AddCommGrpCat.{0} X}
    (h : freeOpen (⊤ : Opens X) ⟶ F) :
    integerToFreeTop X ≫ h = topHomEquiv X F h :=
  (topHomEquiv_naturality X (𝟙 _) h).symm.trans
    (congrArg (topHomEquiv X F) (Category.id_comp h))

theorem integerToFreeTop_freeTopToInteger :
    integerToFreeTop X ≫ freeTopToInteger X = 𝟙 (integerSheaf X) :=
  (integerToFreeTop_comp X (freeTopToInteger X)).trans
    ((topHomEquiv X (integerSheaf X)).apply_symm_apply _)

theorem freeTopToInteger_integerToFreeTop :
    freeTopToInteger X ≫ integerToFreeTop X = 𝟙 (freeOpen (⊤ : Opens X)) := by
  apply (topHomEquiv X (freeOpen (⊤ : Opens X))).injective
  rw [topHomEquiv_naturality]
  change (topHomEquiv X (integerSheaf X))
    ((topHomEquiv X (integerSheaf X)).symm (𝟙 _)) ≫ integerToFreeTop X = integerToFreeTop X
  rw [AddEquiv.apply_symm_apply, Category.id_comp]

/-- The actual two representing sheaves are canonically isomorphic. -/
def freeTopIsoInteger : freeOpen (⊤ : Opens X) ≅ integerSheaf X where
  hom := freeTopToInteger X
  inv := integerToFreeTop X
  hom_inv_id := freeTopToInteger_integerToFreeTop X
  inv_hom_id := integerToFreeTop_freeTopToInteger X

/-- The genuine Ext functor carries the actual representing isomorphism
to the actual top-open/sheaf-cohomology comparison. -/
def topCohomologyIso (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ) :
    CategoryTheory.Sheaf.H'.{0} F n (⊤ : Opens X) ≅
      AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} F n) :=
  ((extFunctor (C := TopCat.Sheaf AddCommGrpCat.{0} X) n).mapIso
    (freeTopIsoInteger X).symm.op).app F

/-- Actual top-open cohomology and genuine sheaf cohomology agree in every degree. -/
def topCohomologyEquiv (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ) :
    CategoryTheory.Sheaf.H'.{0} F n (⊤ : Opens X) ≃+
      CategoryTheory.Sheaf.H.{0} F n :=
  (topCohomologyIso X F n).addCommGroupIsoToAddEquiv

theorem topCohomologyEquiv_mk₀ {F : TopCat.Sheaf AddCommGrpCat.{0} X}
    (h : freeOpen (⊤ : Opens X) ⟶ F) :
    topCohomologyEquiv X F 0 (Ext.mk₀ h) = Ext.mk₀ (integerToFreeTop X ≫ h) := by
  change (Ext.mk₀ (integerToFreeTop X)).comp (Ext.mk₀ h) (zero_add 0) = _
  exact Ext.mk₀_comp_mk₀ _ _

theorem topCohomologyEquiv_naturality {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
    (g : F ⟶ G) (n : ℕ) (a : CategoryTheory.Sheaf.H'.{0} F n (⊤ : Opens X)) :
    topCohomologyEquiv X G n
        (((CategoryTheory.Sheaf.cohomologyPresheafFunctor
          (Opens.grothendieckTopology X) n).map g).app (op ⊤) a) =
      CategoryTheory.Sheaf.H.map g n (topCohomologyEquiv X F n a) :=
  ConcreteCategory.congr_hom
    (((extFunctor (C := TopCat.Sheaf AddCommGrpCat.{0} X) n).mapIso
      (freeTopIsoInteger X).symm.op).hom.naturality g) a

theorem topCohomology_subsingleton (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ)
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F n (⊤ : Opens X))] :
    Subsingleton (CategoryTheory.Sheaf.H.{0} F n) :=
  (topCohomologyEquiv X F n).symm.injective.subsingleton

theorem topOpenCohomology_subsingleton (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ)
    [Subsingleton (CategoryTheory.Sheaf.H.{0} F n)] :
    Subsingleton (CategoryTheory.Sheaf.H'.{0} F n (⊤ : Opens X)) :=
  (topCohomologyEquiv X F n).injective.subsingleton

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.OpenRestriction
