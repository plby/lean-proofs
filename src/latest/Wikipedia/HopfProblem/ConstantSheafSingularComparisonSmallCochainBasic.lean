import Wikipedia.HopfProblem.ConstantSheafSingularComparisonSmallEquivalence
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCochainHomotopy

/-!
# Actual small singular cochains with arbitrary abelian coefficients

The complex is the additive dual of the original small-chain subcomplex.
Its comparison map is restriction along the literal small-chain inclusion.
The established small-chain homotopy equivalence dualizes to that same
restriction, without a divisibility or injectivity assumption on coefficients.
-/

noncomputable section

open CategoryTheory Set

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] {ι : Type*}

/-- Additive cochains on the genuine small-chain group. -/
abbrev SmallCochains (U : ι → Set X) (A : AddCommGrpCat.{0}) (n : ℕ) :=
  (smallComplex U).X n →+ A

/-- The actual additive dual of the original small-chain subcomplex. -/
abbrev smallCochainComplex (U : ι → Set X) (A : AddCommGrpCat.{0}) :=
  dualComplex (smallComplex U) A

variable (A : AddCommGrpCat.{0}) (U : ι → Set X)

/-- Literal restriction of a singular cochain to small chains. -/
def smallCochainRestriction : singularCochainComplex X A ⟶ smallCochainComplex U A :=
  dualMap A (smallInclusion U)

@[simp]
theorem smallCochainRestriction_apply (n : ℕ) (φ : Cochains X A n)
    (c : smallChainSubmodule U n) :
    (smallCochainRestriction A U).f n φ c = φ c.1 := rfl

/-- Restriction to an arbitrary open cover is the forward map of a genuine
cochain homotopy equivalence for every abelian coefficient group. -/
def smallCochainHomotopyEquiv (hU : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = univ) :
    HomotopyEquiv (singularCochainComplex X A) (smallCochainComplex U A) :=
  dualHomotopyEquiv A (smallChainHomotopyEquiv U hU hcover)

@[simp]
theorem smallCochainHomotopyEquiv_hom (hU : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = univ) :
    (smallCochainHomotopyEquiv A U hU hcover).hom = smallCochainRestriction A U := rfl

/-- The actual restriction is a quasi-isomorphism in every degree. -/
theorem smallCochainRestriction_quasiIso (hU : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = univ) : QuasiIso (smallCochainRestriction A U) :=
  (smallCochainHomotopyEquiv A U hU hcover).quasiIso_hom

/-- The native cohomology comparison induced by actual restriction. -/
def smallCochainHomologyIso (hU : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = univ) (n : ℕ) :
    (singularCochainComplex X A).homology n ≅ (smallCochainComplex U A).homology n :=
  (smallCochainHomotopyEquiv A U hU hcover).toHomologyIso n

@[simp]
theorem smallCochainHomologyIso_hom (hU : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = univ) (n : ℕ) :
    (smallCochainHomologyIso A U hU hcover n).hom =
      HomologicalComplex.homologyMap (smallCochainRestriction A U) n := rfl

/-- Coefficient changes commute with literal small-cochain restriction. -/
theorem smallCochainRestriction_coefficient_naturality {B : AddCommGrpCat.{0}}
    (α : A ⟶ B) :
    smallCochainRestriction A U ≫ dualCoefficientMap A (smallComplex U) α =
      coefficientMap X α ≫ smallCochainRestriction B U :=
  dualCoefficientMap_naturality A α (smallInclusion U)

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
