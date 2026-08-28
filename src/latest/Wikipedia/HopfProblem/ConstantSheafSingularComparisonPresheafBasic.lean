import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCochainSingular
import Mathlib.Topology.Sheaves.Abelian

/-!
# Actual singular cochain presheaves

On an open subset the presheaf takes the additive cochains on its original
singular chains.  Every restriction is pullback by the genuine inclusion.
The native differentials form natural transformations and hence an actual
cochain complex of presheaves.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

open FirstHurewicz

variable (X : TopCat.{0}) (A : AddCommGrpCat.{0})

/-- Restrict the actual singular cochain functor to the open subsets. -/
def cochainOpenFunctor : (Opens X)ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{0} ℕ :=
  (Opens.toTopCat X).op ⋙ singularCochainFunctor A

/-- The degreewise presheaf of cochains on actual open subspaces. -/
abbrev cochainPresheaf (n : ℕ) : TopCat.Presheaf AddCommGrpCat.{0} X where
  obj U := AddCommGrpCat.of (Cochains U.unop A n)
  map i := (singularPullback A ((Opens.toTopCat X).map i.unop).hom).f n
  map_id U :=
    (cochainOpenFunctor X A ⋙ HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℕ) n).map_id U
  map_comp i j :=
    (cochainOpenFunctor X A ⋙
      HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℕ) n).map_comp i j

@[simp]
theorem cochainPresheaf_obj (n : ℕ) (U : Opens X) :
    (cochainPresheaf X A n).obj (op U) = AddCommGrpCat.of (Cochains U A n) := rfl

/-- Restrictions precompose with the original singular chain map of inclusion. -/
@[simp]
theorem cochainPresheaf_map_apply (n : ℕ) {U V : Opens X} (i : U ⟶ V)
    (φ : Cochains V A n) (c : Chains U n) :
    (cochainPresheaf X A n).map i.op φ c =
      φ (inducedChain ((Opens.toTopCat X).map i).hom n c) := rfl

@[simp]
theorem cochainPresheaf_map_simplex (n : ℕ) {U V : Opens X} (i : U ⟶ V)
    (φ : Cochains V A n) (σ : SingularSimplex U n) :
    (cochainPresheaf X A n).map i.op φ (simplexChain U n σ) =
      φ (simplexChain V n (((Opens.toTopCat X).map i).hom.comp σ)) :=
  singularPullback_simplex A ((Opens.toTopCat X).map i).hom n φ σ

/-- The original cochain differential commutes with actual open restrictions. -/
def presheafDifferential (i j : ℕ) : cochainPresheaf X A i ⟶ cochainPresheaf X A j where
  app U := (singularCochainComplex U.unop A).d i j
  naturality _ _ f :=
    (singularPullback A ((Opens.toTopCat X).map f.unop).hom).comm i j

@[simp]
theorem presheafDifferential_app (i j : ℕ) (U : Opens X) :
    (presheafDifferential X A i j).app (op U) =
      (singularCochainComplex U A).d i j := rfl

/-- The native singular cochain complex on all opens, before sheafification. -/
abbrev cochainPresheafComplex : CochainComplex (TopCat.Presheaf AddCommGrpCat.{0} X) ℕ where
  X n := cochainPresheaf X A n
  d i j := presheafDifferential X A i j
  shape i j hij := by
    apply NatTrans.ext
    funext U
    exact (singularCochainComplex U.unop A).shape i j hij
  d_comp_d' i j k _ _ := by
    apply NatTrans.ext
    funext U
    exact (singularCochainComplex U.unop A).d_comp_d i j k

@[simp]
theorem cochainPresheafComplex_X (n : ℕ) :
    (cochainPresheafComplex X A).X n = cochainPresheaf X A n := rfl

@[simp]
theorem cochainPresheafComplex_d (i j : ℕ) :
    (cochainPresheafComplex X A).d i j = presheafDifferential X A i j := rfl

variable {A}

/-- Coefficient postcomposition is a morphism of the actual cochain presheaves. -/
def presheafCoefficientMap {B : AddCommGrpCat.{0}} (α : A ⟶ B) (n : ℕ) :
    cochainPresheaf X A n ⟶ cochainPresheaf X B n where
  app U := (coefficientMap U.unop α).f n
  naturality _ _ _ := by
    apply AddCommGrpCat.hom_ext
    ext φ c
    rfl

@[simp]
theorem presheafCoefficientMap_app_apply {B : AddCommGrpCat.{0}} (α : A ⟶ B)
    (n : ℕ) (U : Opens X) (φ : Cochains U A n) (c : Chains U n) :
    (presheafCoefficientMap X α n).app (op U) φ c = α (φ c) := rfl

/-- Actual coefficient changes give morphisms of the whole presheaf complex. -/
def presheafCoefficientComplexMap {B : AddCommGrpCat.{0}} (α : A ⟶ B) :
    cochainPresheafComplex X A ⟶ cochainPresheafComplex X B where
  f n := presheafCoefficientMap X α n
  comm' i j _ := by
    apply NatTrans.ext
    funext U
    exact (coefficientMap U.unop α).comm i j

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
