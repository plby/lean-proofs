import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCochainBasic
import Mathlib.Algebra.Category.Grp.Abelian

/-!
# The actual additive cochain dual complex with arbitrary coefficients

The differential is precomposition by the original chain differential.
Chain maps act contravariantly and coefficient maps act covariantly; all
commutativity identities are identities of the native maps.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

variable (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (A : AddCommGrpCat.{0})

/-- The actual boundary-precomposition map on additive cochains. -/
def dualDifferential (i j : ℕ) : (K.X i →+ A) →+ (K.X j →+ A) :=
  precompose A (K.d j i).hom.toAddMonoidHom

@[simp]
theorem dualDifferential_apply (i j : ℕ) (φ : K.X i →+ A) (c : K.X j) :
    dualDifferential K A i j φ c = φ ((K.d j i).hom c) := rfl

/-- The genuine additive cochain complex dual to a native integer chain complex. -/
abbrev dualComplex : CochainComplex AddCommGrpCat.{0} ℕ where
  X n := AddCommGrpCat.of (K.X n →+ A)
  d i j := AddCommGrpCat.ofHom (dualDifferential K A i j)
  shape i j hij := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro φ
    apply AddMonoidHom.ext
    intro c
    change φ ((K.d j i).hom c) = 0
    rw [K.shape j i hij]
    exact φ.map_zero
  d_comp_d' i j k _ _ := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro φ
    apply AddMonoidHom.ext
    intro c
    change φ ((K.d j i).hom ((K.d k j).hom c)) = 0
    have h : (K.d j i).hom ((K.d k j).hom c) = 0 :=
      congrArg (fun f : K.X k ⟶ K.X i => f.hom c) (K.d_comp_d k j i)
    exact (congrArg φ h).trans φ.map_zero

@[simp]
theorem dualComplex_X (n : ℕ) : (dualComplex K A).X n = AddCommGrpCat.of (K.X n →+ A) :=
  rfl

@[simp]
theorem dualComplex_d_apply (i j : ℕ) (φ : K.X i →+ A) (c : K.X j) :
    (dualComplex K A).d i j φ c = φ ((K.d j i).hom c) := rfl

variable {K} {L M : ChainComplex (ModuleCat.{0} ℤ) ℕ}

/-- Pullback along the original chain map. -/
def dualMap (f : K ⟶ L) : dualComplex L A ⟶ dualComplex K A where
  f n := AddCommGrpCat.ofHom (precompose A (f.f n).hom.toAddMonoidHom)
  comm' i j _ := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro φ
    apply AddMonoidHom.ext
    intro c
    change φ ((f.f i).hom ((K.d j i).hom c)) =
      φ ((L.d j i).hom ((f.f j).hom c))
    exact congrArg φ (congrArg (fun g : K.X j ⟶ L.X i => g.hom c) (f.comm j i).symm)

@[simp]
theorem dualMap_apply (f : K ⟶ L) (n : ℕ) (φ : L.X n →+ A) (c : K.X n) :
    (dualMap A f).f n φ c = φ ((f.f n).hom c) := rfl

@[simp]
theorem dualMap_id (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) :
    dualMap A (𝟙 K) = 𝟙 (dualComplex K A) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply AddCommGrpCat.hom_ext
  ext φ c
  rfl

@[simp]
theorem dualMap_comp (f : K ⟶ L) (g : L ⟶ M) :
    dualMap A (f ≫ g) = dualMap A g ≫ dualMap A f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply AddCommGrpCat.hom_ext
  ext φ c
  rfl

/-- Covariant change of coefficient group on the genuine cochain complex. -/
def dualCoefficientMap (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    {B : AddCommGrpCat.{0}} (α : A ⟶ B) : dualComplex K A ⟶ dualComplex K B where
  f n := AddCommGrpCat.ofHom (postcompose A α.hom)
  comm' i j _ := by
    apply AddCommGrpCat.hom_ext
    ext φ c
    rfl

@[simp]
theorem dualCoefficientMap_apply (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    {B : AddCommGrpCat.{0}} (α : A ⟶ B) (n : ℕ) (φ : K.X n →+ A) (c : K.X n) :
    (dualCoefficientMap A K α).f n φ c = α (φ c) := rfl

@[simp]
theorem dualCoefficientMap_id (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) :
    dualCoefficientMap A K (𝟙 A) = 𝟙 (dualComplex K A) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply AddCommGrpCat.hom_ext
  ext φ c
  rfl

@[simp]
theorem dualCoefficientMap_comp (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    {B C : AddCommGrpCat.{0}} (α : A ⟶ B) (β : B ⟶ C) :
    dualCoefficientMap A K (α ≫ β) =
      dualCoefficientMap A K α ≫ dualCoefficientMap B K β := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply AddCommGrpCat.hom_ext
  ext φ c
  rfl

/-- Coefficient changes commute with the actual contravariant chain-map action. -/
theorem dualCoefficientMap_naturality {B : AddCommGrpCat.{0}} (α : A ⟶ B)
    (f : K ⟶ L) :
    dualMap A f ≫ dualCoefficientMap A K α =
      dualCoefficientMap A L α ≫ dualMap B f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply AddCommGrpCat.hom_ext
  ext φ c
  rfl

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
