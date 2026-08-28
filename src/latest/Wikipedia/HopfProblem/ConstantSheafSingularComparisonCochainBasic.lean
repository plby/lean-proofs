import Wikipedia.HopfProblem.SingularMayerVietorisSmallChainsBasis
import Wikipedia.HopfProblem.FirstHurewiczChainNaturality
import Mathlib.Algebra.Category.Grp.Preadditive

/-!
# Cochains with arbitrary abelian coefficients on the original singular chains

A cochain is an additive homomorphism from the actual integral singular
chain group.  The original simplex basis identifies these homomorphisms
with arbitrary functions on singular simplices.  No tensor replacement or
change of the singular chain complex is involved.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

open FirstHurewicz

/-- An additive homomorphism is linear for any given integer-module
structures, including the actual structure on a categorical chain group. -/
def addHomToIntLinearMap {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [modM : Module ℤ M] [modN : Module ℤ N] (f : M →+ N) : M →ₗ[ℤ] N where
  toFun := f
  map_add' := f.map_add
  map_smul' n x := by
    change f (modM.smul n x) = modN.smul n (f x)
    rw [int_smul_eq_zsmul, int_smul_eq_zsmul]
    exact f.map_zsmul n x

@[simp]
theorem addHomToIntLinearMap_apply {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N] (f : M →+ N) (x : M) :
    addHomToIntLinearMap f x = f x := rfl

/-- Integer-linear maps and additive homomorphisms agree with their original
values, for the chosen integer-module structures. -/
def intLinearAddHomEquiv (M N : Type*) [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N] : (M →ₗ[ℤ] N) ≃+ (M →+ N) where
  toFun := LinearMap.toAddMonoidHom
  invFun := addHomToIntLinearMap
  left_inv f := by ext; rfl
  right_inv f := by ext; rfl
  map_add' _ _ := rfl

/-- Arbitrary-coefficient cochains on the actual integer singular chains. -/
abbrev Cochains (X : Type) [TopologicalSpace X] (A : AddCommGrpCat.{0}) (n : ℕ) :=
  Chains X n →+ A

variable (X : Type) [TopologicalSpace X] (A : AddCommGrpCat.{0}) (n : ℕ)

/-- Evaluation on the original simplex generators. -/
def cochainEval (φ : Cochains X A n) (σ : SingularSimplex X n) : A :=
  φ (simplexChain X n σ)

/-- Extend simplex values using the actual singular-chain coproduct map. -/
def cochainFromValues (f : SingularSimplex X n → A) : Cochains X A n :=
  (chainLift X n f).toAddMonoidHom

@[simp]
theorem cochainFromValues_simplex (f : SingularSimplex X n → A)
    (σ : SingularSimplex X n) :
    cochainFromValues X A n f (simplexChain X n σ) = f σ :=
  chainLift_simplex X n f σ

/-- The actual simplex generators determine an additive cochain. -/
theorem cochain_ext {φ ψ : Cochains X A n}
    (h : ∀ σ : SingularSimplex X n,
      φ (simplexChain X n σ) = ψ (simplexChain X n σ)) : φ = ψ := by
  have he : addHomToIntLinearMap φ = addHomToIntLinearMap ψ :=
    chainMap_ext X n h
  exact congrArg LinearMap.toAddMonoidHom he

/-- The original singular simplex basis identifies cochains with arbitrary
simplex-value functions, additively. -/
def cochainEvalEquiv : Cochains X A n ≃+ (SingularSimplex X n → A) where
  toFun := cochainEval X A n
  invFun := cochainFromValues X A n
  left_inv φ := by
    apply cochain_ext X A n
    intro σ
    exact cochainFromValues_simplex X A n (cochainEval X A n φ) σ
  right_inv f := by
    funext σ
    exact cochainFromValues_simplex X A n f σ
  map_add' _ _ := rfl

@[simp]
theorem cochainEvalEquiv_apply (φ : Cochains X A n) (σ : SingularSimplex X n) :
    cochainEvalEquiv X A n φ σ = φ (simplexChain X n σ) := rfl

@[simp]
theorem cochainEvalEquiv_symm_apply (f : SingularSimplex X n → A) :
    (cochainEvalEquiv X A n).symm f = cochainFromValues X A n f := rfl

section Composition

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- Literal precomposition on additive cochains. -/
def precompose (f : M →+ N) : (N →+ A) →+ (M →+ A) where
  toFun φ := φ.comp f
  map_zero' := by ext; rfl
  map_add' _ _ := by ext; rfl

@[simp]
theorem precompose_apply (f : M →+ N) (φ : N →+ A) (c : M) :
    precompose A f φ c = φ (f c) := rfl

/-- Literal coefficient postcomposition. -/
def postcompose {B : AddCommGrpCat.{0}} (α : A →+ B) : (M →+ A) →+ (M →+ B) where
  toFun φ := α.comp φ
  map_zero' := by ext; exact α.map_zero
  map_add' φ ψ := by ext c; exact α.map_add (φ c) (ψ c)

@[simp]
theorem postcompose_apply {B : AddCommGrpCat.{0}} (α : A →+ B)
    (φ : M →+ A) (c : M) : postcompose A α φ c = α (φ c) := rfl

end Composition

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
