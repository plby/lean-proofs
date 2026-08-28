import Wikipedia.HopfProblem.FirstHurewiczChainNaturality
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Bilinear extensions on actual singular chains

Pairs of singular simplices determine a bilinear map on Mathlib's actual
integral singular-chain modules. Its tensor-product lift is likewise defined
using the actual chain modules, without replacing them by formal chains.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz
open scoped TensorProduct

/-- The standard pointwise module, retaining the specified integer scalar action.
Clients using bilinear operators can enable this instance locally. -/
local instance integerLinearMapModule {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [modA : Module ℤ A] [modB : Module ℤ B] : Module ℤ (A →ₗ[ℤ] B) :=
  @LinearMap.module ℤ ℤ ℤ A B _ _ _ _ modA modB (RingHom.id ℤ) _ modB
    (@smulCommClass_self ℤ B _ modB.toMulAction)

/-- The standard tensor-product module, with the specified actions on both factors. -/
local instance integerTensorModule {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [modA : Module ℤ A] [modB : Module ℤ B] : Module ℤ (A ⊗[ℤ] B) :=
  @TensorProduct.instModule ℤ _ A B _ _ modA modB

section PartialEvaluation

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [Module ℤ A] [Module ℤ B] [Module ℤ C]

/-- Evaluate the second argument of an integer bilinear map, retaining the given modules. -/
def integerBilinearRightApply (F : A →ₗ[ℤ] B →ₗ[ℤ] C) (b : B) : A →ₗ[ℤ] C where
  toFun a := F a b
  map_add' a a' := congrArg (fun l : B →ₗ[ℤ] C => l b) (F.map_add a a')
  map_smul' r a := congrArg (fun l : B →ₗ[ℤ] C => l b) (F.map_smul r a)

@[simp] theorem integerBilinearRightApply_apply (F : A →ₗ[ℤ] B →ₗ[ℤ] C) (b : B) (a : A) :
    integerBilinearRightApply F b a = F a b := rfl

/-- Flip an integer bilinear map without changing any of its scalar-action instances. -/
def integerBilinearFlip (F : A →ₗ[ℤ] B →ₗ[ℤ] C) : B →ₗ[ℤ] A →ₗ[ℤ] C where
  toFun := integerBilinearRightApply F
  map_add' b b' := by
    apply LinearMap.ext
    intro a
    exact (F a).map_add b b'
  map_smul' r b := by
    apply LinearMap.ext
    intro a
    exact (F a).map_smul r b

@[simp] theorem integerBilinearFlip_apply (F : A →ₗ[ℤ] B →ₗ[ℤ] C) (b : B) (a : A) :
    integerBilinearFlip F b a = F a b := rfl

end PartialEvaluation

variable (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
variable (p q : ℕ) {M : Type} [AddCommGroup M] [modM : Module ℤ M]

/-- Bilinear extension of prescribed values on pairs of actual singular simplices. -/
def chainBilinearLift (f : SingularSimplex X p → SingularSimplex Y q → M) :
    Chains X p →ₗ[ℤ] Chains Y q →ₗ[ℤ] M :=
  chainLift X p fun σ => chainLift Y q (f σ)

@[simp] theorem chainBilinearLift_simplex_left
    (f : SingularSimplex X p → SingularSimplex Y q → M) (σ : SingularSimplex X p) :
    chainBilinearLift X Y p q f (simplexChain X p σ) = chainLift Y q (f σ) :=
  chainLift_simplex X p _ σ

@[simp] theorem chainBilinearLift_simplex
    (f : SingularSimplex X p → SingularSimplex Y q → M)
    (σ : SingularSimplex X p) (τ : SingularSimplex Y q) :
    chainBilinearLift X Y p q f (simplexChain X p σ) (simplexChain Y q τ) = f σ τ := by
  rw [chainBilinearLift_simplex_left, chainLift_simplex]

@[simp] theorem chainBilinearLift_simplex_right
    (f : SingularSimplex X p → SingularSimplex Y q → M)
    (c : Chains X p) (τ : SingularSimplex Y q) :
    chainBilinearLift X Y p q f c (simplexChain Y q τ) =
      chainLift X p (fun σ => f σ τ) c := by
  let e := integerBilinearRightApply (chainBilinearLift X Y p q f) (simplexChain Y q τ)
  have h : e = chainLift X p (fun σ => f σ τ) := by
    apply chainMap_ext X p
    intro σ
    exact (chainBilinearLift_simplex X Y p q f σ τ).trans
      (chainLift_simplex X p (fun σ => f σ τ) σ).symm
  exact LinearMap.congr_fun h c

/-- Bilinear maps on actual chains are determined by pairs of simplex generators. -/
theorem chainBilinearMap_ext
    {F G : Chains X p →ₗ[ℤ] Chains Y q →ₗ[ℤ] M}
    (h : ∀ σ τ, F (simplexChain X p σ) (simplexChain Y q τ) =
      G (simplexChain X p σ) (simplexChain Y q τ)) : F = G := by
  apply chainMap_ext X p
  intro σ
  apply chainMap_ext Y q
  intro τ
  exact h σ τ

/-- The universal tensor-product extension on the actual singular-chain modules. -/
def chainTensorLift (f : SingularSimplex X p → SingularSimplex Y q → M) :
    Chains X p ⊗[ℤ] Chains Y q →ₗ[ℤ] M :=
  TensorProduct.lift (chainBilinearLift X Y p q f)

@[simp] theorem chainTensorLift_tmul
    (f : SingularSimplex X p → SingularSimplex Y q → M)
    (c : Chains X p) (d : Chains Y q) :
    chainTensorLift X Y p q f (c ⊗ₜ[ℤ] d) = chainBilinearLift X Y p q f c d := rfl

@[simp] theorem chainTensorLift_simplex_tmul_simplex
    (f : SingularSimplex X p → SingularSimplex Y q → M)
    (σ : SingularSimplex X p) (τ : SingularSimplex Y q) :
    chainTensorLift X Y p q f (simplexChain X p σ ⊗ₜ[ℤ] simplexChain Y q τ) = f σ τ := by
  rw [chainTensorLift_tmul, chainBilinearLift_simplex]

/-- Tensor-product maps are determined by tensor products of simplex generators. -/
theorem chainTensorMap_ext
    {F G : Chains X p ⊗[ℤ] Chains Y q →ₗ[ℤ] M}
    (h : ∀ σ τ, F (simplexChain X p σ ⊗ₜ[ℤ] simplexChain Y q τ) =
      G (simplexChain X p σ ⊗ₜ[ℤ] simplexChain Y q τ)) : F = G := by
  apply TensorProduct.ext
  apply chainBilinearMap_ext X Y p q
  intro σ τ
  exact h σ τ

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
