import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductBilinearMaps

/-!
# Trilinear extensions on actual singular chains

The scalar-action instances in these pointwise constructions are the supplied
integer-module instances. They therefore apply directly to Mathlib's singular
chain modules, as well as to formal chains.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz

attribute [local instance] integerLinearMapModule integerTensorModule

section Composition

variable {A B C D E A' B' C' : Type*}
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
  [AddCommGroup E] [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
variable [Module ℤ A] [Module ℤ B] [Module ℤ C] [Module ℤ D] [Module ℤ E]
  [Module ℤ A'] [Module ℤ B'] [Module ℤ C']

/-- Postcomposition of an integer trilinear map. -/
def integerTrilinearPostcompose (F : A →ₗ[ℤ] B →ₗ[ℤ] C →ₗ[ℤ] D)
    (g : D →ₗ[ℤ] E) : A →ₗ[ℤ] B →ₗ[ℤ] C →ₗ[ℤ] E where
  toFun a := integerBilinearPostcompose (F a) g
  map_add' a a' := by
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    simp only [integerBilinearPostcompose_apply, map_add, LinearMap.add_apply]
  map_smul' r a := by
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    exact (congrArg (fun l : B →ₗ[ℤ] C →ₗ[ℤ] D => g (l b c))
      (F.map_smul r a)).trans (g.map_smul r (F a b c))

@[simp] theorem integerTrilinearPostcompose_apply
    (F : A →ₗ[ℤ] B →ₗ[ℤ] C →ₗ[ℤ] D) (g : D →ₗ[ℤ] E) (a : A) (b : B) (c : C) :
    integerTrilinearPostcompose F g a b c = g (F a b c) := rfl

/-- Independent precomposition in all three arguments. -/
def integerTrilinearPrecompose (F : A →ₗ[ℤ] B →ₗ[ℤ] C →ₗ[ℤ] D)
    (f : A' →ₗ[ℤ] A) (g : B' →ₗ[ℤ] B) (h : C' →ₗ[ℤ] C) :
    A' →ₗ[ℤ] B' →ₗ[ℤ] C' →ₗ[ℤ] D where
  toFun a := integerBilinearPrecompose (F (f a)) g h
  map_add' a a' := by
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    simp only [integerBilinearPrecompose_apply, map_add, LinearMap.add_apply]
  map_smul' r a := by
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    exact (congrArg (fun x => F x (g b) (h c)) (f.map_smul r a)).trans
      (congrArg (fun l : B →ₗ[ℤ] C →ₗ[ℤ] D => l (g b) (h c))
        (F.map_smul r (f a)))

@[simp] theorem integerTrilinearPrecompose_apply
    (F : A →ₗ[ℤ] B →ₗ[ℤ] C →ₗ[ℤ] D)
    (f : A' →ₗ[ℤ] A) (g : B' →ₗ[ℤ] B) (h : C' →ₗ[ℤ] C)
    (a : A') (b : B') (c : C') :
    integerTrilinearPrecompose F f g h a b c = F (f a) (g b) (h c) := rfl

/-- Compose two bilinear maps with the inner product in the first two inputs. -/
def integerTrilinearLeftAssociated (F : A →ₗ[ℤ] B →ₗ[ℤ] D)
    (G : D →ₗ[ℤ] C →ₗ[ℤ] E) : A →ₗ[ℤ] B →ₗ[ℤ] C →ₗ[ℤ] E where
  toFun a := integerBilinearPrecompose G (F a) LinearMap.id
  map_add' a a' := by
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    simp only [integerBilinearPrecompose_apply, LinearMap.id_apply, map_add,
      LinearMap.add_apply]
  map_smul' r a := by
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    exact (congrArg (fun l : B →ₗ[ℤ] D => G (l b) c) (F.map_smul r a)).trans
      (congrArg (fun l : C →ₗ[ℤ] E => l c) (G.map_smul r (F a b)))

@[simp] theorem integerTrilinearLeftAssociated_apply
    (F : A →ₗ[ℤ] B →ₗ[ℤ] D) (G : D →ₗ[ℤ] C →ₗ[ℤ] E) (a : A) (b : B) (c : C) :
    integerTrilinearLeftAssociated F G a b c = G (F a b) c := rfl

/-- Compose two bilinear maps with the inner product in the last two inputs. -/
def integerTrilinearRightAssociated (F : A →ₗ[ℤ] D →ₗ[ℤ] E)
    (G : B →ₗ[ℤ] C →ₗ[ℤ] D) : A →ₗ[ℤ] B →ₗ[ℤ] C →ₗ[ℤ] E where
  toFun a := integerBilinearPostcompose G (F a)
  map_add' a a' := by
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    simp only [integerBilinearPostcompose_apply, map_add, LinearMap.add_apply]
  map_smul' r a := by
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    exact congrArg (fun l : D →ₗ[ℤ] E => l (G b c)) (F.map_smul r a)

@[simp] theorem integerTrilinearRightAssociated_apply
    (F : A →ₗ[ℤ] D →ₗ[ℤ] E) (G : B →ₗ[ℤ] C →ₗ[ℤ] D) (a : A) (b : B) (c : C) :
    integerTrilinearRightAssociated F G a b c = F a (G b c) := rfl

end Composition

variable (X Y Z : Type) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable (p q r : ℕ) {M : Type} [AddCommGroup M] [Module ℤ M]

/-- Trilinear extension of prescribed values on triples of singular simplices. -/
def chainTrilinearLift
    (f : SingularSimplex X p → SingularSimplex Y q → SingularSimplex Z r → M) :
    Chains X p →ₗ[ℤ] Chains Y q →ₗ[ℤ] Chains Z r →ₗ[ℤ] M :=
  chainLift X p fun σ => chainBilinearLift Y Z q r (f σ)

@[simp] theorem chainTrilinearLift_simplex
    (f : SingularSimplex X p → SingularSimplex Y q → SingularSimplex Z r → M)
    (σ : SingularSimplex X p) (τ : SingularSimplex Y q) (υ : SingularSimplex Z r) :
    chainTrilinearLift X Y Z p q r f
      (simplexChain X p σ) (simplexChain Y q τ) (simplexChain Z r υ) = f σ τ υ := by
  rw [chainTrilinearLift, chainLift_simplex, chainBilinearLift_simplex]

/-- Trilinear maps on actual singular chains are determined by triples of simplices. -/
theorem chainTrilinearMap_ext
    {F G : Chains X p →ₗ[ℤ] Chains Y q →ₗ[ℤ] Chains Z r →ₗ[ℤ] M}
    (h : ∀ σ τ υ,
      F (simplexChain X p σ) (simplexChain Y q τ) (simplexChain Z r υ) =
      G (simplexChain X p σ) (simplexChain Y q τ) (simplexChain Z r υ)) : F = G := by
  apply chainMap_ext X p
  intro σ
  apply chainBilinearMap_ext Y Z q r
  exact h σ

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
