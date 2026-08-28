import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductBilinear
import Wikipedia.HopfProblem.SingularMayerVietorisFormalChains

/-!
# Composition of integer bilinear maps

These pointwise constructions retain the supplied integer-module structures.
They allow bilinear comparisons between formal chains and actual singular
chains without identifying either chain module with a replacement model.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open SingularMayerVietoris

attribute [local instance] integerLinearMapModule integerTensorModule

section Composition

variable {A B C D A' B' : Type*}
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
variable [AddCommGroup A'] [AddCommGroup B']
variable [Module ℤ A] [Module ℤ B] [Module ℤ C] [Module ℤ D]
variable [Module ℤ A'] [Module ℤ B']

/-- Postcompose an integer bilinear map with a linear map. -/
def integerBilinearPostcompose (F : A →ₗ[ℤ] B →ₗ[ℤ] C) (g : C →ₗ[ℤ] D) :
    A →ₗ[ℤ] B →ₗ[ℤ] D where
  toFun a := g.comp (F a)
  map_add' a a' := by
    apply LinearMap.ext
    intro b
    exact (congrArg (fun l : B →ₗ[ℤ] C => g (l b)) (F.map_add a a')).trans
      (g.map_add (F a b) (F a' b))
  map_smul' r a := by
    apply LinearMap.ext
    intro b
    exact (congrArg (fun l : B →ₗ[ℤ] C => g (l b)) (F.map_smul r a)).trans
      (g.map_smul r (F a b))

@[simp] theorem integerBilinearPostcompose_apply
    (F : A →ₗ[ℤ] B →ₗ[ℤ] C) (g : C →ₗ[ℤ] D) (a : A) (b : B) :
    integerBilinearPostcompose F g a b = g (F a b) := rfl

/-- Precompose the two arguments of an integer bilinear map independently. -/
def integerBilinearPrecompose (F : A →ₗ[ℤ] B →ₗ[ℤ] C)
    (f : A' →ₗ[ℤ] A) (g : B' →ₗ[ℤ] B) : A' →ₗ[ℤ] B' →ₗ[ℤ] C where
  toFun a := (F (f a)).comp g
  map_add' a a' := by
    apply LinearMap.ext
    intro b
    exact (congrArg (fun x => F x (g b)) (f.map_add a a')).trans
      (congrArg (fun l : B →ₗ[ℤ] C => l (g b)) (F.map_add (f a) (f a')))
  map_smul' r a := by
    apply LinearMap.ext
    intro b
    exact (congrArg (fun x => F x (g b)) (f.map_smul r a)).trans
      (congrArg (fun l : B →ₗ[ℤ] C => l (g b)) (F.map_smul r (f a)))

@[simp] theorem integerBilinearPrecompose_apply
    (F : A →ₗ[ℤ] B →ₗ[ℤ] C) (f : A' →ₗ[ℤ] A) (g : B' →ₗ[ℤ] B) (a : A') (b : B') :
    integerBilinearPrecompose F f g a b = F (f a) (g b) := rfl

end Composition

/-- Bilinear maps on ordered formal chains are determined by pairs of simplex generators. -/
theorem integerFormalBilinearMap_ext (V W : Type*) (p q : ℕ)
    {M : Type*} [AddCommGroup M] [Module ℤ M]
    {F G : FormalChains V p →ₗ[ℤ] FormalChains W q →ₗ[ℤ] M}
    (h : ∀ v w, F (formalSimplex v) (formalSimplex w) =
      G (formalSimplex v) (formalSimplex w)) : F = G := by
  apply formalChains_ext
  intro v
  apply formalChains_ext
  intro w
  exact h v w

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
