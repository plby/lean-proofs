import Wikipedia.HopfProblem.SingularCohomologyFree
import Mathlib.GroupTheory.OrderOfElement

/-!
# Injective actual cohomology pullback from finite-index homology image

An integral functional is determined by its values on any finite-index
submodule: the subgroup index multiplies every element into that submodule,
and the integers have no torsion.  Combining this elementary fact with the
proved natural evaluation isomorphism yields injectivity of the actual
singular-cohomology pullback whenever the actual homological pushforward
has finite-index image and the target's actual homology is projective.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SingularCohomologyFree

section Linear

variable {M N : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]

/-- Integral dual restriction is injective when the actual linear map has finite-index image. -/
theorem dualMap_injective_of_finiteIndex (f : M →ₗ[ℤ] N)
    (hf : (LinearMap.range f).toAddSubgroup.FiniteIndex) :
    Function.Injective f.dualMap := by
  intro φ ψ h
  ext x
  have hx := (LinearMap.range f).toAddSubgroup.nsmul_index_mem x
  obtain ⟨a, ha⟩ := hx
  have he : φ (f a) = ψ (f a) := LinearMap.congr_fun h a
  rw [ha, map_nsmul, map_nsmul] at he
  have hn : ((LinearMap.range f).toAddSubgroup.index : ℤ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hf.index_ne_zero
  apply mul_left_cancel₀ hn
  simpa only [nsmul_eq_mul] using he

end Linear

open SingularMayerVietoris

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [∀ n, Module.Projective ℤ (SingularHomology Y n)]

/-- Finite-index image of the genuine homology map forces injectivity
of actual cohomological pullback. -/
theorem singularCohomologyPullback_injective_of_finiteIndex (f : C(X, Y)) (n : ℕ)
    (hf : (LinearMap.range (singularHomologyMap f n)).toAddSubgroup.FiniteIndex) :
    Function.Injective (singularCohomologyPullback f n) := by
  intro a b hab
  apply (singularEvaluationEquiv Y n).injective
  apply dualMap_injective_of_finiteIndex (singularHomologyMap f n) hf
  ext x
  change singularEvaluation Y n a (singularHomologyMap f n x) =
    singularEvaluation Y n b (singularHomologyMap f n x)
  rw [← singularEvaluation_naturality, ← singularEvaluation_naturality, hab]

end Wikipedia.HopfProblem.SingularCohomologyFree
