import Mathlib.Algebra.Exact.Basic
import Mathlib.LinearAlgebra.Prod

/-!
# Exactness through the actual attachment homology identifications

This small algebraic lemma transfers exactness through commuting squares
of proved integral linear equivalences. The geometric applications supply
equivalences induced by the existing homeomorphisms of actual spaces.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology

variable {A B C A' B' C' : Type*}
  [AddCommGroup A] [Module ℤ A] [AddCommGroup B] [Module ℤ B]
  [AddCommGroup C] [Module ℤ C] [AddCommGroup A'] [Module ℤ A']
  [AddCommGroup B'] [Module ℤ B'] [AddCommGroup C'] [Module ℤ C']

/-- Actual commuting equivalences preserve exactness at the middle term. -/
theorem exact_of_linearEquiv_squares
    (f : A →ₗ[ℤ] B) (g : B →ₗ[ℤ] C)
    (f' : A' →ₗ[ℤ] B') (g' : B' →ₗ[ℤ] C')
    (eA : A ≃ₗ[ℤ] A') (eB : B ≃ₗ[ℤ] B') (eC : C ≃ₗ[ℤ] C')
    (hf : f'.comp eA.toLinearMap = eB.toLinearMap.comp f)
    (hg : g'.comp eB.toLinearMap = eC.toLinearMap.comp g)
    (hexact : Function.Exact f g) : Function.Exact f' g' := by
  intro b
  constructor
  · intro hb
    have hgb : g (eB.symm b) = 0 := by
      apply eC.injective
      have h := LinearMap.congr_fun hg (eB.symm b)
      change g' (eB (eB.symm b)) = eC (g (eB.symm b)) at h
      rw [LinearEquiv.apply_symm_apply, hb] at h
      exact h.symm.trans (map_zero eC).symm
    obtain ⟨a, ha⟩ := (hexact (eB.symm b)).mp hgb
    refine ⟨eA a, ?_⟩
    have h := LinearMap.congr_fun hf a
    change f' (eA a) = eB (f a) at h
    exact h.trans ((congrArg eB ha).trans (eB.apply_symm_apply b))
  · rintro ⟨a', rfl⟩
    obtain ⟨a, rfl⟩ := eA.surjective a'
    have hfa := LinearMap.congr_fun hf a
    change f' (eA a) = eB (f a) at hfa
    rw [hfa]
    have hga := LinearMap.congr_fun hg (f a)
    change g' (eB (f a)) = eC (g (f a)) at hga
    rw [hga, hexact.apply_apply_eq_zero, map_zero]

/-- The degree-zero surjectivity endpoint is preserved through the same
genuine commuting identifications. -/
theorem surjective_of_linearEquiv_square (f : A →ₗ[ℤ] B) (f' : A' →ₗ[ℤ] B')
    (eA : A ≃ₗ[ℤ] A') (eB : B ≃ₗ[ℤ] B')
    (hf : f'.comp eA.toLinearMap = eB.toLinearMap.comp f)
    (hsurj : Function.Surjective f) : Function.Surjective f' := by
  intro b
  obtain ⟨a, ha⟩ := hsurj (eB.symm b)
  refine ⟨eA a, ?_⟩
  have h := LinearMap.congr_fun hf a
  change f' (eA a) = eB (f a) at h
  exact h.trans ((congrArg eB ha).trans (eB.apply_symm_apply b))

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology
