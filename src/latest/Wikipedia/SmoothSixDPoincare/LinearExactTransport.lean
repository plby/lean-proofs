import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Transporting exactness through explicit linear equivalences -/

namespace Wikipedia.SmoothSixDPoincare.HomologyTransport

variable {R A B C A' B' C' : Type*} [Ring R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C] [AddCommGroup A'] [Module R A']
  [AddCommGroup B'] [Module R B'] [AddCommGroup C'] [Module R C']

theorem exact_of_equivalences (eA : A ≃ₗ[R] A') (eB : B ≃ₗ[R] B') (eC : C ≃ₗ[R] C')
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (f' : A' →ₗ[R] B') (g' : B' →ₗ[R] C')
    (hf : ∀ a, f' (eA a) = eB (f a)) (hg : ∀ b, g' (eB b) = eC (g b))
    (hexact : LinearMap.range f = LinearMap.ker g) :
    LinearMap.range f' = LinearMap.ker g' := by
  ext b'
  constructor
  · rintro ⟨a', rfl⟩
    obtain ⟨a, rfl⟩ := eA.surjective a'
    have hfa : g (f a) = 0 := by
      have hmem : f a ∈ LinearMap.range f := ⟨a, rfl⟩
      rw [hexact] at hmem
      exact hmem
    change g' (f' (eA a)) = 0
    rw [hf, hg, hfa, map_zero]
  · intro hb'
    obtain ⟨b, rfl⟩ := eB.surjective b'
    have hgb : g b = 0 :=
      eC.injective ((hg b).symm.trans (hb'.trans (map_zero eC).symm))
    have hb : b ∈ LinearMap.range f := by
      rw [hexact]
      exact hgb
    obtain ⟨a, ha⟩ := hb
    exact ⟨eA a, (hf a).trans (congrArg eB ha)⟩

end Wikipedia.SmoothSixDPoincare.HomologyTransport
