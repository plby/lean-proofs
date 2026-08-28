import Wikipedia.HopfProblem.SingularMayerVietorisSequenceAlgebra

/-!
# Transport of the right object of an exact homology sequence

These integral linear-algebra lemmas transport an exact sequence through
an actual linear equivalence of its right homology module. The incoming
map is postcomposed with the equivalence and the connecting map is
precomposed with its inverse. No homology comparison is assumed here;
the application supplies its proved comparison equivalence.
-/

namespace Wikipedia.HopfProblem.SingularMayerVietoris

variable {A P B C : Type*}
  [AddCommGroup A] [Module ℤ A] [AddCommGroup P] [Module ℤ P]
  [AddCommGroup B] [Module ℤ B] [AddCommGroup C] [Module ℤ C]

/-- Exactness is preserved when the right homology module is replaced
through a genuine linear equivalence. -/
theorem rightTransport_range_eq_ker (e : B ≃ₗ[ℤ] C)
    (g : P →ₗ[ℤ] B) (δ : B →ₗ[ℤ] A)
    (h : LinearMap.range g = LinearMap.ker δ) :
    LinearMap.range (e.toLinearMap.comp g) =
      LinearMap.ker (δ.comp e.symm.toLinearMap) := by
  ext c
  change (∃ p, e (g p) = c) ↔ δ (e.symm c) = 0
  constructor
  · rintro ⟨p, rfl⟩
    rw [LinearEquiv.symm_apply_apply]
    have hp : g p ∈ LinearMap.range g := ⟨p, rfl⟩
    rw [h] at hp
    exact hp
  · intro hc
    have hp : e.symm c ∈ LinearMap.range g := by
      rw [h]
      exact hc
    obtain ⟨p, hp⟩ := hp
    exact ⟨p, (congrArg e hp).trans (e.apply_symm_apply c)⟩

/-- Replacing the domain of the connecting map by an equivalent module
does not change its image in the next homology group. -/
theorem rightTransport_connecting_range (e : B ≃ₗ[ℤ] C) (δ : B →ₗ[ℤ] A) :
    LinearMap.range (δ.comp e.symm.toLinearMap) = LinearMap.range δ :=
  e.symm.range_comp δ

/-- Postcomposing the incoming map with the equivalence preserves its kernel. -/
theorem rightTransport_second_ker (e : B ≃ₗ[ℤ] C) (g : P →ₗ[ℤ] B) :
    LinearMap.ker (e.toLinearMap.comp g) = LinearMap.ker g :=
  e.ker_comp g

/-- Surjectivity at degree zero is preserved by the right-module equivalence. -/
theorem rightTransport_second_surjective (e : B ≃ₗ[ℤ] C) (g : P →ₗ[ℤ] B)
    (hg : Function.Surjective g) : Function.Surjective (e.toLinearMap.comp g) :=
  e.surjective.comp hg

end Wikipedia.HopfProblem.SingularMayerVietoris
