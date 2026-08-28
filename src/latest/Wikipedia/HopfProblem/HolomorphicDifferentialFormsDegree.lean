import Wikipedia.HopfProblem.HolomorphicDifferentialForms
import Mathlib.LinearAlgebra.Alternating.Basic

/-!
# Genuine forms above the native tangent dimension

An alternating covector of degree larger than the size of an actual
basis is zero. This gives the same statement for every analytic section
of the original alternating cotangent bundle, without a coordinate
ansatz for the section.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicDifferentialForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem covector_eq_zero_of_basis_card_lt {n p : ℕ} (b : Module.Basis (Fin n) ℂ E)
    (hp : n < p) (α : E [⋀^Fin p]→L[ℂ] ℂ) : α = 0 := by
  have ha : α.toAlternatingMap = 0 := by
    apply b.ext_alternating
    intro v hv
    have hc := Fintype.card_le_of_injective v hv
    simp only [Fintype.card_fin] at hc
    omega
  ext v
  exact congrArg (fun a : E [⋀^Fin p]→ₗ[ℂ] ℂ => a v) ha

variable {M : Type*} [FiniteDimensional ℂ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ω M]

omit [FiniteDimensional ℂ E] in
theorem form_eq_zero_of_basis_card_lt {n p : ℕ} (b : Module.Basis (Fin n) ℂ E)
    (hp : n < p) (θ : Form E M p) : θ = 0 := by
  apply ContMDiffSection.ext
  intro x
  exact covector_eq_zero_of_basis_card_lt b hp (θ x)

end Wikipedia.HopfProblem.HolomorphicDifferentialForms
