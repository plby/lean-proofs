import ErdosProblems.Erdos547.FractionalCompactness

/-!
# Compact optimization of a skew and fractional matching together
-/

namespace Erdos547.DPRS

variable {V : Type*} [Fintype V] (G : SimpleGraph V) (γ : ℝ)

theorem exists_maximizing_mixed_with_constraints (hγ : 0 ≤ γ)
    (P : Set ((V → V → ℝ) × (V → V → ℝ))) (hP : IsClosed P)
    (hne : ∃ σ : SkewMatching G γ, ∃ μ : FractionalMatching G, (σ.weight, μ.weight) ∈ P)
    (objective : ((V → V → ℝ) × (V → V → ℝ)) → ℝ) (hc : Continuous objective) :
    ∃ σ : SkewMatching G γ, ∃ μ : FractionalMatching G, (σ.weight, μ.weight) ∈ P ∧
      ∀ τ : SkewMatching G γ, ∀ ν : FractionalMatching G, (τ.weight, ν.weight) ∈ P →
        objective (τ.weight, ν.weight) ≤ objective (σ.weight, μ.weight) := by
  let F := (feasibleSkew G γ ×ˢ feasibleFractional G) ∩ P
  have hcomp : IsCompact F :=
    ((isCompact_feasibleSkew G γ hγ).prod (isCompact_feasibleFractional G)).inter_right hP
  obtain ⟨σ₀, μ₀, h₀⟩ := hne
  have hnonempty : F.Nonempty := ⟨(σ₀.weight, μ₀.weight),
    ⟨⟨σ₀.nonnegative, σ₀.supported, σ₀.capacity⟩,
      μ₀.symmetric, μ₀.nonnegative, μ₀.supported, μ₀.capacity⟩, h₀⟩
  obtain ⟨p, hp, hmax⟩ := hcomp.exists_isMaxOn hnonempty hc.continuousOn
  let σ : SkewMatching G γ := ⟨hγ, p.1, hp.1.1.1, hp.1.1.2.1, hp.1.1.2.2⟩
  let μ : FractionalMatching G :=
    ⟨p.2, hp.1.2.1, hp.1.2.2.1, hp.1.2.2.2.1, hp.1.2.2.2.2⟩
  refine ⟨σ, μ, hp.2, ?_⟩
  intro τ ν hν
  exact hmax ⟨⟨⟨τ.nonnegative, τ.supported, τ.capacity⟩,
    ν.symmetric, ν.nonnegative, ν.supported, ν.capacity⟩, hν⟩

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_maximizing_mixed_with_constraints
