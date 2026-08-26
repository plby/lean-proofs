/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Density

open scoped SimpleGraph

namespace Erdos547b

/-- An equal cut of the Ramsey host `Fin (2 * n - 2)`. -/
def IsRamseyBalancedCut {n : ℕ} (V₁ V₂ : Finset (Fin (2 * n - 2))) : Prop :=
  Disjoint V₁ V₂ ∧ V₁ ∪ V₂ = Finset.univ ∧ V₁.card = n - 1 ∧ V₂.card = n - 1

/-- Zhao's dense-crossing-edge extremal case, specialized to the Ramsey host. -/
def ZhaoExtremalCaseOne {n : ℕ} (α : ℚ) (G : SimpleGraph (Fin (2 * n - 2))) : Prop :=
  by
    classical
    exact ∃ V₁ V₂, IsRamseyBalancedCut V₁ V₂ ∧ 1 - α ≤ G.edgeDensity V₁ V₂

/-- Zhao's sparse-crossing-edge extremal case, specialized to the Ramsey host. -/
def ZhaoExtremalCaseTwo {n : ℕ} (α : ℚ) (G : SimpleGraph (Fin (2 * n - 2))) : Prop :=
  by
    classical
    exact ∃ V₁ V₂, IsRamseyBalancedCut V₁ V₂ ∧ G.edgeDensity V₁ V₂ ≤ α

/-- The conclusion that a Ramsey-sized host contains every tree allowed by
Zhao's even-host theorem. -/
def ZhaoContainsAllTrees {n : ℕ} (G : SimpleGraph (Fin (2 * n - 2))) : Prop :=
  ∀ (t : ℕ) (T : SimpleGraph (Fin t)), T.IsTree → t - 1 ≤ n - 1 → T ⊑ G

/-- Proposition 3.1 of Zhao, only at the value `σ = 1/2` needed here. -/
def ZhaoDenseCutEmbeddingProperty : Prop :=
  by
    classical
    exact ∃ c : ℚ, 0 < c ∧ c < 1 ∧ ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n →
      ∀ G : SimpleGraph (Fin (2 * n - 2)),
        n - 1 ≤ (Finset.univ.filter fun v => n - 1 ≤ G.degree v).card →
          ZhaoExtremalCaseOne c G → ZhaoContainsAllTrees G

/-- Theorem 3.2 of Zhao, specialized to even Ramsey hosts. -/
def ZhaoSparseCutEmbeddingProperty : Prop :=
  by
    classical
    exact ∃ α₂ : ℚ, 0 < α₂ ∧ α₂ < 1 ∧ ∃ n₂ : ℕ,
      ∀ α : ℚ, 0 < α → α ≤ α₂ → ∀ n : ℕ, n₂ ≤ n →
        ∀ G : SimpleGraph (Fin (2 * n - 2)),
          n - 1 ≤ (Finset.univ.filter fun v => n - 1 ≤ G.degree v).card →
            ZhaoExtremalCaseTwo α G → ZhaoContainsAllTrees G

/-- Theorem 3.3 of Zhao in the stronger high-degree regime used by Theorem
1.6: a host either contains all allowed trees or is in one of the two
extremal cases. -/
def ZhaoStabilityProperty : Prop :=
  by
    classical
    exact ∀ α : ℚ, 0 < α → ∃ n₃ : ℕ, ∀ n : ℕ, n₃ ≤ n →
      ∀ G : SimpleGraph (Fin (2 * n - 2)),
        n - 1 ≤ (Finset.univ.filter fun v => n - 1 ≤ G.degree v).card →
          ZhaoContainsAllTrees G ∨ ZhaoExtremalCaseOne α G ∨ ZhaoExtremalCaseTwo α G

end Erdos547b
