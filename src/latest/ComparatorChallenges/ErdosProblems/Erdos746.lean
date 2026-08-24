/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos746

noncomputable def uniformProbability {Ω : Type*} [Fintype Ω] (event : Ω → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter event).card : ℝ) / Fintype.card Ω

abbrev Edge (n : ℕ) := (⊤ : SimpleGraph (Fin n)).edgeFinset

abbrev FixedEdgeGraph (n m : ℕ) := Set.powersetCard (Edge n) m

def edgeEmbedding (n : ℕ) : Edge n ↪ Sym2 (Fin n) :=
  Function.Embedding.subtype
    (fun e => e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset)

def graphOfEdges {n : ℕ} (s : Finset (Edge n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (s.map (edgeEmbedding n) : Set (Sym2 (Fin n)))

namespace FixedEdgeGraph

def graph {n m : ℕ} (G : FixedEdgeGraph n m) : SimpleGraph (Fin n) :=
  graphOfEdges G.1

end FixedEdgeGraph

noncomputable def hamiltonianProbability (n m : ℕ) : ℝ :=
  uniformProbability (fun G : FixedEdgeGraph n m =>
    (FixedEdgeGraph.graph G).IsHamiltonian)

theorem erdos_746 :
    ∀ ε : ℝ, 0 < ε → ∀ m : ℕ → ℕ,
      (∀ᶠ n : ℕ in Filter.atTop,
        (1 / 2 + ε) * (n : ℝ) * Real.log (n : ℝ) ≤ (m n : ℝ)) →
      (∀ᶠ n : ℕ in Filter.atTop, m n ≤ n.choose 2) →
      Filter.Tendsto (fun n ↦ Erdos746.hamiltonianProbability n (m n)) Filter.atTop (nhds 1) := by
  sorry

end Erdos746
