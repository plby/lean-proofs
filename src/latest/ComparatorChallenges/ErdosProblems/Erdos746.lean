import Mathlib

open Filter

noncomputable section


namespace Erdos746

open scoped Classical in
def uniformProbability {Ω : Type*} [Fintype Ω] (event : Ω → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter event).card : ℝ) / Fintype.card Ω

end Erdos746

namespace Erdos746

open scoped Classical in
abbrev Edge (n : ℕ) := (⊤ : SimpleGraph (Fin n)).edgeFinset

end Erdos746

namespace Erdos746

open scoped Classical in
abbrev FixedEdgeGraph (n m : ℕ) := Set.powersetCard (Edge n) m

end Erdos746

namespace Erdos746

open scoped Classical in
def edgeEmbedding (n : ℕ) : Edge n ↪ Sym2 (Fin n) :=
  Function.Embedding.subtype
    (fun e => e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset)

end Erdos746

namespace Erdos746

open scoped Classical in
def graphOfEdges {n : ℕ} (s : Finset (Edge n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (s.map (edgeEmbedding n) : Set (Sym2 (Fin n)))

end Erdos746

namespace Erdos746.FixedEdgeGraph

open scoped Classical in
def graph {n m : ℕ} (G : FixedEdgeGraph n m) : SimpleGraph (Fin n) :=
  graphOfEdges G.1

end Erdos746.FixedEdgeGraph

namespace Erdos746

open scoped Classical in
def hamiltonianProbability (n m : ℕ) : ℝ :=
  uniformProbability (fun G : FixedEdgeGraph n m =>
    (FixedEdgeGraph.graph G).IsHamiltonian)

end Erdos746

namespace Erdos746

open scoped Classical in
noncomputable def edgeThreshold (ε : ℝ) (n : ℕ) : ℕ :=
  Nat.ceil ((1 / 2 + ε) * (n : ℝ) * Real.log (n : ℝ))

end Erdos746

namespace Erdos746

open scoped Classical in
def Erdos746Statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ m : ℕ → ℕ,
    (∀ᶠ n : ℕ in atTop,
      (1 / 2 + ε) * (n : ℝ) * Real.log (n : ℝ) ≤ (m n : ℝ)) →
    (∀ᶠ n : ℕ in atTop, m n ≤ n.choose 2) →
    Tendsto (fun n ↦ hamiltonianProbability n (m n)) atTop (nhds 1)

end Erdos746

namespace Erdos746

open scoped Classical in
theorem erdos_746 : Erdos746Statement := by
  sorry

end Erdos746

end
