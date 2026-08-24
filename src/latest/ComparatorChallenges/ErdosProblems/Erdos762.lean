/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

namespace Erdos762

def IsCochromaticColoring {V : Type*} (G : SimpleGraph V) {α : Type*} (c : V → α) : Prop :=
  ∀ i, G.IsClique (c ⁻¹' {i}) ∨ G.IsIndepSet (c ⁻¹' {i})
def CochromaticColorable {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ c : V → Fin n, IsCochromaticColoring G c
noncomputable def cochromaticNumber {V : Type*} (G : SimpleGraph V) : ℕ∞ :=
  sInf { n : ℕ∞ | ∃ m : ℕ, n = m ∧ CochromaticColorable G m }

end Erdos762

theorem Erdos762.not_erdos_762 :
    Not (∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    G.CliqueFree 5 →
    4 ≤ Erdos762.cochromaticNumber G →
    G.chromaticNumber ≤ Erdos762.cochromaticNumber G + 2) := by
  sorry
