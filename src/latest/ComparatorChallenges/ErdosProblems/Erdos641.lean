/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos641

open scoped Classical in
def IsCycleGraph {V : Type*} [Fintype V] (C : SimpleGraph V) : Prop :=
  C.Connected ∧ C.IsRegularOfDegree 2

def HasCommonVertexCycles {V : Type*} [Fintype V]
    (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∃ m : ℕ, 0 < m ∧
    ∃ C : Fin r → SimpleGraph (Fin m),
      (∀ i, IsCycleGraph (C i)) ∧
      (∀ ⦃i j : Fin r⦄, i ≠ j → Disjoint (C i) (C j)) ∧
      Nonempty (SimpleGraph.Copy (⨆ i, C i) G)

def ErdosHajnalProperty (F : ℕ → ℕ) : Prop :=
  ∀ r : ℕ, 1 ≤ r →
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      (F r : ℕ∞) ≤ G.chromaticNumber → HasCommonVertexCycles G r

theorem not_erdos_641 : ¬ ∃ F : ℕ → ℕ, ErdosHajnalProperty F := by
  sorry

end Erdos641
