/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped SimpleGraph

namespace Erdos79

abbrev GraphCode := Σ n : ℕ, SimpleGraph (Fin n)

namespace GraphCode

abbrev vertexCount (G : GraphCode) : ℕ := G.1

abbrev graph (G : GraphCode) : SimpleGraph (Fin G.vertexCount) := G.2

end GraphCode

def NoIsolated (G : GraphCode) : Prop :=
  ∀ v, ¬ G.graph.IsIsolated v

def RamseyAt (F H : GraphCode) (N : ℕ) : Prop :=
  ∀ C : SimpleGraph (Fin N), F.graph ⊑ C ∨ H.graph ⊑ Cᶜ

namespace GraphCode

noncomputable def edgeCount (G : GraphCode) : ℕ :=
  Nat.card G.graph.edgeSet

end GraphCode

def RamseySizeLinear (F : GraphCode) : Prop :=
  ∃ C : ℕ, ∀ H : GraphCode, NoIsolated H → RamseyAt F H (C * H.edgeCount)

abbrev IsContained (F G : GraphCode) : Prop := F.graph ⊑ G.graph

abbrev Isomorphic (F G : GraphCode) : Prop := Nonempty (F.graph ≃g G.graph)

def ProperSubgraph (F G : GraphCode) : Prop :=
  IsContained F G ∧ ¬ Isomorphic F G

def MinimallyNonRamseySizeLinear (G : GraphCode) : Prop :=
  ¬ RamseySizeLinear G ∧
    ∀ F : GraphCode, ProperSubgraph F G → RamseySizeLinear F

theorem erdos_79 :
    ∃ f : ℕ → GraphCode,
      (∀ n, MinimallyNonRamseySizeLinear (f n)) ∧
      Pairwise fun i j ↦ ¬ Isomorphic (f i) (f j) := by
  sorry

end Erdos79
