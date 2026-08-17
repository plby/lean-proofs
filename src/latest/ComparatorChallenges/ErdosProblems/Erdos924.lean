import Mathlib

open Finset Fintype
open SimpleGraph
open scoped SimpleGraph

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace Erdos924

structure BipartiteRel (L R : Type*) where
  Rel : L → R → Prop

end Erdos924

namespace Erdos924.BipartiteRel

variable {L R L' R' ι K : Type*}

def Edge (G : BipartiteRel L R) := {p : L × R // G.Rel p.1 p.2}

end Erdos924.BipartiteRel

namespace Erdos924.BipartiteRel

def EdgeLabeling (G : BipartiteRel L R) (K : Type*) := G.Edge → K

end Erdos924.BipartiteRel

namespace Erdos924

def IsEdgeRamseyForClique {V : Type*} (G : SimpleGraph V) (k l : ℕ) : Prop :=
  ∀ C : SimpleGraph.EdgeLabeling G (Fin k),
    ∃ i : Fin k, ∃ S : Finset V, (C.labelGraph i).IsNClique l S

/-! ## Arbitrary-palette finite hypergraph Ramsey -/

end Erdos924

namespace Erdos924

theorem erdos_924 : True ↔
    ∀ k l : ℕ, 2 ≤ k → 3 ≤ l →
      ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
        G.CliqueFree (l + 1) ∧ IsEdgeRamseyForClique G k l := by
  sorry

end Erdos924

end
