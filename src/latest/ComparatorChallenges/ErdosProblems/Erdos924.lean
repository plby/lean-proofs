/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Finset Fintype
open SimpleGraph
open scoped SimpleGraph

noncomputable section

namespace Erdos924

open scoped Classical in
structure BipartiteRel (L R : Type*) where
  Rel : L → R → Prop

end Erdos924

namespace Erdos924.BipartiteRel

variable {L R L' R' ι K : Type*}

open scoped Classical in
def Edge (G : BipartiteRel L R) := {p : L × R // G.Rel p.1 p.2}

end Erdos924.BipartiteRel

namespace Erdos924.BipartiteRel

open scoped Classical in
def EdgeLabeling (G : BipartiteRel L R) (K : Type*) := G.Edge → K

end Erdos924.BipartiteRel

namespace Erdos924

open scoped Classical in
def IsEdgeRamseyForClique {V : Type*} (G : SimpleGraph V) (k l : ℕ) : Prop :=
  ∀ C : SimpleGraph.EdgeLabeling G (Fin k),
    ∃ i : Fin k, ∃ S : Finset V, (C.labelGraph i).IsNClique l S

/-! ## Arbitrary-palette finite hypergraph Ramsey -/

end Erdos924

namespace Erdos924

open scoped Classical in
theorem erdos_924 :
    ∀ k l : ℕ, 2 ≤ k → 3 ≤ l →
      ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
        G.CliqueFree (l + 1) ∧ IsEdgeRamseyForClique G k l := by
  sorry

end Erdos924

end
