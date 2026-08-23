/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Finset
open scoped Finset

noncomputable section


namespace Erdos801

variable {V : Type*} [Fintype V] [DecidableEq V]

open scoped Classical in
def edgesInside (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e ↦ e.toFinset ⊆ S)

end Erdos801

namespace Erdos801

variable {V : Type*} [Fintype V] [DecidableEq V]

open scoped Classical in
noncomputable def edgeCountInside (G : SimpleGraph V) (S : Finset V) : ℕ :=
  (@edgesInside V _ _ G (Classical.decRel G.Adj) S).card

end Erdos801

namespace Erdos801

open scoped Classical in
theorem erdos_801 :
    ∃ C N : ℕ, 0 < C ∧ ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
      G.indepNum ≤ Nat.sqrt n →
        ∃ S : Finset (Fin n), S.card ≤ Nat.sqrt n ∧
          Nat.sqrt n * Nat.log 2 n ≤ C * edgeCountInside G S := by
  sorry

end Erdos801

end
