/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos914

set_option linter.style.setOption false
set_option linter.style.maxHeartbeats false
set_option linter.style.cases false
set_option linter.flexible false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false


namespace TerminalVertex

variable {α : Type*} [Fintype α] [DecidableEq α]
omit [DecidableEq α]

end TerminalVertex

open Finset

namespace HajnalSzemeredi

open Finset Function SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

open scoped Classical in
def HasDisjointCliques (G : SimpleGraph V) (r m : ℕ) : Prop :=
  ∃ f : Fin m → Finset V,
    (∀ i, (f i).card = r) ∧
    (∀ i, ∀ v ∈ f i, ∀ w ∈ f i, v ≠ w → G.Adj v w) ∧
    (∀ i j, i ≠ j → Disjoint (f i) (f j))
end HajnalSzemeredi

end Erdos914



open Finset
open Finset Function SimpleGraph

namespace Erdos914.HajnalSzemeredi

open scoped Classical in
theorem hajnal_szemeredi_clique_cover {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r m : ℕ) (hr : 1 ≤ r) (hcard : Fintype.card V = r * m)
    (hmin : m * (r - 1) ≤ G.minDegree) :
    HasDisjointCliques G r m := by
  sorry

end Erdos914.HajnalSzemeredi
