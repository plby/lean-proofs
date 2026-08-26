import ErdosProblems.Erdos593.Graph.ShiftGraphChromatic
import ErdosProblems.Erdos593.Graph.ShiftGraphOddGirth

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# High-chromatic host graphs with controlled odd closed walks

This packages the two shift-graph estimates into a single reusable host.
-/

namespace Erdos593

open scoped Cardinal

namespace ShiftGraph

universe u

/-- A canonical well-order whose cardinality is the successor of the beth
number needed for the `r`-dimensional coloring obstruction. -/
def HostOrder (r : ℕ) : Type u :=
  (Order.succ (ℶ_ ((r - 1 : ℕ) : Ordinal.{u}))).ord.ToType

noncomputable instance (r : ℕ) : LinearOrder (HostOrder r) :=
  linearOrder_toType _

/-- The canonical host graph for an odd-closed-walk cutoff `m`. -/
noncomputable def hostGraph (m : ℕ) : SimpleGraph (Tuple (HostOrder (m + 1)) (m + 1)) :=
  graph (HostOrder (m + 1)) (m + 1)

/-- The canonical host has no odd closed walk of length at most `m`. -/
theorem hostGraph_no_odd_closedWalk_up_to (m : ℕ) :
    ∀ ⦃v⦄ (w : (hostGraph m).Walk v v), w.length ≤ m → ¬ Odd w.length := by
  exact no_odd_closedWalk_up_to (HostOrder (m + 1)) (by omega)

/-- The canonical host has no coloring by natural numbers. -/
theorem hostGraph_not_nonempty_coloring_nat (m : ℕ) :
    ¬ Nonempty ((hostGraph m).Coloring ℕ) := by
  apply not_nonempty_coloring_nat_of_beth_lt (Nat.succ_pos m)
  simp only [HostOrder, Cardinal.mk_ord_toType]
  exact Order.lt_succ _

/-- In particular, the canonical host cannot be colored with any prescribed
finite palette. -/
theorem hostGraph_not_nonempty_coloring_fin (m chromaticBound : ℕ) :
    ¬ Nonempty ((hostGraph m).Coloring (Fin chromaticBound)) := by
  rintro ⟨c⟩
  apply hostGraph_not_nonempty_coloring_nat m
  exact ⟨SimpleGraph.Coloring.mk (fun v => (c v : ℕ)) (fun h hEq => by
    exact c.valid h (Fin.ext hEq))⟩

/-- Existential packaging for a prescribed odd-walk cutoff and finite palette. -/
theorem exists_graph_no_short_odd_closedWalk_and_not_colorable
    (m chromaticBound : ℕ) :
    ∃ (V : Type) (G : SimpleGraph V),
      (∀ ⦃v⦄ (w : G.Walk v v), w.length ≤ m → ¬ Odd w.length) ∧
      ¬ Nonempty (G.Coloring (Fin chromaticBound)) := by
  exact ⟨_, hostGraph m, hostGraph_no_odd_closedWalk_up_to m,
    hostGraph_not_nonempty_coloring_fin m chromaticBound⟩

end ShiftGraph

end Erdos593
