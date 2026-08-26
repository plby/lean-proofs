import ErdosProblems.Erdos118.Reused591.CriticalRootLabels

namespace Erdos118.Reused591

/-!
# Upper first/last leaf at consecutive prescribed lower ranks

The finite root-label construction is also a leaf-label construction.
Its singleton lower view supplies the saved first-leaf response, while
the original full lower label and its next selected entry are retained.
-/

namespace Erdos591.Positive.Game.CriticalRootLabels

def leaf_view {H : Set ℕ} {B n c s : ℕ}
    (D : CriticalRootLabels H B n c s) : LastFirstLabels H B 1 c where
  lower := {D.shared}
  upper := D.upper
  pivot := D.shared
  marker := D.marker
  lower_card := by simp
  upper_card := D.upper_card
  pivot_lower := by simp
  pivot_upper := D.shared_upper
  lower_le := fun _ hx => (Finset.mem_singleton.mp hx).le
  upper_ge := fun x hx => (D.upper_bounds x hx).1
  lower_fresh := by
    intro x hx
    rw [Finset.mem_singleton.mp hx]
    exact D.lower_fresh _ D.shared_lower
  upper_fresh := D.upper_fresh
  marker_fresh := D.marker_fresh

end Erdos591.Positive.Game.CriticalRootLabels

end Erdos118.Reused591
