import ErdosProblems.Erdos591.OverlapLabels

/-! # The last lower selection as an upper first-leaf view -/

namespace Erdos591.Positive.Game.LastFirstLabels

variable {H : Set ℕ} {B a c : ℕ}

def upper_first_view (D : LastFirstLabels H B a c) : LastFirstLabels H B 1 c where
  lower := {D.pivot}
  upper := D.upper
  pivot := D.pivot
  marker := D.marker
  lower_card := by simp
  upper_card := D.upper_card
  pivot_lower := by simp
  pivot_upper := D.pivot_upper
  lower_le := fun _ hx => (Finset.mem_singleton.mp hx).le
  upper_ge := D.upper_ge
  lower_fresh := by
    intro x hx
    rw [Finset.mem_singleton.mp hx]
    exact D.lower_fresh _ D.pivot_lower
  upper_fresh := D.upper_fresh
  marker_fresh := D.marker_fresh

theorem pivot_rank (D : LastFirstLabels H B a c) :
    (D.lower.filter (fun x => x ≤ D.pivot)).card = a := by
  rw [Finset.filter_eq_self.mpr D.lower_le, D.lower_card]

#print axioms pivot_rank

end Erdos591.Positive.Game.LastFirstLabels
