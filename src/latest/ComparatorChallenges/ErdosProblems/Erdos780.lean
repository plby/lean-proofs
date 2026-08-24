/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos780

abbrev Edge (n r : ℕ) := {s : Finset (Fin n) // s.card = r}

def HasMonoMatching {n r t : ℕ} (c : Edge n r → Fin t) (k : ℕ) : Prop :=
  ∃ color : Fin t, ∃ e : Fin k → Edge n r,
    (∀ i, c (e i) = color) ∧
    ∀ i j : Fin k, i ≠ j → Disjoint (e i).1 (e j).1

theorem erdos_780 {n k r t : ℕ} (hr : 1 ≤ r) (ht : 1 ≤ t)
    (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : Edge n r → Fin t) :
    HasMonoMatching c k := by
  sorry

end Erdos780
