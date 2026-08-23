/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib


namespace Erdos1047

open scoped Classical in
theorem main_result : ∃ (f : Polynomial ℂ) (c : ℝ) (m : ℕ),
  f.Monic ∧
  f.roots.Nodup ∧
  f.roots.toFinset.card = m ∧
  c > 0 ∧
  (f.roots.toFinset.image
    (fun z => connectedComponentIn {w | ‖f.eval w‖ ≤ c} z)).card = m ∧
  ∃ K ∈
      (f.roots.toFinset.image
        (fun z => connectedComponentIn {w | ‖f.eval w‖ ≤ c} z)),
    ¬ Convex ℝ K := by
  sorry

end Erdos1047

namespace Erdos1047

open scoped Classical in
theorem erdos_1047 :
  ¬ (∀ (f : Polynomial ℂ) (c : ℝ) (m : ℕ),
      f.Monic →
      f.roots.Nodup →
      f.roots.toFinset.card = m →
      c > 0 →
      (f.roots.toFinset.image
            (fun z => connectedComponentIn {w | ‖f.eval w‖ ≤ c} z)).card = m →
      ∀ K ∈ (f.roots.toFinset.image
            (fun z => connectedComponentIn {w | ‖f.eval w‖ ≤ c} z)),
        Convex ℝ K) := by
  sorry

end Erdos1047
