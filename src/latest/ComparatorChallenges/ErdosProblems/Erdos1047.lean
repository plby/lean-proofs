import Mathlib

attribute [local instance] Classical.propDecidable

namespace Erdos1047

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
