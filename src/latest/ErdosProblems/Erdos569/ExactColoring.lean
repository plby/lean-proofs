/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos569.Coloring

/-! # Simultaneous linear and quadratic bounds on the number of colors -/

namespace Erdos569

open Erdos79 Erdos570

theorem exists_colorable_half_square (H : GraphCode) (hm : 4 ≤ H.edgeCount) :
    ∃ q : ℕ, 2 * q ≤ H.edgeCount ∧ q * q ≤ 2 * H.edgeCount ∧
      H.graph.Colorable (q + 1) := by
  classical
  let m := H.edgeCount
  have hedge : H.graph.edgeFinset.card ≤ m := by
    rw [← GraphCode.edgeCount_eq_card_edgeFinset]
  by_cases hq : m / 2 ≤ Nat.sqrt (2 * m)
  · refine ⟨m / 2, by dsimp [m]; omega, ?_, colorable_half_edge_bound H.graph hm hedge⟩
    exact (Nat.mul_le_mul hq hq).trans (Nat.sqrt_le _)
  · refine ⟨Nat.sqrt (2 * m), ?_, Nat.sqrt_le _, colorable_sqrt_twice_edge_bound H.graph hedge⟩
    dsimp only [m] at hq ⊢
    omega

end Erdos569
