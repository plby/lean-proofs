import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Tactic.Ring

/-! # Algebraic assembly of hyperbola strip and boundary errors -/

namespace Erdos1148.DukeArithmetic

lemma norm_hyperbola_error_le {A B P L Z R S T U a b c d : ℝ}
    (hA : ‖A - (Z * S + R * T)‖ ≤ a) (hB : ‖B - P * L‖ ≤ b)
    (hC : ‖(P - Z) * (L - S)‖ ≤ c) (hD : ‖R * (U - T)‖ ≤ d) :
    ‖A + B - S * P - (Z * L + R * U)‖ ≤ a + b + c + d := by
  have heq : A + B - S * P - (Z * L + R * U) =
      (A - (Z * S + R * T)) + (B - P * L) + (P - Z) * (L - S) - R * (U - T) := by ring
  rw [heq]
  calc
    _ ≤ (‖A - (Z * S + R * T)‖ + ‖B - P * L‖) + ‖(P - Z) * (L - S)‖ + ‖R * (U - T)‖ :=
      (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := add_le_add (add_le_add (add_le_add hA hB) hC) hD

end Erdos1148.DukeArithmetic
