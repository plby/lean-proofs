import Mathlib.Algebra.Prime.Defs

namespace Erdos1187b

def Prime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p
def MonochromaticAP {c : Nat} (color : Nat → Fin c) (a d k : Nat) : Prop :=
  ∀ i : Nat, i < k → color (a + i * d) = color a
def SecondQuestionStatement : Prop :=
  ∀ (c k : Nat), 0 < c → 3 ≤ k → ∀ color : Nat → Fin c,
    ∃ a p : Nat, Prime p ∧ MonochromaticAP color a p k
end Erdos1187b


open scoped Classical in
theorem Erdos1187b.second_question_general_statement_is_false :
    Not Erdos1187b.SecondQuestionStatement
  := by
  sorry
