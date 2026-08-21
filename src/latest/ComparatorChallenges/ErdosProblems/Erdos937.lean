import Mathlib

syntax (name := answerSyntax937Challenge) "answer(" term ")" : term
macro_rules
  | `(answer($t)) => `($t)

namespace Nat

def Full (k n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p ^ k ∣ n

abbrev Powerful : ℕ → Prop := Full 2

end Nat

namespace Erdos937

open Nat Set

def IsCoprimePowerfulAP4 (a d : ℕ) : Prop :=
  0 < d ∧
  a.Powerful ∧ (a + d).Powerful ∧ (a + 2 * d).Powerful ∧ (a + 3 * d).Powerful ∧
  a.Coprime (a + d) ∧ a.Coprime (a + 2 * d) ∧ a.Coprime (a + 3 * d) ∧
  (a + d).Coprime (a + 2 * d) ∧ (a + d).Coprime (a + 3 * d) ∧
  (a + 2 * d).Coprime (a + 3 * d)

theorem erdos_937 :
    answer(True) ↔ {p : ℕ × ℕ | IsCoprimePowerfulAP4 p.1 p.2}.Infinite := by
  sorry

end Erdos937
