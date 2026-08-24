/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Algebra.Prime.Defs

namespace Erdos1187b

def Prime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p
def MonochromaticAP {c : Nat} (color : Nat → Fin c) (a d k : Nat) : Prop :=
  ∀ i : Nat, i < k → color (a + i * d) = color a

end Erdos1187b

theorem Erdos1187b.not_erdos_1187 :
    Not (∀ (c k : Nat), 0 < c → 3 ≤ k → ∀ color : Nat → Fin c,
      ∃ a p : Nat, Erdos1187b.Prime p ∧ Erdos1187b.MonochromaticAP color a p k) := by
  sorry
