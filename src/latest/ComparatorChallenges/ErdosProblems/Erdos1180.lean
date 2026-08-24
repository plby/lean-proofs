/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1180

def AdmissibleDenom (ε : ℝ) (p n : ℕ) : Prop :=
  0 < n ∧ (n : ℝ) ≤ (p : ℝ) ^ ε ∧ Nat.Coprime n p

def Represents (ε : ℝ) (p : ℕ) (a : ZMod p) (xs : List ℕ) : Prop :=
  (∀ n ∈ xs, AdmissibleDenom ε p n) ∧
    (List.map (fun n : ℕ ↦ ((n : ZMod p)⁻¹)) xs).sum = a

theorem erdos_1180 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℕ, ∀ p : ℕ, p.Prime → ∀ a : ZMod p,
      ∃ xs : List ℕ, xs.length ≤ C ∧ Erdos1180.Represents ε p a xs := by
  sorry

end Erdos1180
