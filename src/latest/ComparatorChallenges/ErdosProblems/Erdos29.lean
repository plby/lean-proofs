/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped Pointwise

namespace Erdos29

noncomputable def addRepCount (A : Set ℕ) (n : ℕ) : ℕ :=
  by
    classical
    exact ((Finset.HasAntidiagonal.antidiagonal
      (self := Finset.Nat.instHasAntidiagonal) n : Finset (ℕ × ℕ)).filter
      fun ab : ℕ × ℕ => ab.1 ∈ A ∧ ab.2 ∈ A).card

def SolvesErdos29 (A : Set ℕ) : Prop :=
  A + A = Set.univ ∧
    ∀ ε : ℝ, 0 < ε →
      Asymptotics.IsLittleO Filter.atTop
        (fun n : ℕ => (addRepCount A n : ℝ))
        (fun n : ℕ => (n : ℝ) ^ ε)

/-! ## The explicit construction -/

theorem erdos_29 : ∃ A : Set ℕ, SolvesErdos29 A := by
  sorry

end Erdos29
