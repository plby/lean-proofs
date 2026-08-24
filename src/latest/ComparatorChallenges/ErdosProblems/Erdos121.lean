/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos121

def HasSquareProduct (S : Finset ℕ) : Prop :=
  IsSquare (S.prod id)

def IsAdmissible (k N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧
    ∀ S : Finset ℕ, S ⊆ A → S.card = k → ¬ HasSquareProduct S

def Attainable (k N m : ℕ) : Prop :=
  ∃ A : Finset ℕ, IsAdmissible k N A ∧ A.card = m

noncomputable def extremalSize (k N : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (Attainable k N) N

theorem erdos_121 :
    ∀ k : ℕ, 4 ≤ k → ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      (extremalSize k N : ℝ) ≤ (1 - c) * N := by
  sorry

end Erdos121
