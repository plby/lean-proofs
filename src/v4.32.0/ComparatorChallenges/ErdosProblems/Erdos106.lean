import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.CompletePartialOrder

open scoped BigOperators

namespace Erdos106

noncomputable section

abbrev Point := ℝ × ℝ

structure Square where
  center : Point
  direction : Point
  side : ℝ

def Square.point (S : Square) (lam mu : ℝ) : Point :=
  (S.center.1 + lam * S.direction.1 - mu * S.direction.2,
    S.center.2 + lam * S.direction.2 + mu * S.direction.1)

def Square.carrier (S : Square) : Set Point :=
  {p | ∃ lam mu : ℝ,
    |lam| ≤ S.side / 2 ∧ |mu| ≤ S.side / 2 ∧ p = S.point lam mu}

def Square.openCarrier (S : Square) : Set Point :=
  {p | ∃ lam mu : ℝ,
    |lam| < S.side / 2 ∧ |mu| < S.side / 2 ∧ p = S.point lam mu}

def Square.IsGenuine (S : Square) : Prop :=
  0 < S.side ∧ S.direction.1 ^ 2 + S.direction.2 ^ 2 = 1

def box (L : ℝ) : Set Point :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ L ∧ 0 ≤ p.2 ∧ p.2 ≤ L}

def IsPackingIn (L : ℝ) {n : ℕ} (P : Fin n → Square) : Prop :=
  (∀ i, (P i).IsGenuine) ∧
  (∀ i, (P i).carrier ⊆ box L) ∧
  (∀ i j, i ≠ j → Disjoint (P i).openCarrier (P j).openCarrier)

def totalSideLength {n : ℕ} (P : Fin n → Square) : ℝ :=
  ∑ i, (P i).side

def attainableSideSums (n : ℕ) : Set ℝ :=
  {t | ∃ P : Fin n → Square, IsPackingIn 1 P ∧ totalSideLength P = t}

noncomputable def f (n : ℕ) : ℝ :=
  sSup (attainableSideSums n)

theorem not_erdos_106 :
    ¬ ∀ k : ℕ, f (k ^ 2 + 1) = k := by
  sorry

end

end Erdos106
