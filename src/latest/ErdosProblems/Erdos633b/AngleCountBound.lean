import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! The small corner-column bound from the actual angle inventory.
The local coefficient equations, not a shape classification, are the hypotheses. -/

namespace Erdos633b

theorem exists_count_deficit {ι : Type*} [Fintype ι] (p r : ι → ℕ) (P : ℕ)
    (hP : 0 < P) (h : P + ∑ i, p i = ∑ i, r i) : ∃ i, p i < r i := by
  by_contra hn
  have hle : ∑ i, r i ≤ ∑ i, p i := by
    apply Finset.sum_le_sum
    intro i _
    exact le_of_not_gt (fun hi => hn ⟨i, hi⟩)
  omega

theorem corner_coefficients_le_three (P Q p q r k : ℕ) (hkr : k ≤ 2)
    (hpr : p < r) (hp : p + P * r = P * k + r) (hq : q + Q * r = Q * k + r) :
    P ≤ 3 ∧ Q ≤ 3 := by
  have hlt : k < r := by
    by_contra hn
    have hle : r ≤ k := by omega
    have hm := Nat.mul_le_mul_left P hle
    omega
  let l := r - k
  have hl : 0 < l := Nat.sub_pos_of_lt hlt
  have hlk : l + k = r := Nat.sub_add_cancel hlt.le
  have hp' : p + P * l = k + l := by nlinarith [hp]
  have hq' : q + Q * l = k + l := by nlinarith [hq]
  constructor
  · by_contra hn
    have hP : 4 ≤ P := by omega
    have hm := Nat.mul_le_mul_right l hP
    nlinarith
  · by_contra hn
    have hQ : 4 ≤ Q := by omega
    have hm := Nat.mul_le_mul_right l hQ
    nlinarith

theorem corner_bounds_of_inventory {ι : Type*} [Fintype ι]
    (p q r k : ι → ℕ) (P Q : ℕ) (hP : 0 < P)
    (hinventory : P + ∑ i, p i = ∑ i, r i)
    (hk : ∀ i, k i ≤ 2)
    (hp : ∀ i, p i + P * r i = P * k i + r i)
    (hq : ∀ i, q i + Q * r i = Q * k i + r i) : P ≤ 3 ∧ Q ≤ 3 := by
  obtain ⟨i, hi⟩ := exists_count_deficit p r P hP hinventory
  exact corner_coefficients_le_three P Q (p i) (q i) (r i) (k i) (hk i) hi (hp i) (hq i)

end Erdos633b
