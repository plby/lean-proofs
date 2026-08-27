import Mathlib.Tactic

/-! # Odd transformations preserve cancellation of at most two terms -/

open Finset
open scoped BigOperators

namespace Arxiv2411_18291

theorem sum_odd_eq_zero_of_card_le_two {I : Type*}
    (s : Finset I) (hs : s.card ≤ 2) (x : I → ℤ) (f : ℤ → ℤ)
    (hf0 : f 0 = 0) (hfneg : ∀ z, f (-z) = -f z) (hx : ∑ i ∈ s, x i = 0) :
    ∑ i ∈ s, f (x i) = 0 := by
  classical
  have hcases : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 := by omega
  rcases hcases with hzero | hone | htwo
  · rw [card_eq_zero.mp hzero]
    simp
  · obtain ⟨i, rfl⟩ := card_eq_one.mp hone
    simp only [sum_singleton] at hx ⊢
    rw [hx, hf0]
  · obtain ⟨i, j, hij, rfl⟩ := card_eq_two.mp htwo
    simp only [sum_pair hij] at hx ⊢
    rw [show x j = -x i by omega, hfneg, add_neg_cancel]

/-- The signed indicator of one absolute-value level of an integer. -/
def intMagnitudeLevel (t : ℕ) (z : ℤ) : ℤ := if z.natAbs = t then z.sign else 0

@[simp] theorem intMagnitudeLevel_zero (t : ℕ) : intMagnitudeLevel t 0 = 0 := by
  simp [intMagnitudeLevel]

@[simp] theorem intMagnitudeLevel_neg (t : ℕ) (z : ℤ) :
    intMagnitudeLevel t (-z) = -intMagnitudeLevel t z := by
  simp only [intMagnitudeLevel, Int.natAbs_neg, Int.sign_neg]
  split_ifs <;> simp

theorem abs_intMagnitudeLevel_le (t : ℕ) (z : ℤ) : |intMagnitudeLevel t z| ≤ 1 := by
  by_cases hz : z = 0
  · simp [hz]
  · unfold intMagnitudeLevel
    split_ifs
    · exact (Int.abs_sign_of_ne_zero hz).le
    · norm_num

theorem sum_intMagnitudeLevel (s : Finset ℕ) (z : ℤ) (hz : z.natAbs ∈ s) :
    (∑ t ∈ s, (t : ℤ) * intMagnitudeLevel t z) = z := by
  rw [sum_eq_single z.natAbs]
  · rw [intMagnitudeLevel, if_pos rfl, mul_comm, Int.sign_mul_natAbs]
  · intro t _ ht
    rw [intMagnitudeLevel, if_neg ht.symm, mul_zero]
  · intro hnot
    exact (hnot hz).elim

end Arxiv2411_18291
