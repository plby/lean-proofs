import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The exact scalar three-region partition for the basic group-2 trapezoid. -/

namespace Erdos633b.TrapezoidPartition

inductive Piece
  | left | right | middle
  deriving DecidableEq

instance : Fintype Piece :=
  ⟨{.left, .right, .middle}, by intro k; cases k <;> simp⟩

def trapezoid (x y s t : ℝ) : Prop := 0 ≤ s ∧ 0 ≤ t ∧ t ≤ y ∧ s + t ≤ x + y

def closed (p q y s t : ℝ) : Piece → Prop
  | .left => 0 ≤ s ∧ t ≤ y ∧ y * s ≤ p * t
  | .right => t ≤ y ∧ s + t ≤ p + q + y ∧ y * (p + q + y) ≤ y * s + (q + y) * t
  | .middle => 0 ≤ t ∧ p * t ≤ y * s ∧ y * s + (q + y) * t ≤ y * (p + q + y)

def inside (p q y s t : ℝ) : Piece → Prop
  | .left => 0 < s ∧ t < y ∧ y * s < p * t
  | .right => t < y ∧ s + t < p + q + y ∧ y * (p + q + y) < y * s + (q + y) * t
  | .middle => 0 < t ∧ p * t < y * s ∧ y * s + (q + y) * t < y * (p + q + y)

theorem closed_subset (p q y : ℝ) (hp : 0 < p) (hq : 0 < q) (hy : 0 < y)
    (s t : ℝ) (k : Piece) (h : closed p q y s t k) : trapezoid (p + q) y s t := by
  cases k
  · obtain ⟨hs, ht, he⟩ := h
    have ht0 : 0 ≤ t := by nlinarith [mul_nonneg hy.le hs]
    have hsp : s ≤ p := by nlinarith [mul_nonneg hp.le (sub_nonneg.mpr ht)]
    exact ⟨hs, ht0, ht, by linarith⟩
  · obtain ⟨ht, hst, he⟩ := h
    have ht0 : 0 ≤ t := by
      nlinarith [mul_nonneg hy.le (sub_nonneg.mpr hst)]
    have hsp : p ≤ s := by
      nlinarith [mul_nonneg (add_pos hq hy).le (sub_nonneg.mpr ht)]
    exact ⟨hp.le.trans hsp, ht0, ht, hst⟩
  · obtain ⟨ht, hl, hr⟩ := h
    have hs : 0 ≤ s := by nlinarith [mul_nonneg hp.le ht]
    have hty : t ≤ y := by
      have hpos : 0 < p + q + y := by linarith
      nlinarith
    have hst : s + t ≤ p + q + y := by nlinarith [mul_nonneg hq.le ht]
    exact ⟨hs, ht, hty, hst⟩

theorem exists_closed (p q y s t : ℝ) (h : trapezoid (p + q) y s t) :
    ∃ k, closed p q y s t k := by
  obtain ⟨hs, ht, hty, hst⟩ := h
  by_cases hl : y * s ≤ p * t
  · exact ⟨.left, hs, hty, hl⟩
  by_cases hr : y * s + (q + y) * t ≤ y * (p + q + y)
  · exact ⟨.middle, ht, le_of_not_ge hl, hr⟩
  · exact ⟨.right, hty, hst, le_of_not_ge hr⟩

theorem inside_left_lt (p q y s t : ℝ) (hp : 0 < p) (hy : 0 < y)
    (h : inside p q y s t .left) : s < p := by
  obtain ⟨hs, ht, he⟩ := h
  nlinarith [mul_pos hp (sub_pos.mpr ht)]

theorem inside_right_gt (p q y s t : ℝ) (hq : 0 < q) (hy : 0 < y)
    (h : inside p q y s t .right) : p < s := by
  obtain ⟨ht, hst, he⟩ := h
  nlinarith [mul_pos (add_pos hq hy) (sub_pos.mpr ht)]

theorem inside_unique (p q y : ℝ) (hp : 0 < p) (hq : 0 < q) (hy : 0 < y)
    (s t : ℝ) (k l : Piece) (hk : inside p q y s t k) (hl : inside p q y s t l) : k = l := by
  cases k <;> cases l
  · rfl
  · exact (lt_asymm (inside_left_lt p q y s t hp hy hk)
      (inside_right_gt p q y s t hq hy hl)).elim
  · exact (lt_asymm hk.2.2 hl.2.1).elim
  · exact (lt_asymm (inside_right_gt p q y s t hq hy hk)
      (inside_left_lt p q y s t hp hy hl)).elim
  · rfl
  · exact (lt_asymm hk.2.2 hl.2.2).elim
  · exact (lt_asymm hk.2.1 hl.2.2).elim
  · exact (lt_asymm hk.2.2 hl.2.2).elim
  · rfl

theorem left_coords_iff (p q y : ℝ) (hp : 0 < p) (hy : 0 < y) (u v : ℝ) :
    closed p q y (p * v) (y * (1 - u)) .left ↔ 0 ≤ u ∧ 0 ≤ v ∧ u + v ≤ 1 := by
  have hpy := mul_pos hp hy
  constructor
  · rintro ⟨hv, hu, hs⟩
    have hsum : (p * y) * (u + v) ≤ (p * y) * 1 := by nlinarith only [hs]
    exact ⟨by nlinarith, by nlinarith, le_of_mul_le_mul_left hsum hpy⟩
  · rintro ⟨hu, hv, hs⟩
    have hsum := mul_le_mul_of_nonneg_left hs hpy.le
    exact ⟨mul_nonneg hp.le hv, by nlinarith [mul_nonneg hy.le hu],
      by nlinarith only [hsum]⟩

theorem right_coords_iff (p q y : ℝ) (hq : 0 < q) (hy : 0 < y) (u v : ℝ) :
    closed p q y (p + q - q * u + y * v) (y * (1 - v)) .right ↔
      0 ≤ u ∧ 0 ≤ v ∧ u + v ≤ 1 := by
  have hqy := mul_pos hq hy
  constructor
  · rintro ⟨hv, hu, hs⟩
    have hsum : (q * y) * (u + v) ≤ (q * y) * 1 := by nlinarith only [hs]
    exact ⟨by nlinarith, by nlinarith, le_of_mul_le_mul_left hsum hqy⟩
  · rintro ⟨hu, hv, hs⟩
    have hsum := mul_le_mul_of_nonneg_left hs hqy.le
    exact ⟨by nlinarith [mul_nonneg hy.le hv], by nlinarith [mul_nonneg hq.le hu],
      by nlinarith only [hsum]⟩

theorem middle_coords_iff (p q y : ℝ) (hp : 0 < p) (hq : 0 < q) (hy : 0 < y)
    (u v : ℝ) :
    closed p q y (p * (1 - u - v) + (p + q + y) * u) (y * (1 - u - v)) .middle ↔
      0 ≤ u ∧ 0 ≤ v ∧ u + v ≤ 1 := by
  have hL : 0 < p + q + y := by linarith
  have hLy := mul_pos hL hy
  constructor
  · rintro ⟨hs, hu, hv⟩
    have hu' : 0 ≤ (p + q + y) * y * u := by nlinarith only [hu]
    have hv' : 0 ≤ (p + q + y) * y * v := by nlinarith only [hv]
    exact ⟨by nlinarith only [hu', hLy], by nlinarith only [hv', hLy], by nlinarith⟩
  · rintro ⟨hu, hv, hs⟩
    have hu' := mul_nonneg hLy.le hu
    have hv' := mul_nonneg hLy.le hv
    exact ⟨mul_nonneg hy.le (by linarith), by nlinarith only [hu'], by nlinarith only [hv']⟩

end Erdos633b.TrapezoidPartition
