import ErdosProblems.Erdos633b.Grid
import Mathlib.Tactic.LinearCombination

/-!
# The four regions in the triquadratic construction

These scalar inequalities describe the three enlarged triangles and the
parallelogram in affine coordinates of the outer triangle. Coverage includes
boundaries. Connecting these regions to the rigidly placed supports is a
separate geometric obligation.
-/

namespace Erdos633b.TriquadraticPartition

inductive Piece
  | first | second | third | parallelogram
  deriving DecidableEq

instance : Fintype Piece :=
  ⟨{.first, .second, .third, .parallelogram}, by intro k; cases k <;> simp⟩

def Closed (t : ℝ) : Piece → ℝ → ℝ → Prop
  | .first, x, y => 0 ≤ x ∧ x ≤ t * y ∧ x + t ^ 2 * y ≤ t ^ 2
  | .second, x, y => 0 ≤ y ∧ t * y ≤ x ∧ x + y ≤ t
  | .third, x, y => t ≤ (1 + t) * y ∧ t ^ 2 ≤ x + t ^ 2 * y ∧ x + y ≤ 1
  | .parallelogram, x, y => 0 ≤ y ∧ (1 + t) * y ≤ t ∧ t ≤ x + y ∧ x + y ≤ 1

def Inside (t : ℝ) : Piece → ℝ → ℝ → Prop
  | .first, x, y => 0 < x ∧ x < t * y ∧ x + t ^ 2 * y < t ^ 2
  | .second, x, y => 0 < y ∧ t * y < x ∧ x + y < t
  | .third, x, y => t < (1 + t) * y ∧ t ^ 2 < x + t ^ 2 * y ∧ x + y < 1
  | .parallelogram, x, y => 0 < y ∧ (1 + t) * y < t ∧ t < x + y ∧ x + y < 1

theorem closed_subset (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (k : Piece)
    {x y : ℝ} (h : Closed t k x y) : 0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ 1 := by
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
  have ht2' : 0 < 1 - t ^ 2 := by nlinarith
  cases k with
  | first =>
    obtain ⟨hx, hxy, hq⟩ := h
    have hy : 0 ≤ y := by nlinarith
    refine ⟨hx, hy, ?_⟩
    apply le_of_mul_le_mul_left (a := t ^ 2) _ ht2
    nlinarith [mul_nonneg ht2'.le hx]
  | second =>
    obtain ⟨hy, hxy, hq⟩ := h
    exact ⟨(mul_nonneg ht.le hy).trans hxy, hy, hq.trans ht1.le⟩
  | third =>
    obtain ⟨hy', hq, hsum⟩ := h
    have hy : 0 ≤ y := by nlinarith
    have hy1 : y ≤ 1 := by
      apply le_of_mul_le_mul_left (a := 1 - t ^ 2) _ ht2'
      nlinarith
    exact ⟨by nlinarith [mul_nonneg ht2.le (sub_nonneg.mpr hy1)], hy, hsum⟩
  | parallelogram =>
    obtain ⟨hy, hhigh, hlow, hsum⟩ := h
    have hty : 0 ≤ t * y := mul_nonneg ht.le hy
    exact ⟨by nlinarith, hy, hsum⟩

theorem exists_closed (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y ≤ 1) :
    ∃ k : Piece, Closed t k x y := by
  by_cases hsum : x + y ≤ t
  · by_cases hside : x ≤ t * y
    · refine ⟨.first, hx, hside, ?_⟩
      nlinarith [mul_nonneg (sub_nonneg.mpr ht1.le) (sub_nonneg.mpr hside),
        mul_nonneg ht.le (sub_nonneg.mpr hsum)]
    · exact ⟨.second, hy, (le_of_not_ge hside), hsum⟩
  · by_cases hhigh : (1 + t) * y ≤ t
    · exact ⟨.parallelogram, hy, hhigh, le_of_not_ge hsum, hxy⟩
    · by_cases hquad : t ^ 2 ≤ x + t ^ 2 * y
      · exact ⟨.third, le_of_not_ge hhigh, hquad, hxy⟩
      · refine ⟨.first, hx, ?_, le_of_not_ge hquad⟩
        have hh : 0 ≤ (1 + t) * y - t := sub_nonneg.mpr (le_of_not_ge hhigh)
        nlinarith [mul_nonneg ht.le hh]

theorem inside_unique (t : ℝ) (k l : Piece) {x y : ℝ}
    (hk : Inside t k x y) (hl : Inside t l x y) : k = l := by
  cases k <;> cases l <;> first
    | rfl
    | (simp only [Inside] at hk hl
       exfalso
       nlinarith [hk.1, hk.2.1, hk.2.2, hl.1, hl.2.1, hl.2.2])

theorem first_coordinates (t q : ℝ) (ht : 0 < t) (hq : 0 < q)
    (he : (1 + t) * q = t) (u v : ℝ) :
    Closed t .first (t * q * v) (u + q * v) ↔ 0 ≤ u ∧ 0 ≤ v ∧ u + v ≤ 1 := by
  have h1 : 0 ≤ t * q * v ↔ 0 ≤ v := mul_nonneg_iff_of_pos_left (mul_pos ht hq)
  have h2 : t * q * v ≤ t * (u + q * v) ↔ 0 ≤ u := by
    rw [← sub_nonneg, show t * (u + q * v) - t * q * v = t * u by ring]
    exact mul_nonneg_iff_of_pos_left ht
  have h3 : t * q * v + t ^ 2 * (u + q * v) ≤ t ^ 2 ↔ u + v ≤ 1 := by
    rw [← sub_nonneg]
    have h : t ^ 2 - (t * q * v + t ^ 2 * (u + q * v)) = t ^ 2 * (1 - u - v) := by
      linear_combination -t * v * he
    rw [h, mul_nonneg_iff_of_pos_left (sq_pos_of_pos ht)]
    constructor <;> intro h <;> linarith
  change (0 ≤ t * q * v ∧ _ ∧ _) ↔ _
  rw [h1, h2, h3]
  tauto

theorem second_coordinates (t q : ℝ) (ht : 0 < t) (hq : 0 < q)
    (he : (1 + t) * q = t) (u v : ℝ) :
    Closed t .second (t * u + t * q * v) (q * v) ↔ 0 ≤ u ∧ 0 ≤ v ∧ u + v ≤ 1 := by
  have h1 : 0 ≤ q * v ↔ 0 ≤ v := mul_nonneg_iff_of_pos_left hq
  have h2 : t * (q * v) ≤ t * u + t * q * v ↔ 0 ≤ u := by
    rw [← sub_nonneg, show t * u + t * q * v - t * (q * v) = t * u by ring]
    exact mul_nonneg_iff_of_pos_left ht
  have h3 : t * u + t * q * v + q * v ≤ t ↔ u + v ≤ 1 := by
    rw [← sub_nonneg]
    have h : t - (t * u + t * q * v + q * v) = t * (1 - u - v) := by
      linear_combination -v * he
    rw [h, mul_nonneg_iff_of_pos_left ht]
    constructor <;> intro h <;> linarith
  change (0 ≤ q * v ∧ _ ∧ _) ↔ _
  rw [h1, h2, h3]
  tauto

theorem third_coordinates (t q : ℝ) (ht : 0 < t) (ht1 : t < 1) (hq : 0 < q)
    (he : (1 + t) * q = t) (u v : ℝ) :
    Closed t .third ((1 - q) * u + t * q * v) (1 - (1 - q) * (u + v)) ↔
      0 ≤ u ∧ 0 ≤ v ∧ u + v ≤ 1 := by
  have hq1 : 0 < 1 - q := by nlinarith [mul_pos ht hq]
  have ht2 : 0 < 1 - t ^ 2 := by nlinarith
  have hc := mul_pos hq1 ht2
  have h1 : t ≤ (1 + t) * (1 - (1 - q) * (u + v)) ↔ u + v ≤ 1 := by
    rw [← sub_nonneg]
    have h : (1 + t) * (1 - (1 - q) * (u + v)) - t = 1 - u - v := by
      linear_combination (u + v) * he
    rw [h]
    constructor <;> intro h <;> linarith
  have h2 : t ^ 2 ≤ (1 - q) * u + t * q * v + t ^ 2 * (1 - (1 - q) * (u + v)) ↔
      0 ≤ u := by
    rw [← sub_nonneg]
    have h : (1 - q) * u + t * q * v + t ^ 2 * (1 - (1 - q) * (u + v)) - t ^ 2 =
        ((1 - q) * (1 - t ^ 2)) * u := by
      linear_combination t * v * he
    rw [h, mul_nonneg_iff_of_pos_left hc]
  have h3 : (1 - q) * u + t * q * v + (1 - (1 - q) * (u + v)) ≤ 1 ↔ 0 ≤ v := by
    rw [← sub_nonneg]
    have h : 1 - ((1 - q) * u + t * q * v + (1 - (1 - q) * (u + v))) =
        ((1 - q) * (1 - t ^ 2)) * v := by
      linear_combination -t * v * he
    rw [h, mul_nonneg_iff_of_pos_left hc]
  change (_ ∧ _ ∧ _) ↔ _
  rw [h1, h2, h3]
  tauto

end Erdos633b.TriquadraticPartition
