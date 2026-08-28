import Wikipedia.HopfProblem.OrbitPairDeterminantSignCover
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Scalar orientation weights and endpoint determinant signs

A Boolean orientation choice has weight `1` or `-1`. This translates the
determinant-sign action into strict real inequalities and permits the
source and target orientation factors to be canceled in a comparison of
two actual corner determinants.
-/

noncomputable section

namespace Wikipedia.HopfProblem.OrbitPair.OrientationWeights

open DeterminantSignCover

def weight (b : Bool) : ℝ := if b then -1 else 1

theorem weight_sq (b : Bool) : weight b ^ 2 = 1 := by
  cases b <;> norm_num [weight]

theorem weight_ne_zero (b : Bool) : weight b ≠ 0 := by
  cases b <;> norm_num [weight]

theorem weight_xor (b c : Bool) : weight (Bool.xor b c) = weight b * weight c := by
  cases b <;> cases c <;> norm_num [weight]

theorem action_eq_iff_product_pos (d e : ℝ) (hd : d ≠ 0) (he : e ≠ 0) (b c : Bool) :
    action d b = action e c ↔ 0 < (weight b * d) * (weight c * e) := by
  rcases lt_or_gt_of_ne hd with hd | hd <;> rcases lt_or_gt_of_ne he with he | he <;>
    cases b <;> cases c <;>
    simp [action, weight, mul_pos_iff, hd, he, not_lt_of_ge hd.le, not_lt_of_ge he.le]
  all_goals first
    | exact he.le
    | exact (mul_pos_of_neg_of_neg hd he).le
    | exact mul_neg_of_neg_of_pos hd he
    | exact mul_neg_of_pos_of_neg hd he

theorem action_ne_iff_product_neg (d e : ℝ) (hd : d ≠ 0) (he : e ≠ 0) (b c : Bool) :
    action d b ≠ action e c ↔ (weight b * d) * (weight c * e) < 0 := by
  rcases lt_or_gt_of_ne hd with hd | hd <;> rcases lt_or_gt_of_ne he with he | he <;>
    cases b <;> cases c <;>
    simp [action, weight, mul_neg_iff, hd, he, not_lt_of_ge hd.le, not_lt_of_ge he.le]
  all_goals exact mul_pos_of_neg_of_neg hd he

theorem normalize_comparison {m c k d a b : ℝ} (u v w : Bool)
    (h : m * c * k = d * a * b) :
    m * (weight w * c) * k =
      (weight (Bool.xor (Bool.xor u v) w) * d) * (weight u * a) * (weight v * b) := by
  cases u <;> cases v <;> cases w <;> norm_num [weight] at * <;> nlinarith [h]

theorem negative_product_of_comparison
    {m₀ m₁ c₀ c₁ d₀ d₁ a₀ a₁ b₀ b₁ k : ℝ}
    (h₀ : m₀ * c₀ * k = d₀ * a₀ * b₀)
    (h₁ : m₁ * c₁ * k = d₁ * a₁ * b₁)
    (hk : k ≠ 0) (hc : 0 < c₀ * c₁)
    (ha : 0 < a₀ * a₁) (hb : 0 < b₀ * b₁) (hd : d₀ * d₁ < 0) :
    m₀ * m₁ < 0 := by
  have heq : (m₀ * m₁) * ((c₀ * c₁) * k ^ 2) =
      ((d₀ * d₁) * (a₀ * a₁)) * (b₀ * b₁) := by
    calc
      _ = (m₀ * c₀ * k) * (m₁ * c₁ * k) := by ring
      _ = (d₀ * a₀ * b₀) * (d₁ * a₁ * b₁) := congrArg₂ (· * ·) h₀ h₁
      _ = _ := by ring
  have hright : ((d₀ * d₁) * (a₀ * a₁)) * (b₀ * b₁) < 0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hd ha) hb
  have hscale : 0 < (c₀ * c₁) * k ^ 2 := mul_pos hc (sq_pos_of_ne_zero hk)
  have hmul : (m₀ * m₁) * ((c₀ * c₁) * k ^ 2) < 0 := heq.symm ▸ hright
  by_contra hm
  exact (not_lt_of_ge (mul_nonneg (le_of_not_gt hm) hscale.le)) hmul

end Wikipedia.HopfProblem.OrbitPair.OrientationWeights
