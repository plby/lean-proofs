/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Elementary diagonal-surface calculations from Proposition 3.4 of
Liam Price (GPT Pro), Large Powers Tile the Integers, 26 June 2026.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.BadShifts

namespace Erdos477

/-- The affine diagonal equation associated with a bad shift. -/
def DiagonalPoint (c : ℤ) (u x y : ℕ) : Prop :=
  (u : ℤ) ^ 6 + (y : ℤ) ^ 6 - (x : ℤ) ^ 6 - c = 0

lemma diagonalPoint_iff (c : ℤ) (u x y : ℕ) :
    DiagonalPoint c u x y ↔ (u : ℤ) ^ 6 - c = (x : ℤ) ^ 6 - (y : ℤ) ^ 6 := by
  unfold DiagonalPoint
  omega

/-- None of the six individual pair-cancellation equations can hold at a
selected point. These are exactly the equations examined on page 3. -/
theorem diagonalPoint_no_cancellation {c : ℤ} {u x y : ℕ}
    (hc : c ∉ PowerValues 6) (hu : 1 ≤ u) (hp : DiagonalPoint c u x y) :
    (u : ℤ) ^ 6 + (y : ℤ) ^ 6 ≠ 0 ∧
    (u : ℤ) ^ 6 - (x : ℤ) ^ 6 ≠ 0 ∧
    (u : ℤ) ^ 6 - c ≠ 0 ∧
    (y : ℤ) ^ 6 - (x : ℤ) ^ 6 ≠ 0 ∧
    (y : ℤ) ^ 6 - c ≠ 0 ∧
    -(x : ℤ) ^ 6 - c ≠ 0 := by
  have hu0 : 0 < (u : ℤ) ^ 6 := by positivity
  have hy0 : 0 ≤ (y : ℤ) ^ 6 := by positivity
  have huc : (u : ℤ) ^ 6 ≠ c := fun h => hc ⟨u, h⟩
  have hyc : (y : ℤ) ^ 6 ≠ c := fun h => hc ⟨y, h⟩
  unfold DiagonalPoint at hp
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega

/-- The height bound including the gap between the two witnesses. -/
theorem diagonalPoint_gap_bound {c : ℤ} {u x y : ℕ}
    (hp : DiagonalPoint c u x y) :
    |(x : ℤ) - y| * ((max x y : ℕ) : ℤ) ^ 5 ≤ (u : ℤ) ^ 6 + |c| := by
  have h := sixth_power_gap_separation x y
  rw [← (diagonalPoint_iff c u x y).mp hp] at h
  refine h.trans ?_
  calc
    |(u : ℤ) ^ 6 - c| ≤ |(u : ℤ) ^ 6| + |c| := abs_sub _ _
    _ = (u : ℤ) ^ 6 + |c| := by rw [abs_of_nonneg (by positivity)]

/-- The positive-sign and negative-sign coordinate changes in page 3. -/
lemma diagonal_coordinate_changes (c u X h w : ℝ) :
    (u ^ 6 - c * w ^ 6 - (X ^ 6 - (X - h) ^ 6) =
      u ^ 6 + (X - h) ^ 6 - X ^ 6 - c * w ^ 6) ∧
    (u ^ 6 - c * w ^ 6 + (X ^ 6 - (X - h) ^ 6) =
      u ^ 6 + X ^ 6 - (X - h) ^ 6 - c * w ^ 6) := by
  constructor <;> ring

/-- The four partial derivatives of a diagonal sextic cannot all vanish
at a nonzero point when all four coefficients are nonzero. -/
lemma diagonal_gradient_nonzero {K : Type*} [Field K] [CharZero K]
    (a z : Fin 4 → K) (ha : ∀ i, a i ≠ 0) (hz : z ≠ 0) :
    ∃ i, 6 * a i * z i ^ 5 ≠ 0 := by
  by_contra h
  push Not at h
  apply hz
  funext i
  have hi := h i
  have h6 : (6 : K) ≠ 0 := by norm_num
  have hpow : z i ^ 5 = 0 := (mul_eq_zero.mp hi).resolve_left (mul_ne_zero h6 (ha i))
  exact (pow_eq_zero_iff (by decide : (5 : ℕ) ≠ 0)).mp hpow

#print axioms diagonalPoint_no_cancellation
-- 'Erdos477.diagonalPoint_no_cancellation' depends on axioms:
-- [propext, Classical.choice, Quot.sound]
#print axioms diagonalPoint_gap_bound
-- 'Erdos477.diagonalPoint_gap_bound' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477
