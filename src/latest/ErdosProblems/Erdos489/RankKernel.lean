import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

open Filter
open scoped Topology BigOperators NNReal

noncomputable def rankDecay (n : ℕ) : ℝ :=
  1 / (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1))

lemma summable_rankDecay : Summable rankDecay := by
  have h := (Real.summable_one_div_nat_add_rpow 1 (3 / 2 : ℝ)).2 (by norm_num)
  convert h using 1
  funext n
  rw [rankDecay, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  congr 2
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add (by positivity) 1 (1 / 2), Real.rpow_one,
    ← Real.sqrt_eq_rpow]

noncomputable def rankPairKernel (a : ℕ → ℕ) (z : ℕ × ℕ) : ℝ :=
  let x : ℝ := z.1 + 1
  let y : ℝ := z.2 + 1
  min x y / ((a z.1 : ℝ) * (a z.2 : ℝ))

/-- A global quadratic lower bound on an enumeration makes its rank-weighted
pair kernel summable. -/
theorem summable_rankPairKernel_of_sq_le (a : ℕ → ℕ)
    (ha : ∀ n, (n + 1) ^ 2 ≤ a n) :
    Summable (rankPairKernel a) := by
  have hprod : Summable (fun z : ℕ × ℕ => rankDecay z.1 * rankDecay z.2) := by
    exact summable_mul_of_summable_norm summable_rankDecay.norm summable_rankDecay.norm
  apply Summable.of_norm_bounded hprod
  intro z
  dsimp [rankPairKernel, rankDecay]
  rw [abs_of_nonneg (by positivity)]
  let x : ℝ := (z.1 : ℝ) + 1
  let y : ℝ := (z.2 : ℝ) + 1
  let A : ℝ := a z.1
  let B : ℝ := a z.2
  have hx : 0 < x := by dsimp [x]; positivity
  have hy : 0 < y := by dsimp [y]; positivity
  have hA : 0 < A := by
    dsimp [A]
    exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < (z.1 + 1) ^ 2) (ha z.1))
  have hB : 0 < B := by
    dsimp [B]
    exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < (z.2 + 1) ^ 2) (ha z.2))
  have hAi : x ^ 2 ≤ A := by dsimp [x, A]; exact_mod_cast ha z.1
  have hBj : y ^ 2 ≤ B := by dsimp [y, B]; exact_mod_cast ha z.2
  have hmin : min x y ≤ Real.sqrt (x * y) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    rw [pow_two]
    exact mul_le_mul (min_le_left _ _) (min_le_right _ _) (by positivity) (by positivity)
  rw [Real.sqrt_mul hx.le] at hmin
  have hsx : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx.le
  have hsy : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy.le
  have hmxy : min x y * (Real.sqrt x * Real.sqrt y) ≤ x * y := by
    have hsnon : 0 ≤ Real.sqrt x * Real.sqrt y :=
      mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)
    have hmul := mul_le_mul_of_nonneg_right hmin hsnon
    calc
      min x y * (Real.sqrt x * Real.sqrt y) ≤
          (Real.sqrt x * Real.sqrt y) * (Real.sqrt x * Real.sqrt y) := by simpa [mul_comm] using hmul
      _ = (Real.sqrt x) ^ 2 * (Real.sqrt y) ^ 2 := by ring
      _ = x * y := by rw [hsx, hsy]
  let den : ℝ := (x * Real.sqrt x) * (y * Real.sqrt y)
  have hdpos : 0 < den := by dsimp [den]; positivity
  have hcross : min x y * den ≤ A * B := by
    calc
      min x y * den = (min x y * (Real.sqrt x * Real.sqrt y)) * (x * y) := by
        dsimp [den]
        ring
      _ ≤ (x * y) * (x * y) :=
        mul_le_mul_of_nonneg_right hmxy (mul_nonneg hx.le hy.le)
      _ = (x ^ 2) * (y ^ 2) := by ring
      _ ≤ A * B := mul_le_mul hAi hBj (sq_nonneg _) hA.le
  have hquot : min x y / (A * B) ≤ (1 / (x * Real.sqrt x)) * (1 / (y * Real.sqrt y)) := by
    apply (div_le_iff₀ (mul_pos hA hB)).2
    calc
      min x y ≤ (A * B) / den := (le_div_iff₀ hdpos).2 hcross
      _ = (1 / (x * Real.sqrt x)) * (1 / (y * Real.sqrt y)) * (A * B) := by
        field_simp
        <;> ring
  simpa [x, y, A, B] using hquot

end Erdos489
