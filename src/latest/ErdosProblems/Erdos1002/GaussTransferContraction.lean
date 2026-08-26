import ErdosProblems.Erdos1002.GaussDigitQuasiBernoulli
import ErdosProblems.Erdos1002.GaussCylinderContraction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A strict contraction estimate for the Gauss transfer kernel

This file supplies an elementary quantitative step toward the decaying
`GaussDigitPsiMixing` input.  The normalized inverse-branch kernel is already
defined in `GaussDigitQuasiBernoulli`.  Here we prove that each branch weight
has an explicit Lipschitz constant.  The constants are chosen so that, after
combining the movement of the inverse branches with the movement of their
weights, the resulting majorant has total mass `527 / 540 < 1`.

No mixing or spectral-gap theorem is assumed in this file.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology ENNReal NNReal

namespace Erdos1002

noncomputable section

/-- Exact derivative of the normalized one-branch Gauss kernel. -/
theorem hasDerivAt_gaussBranchRatio
    {q : ℕ} {y : ℝ} (hqy : (q : ℝ) + y ≠ 0)
    (hqy1 : (q : ℝ) + y + 1 ≠ 0) :
    HasDerivAt (gaussBranchRatio q)
      (((q : ℝ) ^ 2 - (q : ℝ) - (y + 1) ^ 2) /
        (((q : ℝ) + y) ^ 2 * ((q : ℝ) + y + 1) ^ 2)) y := by
  unfold gaussBranchRatio
  have h := ((hasDerivAt_const y (1 : ℝ)).add (hasDerivAt_id y)).div
      (((hasDerivAt_const y (q : ℝ)).add (hasDerivAt_id y)).mul
        (((hasDerivAt_const y (q : ℝ)).add (hasDerivAt_id y)).add_const 1))
      (mul_ne_zero hqy hqy1)
  convert! h using 1
  simp only [Pi.add_apply, Pi.mul_apply, id_eq]
  field_simp [hqy, hqy1]
  ring

/-- The branch with digit one has kernel Lipschitz constant `1/4`. -/
theorem abs_gaussBranchRatio_one_sub_le
    {y z : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    |gaussBranchRatio 1 y - gaussBranchRatio 1 z| ≤
      (1 / 4 : ℝ) * |y - z| := by
  have hderiv : ∀ x ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (gaussBranchRatio 1) x := by
    intro x hx
    exact (hasDerivAt_gaussBranchRatio
      (by norm_num; linarith [hx.1])
      (by norm_num; linarith [hx.1])).differentiableAt
  have hbound : ∀ x ∈ Icc (0 : ℝ) 1,
      ‖deriv (gaussBranchRatio 1) x‖₊ ≤ (1 / 4 : ℝ≥0) := by
    intro x hx
    rw [(hasDerivAt_gaussBranchRatio
      (q := 1) (y := x) (by norm_num; linarith [hx.1])
      (by norm_num; linarith [hx.1])).deriv]
    apply NNReal.coe_le_coe.mp
    simp only [coe_nnnorm, Real.norm_eq_abs, NNReal.coe_div, NNReal.coe_one,
      NNReal.coe_ofNat]
    norm_num only [Nat.cast_one, one_pow]
    have hx2 : 2 ≤ 2 + x := by linarith [hx.1]
    have hx2pos : 0 < 2 + x := by linarith [hx.1]
    have h1xpos : 0 < 1 + x := by linarith [hx.1]
    have hdenpos : 0 < (1 + x) ^ 2 * (1 + x + 1) ^ 2 := by positivity
    rw [abs_div, abs_sub_comm, sub_zero, abs_of_nonneg (sq_nonneg _),
      abs_of_pos hdenpos, div_le_iff₀ hdenpos]
    have hsq : (4 : ℝ) ≤ (2 + x) ^ 2 := by
      nlinarith [mul_nonneg hx.1 (by linarith [hx.1] : 0 ≤ x + 4)]
    have hmul := mul_le_mul_of_nonneg_left hsq (sq_nonneg (1 + x))
    nlinarith
  have hlip := Convex.lipschitzOnWith_of_nnnorm_deriv_le
    hderiv hbound (convex_Icc (0 : ℝ) 1)
  simpa only [Real.norm_eq_abs, NNReal.coe_div, NNReal.coe_one,
    NNReal.coe_ofNat] using! hlip.norm_sub_le hy hz

/-- The branch with digit two has kernel Lipschitz constant `1/18`. -/
theorem abs_gaussBranchRatio_two_sub_le
    {y z : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    |gaussBranchRatio 2 y - gaussBranchRatio 2 z| ≤
      (1 / 18 : ℝ) * |y - z| := by
  have hderiv : ∀ x ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (gaussBranchRatio 2) x := by
    intro x hx
    exact (hasDerivAt_gaussBranchRatio
      (by norm_num; linarith [hx.1])
      (by norm_num; linarith [hx.1])).differentiableAt
  have hbound : ∀ x ∈ Icc (0 : ℝ) 1,
      ‖deriv (gaussBranchRatio 2) x‖₊ ≤ (1 / 18 : ℝ≥0) := by
    intro x hx
    rw [(hasDerivAt_gaussBranchRatio
      (q := 2) (y := x) (by norm_num; linarith [hx.1])
      (by norm_num; linarith [hx.1])).deriv]
    apply NNReal.coe_le_coe.mp
    simp only [coe_nnnorm, Real.norm_eq_abs, NNReal.coe_div, NNReal.coe_one,
      NNReal.coe_ofNat]
    norm_num only [Nat.cast_ofNat]
    have hsquare : (x + 1) ^ 2 ≤ 4 := by
      nlinarith [mul_nonneg (by linarith [hx.2] : 0 ≤ 1 - x)
        (by linarith [hx.1] : 0 ≤ 3 + x)]
    have hnum : |(2 : ℝ) - (x + 1) ^ 2| ≤ 2 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (x + 1)]
    have hden1 : 2 ≤ 2 + x := by linarith [hx.1]
    have hden2 : 3 ≤ 2 + x + 1 := by linarith [hx.1]
    have hdenpos : 0 < (2 + x) ^ 2 * (2 + x + 1) ^ 2 := by positivity
    rw [abs_div, abs_of_pos hdenpos, div_le_iff₀ hdenpos]
    calc
      |(2 : ℝ) - (x + 1) ^ 2| ≤ 2 := hnum
      _ ≤ (1 / 18 : ℝ) *
          ((2 + x) ^ 2 * (2 + x + 1) ^ 2) := by
        have hsq1 : (4 : ℝ) ≤ (2 + x) ^ 2 := by nlinarith
        have hsq2 : (9 : ℝ) ≤ (2 + x + 1) ^ 2 := by nlinarith
        nlinarith [mul_le_mul hsq1 hsq2 (by norm_num : (0 : ℝ) ≤ 9)
          (sq_nonneg (2 + x))]
  have hlip := Convex.lipschitzOnWith_of_nnnorm_deriv_le
    hderiv hbound (convex_Icc (0 : ℝ) 1)
  simpa only [Real.norm_eq_abs, NNReal.coe_div, NNReal.coe_one,
    NNReal.coe_ofNat] using! hlip.norm_sub_le hy hz

/-- For every digit at least three, the sharper summable derivative envelope
`(q-1)/(q(q+1)^2)` is valid. -/
theorem abs_gaussBranchRatio_sub_le_of_three_le
    {q : ℕ} (hq : 3 ≤ q) {y z : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    |gaussBranchRatio q y - gaussBranchRatio q z| ≤
      (((q : ℝ) - 1) / ((q : ℝ) * ((q : ℝ) + 1) ^ 2)) *
        |y - z| := by
  let C : ℝ := ((q : ℝ) - 1) / ((q : ℝ) * ((q : ℝ) + 1) ^ 2)
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hC : 0 ≤ C := by
    dsimp [C]
    have hq0 : (0 : ℝ) < q := by positivity
    have hq1 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
    exact div_nonneg (by linarith) (mul_nonneg hq0.le (sq_nonneg _))
  have hderiv : ∀ x ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (gaussBranchRatio q) x := by
    intro x hx
    exact (hasDerivAt_gaussBranchRatio
      (by linarith [hx.1]) (by linarith [hx.1])).differentiableAt
  have hbound : ∀ x ∈ Icc (0 : ℝ) 1,
      ‖deriv (gaussBranchRatio q) x‖₊ ≤ C.toNNReal := by
    intro x hx
    rw [(hasDerivAt_gaussBranchRatio
      (q := q) (y := x) (by linarith [hx.1])
      (by linarith [hx.1])).deriv]
    apply NNReal.coe_le_coe.mp
    rw [coe_nnnorm, Real.norm_eq_abs, Real.coe_toNNReal C hC]
    have hx0 : 0 ≤ x := hx.1
    have hx1 : x ≤ 1 := hx.2
    have hsquare : (x + 1) ^ 2 ≤ 4 := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - x)
        (by linarith : 0 ≤ 3 + x)]
    have hnum0 : 0 ≤ (q : ℝ) ^ 2 - q - (x + 1) ^ 2 := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ (q : ℝ) - 3)
        (by linarith : 0 ≤ (q : ℝ) + 2)]
    have hnum : (q : ℝ) ^ 2 - q - (x + 1) ^ 2 ≤
        (q : ℝ) ^ 2 - q := by nlinarith [sq_nonneg (x + 1)]
    have hden1 : (q : ℝ) ≤ q + x := by linarith [hx.1]
    have hden2 : (q : ℝ) + 1 ≤ q + x + 1 := by linarith [hx.1]
    have hqx : 0 < (q : ℝ) + x := by linarith
    have hqx1 : 0 < (q : ℝ) + x + 1 := by linarith
    have hdenpos : 0 < (q + x) ^ 2 * (q + x + 1) ^ 2 :=
      mul_pos (sq_pos_of_pos hqx) (sq_pos_of_pos hqx1)
    rw [abs_div, abs_of_nonneg hnum0, abs_of_pos hdenpos,
      div_le_iff₀ hdenpos]
    have hsq1 : (q : ℝ) ^ 2 ≤ (q + x) ^ 2 := by nlinarith
    have hsq2 : ((q : ℝ) + 1) ^ 2 ≤ (q + x + 1) ^ 2 := by nlinarith
    have hprod : (q : ℝ) ^ 2 * ((q : ℝ) + 1) ^ 2 ≤
        (q + x) ^ 2 * (q + x + 1) ^ 2 :=
      mul_le_mul hsq1 hsq2 (sq_nonneg _) (sq_nonneg _)
    dsimp [C]
    have hbase : 0 < (q : ℝ) * ((q : ℝ) + 1) ^ 2 := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hbase]
    calc
      ((q : ℝ) ^ 2 - q - (x + 1) ^ 2) *
          ((q : ℝ) * ((q : ℝ) + 1) ^ 2) ≤
          ((q : ℝ) ^ 2 - q) *
            ((q : ℝ) * ((q : ℝ) + 1) ^ 2) := by
        gcongr
      _ = ((q : ℝ) - 1) *
          ((q : ℝ) ^ 2 * ((q : ℝ) + 1) ^ 2) := by ring
      _ ≤ ((q : ℝ) - 1) *
          ((q + x) ^ 2 * (q + x + 1) ^ 2) := by
        exact mul_le_mul_of_nonneg_left hprod (by linarith)
  have hlip := Convex.lipschitzOnWith_of_nnnorm_deriv_le
    hderiv hbound (convex_Icc (0 : ℝ) 1)
  simpa only [Real.norm_eq_abs, Real.coe_toNNReal C hC, C] using!
    hlip.norm_sub_le hy hz

/-! ## The summable strict-contraction envelope -/

/-- Majorant for the contribution of digit `n+1` to the Lipschitz norm of
the transfer operator.  The first two branches are separated because their
sharp elementary constants are what makes the total strictly less than one. -/
def gaussTransferLipschitzMajorant (n : ℕ) : ℝ :=
  if n = 0 then 3 / 4
  else if n = 1 then 7 / 90
  else
    (1 / ((n + 1 : ℕ) : ℝ) ^ 3 -
      1 / ((n + 2 : ℕ) : ℝ) ^ 3) +
    (1 / ((n + 1 : ℕ) : ℝ) ^ 2 -
      1 / ((n + 2 : ℕ) : ℝ) ^ 2)

theorem gaussTransferLipschitzMajorant_zero :
    gaussTransferLipschitzMajorant 0 = 3 / 4 := by
  simp [gaussTransferLipschitzMajorant]

theorem gaussTransferLipschitzMajorant_one :
    gaussTransferLipschitzMajorant 1 = 7 / 90 := by
  simp [gaussTransferLipschitzMajorant]

theorem gaussTransferLipschitzMajorant_add_two (n : ℕ) :
    gaussTransferLipschitzMajorant (n + 2) =
      (1 / ((n + 3 : ℕ) : ℝ) ^ 3 -
        1 / ((n + 4 : ℕ) : ℝ) ^ 3) +
      (1 / ((n + 3 : ℕ) : ℝ) ^ 2 -
        1 / ((n + 4 : ℕ) : ℝ) ^ 2) := by
  simp only [gaussTransferLipschitzMajorant, if_neg (by omega : n + 2 ≠ 0),
    if_neg (by omega : n + 2 ≠ 1)]

/-- Exact partial-sum formula for the majorant after the two exceptional
digits. -/
theorem sum_range_gaussTransferLipschitzMajorant_add_two (R : ℕ) :
    (∑ n ∈ Finset.range (R + 2), gaussTransferLipschitzMajorant n) =
      3 / 4 + 7 / 90 +
        (1 / (3 : ℝ) ^ 3 - 1 / ((R + 3 : ℕ) : ℝ) ^ 3) +
        (1 / (3 : ℝ) ^ 2 - 1 / ((R + 3 : ℕ) : ℝ) ^ 2) := by
  rw [show R + 2 = 2 + R by omega]
  rw [Finset.sum_range_add]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    gaussTransferLipschitzMajorant_zero,
    gaussTransferLipschitzMajorant_one]
  simp_rw [show ∀ n : ℕ, gaussTransferLipschitzMajorant (2 + n) =
      (1 / ((n + 3 : ℕ) : ℝ) ^ 3 -
        1 / ((n + 4 : ℕ) : ℝ) ^ 3) +
      (1 / ((n + 3 : ℕ) : ℝ) ^ 2 -
        1 / ((n + 4 : ℕ) : ℝ) ^ 2) by
    intro n
    rw [add_comm]
    exact gaussTransferLipschitzMajorant_add_two n]
  rw [Finset.sum_add_distrib]
  have h3 := Finset.sum_range_sub'
    (fun n : ℕ => 1 / ((n + 3 : ℕ) : ℝ) ^ 3) R
  have h2 := Finset.sum_range_sub'
    (fun n : ℕ => 1 / ((n + 3 : ℕ) : ℝ) ^ 2) R
  simp only [Nat.zero_add] at h3 h2
  rw [h3, h2]
  norm_num [Nat.cast_add]
  ring

/-- Every finite partial sum of the envelope is at most `527/540`. -/
theorem sum_range_gaussTransferLipschitzMajorant_le (R : ℕ) :
    (∑ n ∈ Finset.range R, gaussTransferLipschitzMajorant n) ≤
      (527 / 540 : ℝ) := by
  cases R with
  | zero => norm_num
  | succ R =>
      cases R with
      | zero => norm_num [gaussTransferLipschitzMajorant]
      | succ R =>
          rw [show R + 1 + 1 = R + 2 by omega,
            sum_range_gaussTransferLipschitzMajorant_add_two]
          have hpow3 : 0 ≤ 1 / (((R : ℝ) + 3) ^ 3) := by positivity
          have hpow2 : 0 ≤ 1 / (((R : ℝ) + 3) ^ 2) := by positivity
          norm_num [Nat.cast_add]
          have hc : (149 / 180 : ℝ) + 1 / 27 + 1 / 9 = 527 / 540 := by
            norm_num
          rw [← hc]
          simp only [one_div] at hpow3 hpow2
          linarith

theorem gaussTransferLipschitzMajorant_nonneg (n : ℕ) :
    0 ≤ gaussTransferLipschitzMajorant n := by
  rcases n with (_ | _ | n)
  · norm_num [gaussTransferLipschitzMajorant]
  · norm_num [gaussTransferLipschitzMajorant]
  · rw [gaussTransferLipschitzMajorant_add_two]
    have h3 : 1 / ((n + 4 : ℕ) : ℝ) ^ 3 ≤
        1 / ((n + 3 : ℕ) : ℝ) ^ 3 := by
      apply one_div_le_one_div_of_le (by positivity)
      gcongr
      omega
    have h2 : 1 / ((n + 4 : ℕ) : ℝ) ^ 2 ≤
        1 / ((n + 3 : ℕ) : ℝ) ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity)
      gcongr
      omega
    linarith

/-- The contraction coefficient is genuinely strict. -/
theorem gaussTransferContractionCoefficient_lt_one :
    (527 / 540 : ℝ) < 1 := by norm_num

/-! ## Pointwise branch contributions -/

theorem gaussBranchRatio_one_le_half
    {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    gaussBranchRatio 1 y ≤ (1 / 2 : ℝ) := by
  have h1 : 0 < 1 + y := by linarith [hy.1]
  have h2 : 0 < 1 + y + 1 := by linarith [hy.1]
  unfold gaussBranchRatio
  norm_num only [Nat.cast_one]
  have heq : (1 + y) / ((1 + y) * (1 + y + 1)) =
      1 / (2 + y) := by
    field_simp [ne_of_gt h1, show 2 + y ≠ 0 by linarith [hy.1]]
    ring
  rw [heq]
  exact one_div_le_one_div_of_le (by norm_num) (by linarith [hy.1])

theorem gaussBranchRatio_two_le_one_fifth
    {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    gaussBranchRatio 2 y ≤ (1 / 5 : ℝ) := by
  have h2 : 0 < 2 + y := by linarith [hy.1]
  have h3 : 0 < 2 + y + 1 := by linarith [hy.1]
  unfold gaussBranchRatio
  norm_num only [Nat.cast_ofNat]
  rw [div_le_iff₀ (mul_pos h2 h3)]
  nlinarith [sq_nonneg y]

theorem gaussBranchRatio_le_endpoint_of_three_le
    {q : ℕ} (hq : 3 ≤ q) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    gaussBranchRatio q y ≤
      2 / (((q : ℝ) + 1) * ((q : ℝ) + 2)) := by
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hqy : 0 < (q : ℝ) + y := by linarith [hy.1]
  have hqy1 : 0 < (q : ℝ) + y + 1 := by linarith [hy.1]
  have hq1 : 0 < (q : ℝ) + 1 := by linarith
  have hq2 : 0 < (q : ℝ) + 2 := by linarith
  unfold gaussBranchRatio
  rw [div_le_div_iff₀ (mul_pos hqy hqy1) (mul_pos hq1 hq2)]
  have hyupper : 0 ≤ 1 - y := sub_nonneg.mpr hy.2
  have hqthree : 0 ≤ (q : ℝ) - 3 := by linarith
  nlinarith [mul_nonneg hy.1 hyupper, mul_nonneg hqthree hyupper]

/-- Movement of the inverse point for digit one contributes at most `1/2`. -/
theorem gaussBranchMotionCoefficient_one_le
    {y z : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    gaussBranchRatio 1 y /
        (((1 : ℝ) + y) * ((1 : ℝ) + z)) ≤ 1 / 2 := by
  have hden : 1 ≤ ((1 : ℝ) + y) * ((1 : ℝ) + z) := by
    nlinarith [hy.1, hz.1, mul_nonneg hy.1 hz.1]
  exact (div_le_self (gaussBranchRatio_pos (by omega) hy).le hden).trans
    (gaussBranchRatio_one_le_half hy)

/-- Movement of the inverse point for digit two contributes at most `1/20`. -/
theorem gaussBranchMotionCoefficient_two_le
    {y z : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    gaussBranchRatio 2 y /
        (((2 : ℝ) + y) * ((2 : ℝ) + z)) ≤ 1 / 20 := by
  have hden : 4 ≤ ((2 : ℝ) + y) * ((2 : ℝ) + z) := by
    nlinarith [hy.1, hz.1, mul_nonneg hy.1 hz.1]
  calc
    gaussBranchRatio 2 y / (((2 : ℝ) + y) * ((2 : ℝ) + z)) ≤
        gaussBranchRatio 2 y / 4 := by
      exact div_le_div_of_nonneg_left
        (gaussBranchRatio_pos (by omega) hy).le (by norm_num) hden
    _ ≤ (1 / 5 : ℝ) / 4 := by
      gcongr
      exact gaussBranchRatio_two_le_one_fifth hy
    _ = 1 / 20 := by norm_num

/-- For digits at least three, the movement term is bounded by a telescoping
reciprocal-cube difference. -/
theorem gaussBranchMotionCoefficient_le_cube_sub
    {q : ℕ} (hq : 3 ≤ q) {y z : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    gaussBranchRatio q y /
        (((q : ℝ) + y) * ((q : ℝ) + z)) ≤
      1 / (q : ℝ) ^ 3 - 1 / ((q : ℝ) + 1) ^ 3 := by
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hyz : 0 ≤ y + z := add_nonneg hy.1 hz.1
  have hden : (q : ℝ) ^ 2 ≤
      ((q : ℝ) + y) * ((q : ℝ) + z) := by
    nlinarith [hy.1, hz.1, mul_nonneg hy.1 hz.1,
      mul_nonneg (by linarith : 0 ≤ (q : ℝ)) hyz]
  have hratio := gaussBranchRatio_le_endpoint_of_three_le hq hy
  have hleft : gaussBranchRatio q y /
      (((q : ℝ) + y) * ((q : ℝ) + z)) ≤
      (2 / (((q : ℝ) + 1) * ((q : ℝ) + 2))) / (q : ℝ) ^ 2 := by
    calc
      gaussBranchRatio q y /
          (((q : ℝ) + y) * ((q : ℝ) + z)) ≤
          gaussBranchRatio q y / (q : ℝ) ^ 2 := by
        exact div_le_div_of_nonneg_left
          (gaussBranchRatio_pos (by omega) hy).le (by positivity) hden
      _ ≤ (2 / (((q : ℝ) + 1) * ((q : ℝ) + 2))) /
          (q : ℝ) ^ 2 := by gcongr
  refine hleft.trans ?_
  have hq0 : 0 < (q : ℝ) := by positivity
  have hq1 : 0 < (q : ℝ) + 1 := by positivity
  have hq2 : 0 < (q : ℝ) + 2 := by positivity
  field_simp
  nlinarith [sq_nonneg ((q : ℝ) - 1)]

/-- For digits at least three, the movement of the branch weight, after the
centered value bound, is dominated by a telescoping reciprocal-square
difference. -/
theorem gaussBranchWeightCoefficient_le_square_sub
    {q : ℕ} (hq : 3 ≤ q) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    (((q : ℝ) - 1) / ((q : ℝ) * ((q : ℝ) + 1) ^ 2)) /
        ((q : ℝ) + z) ≤
      1 / (q : ℝ) ^ 2 - 1 / ((q : ℝ) + 1) ^ 2 := by
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hqz : (q : ℝ) ≤ q + z := by linarith [hz.1]
  have hnonneg : 0 ≤
      ((q : ℝ) - 1) / ((q : ℝ) * ((q : ℝ) + 1) ^ 2) := by
    exact div_nonneg (by linarith) (mul_nonneg (by linarith) (sq_nonneg _))
  calc
    (((q : ℝ) - 1) / ((q : ℝ) * ((q : ℝ) + 1) ^ 2)) /
        ((q : ℝ) + z) ≤
      (((q : ℝ) - 1) / ((q : ℝ) * ((q : ℝ) + 1) ^ 2)) /
        (q : ℝ) := by
      exact div_le_div_of_nonneg_left hnonneg (by positivity) hqz
    _ ≤ 1 / (q : ℝ) ^ 2 - 1 / ((q : ℝ) + 1) ^ 2 := by
      field_simp
      nlinarith

/-- A real-valued function has unit-interval Lipschitz bound `K`.  We keep
the constant in `ℝ` because all transfer estimates below are real-valued. -/
def GaussUnitLipschitzBound (K : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ⦃x⦄, x ∈ Icc (0 : ℝ) 1 → ∀ ⦃y⦄, y ∈ Icc (0 : ℝ) 1 →
    |f x - f y| ≤ K * |x - y|

/-- One centered branch term, abstracting only the two numerical branch
coefficients that will be supplied explicitly below. -/
theorem abs_gaussTransfer_branchTerm_sub_le
    {q : ℕ} (hq : 0 < q) {K A D : ℝ} {f : ℝ → ℝ}
    (hK : 0 ≤ K) (hD0 : 0 ≤ D) (hf0 : f 0 = 0)
    (hf : GaussUnitLipschitzBound K f)
    {y z : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1)
    (hA : gaussBranchRatio q y /
      (((q : ℝ) + y) * ((q : ℝ) + z)) ≤ A)
    (hD : |gaussBranchRatio q y - gaussBranchRatio q z| ≤
      D * |y - z|) :
    |gaussBranchRatio q y * f (gaussInverseBranch q y) -
        gaussBranchRatio q z * f (gaussInverseBranch q z)| ≤
      K * |y - z| * (A + D / ((q : ℝ) + z)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqz : 0 < (q : ℝ) + z := by linarith [hz.1]
  have hden : 0 < ((q : ℝ) + y) * ((q : ℝ) + z) := by
    exact mul_pos (by linarith [hy.1]) hqz
  have hyi := gaussInverseBranch_mem_Icc q hq hy
  have hzi := gaussInverseBranch_mem_Icc q hq hz
  have hfdiff := hf hyi hzi
  rw [abs_gaussInverseBranch_sub q hq hy.1 hz.1] at hfdiff
  have hfz0 := hf hzi (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
  have hinvpos : 0 < gaussInverseBranch q z := by
    unfold gaussInverseBranch
    positivity
  have hinvabs : |gaussInverseBranch q z - 0| =
      1 / ((q : ℝ) + z) := by
    rw [sub_zero, abs_of_pos hinvpos]
    rfl
  rw [hf0, hinvabs] at hfz0
  simp only [sub_zero] at hfz0
  have hky0 : 0 ≤ gaussBranchRatio q y :=
    (gaussBranchRatio_pos hq hy).le
  have hfirst :
      |gaussBranchRatio q y *
          (f (gaussInverseBranch q y) - f (gaussInverseBranch q z))| ≤
        K * |y - z| * A := by
    calc
      |gaussBranchRatio q y *
          (f (gaussInverseBranch q y) - f (gaussInverseBranch q z))| =
          gaussBranchRatio q y *
            |f (gaussInverseBranch q y) - f (gaussInverseBranch q z)| := by
        rw [abs_mul, abs_of_nonneg hky0]
      _ ≤ gaussBranchRatio q y *
          (K * (|y - z| /
            (((q : ℝ) + y) * ((q : ℝ) + z)))) := by
        exact mul_le_mul_of_nonneg_left hfdiff hky0
      _ = K * |y - z| *
          (gaussBranchRatio q y /
            (((q : ℝ) + y) * ((q : ℝ) + z))) := by ring
      _ ≤ K * |y - z| * A := by
        exact mul_le_mul_of_nonneg_left hA
          (mul_nonneg hK (abs_nonneg _))
  have hDyz0 : 0 ≤ D * |y - z| := mul_nonneg hD0 (abs_nonneg _)
  have hKdiv0 : 0 ≤ K * (1 / ((q : ℝ) + z)) := by positivity
  have hsecond :
      |(gaussBranchRatio q y - gaussBranchRatio q z) *
          f (gaussInverseBranch q z)| ≤
        K * |y - z| * (D / ((q : ℝ) + z)) := by
    calc
      |(gaussBranchRatio q y - gaussBranchRatio q z) *
          f (gaussInverseBranch q z)| =
          |gaussBranchRatio q y - gaussBranchRatio q z| *
            |f (gaussInverseBranch q z)| := abs_mul _ _
      _ ≤ (D * |y - z|) * (K * (1 / ((q : ℝ) + z))) := by
        exact mul_le_mul hD hfz0 (abs_nonneg _) hDyz0
      _ = K * |y - z| * (D / ((q : ℝ) + z)) := by ring
  calc
    |gaussBranchRatio q y * f (gaussInverseBranch q y) -
        gaussBranchRatio q z * f (gaussInverseBranch q z)| =
      |gaussBranchRatio q y *
          (f (gaussInverseBranch q y) - f (gaussInverseBranch q z)) +
        (gaussBranchRatio q y - gaussBranchRatio q z) *
          f (gaussInverseBranch q z)| := by
        congr 1
        ring
    _ ≤ |gaussBranchRatio q y *
          (f (gaussInverseBranch q y) - f (gaussInverseBranch q z))| +
        |(gaussBranchRatio q y - gaussBranchRatio q z) *
          f (gaussInverseBranch q z)| := abs_add_le _ _
    _ ≤ K * |y - z| * A +
        K * |y - z| * (D / ((q : ℝ) + z)) :=
      add_le_add hfirst hsecond
    _ = K * |y - z| * (A + D / ((q : ℝ) + z)) := by ring

/-- Every digit contribution is bounded by the corresponding term of the
strictly summable majorant. -/
theorem abs_gaussTransfer_branchTerm_sub_le_majorant
    (n : ℕ) {K : ℝ} {f : ℝ → ℝ} (hK : 0 ≤ K) (hf0 : f 0 = 0)
    (hf : GaussUnitLipschitzBound K f)
    {y z : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    |gaussBranchRatio (n + 1) y *
          f (gaussInverseBranch (n + 1) y) -
        gaussBranchRatio (n + 1) z *
          f (gaussInverseBranch (n + 1) z)| ≤
      K * |y - z| * gaussTransferLipschitzMajorant n := by
  rcases n with (_ | _ | n)
  · have hbase := abs_gaussTransfer_branchTerm_sub_le
      (q := 1) (K := K) (A := 1 / 2) (D := 1 / 4)
      (by omega) hK (by norm_num) hf0 hf hy hz
      (by
        norm_num only [Nat.cast_one]
        exact gaussBranchMotionCoefficient_one_le hy hz)
      (abs_gaussBranchRatio_one_sub_le hy hz)
    have hden : (1 : ℝ) ≤ 1 + z := by linarith [hz.1]
    have hdiv : (1 / 4 : ℝ) / (1 + z) ≤ 1 / 4 :=
      div_le_self (by norm_num) hden
    calc
      |gaussBranchRatio (0 + 1) y *
            f (gaussInverseBranch (0 + 1) y) -
          gaussBranchRatio (0 + 1) z *
            f (gaussInverseBranch (0 + 1) z)| ≤
          K * |y - z| * (1 / 2 + (1 / 4) / (1 + z)) := by
        norm_num only [zero_add] at hbase ⊢
        exact hbase
      _ ≤ K * |y - z| * (3 / 4) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK (abs_nonneg _))
        linarith
      _ = K * |y - z| * gaussTransferLipschitzMajorant 0 := by
        rw [gaussTransferLipschitzMajorant_zero]
  · have hbase := abs_gaussTransfer_branchTerm_sub_le
      (q := 2) (K := K) (A := 1 / 20) (D := 1 / 18)
      (by omega) hK (by norm_num) hf0 hf hy hz
      (gaussBranchMotionCoefficient_two_le hy hz)
      (abs_gaussBranchRatio_two_sub_le hy hz)
    have hden : (2 : ℝ) ≤ 2 + z := by linarith [hz.1]
    have hdiv : (1 / 18 : ℝ) / (2 + z) ≤ 1 / 36 := by
      calc
        (1 / 18 : ℝ) / (2 + z) ≤ (1 / 18 : ℝ) / 2 := by
          exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden
        _ = 1 / 36 := by norm_num
    calc
      |gaussBranchRatio (1 + 1) y *
            f (gaussInverseBranch (1 + 1) y) -
          gaussBranchRatio (1 + 1) z *
            f (gaussInverseBranch (1 + 1) z)| ≤
          K * |y - z| * (1 / 20 + (1 / 18) / (2 + z)) := by
        norm_num at hbase ⊢
        exact hbase
      _ ≤ K * |y - z| * (7 / 90) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK (abs_nonneg _))
        norm_num at hdiv ⊢
        linarith
      _ = K * |y - z| * gaussTransferLipschitzMajorant 1 := by
        rw [gaussTransferLipschitzMajorant_one]
  · let q : ℕ := n + 3
    have hq : 3 ≤ q := by dsimp [q]; omega
    let A : ℝ := 1 / (q : ℝ) ^ 3 - 1 / ((q : ℝ) + 1) ^ 3
    let D : ℝ := ((q : ℝ) - 1) /
      ((q : ℝ) * ((q : ℝ) + 1) ^ 2)
    have hD0 : 0 ≤ D := by
      dsimp [D]
      exact div_nonneg (by
        have : (3 : ℝ) ≤ q := by exact_mod_cast hq
        linarith) (by
          have hq0 : (0 : ℝ) < q := by positivity
          exact mul_nonneg hq0.le (sq_nonneg _))
    have hbase := abs_gaussTransfer_branchTerm_sub_le
      (q := q) (K := K) (A := A) (D := D)
      (by dsimp [q]; omega) hK hD0 hf0 hf hy hz
      (by
        dsimp [A]
        exact gaussBranchMotionCoefficient_le_cube_sub hq hy hz)
      (by
        dsimp [D]
        exact abs_gaussBranchRatio_sub_le_of_three_le hq hy hz)
    have hweight : D / ((q : ℝ) + z) ≤
        1 / (q : ℝ) ^ 2 - 1 / ((q : ℝ) + 1) ^ 2 := by
      dsimp [D]
      exact gaussBranchWeightCoefficient_le_square_sub hq hz
    calc
      |gaussBranchRatio (n + 2 + 1) y *
            f (gaussInverseBranch (n + 2 + 1) y) -
          gaussBranchRatio (n + 2 + 1) z *
            f (gaussInverseBranch (n + 2 + 1) z)| ≤
          K * |y - z| * (A + D / ((q : ℝ) + z)) := by
        simpa [q] using! hbase
      _ ≤ K * |y - z| *
          (A + (1 / (q : ℝ) ^ 2 - 1 / ((q : ℝ) + 1) ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK (abs_nonneg _))
        linarith
      _ = K * |y - z| * gaussTransferLipschitzMajorant (n + 2) := by
        rw [gaussTransferLipschitzMajorant_add_two]
        dsimp [A, q]
        have hcast3 : (((n + 3 : ℕ) : ℝ) + 1) =
            ((n + 4 : ℕ) : ℝ) := by
          norm_num [Nat.cast_add]
          ring
        rw [hcast3]

/-! ## Finite and infinite transfer contraction -/

/-- The first `R` branches of the normalized Gauss transfer operator. -/
def gaussTransferPartial (R : ℕ) (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∑ n ∈ Finset.range R,
    gaussBranchRatio (n + 1) y * f (gaussInverseBranch (n + 1) y)

theorem abs_gaussTransferPartial_sub_le
    (R : ℕ) {K : ℝ} {f : ℝ → ℝ} (hK : 0 ≤ K) (hf0 : f 0 = 0)
    (hf : GaussUnitLipschitzBound K f)
    {y z : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    |gaussTransferPartial R f y - gaussTransferPartial R f z| ≤
      (527 / 540 : ℝ) * K * |y - z| := by
  unfold gaussTransferPartial
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ n ∈ Finset.range R,
        (gaussBranchRatio (n + 1) y * f (gaussInverseBranch (n + 1) y) -
          gaussBranchRatio (n + 1) z * f (gaussInverseBranch (n + 1) z))| ≤
      ∑ n ∈ Finset.range R,
        |gaussBranchRatio (n + 1) y * f (gaussInverseBranch (n + 1) y) -
          gaussBranchRatio (n + 1) z * f (gaussInverseBranch (n + 1) z)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range R,
        K * |y - z| * gaussTransferLipschitzMajorant n := by
      apply Finset.sum_le_sum
      intro n hn
      exact abs_gaussTransfer_branchTerm_sub_le_majorant n hK hf0 hf hy hz
    _ = K * |y - z| *
        (∑ n ∈ Finset.range R, gaussTransferLipschitzMajorant n) := by
      rw [Finset.mul_sum]
    _ ≤ K * |y - z| * (527 / 540 : ℝ) := by
      exact mul_le_mul_of_nonneg_left
        (sum_range_gaussTransferLipschitzMajorant_le R)
        (mul_nonneg hK (abs_nonneg _))
    _ = (527 / 540 : ℝ) * K * |y - z| := by ring

/-- Centered unit-Lipschitz data give an absolutely summable transfer series
at every state in the closed unit interval. -/
theorem summable_gaussTransfer_branch_of_centered_lipschitz
    {K : ℝ} {f : ℝ → ℝ} (hK : 0 ≤ K) (hf0 : f 0 = 0)
    (hf : GaussUnitLipschitzBound K f)
    {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    Summable fun n : ℕ =>
      gaussBranchRatio (n + 1) y * f (gaussInverseBranch (n + 1) y) := by
  have hweights : Summable fun n : ℕ => gaussBranchRatio (n + 1) y :=
    (hasSum_gaussBranchRatio y hy).summable
  have hmajor : Summable fun n : ℕ =>
      K * gaussBranchRatio (n + 1) y := hweights.mul_left K
  apply Summable.of_norm_bounded hmajor
  intro n
  have hn : 0 < n + 1 := by omega
  have hi := gaussInverseBranch_mem_Icc (n + 1) hn hy
  have hfbound := hf hi (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
  simp only [hf0, sub_zero] at hfbound
  have hinvnonneg : 0 ≤ gaussInverseBranch (n + 1) y := hi.1
  have hinvle : |gaussInverseBranch (n + 1) y| ≤ 1 := by
    rw [abs_of_nonneg hinvnonneg]
    exact hi.2
  have hfone : |f (gaussInverseBranch (n + 1) y)| ≤ K := by
    calc
      |f (gaussInverseBranch (n + 1) y)| ≤
          K * |gaussInverseBranch (n + 1) y| := hfbound
      _ ≤ K * 1 := by
        apply mul_le_mul_of_nonneg_left _ hK
        simpa only [sub_zero] using! hinvle
      _ = K := mul_one _
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (gaussBranchRatio_pos hn hy).le]
  simpa only [mul_comm] using!
    (mul_le_mul_of_nonneg_left hfone
      (gaussBranchRatio_pos hn hy).le)

/-- The finite branch sums converge to the total transfer operator. -/
theorem tendsto_gaussTransferPartial
    {K : ℝ} {f : ℝ → ℝ} (hK : 0 ≤ K) (hf0 : f 0 = 0)
    (hf : GaussUnitLipschitzBound K f)
    {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun R : ℕ => gaussTransferPartial R f y) atTop
      (𝓝 (gaussTransfer f y)) := by
  have hs := summable_gaussTransfer_branch_of_centered_lipschitz
    hK hf0 hf hy
  unfold gaussTransferPartial gaussTransfer
  exact hs.hasSum.tendsto_sum_nat

/-- The total normalized Gauss transfer operator strictly contracts the
unit-interval Lipschitz seminorm on centered functions. -/
theorem gaussTransfer_strict_lipschitz_contraction
    {K : ℝ} {f : ℝ → ℝ} (hK : 0 ≤ K) (hf0 : f 0 = 0)
    (hf : GaussUnitLipschitzBound K f) :
    GaussUnitLipschitzBound ((527 / 540 : ℝ) * K) (gaussTransfer f) := by
  intro y hy z hz
  have hyT := tendsto_gaussTransferPartial hK hf0 hf hy
  have hzT := tendsto_gaussTransferPartial hK hf0 hf hz
  have hlim : Tendsto
      (fun R : ℕ => |gaussTransferPartial R f y -
        gaussTransferPartial R f z|) atTop
      (𝓝 |gaussTransfer f y - gaussTransfer f z|) :=
    (hyT.sub hzT).abs
  exact le_of_tendsto' hlim fun R =>
    abs_gaussTransferPartial_sub_le R hK hf0 hf hy hz

/-- Center the output of one transfer step at the state `0`. -/
def gaussCenteredTransfer (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  gaussTransfer f y - gaussTransfer f 0

theorem gaussCenteredTransfer_zero (f : ℝ → ℝ) :
    gaussCenteredTransfer f 0 = 0 := by
  simp [gaussCenteredTransfer]

theorem gaussCenteredTransfer_strict_lipschitz_contraction
    {K : ℝ} {f : ℝ → ℝ} (hK : 0 ≤ K) (hf0 : f 0 = 0)
    (hf : GaussUnitLipschitzBound K f) :
    GaussUnitLipschitzBound ((527 / 540 : ℝ) * K)
      (gaussCenteredTransfer f) := by
  have htransfer := gaussTransfer_strict_lipschitz_contraction hK hf0 hf
  intro y hy z hz
  simpa only [gaussCenteredTransfer, sub_sub_sub_cancel_right] using!
    htransfer hy hz

/-- Iterating the centered transfer operator gives the explicit exponential
factor `(527/540)^m`. -/
theorem gaussCenteredTransfer_iterate_lipschitz
    (m : ℕ) {K : ℝ} {f : ℝ → ℝ} (hK : 0 ≤ K) (hf0 : f 0 = 0)
    (hf : GaussUnitLipschitzBound K f) :
    GaussUnitLipschitzBound ((527 / 540 : ℝ) ^ m * K)
      ((gaussCenteredTransfer^[m]) f) := by
  induction m with
  | zero => simpa using! hf
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      have hpowK : 0 ≤ (527 / 540 : ℝ) ^ m * K :=
        mul_nonneg (by positivity) hK
      have hzero : (gaussCenteredTransfer^[m]) f 0 = 0 := by
        cases m with
        | zero => simpa using! hf0
        | succ m =>
            rw [Function.iterate_succ_apply']
            exact gaussCenteredTransfer_zero _
      have hstep := gaussCenteredTransfer_strict_lipschitz_contraction
        hpowK hzero ih
      simpa only [mul_assoc, mul_left_comm, mul_comm, pow_succ] using! hstep

theorem gaussCenteredTransfer_iterate_zero
    (m : ℕ) (hm : 0 < m) (f : ℝ → ℝ) :
    (gaussCenteredTransfer^[m]) f 0 = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  rw [Function.iterate_succ_apply']
  exact gaussCenteredTransfer_zero _

/-- The explicit exponential factor tends to zero. -/
theorem tendsto_gaussTransferContractionCoefficient_pow :
    Tendsto (fun m : ℕ => (527 / 540 : ℝ) ^ m) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-! ## Finite one-digit conditional densities -/

/-- Lipschitz envelope for the branch with positive digit `q`.  The value at
`q=0` is irrelevant and is set to zero. -/
def gaussBranchWeightLipschitzEnvelope (q : ℕ) : ℝ :=
  if q = 0 then 0
  else if q = 1 then 1 / 4
  else if q = 2 then 1 / 18
  else ((q : ℝ) - 1) / ((q : ℝ) * ((q : ℝ) + 1) ^ 2)

theorem abs_gaussBranchRatio_sub_le_envelope
    {q : ℕ} (hq : 0 < q) {y z : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    |gaussBranchRatio q y - gaussBranchRatio q z| ≤
      gaussBranchWeightLipschitzEnvelope q * |y - z| := by
  rcases q with (_ | _ | q)
  · omega
  · simpa [gaussBranchWeightLipschitzEnvelope] using!
      abs_gaussBranchRatio_one_sub_le hy hz
  · rcases q with (_ | q)
    · simpa [gaussBranchWeightLipschitzEnvelope] using!
      abs_gaussBranchRatio_two_sub_le hy hz
    · have hthree : 3 ≤ q + 3 := by omega
      have h := abs_gaussBranchRatio_sub_le_of_three_le hthree hy hz
      convert! h using 1

/-- Each branch Lipschitz constant is bounded by that branch's density at
the reference state zero. -/
theorem gaussBranchWeightLipschitzEnvelope_le_ratio_zero
    {q : ℕ} (hq : 0 < q) :
    gaussBranchWeightLipschitzEnvelope q ≤ gaussBranchRatio q 0 := by
  rcases q with (_ | _ | q)
  · omega
  · norm_num [gaussBranchWeightLipschitzEnvelope, gaussBranchRatio]
  · rcases q with (_ | q)
    · norm_num [gaussBranchWeightLipschitzEnvelope, gaussBranchRatio]
    · have hqR : (3 : ℝ) ≤ q + 3 := by exact_mod_cast (show 3 ≤ q + 3 by omega)
      simp only [gaussBranchWeightLipschitzEnvelope,
        if_neg (by omega : q + 3 ≠ 0), if_neg (by omega : q + 3 ≠ 1),
        if_neg (by omega : q + 3 ≠ 2), gaussBranchRatio, add_zero,
        Nat.cast_add, one_div]
      norm_num only [Nat.cast_one]
      have hq0 : 0 < (q : ℝ) + 3 := by positivity
      have hq1 : 0 < (q : ℝ) + 4 := by positivity
      field_simp
      nlinarith

/-- Unnormalized tail density for a finite collection of positive first
digits, indexed as `q=n+1`. -/
def finiteGaussDigitTailDensity (digits : Finset ℕ) (y : ℝ) : ℝ :=
  ∑ n ∈ digits, gaussBranchRatio (n + 1) y

/-- The same finite digit collection's stationary probability. -/
def finiteGaussDigitProbability (digits : Finset ℕ) : ℝ :=
  ∑ n ∈ digits, gaussMeasure.real (firstDigitCylinder (n + 1))

theorem finiteGaussDigitTailDensity_nonneg
    (digits : Finset ℕ) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    0 ≤ finiteGaussDigitTailDensity digits y := by
  unfold finiteGaussDigitTailDensity
  exact Finset.sum_nonneg fun n hn => (gaussBranchRatio_pos (by omega) hy).le

theorem finiteGaussDigitProbability_nonneg (digits : Finset ℕ) :
    0 ≤ finiteGaussDigitProbability digits := by
  unfold finiteGaussDigitProbability
  exact Finset.sum_nonneg fun _ _ => measureReal_nonneg

/-- Before normalization, the finite conditional density has Lipschitz
constant no larger than its value at zero. -/
theorem finiteGaussDigitTailDensity_lipschitz_ratio_zero
    (digits : Finset ℕ) :
    GaussUnitLipschitzBound (finiteGaussDigitTailDensity digits 0)
      (finiteGaussDigitTailDensity digits) := by
  intro y hy z hz
  unfold finiteGaussDigitTailDensity
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ n ∈ digits,
        (gaussBranchRatio (n + 1) y - gaussBranchRatio (n + 1) z)| ≤
      ∑ n ∈ digits,
        |gaussBranchRatio (n + 1) y - gaussBranchRatio (n + 1) z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ digits,
        gaussBranchWeightLipschitzEnvelope (n + 1) * |y - z| := by
      apply Finset.sum_le_sum
      intro n hn
      exact abs_gaussBranchRatio_sub_le_envelope (by omega) hy hz
    _ ≤ ∑ n ∈ digits,
        gaussBranchRatio (n + 1) 0 * |y - z| := by
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_right
        (gaussBranchWeightLipschitzEnvelope_le_ratio_zero (by omega))
        (abs_nonneg _)
    _ = (∑ n ∈ digits, gaussBranchRatio (n + 1) 0) * |y - z| := by
      rw [Finset.sum_mul]

theorem gaussBranchRatio_zero_le_six_mul_measureReal
    {q : ℕ} (hq : 0 < q) :
    gaussBranchRatio q 0 ≤
      6 * gaussMeasure.real (firstDigitCylinder q) := by
  have h := ofReal_gaussBranchRatio_le_six_mul_firstDigitMeasure
    hq (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
  have hreal := ENNReal.toReal_mono (by finiteness) h
  rw [ENNReal.toReal_ofReal (gaussBranchRatio_pos hq (by norm_num)).le,
    ENNReal.toReal_mul, ENNReal.toReal_ofNat] at hreal
  change gaussBranchRatio q 0 ≤
    6 * (gaussMeasure (firstDigitCylinder q)).toReal
  exact hreal

theorem finiteGaussDigitTailDensity_zero_le_six_mul_probability
    (digits : Finset ℕ) :
    finiteGaussDigitTailDensity digits 0 ≤
      6 * finiteGaussDigitProbability digits := by
  unfold finiteGaussDigitTailDensity finiteGaussDigitProbability
  calc
    (∑ n ∈ digits, gaussBranchRatio (n + 1) 0) ≤
      ∑ n ∈ digits,
        6 * gaussMeasure.real (firstDigitCylinder (n + 1)) := by
      apply Finset.sum_le_sum
      intro n hn
      exact gaussBranchRatio_zero_le_six_mul_measureReal (by omega)
    _ = 6 * ∑ n ∈ digits,
        gaussMeasure.real (firstDigitCylinder (n + 1)) := by
      rw [Finset.mul_sum]

/-- Normalizing a nonempty finite digit density by its stationary mass gives
the uniform Lipschitz constant `6`, independent of the chosen digits. -/
theorem finiteGaussDigitTailDensity_div_probability_lipschitz
    (digits : Finset ℕ) (hprob : 0 < finiteGaussDigitProbability digits) :
    GaussUnitLipschitzBound 6
      (fun y => finiteGaussDigitTailDensity digits y /
        finiteGaussDigitProbability digits) := by
  have hlip := finiteGaussDigitTailDensity_lipschitz_ratio_zero digits
  intro y hy z hz
  rw [div_sub_div_same]
  rw [abs_div, abs_of_pos hprob]
  have h0 := finiteGaussDigitTailDensity_zero_le_six_mul_probability digits
  calc
    |finiteGaussDigitTailDensity digits y -
        finiteGaussDigitTailDensity digits z| /
        finiteGaussDigitProbability digits ≤
      (finiteGaussDigitTailDensity digits 0 * |y - z|) /
        finiteGaussDigitProbability digits := by
      exact div_le_div_of_nonneg_right (hlip hy hz) hprob.le
    _ ≤ (6 * finiteGaussDigitProbability digits * |y - z|) /
        finiteGaussDigitProbability digits := by
      apply div_le_div_of_nonneg_right _ hprob.le
      exact mul_le_mul_of_nonneg_right h0 (abs_nonneg _)
    _ = 6 * |y - z| := by field_simp

/-- The normalized finite-digit density, centered at the reference state. -/
def finiteGaussDigitCenteredDensity
    (digits : Finset ℕ) (y : ℝ) : ℝ :=
  finiteGaussDigitTailDensity digits y /
      finiteGaussDigitProbability digits -
    finiteGaussDigitTailDensity digits 0 /
      finiteGaussDigitProbability digits

theorem finiteGaussDigitCenteredDensity_zero (digits : Finset ℕ) :
    finiteGaussDigitCenteredDensity digits 0 = 0 := by
  simp [finiteGaussDigitCenteredDensity]

theorem finiteGaussDigitCenteredDensity_lipschitz
    (digits : Finset ℕ) (hprob : 0 < finiteGaussDigitProbability digits) :
    GaussUnitLipschitzBound 6
      (finiteGaussDigitCenteredDensity digits) := by
  have h := finiteGaussDigitTailDensity_div_probability_lipschitz
    digits hprob
  intro y hy z hz
  simpa only [finiteGaussDigitCenteredDensity, sub_sub_sub_cancel_right] using!
    h hy hz

/-- Fully explicit exponential loss of memory for every nonempty finite
one-digit selection, at the level of the centered conditional density. -/
theorem finiteGaussDigitCenteredDensity_iterate_lipschitz
    (digits : Finset ℕ) (hprob : 0 < finiteGaussDigitProbability digits)
    (m : ℕ) :
    GaussUnitLipschitzBound
      (6 * (527 / 540 : ℝ) ^ m)
      ((gaussCenteredTransfer^[m])
        (finiteGaussDigitCenteredDensity digits)) := by
  have h := gaussCenteredTransfer_iterate_lipschitz m
    (K := 6) (f := finiteGaussDigitCenteredDensity digits)
    (by norm_num) (finiteGaussDigitCenteredDensity_zero digits)
    (finiteGaussDigitCenteredDensity_lipschitz digits hprob)
  convert! h using 1
  ring

theorem abs_finiteGaussDigitCenteredDensity_iterate_le
    (digits : Finset ℕ) (hprob : 0 < finiteGaussDigitProbability digits)
    {m : ℕ} (hm : 0 < m) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    |(gaussCenteredTransfer^[m])
        (finiteGaussDigitCenteredDensity digits) y| ≤
      6 * (527 / 540 : ℝ) ^ m := by
  have hlip := finiteGaussDigitCenteredDensity_iterate_lipschitz
    digits hprob m
  have hzero := gaussCenteredTransfer_iterate_zero m hm
    (finiteGaussDigitCenteredDensity digits)
  have h := hlip hy (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
  rw [hzero, sub_zero] at h
  calc
    |(gaussCenteredTransfer^[m])
        (finiteGaussDigitCenteredDensity digits) y| ≤
      (6 * (527 / 540 : ℝ) ^ m) * |y - 0| := h
    _ ≤ (6 * (527 / 540 : ℝ) ^ m) * 1 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [sub_zero, abs_of_nonneg hy.1]
      exact hy.2
    _ = 6 * (527 / 540 : ℝ) ^ m := mul_one _

end

end Erdos1002
