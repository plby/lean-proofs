/- leanprover/lean4:v4.33.0 -/

import ErdosProblems.Erdos175.TypeIICoefficientCollapse
import ErdosProblems.Erdos175.TypeIIScalar

/-!
# Closed global estimates for the Vaughan Type-II sums

This file combines the zero-threshold reciprocal-sum estimate, the sharp
support-scale cube bounds, the explicit coefficient majorants, and the
dyadic block count.  The resulting exponent is `27/28` in the square-root
variable, hence `27/56` in the original variable.  All logarithmic losses
are absorbed into six powers of one common logarithm.
-/

noncomputable section

namespace Erdos175.TypeIIGlobal

open Erdos175.VaughanTypeIIDyadic
open Erdos175.VaughanTypeIICoefficients

private lemma three_le_scalarLog {y : ℕ} (hy : 1 ≤ y) :
    3 ≤ TypeIIScalar.scalarLog y := by
  have harg : (256 : ℝ) ≤ 256 * (y : ℝ) ^ 2 := by
    have hyR : (1 : ℝ) ≤ y := by exact_mod_cast hy
    nlinarith [sq_nonneg ((y : ℝ) - 1)]
  have hlog256 : (3 : ℝ) ≤ Real.log 256 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
    have hlog2 := Real.log_two_gt_d9
    norm_num at hlog2 ⊢
    nlinarith
  exact hlog256.trans (by
    unfold TypeIIScalar.scalarLog
    exact Real.log_le_log (by norm_num) harg)

/-- A dyadic count whose endpoint lies below `256 y²` is at most three
copies of the common logarithmic envelope. -/
lemma dyadicCount_cast_le_three_scalarLog
    {y N : ℕ} (hy : 1 ≤ y) (hN : N ≠ 0)
    (hNle : N ≤ 256 * y ^ 2) :
    (TypeI.dyadicCount N : ℝ) ≤ 3 * TypeIIScalar.scalarLog y := by
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast hNpos
  have hlogNH : Real.log (N : ℝ) ≤ TypeIIScalar.scalarLog y := by
    unfold TypeIIScalar.scalarLog
    apply Real.log_le_log
    · positivity
    · exact_mod_cast hNle
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv : Real.log (N : ℝ) / Real.log 2 ≤
      2 * Real.log (N : ℝ) := by
    rw [div_le_iff₀ hlog2]
    nlinarith [Real.log_two_gt_d9]
  have hraw := TypeI.dyadicCount_cast_le_log_div_add_one hN
  have hH := TypeIIScalar.scalarLog_one_le hy
  calc
    (TypeI.dyadicCount N : ℝ) ≤
        Real.log N / Real.log 2 + 1 := hraw
    _ ≤ 2 * Real.log N + 1 := by linarith
    _ ≤ 3 * TypeIIScalar.scalarLog y := by linarith

/-- The oriented zero-threshold analytic factor has the uniform scalar
bound needed by both coefficient families. -/
lemma orientedDyadicAnalyticFactor_zero_le_closed
    {x : ℝ} {y y' j k : ℕ}
    (hy : 1 ≤ y) (hy' : y' ≤ 2 * y)
    (hactive : blockActive y y' j k)
    (hlarge : 2304 ≤ orientedLargeScale j k)
    (hcube : orientedLargeScale j k ^ 3 ≤ 512 * y ^ 2)
    (hxlower : (y : ℝ) ^ 2 ≤ x)
    (hxupper : x ≤ 12 * (y : ℝ) ^ 2) :
    (if j < k then dyadicAnalyticFactor x y y' k j 0
     else dyadicAnalyticFactor x y y' j k 0) ≤
      64 * (y : ℝ) ^ (13 / 28 : ℝ) * TypeIIScalar.scalarLog y := by
  let U := orientedLargeScale j k
  let V := orientedSmallScale j k
  have hU : 0 < U := by simp [U]
  have hV : 0 < V := by simp [V]
  have hVU : V ≤ U := by
    simpa only [U, V] using orientedSmallScale_le_orientedLargeScale j k
  have hproduct : U * V ≤ 2 * y := by
    dsimp only [U, V]
    rw [orientedLargeScale_mul_orientedSmallScale]
    exact (blockActive_lower_product_le hactive).trans hy'
  have hactive' : y < 4 * (U * V) := by
    dsimp only [U, V]
    rw [orientedLargeScale_mul_orientedSmallScale]
    exact blockActive_y_lt_four_mul_lower_product hactive
  have hhone : 12 * (x / (V : ℝ)) ≤ (U : ℝ) ^ 4 :=
    honeScale_of_active_oriented hxupper hlarge hV hVU hactive'
  have hx : 0 < x := by
    have hyR : (1 : ℝ) ≤ y := by exact_mod_cast hy
    exact lt_of_lt_of_le (sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hyR)) hxlower
  have hscalar :
      Real.sqrt
          (2 * (U : ℝ) +
            TypeII.orientedPowerBlockFarQ x U V * (V : ℝ)) ≤
        64 * (y : ℝ) ^ (13 / 28 : ℝ) * TypeIIScalar.scalarLog y :=
    TypeIIScalar.sqrt_two_mul_add_orientedPowerBlockFarQ_mul_le
      hy hU hV hVU hactive' hproduct hcube hxlower hxupper
  by_cases hjk : j < k
  · simp only [hjk, if_pos]
    have hfactor := dyadicAnalyticFactor_zero_le_orientedPowerBlockFarQ
      x y y' k j hx (by
        simpa [U, V, orientedLargeScale, orientedSmallScale, hjk] using hhone)
    exact hfactor.trans (by
      simpa [U, V, orientedLargeScale, orientedSmallScale, hjk] using hscalar)
  · simp only [hjk, if_neg]
    have hfactor := dyadicAnalyticFactor_zero_le_orientedPowerBlockFarQ
      x y y' j k hx (by
        simpa [U, V, orientedLargeScale, orientedSmallScale, hjk] using hhone)
    exact hfactor.trans (by
      simpa [U, V, orientedLargeScale, orientedSmallScale, hjk] using hscalar)

private lemma sigma22_largeScale_ge
    {M j k : ℕ} (hMlarge : 4608 ≤ M)
    (hs : sigma22SupportActive M j) :
    2304 ≤ orientedLargeScale j k := by
  have hsupport : M < 2 ^ j * 2 := by
    simpa only [sigma22SupportActive, pow_succ] using hs
  have hjbase : 2304 ≤ 2 ^ j := by omega
  by_cases hjk : j < k
  · have hjkpow : 2 ^ j ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hjk.le
    rw [orientedLargeScale, if_pos hjk]
    exact hjbase.trans hjkpow
  · rw [orientedLargeScale, if_neg hjk]
    exact hjbase

private lemma sigma3_largeScale_ge
    {M j k : ℕ} (hMlarge : 4608 ≤ M)
    (hs : sigma3SupportActive M M j k) :
    2304 ≤ orientedLargeScale j k := by
  have hsmall := sigma3SupportActive_lt_two_mul_orientedSmallScale
    (L := M) (M := M) (K := M) (j := j) (k := k) le_rfl le_rfl hs
  have hsmallLarge := orientedSmallScale_le_orientedLargeScale j k
  omega

private lemma log_scale_le_two_scalarLog
    {y U V : ℕ} (hy : 1 ≤ y) (hU : 0 < U) (hV : 0 < V)
    (hUV : U * V ≤ 2 * y) :
    Real.log (2 * (U : ℝ)) ≤ 2 * TypeIIScalar.scalarLog y := by
  have h := TypeIIScalar.one_add_log_two_mul_le_two_scalarLog hy hU hV hUV
  linarith

/-- Uniform closed bound for one supported active `Σ₂,₂` block. -/
lemma sigma22OrientedBlockMajorant_le_final
    {x : ℝ} {y y' M j k : ℕ}
    (hy : 1 ≤ y) (hy' : y' ≤ 2 * y)
    (hM3 : M ^ 3 ≤ y) (hyM : y ≤ 8 * M ^ 3)
    (hMlarge : 4608 ≤ M)
    (hj : j ∈ Finset.range (TypeI.dyadicCount (M * M)))
    (hactive : blockActive y y' j k)
    (hs : sigma22SupportActive M j)
    (hxlower : (y : ℝ) ^ 2 ≤ x)
    (hxupper : x ≤ 12 * (y : ℝ) ^ 2) :
    sigma22OrientedBlockMajorant x y y' j k 0 ≤
      2048 * (y : ℝ) ^ (27 / 28 : ℝ) * TypeIIScalar.scalarLog y ^ 4 := by
  have hy0 : 0 < y := by omega
  have hH := TypeIIScalar.scalarLog_one_le hy
  have hprod : orientedLargeScale j k * orientedSmallScale j k ≤ 2 * y := by
    rw [orientedLargeScale_mul_orientedSmallScale]
    exact (blockActive_lower_product_le hactive).trans hy'
  have hlogLarge := log_scale_le_two_scalarLog hy
    (orientedLargeScale_pos j k) (orientedSmallScale_pos j k) hprod
  have hlogSmall := log_scale_le_two_scalarLog hy
    (orientedSmallScale_pos j k) (orientedLargeScale_pos j k)
      (by simpa [Nat.mul_comm] using hprod)
  have hcube := sigma22_orientedLargeScale_cube_le_512
    hy0 hy' hM3 hyM hj hactive hs
  have hanalytic0 := orientedDyadicAnalyticFactor_zero_le_closed
    hy hy' hactive (sigma22_largeScale_ge hMlarge hs) hcube hxlower hxupper
  have hanalytic :
      (if j < k then dyadicAnalyticFactor x y y' k j 0
       else dyadicAnalyticFactor x y y' j k 0) ≤
        64 * (y : ℝ) ^ (13 / 28 : ℝ) *
          (2 * TypeIIScalar.scalarLog y) := by
    calc
      _ ≤ 64 * (y : ℝ) ^ (13 / 28 : ℝ) *
          TypeIIScalar.scalarLog y := hanalytic0
      _ ≤ 64 * (y : ℝ) ^ (13 / 28 : ℝ) *
          (2 * TypeIIScalar.scalarLog y) := by
        exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  have hs1 : sigma22SupportActive 1 j := by
    unfold sigma22SupportActive at hs ⊢
    omega
  have hblock := TypeIICoefficientCollapse.sigma22OrientedBlockMajorant_le_closed
    (x := x) (y := y) (y' := y') (j := j) (k := k)
      (C := 64) (H := 2 * TypeIIScalar.scalarLog y)
      hy0 hy' hactive hs1 (by norm_num) (by nlinarith)
      hlogLarge hlogSmall hanalytic
  calc
    sigma22OrientedBlockMajorant x y y' j k 0 ≤
        (2 * 64 : ℝ) * (y : ℝ) ^ (27 / 28 : ℝ) *
          (2 * TypeIIScalar.scalarLog y) ^ 4 := hblock
    _ = 2048 * (y : ℝ) ^ (27 / 28 : ℝ) *
          TypeIIScalar.scalarLog y ^ 4 := by ring

/-- Uniform closed bound for one supported active `Σ₃` block. -/
lemma sigma3OrientedBlockMajorant_le_final
    {x : ℝ} {y y' M j k : ℕ}
    (hy : 1 ≤ y) (hy' : y' ≤ 2 * y)
    (hM : 1 ≤ M) (hM3 : M ^ 3 ≤ y) (hyM : y ≤ 8 * M ^ 3)
    (hMlarge : 4608 ≤ M)
    (hactive : blockActive y y' j k)
    (hs : sigma3SupportActive M M j k)
    (hxlower : (y : ℝ) ^ 2 ≤ x)
    (hxupper : x ≤ 12 * (y : ℝ) ^ 2) :
    sigma3OrientedBlockMajorant x y y' M j k 0 ≤
      4096 * (y : ℝ) ^ (27 / 28 : ℝ) * TypeIIScalar.scalarLog y ^ 4 := by
  have hy0 : 0 < y := by omega
  have hH := TypeIIScalar.scalarLog_one_le hy
  have hprod : orientedLargeScale j k * orientedSmallScale j k ≤ 2 * y := by
    rw [orientedLargeScale_mul_orientedSmallScale]
    exact (blockActive_lower_product_le hactive).trans hy'
  have hlogLarge := log_scale_le_two_scalarLog hy
    (orientedLargeScale_pos j k) (orientedSmallScale_pos j k) hprod
  have hlogSmall := log_scale_le_two_scalarLog hy
    (orientedSmallScale_pos j k) (orientedLargeScale_pos j k)
      (by simpa [Nat.mul_comm] using hprod)
  have hlogM0 : Real.log (M : ℝ) ≤ TypeIIScalar.scalarLog y := by
    unfold TypeIIScalar.scalarLog
    apply Real.log_le_log
    · positivity
    · have hMy : M ≤ y := by
        have hMM3 : M ≤ M ^ 3 := Nat.le_self_pow (by norm_num) M
        omega
      have hy256 : y ≤ 256 * y ^ 2 := by nlinarith
      exact_mod_cast hMy.trans hy256
  have hlogM : Real.log (M : ℝ) + 3 ≤
      2 * TypeIIScalar.scalarLog y := by
    linarith [three_le_scalarLog hy]
  have hcube := sigma3_orientedLargeScale_cube_le_512
    (show 0 < y by omega) hy' hyM hactive hs
  have hanalytic0 := orientedDyadicAnalyticFactor_zero_le_closed
    hy hy' hactive (sigma3_largeScale_ge hMlarge hs) hcube hxlower hxupper
  have hanalytic :
      (if j < k then dyadicAnalyticFactor x y y' k j 0
       else dyadicAnalyticFactor x y y' j k 0) ≤
        64 * (y : ℝ) ^ (13 / 28 : ℝ) *
          (2 * TypeIIScalar.scalarLog y) := by
    calc
      _ ≤ 64 * (y : ℝ) ^ (13 / 28 : ℝ) *
          TypeIIScalar.scalarLog y := hanalytic0
      _ ≤ 64 * (y : ℝ) ^ (13 / 28 : ℝ) *
          (2 * TypeIIScalar.scalarLog y) := by
        exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  have hblock := TypeIICoefficientCollapse.sigma3OrientedBlockMajorant_le_closed
    (x := x) (y := y) (y' := y') (M := M) (j := j) (k := k)
      (C := 64) (H := 2 * TypeIIScalar.scalarLog y)
      hy0 hy' hM hactive hs (by norm_num) (by nlinarith)
      hlogLarge hlogSmall hlogM hanalytic
  calc
    sigma3OrientedBlockMajorant x y y' M j k 0 ≤
        (4 * 64 : ℝ) * (y : ℝ) ^ (27 / 28 : ℝ) *
          (2 * TypeIIScalar.scalarLog y) ^ 4 := hblock
    _ = 4096 * (y : ℝ) ^ (27 / 28 : ℝ) *
          TypeIIScalar.scalarLog y ^ 4 := by ring

private lemma endpoint_le_256_mul_sq {y N : ℕ}
    (hy : 1 ≤ y) (hN : N ≤ 2 * y) : N ≤ 256 * y ^ 2 := by
  have hy256 : 2 * y ≤ 256 * y ^ 2 := by nlinarith
  exact hN.trans hy256

/-- Closed global estimate for `Σ₂,₂` in the square-root variable. -/
theorem norm_sigma22_le_closed
    {x : ℝ} {y y' M : ℕ}
    (hy : 1 ≤ y) (hyy' : y ≤ y') (hy' : y' ≤ 2 * y)
    (hM : 1 ≤ M) (hM3 : M ^ 3 ≤ y) (hyM : y ≤ 8 * M ^ 3)
    (hMlarge : 4608 ≤ M)
    (hxlower : (y : ℝ) ^ 2 ≤ x)
    (hxupper : x ≤ 12 * (y : ℝ) ^ 2) :
    ‖VaughanFourSums.sigma22 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M M‖ ≤
      18432 * (y : ℝ) ^ (27 / 28 : ℝ) *
        TypeIIScalar.scalarLog y ^ 6 := by
  have hx : 0 < x := by
    have hyR : (1 : ℝ) ≤ y := by exact_mod_cast hy
    exact lt_of_lt_of_le (sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hyR)) hxlower
  have hraw := norm_sigma22_le_sum_dyadic_coefficient_majorant_supported
    y y' M M x hx
  let C : ℝ := 2048 * (y : ℝ) ^ (27 / 28 : ℝ) *
    TypeIIScalar.scalarLog y ^ 4
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hsum :
      (∑ j ∈ Finset.range (TypeI.dyadicCount (M * M)),
        ∑ k ∈ Finset.range (TypeI.dyadicCount y'),
          if blockActive y y' j k ∧ sigma22SupportActive M j then
            sigma22OrientedBlockMajorant x y y' j k 0 else 0) ≤
        (TypeI.dyadicCount (M * M) : ℝ) *
          TypeI.dyadicCount y' * C := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (TypeI.dyadicCount (M * M)),
          ∑ _k ∈ Finset.range (TypeI.dyadicCount y'), C := by
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro k hk
        by_cases hact : blockActive y y' j k ∧ sigma22SupportActive M j
        · simp only [hact, if_pos]
          exact sigma22OrientedBlockMajorant_le_final hy hy' hM3 hyM hMlarge
            hj hact.1 hact.2 hxlower hxupper
        · simp only [hact, if_neg]
          exact hC
      _ = (TypeI.dyadicCount (M * M) : ℝ) *
          TypeI.dyadicCount y' * C := by simp [mul_assoc]
  have hMMne : M * M ≠ 0 := mul_ne_zero (by omega) (by omega)
  have hMMle : M * M ≤ 256 * y ^ 2 := by
    have hMM3 : M * M ≤ M ^ 3 := by
      calc M * M = (M * M) * 1 := by ring
        _ ≤ (M * M) * M := Nat.mul_le_mul_left (M * M) hM
        _ = M ^ 3 := by ring
    exact hMM3.trans (hM3.trans (by nlinarith))
  have hy'ne : y' ≠ 0 := by omega
  have hcount1 := dyadicCount_cast_le_three_scalarLog hy hMMne hMMle
  have hcount2 := dyadicCount_cast_le_three_scalarLog hy hy'ne
    (endpoint_le_256_mul_sq hy hy')
  have hcountProd :
      (TypeI.dyadicCount (M * M) : ℝ) * TypeI.dyadicCount y' ≤
        9 * TypeIIScalar.scalarLog y ^ 2 := by
    calc
      (TypeI.dyadicCount (M * M) : ℝ) * TypeI.dyadicCount y' ≤
          (3 * TypeIIScalar.scalarLog y) *
            (3 * TypeIIScalar.scalarLog y) := by
              exact mul_le_mul hcount1 hcount2 (by positivity)
                (by have := TypeIIScalar.scalarLog_one_le hy; positivity)
      _ = 9 * TypeIIScalar.scalarLog y ^ 2 := by ring
  calc
    ‖VaughanFourSums.sigma22 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M M‖ ≤ _ := hraw
    _ ≤ (TypeI.dyadicCount (M * M) : ℝ) *
          TypeI.dyadicCount y' * C := hsum
    _ ≤ (9 * TypeIIScalar.scalarLog y ^ 2) * C :=
      mul_le_mul_of_nonneg_right hcountProd hC
    _ = 18432 * (y : ℝ) ^ (27 / 28 : ℝ) *
          TypeIIScalar.scalarLog y ^ 6 := by simp only [C]; ring

/-- Closed global estimate for `Σ₃` in the square-root variable. -/
theorem norm_sigma3_le_closed
    {x : ℝ} {y y' M : ℕ}
    (hy : 1 ≤ y) (hyy' : y ≤ y') (hy' : y' ≤ 2 * y)
    (hM : 1 ≤ M) (hM3 : M ^ 3 ≤ y) (hyM : y ≤ 8 * M ^ 3)
    (hMlarge : 4608 ≤ M)
    (hxlower : (y : ℝ) ^ 2 ≤ x)
    (hxupper : x ≤ 12 * (y : ℝ) ^ 2) :
    ‖VaughanFourSums.sigma3 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M M‖ ≤
      36864 * (y : ℝ) ^ (27 / 28 : ℝ) *
        TypeIIScalar.scalarLog y ^ 6 := by
  have hx : 0 < x := by
    have hyR : (1 : ℝ) ≤ y := by exact_mod_cast hy
    exact lt_of_lt_of_le (sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hyR)) hxlower
  have hraw := norm_sigma3_le_sum_dyadic_coefficient_majorant_supported
    y y' M M x hx hM
  let C : ℝ := 4096 * (y : ℝ) ^ (27 / 28 : ℝ) *
    TypeIIScalar.scalarLog y ^ 4
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hsum :
      (∑ j ∈ Finset.range (TypeI.dyadicCount y'),
        ∑ k ∈ Finset.range (TypeI.dyadicCount y'),
          if blockActive y y' j k ∧ sigma3SupportActive M M j k then
            sigma3OrientedBlockMajorant x y y' M j k 0 else 0) ≤
        (TypeI.dyadicCount y' : ℝ) * TypeI.dyadicCount y' * C := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (TypeI.dyadicCount y'),
          ∑ _k ∈ Finset.range (TypeI.dyadicCount y'), C := by
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro k hk
        by_cases hact : blockActive y y' j k ∧ sigma3SupportActive M M j k
        · simp only [hact, if_pos]
          exact sigma3OrientedBlockMajorant_le_final hy hy' hM hM3 hyM hMlarge
            hact.1 hact.2 hxlower hxupper
        · simp only [hact, if_neg]
          exact hC
      _ = (TypeI.dyadicCount y' : ℝ) * TypeI.dyadicCount y' * C := by
        simp [mul_assoc]
  have hy'ne : y' ≠ 0 := by omega
  have hcount := dyadicCount_cast_le_three_scalarLog hy hy'ne
    (endpoint_le_256_mul_sq hy hy')
  have hcountProd :
      (TypeI.dyadicCount y' : ℝ) * TypeI.dyadicCount y' ≤
        9 * TypeIIScalar.scalarLog y ^ 2 := by
    calc
      (TypeI.dyadicCount y' : ℝ) * TypeI.dyadicCount y' ≤
          (3 * TypeIIScalar.scalarLog y) *
            (3 * TypeIIScalar.scalarLog y) := by
              exact mul_le_mul hcount hcount (by positivity)
                (by have := TypeIIScalar.scalarLog_one_le hy; positivity)
      _ = 9 * TypeIIScalar.scalarLog y ^ 2 := by ring
  calc
    ‖VaughanFourSums.sigma3 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M M‖ ≤ _ := hraw
    _ ≤ (TypeI.dyadicCount y' : ℝ) * TypeI.dyadicCount y' * C := hsum
    _ ≤ (9 * TypeIIScalar.scalarLog y ^ 2) * C :=
      mul_le_mul_of_nonneg_right hcountProd hC
    _ = 36864 * (y : ℝ) ^ (27 / 28 : ℝ) *
          TypeIIScalar.scalarLog y ^ 6 := by simp only [C]; ring

private lemma sqrt_scale_rpow_le_original
    {y n : ℕ} (hy : 1 ≤ y) (hysq : y ^ 2 ≤ n) :
    (y : ℝ) ^ (27 / 28 : ℝ) ≤ (n : ℝ) ^ (27 / 56 : ℝ) := by
  have hyR : 0 ≤ (y : ℝ) := by positivity
  calc
    (y : ℝ) ^ (27 / 28 : ℝ) =
        ((y : ℝ) ^ 2) ^ (27 / 56 : ℝ) := by
      rw [show (27 / 28 : ℝ) = 2 * (27 / 56) by norm_num,
        Real.rpow_mul hyR]
      norm_num [Real.rpow_natCast]
    _ ≤ (n : ℝ) ^ (27 / 56 : ℝ) := by
      apply Real.rpow_le_rpow (by positivity) (by exact_mod_cast hysq)
      norm_num

private lemma scalarLog_le_originalLog
    {y n : ℕ} (hy : 1 ≤ y) (hysq : y ^ 2 ≤ n) :
    TypeIIScalar.scalarLog y ≤ Real.log (256 * (n : ℝ)) := by
  unfold TypeIIScalar.scalarLog
  apply Real.log_le_log
  · positivity
  · exact_mod_cast Nat.mul_le_mul_left 256 hysq

/-- `Σ₂,₂` on the final `n^(27/56) log⁶` envelope. -/
theorem norm_sigma22_le_closed_original
    {x : ℝ} {n y y' M : ℕ}
    (hy : 1 ≤ y) (hyy' : y ≤ y') (hy' : y' ≤ 2 * y)
    (hM : 1 ≤ M) (hM3 : M ^ 3 ≤ y) (hyM : y ≤ 8 * M ^ 3)
    (hMlarge : 4608 ≤ M) (hysq : y ^ 2 ≤ n)
    (hxlower : (y : ℝ) ^ 2 ≤ x)
    (hxupper : x ≤ 12 * (y : ℝ) ^ 2) :
    ‖VaughanFourSums.sigma22 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M M‖ ≤
      18432 * (n : ℝ) ^ (27 / 56 : ℝ) *
        Real.log (256 * (n : ℝ)) ^ 6 := by
  have hraw := norm_sigma22_le_closed hy hyy' hy' hM hM3 hyM hMlarge
    hxlower hxupper
  have hp := sqrt_scale_rpow_le_original hy hysq
  have hlog := scalarLog_le_originalLog hy hysq
  have hlog0 : 0 ≤ TypeIIScalar.scalarLog y :=
    (TypeIIScalar.scalarLog_one_le hy).trans' (by norm_num)
  have hlogPow := pow_le_pow_left₀ hlog0 hlog 6
  calc
    ‖VaughanFourSums.sigma22 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M M‖ ≤
        18432 * (y : ℝ) ^ (27 / 28 : ℝ) *
          TypeIIScalar.scalarLog y ^ 6 := hraw
    _ ≤ 18432 * (n : ℝ) ^ (27 / 56 : ℝ) *
          TypeIIScalar.scalarLog y ^ 6 := by gcongr
    _ ≤ 18432 * (n : ℝ) ^ (27 / 56 : ℝ) *
          Real.log (256 * (n : ℝ)) ^ 6 := by gcongr

/-- `Σ₃` on the final `n^(27/56) log⁶` envelope. -/
theorem norm_sigma3_le_closed_original
    {x : ℝ} {n y y' M : ℕ}
    (hy : 1 ≤ y) (hyy' : y ≤ y') (hy' : y' ≤ 2 * y)
    (hM : 1 ≤ M) (hM3 : M ^ 3 ≤ y) (hyM : y ≤ 8 * M ^ 3)
    (hMlarge : 4608 ≤ M) (hysq : y ^ 2 ≤ n)
    (hxlower : (y : ℝ) ^ 2 ≤ x)
    (hxupper : x ≤ 12 * (y : ℝ) ^ 2) :
    ‖VaughanFourSums.sigma3 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M M‖ ≤
      36864 * (n : ℝ) ^ (27 / 56 : ℝ) *
        Real.log (256 * (n : ℝ)) ^ 6 := by
  have hraw := norm_sigma3_le_closed hy hyy' hy' hM hM3 hyM hMlarge
    hxlower hxupper
  have hp := sqrt_scale_rpow_le_original hy hysq
  have hlog := scalarLog_le_originalLog hy hysq
  have hlog0 : 0 ≤ TypeIIScalar.scalarLog y :=
    (TypeIIScalar.scalarLog_one_le hy).trans' (by norm_num)
  have hlogPow := pow_le_pow_left₀ hlog0 hlog 6
  calc
    ‖VaughanFourSums.sigma3 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M M‖ ≤
        36864 * (y : ℝ) ^ (27 / 28 : ℝ) *
          TypeIIScalar.scalarLog y ^ 6 := hraw
    _ ≤ 36864 * (n : ℝ) ^ (27 / 56 : ℝ) *
          TypeIIScalar.scalarLog y ^ 6 := by gcongr
    _ ≤ 36864 * (n : ℝ) ^ (27 / 56 : ℝ) *
          Real.log (256 * (n : ℝ)) ^ 6 := by gcongr

#print axioms orientedDyadicAnalyticFactor_zero_le_closed
#print axioms norm_sigma22_le_closed_original
#print axioms norm_sigma3_le_closed_original

end Erdos175.TypeIIGlobal
