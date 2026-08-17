/- leanprover/lean4:v4.33.0 -/

import ErdosProblems.Erdos175.VaughanTypeIIDyadic

/-!
# Explicit coefficient majorants for the dyadic Vaughan Type-II sums

This file removes the coefficient norms from the oriented active-block
estimates.  What remains in each block is the explicit near--far analytic
factor multiplied by square roots of the concrete `a`, `b`, von Mangoldt,
and constant-sequence mass bounds.
-/

noncomputable section

namespace Erdos175.VaughanTypeIICoefficients

open scoped BigOperators

open VaughanTypeIIDyadic

/-- The square-root term in the dyadic near--far estimate, separated from
the two coefficient norms. -/
noncomputable def dyadicAnalyticFactor
    (x : ℝ) (y y' j k T : ℕ) : ℝ :=
  Real.sqrt
    (2 * (2 ^ j : ℕ) * (2 * T + 1) +
      TypeII.threeBranchFarQ x y y'
        (2 ^ j - 1) (2 ^ (j + 1) - 1)
        (2 ^ k - 1) (2 ^ (k + 1) - 1) T * (2 ^ k : ℕ))

theorem dyadicNearFarFactor_eq
    (x : ℝ) (y y' j k T : ℕ) (alpha beta : ℕ → ℂ) :
    dyadicNearFarFactor x y y' j k T alpha beta =
      TypeII.l2Norm (TypeI.dyadicBlock j) alpha *
        dyadicAnalyticFactor x y y' j k T *
          TypeII.l2Norm (TypeI.dyadicBlock k) beta := rfl

/-- A nonnegative quantity whose square is at most `C` is at most
`sqrt C`. -/
lemma le_sqrt_of_nonneg_of_sq_le {a C : ℝ}
    (_ha : 0 ≤ a) (h : a ^ 2 ≤ C) : a ≤ Real.sqrt C := by
  have hC : 0 ≤ C := (sq_nonneg a).trans h
  have hsqrt := Real.sq_sqrt hC
  have hsqrt0 := Real.sqrt_nonneg C
  nlinarith

lemma l2Norm_nonneg (s : Finset ℕ) (a : ℕ → ℂ) :
    0 ≤ TypeII.l2Norm s a := by
  unfold TypeII.l2Norm
  exact Real.sqrt_nonneg _

/-- The masked constant-one sequence has squared mass at most the size of
the full dyadic block. -/
theorem l2Norm_restrict_one_dyadicBlock_sq_le
    (support : Finset ℕ) (j : ℕ) :
    TypeII.l2Norm (TypeI.dyadicBlock j)
        (restrictCoeff support (fun _ => (1 : ℂ))) ^ 2 ≤
      (2 ^ j : ℕ) := by
  rw [TypeII.l2Norm_sq]
  calc
    (∑ n ∈ TypeI.dyadicBlock j,
        ‖restrictCoeff support (fun _ => (1 : ℂ)) n‖ ^ 2) ≤
        ∑ _n ∈ TypeI.dyadicBlock j, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hns : n ∈ support
      · simp [restrictCoeff, hns]
      · simp [restrictCoeff, hns]
    _ = (2 ^ j : ℕ) := by
      simp [TypeI.card_dyadicBlock]

/-- Square-root form of the masked `b`-coefficient mass estimate. -/
theorem l2Norm_restrict_bCoeff_dyadicBlock_le
    (support : Finset ℕ) (M K j : ℕ) :
    TypeII.l2Norm (TypeI.dyadicBlock j)
        (restrictCoeff support
          (fun r => ((VaughanFourSums.bCoeff M K r : ℝ) : ℂ))) ≤
      Real.sqrt
        ((2 ^ j : ℕ) * Real.log (2 * (2 ^ j : ℕ)) ^ 2) := by
  apply le_sqrt_of_nonneg_of_sq_le
  · exact l2Norm_nonneg _ _
  · exact l2Norm_restrict_bCoeff_dyadicBlock_sq_le support M K j

/-- Square-root form of the shifted `a`-coefficient mass estimate. -/
theorem l2Norm_restrict_aCoeff_dyadicBlock_le
    (support : Finset ℕ) (M j : ℕ) (hM : 1 ≤ M) :
    TypeII.l2Norm (TypeI.dyadicBlock j)
        (restrictCoeff support
          (fun n => ((VaughanFourSums.aCoeff M n : ℝ) : ℂ))) ≤
      Real.sqrt
        ((8 / 9 : ℝ) * (2 ^ j : ℕ) *
          (Real.log M + 3) ^ 3 + 1) := by
  apply le_sqrt_of_nonneg_of_sq_le
  · exact l2Norm_nonneg _ _
  · exact l2Norm_restrict_aCoeff_dyadicBlock_sq_le support M j hM

/-- Square-root form of the masked von Mangoldt mass estimate. -/
theorem l2Norm_restrict_vonMangoldt_dyadicBlock_le
    (support : Finset ℕ) (j : ℕ) :
    TypeII.l2Norm (TypeI.dyadicBlock j)
        (restrictCoeff support
          (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))) ≤
      Real.sqrt
        ((2 ^ j : ℕ) * Real.log (2 * (2 ^ j : ℕ)) ^ 2) := by
  apply le_sqrt_of_nonneg_of_sq_le
  · exact l2Norm_nonneg _ _
  · exact l2Norm_restrict_vonMangoldt_dyadicBlock_sq_le support j

/-- Square-root form of the masked constant-one mass estimate. -/
theorem l2Norm_restrict_one_dyadicBlock_le
    (support : Finset ℕ) (j : ℕ) :
    TypeII.l2Norm (TypeI.dyadicBlock j)
        (restrictCoeff support (fun _ => (1 : ℂ))) ≤
      Real.sqrt (2 ^ j : ℕ) := by
  apply le_sqrt_of_nonneg_of_sq_le
  · exact l2Norm_nonneg _ _
  · exact l2Norm_restrict_one_dyadicBlock_sq_le support j

/-- Replace both coefficient norms in the oriented near--far factor by
arbitrary proved squared-mass bounds. -/
theorem orientedDyadicNearFarFactor_le_of_l2_sq
    (x : ℝ) (y y' j k T : ℕ) (alpha beta : ℕ → ℂ) (A B : ℝ)
    (hA : TypeII.l2Norm (TypeI.dyadicBlock j) alpha ^ 2 ≤ A)
    (hB : TypeII.l2Norm (TypeI.dyadicBlock k) beta ^ 2 ≤ B) :
    orientedDyadicNearFarFactorAt x y y' j k T alpha beta ≤
      if j < k then
        Real.sqrt B * dyadicAnalyticFactor x y y' k j T * Real.sqrt A
      else
        Real.sqrt A * dyadicAnalyticFactor x y y' j k T * Real.sqrt B := by
  have hAlpha : TypeII.l2Norm (TypeI.dyadicBlock j) alpha ≤ Real.sqrt A :=
    le_sqrt_of_nonneg_of_sq_le (l2Norm_nonneg _ _) hA
  have hBeta : TypeII.l2Norm (TypeI.dyadicBlock k) beta ≤ Real.sqrt B :=
    le_sqrt_of_nonneg_of_sq_le (l2Norm_nonneg _ _) hB
  by_cases hjk : j < k
  · simp only [orientedDyadicNearFarFactorAt, hjk, if_pos,
      dyadicNearFarFactor_eq]
    have hroot : 0 ≤ dyadicAnalyticFactor x y y' k j T := by
      unfold dyadicAnalyticFactor
      positivity
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right hBeta hroot) hAlpha
      (l2Norm_nonneg _ _) (mul_nonneg (Real.sqrt_nonneg _) hroot)
  · simp only [orientedDyadicNearFarFactorAt, hjk,
      dyadicNearFarFactor_eq]
    have hroot : 0 ≤ dyadicAnalyticFactor x y y' j k T := by
      unfold dyadicAnalyticFactor
      positivity
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right hAlpha hroot) hBeta
      (l2Norm_nonneg _ _) (mul_nonneg (Real.sqrt_nonneg _) hroot)

/-- The explicit coefficient-replaced block majorant for `Σ₂,₂`. -/
noncomputable def sigma22OrientedBlockMajorant
    (x : ℝ) (y y' j k T : ℕ) : ℝ :=
  let bMass := (2 ^ j : ℕ) * Real.log (2 * (2 ^ j : ℕ)) ^ 2
  let oneMass : ℝ := (2 ^ k : ℕ)
  if j < k then
    Real.sqrt oneMass * dyadicAnalyticFactor x y y' k j T *
      Real.sqrt bMass
  else
    Real.sqrt bMass * dyadicAnalyticFactor x y y' j k T *
      Real.sqrt oneMass

/-- The explicit coefficient-replaced block majorant for `Σ₃`. -/
noncomputable def sigma3OrientedBlockMajorant
    (x : ℝ) (y y' M j k T : ℕ) : ℝ :=
  let aMass :=
    (8 / 9 : ℝ) * (2 ^ j : ℕ) * (Real.log M + 3) ^ 3 + 1
  let lambdaMass :=
    (2 ^ k : ℕ) * Real.log (2 * (2 ^ k : ℕ)) ^ 2
  if j < k then
    Real.sqrt lambdaMass * dyadicAnalyticFactor x y y' k j T *
      Real.sqrt aMass
  else
    Real.sqrt aMass * dyadicAnalyticFactor x y y' j k T *
      Real.sqrt lambdaMass

theorem sigma22_orientedFactor_le_majorant
    (y y' M K j k T : ℕ) (x : ℝ) :
    orientedDyadicNearFarFactorAt x y y' j k T
        (restrictCoeff (Finset.Ioc M (M * K))
          (fun r => (VaughanFourSums.bCoeff M K r : ℂ)))
        (restrictCoeff (Finset.Icc 1 y') (fun _ => 1)) ≤
      sigma22OrientedBlockMajorant x y y' j k T := by
  simpa only [sigma22OrientedBlockMajorant] using
    orientedDyadicNearFarFactor_le_of_l2_sq x y y' j k T _ _
      ((2 ^ j : ℕ) * Real.log (2 * (2 ^ j : ℕ)) ^ 2)
      (2 ^ k : ℕ)
      (l2Norm_restrict_bCoeff_dyadicBlock_sq_le
        (Finset.Ioc M (M * K)) M K j)
      (l2Norm_restrict_one_dyadicBlock_sq_le (Finset.Icc 1 y') k)

theorem sigma3_orientedFactor_le_majorant
    (y y' M K j k T : ℕ) (x : ℝ) (hM : 1 ≤ M) :
    orientedDyadicNearFarFactorAt x y y' j k T
        (restrictCoeff (Finset.Ioc M y')
          (fun l => (VaughanFourSums.aCoeff M l : ℂ)))
        (restrictCoeff (Finset.Ioc K y')
          (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))) ≤
      sigma3OrientedBlockMajorant x y y' M j k T := by
  simpa only [sigma3OrientedBlockMajorant] using
    orientedDyadicNearFarFactor_le_of_l2_sq x y y' j k T _ _
      ((8 / 9 : ℝ) * (2 ^ j : ℕ) * (Real.log M + 3) ^ 3 + 1)
      ((2 ^ k : ℕ) * Real.log (2 * (2 ^ k : ℕ)) ^ 2)
      (l2Norm_restrict_aCoeff_dyadicBlock_sq_le
        (Finset.Ioc M y') M j hM)
      (l2Norm_restrict_vonMangoldt_dyadicBlock_sq_le
        (Finset.Ioc K y') k)

/-- Actual `Σ₂,₂`, with all coefficient norms replaced by explicit
square-root expressions and inactive rectangles erased. -/
theorem norm_sigma22_le_sum_dyadic_coefficient_majorant
    (y y' M K : ℕ) (x : ℝ) (threshold : ℕ → ℕ → ℕ) (hx : 0 < x) :
    ‖VaughanFourSums.sigma22 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M K‖ ≤
      ∑ j ∈ Finset.range (TypeI.dyadicCount (M * K)),
        ∑ k ∈ Finset.range (TypeI.dyadicCount y'),
          if blockActive y y' j k then
            sigma22OrientedBlockMajorant x y y' j k (threshold j k)
          else 0 := by
  refine (norm_sigma22_le_sum_dyadic_oriented_active_at
    y y' M K x threshold hx).trans ?_
  apply Finset.sum_le_sum
  intro j hj
  apply Finset.sum_le_sum
  intro k hk
  by_cases hactive : blockActive y y' j k
  · simp only [hactive, if_pos]
    exact sigma22_orientedFactor_le_majorant
      y y' M K j k (threshold j k) x
  · simp [hactive]

/-- Actual `Σ₃`, with all coefficient norms replaced by explicit
square-root expressions and inactive rectangles erased. -/
theorem norm_sigma3_le_sum_dyadic_coefficient_majorant
    (y y' M K : ℕ) (x : ℝ) (threshold : ℕ → ℕ → ℕ)
    (hx : 0 < x) (hM : 1 ≤ M) :
    ‖VaughanFourSums.sigma3 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M K‖ ≤
      ∑ j ∈ Finset.range (TypeI.dyadicCount y'),
        ∑ k ∈ Finset.range (TypeI.dyadicCount y'),
          if blockActive y y' j k then
            sigma3OrientedBlockMajorant x y y' M j k (threshold j k)
          else 0 := by
  refine (norm_sigma3_le_sum_dyadic_oriented_active_at
    y y' M K x threshold hx).trans ?_
  apply Finset.sum_le_sum
  intro j hj
  apply Finset.sum_le_sum
  intro k hk
  by_cases hactive : blockActive y y' j k
  · simp only [hactive, if_pos]
    exact sigma3_orientedFactor_le_majorant
      y y' M K j k (threshold j k) x hM
  · simp [hactive]

/-! ## Support-sensitive coefficient majorants

The coarse coefficient estimates above remain positive even when a power
block misses the original Vaughan support.  Keeping this elementary support
information is essential in the quantitative Type-II application: it gives
a lower bound for the smaller of the two oriented block scales. -/

/-- A reciprocal bilinear block vanishes when its first coefficient is zero
on the first support. -/
theorem reciprocalBilinearSum_eq_zero_of_left
    (I us vs : Finset ℕ) (x : ℝ) (alpha beta : ℕ → ℂ)
    (hzero : ∀ u ∈ us, alpha u = 0) :
    TypeII.reciprocalBilinearSum I us vs x alpha beta = 0 := by
  unfold TypeII.reciprocalBilinearSum TypeII.bilinearSum
  apply Finset.sum_eq_zero
  intro u hu
  rw [hzero u hu, zero_mul]

/-- A reciprocal bilinear block vanishes when its second coefficient is zero
on the second support. -/
theorem reciprocalBilinearSum_eq_zero_of_right
    (I us vs : Finset ℕ) (x : ℝ) (alpha beta : ℕ → ℂ)
    (hzero : ∀ v ∈ vs, beta v = 0) :
    TypeII.reciprocalBilinearSum I us vs x alpha beta = 0 := by
  unfold TypeII.reciprocalBilinearSum TypeII.bilinearSum TypeII.innerSum
  apply Finset.sum_eq_zero
  intro u hu
  rw [show (∑ v ∈ vs,
      beta v * TypeII.restrictedReciprocalKernel I x u v) = 0 by
    apply Finset.sum_eq_zero
    intro v hv
    rw [hzero v hv, zero_mul]]
  simp

/-- A block below the lower endpoint of an `Ioc` coefficient support carries
only zero restricted coefficients. -/
theorem restrictCoeff_Ioc_eq_zero_on_dyadicBlock_of_upper_le
    (L R j : ℕ) (a : ℕ → ℂ) (hupper : 2 ^ (j + 1) ≤ L) :
    ∀ n ∈ TypeI.dyadicBlock j,
      restrictCoeff (Finset.Ioc L R) a n = 0 := by
  intro n hn
  apply restrictCoeff_of_not_mem
  have hnlt := (TypeI.mem_dyadicBlock.mp hn).2
  simp only [Finset.mem_Ioc, not_and_or]
  left
  omega

/-- `Σ₂,₂` block support: the `b`-coefficient block must reach above
the strict lower endpoint `M`. -/
def sigma22SupportActive (M j : ℕ) : Prop := M < 2 ^ (j + 1)

instance sigma22SupportActiveDecidable (M j : ℕ) :
    Decidable (sigma22SupportActive M j) := by
  unfold sigma22SupportActive
  infer_instance

/-- `Σ₃` block support: both coefficient blocks must reach above their
strict lower endpoints. -/
def sigma3SupportActive (M K j k : ℕ) : Prop :=
  M < 2 ^ (j + 1) ∧ K < 2 ^ (k + 1)

instance sigma3SupportActiveDecidable (M K j k : ℕ) :
    Decidable (sigma3SupportActive M K j k) := by
  unfold sigma3SupportActive
  infer_instance

/-- Larger power scale after orienting a dyadic rectangle. -/
def orientedLargeScale (j k : ℕ) : ℕ :=
  if j < k then 2 ^ k else 2 ^ j

/-- Smaller power scale after orienting a dyadic rectangle. -/
def orientedSmallScale (j k : ℕ) : ℕ :=
  if j < k then 2 ^ j else 2 ^ k

@[simp] theorem orientedLargeScale_mul_orientedSmallScale (j k : ℕ) :
    orientedLargeScale j k * orientedSmallScale j k = 2 ^ j * 2 ^ k := by
  by_cases hjk : j < k <;>
    simp [orientedLargeScale, orientedSmallScale, hjk, Nat.mul_comm]

theorem orientedSmallScale_le_orientedLargeScale (j k : ℕ) :
    orientedSmallScale j k ≤ orientedLargeScale j k := by
  by_cases hjk : j < k
  · simp only [orientedSmallScale, orientedLargeScale, hjk, if_pos]
    exact Nat.pow_le_pow_right (by norm_num) hjk.le
  · simp only [orientedSmallScale, orientedLargeScale, hjk, if_neg]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_gt hjk)

@[simp] theorem orientedLargeScale_pos (j k : ℕ) :
    0 < orientedLargeScale j k := by
  by_cases hjk : j < k <;>
    simp [orientedLargeScale, hjk, pow_pos]

@[simp] theorem orientedSmallScale_pos (j k : ℕ) :
    0 < orientedSmallScale j k := by
  by_cases hjk : j < k <;>
    simp [orientedSmallScale, hjk, pow_pos]

/-- Every dyadic block index used to cover a nonempty initial interval has
lower endpoint at most that interval's endpoint. -/
theorem two_pow_le_of_mem_range_dyadicCount
    {N j : ℕ} (hN : N ≠ 0)
    (hj : j ∈ Finset.range (TypeI.dyadicCount N)) :
    2 ^ j ≤ N := by
  have hjlog : j ≤ Nat.log 2 N := by
    have hj' : j < Nat.log 2 N + 1 := by
      simpa only [Finset.mem_range, TypeI.dyadicCount] using hj
    omega
  exact (Nat.pow_le_pow_right (by norm_num) hjlog).trans
    (Nat.pow_log_le_self 2 hN)

/-- On a support-active `Σ₃` block, the smaller oriented scale reaches
half of any common lower bound for `M` and `K`. -/
theorem sigma3SupportActive_lt_two_mul_orientedSmallScale
    {L M K j k : ℕ} (hLM : L ≤ M) (hLK : L ≤ K)
    (hs : sigma3SupportActive M K j k) :
    L < 2 * orientedSmallScale j k := by
  rcases hs with ⟨hsj, hsk⟩
  by_cases hjk : j < k
  · simpa [orientedSmallScale, hjk, pow_succ, Nat.mul_comm] using
      hLM.trans_lt hsj
  · simpa [orientedSmallScale, hjk, pow_succ, Nat.mul_comm] using
      hLK.trans_lt hsk

/-- For `Σ₂,₂`, either the smaller oriented scale is the supported
`b` block and is at least `M/2`, or product activity and the upper support
`M*K` give the alternative lower-scale inequality. -/
theorem sigma22SupportActive_or_product_lt_small
    {y y' M K j k : ℕ} (hMK : M * K ≠ 0)
    (hj : j ∈ Finset.range (TypeI.dyadicCount (M * K)))
    (hactive : blockActive y y' j k)
    (hs : sigma22SupportActive M j) :
    M < 2 * orientedSmallScale j k ∨
      y < 4 * (M * K) * orientedSmallScale j k := by
  by_cases hjk : j < k
  · left
    simpa [sigma22SupportActive, orientedSmallScale, hjk, pow_succ,
      Nat.mul_comm] using hs
  · right
    have hjupper : 2 ^ j ≤ M * K :=
      two_pow_le_of_mem_range_dyadicCount hMK hj
    have hprod := blockActive_y_lt_four_mul_lower_product hactive
    simp only [orientedSmallScale, hjk, if_neg]
    calc
      y < 4 * (2 ^ j * 2 ^ k) := hprod
      _ ≤ 4 * ((M * K) * 2 ^ k) :=
        Nat.mul_le_mul_left 4 (Nat.mul_le_mul_right (2 ^ k) hjupper)
      _ = 4 * (M * K) * 2 ^ k := by ring

/-- Product activity, orientation, and a large first scale imply the simple
upper-frequency hypothesis needed by the closed far-correlation estimate.
The generous cutoff `2304` keeps this entirely polynomial. -/
theorem honeScale_of_active_oriented
    {x : ℝ} {y U V : ℕ}
    (hxupper : x ≤ 12 * (y : ℝ) ^ 2)
    (hU : 2304 ≤ U) (hV : 0 < V) (hVU : V ≤ U)
    (hproduct : y < 4 * (U * V)) :
    12 * (x / (V : ℝ)) ≤ (U : ℝ) ^ 4 := by
  have hVreal : 0 < (V : ℝ) := by exact_mod_cast hV
  have hproductR : (y : ℝ) ≤ 4 * (U : ℝ) * V := by
    have hproductR' : (y : ℝ) ≤ ((4 * (U * V) : ℕ) : ℝ) := by
      exact_mod_cast hproduct.le
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hproductR'
    simpa only [mul_assoc] using hproductR'
  have hUreal : (2304 : ℝ) ≤ U := by exact_mod_cast hU
  have hVUreal : (V : ℝ) ≤ U := by exact_mod_cast hVU
  have hyU : (y : ℝ) ≤ 4 * (U : ℝ) ^ 2 := by
    calc
      (y : ℝ) ≤ 4 * (U : ℝ) * V := hproductR
      _ ≤ 4 * (U : ℝ) * U := by gcongr
      _ = 4 * (U : ℝ) ^ 2 := by ring
  have hU3 : 576 * (y : ℝ) ≤ (U : ℝ) ^ 3 := by
    calc
      576 * (y : ℝ) ≤ 576 * (4 * (U : ℝ) ^ 2) := by gcongr
      _ = 2304 * (U : ℝ) ^ 2 := by ring
      _ ≤ (U : ℝ) * (U : ℝ) ^ 2 := by gcongr
      _ = (U : ℝ) ^ 3 := by ring
  have hy2 : 144 * (y : ℝ) ^ 2 ≤
      (U : ℝ) ^ 4 * V := by
    have hmulProduct :
        0 ≤ (y : ℝ) * (4 * (U : ℝ) * V - (y : ℝ)) :=
      mul_nonneg (Nat.cast_nonneg y) (sub_nonneg.mpr hproductR)
    have hfirst : 144 * (y : ℝ) ^ 2 ≤
        144 * (y : ℝ) * (4 * (U : ℝ) * V) := by
      nlinarith
    have hsecond : (576 * (y : ℝ)) * ((U : ℝ) * V) ≤
        (U : ℝ) ^ 3 * ((U : ℝ) * V) :=
      mul_le_mul_of_nonneg_right hU3 (by positivity)
    calc
      144 * (y : ℝ) ^ 2 ≤
          144 * (y : ℝ) * (4 * (U : ℝ) * V) := hfirst
      _ = (576 * (y : ℝ)) * ((U : ℝ) * V) := by ring
      _ ≤ (U : ℝ) ^ 3 * ((U : ℝ) * V) := hsecond
      _ = (U : ℝ) ^ 4 * V := by ring
  have hxscaled : 12 * x ≤ (U : ℝ) ^ 4 * V := by
    calc
      12 * x ≤ 144 * (y : ℝ) ^ 2 := by nlinarith
      _ ≤ (U : ℝ) ^ 4 * V := hy2
  rw [show 12 * (x / (V : ℝ)) = (12 * x) / V by ring,
    div_le_iff₀ hVreal]
  simpa [mul_comm] using hxscaled

/-- Replace the finite far-pair maximum in the zero-threshold analytic
factor by the closed oriented power-block expression. -/
theorem dyadicAnalyticFactor_zero_le_orientedPowerBlockFarQ
    (x : ℝ) (y y' j k : ℕ) (hx : 0 < x)
    (hhoneScale :
      12 * (x / ((2 ^ k : ℕ) : ℝ)) ≤ (((2 ^ j : ℕ) : ℝ)) ^ 4) :
    dyadicAnalyticFactor x y y' j k 0 ≤
      Real.sqrt
        (2 * ((2 ^ j : ℕ) : ℝ) +
          TypeII.orientedPowerBlockFarQ x (2 ^ j) (2 ^ k) *
            ((2 ^ k : ℕ) : ℝ)) := by
  have hQ := TypeII.threeBranchFarQ_powerBlock_zero_le
    x y y' (2 ^ j) (2 ^ k) hx
      (pow_pos (by norm_num) j) (pow_pos (by norm_num) k) hhoneScale
  unfold dyadicAnalyticFactor
  apply Real.sqrt_le_sqrt
  norm_num only [Nat.cast_pow, Nat.cast_ofNat, mul_one]
  have hk0 : 0 ≤ (((2 ^ k : ℕ) : ℝ)) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hQ hk0
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hmul
  simpa only [pow_succ, Nat.mul_comm, add_comm] using
    add_le_add_left hmul (2 * (2 : ℝ) ^ j)

/-- Sharp form of the common-support scale calculation used after the
power-of-two Vaughan specialization. -/
theorem orientedLargeScale_cube_le_of_common_lower
    {c y y' M U V : ℕ} (hy : 0 < y) (hy' : y' ≤ 2 * y)
    (hyM : y ≤ c * M ^ 3) (hsmall : M ≤ 2 * V)
    (hUV : U * V ≤ y') :
    U ^ 3 ≤ (64 * c) * y ^ 2 := by
  have hMU : M * U ≤ 4 * y := by
    calc
      M * U ≤ (2 * V) * U := Nat.mul_le_mul_right U hsmall
      _ = 2 * (U * V) := by ring
      _ ≤ 2 * y' := Nat.mul_le_mul_left 2 hUV
      _ ≤ 4 * y := by omega
  have hcube := Nat.pow_le_pow_left hMU 3
  have hMUcube : M ^ 3 * U ^ 3 ≤ 64 * y ^ 3 := by
    calc
      M ^ 3 * U ^ 3 = (M * U) ^ 3 := by ring
      _ ≤ (4 * y) ^ 3 := hcube
      _ = 64 * y ^ 3 := by ring
  have hscaled : y * U ^ 3 ≤ y * ((64 * c) * y ^ 2) := by
    calc
      y * U ^ 3 ≤ (c * M ^ 3) * U ^ 3 :=
        Nat.mul_le_mul_right (U ^ 3) hyM
      _ = c * (M ^ 3 * U ^ 3) := by ring
      _ ≤ c * (64 * y ^ 3) := Nat.mul_le_mul_left c hMUcube
      _ = y * ((64 * c) * y ^ 2) := by ring
  exact Nat.le_of_mul_le_mul_left hscaled hy

/-- With `y ≤ 8 M³`, every support-active `Σ₃` block has the exact
cube bound consumed by `TypeIIScalar`. -/
theorem sigma3_orientedLargeScale_cube_le_512
    {y y' M j k : ℕ} (hy : 0 < y) (hy' : y' ≤ 2 * y)
    (hyM : y ≤ 8 * M ^ 3)
    (hactive : blockActive y y' j k)
    (hs : sigma3SupportActive M M j k) :
    orientedLargeScale j k ^ 3 ≤ 512 * y ^ 2 := by
  apply orientedLargeScale_cube_le_of_common_lower
    (c := 8) hy hy' hyM
  · exact (sigma3SupportActive_lt_two_mul_orientedSmallScale
      (L := M) (M := M) (K := M) (j := j) (k := k)
      le_rfl le_rfl hs).le
  · rw [orientedLargeScale_mul_orientedSmallScale]
    exact blockActive_lower_product_le hactive

/-- The analogous exact cube bound for support-active `Σ₂,₂`
blocks. -/
theorem sigma22_orientedLargeScale_cube_le_512
    {y y' M j k : ℕ} (hy : 0 < y) (hy' : y' ≤ 2 * y)
    (hylow : M ^ 3 ≤ y) (hyM : y ≤ 8 * M ^ 3)
    (hj : j ∈ Finset.range (TypeI.dyadicCount (M * M)))
    (hactive : blockActive y y' j k)
    (hs : sigma22SupportActive M j) :
    orientedLargeScale j k ^ 3 ≤ 512 * y ^ 2 := by
  by_cases hjk : j < k
  · apply orientedLargeScale_cube_le_of_common_lower
      (c := 8) (M := M) (U := orientedLargeScale j k)
        (V := orientedSmallScale j k) hy hy' hyM
    · simpa [sigma22SupportActive, orientedSmallScale, hjk, pow_succ,
        Nat.mul_comm] using hs.le
    · rw [orientedLargeScale_mul_orientedSmallScale]
      exact blockActive_lower_product_le hactive
  · have hM : 0 < M := by
      by_contra hnot
      have : M = 0 := Nat.eq_zero_of_not_pos hnot
      subst M
      simp at hyM
      omega
    have hMM : M * M ≠ 0 := mul_ne_zero hM.ne' hM.ne'
    have hU : orientedLargeScale j k ≤ M ^ 2 := by
      simp only [orientedLargeScale, hjk, if_neg]
      simpa [pow_two] using
        two_pow_le_of_mem_range_dyadicCount hMM hj
    have hcube := Nat.pow_le_pow_left hU 3
    calc
      orientedLargeScale j k ^ 3 ≤ (M ^ 2) ^ 3 := hcube
      _ = (M ^ 3) ^ 2 := by ring
      _ ≤ y ^ 2 := Nat.pow_le_pow_left hylow 2
      _ ≤ 512 * y ^ 2 := by nlinarith

/-- Actual `Σ₂,₂` with both product activity and the original
`b`-coefficient support retained in the explicit majorant. -/
theorem norm_sigma22_le_sum_dyadic_coefficient_majorant_supported
    (y y' M K : ℕ) (x : ℝ) (hx : 0 < x) :
    ‖VaughanFourSums.sigma22 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M K‖ ≤
      ∑ j ∈ Finset.range (TypeI.dyadicCount (M * K)),
        ∑ k ∈ Finset.range (TypeI.dyadicCount y'),
          if blockActive y y' j k ∧ sigma22SupportActive M j then
            sigma22OrientedBlockMajorant x y y' j k 0
          else 0 := by
  apply norm_sigma22_le_sum_dyadic_of_block
  intro j hj k hk
  by_cases hactive : blockActive y y' j k
  · by_cases hs : sigma22SupportActive M j
    · simp only [hactive, hs, and_self, if_pos]
      exact (norm_reciprocalBilinearSum_dyadic_le_oriented_active_at
        x y y' j k 0 _ _ hx).trans (by
          simp only [hactive, if_pos]
          exact sigma22_orientedFactor_le_majorant y y' M K j k 0 x)
    · have hupper : 2 ^ (j + 1) ≤ M := by
        exact Nat.le_of_not_gt hs
      have hzero := restrictCoeff_Ioc_eq_zero_on_dyadicBlock_of_upper_le
        M (M * K) j
          (fun r => (VaughanFourSums.bCoeff M K r : ℂ)) hupper
      rw [reciprocalBilinearSum_eq_zero_of_left _ _ _ _ _ _ hzero,
        norm_zero]
      simp [hs]
  · rw [VaughanTypeIIDyadic.reciprocalBilinearSum_dyadic_eq_zero_of_not_blockActive
      y y' j k x _ _ hactive, norm_zero]
    simp [hactive]

/-- Actual `Σ₃` with both original strict lower coefficient supports
retained in the explicit majorant. -/
theorem norm_sigma3_le_sum_dyadic_coefficient_majorant_supported
    (y y' M K : ℕ) (x : ℝ) (hx : 0 < x) (hM : 1 ≤ M) :
    ‖VaughanFourSums.sigma3 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M K‖ ≤
      ∑ j ∈ Finset.range (TypeI.dyadicCount y'),
        ∑ k ∈ Finset.range (TypeI.dyadicCount y'),
          if blockActive y y' j k ∧ sigma3SupportActive M K j k then
            sigma3OrientedBlockMajorant x y y' M j k 0
          else 0 := by
  apply norm_sigma3_le_sum_dyadic_of_block
  intro j hj k hk
  by_cases hactive : blockActive y y' j k
  · by_cases hs : sigma3SupportActive M K j k
    · simp only [hactive, hs, and_self, if_pos]
      exact (norm_reciprocalBilinearSum_dyadic_le_oriented_active_at
        x y y' j k 0 _ _ hx).trans (by
          simp only [hactive, if_pos]
          exact sigma3_orientedFactor_le_majorant y y' M K j k 0 x hM)
    · rcases not_and_or.mp hs with hsj | hsk
      · have hupper : 2 ^ (j + 1) ≤ M := Nat.le_of_not_gt hsj
        have hzero := restrictCoeff_Ioc_eq_zero_on_dyadicBlock_of_upper_le
          M y' j (fun l => (VaughanFourSums.aCoeff M l : ℂ)) hupper
        rw [reciprocalBilinearSum_eq_zero_of_left _ _ _ _ _ _ hzero,
          norm_zero]
        simp [hs]
      · have hupper : 2 ^ (k + 1) ≤ K := Nat.le_of_not_gt hsk
        have hzero := restrictCoeff_Ioc_eq_zero_on_dyadicBlock_of_upper_le
          K y' k
            (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) hupper
        rw [reciprocalBilinearSum_eq_zero_of_right _ _ _ _ _ _ hzero,
          norm_zero]
        simp [hs]
  · rw [VaughanTypeIIDyadic.reciprocalBilinearSum_dyadic_eq_zero_of_not_blockActive
      y y' j k x _ _ hactive, norm_zero]
    simp [hactive]

/-- Canonically thresholded coefficient majorant for the actual `Σ₂,₂`. -/
theorem norm_sigma22_le_sum_dyadic_coefficient_majorant_threeQuarter
    (y y' M K : ℕ) (x : ℝ) (hx : 0 < x) :
    ‖VaughanFourSums.sigma22 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M K‖ ≤
      ∑ j ∈ Finset.range (TypeI.dyadicCount (M * K)),
        ∑ k ∈ Finset.range (TypeI.dyadicCount y'),
          if blockActive y y' j k then
            sigma22OrientedBlockMajorant x y y' j k
              (threeQuarterThreshold j k)
          else 0 := by
  exact norm_sigma22_le_sum_dyadic_coefficient_majorant
    y y' M K x threeQuarterThreshold hx

/-- Canonically thresholded coefficient majorant for the actual `Σ₃`. -/
theorem norm_sigma3_le_sum_dyadic_coefficient_majorant_threeQuarter
    (y y' M K : ℕ) (x : ℝ) (hx : 0 < x) (hM : 1 ≤ M) :
    ‖VaughanFourSums.sigma3 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M K‖ ≤
      ∑ j ∈ Finset.range (TypeI.dyadicCount y'),
        ∑ k ∈ Finset.range (TypeI.dyadicCount y'),
          if blockActive y y' j k then
            sigma3OrientedBlockMajorant x y y' M j k
              (threeQuarterThreshold j k)
          else 0 := by
  exact norm_sigma3_le_sum_dyadic_coefficient_majorant
    y y' M K x threeQuarterThreshold hx hM

/-- The number of active second blocks in any finite range is bounded by
the length of that range. -/
theorem card_filter_blockActive_le
    (y y' j K : ℕ) :
    ((Finset.range K).filter fun k => blockActive y y' j k).card ≤ K := by
  simpa using Finset.card_le_card
    (Finset.filter_subset (fun k => blockActive y y' j k) (Finset.range K))

/-- Collapse a finite active-block double sum once a uniform block
majorant has been proved. -/
theorem sum_active_blocks_le_dyadic_counts_mul
    (y y' J K : ℕ) (F : ℕ → ℕ → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hF : ∀ j ∈ Finset.range J, ∀ k ∈ Finset.range K,
      blockActive y y' j k → F j k ≤ C) :
    (∑ j ∈ Finset.range J, ∑ k ∈ Finset.range K,
        if blockActive y y' j k then F j k else 0) ≤
      (J : ℝ) * K * C := by
  calc
    (∑ j ∈ Finset.range J, ∑ k ∈ Finset.range K,
        if blockActive y y' j k then F j k else 0) ≤
        ∑ _j ∈ Finset.range J, ∑ _k ∈ Finset.range K, C := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro k hk
      by_cases hactive : blockActive y y' j k
      · simpa only [hactive, if_pos] using hF j hj k hk hactive
      · simp only [hactive]
        exact hC
    _ = (J : ℝ) * K * C := by
      simp [mul_assoc]

#print axioms norm_sigma22_le_sum_dyadic_coefficient_majorant
#print axioms norm_sigma3_le_sum_dyadic_coefficient_majorant
#print axioms norm_sigma22_le_sum_dyadic_coefficient_majorant_threeQuarter
#print axioms norm_sigma3_le_sum_dyadic_coefficient_majorant_threeQuarter

end Erdos175.VaughanTypeIICoefficients
