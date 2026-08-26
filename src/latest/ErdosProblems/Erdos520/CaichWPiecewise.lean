import ErdosProblems.Erdos520.CaichWPointwise

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory Set
open scoped BigOperators ENNReal Interval Topology

namespace Erdos
namespace Problem520

/-!
# The floor-safe piecewise `W` budget

The raw divisor-energy budget is useful only while the short interval
contains many integers.  When `x < p * (X + 1)`, the interval contains at
most one integer and the corresponding prime contribution has every
positive moment root at most one.  This file combines those two estimates
before the finite-prime Minkowski inequality.  This is essential: the raw
divisor budget itself need not be at most one in the single-atom range.
-/

/-- For one prime, use the exact divisor budget in the many-atom range and
the pointwise constant-one budget in the single-atom range. -/
noncomputable def caichWPiecewisePrimeMomentRootBudget
    (r X x p : ℕ) : ℝ :=
  if x < p * (X + 1) then 1
  else caichWPrimeMomentRootBudget r (X : ℝ) x p

/-- The displayed piecewise budget after finite-prime Minkowski. -/
noncomputable def caichWPiecewiseTotalMomentRootBudget
    (r X x a b : ℕ) : ℝ :=
  ∑ p ∈ freshPrimes a b,
    caichWPiecewisePrimeMomentRootBudget r X x p

theorem caichWPiecewisePrimeMomentRootBudget_nonneg
    (r : ℕ) {X : ℕ} (hX : 0 < X) (x p : ℕ) :
    0 ≤ caichWPiecewisePrimeMomentRootBudget r X x p := by
  unfold caichWPiecewisePrimeMomentRootBudget
  split_ifs
  · norm_num
  · unfold caichWPrimeMomentRootBudget
    have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
    exact mul_nonneg (div_nonneg hXR.le (Nat.cast_nonneg p))
      (intervalIntegral.integral_nonneg (by
        have : 0 ≤ 1 / (X : ℝ) := by positivity
        have hpR : 0 ≤ (p : ℝ) := by positivity
        nlinarith) fun t _ht ↦
          caichWShortMomentRootBudget_nonneg r x p t)

theorem caichWPiecewiseTotalMomentRootBudget_nonneg
    (r : ℕ) {X : ℕ} (hX : 0 < X) (x a b : ℕ) :
    0 ≤ caichWPiecewiseTotalMomentRootBudget r X x a b := by
  unfold caichWPiecewiseTotalMomentRootBudget
  exact Finset.sum_nonneg fun p _hp ↦
    caichWPiecewisePrimeMomentRootBudget_nonneg r hX x p

/-- The probabilistic moment root for one prime is controlled by the
piecewise budget. -/
theorem caichWPrimeContribution_moment_root_le_piecewise
    (r x : ℕ) {X p : ℕ} (hr : 1 ≤ r) (hX : 0 < X)
    (hp : p.Prime) :
    (∫ omega, caichWPrimeContribution (X : ℝ) x p omega ^ r ∂μ) ^
        (1 / (r : ℝ)) ≤
      caichWPiecewisePrimeMomentRootBudget r X x p := by
  unfold caichWPiecewisePrimeMomentRootBudget
  by_cases hlarge : caichWLargePrimeCondition X x p
  · rw [if_pos (by simpa only [caichWLargePrimeCondition] using! hlarge)]
    exact caichWPrimeContribution_moment_root_le_one_of_largePrime
      hX hp.pos hlarge (by omega)
  · rw [if_neg (by simpa only [caichWLargePrimeCondition] using! hlarge)]
    exact caichWPrimeContribution_moment_root_le r x hr
      (by exact_mod_cast hX) hp

set_option maxHeartbeats 800000 in
/-- Finite-prime Minkowski with the single-atom repair made before the
arithmetic estimate. -/
theorem caichInitialSmoothingError_moment_root_le_piecewise
    (r X x a b : ℕ) (hr : 1 ≤ r) (hX : 0 < X) :
    (∫ omega,
        caichInitialSmoothingError (X : ℝ) omega x a b ^ r ∂μ) ^
        (1 / (r : ℝ)) ≤
      caichWPiecewiseTotalMomentRootBudget r X x a b := by
  let P : Finset ℕ := freshPrimes a b
  let F : ℕ → Omega → ℝ := fun p ↦
    caichWPrimeContribution (X : ℝ) x p
  have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hr0 : r ≠ 0 := by omega
  have hsum := lpNorm_sum_le
    (p := (r : ℝ≥0∞)) (μ := μ) (s := P) (f := F)
    (fun p hp ↦ memLp_caichWPrimeContribution hXR x
      (mem_freshPrimes.mp hp).1.pos (r : ℝ≥0∞))
    (by exact_mod_cast hr)
  have hsum_eq : (∑ p ∈ P, F p) =
      fun omega ↦
        caichInitialSmoothingError (X : ℝ) omega x a b := by
    funext omega
    simpa only [Finset.sum_apply] using!
      (caichInitialSmoothingError_eq_sum_primeContributions
        (X : ℝ) omega x a b).symm
  have hleft : lpNorm (fun omega ↦
      caichInitialSmoothingError (X : ℝ) omega x a b)
      (r : ℝ≥0∞) μ =
      (∫ omega,
          caichInitialSmoothingError (X : ℝ) omega x a b ^ r ∂μ) ^
        (1 / (r : ℝ)) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by exact_mod_cast hr0)
      (by simp)
      (measurable_caichInitialSmoothingError hXR x a b).aestronglyMeasurable]
    simp only [ENNReal.toReal_natCast, Real.rpow_natCast, Real.norm_eq_abs,
      abs_of_nonneg (caichInitialSmoothingError_nonneg hXR _ _ _ _),
      inv_eq_one_div]
  have hprime (p : ℕ) (hp : p ∈ P) :
      lpNorm (F p) (r : ℝ≥0∞) μ ≤
        caichWPiecewisePrimeMomentRootBudget r X x p := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by exact_mod_cast hr0)
      (by simp) (measurable_caichWPrimeContribution hXR x
        (mem_freshPrimes.mp hp).1.pos).aestronglyMeasurable]
    simp only [ENNReal.toReal_natCast, Real.rpow_natCast, Real.norm_eq_abs,
      abs_of_nonneg (caichWPrimeContribution_nonneg hXR x
        (mem_freshPrimes.mp hp).1.pos _), inv_eq_one_div]
    exact caichWPrimeContribution_moment_root_le_piecewise r x hr hX
      (mem_freshPrimes.mp hp).1
  rw [hsum_eq, hleft] at hsum
  exact hsum.trans (by
    unfold caichWPiecewiseTotalMomentRootBudget P
    exact Finset.sum_le_sum fun p hp ↦ hprime p hp)

theorem caichInitialSmoothingError_moment_le_piecewise
    (r X x a b : ℕ) (hr : 1 ≤ r) (hX : 0 < X) :
    (∫ omega,
        caichInitialSmoothingError (X : ℝ) omega x a b ^ r ∂μ) ≤
      caichWPiecewiseTotalMomentRootBudget r X x a b ^ r := by
  let I : ℝ := ∫ omega,
    caichInitialSmoothingError (X : ℝ) omega x a b ^ r ∂μ
  let B : ℝ := caichWPiecewiseTotalMomentRootBudget r X x a b
  have hI : 0 ≤ I := integral_nonneg fun omega ↦
    pow_nonneg (caichInitialSmoothingError_nonneg
      (by exact_mod_cast hX : (0 : ℝ) < (X : ℝ)) omega x a b) r
  have hroot : I ^ (1 / (r : ℝ)) ≤ B := by
    simpa only [I, B] using!
      caichInitialSmoothingError_moment_root_le_piecewise
        r X x a b hr hX
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg hI _) hroot r
  have hr0 : r ≠ 0 := by omega
  simpa only [I, B, one_div, Real.rpow_inv_natCast_pow hI hr0] using! hpow

/-- Moment estimate for the normalized `W/x` auxiliary with natural
smoothing parameter. -/
theorem caichConcreteWoverX_moment_le_piecewise
    (r X x a b : ℕ) (hr : 1 ≤ r) (hX : 0 < X) (hx : 0 < x) :
    (∫ omega,
        (caichInitialSmoothingError (X : ℝ) omega x a b /
          (x : ℝ)) ^ r ∂μ) ≤
      (caichWPiecewiseTotalMomentRootBudget r X x a b /
        (x : ℝ)) ^ r := by
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  simp_rw [div_pow]
  rw [integral_div]
  exact div_le_div_of_nonneg_right
    (caichInitialSmoothingError_moment_le_piecewise r X x a b hr hX)
    (pow_nonneg hxR.le r)

/-- The aligned `W/x` variable using literally the same floor-safe natural
parameter as the scheduled main term. -/
noncomputable def caichAlignedConcreteWoverXNat
    (r m : ℕ) (a : ℕ → ℕ → ℕ)
    (ell i : ℕ) (omega : Omega) : ℝ :=
  caichInitialSmoothingError
      (caichWSmoothingParameterNatCast r
        (alignedRootExpTestPoint m i))
      omega (alignedRootExpTestPoint m i) (a ell i)
      (alignedRootExpTestPoint m i) /
    (alignedRootExpTestPoint m i : ℝ)

theorem caichAlignedConcreteWoverXNat_nonneg
    {r K m : ℕ} {a : ℕ → ℕ → ℕ}
    {ell i : ℕ} (hi : i ∈ alignedRootExpTests K m ell)
    (omega : Omega) :
    0 ≤ caichAlignedConcreteWoverXNat r m a ell i omega := by
  unfold caichAlignedConcreteWoverXNat
  exact div_nonneg
    (caichInitialSmoothingError_nonneg
      (caichWSmoothingParameterNatCast_pos r
        (alignedRootExpTestPoint m i)) omega _ _ _)
    (Nat.cast_nonneg _)

theorem integrable_caichAlignedConcreteWoverXNat_pow
    {r K m : ℕ} (hr : 1 ≤ r) {a : ℕ → ℕ → ℕ}
    {ell i : ℕ} (hi : i ∈ alignedRootExpTests K m ell) :
    Integrable (fun omega ↦
      caichAlignedConcreteWoverXNat r m a ell i omega ^ r) μ := by
  let x := alignedRootExpTestPoint m i
  let X := caichWSmoothingParameterNat r x
  have hx : 0 < x :=
    Nat.zero_lt_of_lt (one_lt_alignedRootExpTestPoint_of_mem hi)
  have hX : 0 < X := caichWSmoothingParameterNat_pos r x
  have hW := integrable_caichInitialSmoothingError_pow
    (X := (X : ℝ)) (by exact_mod_cast hX : (0 : ℝ) < (X : ℝ))
    x (a ell i) x r (by omega)
  unfold caichAlignedConcreteWoverXNat
    caichWSmoothingParameterNatCast
  simpa only [x, X, div_pow] using! hW.div_const ((x : ℝ) ^ r)

end Problem520
end Erdos
