import ErdosProblems.Erdos67.MRFiniteHalaszGaussianMean

/-!
# Weighted Schur reduction for the Gaussian mean value

GHS Lemma 2.6 is obtained by combining a local prime-mass estimate with a
weighted Schur test.  This file isolates the purely analytic finite-sum
part.  It is deliberately stated for arbitrary nonnegative weights: the
arithmetic specialization uses

`q(n) = Λ(n) n^(1-2σ)` and `w(n) = Λ(n)/n`.
-/

open scoped BigOperators

namespace Erdos67.MRHalaszBands

noncomputable section

/-- The Gaussian pair kernel is even. -/
theorem finiteHalaszGaussianPairKernel_neg
    (b x : ℝ) :
    finiteHalaszGaussianPairKernel b (-x) =
      finiteHalaszGaussianPairKernel b x := by
  unfold finiteHalaszGaussianPairKernel
  congr 2
  ring

/-- Weighted Schur test for the finite Gaussian pair majorant.  The
two-weight inequality is the form of weighted AM--GM used for Mangoldt
coefficients. -/
theorem finiteHalaszLogGaussianPairMajorant_le_weightedSchur
    (D : Finset ℕ) (a : ℕ → ℂ) (q w : ℕ → ℝ)
    {b R : ℝ} (_hb : 0 < b)
    (hq : ∀ n ∈ D, 0 ≤ q n) (_hw : ∀ n ∈ D, 0 ≤ w n)
    (hpair : ∀ n ∈ D, ∀ m ∈ D,
      ‖a n‖ * ‖a m‖ ≤ (q n * w m + q m * w n) / 2)
    (hrow : ∀ n ∈ D,
      (∑ m ∈ D, w m * finiteHalaszGaussianPairKernel b
        (Real.log m - Real.log n)) ≤ R) :
    finiteHalaszLogGaussianPairMajorant D a b ≤
      Real.sqrt (Real.pi / b) * (R * ∑ n ∈ D, q n) := by
  let K : ℕ → ℕ → ℝ := fun n m ↦
    finiteHalaszGaussianPairKernel b (Real.log m - Real.log n)
  have hKnonneg : ∀ n m, 0 ≤ K n m := fun n m ↦
    finiteHalaszGaussianPairKernel_nonneg b _
  have hKsymm : ∀ n m, K n m = K m n := by
    intro n m
    dsimp only [K]
    rw [show Real.log m - Real.log n =
        -(Real.log n - Real.log m) by ring,
      finiteHalaszGaussianPairKernel_neg]
  have hfirst :
      (∑ n ∈ D, ∑ m ∈ D, q n * w m * K n m) ≤
        R * ∑ n ∈ D, q n := by
    calc
      (∑ n ∈ D, ∑ m ∈ D, q n * w m * K n m) =
          ∑ n ∈ D, q n * (∑ m ∈ D, w m * K n m) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        ring_nf
      _ ≤ ∑ n ∈ D, q n * R := by
        apply Finset.sum_le_sum
        intro n hn
        exact mul_le_mul_of_nonneg_left (by simpa only [K] using hrow n hn)
          (hq n hn)
      _ = R * ∑ n ∈ D, q n := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        ring
  have hsecondEq :
      (∑ n ∈ D, ∑ m ∈ D, q m * w n * K n m) =
        ∑ n ∈ D, ∑ m ∈ D, q n * w m * K n m := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro m hm
    rw [hKsymm]
  have hpairs :
      (∑ n ∈ D, ∑ m ∈ D,
          ‖a n‖ * ‖a m‖ * K n m) ≤
        R * ∑ n ∈ D, q n := by
    calc
      (∑ n ∈ D, ∑ m ∈ D,
          ‖a n‖ * ‖a m‖ * K n m) ≤
          ∑ n ∈ D, ∑ m ∈ D,
            ((q n * w m + q m * w n) / 2) * K n m := by
        apply Finset.sum_le_sum
        intro n hn
        apply Finset.sum_le_sum
        intro m hm
        exact mul_le_mul_of_nonneg_right (hpair n hn m hm) (hKnonneg n m)
      _ = ((∑ n ∈ D, ∑ m ∈ D, q n * w m * K n m) +
            (∑ n ∈ D, ∑ m ∈ D, q m * w n * K n m)) / 2 := by
        simp only [add_mul, div_eq_mul_inv, Finset.sum_add_distrib,
          Finset.sum_mul]
        ring_nf
      _ = ∑ n ∈ D, ∑ m ∈ D, q n * w m * K n m := by
        rw [hsecondEq]
        ring
      _ ≤ R * ∑ n ∈ D, q n := hfirst
  unfold finiteHalaszLogGaussianPairMajorant
  exact mul_le_mul_of_nonneg_left (by simpa only [K] using hpairs)
    (Real.sqrt_nonneg _)

end

end Erdos67.MRHalaszBands

#print axioms Erdos67.MRHalaszBands.finiteHalaszLogGaussianPairMajorant_le_weightedSchur
