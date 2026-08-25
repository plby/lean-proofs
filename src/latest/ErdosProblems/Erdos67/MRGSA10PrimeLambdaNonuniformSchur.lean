import ErdosProblems.Erdos67.MRGSA10PrimeLambdaL2

/-!
# Row-dependent weighted Schur bounds for the A.10 prime polynomial

The uniform Schur bound loses the dependence of the Gaussian row on its
base prime.  This module keeps the row majorant `R n` inside the diagonal
sum.  In particular, a local beta-sieve density of size `1 / log n` is not
replaced by its worst value at the bottom of the prime window.
-/

open scoped BigOperators

namespace Erdos67.MRHalaszBands

noncomputable section

/-- Weighted Schur with a row-dependent majorant.  This is the exact
finite-sum form needed when the arithmetic row bound improves with the
base point. -/
theorem finiteHalaszLogGaussianPairMajorant_le_weightedSchur_rowDependent
    (D : Finset ℕ) (a : ℕ → ℂ) (q w R : ℕ → ℝ)
    {b : ℝ} (_hb : 0 < b)
    (hq : ∀ n ∈ D, 0 ≤ q n) (_hw : ∀ n ∈ D, 0 ≤ w n)
    (hpair : ∀ n ∈ D, ∀ m ∈ D,
      ‖a n‖ * ‖a m‖ ≤ (q n * w m + q m * w n) / 2)
    (hrow : ∀ n ∈ D,
      (∑ m ∈ D, w m * finiteHalaszGaussianPairKernel b
        (Real.log m - Real.log n)) ≤ R n) :
    finiteHalaszLogGaussianPairMajorant D a b ≤
      Real.sqrt (Real.pi / b) * (∑ n ∈ D, q n * R n) := by
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
        ∑ n ∈ D, q n * R n := by
    calc
      (∑ n ∈ D, ∑ m ∈ D, q n * w m * K n m) =
          ∑ n ∈ D, q n * (∑ m ∈ D, w m * K n m) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        ring
      _ ≤ ∑ n ∈ D, q n * R n := by
        apply Finset.sum_le_sum
        intro n hn
        exact mul_le_mul_of_nonneg_left (by simpa only [K] using hrow n hn)
          (hq n hn)
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
        ∑ n ∈ D, q n * R n := by
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
      _ ≤ ∑ n ∈ D, q n * R n := hfirst
  unfold finiteHalaszLogGaussianPairMajorant
  exact mul_le_mul_of_nonneg_left (by simpa only [K] using hpairs)
    (Real.sqrt_nonneg _)

/-- Prime-part GHS mean square with the local Gaussian row retained
inside the exact Schur diagonal sum. -/
theorem intervalIntegral_normSq_gsA10PrimeLambdaPolynomial_le_rowDependentSchur
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) (sigma T : ℝ) (R : ℕ → ℝ)
    (hT : 0 < T)
    (hrow : ∀ n ∈ gsA10PrimeWindow y X,
      (∑ m ∈ gsA10PrimeWindow y X,
          (Real.log (m : ℝ) / m) *
            finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
              (Real.log m - Real.log n)) ≤ R n) :
    (∫ t in -T..T,
        Complex.normSq
          (gsA10PrimeLambdaPolynomial hmul y X sigma t)) ≤
      Real.exp 1 *
        (Real.sqrt (Real.pi / (T⁻¹ ^ 2)) *
          (∑ n ∈ gsA10PrimeWindow y X,
            gsA10PrimeLambdaSchurWeight hmul y sigma n * R n)) := by
  let D := gsA10PrimeWindow y X
  let a := gsA10PrimeLambdaCoefficient hmul y sigma
  let q := gsA10PrimeLambdaSchurWeight hmul y sigma
  let w : ℕ → ℝ := fun n ↦ Real.log (n : ℝ) / n
  have hq : ∀ n ∈ D, 0 ≤ q n := by
    intro n hn
    have hnData := mem_gsA10PrimeWindow.mp (by simpa only [D] using hn)
    exact div_nonneg (sq_nonneg _)
      (div_nonneg
        (Real.log_nonneg (by exact_mod_cast hnData.2.2.one_le))
        (by positivity))
  have hw : ∀ n ∈ D, 0 ≤ w n := by
    intro n hn
    have hnData := mem_gsA10PrimeWindow.mp (by simpa only [D] using hn)
    exact div_nonneg
      (Real.log_nonneg (by exact_mod_cast hnData.2.2.one_le))
      (by positivity)
  have hpair : ∀ n ∈ D, ∀ m ∈ D,
      ‖a n‖ * ‖a m‖ ≤ (q n * w m + q m * w n) / 2 := by
    intro n hn m hm
    have hnData := mem_gsA10PrimeWindow.mp (by simpa only [D] using hn)
    have hmData := mem_gsA10PrimeWindow.mp (by simpa only [D] using hm)
    have hwn : 0 < w n := by
      dsimp only [w]
      exact div_pos
        (Real.log_pos (by exact_mod_cast hnData.2.2.one_lt))
        (by exact_mod_cast hnData.2.2.pos)
    have hwm : 0 < w m := by
      dsimp only [w]
      exact div_pos
        (Real.log_pos (by exact_mod_cast hmData.2.2.one_lt))
        (by exact_mod_cast hmData.2.2.pos)
    simpa only [q, gsA10PrimeLambdaSchurWeight, a] using
      (mul_le_weighted_square_average
        (A := ‖a n‖) (B := ‖a m‖) hwn hwm)
  have hrow' : ∀ n ∈ D,
      (∑ m ∈ D, w m * finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
        (Real.log m - Real.log n)) ≤ R n := by
    intro n hn
    simpa only [D, w] using hrow n (by simpa only [D] using hn)
  have hmajor :=
    finiteHalaszLogGaussianPairMajorant_le_weightedSchur_rowDependent
      D a q w R (sq_pos_of_pos (inv_pos.mpr hT)) hq hw hpair hrow'
  have hgauss :=
    intervalIntegral_normSq_logarithmicDirichletPolynomial_le_gaussianPairMajorant
      D a hT
  unfold gsA10PrimeLambdaPolynomial
  calc
    (∫ t in -T..T,
        Complex.normSq
          (logarithmicDirichletPolynomial D a t)) ≤
      Real.exp 1 * finiteHalaszLogGaussianPairMajorant D a (T⁻¹ ^ 2) := hgauss
    _ ≤ Real.exp 1 *
        (Real.sqrt (Real.pi / (T⁻¹ ^ 2)) *
          (∑ n ∈ D, q n * R n)) :=
      mul_le_mul_of_nonneg_left hmajor (Real.exp_pos 1).le
    _ = _ := rfl

/-- On a multiplicative neighborhood of `n`, the logarithmic prime weight
has the local bound `4 log(4n) / n`, with no ambient `log X` loss. -/
theorem primeLogDiv_le_four_mul_log_four_mul_div
    {n p : ℕ} (hn : 0 < n) (hp : 0 < p)
    (hnp : n / 4 < p) (hpn : p ≤ 4 * n) :
    Real.log (p : ℝ) / p ≤ 4 * Real.log ((4 * n : ℕ) : ℝ) / n := by
  exact primeLogDiv_le_four_mul_log_div hn hp hpn hnp

/-- A local sieve block only has to lie below `n / 4`, rather than below
the global bottom `y` of the prime window. -/
theorem gsA10PrimeNearWindow_subset_missingBlock_of_block_le_quarter
    {I : ℕ × ℕ} {y X n : ℕ}
    (hIz : ∀ q ∈ Erdos67.primesInBlock I,
      q ≤ n / 4) :
    gsA10PrimeNearWindow y X n ⊆
      Erdos67.MRIntervalBetaSieve.intervalMissingPrimeBlockSet
        I (n / 4) (4 * n) := by
  intro p hp
  have hpData := mem_gsA10PrimeNearWindow.mp hp
  have hpWindow := mem_gsA10PrimeWindow.mp hpData.1
  exact prime_mem_intervalMissingPrimeBlockSet_of_block_le
    hpWindow.2.2 hpData.2.1 hpData.2.2 hpData.2.1 hIz

/-- Near-prime Gaussian row with both local quantities retained: the
weight is `4 log(4n) / n`, and the sieve level need only be below `n/4`.
This is the row form which can later take density `O(1 / log n)`. -/
theorem sum_gsA10PrimeNearWindow_log_div_gaussian_le_of_localIntervalBeta
    {I : ℕ × ℕ} {y X n : ℕ} {T density remainder : ℝ}
    (hT : 0 < T) (hnWindow : n ∈ gsA10PrimeWindow y X)
    (hIz : ∀ q ∈ Erdos67.primesInBlock I,
      q ≤ n / 4)
    (hdensity : 0 ≤ density) (hrem : 0 ≤ remainder)
    (hbeta : ∀ A B : ℕ, A ≤ B →
      ((Erdos67.MRIntervalBetaSieve.intervalMissingPrimeBlockSet
          I A B).card : ℝ) ≤
        (((B - A : ℕ) : ℝ) * density + remainder)) :
    (∑ m ∈ gsA10PrimeNearWindow y X n,
        (Real.log (m : ℝ) / m) *
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n)) ≤
      (4 * Real.log ((4 * n : ℕ) : ℝ) / n) *
        (32 * ((4 * n : ℕ) : ℝ) / T * density +
          6 * density + 2 * remainder) := by
  have hnData := mem_gsA10PrimeWindow.mp hnWindow
  have hnpos : 0 < n := (Nat.zero_le y).trans_lt hnData.1
  have hnNear :
      n ∈ Erdos67.MRIntervalBetaSieve.intervalMissingPrimeBlockSet
        I (n / 4) (4 * n) := by
    exact prime_mem_intervalMissingPrimeBlockSet_of_block_le
      hnData.2.2 (by omega) (by omega) (by omega) hIz
  let W : ℝ := 4 * Real.log ((4 * n : ℕ) : ℝ) / n
  let E := gsA10PrimeNearWindow y X n
  let D := Erdos67.MRIntervalBetaSieve.intervalMissingPrimeBlockSet
    I (n / 4) (4 * n)
  have hW0 : 0 ≤ W := by
    dsimp only [W]
    exact div_nonneg
      (mul_nonneg (by norm_num)
        (Real.log_nonneg (by exact_mod_cast (show 1 ≤ 4 * n by omega))))
      (by positivity)
  have hED : E ⊆ D := by
    simpa only [E, D] using
      (gsA10PrimeNearWindow_subset_missingBlock_of_block_le_quarter
        (I := I) (y := y) (X := X) hIz)
  have hpoint : ∀ m ∈ E,
      (Real.log (m : ℝ) / m) *
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n) ≤
        W * finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n) := by
    intro m hm
    have hmData := mem_gsA10PrimeNearWindow.mp (by simpa only [E] using hm)
    have hmWindow := mem_gsA10PrimeWindow.mp hmData.1
    have hmpos : 0 < m := (Nat.zero_le y).trans_lt hmWindow.1
    exact mul_le_mul_of_nonneg_right
      (by
        simpa only [W] using
          (primeLogDiv_le_four_mul_log_four_mul_div
            (n := n) (p := m) hnpos hmpos hmData.2.1 hmData.2.2))
      (finiteHalaszGaussianPairKernel_nonneg _ _)
  have hweighted :
      (∑ m ∈ E, (Real.log (m : ℝ) / m) *
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n)) ≤
        W * ∑ m ∈ D,
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n) := by
    calc
      _ ≤ ∑ m ∈ E, W *
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n) := Finset.sum_le_sum hpoint
      _ = W * ∑ m ∈ E,
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n) := by rw [Finset.mul_sum]
      _ ≤ W * ∑ m ∈ D,
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n) := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum_of_subset_of_nonneg hED
            (fun _ _ _ ↦ finiteHalaszGaussianPairKernel_nonneg _ _)
        · exact hW0
  have hrow := sum_missingBlock_gaussianRow_le_of_intervalBeta
    (I := I) (L := n / 4) (U := 4 * n) (n := n)
    hT (by omega) hnNear hdensity hrem hbeta
  simpa only [E, W] using
    hweighted.trans (mul_le_mul_of_nonneg_left hrow hW0)

/-- Full prime Gaussian row with a row-specific beta-sieve input.  Only
the fixed-gap Gaussian tail still refers to the ambient endpoint `X`. -/
theorem sum_gsA10PrimeWindow_log_div_gaussian_le_of_localIntervalBeta
    {I : ℕ × ℕ} {y X n : ℕ} {T density remainder : ℝ}
    (hT : 0 < T) (hnWindow : n ∈ gsA10PrimeWindow y X)
    (hIz : ∀ q ∈ Erdos67.primesInBlock I,
      q ≤ n / 4)
    (hdensity : 0 ≤ density) (hrem : 0 ≤ remainder)
    (hbeta : ∀ A B : ℕ, A ≤ B →
      ((Erdos67.MRIntervalBetaSieve.intervalMissingPrimeBlockSet
          I A B).card : ℝ) ≤
        (((B - A : ℕ) : ℝ) * density + remainder)) :
    (∑ m ∈ gsA10PrimeWindow y X,
        (Real.log (m : ℝ) / m) *
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n)) ≤
      (4 * Real.log ((4 * n : ℕ) : ℝ) / n) *
          (32 * ((4 * n : ℕ) : ℝ) / T * density +
            6 * density + 2 * remainder) +
        finiteHalaszGaussianPairKernel (T⁻¹ ^ 2) (Real.log 4) *
          (Real.log (X : ℝ) + polynomialHeightPrimeLogMertensBound) := by
  let term : ℕ → ℝ := fun m ↦
    (Real.log (m : ℝ) / m) *
      finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
        (Real.log m - Real.log n)
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (gsA10PrimeWindow y X)
    (fun m ↦ m ∈ Finset.Ioc (n / 4) (4 * n)) term
  have hnear :=
    sum_gsA10PrimeNearWindow_log_div_gaussian_le_of_localIntervalBeta
      hT hnWindow hIz hdensity hrem hbeta
  have hfar := sum_gsA10PrimeFarWindow_log_div_gaussian_le hT hnWindow
  have hEq :
      (∑ m ∈ gsA10PrimeWindow y X, term m) =
        (∑ m ∈ gsA10PrimeNearWindow y X n, term m) +
          ∑ m ∈ gsA10PrimeFarWindow y X n, term m := by
    simpa only [gsA10PrimeNearWindow, gsA10PrimeFarWindow] using hsplit.symm
  rw [show (∑ m ∈ gsA10PrimeWindow y X,
      (Real.log (m : ℝ) / m) *
        finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
          (Real.log m - Real.log n)) =
      ∑ m ∈ gsA10PrimeWindow y X, term m by rfl,
    hEq]
  exact add_le_add hnear hfar

end

end Erdos67.MRHalaszBands

#print axioms Erdos67.MRHalaszBands.finiteHalaszLogGaussianPairMajorant_le_weightedSchur_rowDependent
#print axioms Erdos67.MRHalaszBands.intervalIntegral_normSq_gsA10PrimeLambdaPolynomial_le_rowDependentSchur
#print axioms Erdos67.MRHalaszBands.primeLogDiv_le_four_mul_log_four_mul_div
#print axioms Erdos67.MRHalaszBands.sum_gsA10PrimeNearWindow_log_div_gaussian_le_of_localIntervalBeta
#print axioms Erdos67.MRHalaszBands.sum_gsA10PrimeWindow_log_div_gaussian_le_of_localIntervalBeta
