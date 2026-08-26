import ErdosProblems.Erdos67b.MRGSA10ShortPrimeIntervalBeta
import ErdosProblems.Erdos67b.MRFiniteHalaszGaussianLocalPair
import ErdosProblems.Erdos67b.MRFiniteHalaszGaussianSchur
import ErdosProblems.Erdos67b.TwistSeparationAnalytic

/-!
# The near part of a Mangoldt-prime Gaussian row

For a fixed prime `n`, primes `m` with `n/4 < m ≤ 4n` have weight
`log m / m ≤ 4 log X / n`.  The already formalized additive Gaussian
bucket estimate, applied to a prime block lying below the Lambda window,
then supplies the source-sharp `1/T` row contribution.
-/

open scoped BigOperators

namespace Erdos67b.MRHalaszBands

noncomputable section

open Erdos67b
open Erdos67b.MRIntervalBetaSieve

/-- The prime support of the A.10 Lambda window. -/
def gsA10PrimeWindow (y X : ℕ) : Finset ℕ :=
  (Finset.Ioo y (X / y)).filter Nat.Prime

/-- The portion of the prime window multiplicatively close to `n`. -/
def gsA10PrimeNearWindow (y X n : ℕ) : Finset ℕ :=
  (gsA10PrimeWindow y X).filter fun m ↦
    m ∈ Finset.Ioc (n / 4) (4 * n)

/-- The complementary, Gaussian-negligible portion of the prime window. -/
def gsA10PrimeFarWindow (y X n : ℕ) : Finset ℕ :=
  (gsA10PrimeWindow y X).filter fun m ↦
    m ∉ Finset.Ioc (n / 4) (4 * n)

@[simp] theorem mem_gsA10PrimeWindow {y X p : ℕ} :
    p ∈ gsA10PrimeWindow y X ↔ y < p ∧ p < X / y ∧ p.Prime := by
  simp [gsA10PrimeWindow, and_assoc]

@[simp] theorem mem_gsA10PrimeNearWindow {y X n p : ℕ} :
    p ∈ gsA10PrimeNearWindow y X n ↔
      p ∈ gsA10PrimeWindow y X ∧ n / 4 < p ∧ p ≤ 4 * n := by
  simp [gsA10PrimeNearWindow, and_assoc]

@[simp] theorem mem_gsA10PrimeFarWindow {y X n p : ℕ} :
    p ∈ gsA10PrimeFarWindow y X n ↔
      p ∈ gsA10PrimeWindow y X ∧
        (p ≤ n / 4 ∨ 4 * n < p) := by
  simp only [gsA10PrimeFarWindow, Finset.mem_filter,
    Finset.mem_Ioc, not_and_or, not_lt, not_le]

/-- Outside the multiplicative neighborhood `(n/4,4n]`, logarithmic
frequencies are separated by at least `log 4`. -/
theorem log_four_le_abs_log_sub_log_of_far
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hfar : m ≤ n / 4 ∨ 4 * n < m) :
    Real.log 4 ≤ |Real.log m - Real.log n| := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rcases hfar with hlow | hhigh
  · have hmul : 4 * m ≤ n := by omega
    have hlog : Real.log ((4 : ℝ) * m) ≤ Real.log (n : ℝ) := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast hmul
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by exact_mod_cast hm.ne')] at hlog
    have hmn : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log hmR (by exact_mod_cast (hmul.trans' (by omega : m ≤ 4 * m)))
    rw [abs_of_nonpos (sub_nonpos.mpr hmn)]
    linarith
  · have hmul : 4 * n ≤ m := hhigh.le
    have hlog : Real.log ((4 : ℝ) * n) ≤ Real.log (m : ℝ) := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast hmul
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by exact_mod_cast hn.ne')] at hlog
    have hnm : Real.log (n : ℝ) ≤ Real.log (m : ℝ) :=
      Real.log_le_log hnR (by exact_mod_cast (show n ≤ m by omega))
    rw [abs_of_nonneg (sub_nonneg.mpr hnm)]
    linarith

/-- A prime above every prime in `I` belongs to the corresponding
missing-block interval. -/
theorem prime_mem_intervalMissingPrimeBlockSet_of_block_le
    {I : ℕ × ℕ} {A B z p : ℕ}
    (hp : p.Prime) (hAp : A < p) (hpB : p ≤ B)
    (hzp : z < p) (hIz : ∀ q ∈ primesInBlock I, q ≤ z) :
    p ∈ intervalMissingPrimeBlockSet I A B := by
  rw [mem_intervalMissingPrimeBlockSet]
  refine ⟨hAp, hpB, ?_⟩
  intro q hq hqp
  have hqPrime := (mem_primesInBlock.mp hq).1
  have hEq : q = p :=
    (Nat.prime_dvd_prime_iff_eq hqPrime hp).mp hqp
  have hqz := hIz q hq
  omega

/-- Every near-window prime is contained in the centered missing-block
interval used by the Gaussian local-pair theorem. -/
theorem gsA10PrimeNearWindow_subset_missingBlock
    {I : ℕ × ℕ} {y X n : ℕ}
    (hIz : ∀ q ∈ primesInBlock I, q ≤ y) :
    gsA10PrimeNearWindow y X n ⊆
      intervalMissingPrimeBlockSet I (n / 4) (4 * n) := by
  intro p hp
  have hpData := mem_gsA10PrimeNearWindow.mp hp
  have hpWindow := mem_gsA10PrimeWindow.mp hpData.1
  exact prime_mem_intervalMissingPrimeBlockSet_of_block_le
    hpWindow.2.2 hpData.2.1 hpData.2.2 hpWindow.1 hIz

/-- The elementary weight bound on the near window. -/
theorem primeLogDiv_le_four_mul_log_div
    {X n p : ℕ} (hn : 0 < n) (hp : 0 < p)
    (hpX : p ≤ X) (hnp : n / 4 < p) :
    Real.log (p : ℝ) / p ≤ 4 * Real.log (X : ℝ) / n := by
  have hn4p : n ≤ 4 * p := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hXR : (0 : ℝ) < X := by
    exact_mod_cast hp.trans_le hpX
  have hlogp0 : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp)
  have hlogX0 : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.trans_le hpX)
  have hlog : Real.log (p : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log hpR (by exact_mod_cast hpX)
  have hinv : (1 : ℝ) / p ≤ 4 / n := by
    rw [div_le_div_iff₀ hpR hnR]
    have hcast : (n : ℝ) ≤ 4 * (p : ℝ) := by exact_mod_cast hn4p
    simpa using hcast
  calc
    Real.log (p : ℝ) / p = Real.log (p : ℝ) * (1 / p) := by ring
    _ ≤ Real.log (X : ℝ) * (1 / p) :=
      mul_le_mul_of_nonneg_right hlog (by positivity)
    _ ≤ Real.log (X : ℝ) * (4 / n) :=
      mul_le_mul_of_nonneg_left hinv hlogX0
    _ = 4 * Real.log (X : ℝ) / n := by ring

/-- Near-prime part of one Gaussian Schur row.  The local interval beta
sieve is supplied abstractly so the final schedule can choose its level
without changing the analytic statement. -/
theorem sum_gsA10PrimeNearWindow_log_div_gaussian_le_of_intervalBeta
    {I : ℕ × ℕ} {y X n : ℕ} {T density remainder : ℝ}
    (hT : 0 < T) (hnWindow : n ∈ gsA10PrimeWindow y X)
    (hIz : ∀ q ∈ primesInBlock I, q ≤ y)
    (hdensity : 0 ≤ density) (hrem : 0 ≤ remainder)
    (hbeta : ∀ A B : ℕ, A ≤ B →
      ((intervalMissingPrimeBlockSet I A B).card : ℝ) ≤
        (((B - A : ℕ) : ℝ) * density + remainder)) :
    (∑ m ∈ gsA10PrimeNearWindow y X n,
        (Real.log (m : ℝ) / m) *
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n)) ≤
      (4 * Real.log (X : ℝ) / n) *
        (32 * ((4 * n : ℕ) : ℝ) / T * density +
          6 * density + 2 * remainder) := by
  have hnData := mem_gsA10PrimeWindow.mp hnWindow
  have hnpos : 0 < n := (Nat.zero_le y).trans_lt hnData.1
  have hXdivX : X / y ≤ X := Nat.div_le_self X y
  have hnX : n ≤ X := hnData.2.1.le.trans hXdivX
  have hnNear : n ∈ intervalMissingPrimeBlockSet I (n / 4) (4 * n) := by
    exact prime_mem_intervalMissingPrimeBlockSet_of_block_le
      hnData.2.2 (by omega) (by omega) hnData.1 hIz
  let W : ℝ := 4 * Real.log (X : ℝ) / n
  let E := gsA10PrimeNearWindow y X n
  let D := intervalMissingPrimeBlockSet I (n / 4) (4 * n)
  have hED : E ⊆ D := by
    simpa only [E, D] using
      (gsA10PrimeNearWindow_subset_missingBlock (I := I) hIz)
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
    have hmX : m ≤ X := hmWindow.2.1.le.trans hXdivX
    exact mul_le_mul_of_nonneg_right
      (by simpa only [W] using
        primeLogDiv_le_four_mul_log_div hnpos hmpos hmX hmData.2.1)
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
        · dsimp only [W]
          positivity
  have hrow := sum_missingBlock_gaussianRow_le_of_intervalBeta
    (I := I) (L := n / 4) (U := 4 * n) (n := n)
    hT (by omega) hnNear hdensity hrem hbeta
  exact hweighted.trans (mul_le_mul_of_nonneg_left hrow (by
    dsimp only [W]
    positivity))

/-- The far portion of a prime Gaussian row is bounded by the kernel at
the fixed logarithmic gap `log 4`, times the full prime logarithmic
harmonic mass. -/
theorem sum_gsA10PrimeFarWindow_log_div_gaussian_le
    {y X n : ℕ} {T : ℝ} (hT : 0 < T)
    (hnWindow : n ∈ gsA10PrimeWindow y X) :
    (∑ m ∈ gsA10PrimeFarWindow y X n,
        (Real.log (m : ℝ) / m) *
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n)) ≤
      finiteHalaszGaussianPairKernel (T⁻¹ ^ 2) (Real.log 4) *
        (Real.log (X : ℝ) + polynomialHeightPrimeLogMertensBound) := by
  have hnData := mem_gsA10PrimeWindow.mp hnWindow
  have hnpos : 0 < n := (Nat.zero_le y).trans_lt hnData.1
  have hXdivX : X / y ≤ X := Nat.div_le_self X y
  let E := gsA10PrimeFarWindow y X n
  let K : ℝ := finiteHalaszGaussianPairKernel (T⁻¹ ^ 2) (Real.log 4)
  have hb : 0 < T⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr hT)
  have hpoint : ∀ m ∈ E,
      finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
          (Real.log m - Real.log n) ≤ K := by
    intro m hm
    have hmData := mem_gsA10PrimeFarWindow.mp (by simpa only [E] using hm)
    have hmWindow := mem_gsA10PrimeWindow.mp hmData.1
    have hmpos : 0 < m := (Nat.zero_le y).trans_lt hmWindow.1
    exact finiteHalaszGaussianPairKernel_le_of_gap hb
      (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4))
      (log_four_le_abs_log_sub_log_of_far hmpos hnpos hmData.2)
  have hweightNonneg : ∀ m ∈ E, 0 ≤ Real.log (m : ℝ) / m := by
    intro m hm
    have hmData := mem_gsA10PrimeFarWindow.mp (by simpa only [E] using hm)
    have hmWindow := mem_gsA10PrimeWindow.mp hmData.1
    exact div_nonneg
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by
        exact hmWindow.2.2.one_le))) (by positivity)
  have hprimeSubset : E ⊆ Nat.primesLE X := by
    intro p hp
    have hpData := mem_gsA10PrimeFarWindow.mp (by simpa only [E] using hp)
    have hpWindow := mem_gsA10PrimeWindow.mp hpData.1
    rw [Nat.mem_primesLE]
    exact ⟨hpWindow.2.1.le.trans hXdivX, hpWindow.2.2⟩
  have hmass :
      (∑ m ∈ E, Real.log (m : ℝ) / m) ≤
        BoundedGaps.Maynard.primeLogHarmonicSum X := by
    unfold BoundedGaps.Maynard.primeLogHarmonicSum
    exact Finset.sum_le_sum_of_subset_of_nonneg hprimeSubset
      (fun p hp _ ↦ by
        have hpPrime := Nat.prime_of_mem_primesLE hp
        exact div_nonneg
          (Real.log_nonneg (by exact_mod_cast hpPrime.one_le)) (by positivity))
  have hMertens := primeLogHarmonicSum_le_log_add_bound X
  calc
    (∑ m ∈ gsA10PrimeFarWindow y X n,
        (Real.log (m : ℝ) / m) *
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n)) =
        ∑ m ∈ E, (Real.log (m : ℝ) / m) *
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n) := rfl
    _ ≤ ∑ m ∈ E, (Real.log (m : ℝ) / m) * K := by
      apply Finset.sum_le_sum
      intro m hm
      exact mul_le_mul_of_nonneg_left (hpoint m hm) (hweightNonneg m hm)
    _ = K * ∑ m ∈ E, Real.log (m : ℝ) / m := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      ring
    _ ≤ K * BoundedGaps.Maynard.primeLogHarmonicSum X :=
      mul_le_mul_of_nonneg_left hmass
        (finiteHalaszGaussianPairKernel_nonneg _ _)
    _ ≤ K * (Real.log (X : ℝ) +
        polynomialHeightPrimeLogMertensBound) :=
      mul_le_mul_of_nonneg_left hMertens
        (finiteHalaszGaussianPairKernel_nonneg _ _)
    _ = finiteHalaszGaussianPairKernel (T⁻¹ ^ 2) (Real.log 4) *
        (Real.log (X : ℝ) + polynomialHeightPrimeLogMertensBound) := rfl

/-- Full prime Gaussian row, split into its beta-sieved near part and its
fixed-gap Gaussian tail. -/
theorem sum_gsA10PrimeWindow_log_div_gaussian_le_of_intervalBeta
    {I : ℕ × ℕ} {y X n : ℕ} {T density remainder : ℝ}
    (hT : 0 < T) (hnWindow : n ∈ gsA10PrimeWindow y X)
    (hIz : ∀ q ∈ primesInBlock I, q ≤ y)
    (hdensity : 0 ≤ density) (hrem : 0 ≤ remainder)
    (hbeta : ∀ A B : ℕ, A ≤ B →
      ((intervalMissingPrimeBlockSet I A B).card : ℝ) ≤
        (((B - A : ℕ) : ℝ) * density + remainder)) :
    (∑ m ∈ gsA10PrimeWindow y X,
        (Real.log (m : ℝ) / m) *
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n)) ≤
      (4 * Real.log (X : ℝ) / n) *
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
    sum_gsA10PrimeNearWindow_log_div_gaussian_le_of_intervalBeta
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

/-- The concrete beta-sieve density occurring in the A.10 prime row. -/
def gsA10PrimeRowBetaDensity (Cβ : ℝ) (Q S : ℕ) : ℝ :=
  (1 + (4 * Cβ / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
    primeBlockDensity (3, Q)

/-- The finite beta-sieve level remainder in the A.10 prime row. -/
def gsA10PrimeRowBetaRemainder (Q S : ℕ) : ℝ :=
  (((Q ^ S : ℕ) : ℝ) ^ 2)

/-- Fully concrete finite-beta version of the full prime Gaussian row.
The choice of `Q,S` remains visible for the eventual source schedule. -/
theorem exists_sum_gsA10PrimeWindow_log_div_gaussian_beta_bound :
    ∃ Cβ : ℝ, 1 ≤ Cβ ∧
      ∀ y X n Q S : ℕ, ∀ T : ℝ,
        n ∈ gsA10PrimeWindow y X → 3 ≤ Q → Q ≤ y → 101 ≤ S →
        Real.log Cβ ≤ 2 * (S - 100 : ℕ) / 99 → 0 < T →
        (∑ m ∈ gsA10PrimeWindow y X,
            (Real.log (m : ℝ) / m) *
              finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
                (Real.log m - Real.log n)) ≤
          (4 * Real.log (X : ℝ) / n) *
              (32 * ((4 * n : ℕ) : ℝ) / T *
                    gsA10PrimeRowBetaDensity Cβ Q S +
                6 * gsA10PrimeRowBetaDensity Cβ Q S +
                2 * gsA10PrimeRowBetaRemainder Q S) +
            finiteHalaszGaussianPairKernel (T⁻¹ ^ 2) (Real.log 4) *
              (Real.log (X : ℝ) +
                polynomialHeightPrimeLogMertensBound) := by
  obtain ⟨Cβ, hCβ, hbeta⟩ :=
    Erdos67b.MRIntervalBetaSieve.exists_card_intervalMissingPrimeBlockSet_beta_bound
  refine ⟨Cβ, hCβ, ?_⟩
  intro y X n Q S T hnWindow hQ hQy hS hlog hT
  have hdensity : 0 ≤ gsA10PrimeRowBetaDensity Cβ Q S := by
    unfold gsA10PrimeRowBetaDensity
    exact mul_nonneg (by positivity) (primeBlockDensity_nonneg _)
  have hrem : 0 ≤ gsA10PrimeRowBetaRemainder Q S := by
    unfold gsA10PrimeRowBetaRemainder
    positivity
  have hIz : ∀ q ∈ primesInBlock (3, Q), q ≤ y := by
    intro q hq
    exact (mem_primesInBlock.mp hq).2.2.trans hQy
  have hinterval : ∀ A B : ℕ, A ≤ B →
      ((intervalMissingPrimeBlockSet (3, Q) A B).card : ℝ) ≤
        (((B - A : ℕ) : ℝ) * gsA10PrimeRowBetaDensity Cβ Q S +
          gsA10PrimeRowBetaRemainder Q S) := by
    intro A B hAB
    have h := hbeta A B 3 Q S hAB (by norm_num) hQ hS hlog
    simpa only [gsA10PrimeRowBetaDensity,
      gsA10PrimeRowBetaRemainder] using h
  exact sum_gsA10PrimeWindow_log_div_gaussian_le_of_intervalBeta
    hT hnWindow hIz hdensity hrem hinterval

end

end Erdos67b.MRHalaszBands

#print axioms Erdos67b.MRHalaszBands.sum_gsA10PrimeNearWindow_log_div_gaussian_le_of_intervalBeta
#print axioms Erdos67b.MRHalaszBands.sum_gsA10PrimeFarWindow_log_div_gaussian_le
#print axioms Erdos67b.MRHalaszBands.sum_gsA10PrimeWindow_log_div_gaussian_le_of_intervalBeta
#print axioms Erdos67b.MRHalaszBands.exists_sum_gsA10PrimeWindow_log_div_gaussian_beta_bound
