import ErdosProblems.Erdos67b.MRGSA10BetaSourceSchedule
import ErdosProblems.Erdos67b.MRGSA10PrimeLambdaNonuniformSchur

/-!
# Row-local beta sieve for the A.10 prime Gaussian kernel

Unlike the uniform estimate in `MRGSA10PrimeGaussianNearRow`, the sieve
cutoff in this file is allowed to depend on the row centre `n`.  It is only
required to lie below `n / 4`, hence below every prime in the near window.
The logarithmic weight is also kept local, as `log (4n)`, rather than being
enlarged to `log X`.
-/

open scoped BigOperators
open Filter
open scoped Topology

namespace Erdos67b.MRHalaszBands

noncomputable section

open Erdos67b
open Erdos67b.MRIntervalBetaSieve

/-- Concrete finite-beta row estimate with a cutoff chosen independently at
each row centre.  The only comparison required of `Q` is `Q ≤ n / 4`; in
particular there is no condition `Q ≤ y`. -/
theorem exists_sum_gsA10PrimeNearWindow_log_div_gaussian_local_beta_bound :
    ∃ Cβ : ℝ, 1 ≤ Cβ ∧
      ∀ y X n Q S : ℕ, ∀ T : ℝ,
        n ∈ gsA10PrimeWindow y X → 3 ≤ Q → Q ≤ n / 4 → 101 ≤ S →
        Real.log Cβ ≤ 2 * (S - 100 : ℕ) / 99 → 0 < T →
        (∑ m ∈ gsA10PrimeNearWindow y X n,
            (Real.log (m : ℝ) / m) *
              finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
                (Real.log m - Real.log n)) ≤
          (4 * Real.log ((4 * n : ℕ) : ℝ) / n) *
            (32 * ((4 * n : ℕ) : ℝ) / T *
                  gsA10PrimeRowBetaDensity Cβ Q S +
              6 * gsA10PrimeRowBetaDensity Cβ Q S +
              2 * gsA10PrimeRowBetaRemainder Q S) := by
  obtain ⟨Cβ, hCβ, hbeta⟩ :=
    Erdos67b.MRIntervalBetaSieve.exists_card_intervalMissingPrimeBlockSet_beta_bound
  refine ⟨Cβ, hCβ, ?_⟩
  intro y X n Q S T hnWindow hQ hQn hS hlog hT
  have hdensity : 0 ≤ gsA10PrimeRowBetaDensity Cβ Q S := by
    unfold gsA10PrimeRowBetaDensity
    exact mul_nonneg (by positivity) (primeBlockDensity_nonneg _)
  have hrem : 0 ≤ gsA10PrimeRowBetaRemainder Q S := by
    unfold gsA10PrimeRowBetaRemainder
    positivity
  have hIz : ∀ q ∈ primesInBlock (3, Q), q ≤ n / 4 := by
    intro q hq
    exact (mem_primesInBlock.mp hq).2.2.trans hQn
  have hinterval : ∀ A B : ℕ, A ≤ B →
      ((intervalMissingPrimeBlockSet (3, Q) A B).card : ℝ) ≤
        (((B - A : ℕ) : ℝ) * gsA10PrimeRowBetaDensity Cβ Q S +
          gsA10PrimeRowBetaRemainder Q S) := by
    intro A B hAB
    have h := hbeta A B 3 Q S hAB (by norm_num) hQ hS hlog
    simpa only [gsA10PrimeRowBetaDensity,
      gsA10PrimeRowBetaRemainder] using h
  exact sum_gsA10PrimeNearWindow_log_div_gaussian_le_of_localIntervalBeta
    hT hnWindow hIz hdensity hrem hinterval

/-- Source-scheduled local row.  The row centre itself is fed to the beta
cutoff, so the displayed density is `O(1 / log n)` and the finite-level
remainder is `O(n^(1/8))`, with all constants explicit. -/
theorem exists_sum_gsA10PrimeNearWindow_log_div_gaussian_source_local_bound :
    ∃ Cβ : ℝ, 1 ≤ Cβ ∧
      ∀ y X n : ℕ, ∀ T : ℝ,
        n ∈ gsA10PrimeWindow y X →
        3 ≤ gsA10BetaSourceCutoff Cβ n →
        gsA10BetaSourceCutoff Cβ n ≤ n / 4 → 0 < T →
        (∑ m ∈ gsA10PrimeNearWindow y X n,
            (Real.log (m : ℝ) / m) *
              finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
                (Real.log m - Real.log n)) ≤
          (4 * Real.log ((4 * n : ℕ) : ℝ) / n) *
            (32 * ((4 * n : ℕ) : ℝ) / T *
                  (gsA10BetaSourceDensityConstant Cβ /
                    Real.log (n : ℝ)) +
              6 * (gsA10BetaSourceDensityConstant Cβ /
                    Real.log (n : ℝ)) +
              2 * ((2 : ℝ) ^
                    (2 * gsA10BetaSourceDepth Cβ : ℕ) *
                  (n : ℝ) ^ (1 / 8 : ℝ))) := by
  obtain ⟨Cβ, hCβ, hlocal⟩ :=
    exists_sum_gsA10PrimeNearWindow_log_div_gaussian_local_beta_bound
  refine ⟨Cβ, hCβ, ?_⟩
  intro y X n T hnWindow hQ hQn hT
  have hnData := mem_gsA10PrimeWindow.mp hnWindow
  have hn2 : 2 ≤ n := hnData.2.2.two_le
  let Q := gsA10BetaSourceCutoff Cβ n
  let S := gsA10BetaSourceDepth Cβ
  have hraw := hlocal y X n Q S T hnWindow
    (by simpa only [Q] using hQ) (by simpa only [Q] using hQn)
    (by simpa only [S] using gsA10BetaSourceDepth_ge Cβ)
    (by simpa only [S] using
      log_le_two_mul_gsA10BetaSourceDepth_sub_div Cβ) hT
  have hdensity : gsA10PrimeRowBetaDensity Cβ Q S ≤
      gsA10BetaSourceDensityConstant Cβ / Real.log (n : ℝ) := by
    simpa only [Q, S] using
      gsA10PrimeRowBetaDensity_source_le hCβ hn2 hQ
  have hremainder : gsA10PrimeRowBetaRemainder Q S ≤
      (2 : ℝ) ^ (2 * S : ℕ) * (n : ℝ) ^ (1 / 8 : ℝ) := by
    simpa only [Q, S] using
      gsA10PrimeRowBetaRemainder_source_le_rpow Cβ (by omega : 1 ≤ n)
  have hweight : 0 ≤ 4 * Real.log ((4 * n : ℕ) : ℝ) / (n : ℝ) := by
    positivity
  calc
    (∑ m ∈ gsA10PrimeNearWindow y X n,
        (Real.log (m : ℝ) / m) *
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n)) ≤
        (4 * Real.log ((4 * n : ℕ) : ℝ) / n) *
          (32 * ((4 * n : ℕ) : ℝ) / T *
                gsA10PrimeRowBetaDensity Cβ Q S +
            6 * gsA10PrimeRowBetaDensity Cβ Q S +
            2 * gsA10PrimeRowBetaRemainder Q S) := hraw
    _ ≤ (4 * Real.log ((4 * n : ℕ) : ℝ) / n) *
          (32 * ((4 * n : ℕ) : ℝ) / T *
                (gsA10BetaSourceDensityConstant Cβ / Real.log (n : ℝ)) +
            6 * (gsA10BetaSourceDensityConstant Cβ / Real.log (n : ℝ)) +
            2 * ((2 : ℝ) ^ (2 * S : ℕ) *
              (n : ℝ) ^ (1 / 8 : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ hweight
      gcongr
    _ = _ := by rfl

/-- Full-row version of the concrete local beta estimate.  The far part is
the unchanged Gaussian fixed-gap tail; all beta-sieve quantities remain
row-local. -/
theorem exists_sum_gsA10PrimeWindow_log_div_gaussian_local_beta_bound :
    ∃ Cβ : ℝ, 1 ≤ Cβ ∧
      ∀ y X n Q S : ℕ, ∀ T : ℝ,
        n ∈ gsA10PrimeWindow y X → 3 ≤ Q → Q ≤ n / 4 → 101 ≤ S →
        Real.log Cβ ≤ 2 * (S - 100 : ℕ) / 99 → 0 < T →
        (∑ m ∈ gsA10PrimeWindow y X,
            (Real.log (m : ℝ) / m) *
              finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
                (Real.log m - Real.log n)) ≤
          (4 * Real.log ((4 * n : ℕ) : ℝ) / n) *
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
  intro y X n Q S T hnWindow hQ hQn hS hlog hT
  have hdensity : 0 ≤ gsA10PrimeRowBetaDensity Cβ Q S := by
    unfold gsA10PrimeRowBetaDensity
    exact mul_nonneg (by positivity) (primeBlockDensity_nonneg _)
  have hrem : 0 ≤ gsA10PrimeRowBetaRemainder Q S := by
    unfold gsA10PrimeRowBetaRemainder
    positivity
  have hIz : ∀ q ∈ primesInBlock (3, Q), q ≤ n / 4 := by
    intro q hq
    exact (mem_primesInBlock.mp hq).2.2.trans hQn
  have hinterval : ∀ A B : ℕ, A ≤ B →
      ((intervalMissingPrimeBlockSet (3, Q) A B).card : ℝ) ≤
        (((B - A : ℕ) : ℝ) * gsA10PrimeRowBetaDensity Cβ Q S +
          gsA10PrimeRowBetaRemainder Q S) := by
    intro A B hAB
    have h := hbeta A B 3 Q S hAB (by norm_num) hQ hS hlog
    simpa only [gsA10PrimeRowBetaDensity,
      gsA10PrimeRowBetaRemainder] using h
  exact sum_gsA10PrimeWindow_log_div_gaussian_le_of_localIntervalBeta
    hT hnWindow hIz hdensity hrem hinterval

/-- Full source-scheduled local row, prior to replacing its centre by the
bottom `y` of the prime window. -/
theorem exists_sum_gsA10PrimeWindow_log_div_gaussian_source_local_bound :
    ∃ Cβ : ℝ, 1 ≤ Cβ ∧
      ∀ y X n : ℕ, ∀ T : ℝ,
        n ∈ gsA10PrimeWindow y X →
        3 ≤ gsA10BetaSourceCutoff Cβ n →
        gsA10BetaSourceCutoff Cβ n ≤ n / 4 → 0 < T →
        (∑ m ∈ gsA10PrimeWindow y X,
            (Real.log (m : ℝ) / m) *
              finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
                (Real.log m - Real.log n)) ≤
          (4 * Real.log ((4 * n : ℕ) : ℝ) / n) *
              (32 * ((4 * n : ℕ) : ℝ) / T *
                    (gsA10BetaSourceDensityConstant Cβ /
                      Real.log (n : ℝ)) +
                6 * (gsA10BetaSourceDensityConstant Cβ /
                      Real.log (n : ℝ)) +
                2 * ((2 : ℝ) ^
                      (2 * gsA10BetaSourceDepth Cβ : ℕ) *
                    (n : ℝ) ^ (1 / 8 : ℝ))) +
            finiteHalaszGaussianPairKernel (T⁻¹ ^ 2) (Real.log 4) *
              (Real.log (X : ℝ) +
                polynomialHeightPrimeLogMertensBound) := by
  obtain ⟨Cβ, hCβ, hlocal⟩ :=
    exists_sum_gsA10PrimeWindow_log_div_gaussian_local_beta_bound
  refine ⟨Cβ, hCβ, ?_⟩
  intro y X n T hnWindow hQ hQn hT
  have hnData := mem_gsA10PrimeWindow.mp hnWindow
  have hn2 : 2 ≤ n := hnData.2.2.two_le
  let Q := gsA10BetaSourceCutoff Cβ n
  let S := gsA10BetaSourceDepth Cβ
  have hraw := hlocal y X n Q S T hnWindow
    (by simpa only [Q] using hQ) (by simpa only [Q] using hQn)
    (by simpa only [S] using gsA10BetaSourceDepth_ge Cβ)
    (by simpa only [S] using
      log_le_two_mul_gsA10BetaSourceDepth_sub_div Cβ) hT
  have hdensity : gsA10PrimeRowBetaDensity Cβ Q S ≤
      gsA10BetaSourceDensityConstant Cβ / Real.log (n : ℝ) := by
    simpa only [Q, S] using
      gsA10PrimeRowBetaDensity_source_le hCβ hn2 hQ
  have hremainder : gsA10PrimeRowBetaRemainder Q S ≤
      (2 : ℝ) ^ (2 * S : ℕ) * (n : ℝ) ^ (1 / 8 : ℝ) := by
    simpa only [Q, S] using
      gsA10PrimeRowBetaRemainder_source_le_rpow Cβ (by omega : 1 ≤ n)
  have hweight : 0 ≤ 4 * Real.log ((4 * n : ℕ) : ℝ) / (n : ℝ) := by
    positivity
  calc
    (∑ m ∈ gsA10PrimeWindow y X,
        (Real.log (m : ℝ) / m) *
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n)) ≤
        (4 * Real.log ((4 * n : ℕ) : ℝ) / n) *
            (32 * ((4 * n : ℕ) : ℝ) / T *
                  gsA10PrimeRowBetaDensity Cβ Q S +
              6 * gsA10PrimeRowBetaDensity Cβ Q S +
              2 * gsA10PrimeRowBetaRemainder Q S) +
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2) (Real.log 4) *
            (Real.log (X : ℝ) +
              polynomialHeightPrimeLogMertensBound) := hraw
    _ ≤ (4 * Real.log ((4 * n : ℕ) : ℝ) / n) *
            (32 * ((4 * n : ℕ) : ℝ) / T *
                  (gsA10BetaSourceDensityConstant Cβ / Real.log (n : ℝ)) +
              6 * (gsA10BetaSourceDensityConstant Cβ / Real.log (n : ℝ)) +
              2 * ((2 : ℝ) ^ (2 * S : ℕ) *
                (n : ℝ) ^ (1 / 8 : ℝ))) +
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2) (Real.log 4) *
            (Real.log (X : ℝ) +
              polynomialHeightPrimeLogMertensBound) := by
      gcongr
    _ = _ := by rfl

/-- On a prime row, the local logarithm costs only a fixed factor relative
to `log n`. -/
theorem log_four_mul_le_three_mul_log_of_prime
    {n : ℕ} (hn : n.Prime) :
    Real.log ((4 * n : ℕ) : ℝ) ≤ 3 * Real.log (n : ℝ) := by
  have hn2 : 2 ≤ n := hn.two_le
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn.pos
  have hlog2n : Real.log (2 : ℝ) ≤ Real.log (n : ℝ) := by
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
  have hlogFour : Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [show (((4 * n : ℕ) : ℝ)) = (4 : ℝ) * (n : ℝ) by norm_num,
    Real.log_mul (by norm_num) hnpos.ne', hlogFour]
  linarith

/-- Exact scalar collapse of the row-local source terms.  This is the
quantitative reason for retaining both `log (4n)` and `1 / log n` until the
last step. -/
theorem gsA10Prime_source_local_terms_le_uniform
    {y X n : ℕ} {T C K : ℝ}
    (hnWindow : n ∈ gsA10PrimeWindow y X) (hy : 1 ≤ y)
    (hT : 0 < T) (hC : 0 ≤ C) (hK : 0 ≤ K) :
    (4 * Real.log ((4 * n : ℕ) : ℝ) / n) *
        (32 * ((4 * n : ℕ) : ℝ) / T *
              (C / Real.log (n : ℝ)) +
          6 * (C / Real.log (n : ℝ)) +
          2 * (K * (n : ℝ) ^ (1 / 8 : ℝ))) ≤
      1536 * C / T + 72 * C / y +
        8 * K * Real.log ((4 * X : ℕ) : ℝ) *
          (y : ℝ) ^ (-7 / 8 : ℝ) := by
  have hnData := mem_gsA10PrimeWindow.mp hnWindow
  have hyn : y ≤ n := hnData.1.le
  have hnposN : 0 < n := hnData.2.2.pos
  have hyposN : 0 < y := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hnposN
  have hypos : (0 : ℝ) < y := by exact_mod_cast hyposN
  have hlogn : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast hnData.2.2.one_lt)
  have hnXNat : n ≤ X :=
    hnData.2.1.le.trans (Nat.div_le_self X y)
  have hlogLocal := log_four_mul_le_three_mul_log_of_prime hnData.2.2
  have hW :
      4 * Real.log ((4 * n : ℕ) : ℝ) / (n : ℝ) ≤
        12 * Real.log (n : ℝ) / (n : ℝ) := by
    apply div_le_div_of_nonneg_right _ hnpos.le
    nlinarith
  have hlogX :
      Real.log ((4 * n : ℕ) : ℝ) ≤
        Real.log ((4 * X : ℕ) : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast (Nat.mul_le_mul_left 4 hnXNat)
  have hrpow :
      (n : ℝ) ^ (-7 / 8 : ℝ) ≤ (y : ℝ) ^ (-7 / 8 : ℝ) := by
    exact Real.rpow_le_rpow_of_nonpos hypos (by exact_mod_cast hyn) (by norm_num)
  have hquot :
      (n : ℝ) ^ (1 / 8 : ℝ) / (n : ℝ) =
        (n : ℝ) ^ (-7 / 8 : ℝ) := by
    calc
      (n : ℝ) ^ (1 / 8 : ℝ) / (n : ℝ) =
          (n : ℝ) ^ (1 / 8 : ℝ) / (n : ℝ) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = (n : ℝ) ^ ((1 / 8 : ℝ) - 1) :=
        (Real.rpow_sub hnpos _ _).symm
      _ = (n : ℝ) ^ (-7 / 8 : ℝ) := by norm_num
  have hA0 : 0 ≤ 32 * ((4 * n : ℕ) : ℝ) / T *
      (C / Real.log (n : ℝ)) := by positivity
  have hB0 : 0 ≤ 6 * (C / Real.log (n : ℝ)) := by positivity
  have hR0 : 0 ≤ 2 * (K * (n : ℝ) ^ (1 / 8 : ℝ)) := by positivity
  have hmain :
      (4 * Real.log ((4 * n : ℕ) : ℝ) / n) *
          (32 * ((4 * n : ℕ) : ℝ) / T *
            (C / Real.log (n : ℝ))) ≤
        1536 * C / T := by
    calc
      _ ≤ (12 * Real.log (n : ℝ) / n) *
          (32 * ((4 * n : ℕ) : ℝ) / T *
            (C / Real.log (n : ℝ))) :=
        mul_le_mul_of_nonneg_right hW hA0
      _ = 1536 * C / T := by
        norm_num only [Nat.cast_mul, Nat.cast_ofNat]
        field_simp [hnpos.ne', hlogn.ne', hT.ne']
        ring
  have hlower :
      (4 * Real.log ((4 * n : ℕ) : ℝ) / n) *
          (6 * (C / Real.log (n : ℝ))) ≤
        72 * C / y := by
    calc
      _ ≤ (12 * Real.log (n : ℝ) / n) *
          (6 * (C / Real.log (n : ℝ))) :=
        mul_le_mul_of_nonneg_right hW hB0
      _ = 72 * C / n := by
        field_simp [hnpos.ne', hlogn.ne']
        ring
      _ ≤ 72 * C / y :=
        div_le_div_of_nonneg_left (by positivity) hypos (by exact_mod_cast hyn)
  have hremainder :
      (4 * Real.log ((4 * n : ℕ) : ℝ) / n) *
          (2 * (K * (n : ℝ) ^ (1 / 8 : ℝ))) ≤
        8 * K * Real.log ((4 * X : ℕ) : ℝ) *
          (y : ℝ) ^ (-7 / 8 : ℝ) := by
    calc
      _ = 8 * K * Real.log ((4 * n : ℕ) : ℝ) *
          ((n : ℝ) ^ (1 / 8 : ℝ) / n) := by ring
      _ = 8 * K * Real.log ((4 * n : ℕ) : ℝ) *
          (n : ℝ) ^ (-7 / 8 : ℝ) := by rw [hquot]
      _ ≤ 8 * K * Real.log ((4 * X : ℕ) : ℝ) *
          (y : ℝ) ^ (-7 / 8 : ℝ) := by
        gcongr
  calc
    (4 * Real.log ((4 * n : ℕ) : ℝ) / n) *
        (32 * ((4 * n : ℕ) : ℝ) / T *
              (C / Real.log (n : ℝ)) +
          6 * (C / Real.log (n : ℝ)) +
          2 * (K * (n : ℝ) ^ (1 / 8 : ℝ))) =
      (4 * Real.log ((4 * n : ℕ) : ℝ) / n) *
          (32 * ((4 * n : ℕ) : ℝ) / T *
            (C / Real.log (n : ℝ))) +
        (4 * Real.log ((4 * n : ℕ) : ℝ) / n) *
          (6 * (C / Real.log (n : ℝ))) +
        (4 * Real.log ((4 * n : ℕ) : ℝ) / n) *
          (2 * (K * (n : ℝ) ^ (1 / 8 : ℝ))) := by ring
    _ ≤ 1536 * C / T + 72 * C / y +
        8 * K * Real.log ((4 * X : ℕ) : ℝ) *
          (y : ℝ) ^ (-7 / 8 : ℝ) := by linarith

/-- Uniform-in-the-row-centre form of the source-scheduled **near** row.
This is the source-sharp local contribution; it deliberately does not append
the older global fixed-gap far estimate. -/
theorem exists_sum_gsA10PrimeNearWindow_log_div_gaussian_source_uniform_bound :
    ∃ Cβ : ℝ, 1 ≤ Cβ ∧
      ∀ y X n : ℕ, ∀ T : ℝ,
        1 ≤ y → n ∈ gsA10PrimeWindow y X →
        3 ≤ gsA10BetaSourceCutoff Cβ n →
        gsA10BetaSourceCutoff Cβ n ≤ n / 4 → 0 < T →
        (∑ m ∈ gsA10PrimeNearWindow y X n,
            (Real.log (m : ℝ) / m) *
              finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
                (Real.log m - Real.log n)) ≤
          1536 * gsA10BetaSourceDensityConstant Cβ / T +
            72 * gsA10BetaSourceDensityConstant Cβ / y +
            8 * (2 : ℝ) ^
                (2 * gsA10BetaSourceDepth Cβ : ℕ) *
              Real.log ((4 * X : ℕ) : ℝ) *
                (y : ℝ) ^ (-7 / 8 : ℝ) := by
  obtain ⟨Cβ, hCβ, hlocal⟩ :=
    exists_sum_gsA10PrimeNearWindow_log_div_gaussian_source_local_bound
  refine ⟨Cβ, hCβ, ?_⟩
  intro y X n T hy hnWindow hQ hQn hT
  let C := gsA10BetaSourceDensityConstant Cβ
  let K := (2 : ℝ) ^ (2 * gsA10BetaSourceDepth Cβ : ℕ)
  have hC0 : 0 ≤ C := by
    dsimp only [C, gsA10BetaSourceDensityConstant]
    positivity
  have hK0 : 0 ≤ K := by positivity
  have hraw := hlocal y X n T hnWindow hQ hQn hT
  have hscalar := gsA10Prime_source_local_terms_le_uniform
    (T := T) (C := C) (K := K) hnWindow hy hT hC0 hK0
  exact hraw.trans (by simpa only [C, K] using hscalar)

/-- The row-local source cutoff is eventually below the lower endpoint
`n/4` of its near window. -/
theorem eventually_gsA10BetaSourceCutoff_le_quarter (Cβ : ℝ) :
    ∀ᶠ n : ℕ in atTop, gsA10BetaSourceCutoff Cβ n ≤ n / 4 := by
  filter_upwards [eventually_ge_atTop 64] with n hn64
  let S := gsA10BetaSourceDepth Cβ
  let u := gsA10BetaSourceExponent Cβ n
  let Q := gsA10BetaSourceCutoff Cβ n
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog0 : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hden2 : (2 : ℝ) ≤ (16 * S : ℕ) := by
    exact_mod_cast (show 2 ≤ 16 * S by
      dsimp only [S]
      have := gsA10BetaSourceDepth_pos Cβ
      omega)
  have hu : u ≤ Real.log (n : ℝ) / 2 := by
    dsimp only [u, gsA10BetaSourceExponent, S]
    exact div_le_div_of_nonneg_left hlog0 (by norm_num) hden2
  let a : ℝ := Real.exp (Real.log (n : ℝ) / 2)
  have hua : Real.exp u ≤ a := by
    exact Real.exp_le_exp.mpr hu
  have ha0 : 0 < a := Real.exp_pos _
  have hasq : a ^ 2 = (n : ℝ) := by
    dsimp only [a]
    calc
      Real.exp (Real.log (n : ℝ) / 2) ^ 2 =
          Real.exp (Real.log (n : ℝ) / 2 +
            Real.log (n : ℝ) / 2) := by rw [pow_two, ← Real.exp_add]
      _ = Real.exp (Real.log (n : ℝ)) := by ring_nf
      _ = (n : ℝ) := Real.exp_log hnpos
  have hn64R : (64 : ℝ) ≤ n := by exact_mod_cast hn64
  have ha8 : 8 ≤ a := by nlinarith [sq_nonneg (a - 8)]
  have hale : a ≤ (n : ℝ) / 8 := by
    rw [← hasq]
    nlinarith
  have hceil : (Q : ℝ) < Real.exp u + 1 := by
    dsimp only [Q, gsA10BetaSourceCutoff]
    exact Nat.ceil_lt_add_one (Real.exp_pos _).le
  have hQreal : (Q : ℝ) < (n : ℝ) / 4 := by
    calc
      (Q : ℝ) < Real.exp u + 1 := hceil
      _ ≤ a + 1 := add_le_add hua le_rfl
      _ ≤ (n : ℝ) / 8 + 1 := add_le_add hale le_rfl
      _ ≤ (n : ℝ) / 4 := by linarith
  have hmulReal : (4 : ℝ) * (Q : ℝ) < (n : ℝ) := by linarith
  have hmulNat : 4 * Q < n := by exact_mod_cast hmulReal
  simpa only [Q] using (show Q ≤ n / 4 by omega)

/-- Both structural cutoff conditions hold eventually at every row centre.-/
theorem eventually_gsA10BetaSourceRowStructural
    {Cβ : ℝ} (hCβ : 1 ≤ Cβ) :
    ∀ᶠ n : ℕ in atTop,
      3 ≤ gsA10BetaSourceCutoff Cβ n ∧
        gsA10BetaSourceCutoff Cβ n ≤ n / 4 := by
  filter_upwards [eventually_gsA10BetaSourceSchedule hCβ,
    eventually_gsA10BetaSourceCutoff_le_quarter Cβ] with n hs hquarter
  exact ⟨hs.1, hquarter⟩

/-- Threshold form convenient for a whole prime window: once its bottom
`y` exceeds `N`, every row centre `n > y` satisfies both cutoff conditions.-/
theorem exists_gsA10BetaSourceRowStructural_threshold
    {Cβ : ℝ} (hCβ : 1 ≤ Cβ) :
    ∃ N : ℕ, ∀ y n : ℕ, N ≤ y → y < n →
      3 ≤ gsA10BetaSourceCutoff Cβ n ∧
        gsA10BetaSourceCutoff Cβ n ≤ n / 4 := by
  have hs := eventually_gsA10BetaSourceRowStructural hCβ
  rw [eventually_atTop] at hs
  obtain ⟨N, hN⟩ := hs
  exact ⟨N, fun y n hNy hyn ↦ hN n (by omega)⟩

/-- Final eventual near-row interface: one threshold discharges both
row-local cutoff conditions simultaneously for every centre in the prime
window. -/
theorem exists_sum_gsA10PrimeNearWindow_log_div_gaussian_source_uniform_eventual_bound :
    ∃ Cβ : ℝ, ∃ N : ℕ, 1 ≤ Cβ ∧
      ∀ y X n : ℕ, ∀ T : ℝ,
        N ≤ y → n ∈ gsA10PrimeWindow y X → 0 < T →
        (∑ m ∈ gsA10PrimeNearWindow y X n,
            (Real.log (m : ℝ) / m) *
              finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
                (Real.log m - Real.log n)) ≤
          1536 * gsA10BetaSourceDensityConstant Cβ / T +
            72 * gsA10BetaSourceDensityConstant Cβ / y +
            8 * (2 : ℝ) ^
                (2 * gsA10BetaSourceDepth Cβ : ℕ) *
              Real.log ((4 * X : ℕ) : ℝ) *
                (y : ℝ) ^ (-7 / 8 : ℝ) := by
  obtain ⟨Cβ, hCβ, hrow⟩ :=
    exists_sum_gsA10PrimeNearWindow_log_div_gaussian_source_uniform_bound
  obtain ⟨N₀, hN₀⟩ := exists_gsA10BetaSourceRowStructural_threshold hCβ
  let N := max N₀ 1
  refine ⟨Cβ, N, hCβ, ?_⟩
  intro y X n T hNy hnWindow hT
  have hN₀y : N₀ ≤ y := (le_max_left N₀ 1).trans hNy
  have hy : 1 ≤ y := (le_max_right N₀ 1).trans hNy
  have hs := hN₀ y n hN₀y (mem_gsA10PrimeWindow.mp hnWindow).1
  exact hrow y X n T hy hnWindow hs.1 hs.2 hT

end

end Erdos67b.MRHalaszBands

#print axioms Erdos67b.MRHalaszBands.exists_sum_gsA10PrimeNearWindow_log_div_gaussian_local_beta_bound
#print axioms Erdos67b.MRHalaszBands.exists_sum_gsA10PrimeNearWindow_log_div_gaussian_source_local_bound
#print axioms Erdos67b.MRHalaszBands.exists_sum_gsA10PrimeWindow_log_div_gaussian_local_beta_bound
#print axioms Erdos67b.MRHalaszBands.exists_sum_gsA10PrimeWindow_log_div_gaussian_source_local_bound
#print axioms Erdos67b.MRHalaszBands.gsA10Prime_source_local_terms_le_uniform
#print axioms Erdos67b.MRHalaszBands.exists_sum_gsA10PrimeNearWindow_log_div_gaussian_source_uniform_bound
#print axioms Erdos67b.MRHalaszBands.eventually_gsA10BetaSourceCutoff_le_quarter
#print axioms Erdos67b.MRHalaszBands.exists_gsA10BetaSourceRowStructural_threshold
#print axioms Erdos67b.MRHalaszBands.exists_sum_gsA10PrimeNearWindow_log_div_gaussian_source_uniform_eventual_bound
