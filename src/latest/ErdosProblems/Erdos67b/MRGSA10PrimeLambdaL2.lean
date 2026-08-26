import ErdosProblems.Erdos67b.MRGSA10PrimeGaussianNearRow
import ErdosProblems.Erdos67b.MRGSA10GaussianSchurWeighted
import ErdosProblems.Erdos67b.MRGSA10SecondSecondaryPrimeChebyshev

/-!
# GHS-type vertical mean square for the prime Lambda window

This module combines the short-prime Gaussian row with a weighted Schur
test.  The result is the finite, ordinary-multiplicative prime part of the
GHS Lemma 2.6 input used in GS Appendix A.10.  The final weighted diagonal
sum is intentionally kept explicit; this is the source form
`sum n |a(n)|^2 Lambda(n)` and is scalarized only after pairing the two
opposite real shifts.
-/

open scoped BigOperators

namespace Erdos67b.MRHalaszBands

noncomputable section

/-- Prime part of the shifted A.10 generalized-Mangoldt polynomial. -/
def gsA10PrimeLambdaCoefficient
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y : ℕ) (sigma : ℝ) (n : ℕ) : ℂ :=
  gsPrimePart (gsA9HighGeneralizedMangoldt hmul y) n *
    ((n : ℝ) ^ (-sigma) : ℝ)

def gsA10PrimeLambdaPolynomial
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) (sigma t : ℝ) : ℂ :=
  logarithmicDirichletPolynomial (gsA10PrimeWindow y X)
    (gsA10PrimeLambdaCoefficient hmul y sigma) t

/-- Schur diagonal weight associated to the exact prime coefficient. -/
def gsA10PrimeLambdaSchurWeight
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y : ℕ) (sigma : ℝ) (n : ℕ) : ℝ :=
  ‖gsA10PrimeLambdaCoefficient hmul y sigma n‖ ^ 2 /
    (Real.log (n : ℝ) / n)

/-- Explicit row bound produced by the near beta sieve and far Gaussian
tail. -/
def gsA10PrimeGaussianRowBound
    (Cβ : ℝ) (Q S y X : ℕ) (T : ℝ) : ℝ :=
  16 * Real.log (X : ℝ) *
      (32 / T * gsA10PrimeRowBetaDensity Cβ Q S) +
    (4 * Real.log (X : ℝ) / (y : ℝ)) *
      (6 * gsA10PrimeRowBetaDensity Cβ Q S +
        2 * gsA10PrimeRowBetaRemainder Q S) +
    finiteHalaszGaussianPairKernel (T⁻¹ ^ 2) (Real.log 4) *
      (Real.log (X : ℝ) + polynomialHeightPrimeLogMertensBound)

/-- Weighted AM--GM in the exact quotient form used by the Schur test. -/
theorem mul_le_weighted_square_average
    {A B u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    A * B ≤ ((A ^ 2 / u) * v + (B ^ 2 / v) * u) / 2 := by
  have heps : 0 < v / u := div_pos hv hu
  have h := two_mul_le_add_mul_sq (a := A) (b := B) heps
  have hfirst : (v / u) * A ^ 2 = (A ^ 2 / u) * v := by
    field_simp
  have hsecond : (v / u)⁻¹ * B ^ 2 = (B ^ 2 / v) * u := by
    rw [inv_div]
    field_simp
  rw [hfirst, hsecond] at h
  linarith

/-- The concrete row theorem can be made uniform in its base prime by
discarding the harmless factors `n/n`. -/
theorem exists_uniform_gsA10PrimeGaussianRow_beta_bound :
    ∃ Cβ : ℝ, 1 ≤ Cβ ∧
      ∀ y X Q S : ℕ, ∀ T : ℝ,
        3 ≤ Q → Q ≤ y → 101 ≤ S →
        Real.log Cβ ≤ 2 * (S - 100 : ℕ) / 99 → 0 < T →
        ∀ n ∈ gsA10PrimeWindow y X,
        (∑ m ∈ gsA10PrimeWindow y X,
            (Real.log (m : ℝ) / m) *
              finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
                (Real.log m - Real.log n)) ≤
          gsA10PrimeGaussianRowBound Cβ Q S y X T := by
  obtain ⟨Cβ, hCβ, hrow⟩ :=
    exists_sum_gsA10PrimeWindow_log_div_gaussian_beta_bound
  refine ⟨Cβ, hCβ, ?_⟩
  intro y X Q S T hQ hQy hS hlog hT n hn
  have hraw := hrow y X n Q S T hn hQ hQy hS hlog hT
  have hnData := mem_gsA10PrimeWindow.mp hn
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n from (Nat.zero_le y).trans_lt hnData.1)
  have hlogX : 0 ≤ Real.log (X : ℝ) := by
    have hnX : n ≤ X := hnData.2.1.le.trans (Nat.div_le_self X y)
    exact Real.log_nonneg (by exact_mod_cast
      (show 1 ≤ X from hnData.2.2.one_le.trans hnX))
  unfold gsA10PrimeGaussianRowBound
  calc
    _ ≤ (4 * Real.log (X : ℝ) / n) *
          (32 * ((4 * n : ℕ) : ℝ) / T *
                gsA10PrimeRowBetaDensity Cβ Q S +
            6 * gsA10PrimeRowBetaDensity Cβ Q S +
            2 * gsA10PrimeRowBetaRemainder Q S) +
        finiteHalaszGaussianPairKernel (T⁻¹ ^ 2) (Real.log 4) *
          (Real.log (X : ℝ) +
            polynomialHeightPrimeLogMertensBound) := hraw
    _ = 16 * Real.log (X : ℝ) *
          (32 / T * gsA10PrimeRowBetaDensity Cβ Q S) +
        (4 * Real.log (X : ℝ) / n) *
          (6 * gsA10PrimeRowBetaDensity Cβ Q S +
            2 * gsA10PrimeRowBetaRemainder Q S) +
        finiteHalaszGaussianPairKernel (T⁻¹ ^ 2) (Real.log 4) *
          (Real.log (X : ℝ) +
            polynomialHeightPrimeLogMertensBound) := by
      push_cast
      field_simp
      ring
    _ ≤ 16 * Real.log (X : ℝ) *
          (32 / T * gsA10PrimeRowBetaDensity Cβ Q S) +
        (4 * Real.log (X : ℝ) / (y : ℝ)) *
          (6 * gsA10PrimeRowBetaDensity Cβ Q S +
            2 * gsA10PrimeRowBetaRemainder Q S) +
        finiteHalaszGaussianPairKernel (T⁻¹ ^ 2) (Real.log 4) *
          (Real.log (X : ℝ) +
            polynomialHeightPrimeLogMertensBound) := by
      have hcoef :
          4 * Real.log (X : ℝ) / (n : ℝ) ≤
            4 * Real.log (X : ℝ) / (y : ℝ) := by
        exact div_le_div_of_nonneg_left
          (mul_nonneg (by norm_num) hlogX)
          (by exact_mod_cast (show 0 < y by omega))
          (by exact_mod_cast hnData.1.le)
      have hfactor :
          0 ≤ 6 * gsA10PrimeRowBetaDensity Cβ Q S +
            2 * gsA10PrimeRowBetaRemainder Q S := by
        have hdensity : 0 ≤ gsA10PrimeRowBetaDensity Cβ Q S := by
          unfold gsA10PrimeRowBetaDensity
          exact mul_nonneg (by positivity) (primeBlockDensity_nonneg _)
        have hremainder : 0 ≤ gsA10PrimeRowBetaRemainder Q S := by
          unfold gsA10PrimeRowBetaRemainder
          positivity
        positivity
      exact add_le_add_left
        (add_le_add_right (mul_le_mul_of_nonneg_right hcoef hfactor) _) _

/-- Prime-part GHS mean square with the exact weighted diagonal sum.
This is the first contour-ready L2 theorem: it has no ambient-support
cardinality loss. -/
theorem exists_intervalIntegral_normSq_gsA10PrimeLambdaPolynomial_le_betaSchur :
    ∃ Cβ : ℝ, 1 ≤ Cβ ∧
      ∀ {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
        (y X Q S : ℕ) (sigma T : ℝ),
        3 ≤ Q → Q ≤ y → 101 ≤ S →
        Real.log Cβ ≤ 2 * (S - 100 : ℕ) / 99 → 0 < T →
        (∫ t in -T..T,
            Complex.normSq
              (gsA10PrimeLambdaPolynomial hmul y X sigma t)) ≤
          Real.exp 1 *
            (Real.sqrt (Real.pi / (T⁻¹ ^ 2)) *
              (gsA10PrimeGaussianRowBound Cβ Q S y X T *
                ∑ n ∈ gsA10PrimeWindow y X,
                  gsA10PrimeLambdaSchurWeight hmul y sigma n)) := by
  obtain ⟨Cβ, hCβ, hrow⟩ :=
    exists_uniform_gsA10PrimeGaussianRow_beta_bound
  refine ⟨Cβ, hCβ, ?_⟩
  intro f hmul y X Q S sigma T hQ hQy hS hlog hT
  let D := gsA10PrimeWindow y X
  let a := gsA10PrimeLambdaCoefficient hmul y sigma
  let q := gsA10PrimeLambdaSchurWeight hmul y sigma
  let w : ℕ → ℝ := fun n ↦ Real.log (n : ℝ) / n
  let R := gsA10PrimeGaussianRowBound Cβ Q S y X T
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
        (Real.log m - Real.log n)) ≤ R := by
    intro n hn
    simpa only [D, w, R] using
      hrow y X Q S T hQ hQy hS hlog hT n (by simpa only [D] using hn)
  have hmajor := finiteHalaszLogGaussianPairMajorant_le_weightedSchur
    D a q w (sq_pos_of_pos (inv_pos.mpr hT)) hq hw hpair hrow'
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
          (R * ∑ n ∈ D, q n)) :=
      mul_le_mul_of_nonneg_left hmajor (Real.exp_pos 1).le
    _ = _ := rfl

end

end Erdos67b.MRHalaszBands

#print axioms Erdos67b.MRHalaszBands.exists_intervalIntegral_normSq_gsA10PrimeLambdaPolynomial_le_betaSchur
