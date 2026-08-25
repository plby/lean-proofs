import ErdosProblems.Erdos67.MRGSA10PrimeVerticalCauchy
import ErdosProblems.Erdos67.MRGSA10LambdaWindowMassOrdinary

/-!
# Exact vertical split of the finite A.10 Lambda window

The actual generalized-Mangoldt window is split before any norm is taken.
Its prime part is exactly the polynomial controlled by the GHS weighted
Schur estimate; the remaining polynomial contains only higher prime powers.
-/

open scoped BigOperators LSeries.notation

namespace Erdos67.MRHalaszBands

noncomputable section

/-- Higher-prime-power counterpart of the prime Lambda coefficient. -/
def gsA10HigherPrimePowerLambdaCoefficient
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y : ℕ) (sigma : ℝ) (n : ℕ) : ℂ :=
  gsHigherPrimePowerPart (gsA9HighGeneralizedMangoldt hmul y) n *
    ((n : ℝ) ^ (-sigma) : ℝ)

def gsA10HigherPrimePowerLambdaPolynomial
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) (sigma t : ℝ) : ℂ :=
  logarithmicDirichletPolynomial (Finset.Ioo y (X / y))
    (gsA10HigherPrimePowerLambdaCoefficient hmul y sigma) t

/-- A finite A.10 Lambda window is exactly its logarithmic polynomial on a
vertical line.  Both endpoints are strict, matching the source definition. -/
theorem LSeries_gsA10LambdaWindow_eq_logarithmic
    (lambda : ArithmeticFunction ℂ) (y X : ℕ) (sigma t : ℝ) :
    LSeries (gsA10LambdaWindow lambda y X)
        ((sigma : ℂ) + Complex.I * (t : ℂ)) =
      logarithmicDirichletPolynomial (Finset.Ioo y (X / y))
        (fun n ↦ lambda n * Complex.ofReal ((n : ℝ) ^ (-sigma))) (-t) := by
  classical
  unfold LSeries logarithmicDirichletPolynomial
  rw [tsum_eq_sum (s := Finset.Ioo y (X / y))]
  · apply Finset.sum_congr rfl
    intro n hn
    have hnData := Finset.mem_Ioo.mp hn
    have hnpos : 0 < n := (Nat.zero_le y).trans_lt hnData.1
    rw [LSeries.term_of_ne_zero hnpos.ne', gsA10LambdaWindow_apply,
      if_pos hnData, div_eq_mul_inv, ← Complex.cpow_neg,
      ← ofReal_rpow_mul_logarithmicPhase_neg_eq_cpow_neg
        hnpos sigma t]
    ring
  · intro n hn
    by_cases hn0 : n = 0
    · subst n
      simp [gsA10LambdaWindow]
    · rw [LSeries.term_of_ne_zero hn0, gsA10LambdaWindow_apply]
      rw [if_neg]
      · simp
      · exact fun hwin ↦ hn (Finset.mem_Ioo.mpr hwin)

/-- The full finite vertical Lambda window is the exact sum of the prime
polynomial and the higher-prime-power polynomial. -/
theorem LSeries_gsA10LambdaWindow_eq_prime_add_higherPrimePower
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) (sigma t : ℝ) :
    LSeries
        (gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X)
        ((sigma : ℂ) + Complex.I * (t : ℂ)) =
      gsA10PrimeLambdaPolynomial hmul y X sigma (-t) +
        gsA10HigherPrimePowerLambdaPolynomial hmul y X sigma (-t) := by
  let lambda : ArithmeticFunction ℂ := gsA9HighGeneralizedMangoldt hmul y
  let prime : ArithmeticFunction ℂ := gsPrimePart lambda
  let hpp : ArithmeticFunction ℂ := gsHigherPrimePowerPart lambda
  have hlambda : lambda = prime + hpp :=
    gsA9HighGeneralizedMangoldt_eq_primePart_add_higherPrimePowerPart hmul y
  rw [LSeries_gsA10LambdaWindow_eq_logarithmic]
  unfold gsA10PrimeLambdaPolynomial gsA10PrimeLambdaCoefficient
  unfold gsA10HigherPrimePowerLambdaPolynomial
  unfold gsA10HigherPrimePowerLambdaCoefficient
  unfold logarithmicDirichletPolynomial
  unfold gsA10PrimeWindow
  rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hnData := Finset.mem_Ioo.mp hn
  have hnpos : 0 < n := (Nat.zero_le y).trans_lt hnData.1
  have hpoint : lambda n = prime n + hpp n := by
    simpa only [ArithmeticFunction.add_apply] using DFunLike.congr_fun hlambda n
  have hpoint' :
      gsA9HighGeneralizedMangoldt hmul y n =
        gsPrimePart (gsA9HighGeneralizedMangoldt hmul y) n +
          gsHigherPrimePowerPart (gsA9HighGeneralizedMangoldt hmul y) n := by
    simpa only [lambda, prime, hpp] using hpoint
  dsimp only
  rw [hpoint']
  by_cases hp : n.Prime
  · simp only [hp, if_true, gsPrimePart_apply]
    ring
  · simp only [hp, if_false, gsPrimePart_apply, zero_mul, zero_add]

/-- Uniform absolute bound for the higher-prime-power vertical polynomial.
The only left-line growth is the explicit top-of-window real power. -/
theorem norm_gsA10HigherPrimePowerLambdaPolynomial_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} (_hX : 2 ≤ X) (sigma t : ℝ) :
    ‖gsA10HigherPrimePowerLambdaPolynomial hmul y X sigma t‖ ≤
      ((X / y : ℕ) : ℝ) ^ (max (1 - sigma) 0) *
        gsA10HigherPrimePowerGeometricMass y X := by
  let D := Finset.Ioo y (X / y)
  let hpp := gsHigherPrimePowerPart (gsA9HighGeneralizedMangoldt hmul y)
  let rho := max (1 - sigma) 0
  let U : ℝ := (X / y : ℕ)
  have hrho : 0 ≤ rho := by dsimp only [rho]; exact le_max_right _ _
  have hpoint : ∀ n ∈ D,
      ‖gsA10HigherPrimePowerLambdaCoefficient hmul y sigma n‖ ≤
        U ^ rho * (‖hpp n‖ / (n : ℝ)) := by
    intro n hn
    have hnData := Finset.mem_Ioo.mp (by simpa only [D] using hn)
    have hnpos : (0 : ℝ) < n := by
      exact_mod_cast (show 0 < n from (Nat.zero_le y).trans_lt hnData.1)
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hnU : (n : ℝ) ≤ U := by
      dsimp only [U]
      exact_mod_cast hnData.2.le
    have hexp : 1 - sigma ≤ rho := by
      dsimp only [rho]
      exact le_max_left _ _
    have hnrho : (n : ℝ) ^ (1 - sigma) ≤ U ^ rho := by
      calc
        (n : ℝ) ^ (1 - sigma) ≤ (n : ℝ) ^ rho :=
          Real.rpow_le_rpow_of_exponent_le hnOne hexp
        _ ≤ U ^ rho := Real.rpow_le_rpow hnpos.le hnU hrho
    unfold gsA10HigherPrimePowerLambdaCoefficient
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hnpos.le _)]
    have hrpow :
        (n : ℝ) ^ (-sigma) =
          (n : ℝ)⁻¹ * (n : ℝ) ^ (1 - sigma) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hnpos]
      congr 1
      ring
    rw [hrpow]
    dsimp only [hpp]
    calc
      ‖gsHigherPrimePowerPart (gsA9HighGeneralizedMangoldt hmul y) n‖ *
          ((n : ℝ)⁻¹ * (n : ℝ) ^ (1 - sigma)) ≤
        ‖gsHigherPrimePowerPart (gsA9HighGeneralizedMangoldt hmul y) n‖ *
          ((n : ℝ)⁻¹ * U ^ rho) := by
        gcongr
      _ = U ^ rho *
          (‖gsHigherPrimePowerPart
              (gsA9HighGeneralizedMangoldt hmul y) n‖ / (n : ℝ)) := by
        rw [div_eq_mul_inv]
        ring
  have hsub : D ⊆ Finset.Icc 1 X := by
    intro n hn
    have hnData := Finset.mem_Ioo.mp (by simpa only [D] using hn)
    exact Finset.mem_Icc.mpr ⟨by omega,
      hnData.2.le.trans (Nat.div_le_self X y)⟩
  have hmass :
      (∑ n ∈ D, ‖hpp n‖ / (n : ℝ)) ≤
        gsA10HigherPrimePowerGeometricMass y X := by
    calc
      (∑ n ∈ D, ‖hpp n‖ / (n : ℝ)) ≤
          ∑ n ∈ Finset.Icc 1 X, ‖hpp n‖ / (n : ℝ) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun _ _ _ ↦ div_nonneg (norm_nonneg _) (by positivity))
      _ = ∑ n ∈ Finset.Icc 1 X,
          ‖gsRealShift 0 hpp n‖ / (n : ℝ) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hn0 : n ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
        rw [gsRealShift_apply_of_ne_zero 0 hpp hn0]
        simp
      _ ≤ gsA10HigherPrimePowerGeometricMass y X := by
        simpa only [hpp] using
          (sum_norm_shift_higherPrimePowerPart_div_le_mass
            hmul hbound (y := y) (X := X) (alpha := 0) le_rfl)
  unfold gsA10HigherPrimePowerLambdaPolynomial
  unfold logarithmicDirichletPolynomial
  calc
    ‖∑ n ∈ D,
        gsA10HigherPrimePowerLambdaCoefficient hmul y sigma n *
          logarithmicPhase n t‖ ≤
        ∑ n ∈ D,
          ‖gsA10HigherPrimePowerLambdaCoefficient hmul y sigma n *
            logarithmicPhase n t‖ := norm_sum_le _ _
    _ = ∑ n ∈ D,
          ‖gsA10HigherPrimePowerLambdaCoefficient hmul y sigma n‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [norm_mul, norm_logarithmicPhase, mul_one]
    _ ≤ ∑ n ∈ D, U ^ rho * (‖hpp n‖ / (n : ℝ)) :=
      Finset.sum_le_sum hpoint
    _ = U ^ rho * (∑ n ∈ D, ‖hpp n‖ / (n : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ U ^ rho * gsA10HigherPrimePowerGeometricMass y X :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := rfl

/-- The corresponding elementary absolute bound for the prime polynomial.
It is used only in error terms containing a higher prime power; the main
prime-by-prime term continues to use the sharp weighted-Schur estimate. -/
theorem norm_gsA10PrimeLambdaPolynomial_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} (hX : 2 ≤ X) (sigma t : ℝ) :
    ‖gsA10PrimeLambdaPolynomial hmul y X sigma t‖ ≤
      ((X / y : ℕ) : ℝ) ^ (max (1 - sigma) 0) *
        gsA10PrimeLambdaHarmonicBudget X := by
  let D := gsA10PrimeWindow y X
  let rho := max (1 - sigma) 0
  let U : ℝ := (X / y : ℕ)
  have hrho : 0 ≤ rho := by dsimp only [rho]; exact le_max_right _ _
  have hpoint : ∀ n ∈ D,
      ‖gsA10PrimeLambdaCoefficient hmul y sigma n‖ ≤
        U ^ rho *
          (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-1 : ℝ)) := by
    intro n hn
    have hn' : n ∈ gsA10PrimeWindow y X := by simpa only [D] using hn
    have hnData := mem_gsA10PrimeWindow.mp hn'
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hnData.2.2.pos
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hnData.2.2.one_le
    have hnU : (n : ℝ) ≤ U := by
      dsimp only [U]
      exact_mod_cast hnData.2.1.le
    have hexp : 1 - sigma ≤ rho := by
      dsimp only [rho]
      exact le_max_left _ _
    have hpow :
        (n : ℝ) ^ (-sigma) ≤ U ^ rho * (n : ℝ) ^ (-1 : ℝ) := by
      have hnrho : (n : ℝ) ^ (1 - sigma) ≤ U ^ rho := by
        calc
          (n : ℝ) ^ (1 - sigma) ≤ (n : ℝ) ^ rho :=
            Real.rpow_le_rpow_of_exponent_le hnOne hexp
          _ ≤ U ^ rho := Real.rpow_le_rpow hnpos.le hnU hrho
      have hid :
          (n : ℝ) ^ (-sigma) =
            (n : ℝ) ^ (-1 : ℝ) * (n : ℝ) ^ (1 - sigma) := by
        rw [← Real.rpow_add hnpos]
        congr 1
        ring
      rw [hid]
      calc
        (n : ℝ) ^ (-1 : ℝ) * (n : ℝ) ^ (1 - sigma) ≤
            (n : ℝ) ^ (-1 : ℝ) * U ^ rho :=
          mul_le_mul_of_nonneg_left hnrho (by positivity)
        _ = _ := by ring
    unfold gsA10PrimeLambdaCoefficient
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hnpos.le _)]
    calc
      ‖gsPrimePart (gsA9HighGeneralizedMangoldt hmul y) n‖ *
          (n : ℝ) ^ (-sigma) ≤
        ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-sigma) :=
          mul_le_mul_of_nonneg_right
            (norm_gsPrimePart_highGeneralizedMangoldt_le_vonMangoldt
              hmul hbound y n) (by positivity)
      _ ≤ ArithmeticFunction.vonMangoldt n *
          (U ^ rho * (n : ℝ) ^ (-1 : ℝ)) :=
        mul_le_mul_of_nonneg_left hpow ArithmeticFunction.vonMangoldt_nonneg
      _ = _ := by ring
  unfold gsA10PrimeLambdaPolynomial logarithmicDirichletPolynomial
  calc
    ‖∑ n ∈ D, gsA10PrimeLambdaCoefficient hmul y sigma n *
        logarithmicPhase n t‖ ≤
        ∑ n ∈ D,
          ‖gsA10PrimeLambdaCoefficient hmul y sigma n *
            logarithmicPhase n t‖ := norm_sum_le _ _
    _ = ∑ n ∈ D, ‖gsA10PrimeLambdaCoefficient hmul y sigma n‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [norm_mul, norm_logarithmicPhase, mul_one]
    _ ≤ ∑ n ∈ D, U ^ rho *
          (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-1 : ℝ)) :=
      Finset.sum_le_sum hpoint
    _ = U ^ rho *
        (∑ n ∈ D,
          ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-1 : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ U ^ rho * gsA10PrimeLambdaHarmonicBudget X :=
      mul_le_mul_of_nonneg_left
        (by simpa only [D] using
          (sum_vonMangoldt_rpow_neg_one_primeWindow_le
            (y := y) hX)) (by positivity)
    _ = _ := rfl

def gsA10PrimeLambdaAbsoluteBudget
    (y X : ℕ) (sigma : ℝ) : ℝ :=
  ((X / y : ℕ) : ℝ) ^ (max (1 - sigma) 0) *
    gsA10PrimeLambdaHarmonicBudget X

def gsA10HigherPrimePowerLambdaAbsoluteBudget
    (y X : ℕ) (sigma : ℝ) : ℝ :=
  ((X / y : ℕ) : ℝ) ^ (max (1 - sigma) 0) *
    gsA10HigherPrimePowerGeometricMass y X

/-- The three terms containing at least one higher prime power after
expanding the product of two actual Lambda windows. -/
def gsA10LambdaVerticalSplitError
    (y X : ℕ) (sigma₁ sigma₂ : ℝ) : ℝ :=
  gsA10PrimeLambdaAbsoluteBudget y X sigma₁ *
      gsA10HigherPrimePowerLambdaAbsoluteBudget y X sigma₂ +
    gsA10HigherPrimePowerLambdaAbsoluteBudget y X sigma₁ *
      gsA10PrimeLambdaAbsoluteBudget y X sigma₂ +
    gsA10HigherPrimePowerLambdaAbsoluteBudget y X sigma₁ *
      gsA10HigherPrimePowerLambdaAbsoluteBudget y X sigma₂

theorem norm_LSeries_gsA10LambdaWindow_product_sub_primeProduct_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} (hX : 2 ≤ X) (sigma₁ sigma₂ t : ℝ) :
    ‖LSeries
          (gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X)
          ((sigma₁ : ℂ) + Complex.I * (t : ℂ)) *
        LSeries
          (gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X)
          ((sigma₂ : ℂ) + Complex.I * (t : ℂ)) -
        gsA10PrimeLambdaPolynomial hmul y X sigma₁ (-t) *
          gsA10PrimeLambdaPolynomial hmul y X sigma₂ (-t)‖ ≤
      gsA10LambdaVerticalSplitError y X sigma₁ sigma₂ := by
  let P₁ := gsA10PrimeLambdaPolynomial hmul y X sigma₁ (-t)
  let P₂ := gsA10PrimeLambdaPolynomial hmul y X sigma₂ (-t)
  let H₁ := gsA10HigherPrimePowerLambdaPolynomial hmul y X sigma₁ (-t)
  let H₂ := gsA10HigherPrimePowerLambdaPolynomial hmul y X sigma₂ (-t)
  have hsplit₁ := LSeries_gsA10LambdaWindow_eq_prime_add_higherPrimePower
    hmul y X sigma₁ t
  have hsplit₂ := LSeries_gsA10LambdaWindow_eq_prime_add_higherPrimePower
    hmul y X sigma₂ t
  have hP₁ : ‖P₁‖ ≤ gsA10PrimeLambdaAbsoluteBudget y X sigma₁ := by
    simpa only [P₁, gsA10PrimeLambdaAbsoluteBudget] using
      norm_gsA10PrimeLambdaPolynomial_le hmul hbound hX sigma₁ (-t)
  have hP₂ : ‖P₂‖ ≤ gsA10PrimeLambdaAbsoluteBudget y X sigma₂ := by
    simpa only [P₂, gsA10PrimeLambdaAbsoluteBudget] using
      norm_gsA10PrimeLambdaPolynomial_le hmul hbound hX sigma₂ (-t)
  have hH₁ : ‖H₁‖ ≤
      gsA10HigherPrimePowerLambdaAbsoluteBudget y X sigma₁ := by
    simpa only [H₁, gsA10HigherPrimePowerLambdaAbsoluteBudget] using
      norm_gsA10HigherPrimePowerLambdaPolynomial_le
        hmul hbound hX sigma₁ (-t)
  have hH₂ : ‖H₂‖ ≤
      gsA10HigherPrimePowerLambdaAbsoluteBudget y X sigma₂ := by
    simpa only [H₂, gsA10HigherPrimePowerLambdaAbsoluteBudget] using
      norm_gsA10HigherPrimePowerLambdaPolynomial_le
        hmul hbound hX sigma₂ (-t)
  have hP₁0 : 0 ≤ gsA10PrimeLambdaAbsoluteBudget y X sigma₁ :=
    (norm_nonneg P₁).trans hP₁
  have hP₂0 : 0 ≤ gsA10PrimeLambdaAbsoluteBudget y X sigma₂ :=
    (norm_nonneg P₂).trans hP₂
  have hH₁0 : 0 ≤ gsA10HigherPrimePowerLambdaAbsoluteBudget y X sigma₁ :=
    (norm_nonneg H₁).trans hH₁
  have hH₂0 : 0 ≤ gsA10HigherPrimePowerLambdaAbsoluteBudget y X sigma₂ :=
    (norm_nonneg H₂).trans hH₂
  rw [hsplit₁, hsplit₂]
  change ‖(P₁ + H₁) * (P₂ + H₂) - P₁ * P₂‖ ≤ _
  rw [show (P₁ + H₁) * (P₂ + H₂) - P₁ * P₂ =
      P₁ * H₂ + H₁ * P₂ + H₁ * H₂ by ring]
  calc
    ‖P₁ * H₂ + H₁ * P₂ + H₁ * H₂‖ ≤
        ‖P₁ * H₂‖ + ‖H₁ * P₂‖ + ‖H₁ * H₂‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add_left (norm_add_le _ _) _)
    _ = ‖P₁‖ * ‖H₂‖ + ‖H₁‖ * ‖P₂‖ + ‖H₁‖ * ‖H₂‖ := by
      rw [norm_mul, norm_mul, norm_mul]
    _ ≤ _ := by
      unfold gsA10LambdaVerticalSplitError
      gcongr

/-- Integrated form of the higher-prime-power correction.  It is entirely
finite and costs only the interval length; the prime-by-prime main term is
left untouched for the weighted-Schur/Cauchy estimate. -/
theorem norm_intervalIntegral_mul_LambdaWindowProduct_sub_primeProduct_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} (hX : 2 ≤ X) (sigma₁ sigma₂ : ℝ)
    {T M : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M)
    (F : ℝ → ℂ) (hF : ∀ t, |t| ≤ T → ‖F t‖ ≤ M) :
    ‖∫ t in -T..T,
        F t *
          (LSeries
              (gsA10LambdaWindow
                (gsA9HighGeneralizedMangoldt hmul y) y X)
              ((sigma₁ : ℂ) + Complex.I * (t : ℂ)) *
            LSeries
              (gsA10LambdaWindow
                (gsA9HighGeneralizedMangoldt hmul y) y X)
              ((sigma₂ : ℂ) + Complex.I * (t : ℂ)) -
            gsA10PrimeLambdaPolynomial hmul y X sigma₁ (-t) *
              gsA10PrimeLambdaPolynomial hmul y X sigma₂ (-t))‖ ≤
      2 * T * M * gsA10LambdaVerticalSplitError y X sigma₁ sigma₂ := by
  let E := gsA10LambdaVerticalSplitError y X sigma₁ sigma₂
  have hpoint (t : ℝ) (ht : t ∈ Set.uIoc (-T) T) :
      ‖F t *
          (LSeries
              (gsA10LambdaWindow
                (gsA9HighGeneralizedMangoldt hmul y) y X)
              ((sigma₁ : ℂ) + Complex.I * (t : ℂ)) *
            LSeries
              (gsA10LambdaWindow
                (gsA9HighGeneralizedMangoldt hmul y) y X)
              ((sigma₂ : ℂ) + Complex.I * (t : ℂ)) -
            gsA10PrimeLambdaPolynomial hmul y X sigma₁ (-t) *
              gsA10PrimeLambdaPolynomial hmul y X sigma₂ (-t))‖ ≤ M * E := by
    rw [Set.uIoc_of_le (by linarith : -T ≤ T)] at ht
    have habs : |t| ≤ T := abs_le.mpr ⟨ht.1.le, ht.2⟩
    have hsplit :
        ‖LSeries
              (gsA10LambdaWindow
                (gsA9HighGeneralizedMangoldt hmul y) y X)
              ((sigma₁ : ℂ) + Complex.I * (t : ℂ)) *
            LSeries
              (gsA10LambdaWindow
                (gsA9HighGeneralizedMangoldt hmul y) y X)
              ((sigma₂ : ℂ) + Complex.I * (t : ℂ)) -
            gsA10PrimeLambdaPolynomial hmul y X sigma₁ (-t) *
              gsA10PrimeLambdaPolynomial hmul y X sigma₂ (-t)‖ ≤ E := by
      simpa only [E] using
        (norm_LSeries_gsA10LambdaWindow_product_sub_primeProduct_le
          hmul hbound hX sigma₁ sigma₂ t)
    rw [norm_mul]
    exact mul_le_mul (hF t habs) hsplit (norm_nonneg _) hM
  have hraw := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t : ℝ ↦
      F t *
        (LSeries
            (gsA10LambdaWindow
              (gsA9HighGeneralizedMangoldt hmul y) y X)
            ((sigma₁ : ℂ) + Complex.I * (t : ℂ)) *
          LSeries
            (gsA10LambdaWindow
              (gsA9HighGeneralizedMangoldt hmul y) y X)
            ((sigma₂ : ℂ) + Complex.I * (t : ℂ)) -
          gsA10PrimeLambdaPolynomial hmul y X sigma₁ (-t) *
            gsA10PrimeLambdaPolynomial hmul y X sigma₂ (-t)))
    (C := M * E) (a := -T) (b := T) hpoint
  calc
    _ ≤ (M * E) * |T - -T| := hraw
    _ = 2 * T * M * gsA10LambdaVerticalSplitError y X sigma₁ sigma₂ := by
      rw [show T - -T = 2 * T by ring, abs_of_nonneg (by positivity)]
      dsimp only [E]
      ring

end

end Erdos67.MRHalaszBands

#print axioms Erdos67.MRHalaszBands.LSeries_gsA10LambdaWindow_eq_prime_add_higherPrimePower
#print axioms Erdos67.MRHalaszBands.norm_gsA10HigherPrimePowerLambdaPolynomial_le
#print axioms Erdos67.MRHalaszBands.norm_LSeries_gsA10LambdaWindow_product_sub_primeProduct_le
#print axioms Erdos67.MRHalaszBands.norm_intervalIntegral_mul_LambdaWindowProduct_sub_primeProduct_le
