import ErdosProblems.Erdos239.External.Erdos67.MRGSA10FiniteMassScalar
import ErdosProblems.Erdos239.External.Erdos67.MRGSA9SourceRadius
import ErdosProblems.Erdos239.External.Erdos67.MRGSA9ZetaMajorant
import ErdosProblems.Erdos239.External.Erdos67.MRGSRiemannZetaUpper

/-!
# Scalar bound for the finite low-prime mass in GS A.10

The low norm-Dirichlet mass is first dominated coefficientwise by the
positive low-prime Euler product.  The finitely many primes below `23` are
absorbed absolutely.  On all remaining primes, the source horizontal-shift
estimate moves `1-alpha` to `1+1/log y` at constant cost.  The latter product
is bounded by the pole-size estimate for zeta, leaving exactly `O(log y)`.
-/

open scoped BigOperators LSeries.notation ComplexOrder

namespace Erdos67.MRHalaszBands

noncomputable section

private theorem one_multiplicative_lowScalar :
    IsMultiplicativeOnPositiveNat (fun _ : ℕ ↦ (1 : ℂ)) := by
  constructor <;> simp

private theorem one_bounded_lowScalar :
    ∀ n : ℕ, 0 < n → ‖(1 : ℂ)‖ ≤ 1 := by simp

/-- The fixed universal multiplicative constant in the low-mass estimate. -/
def gsA10FiniteLowMassConstant : ℝ :=
  gsA9SmallPrimeEulerBound * Real.exp (6 * gsA9SourceShiftConstant)

private theorem gsA9SmallPrimeEulerBound_nonneg :
    0 ≤ gsA9SmallPrimeEulerBound := by
  unfold gsA9SmallPrimeEulerBound
  apply Finset.prod_nonneg
  intro p hp
  exact inv_nonneg.mpr (sub_nonneg.mpr (by
    have hpPrime := (Finset.mem_filter.mp hp).2
    exact (Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast hpPrime.one_le)
      (by norm_num : (-(1 / 2 : ℝ)) ≤ 0))))

theorem gsA10FiniteLowMassConstant_nonneg :
    0 ≤ gsA10FiniteLowMassConstant := by
  unfold gsA10FiniteLowMassConstant gsA9SmallPrimeEulerBound
  apply mul_nonneg
  · exact gsA9SmallPrimeEulerBound_nonneg
  · positivity

/-- The alternating low coefficient is majorized by the positive low Euler
series on every positive real line.  All parameters are explicit so this
lemma elaborates without the expensive higher-order unification of the
generic majorant. -/
theorem gsFiniteNormDirichletMass_twoBlockAlternatingLow_le_positive_LSeries_explicit
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ}
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    gsFiniteNormDirichletMass
        (gsA10TwoBlockAlternatingLow f P₁ P₂ y) X sigma ≤
      ‖LSeries (gsA9Low (fun _ : ℕ ↦ (1 : ℂ)) y) (sigma : ℂ)‖ := by
  let a : ArithmeticFunction ℂ :=
    toArithmeticFunction (gsA9Low (fun _ : ℕ ↦ (1 : ℂ)) y)
  let b : ArithmeticFunction ℂ :=
    gsA10TwoBlockAlternatingLow f P₁ P₂ y
  have hsumFn : LSeriesSummable
      (gsA9Low (fun _ : ℕ ↦ (1 : ℂ)) y) (sigma : ℂ) :=
    primeBandCoefficient_LSeriesSummable_of_pos_re
      one_multiplicative_lowScalar one_bounded_lowScalar
      (fun p ↦ p ≤ y) y (fun _ hp ↦ hp) (by simpa using hsigma)
  have hsum : LSeriesSummable a (sigma : ℂ) := by
    apply (LSeriesSummable_congr (sigma : ℂ) (f := a)
      (g := gsA9Low (fun _ : ℕ ↦ (1 : ℂ)) y) ?_).2 hsumFn
    intro n hn
    simp [a, toArithmeticFunction, hn]
  have haNonneg : ∀ n, 0 ≤ a n := by
    intro n
    change 0 ≤ if n = 0 then 0 else
      gsA9Low (fun _ : ℕ ↦ (1 : ℂ)) y n
    split_ifs
    · simp
    · unfold gsA9Low primeBandCoefficient
      split_ifs <;> simp
  have hmajor : ∀ n ∈ Finset.Icc 1 X, ‖b n‖ ≤ ‖a n‖ := by
    intro n hn
    have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
    by_cases hsupp : PrimeSupported (fun p ↦ p ≤ y) n
    · have hlow := norm_gsA10TwoBlockAlternatingLow_le_one
        hmul hbound P₁ P₂ y hQ₂ hQ₃ n hnpos
      simpa [a, b, toArithmeticFunction, hnpos.ne', gsA9Low,
        primeBandCoefficient, hsupp] using hlow
    · rw [show b n = 0 by
          exact gsA10TwoBlockAlternatingLow_eq_zero_of_not_lowSupported
            f P₁ P₂ y hnpos.ne' hsupp]
      simp
  have hraw := gsFiniteNormDirichletMass_le_norm_LSeries_of_major
    (a := a) (b := b) (X := X) (sigma := sigma) hsum haNonneg hmajor
  have hseries : LSeries a (sigma : ℂ) =
      LSeries (gsA9Low (fun _ : ℕ ↦ (1 : ℂ)) y) (sigma : ℂ) := by
    apply LSeries_congr
    intro n hn
    simp [a, toArithmeticFunction, hn]
  simpa only [b, hseries] using hraw

/-- Source-uniform scalar estimate for the finite alternating low mass. -/
theorem gsFiniteNormDirichletMass_twoBlockAlternatingLow_le_sourceConstant
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hy : 23 ≤ y)
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    {alpha : ℝ} (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹) :
    gsFiniteNormDirichletMass
        (gsA10TwoBlockAlternatingLow f P₁ P₂ y) X (1 - alpha) ≤
      gsA10FiniteLowMassConstant * (1 + Real.log (y : ℝ)) := by
  let eta : ℝ := (Real.log (y : ℝ))⁻¹
  let sigmaLow : ℝ := 1 - alpha
  let sigmaHigh : ℝ := 1 + eta
  let S : Finset ℕ := gsA9LargePrimesUpTo y
  let one : ℕ → ℂ := fun _ ↦ 1
  have hy2 : 2 ≤ y := by omega
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have heta : 0 < eta := inv_pos.mpr hlog
  have hexpTwo : Real.exp 2 < (y : ℝ) := by
    calc
      Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      _ < 3 * 3 := by
        nlinarith [Real.exp_pos 1, Real.exp_one_lt_three]
      _ < 23 := by norm_num
      _ ≤ y := by exact_mod_cast hy
  have hlogTwo : 2 < Real.log (y : ℝ) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    exact hexpTwo
  have hetaHalf : eta ≤ 1 / 2 := by
    dsimp only [eta]
    have hinv := inv_anti₀ (by norm_num : (0 : ℝ) < 2) hlogTwo.le
    norm_num at hinv ⊢
    exact hinv
  have hsigmaHalf : 1 / 2 ≤ sigmaLow := by
    dsimp only [sigmaLow]
    linarith
  have hsigmaPos : 0 < sigmaLow := lt_of_lt_of_le (by norm_num) hsigmaHalf
  have hsigmaHigh : 1 < sigmaHigh := by dsimp only [sigmaHigh]; linarith
  have hle : sigmaLow ≤ sigmaHigh := by
    dsimp only [sigmaLow, sigmaHigh]
    linarith
  have htwoEta : 2 / Real.log (y : ℝ) = 2 * eta := by
    dsimp only [eta]
    rw [div_eq_mul_inv]
  have hsigmaSource : 1 - 2 / Real.log (y : ℝ) ≤ sigmaLow := by
    rw [htwoEta]
    dsimp only [sigmaLow]
    linarith
  have hgap : sigmaHigh - sigmaLow ≤ 3 / Real.log (y : ℝ) := by
    rw [show 3 / Real.log (y : ℝ) = 3 * eta by
      dsimp only [eta]; rw [div_eq_mul_inv]]
    dsimp only [sigmaHigh, sigmaLow]
    linarith
  have hmass :=
    gsFiniteNormDirichletMass_twoBlockAlternatingLow_le_positive_LSeries_explicit
      hmul hbound P₁ P₂ (y := y) (X := X) hQ₂ hQ₃
        (sigma := sigmaLow) hsigmaPos
  have hEulerLow :
      LSeries (gsA9Low one y) (sigmaLow : ℂ) =
        ∏ p ∈ primesUpTo y,
          gsA9LocalEulerFactor one (sigmaLow : ℂ) p :=
    LSeries_gsA9Low_eq_finiteEulerProduct_of_pos_re
      one_multiplicative_lowScalar one_bounded_lowScalar y
        (by simpa using hsigmaPos)
  have hsmallSet :
      (primesUpTo y).filter (fun p ↦ p < 23) = gsA9SmallPrimeFinset := by
    ext p
    simp only [Finset.mem_filter, mem_primesUpTo, gsA9SmallPrimeFinset,
      Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨hp, _⟩, hp23⟩
      exact ⟨hp23, hp⟩
    · rintro ⟨hp23, hp⟩
      exact ⟨⟨hp, hp23.le.trans hy⟩, hp23⟩
  have hlargeSet :
      (primesUpTo y).filter (fun p ↦ ¬ p < 23) = S := by
    ext p
    simp [S, gsA9LargePrimesUpTo]
  have hsplit :
      (∏ p ∈ gsA9SmallPrimeFinset,
          gsA9LocalEulerFactor one (sigmaLow : ℂ) p) *
        (∏ p ∈ S, gsA9LocalEulerFactor one (sigmaLow : ℂ) p) =
      ∏ p ∈ primesUpTo y,
        gsA9LocalEulerFactor one (sigmaLow : ℂ) p := by
    simpa only [hsmallSet, hlargeSet] using
      Finset.prod_filter_mul_prod_filter_not (primesUpTo y)
        (fun p ↦ p < 23)
        (fun p ↦ gsA9LocalEulerFactor one (sigmaLow : ℂ) p)
  have hsmall :
      ‖∏ p ∈ gsA9SmallPrimeFinset,
          gsA9LocalEulerFactor one (sigmaLow : ℂ) p‖ ≤
        gsA9SmallPrimeEulerBound := by
    simpa only [one, mul_zero, Complex.ofReal_zero, add_zero] using
      norm_prod_gsA9LocalEulerFactor_smallPrimes_le
        one_bounded_lowScalar (t := 0) hsigmaHalf
  have hSsub : S ⊆ primesUpTo y := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hSprime : ∀ p ∈ S, p.Prime := by
    intro p hp
    exact (mem_primesUpTo.mp (hSsub hp)).1
  have hSlarge : ∀ p ∈ S, 23 ≤ p := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hthird : ∀ p ∈ S,
      ‖(p : ℂ) ^ (-(sigmaLow : ℂ))‖ ≤ (1 / 3 : ℝ) := by
    intro p hp
    have h := norm_prime_cpow_le_one_third_of_twenty_three_le
      (hSprime p hp) (hSlarge p hp) (t := 0) hsigmaHalf
    simpa only [mul_zero, Complex.ofReal_zero, add_zero] using h
  let c : ℕ → ℝ := fun p ↦ (p : ℝ) ^ (sigmaHigh - sigmaLow)
  have hc : ∀ p ∈ S, 1 ≤ c p := by
    intro p hp
    exact Real.one_le_rpow (by exact_mod_cast (hSprime p hp).one_le)
      (sub_nonneg.mpr hle)
  have hfactor : ∀ p ∈ S,
      (p : ℂ) ^ (-(sigmaLow : ℂ)) =
        (c p : ℂ) * (p : ℂ) ^ (-(sigmaHigh : ℂ)) := by
    intro p hp
    have h := nat_cpow_neg_low_eq_rpow_gap_mul_neg_high
      (hSprime p hp) (t := 0) hle
    simpa only [mul_zero, Complex.ofReal_zero, add_zero, c] using h
  have hD :
      (∑ p ∈ S,
        (‖(p : ℂ) ^ (-(sigmaLow : ℂ))‖ -
          ‖(p : ℂ) ^ (-(sigmaHigh : ℂ))‖)) ≤
        gsA9SourceShiftConstant := by
    have h := sum_prime_radial_norm_sub_subset_sourceGap_le_constant
      hy2 S hSsub hle hsigmaSource hgap (t := 0)
    simpa only [mul_zero, Complex.ofReal_zero, add_zero] using h
  have hshift := norm_prod_gsA9LocalEulerFactor_shift_le_exp_sum_norm_sub
    one_multiplicative_lowScalar one_bounded_lowScalar S hSprime c hc
      hfactor hthird
  have hshift' :
      ‖∏ p ∈ S, gsA9LocalEulerFactor one (sigmaLow : ℂ) p‖ ≤
        ‖∏ p ∈ S, gsA9LocalEulerFactor one (sigmaHigh : ℂ) p‖ *
          Real.exp (6 * gsA9SourceShiftConstant) := by
    exact hshift.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hD (by norm_num)))
      (norm_nonneg _))
  let P : ℕ → Prop := fun p ↦ 23 ≤ p ∧ p ≤ y
  have hEulerHigh :
      LSeries (primeBandCoefficient one P) (sigmaHigh : ℂ) =
        ∏ p ∈ S, gsA9LocalEulerFactor one (sigmaHigh : ℂ) p := by
    have hbase :=
      LSeries_primeBandCoefficient_eq_finiteEulerProduct_of_pos_re
        one_multiplicative_lowScalar one_bounded_lowScalar P y
          (fun _ hp ↦ hp.2) (s := (sigmaHigh : ℂ))
          (by simpa using (show 0 < sigmaHigh by linarith))
    have hfilter : (primesUpTo y).filter P = S := by
      ext p
      simp [P, S, gsA9LargePrimesUpTo]
      aesop
    simpa only [Finset.prod_filter, hfilter] using hbase
  have hPBound : ∀ n, 0 < n → ‖primeBandCoefficient one P n‖ ≤ 1 := by
    intro n hn
    exact norm_primeBandCoefficient_le_one one_bounded_lowScalar P hn
  have hZeta :
      ‖LSeries (primeBandCoefficient one P) (sigmaHigh : ℂ)‖ ≤
        ‖riemannZeta (sigmaHigh : ℂ)‖ := by
    have h := Erdos67.norm_LSeries_le_norm_riemannZeta_real_of_bounded
      hPBound (sigma := sigmaHigh) (t := 0) hsigmaHigh
    simpa only [mul_zero, Complex.ofReal_zero, add_zero] using h
  have hZetaPole : ‖riemannZeta (sigmaHigh : ℂ)‖ ≤
      1 + Real.log (y : ℝ) := by
    have h := Erdos67.norm_riemannZeta_real_le_one_add_inv heta
    have hetaInv : eta⁻¹ = Real.log (y : ℝ) := by
      simp only [eta, inv_inv]
    simpa only [sigmaHigh, hetaInv] using h
  have hlargeHigh :
      ‖∏ p ∈ S, gsA9LocalEulerFactor one (sigmaHigh : ℂ) p‖ ≤
        1 + Real.log (y : ℝ) := by
    rw [← hEulerHigh]
    exact hZeta.trans hZetaPole
  rw [hEulerLow] at hmass
  have hfull :
      ‖∏ p ∈ primesUpTo y,
          gsA9LocalEulerFactor one (sigmaLow : ℂ) p‖ ≤
        gsA10FiniteLowMassConstant * (1 + Real.log (y : ℝ)) := by
    rw [← hsplit, norm_mul]
    unfold gsA10FiniteLowMassConstant
    calc
      _ ≤ gsA9SmallPrimeEulerBound *
          (‖∏ p ∈ S, gsA9LocalEulerFactor one (sigmaHigh : ℂ) p‖ *
            Real.exp (6 * gsA9SourceShiftConstant)) :=
        mul_le_mul hsmall hshift' (norm_nonneg _)
          gsA9SmallPrimeEulerBound_nonneg
      _ ≤ gsA9SmallPrimeEulerBound *
          ((1 + Real.log (y : ℝ)) *
            Real.exp (6 * gsA9SourceShiftConstant)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hlargeHigh (Real.exp_pos _).le)
          gsA9SmallPrimeEulerBound_nonneg
      _ = gsA9SmallPrimeEulerBound *
          Real.exp (6 * gsA9SourceShiftConstant) *
            (1 + Real.log (y : ℝ)) := by ring
  simpa only [sigmaLow, one] using hmass.trans hfull

end

end Erdos67.MRHalaszBands

#print axioms Erdos67.MRHalaszBands.gsFiniteNormDirichletMass_twoBlockAlternatingLow_le_positive_LSeries_explicit
#print axioms Erdos67.MRHalaszBands.gsFiniteNormDirichletMass_twoBlockAlternatingLow_le_sourceConstant
