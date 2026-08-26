import ErdosProblems.Erdos67b.MRGSA10SecondSecondaryPrimeChebyshev
import ErdosProblems.Erdos67b.MRGSA9A14FullSeries
import ErdosProblems.Erdos67b.MRGlobalExpWeightedPrimeTail

/-!
# The finite high-prime Dirichlet mass in GS A.10

The high factor in the second secondary sum is evaluated at
`1 + 2 / log y`.  Its positive Euler product is uniformly bounded: the
prime-linear part is the globally summable exponentially weighted tail,
and the higher-power part is charged to `primeQuadraticConstant`.
-/

open scoped BigOperators LSeries.notation ComplexOrder

namespace Erdos67b.MRHalaszBands

noncomputable section

open Erdos67b.PrimeEstimates Erdos67b.EulerQuantitative

private theorem one_multiplicative :
    IsMultiplicativeOnPositiveNat (fun _ : ℕ ↦ (1 : ℂ)) := by
  constructor <;> simp

private theorem one_bounded :
    ∀ n : ℕ, 0 < n → ‖(1 : ℂ)‖ ≤ 1 := by
  simp

/-- A finite high-prime norm mass is bounded by the complete positive
Euler series on the same finite prime band. -/
theorem gsFiniteNormDirichletMass_gsA9HighArithmetic_le_positive_LSeries
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} {sigma : ℝ} (hsigma : 1 < sigma) :
    gsFiniteNormDirichletMass (gsA9HighArithmetic f y) X sigma ≤
      ‖LSeries (primeBandCoefficient (fun _ : ℕ ↦ (1 : ℂ))
          (fun p ↦ ¬ p ≤ y ∧ p ≤ X)) (sigma : ℂ)‖ := by
  let a : ℕ → ℂ :=
    primeBandCoefficient (fun _ : ℕ ↦ (1 : ℂ))
      (fun p ↦ ¬ p ≤ y ∧ p ≤ X)
  have haBound : ∀ n, n ≠ 0 → ‖a n‖ ≤ 1 := by
    intro n hn
    exact norm_primeBandCoefficient_le_one one_bounded
      (fun p ↦ ¬ p ≤ y ∧ p ≤ X)
      (Nat.pos_of_ne_zero hn)
  have haNonneg : ∀ n, 0 ≤ a n := by
    intro n
    dsimp only [a]
    unfold primeBandCoefficient
    split_ifs <;> simp
  have haOne : 0 < a 1 := by
    simp [a, primeBandCoefficient, primeSupported_one]
  have hsumA : LSeriesSummable a (sigma : ℂ) :=
    LSeriesSummable_of_bounded_of_one_lt_re haBound (by simpa using hsigma)
  have habscissa : LSeries.abscissaOfAbsConv a ≤ (1 : EReal) := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    intro x hx
    exact LSeriesSummable_of_bounded_of_one_lt_re haBound (by simpa using hx)
  have habscissaLt : LSeries.abscissaOfAbsConv a < (sigma : EReal) :=
    habscissa.trans_lt (by exact_mod_cast hsigma)
  have hpos : 0 < LSeries a (sigma : ℂ) :=
    LSeries.positive haNonneg haOne habscissaLt
  have hterm (n : ℕ) :
      ‖LSeries.term a (sigma : ℂ) n‖ =
        (LSeries.term a (sigma : ℂ) n).re := by
    have hn := LSeries.term_nonneg (haNonneg n) sigma
    rw [Complex.nonneg_iff] at hn
    have heq : LSeries.term a (sigma : ℂ) n =
        ((LSeries.term a (sigma : ℂ) n).re : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa using hn.2.symm
    calc
      ‖LSeries.term a (sigma : ℂ) n‖ =
          ‖((LSeries.term a (sigma : ℂ) n).re : ℂ)‖ :=
        congrArg norm heq
      _ = (LSeries.term a (sigma : ℂ) n).re := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn.1]
  have hmass :
      (∑' n : ℕ, ‖LSeries.term a (sigma : ℂ) n‖) =
        (LSeries a (sigma : ℂ)).re := by
    unfold LSeries
    rw [Complex.re_tsum hsumA]
    exact tsum_congr hterm
  have hnormA : ‖LSeries a (sigma : ℂ)‖ =
      (LSeries a (sigma : ℂ)).re := by
    have hp := Complex.pos_iff.mp hpos
    have heq : LSeries a (sigma : ℂ) =
        ((LSeries a (sigma : ℂ)).re : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa using hp.2.symm
    calc
      ‖LSeries a (sigma : ℂ)‖ =
          ‖((LSeries a (sigma : ℂ)).re : ℂ)‖ := congrArg norm heq
      _ = (LSeries a (sigma : ℂ)).re := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp.1]
  have hcoeff : ∀ {n : ℕ}, 0 < n → n ≤ X →
      ‖gsA9HighArithmetic f y n‖ ≤ ‖a n‖ := by
    intro n hn hnX
    rw [gsA9HighArithmetic_apply_of_ne_zero f y hn.ne']
    by_cases hsupp : PrimeSupported (fun p ↦ ¬ p ≤ y) n
    · have hsuppFinite : PrimeSupported (fun p ↦ ¬ p ≤ y ∧ p ≤ X) n := by
        refine ⟨hsupp.1, ?_⟩
        intro p hp
        refine ⟨hsupp.2 p hp, ?_⟩
        exact (Nat.le_of_dvd hn (Nat.dvd_of_mem_primeFactors hp)).trans hnX
      simp only [a, gsA9High, primeBandCoefficient, if_pos hsupp,
        if_pos hsuppFinite, norm_one]
      exact hbound n hn
    · have hsuppFinite : ¬ PrimeSupported (fun p ↦ ¬ p ≤ y ∧ p ≤ X) n :=
        fun h ↦ hsupp ⟨h.1, fun p hp ↦ (h.2 p hp).1⟩
      simp only [a, gsA9High, primeBandCoefficient, if_neg hsupp,
        if_neg hsuppFinite, norm_zero]
      exact le_rfl
  unfold gsFiniteNormDirichletMass
  calc
    (∑ n ∈ Finset.Icc 1 X,
        ‖gsA9HighArithmetic f y n‖ * (n : ℝ) ^ (-sigma)) ≤
        ∑ n ∈ Finset.Icc 1 X,
          ‖LSeries.term a (sigma : ℂ) n‖ := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
      rw [LSeries.norm_term_eq, if_neg hnpos.ne']
      rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ n), div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right
        (hcoeff hnpos (Finset.mem_Icc.mp hn).2) (by positivity)
    _ ≤ ∑' n : ℕ, ‖LSeries.term a (sigma : ℂ) n‖ :=
      hsumA.norm.sum_le_tsum (Finset.Icc 1 X) (fun _ _ ↦ norm_nonneg _)
    _ = ‖LSeries a (sigma : ℂ)‖ := by rw [hmass, hnormA]

/-- Uniform source-line bound for the high finite norm-Dirichlet mass. -/
theorem gsFiniteNormDirichletMass_gsA9HighArithmetic_le_sourceConstant
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} (hy : 2 ≤ y) (hyX : y ≤ X) :
    gsFiniteNormDirichletMass (gsA9HighArithmetic f y) X
        (1 + 2 * (Real.log (y : ℝ))⁻¹) ≤
      Real.exp (Real.log 2 + 2 * mertensBound +
        3 * primeQuadraticConstant) := by
  let eta : ℝ := (Real.log (y : ℝ))⁻¹
  let sigma : ℝ := 1 + 2 * eta
  let S : Finset ℕ :=
    (primesUpTo X).filter (fun p ↦ ¬ p ≤ y ∧ p ≤ X)
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have heta : 0 < eta := inv_pos.mpr hlog
  have hsigma : 1 < sigma := by dsimp [sigma]; linarith
  have hmass :=
    gsFiniteNormDirichletMass_gsA9HighArithmetic_le_positive_LSeries
      hbound (y := y) (X := X) hsigma
  have hEuler :
      LSeries (primeBandCoefficient (fun _ : ℕ ↦ (1 : ℂ))
          (fun p ↦ ¬ p ≤ y ∧ p ≤ X)) (sigma : ℂ) =
        ∏ p ∈ S, gsA9LocalEulerFactor (fun _ : ℕ ↦ (1 : ℂ))
          (sigma : ℂ) p := by
    simpa only [S, Finset.prod_filter] using
      LSeries_primeBandCoefficient_eq_finiteEulerProduct_of_pos_re
        one_multiplicative one_bounded (fun p ↦ ¬ p ≤ y ∧ p ≤ X) X
          (fun _ hp ↦ hp.2)
          (by simpa using (show 0 < sigma by linarith))
  have hprime : ∀ p ∈ S, p.Prime := by
    intro p hp
    exact (mem_primesUpTo.mp (Finset.mem_filter.mp hp).1).1
  have hprod := norm_prod_gsA9LocalEulerFactor_le_exp_linear_add_square
    one_multiplicative one_bounded S hprime hsigma.le 0
  have hlinear :
      (∑ p ∈ S,
        (((1 : ℂ) * (p : ℂ) ^
          (-((sigma : ℂ) + Complex.I * (0 : ℂ)))).re)) ≤
        expWeightedPrimeTail y X := by
    rw [expWeightedPrimeTail_eq_sum_term]
    have hset : S = primesInInterval y X := by
      ext p
      simp only [S, Finset.mem_filter, mem_primesUpTo,
        mem_primesInInterval]
      aesop
    rw [hset]
    apply Finset.sum_le_sum
    intro p hp
    have hpprime := (mem_primesInInterval.mp hp).2.2
    have hpone : (1 : ℝ) ≤ p := by exact_mod_cast hpprime.one_le
    calc
      (((1 : ℂ) * (p : ℂ) ^
          (-((sigma : ℂ) + Complex.I * (0 : ℂ)))).re) ≤
          ‖(p : ℂ) ^
            (-((sigma : ℂ) + Complex.I * (0 : ℂ)))‖ := by
        simpa using Complex.re_le_norm
          ((p : ℂ) ^ (-((sigma : ℂ) + Complex.I * (0 : ℂ))))
      _ = (p : ℝ) ^ (-sigma) := by
        exact Erdos67b.HalaszCpowDeficit.norm_nat_cpow_neg_sigma_add_I_mul
          hpprime.pos sigma 0
      _ ≤ (p : ℝ) ^ (-(1 : ℝ) - eta) := by
        apply Real.rpow_le_rpow_of_exponent_le hpone
        dsimp [sigma]
        linarith
      _ = expWeightedPrimeTerm y p := by
        rfl
  have hlinear' :
      (∑ p ∈ S,
        (((1 : ℂ) * (p : ℂ) ^
          (-((sigma : ℂ) + Complex.I * (0 : ℂ)))).re)) ≤
        Real.log 2 + 2 * mertensBound :=
    hlinear.trans (expWeightedPrimeTail_le_log_two_add_global hy hyX)
  have hquad :
      (∑ p ∈ S,
        ‖(p : ℂ) ^
          (-((sigma : ℂ) + Complex.I * (0 : ℂ)))‖ ^ 2) ≤
        primeQuadraticConstant :=
    sum_norm_prime_cpow_sq_le_primeQuadraticConstant S hprime hsigma
  rw [hEuler] at hmass
  simp only [Complex.ofReal_zero, mul_zero, add_zero] at hprod hlinear' hquad
  simpa only [sigma, eta] using
    hmass.trans (hprod.trans (Real.exp_le_exp.mpr (by linarith)))

end

end Erdos67b.MRHalaszBands

#print axioms Erdos67b.MRHalaszBands.gsFiniteNormDirichletMass_gsA9HighArithmetic_le_positive_LSeries
#print axioms Erdos67b.MRHalaszBands.gsFiniteNormDirichletMass_gsA9HighArithmetic_le_sourceConstant
