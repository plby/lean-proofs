import ErdosProblems.Erdos67b.MRFrequencyRecombination

/-!
# Vertical energy of the prime-square Ramaré correction

The common coefficient equals the original multiplicative value off
the selected-prime-square obstruction. Its sparse square mass controls
the vertical error without any prime-density estimate.
-/

open scoped BigOperators Interval
open Finset MeasureTheory

namespace Erdos67b

noncomputable section

theorem mrCommonRamareCoefficient_eq_of_no_prime_square
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    {n : ℕ} (hn : 0 < n) (hdiv : ∃ p ∈ P, p ∣ n)
    (hsq : ∀ p ∈ P, ¬p * p ∣ n) : mrCommonRamareCoefficient P f n = f n := by
  classical
  have hrewrite : mrCommonRamareCoefficient P f n =
      ∑ p ∈ primeDivisorSet P n,
        f p * f (n / p) / (mrCommonDenominator P (n / p) : ℂ) := by
    unfold mrCommonRamareCoefficient primeDivisorSet
    rw [← Finset.sum_filter]
  rw [hrewrite]
  calc
    _ = ∑ p ∈ primeDivisorSet P n, f n / (ramareDenominator P p (n / p) : ℂ) := by
      apply Finset.sum_congr rfl
      intro p hp
      obtain ⟨hpP, hpn⟩ := mem_primeDivisorSet.mp hp
      have hpprime := hP p hpP
      have hquot : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn hpn) hpprime.pos
      have hnot : ¬p ∣ n / p := fun hh ↦ hsq p hpP ((dvd_div_iff_sq_dvd hpprime.pos hpn).mp hh)
      have hcop : p.Coprime (n / p) := hpprime.coprime_iff_not_dvd.mpr hnot
      have hvalue := hmul.2 p (n / p) hpprime.pos hquot hcop
      rw [Nat.mul_div_cancel' hpn] at hvalue
      rw [← hvalue, ramareDenominator_eq_mrCommon_of_not_dvd hnot]
    _ = f n := ramare_identity_smul hP hdiv (f n)

def mrTypicalValueCoefficient
    (blocks : Finset (ℕ × ℕ)) (Z : ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ := by
  classical
  exact if n ∈ typicalFactorizationSet blocks Z then f n else 0

def mrPrimeSquareErrorCoefficient
    (blocks : Finset (ℕ × ℕ)) (I : ℕ × ℕ) (Z : ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  (mrTypicalValueCoefficient blocks Z f n -
    mrTypicalCommonCoefficient blocks Z (primesInBlock I) f n) / (n : ℂ)

theorem norm_mrTypicalValueCoefficient_le_one
    {blocks : Finset (ℕ × ℕ)} {Z : ℕ} {f : ℕ → ℂ}
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) {n : ℕ} (hn : 0 < n) :
    ‖mrTypicalValueCoefficient blocks Z f n‖ ≤ 1 := by
  classical
  unfold mrTypicalValueCoefficient
  split_ifs
  · exact hbound n hn
  · simp

theorem mrPrimeSquareErrorCoefficient_eq_zero_of_count_zero
    {blocks : Finset (ℕ × ℕ)} {I : ℕ × ℕ} (hI : I ∈ blocks)
    {Z : ℕ} {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    {n : ℕ} (hn : 0 < n) (hcount : primeSquareDivisorCount (primesInBlock I) n = 0) :
    mrPrimeSquareErrorCoefficient blocks I Z f n = 0 := by
  classical
  have hsq : ∀ p ∈ primesInBlock I, ¬p * p ∣ n := by
    intro p hp hpp
    have hpos : 0 < primeSquareDivisorCount (primesInBlock I) n :=
      Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hpp⟩⟩
    omega
  unfold mrPrimeSquareErrorCoefficient mrTypicalValueCoefficient mrTypicalCommonCoefficient
  split_ifs with htyp
  · have hdiv := (mem_typicalFactorizationSet.mp htyp).2.2 I hI
    rw [mrCommonRamareCoefficient_eq_of_no_prime_square
      (fun p hp ↦ (mem_primesInBlock.mp hp).1) hmul hn hdiv hsq, sub_self, zero_div]
  · simp

theorem norm_mrPrimeSquareErrorCoefficient_le
    {blocks : Finset (ℕ × ℕ)} {I : ℕ × ℕ} {Z : ℕ} {f : ℕ → ℂ}
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) {n : ℕ} (hn : 0 < n) :
    ‖mrPrimeSquareErrorCoefficient blocks I Z f n‖ ≤ 2 / n := by
  have hnum : ‖mrTypicalValueCoefficient blocks Z f n -
      mrTypicalCommonCoefficient blocks Z (primesInBlock I) f n‖ ≤ 2 := by
    have ha := norm_mrTypicalValueCoefficient_le_one (blocks := blocks) (Z := Z) hbound hn
    have hb := norm_mrTypicalCommonCoefficient_le_one (blocks := blocks) (Z := Z) (P := primesInBlock I)
      (fun p hp ↦ (mem_primesInBlock.mp hp).1) hbound hn
    exact (norm_sub_le _ _).trans (by linarith)
  unfold mrPrimeSquareErrorCoefficient
  rw [norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right hnum (Nat.cast_nonneg _)

theorem normSq_mrPrimeSquareErrorCoefficient_le_count
    {blocks : Finset (ℕ × ℕ)} {I : ℕ × ℕ} (hI : I ∈ blocks)
    {Z X : ℕ} (hX : 0 < X) {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) {n : ℕ} (hn : X ≤ n) :
    Complex.normSq (mrPrimeSquareErrorCoefficient blocks I Z f n) ≤
      4 * (primeSquareDivisorCount (primesInBlock I) n : ℝ) / (X : ℝ) ^ 2 := by
  have hn0 := hX.trans_le hn
  by_cases hc : primeSquareDivisorCount (primesInBlock I) n = 0
  · rw [mrPrimeSquareErrorCoefficient_eq_zero_of_count_zero hI hmul hn0 hc, hc]
    simp
  · have hc1 : (1 : ℝ) ≤ primeSquareDivisorCount (primesInBlock I) n := by
      exact_mod_cast (by omega : 1 ≤ primeSquareDivisorCount (primesInBlock I) n)
    have hcoeff : ‖mrPrimeSquareErrorCoefficient blocks I Z f n‖ ≤ 2 / X := by
      apply (norm_mrPrimeSquareErrorCoefficient_le hbound hn0).trans
      exact div_le_div_of_nonneg_left (by norm_num) (by exact_mod_cast hX) (by exact_mod_cast hn)
    rw [Complex.normSq_eq_norm_sq]
    calc
      _ ≤ ((2 : ℝ) / X) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hcoeff 2
      _ = 4 / (X : ℝ) ^ 2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)

theorem sum_normSq_mrPrimeSquareErrorCoefficient_le
    {blocks : Finset (ℕ × ℕ)} {I : ℕ × ℕ} (hI : I ∈ blocks) (hL : 0 < I.1)
    {Z X : ℕ} (hX : 0 < X) {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) :
    (∑ n ∈ Finset.Ioc X (2 * X), Complex.normSq (mrPrimeSquareErrorCoefficient blocks I Z f n)) ≤
      16 / ((X : ℝ) * I.1) := by
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hLr : (0 : ℝ) < I.1 := by exact_mod_cast hL
  have hsub : Finset.Ioc X (2 * X) ⊆ Finset.Icc 1 (2 * X) := by
    intro n hn
    obtain ⟨hnlo, hnhi⟩ := Finset.mem_Ioc.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, hnhi⟩
  have hcountNat : (∑ n ∈ Finset.Ioc X (2 * X), primeSquareDivisorCount (primesInBlock I) n) ≤
      ∑ p ∈ primesInBlock I, (2 * X) / (p * p) := by
    rw [← sum_primeSquareDivisorCount_Icc]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ Nat.zero_le _)
  have hcount : (∑ n ∈ Finset.Ioc X (2 * X), (primeSquareDivisorCount (primesInBlock I) n : ℝ)) ≤
      (2 * X : ℕ) * (2 / (I.1 : ℝ)) := by
    have hh := (Nat.cast_le.mpr hcountNat).trans (cast_sum_primesInBlock_nat_div_sq_le_tail I hL)
    simpa only [Nat.cast_sum] using hh
  calc
    _ ≤ ∑ n ∈ Finset.Ioc X (2 * X),
        4 * (primeSquareDivisorCount (primesInBlock I) n : ℝ) / (X : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      exact normSq_mrPrimeSquareErrorCoefficient_le_count hI hX hmul hbound (Finset.mem_Ioc.mp hn).1.le
    _ = (4 / (X : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc X (2 * X),
        (primeSquareDivisorCount (primesInBlock I) n : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ ≤ (4 / (X : ℝ) ^ 2) * ((2 * X : ℕ) * (2 / (I.1 : ℝ))) :=
      mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = _ := by push_cast; field_simp; norm_num

/-- Vertical mean square of the sparse prime-square correction. -/
theorem intervalIntegral_mrPrimeSquareError_le
    {blocks : Finset (ℕ × ℕ)} {I : ℕ × ℕ} (hI : I ∈ blocks) (hL : 0 < I.1)
    {Z X : ℕ} (hX : 0 < X) {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, ‖logarithmicDirichletPolynomial (Finset.Ioc X (2 * X))
      (mrPrimeSquareErrorCoefficient blocks I Z f) t‖ ^ 2) ≤
      64 * (1 + Real.pi) * (T / X + 1) / I.1 := by
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hLr : (0 : ℝ) < I.1 := by exact_mod_cast hL
  have hmass := sum_normSq_mrPrimeSquareErrorCoefficient_le (Z := Z) hI hL hX hmul hbound
  have hmean := norm_logarithmicDirichletPolynomial_intervalIntegral_le_support
    (show 0 < 2 * X by omega)
    (fun n hn ↦ hX.trans (Finset.mem_Ioc.mp hn).1)
    (fun n hn ↦ (Finset.mem_Ioc.mp hn).2) (mrPrimeSquareErrorCoefficient blocks I Z f) hT
  have hscalar : 32 * (T / X + 2 * Real.pi) ≤ 64 * (1 + Real.pi) * (T / X + 1) := by
    have htau : 0 ≤ T / X := by positivity
    nlinarith [Real.pi_pos, mul_nonneg htau Real.pi_pos.le]
  calc
    _ = ‖∫ t in -T..T,
        star (logarithmicDirichletPolynomial (Finset.Ioc X (2 * X)) (mrPrimeSquareErrorCoefficient blocks I Z f) t) *
          logarithmicDirichletPolynomial (Finset.Ioc X (2 * X)) (mrPrimeSquareErrorCoefficient blocks I Z f) t‖ :=
      intervalIntegral_norm_sq_eq_norm_conj_mul_self _ hT
    _ ≤ (2 * T + 2 * Real.pi * (2 * X : ℕ)) *
        ∑ n ∈ Finset.Ioc X (2 * X), Complex.normSq (mrPrimeSquareErrorCoefficient blocks I Z f n) := hmean
    _ ≤ (2 * T + 2 * Real.pi * (2 * X : ℕ)) * (16 / ((X : ℝ) * I.1)) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = (32 * (T / X + 2 * Real.pi)) / I.1 := by push_cast; field_simp; ring
    _ ≤ _ := div_le_div_of_nonneg_right hscalar hLr.le

def mrTypicalDyadicPolynomial
    (blocks : Finset (ℕ × ℕ)) (f : ℕ → ℂ) (X : ℕ) (t : ℝ) : ℂ :=
  logarithmicDirichletPolynomial (Finset.Ioc X (2 * X))
    (fun n ↦ mrTypicalValueCoefficient blocks (2 * X) f n / (n : ℂ)) t

def mrPrimeSquareErrorPolynomial
    (blocks : Finset (ℕ × ℕ)) (I : ℕ × ℕ) (f : ℕ → ℂ) (X : ℕ) (t : ℝ) : ℂ :=
  logarithmicDirichletPolynomial (Finset.Ioc X (2 * X))
    (mrPrimeSquareErrorCoefficient blocks I (2 * X) f) t

theorem mrTypicalDyadicPolynomial_eq_common_add_error
    (blocks : Finset (ℕ × ℕ)) (I : ℕ × ℕ) (f : ℕ → ℂ) (X : ℕ) (t : ℝ) :
    mrTypicalDyadicPolynomial blocks f X t =
      logarithmicDirichletPolynomial (Finset.Ioc X (2 * X))
        (fun n ↦ mrTypicalCommonCoefficient blocks (2 * X) (primesInBlock I) f n / (n : ℂ)) t +
      mrPrimeSquareErrorPolynomial blocks I f X t := by
  unfold mrTypicalDyadicPolynomial mrPrimeSquareErrorPolynomial logarithmicDirichletPolynomial
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  unfold mrPrimeSquareErrorCoefficient
  ring

theorem intervalIntegral_indicator_add_le
    {F G : ℝ → ℂ} (hF : Continuous F) (hG : Continuous G)
    {E : Set ℝ} (hE : MeasurableSet E) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, E.indicator (fun t ↦ ‖F t + G t‖ ^ 2) t) ≤
      2 * (∫ t in -T..T, E.indicator (fun t ↦ ‖F t‖ ^ 2) t) +
        2 * ∫ t in -T..T, ‖G t‖ ^ 2 := by
  have hh := intervalIntegral_indicator_sum_sub_le ({()} : Finset Unit) (fun _ ↦ F)
    (fun t ↦ -G t) (fun _ _ ↦ hF) hG.neg hE hT
  simpa only [Finset.sum_singleton, Finset.card_singleton, Nat.cast_one, mul_one,
    sub_neg_eq_add, norm_neg] using hh

/-- Transfer the class bound to the original typical polynomial. -/
theorem intervalIntegral_typical_le_common_add_primeSquare
    {blocks : Finset (ℕ × ℕ)} {I : ℕ × ℕ} (hI : I ∈ blocks) (hL : 0 < I.1)
    {X : ℕ} (hX : 0 < X) {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {E : Set ℝ} (hE : MeasurableSet E) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, E.indicator (fun t ↦ ‖mrTypicalDyadicPolynomial blocks f X t‖ ^ 2) t) ≤
      2 * (∫ t in -T..T, E.indicator (fun t ↦ ‖logarithmicDirichletPolynomial (Finset.Ioc X (2 * X))
        (fun n ↦ mrTypicalCommonCoefficient blocks (2 * X) (primesInBlock I) f n / (n : ℂ)) t‖ ^ 2) t) +
      128 * (1 + Real.pi) * (T / X + 1) / I.1 := by
  simp_rw [mrTypicalDyadicPolynomial_eq_common_add_error blocks I f X]
  have hbase := intervalIntegral_indicator_add_le
    (continuous_logarithmicDirichletPolynomial (Finset.Ioc X (2 * X))
      (fun n ↦ mrTypicalCommonCoefficient blocks (2 * X) (primesInBlock I) f n / (n : ℂ)))
    (continuous_logarithmicDirichletPolynomial (Finset.Ioc X (2 * X))
      (mrPrimeSquareErrorCoefficient blocks I (2 * X) f)) hE hT
  have herror := intervalIntegral_mrPrimeSquareError_le (Z := 2 * X) hI hL hX hmul hbound hT
  apply hbase.trans
  have hh := mul_le_mul_of_nonneg_left herror (by norm_num : (0 : ℝ) ≤ 2)
  calc
    _ ≤ 2 * (∫ t in -T..T, E.indicator (fun t ↦ ‖logarithmicDirichletPolynomial (Finset.Ioc X (2 * X))
        (fun n ↦ mrTypicalCommonCoefficient blocks (2 * X) (primesInBlock I) f n / (n : ℂ)) t‖ ^ 2) t) +
      2 * (64 * (1 + Real.pi) * (T / X + 1) / I.1) := add_le_add le_rfl hh
    _ = _ := by ring

theorem mrScheduledPrimeInterval_inv_lower_le_exp
    (p₁ q₁ : ℝ) (j : ℕ) :
    ((mrScheduledPrimeInterval p₁ q₁ j).1 : ℝ)⁻¹ ≤ Real.exp (-mrLogScheduleLower p₁ q₁ j) := by
  rw [Real.exp_neg]
  exact inv_anti₀ (Real.exp_pos _) (Nat.le_ceil _)

/-- Higher first-small classes now bound one fixed typical polynomial,
with the prime-square correction included. -/
theorem mrArithmetic_typical_firstSmallClass_energy_le
    (J : ℕ) {eta p₁ q₁ : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hp : 2 ≤ p₁) (hqexp : Real.exp 1 ≤ q₁) (hpq : p₁ ≤ q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁) {j : ℕ} (hj : 2 ≤ j) (hjJ : j ≤ J)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {X : ℕ} (hX : 0 < X) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, (disjointed (mrArithmeticSmallFrequencySet eta p₁ q₁ f) j).indicator
      (fun t ↦ ‖mrTypicalDyadicPolynomial (mrScheduledBlocks p₁ q₁ J) f X t‖ ^ 2) t) ≤
      4096 * Real.exp 13 * (1 + Real.pi) * (T / X + 1) /
        ((j : ℝ) ^ 2 * Real.exp (mrLogScheduleUpper q₁ (j - 1))) +
      128 * (1 + Real.pi) * (T / X + 1) *
        (6 / mrLogBlockResolution eta p₁ q₁ (j : ℝ) + 1 / X + Real.exp (-mrLogScheduleLower p₁ q₁ j)) := by
  have hI : mrScheduledPrimeInterval p₁ q₁ j ∈ mrScheduledBlocks p₁ q₁ J :=
    Finset.mem_image.mpr ⟨j, Finset.mem_Icc.mpr ⟨by omega, hjJ⟩, rfl⟩
  have hL : 0 < (mrScheduledPrimeInterval p₁ q₁ j).1 := by
    have hh := (Real.exp_pos (mrLogScheduleLower p₁ q₁ j)).trans_le (Nat.le_ceil _)
    exact_mod_cast hh
  have hmeas : MeasurableSet (disjointed (mrArithmeticSmallFrequencySet eta p₁ q₁ f) j) :=
    MeasurableSet.disjointed (measurableSet_mrScheduledSmallFrequencySet _ _ _ _ _) j
  have hbase := intervalIntegral_typical_le_common_add_primeSquare hI hL hX hmul hbound hmeas hT
  have hcommon := mrArithmetic_common_firstSmallClass_energy_le J heta0 heta1 hp hqexp hpq hbudget hj hbound hX hT
  have herror : 128 * (1 + Real.pi) * (T / X + 1) / (mrScheduledPrimeInterval p₁ q₁ j).1 ≤
      128 * (1 + Real.pi) * (T / X + 1) * Real.exp (-mrLogScheduleLower p₁ q₁ j) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (mrScheduledPrimeInterval_inv_lower_le_exp p₁ q₁ j) (by positivity)
  apply hbase.trans
  have hh := add_le_add (mul_le_mul_of_nonneg_left hcommon (by norm_num : (0 : ℝ) ≤ 2)) herror
  apply hh.trans_eq
  ring

/-- The first class also bounds the fixed typical polynomial, with its
prime-square correction included. -/
theorem mrArithmetic_typical_firstClass_energy_le
    (J : ℕ) (hJ : 1 ≤ J) {eta p₁ q₁ : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hp : 2 ≤ p₁) (hqexp : Real.exp 1 ≤ q₁) (hpq : p₁ ≤ q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {X : ℕ} (hX : 0 < X) (hscale : Real.exp q₁ ≤ X) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, (disjointed (mrArithmeticSmallFrequencySet eta p₁ q₁ f) 1).indicator
      (fun t ↦ ‖mrTypicalDyadicPolynomial (mrScheduledBlocks p₁ q₁ J) f X t‖ ^ 2) t) ≤
      2048 * Real.exp 1 * (1 + Real.pi) * (T / X * Real.exp q₁ + 1) *
        Real.exp (Real.log q₁ / 3 - (1 / 6 - eta) * p₁) +
      128 * (1 + Real.pi) * (T / X + 1) *
        (6 / mrLogBlockResolution eta p₁ q₁ 1 + 1 / X + Real.exp (-p₁)) := by
  have hI : mrScheduledPrimeInterval p₁ q₁ 1 ∈ mrScheduledBlocks p₁ q₁ J :=
    Finset.mem_image.mpr ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hJ⟩, rfl⟩
  have hL : 0 < (mrScheduledPrimeInterval p₁ q₁ 1).1 := by
    have hh := (Real.exp_pos (mrLogScheduleLower p₁ q₁ 1)).trans_le (Nat.le_ceil _)
    exact_mod_cast hh
  have hmeas : MeasurableSet (disjointed (mrArithmeticSmallFrequencySet eta p₁ q₁ f) 1) :=
    MeasurableSet.disjointed (measurableSet_mrScheduledSmallFrequencySet _ _ _ _ _) 1
  have hbase := intervalIntegral_typical_le_common_add_primeSquare hI hL hX hmul hbound hmeas hT
  have hcommon := mrArithmetic_common_firstClass_energy_le J heta0 heta1 hp hqexp hpq hbudget hbound hX hscale hT
  have hlowerOne : mrLogScheduleLower p₁ q₁ 1 = p₁ := by
    norm_num [mrLogScheduleLower, mrLogScheduleWeight]
  have herror : 128 * (1 + Real.pi) * (T / X + 1) / (mrScheduledPrimeInterval p₁ q₁ 1).1 ≤
      128 * (1 + Real.pi) * (T / X + 1) * Real.exp (-p₁) := by
    rw [div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left ?_ (by positivity)
    simpa only [hlowerOne] using mrScheduledPrimeInterval_inv_lower_le_exp p₁ q₁ 1
  apply hbase.trans
  have hh := add_le_add (mul_le_mul_of_nonneg_left hcommon (by norm_num : (0 : ℝ) ≤ 2)) herror
  apply hh.trans_eq
  ring

end

end Erdos67b
