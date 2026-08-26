import ErdosProblems.Erdos67b.MRCommonDenominator
import ErdosProblems.Erdos67b.MRMultiplicativeEuler
import ErdosProblems.Erdos67b.MRAppendixLargeValues
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Denominator-weighted Ramaré cofactor series

The denominator in the merely-multiplicative Ramaré identity is not an
innocent truncation of the original `LSeries`: its cofactor coefficient is
`f(k) / (1 + omega_P(k))`.  This file records the correct beta-average
representation.  Scaling the values at the selected primes by `u in [0,1]`
preserves ordinary multiplicativity, and

`1 / (1 + omega_P(k)) = integral u in 0..1, u ^ omega_P(k)`.

This gives an unconditional bridge from the denominator-weighted cofactor
factor to the Euler suppression estimates already proved for merely
multiplicative one-bounded coefficients.
-/

open scoped BigOperators ComplexConjugate Interval
open Finset

namespace Erdos67b

noncomputable section

/-- Scale every selected prime divisor (without multiplicity) by `u`. -/
def mrPrimeScaledCoefficient (P : Finset ℕ) (f : ℕ → ℂ)
    (u : ℝ) (n : ℕ) : ℂ :=
  f n * (u ^ primeDivisorCount P n : ℝ)

theorem primeDivisorSet_mul_eq_union_of_coprime
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {m n : ℕ} (_hcop : m.Coprime n) :
    primeDivisorSet P (m * n) =
      primeDivisorSet P m ∪ primeDivisorSet P n := by
  ext p
  simp only [mem_primeDivisorSet, Finset.mem_union]
  constructor
  · rintro ⟨hpP, hpmn⟩
    rcases (hP p hpP).dvd_mul.mp hpmn with hpm | hpn
    · exact Or.inl ⟨hpP, hpm⟩
    · exact Or.inr ⟨hpP, hpn⟩
  · rintro (⟨hpP, hpm⟩ | ⟨hpP, hpn⟩)
    · exact ⟨hpP, dvd_mul_of_dvd_left hpm n⟩
    · exact ⟨hpP, dvd_mul_of_dvd_right hpn m⟩

theorem disjoint_primeDivisorSet_of_coprime
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {m n : ℕ} (hcop : m.Coprime n) :
    Disjoint (primeDivisorSet P m) (primeDivisorSet P n) := by
  rw [Finset.disjoint_left]
  intro p hpm hpn
  rw [mem_primeDivisorSet] at hpm hpn
  exact (Nat.not_coprime_of_dvd_of_dvd
    (hP p hpm.1).one_lt hpm.2 hpn.2) hcop

theorem primeDivisorCount_mul_of_coprime
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {m n : ℕ} (hcop : m.Coprime n) :
    primeDivisorCount P (m * n) =
      primeDivisorCount P m + primeDivisorCount P n := by
  unfold primeDivisorCount
  rw [primeDivisorSet_mul_eq_union_of_coprime hP hcop,
    Finset.card_union_of_disjoint
      (disjoint_primeDivisorSet_of_coprime hP hcop)]

theorem primeDivisorCount_one
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    primeDivisorCount P 1 = 0 := by
  unfold primeDivisorCount primeDivisorSet
  apply Finset.card_eq_zero.mpr
  rw [Finset.filter_eq_empty_iff]
  intro p hp
  exact (hP p hp).not_dvd_one

theorem primeDivisorCount_prime
    {P : Finset ℕ} (hP : ∀ q ∈ P, q.Prime)
    {p : ℕ} (hp : p.Prime) :
    primeDivisorCount P p = if p ∈ P then 1 else 0 := by
  unfold primeDivisorCount
  by_cases hpP : p ∈ P
  · rw [if_pos hpP]
    have hset : primeDivisorSet P p = {p} := by
      ext q
      simp only [mem_primeDivisorSet, Finset.mem_singleton]
      constructor
      · rintro ⟨hqP, hqp⟩
        exact (Nat.prime_dvd_prime_iff_eq (hP q hqP) hp).mp hqp
      · intro hqp
        subst q
        exact ⟨hpP, dvd_refl p⟩
    rw [hset]
    simp
  · rw [if_neg hpP]
    unfold primeDivisorSet
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro q hqP hqp
    have hqp' : q = p :=
      (Nat.prime_dvd_prime_iff_eq (hP q hqP) hp).mp hqp
    exact hpP (hqp' ▸ hqP)

/-- Prime scaling preserves multiplicativity on positive coprime inputs. -/
theorem mrPrimeScaledCoefficient_isMultiplicative
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (u : ℝ) :
    IsMultiplicativeOnPositiveNat (mrPrimeScaledCoefficient P f u) := by
  constructor
  · simp [mrPrimeScaledCoefficient, hmul.1, primeDivisorCount_one hP]
  · intro m n hm hn hcop
    rw [mrPrimeScaledCoefficient, mrPrimeScaledCoefficient,
      mrPrimeScaledCoefficient, hmul.2 m n hm hn hcop,
      primeDivisorCount_mul_of_coprime hP hcop, pow_add]
    push_cast
    ring

/-- On the beta interval, prime scaling preserves the one-bound. -/
theorem norm_mrPrimeScaledCoefficient_le_one
    {P : Finset ℕ} {f : ℕ → ℂ}
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    {n : ℕ} (hn : 0 < n) :
    ‖mrPrimeScaledCoefficient P f u n‖ ≤ 1 := by
  rw [mrPrimeScaledCoefficient, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hu0 _)]
  have hpow : u ^ primeDivisorCount P n ≤ 1 := by
    exact pow_le_one₀ hu0 hu1
  nlinarith [hbound n hn, norm_nonneg (f n),
    pow_nonneg hu0 (primeDivisorCount P n)]

theorem mrPrimeScaledCoefficient_at_prime
    {P : Finset ℕ} (hP : ∀ q ∈ P, q.Prime)
    (f : ℕ → ℂ) (u : ℝ) {p : ℕ} (hp : p.Prime) :
    mrPrimeScaledCoefficient P f u p =
      if p ∈ P then f p * u else f p := by
  unfold mrPrimeScaledCoefficient
  rw [primeDivisorCount_prime hP hp]
  split_ifs <;> simp

/-- Reciprocal mass lost when the selected primes are scaled toward zero. -/
def mrSelectedPrimeReciprocalMass (P : Finset ℕ) (X : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo X, if p ∈ P then (p : ℝ)⁻¹ else 0

theorem pretentiousTerm_le_scaled_add_inv
    {P : Finset ℕ} (hP : ∀ q ∈ P, q.Prime)
    {f g : ℕ → ℂ} {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    {p : ℕ} (hp : p.Prime) (hf : ‖f p‖ ≤ 1) (hg : ‖g p‖ ≤ 1) :
    pretentiousTerm f g p ≤
      pretentiousTerm (mrPrimeScaledCoefficient P f u) g p +
        (if p ∈ P then (p : ℝ)⁻¹ else 0) := by
  rw [pretentiousTerm, pretentiousTerm,
    mrPrimeScaledCoefficient_at_prime hP f u hp]
  by_cases hpP : p ∈ P
  · rw [if_pos hpP, if_pos hpP]
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hreLower : -1 ≤ (f p * conj (g p)).re := by
      have hreNorm : -‖f p * conj (g p)‖ ≤
          (f p * conj (g p)).re := by
        have habs := Complex.abs_re_le_norm (f p * conj (g p))
        have hneg := neg_le_of_abs_le habs
        exact hneg
      calc
        -1 ≤ -‖f p * conj (g p)‖ := by
          rw [norm_mul, Complex.norm_conj]
          nlinarith [norm_nonneg (f p), norm_nonneg (g p)]
        _ ≤ (f p * conj (g p)).re := hreNorm
    have hreScale : (f p * (u : ℂ) * conj (g p)).re =
        u * (f p * conj (g p)).re := by
      rw [show f p * (u : ℂ) * conj (g p) =
          (u : ℂ) * (f p * conj (g p)) by ring]
      simp [Complex.mul_re]
    rw [hreScale]
    rw [inv_eq_one_div]
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ hpR.le
    have hmul := mul_le_mul_of_nonneg_left hreLower
      (sub_nonneg.mpr hu1)
    nlinarith
  · rw [if_neg hpP, if_neg hpP]
    simp

theorem pretentiousDistSq_le_scaled_add_mass
    {P : Finset ℕ} (hP : ∀ q ∈ P, q.Prime)
    {f g : ℕ → ℂ} {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    {X : ℕ}
    (hf : ∀ p, p.Prime → ‖f p‖ ≤ 1)
    (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) :
    pretentiousDistSq f g X ≤
      pretentiousDistSq (mrPrimeScaledCoefficient P f u) g X +
        mrSelectedPrimeReciprocalMass P X := by
  unfold pretentiousDistSq mrSelectedPrimeReciprocalMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have hp' := (mem_primesUpTo.mp hp).1
  exact pretentiousTerm_le_scaled_add_inv hP hu0 hu1 hp'
    (hf p hp') (hg p hp')

/-- The elementary beta identity for one denominator-weighted coefficient. -/
theorem intervalIntegral_mrPrimeScaledCoefficient
    (P : Finset ℕ) (f : ℕ → ℂ) (n : ℕ) :
    (∫ u in (0 : ℝ)..1, mrPrimeScaledCoefficient P f u n) =
      f n / (mrCommonDenominator P n : ℂ) := by
  unfold mrPrimeScaledCoefficient mrCommonDenominator
  rw [intervalIntegral.integral_const_mul]
  have hcast : (∫ u in (0 : ℝ)..1,
      ((u ^ primeDivisorCount P n : ℝ) : ℂ)) =
      (((∫ u in (0 : ℝ)..1,
        u ^ primeDivisorCount P n) : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_ofReal]
  rw [hcast, integral_pow]
  simp only [one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero]
  rw [div_eq_mul_inv]
  congr 2
  push_cast
  ring

/-- The denominator-weighted cofactor Dirichlet series. -/
def mrCofactorLSeries (P : Finset ℕ) (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  LSeries (fun n ↦ f n / (mrCommonDenominator P n : ℂ)) s

theorem intervalIntegral_mrPrimeScaledCoefficient_LSeries_term
    (P : Finset ℕ) (f : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    (∫ u in (0 : ℝ)..1,
      LSeries.term (mrPrimeScaledCoefficient P f u) s n) =
      LSeries.term
        (fun k ↦ f k / (mrCommonDenominator P k : ℂ)) s n := by
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hn]
    have htermfun :
        (fun u : ℝ ↦ LSeries.term (mrPrimeScaledCoefficient P f u) s n) =
          fun u : ℝ ↦ mrPrimeScaledCoefficient P f u n / (n : ℂ) ^ s := by
      funext u
      rw [LSeries.term_of_ne_zero hn]
    rw [htermfun]
    rw [intervalIntegral.integral_div]
    rw [intervalIntegral_mrPrimeScaledCoefficient]

theorem continuous_mrPrimeScaledCoefficient_LSeries_term
    (P : Finset ℕ) (f : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    Continuous (fun u : ℝ ↦
      LSeries.term (mrPrimeScaledCoefficient P f u) s n) := by
  by_cases hn : n = 0
  · subst n
    simpa [LSeries.term] using
      (continuous_const : Continuous (fun _ : ℝ ↦ (0 : ℂ)))
  · rw [show (fun u : ℝ ↦
        LSeries.term (mrPrimeScaledCoefficient P f u) s n) =
      fun u : ℝ ↦ f n * (u ^ primeDivisorCount P n : ℝ) /
        (n : ℂ) ^ s by
      funext u
      rw [LSeries.term_of_ne_zero hn]
      rfl]
    fun_prop

/-- The complete denominator-weighted cofactor series is exactly the beta
average of multiplicative prime-scaled `LSeries`. -/
theorem mrCofactorLSeries_eq_intervalIntegral
    (P : Finset ℕ) {f : ℕ → ℂ}
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    mrCofactorLSeries P f s =
      ∫ u in (0 : ℝ)..1,
        LSeries (mrPrimeScaledCoefficient P f u) s := by
  let F : ℕ → ℝ → ℂ := fun n u ↦
    LSeries.term (mrPrimeScaledCoefficient P f u) s n
  have hFinterval : ∀ n, IntervalIntegrable (F n)
      MeasureTheory.volume (0 : ℝ) 1 := by
    intro n
    exact (continuous_mrPrimeScaledCoefficient_LSeries_term P f s n).intervalIntegrable _ _
  have hFint : ∀ n, MeasureTheory.IntegrableOn (F n) (Set.Ioc (0 : ℝ) 1) := by
    intro n
    exact (continuous_mrPrimeScaledCoefficient_LSeries_term P f s n).integrableOn_Ioc
  have htermBound (n : ℕ) :
      (∫ u in (0 : ℝ)..1, ‖F n u‖) ≤
        ‖LSeries.term (fun _ ↦ (1 : ℂ)) s n‖ := by
    by_cases hn : n = 0
    · subst n
      simp [F, LSeries.term]
    · have hpoint : ∀ u ∈ Set.Icc (0 : ℝ) 1,
          ‖F n u‖ ≤ ‖LSeries.term (fun _ ↦ (1 : ℂ)) s n‖ := by
        intro u hu
        dsimp only [F]
        rw [LSeries.term_of_ne_zero hn,
          LSeries.term_of_ne_zero hn, norm_div, norm_div, norm_one]
        apply div_le_div_of_nonneg_right _ (norm_nonneg _)
        exact norm_mrPrimeScaledCoefficient_le_one hbound hu.1 hu.2
          (Nat.pos_of_ne_zero hn)
      have hint := intervalIntegral.integral_mono_on
        (show (0 : ℝ) ≤ 1 by norm_num)
        (hFinterval n).norm
        (continuous_const.intervalIntegrable 0 1)
        hpoint
      simpa using hint
  have hsummableMajorant : Summable
      (fun n : ℕ ↦ ‖LSeries.term (fun _ ↦ (1 : ℂ)) s n‖) := by
    exact (LSeriesSummable_of_bounded_of_one_lt_re
      (f := fun _ ↦ (1 : ℂ)) (m := 1) (by simp) hs).norm
  have hsummableIntegral : Summable
      (fun n : ℕ ↦ ∫ u in (0 : ℝ)..1, ‖F n u‖) :=
    hsummableMajorant.of_nonneg_of_le
      (fun n ↦ intervalIntegral.integral_nonneg (by norm_num)
        (fun u hu ↦ norm_nonneg _)) htermBound
  have hinterchange :
      (∑' n : ℕ, ∫ u in (0 : ℝ)..1, F n u) =
        ∫ u in (0 : ℝ)..1, ∑' n : ℕ, F n u := by
    have hsummableSet : Summable
        (fun n : ℕ ↦ ∫ u in Set.Ioc (0 : ℝ) 1, ‖F n u‖) := by
      simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        using hsummableIntegral
    simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      (MeasureTheory.integral_tsum_of_summable_integral_norm
        hFint hsummableSet)
  rw [mrCofactorLSeries, LSeries]
  rw [show (∑' n : ℕ,
      LSeries.term (fun k ↦ f k / (mrCommonDenominator P k : ℂ)) s n) =
      ∑' n : ℕ, ∫ u in (0 : ℝ)..1, F n u by
    apply tsum_congr
    intro n
    exact (intervalIntegral_mrPrimeScaledCoefficient_LSeries_term
      P f s n).symm]
  rw [hinterchange]
  apply intervalIntegral.integral_congr
  intro u hu
  rfl

/-- Uniform Euler suppression for the actual denominator-weighted
cofactor series.  The only extra loss relative to the original coefficient
is the reciprocal mass of the selected prime block. -/
theorem exists_uniform_norm_mrCofactorLSeries_lower_halaszPoint_le :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {P : Finset ℕ}, (∀ p ∈ P, p.Prime) →
      ∀ {f : ℕ → ℂ} {A X Y : ℕ},
        IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) →
        2 ≤ Y → Y < X →
        MRArchimedeanNonpretentious f A X →
        ∀ t : ℝ, |t| ≤ X →
          ‖mrCofactorLSeries P f (MRHalaszEuler.halaszPoint Y t)‖ ≤
            Real.exp
              (Real.log (riemannZeta (EulerResidue.taoExponent Y : ℂ)).re -
                Real.exp (-1) *
                  ((A : ℝ) -
                    2 * (Real.log ((X : ℝ) / (Y + 1 : ℝ)) + C) /
                      Real.log (Y + 1 : ℝ) -
                    mrSelectedPrimeReciprocalMass P Y) +
                3 * EulerQuantitative.primeQuadraticConstant) := by
  obtain ⟨C, hC, hprop⟩ :=
    MRHalaszDistancePropagation.exists_uniform_archimedean_distance_ge_at_lower_cutoff
  refine ⟨C, hC, ?_⟩
  intro P hP f A X Y hmul hbound hY hYX hnonpret t ht
  let E : ℝ := Real.exp
    (Real.log (riemannZeta (EulerResidue.taoExponent Y : ℂ)).re -
      Real.exp (-1) *
        ((A : ℝ) -
          2 * (Real.log ((X : ℝ) / (Y + 1 : ℝ)) + C) /
            Real.log (Y + 1 : ℝ) -
          mrSelectedPrimeReciprocalMass P Y) +
      3 * EulerQuantitative.primeQuadraticConstant)
  have hdistBase :
      (A : ℝ) -
          2 * (Real.log ((X : ℝ) / (Y + 1 : ℝ)) + C) /
            Real.log (Y + 1 : ℝ) ≤
        pretentiousDistSq f (archimedeanTwist t) Y :=
    hprop hY hYX (fun p hp ↦ hbound p hp.pos) hnonpret t ht
  have hpoint : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ‖LSeries (mrPrimeScaledCoefficient P f u)
        (MRHalaszEuler.halaszPoint Y t)‖ ≤ E := by
    intro u hu
    have hdistCompare := pretentiousDistSq_le_scaled_add_mass
      hP hu.1 hu.2 (X := Y)
      (fun p hp ↦ hbound p hp.pos)
      (fun p hp ↦ (norm_archimedeanTwist hp.pos t).le)
    have hdistScaled :
        (A : ℝ) -
            2 * (Real.log ((X : ℝ) / (Y + 1 : ℝ)) + C) /
              Real.log (Y + 1 : ℝ) -
            mrSelectedPrimeReciprocalMass P Y ≤
          pretentiousDistSq (mrPrimeScaledCoefficient P f u)
            (archimedeanTwist t) Y := by
      linarith
    have hbase :=
      MRMultiplicativeEuler.norm_LSeries_halaszPoint_le_exp_logZeta_sub_pretentiousDistSq
        (mrPrimeScaledCoefficient_isMultiplicative hP hmul u)
        (fun n hn ↦ norm_mrPrimeScaledCoefficient_le_one
          hbound hu.1 hu.2 hn)
        (show 1 < Y by omega) t
    refine hbase.trans (Real.exp_le_exp.mpr ?_)
    have hexp : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
    nlinarith
  have hsline : 1 < (MRHalaszEuler.halaszPoint Y t).re := by
    rw [MRHalaszEuler.halaszPoint_re]
    exact EulerResidue.one_lt_taoExponent (show 1 < Y by omega)
  rw [mrCofactorLSeries_eq_intervalIntegral P hbound hsline]
  change ‖∫ u in (0 : ℝ)..1,
    LSeries (mrPrimeScaledCoefficient P f u)
      (MRHalaszEuler.halaszPoint Y t)‖ ≤ E
  have hpoint' : ∀ u ∈ Ι (0 : ℝ) 1,
      ‖LSeries (mrPrimeScaledCoefficient P f u)
        (MRHalaszEuler.halaszPoint Y t)‖ ≤ E := by
    intro u hu
    apply hpoint u
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
    exact ⟨hu.1.le, hu.2⟩
  have hintegral := intervalIntegral.norm_integral_le_of_norm_le_const hpoint'
  simpa only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1), sub_zero,
    mul_one] using hintegral

/-- Finite truncation of the denominator-weighted cofactor series in the
same logarithmic convention as the Ramaré prime factor. -/
def mrCofactorPerronPolynomial (P S : Finset ℕ) (f : ℕ → ℂ)
    (sigma t : ℝ) : ℂ :=
  logarithmicDirichletPolynomial S
    (fun n ↦ f n / (mrCommonDenominator P n : ℂ) *
      Complex.ofReal ((n : ℝ) ^ (-sigma))) (-t)

/-- The canonical finite truncation, stated directly with Mathlib's
`LSeries.term`; this is the form used for exact tail estimates. -/
def mrCofactorLSeriesTruncation
    (P S : Finset ℕ) (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ n ∈ S,
    LSeries.term (fun k ↦ f k / (mrCommonDenominator P k : ℂ)) s n

theorem ofReal_rpow_mul_logarithmicPhase_neg_eq_cpow_neg
    {n : ℕ} (hn : 0 < n) (sigma t : ℝ) :
    Complex.ofReal ((n : ℝ) ^ (-sigma)) * logarithmicPhase n (-t) =
      (n : ℂ) ^ (-((sigma : ℂ) + Complex.I * (t : ℂ))) := by
  rw [show -((sigma : ℂ) + Complex.I * (t : ℂ)) =
      ((-sigma : ℝ) : ℂ) + -(Complex.I * (t : ℂ)) by
    push_cast
    ring]
  rw [Complex.cpow_add _ _ (by exact_mod_cast hn.ne')]
  have hreal : (n : ℂ) ^ ((-sigma : ℝ) : ℂ) =
      Complex.ofReal ((n : ℝ) ^ (-sigma)) := by
    simpa using
      (Complex.ofReal_cpow (show (0 : ℝ) ≤ n by positivity) (-sigma)).symm
  rw [hreal, cpow_neg_I_mul_eq_logarithmicPhase_neg hn t]

/-- The logarithmic finite polynomial is definitionally the canonical
`LSeries.term` truncation on a positive support. -/
theorem mrCofactorPerronPolynomial_eq_LSeriesTruncation
    (P S : Finset ℕ) (f : ℕ → ℂ) (sigma t : ℝ)
    (hSpos : ∀ n ∈ S, 0 < n) :
    mrCofactorPerronPolynomial P S f sigma t =
      mrCofactorLSeriesTruncation P S f
        ((sigma : ℂ) + Complex.I * (t : ℂ)) := by
  unfold mrCofactorPerronPolynomial mrCofactorLSeriesTruncation
    logarithmicDirichletPolynomial
  apply Finset.sum_congr rfl
  intro n hnS
  have hn : 0 < n := hSpos n hnS
  rw [LSeries.term_of_ne_zero hn.ne', div_eq_mul_inv,
    ← Complex.cpow_neg,
    ← ofReal_rpow_mul_logarithmicPhase_neg_eq_cpow_neg hn sigma t]
  ring

/-- Absolute tail left outside a chosen finite cofactor support. -/
def mrCofactorLSeriesTail
    (P S : Finset ℕ) (f : ℕ → ℂ) (s : ℂ) : ℝ :=
  ∑' n : ℕ,
    if n ∈ S then 0
    else ‖LSeries.term
      (fun k ↦ f k / (mrCommonDenominator P k : ℂ)) s n‖

theorem norm_mrCofactorCoefficient_le_one
    {P : Finset ℕ} {f : ℕ → ℂ}
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {n : ℕ} (hn : n ≠ 0) :
    ‖f n / (mrCommonDenominator P n : ℂ)‖ ≤ 1 := by
  rw [norm_div, Complex.norm_natCast]
  have hden : (1 : ℝ) ≤ mrCommonDenominator P n := by
    exact_mod_cast (show 1 ≤ mrCommonDenominator P n by
      unfold mrCommonDenominator
      omega)
  have hdenPos : (0 : ℝ) < mrCommonDenominator P n := zero_lt_one.trans_le hden
  calc
    ‖f n‖ / (mrCommonDenominator P n : ℝ) ≤
        1 / (mrCommonDenominator P n : ℝ) :=
      div_le_div_of_nonneg_right (hbound n (Nat.pos_of_ne_zero hn)) hdenPos.le
    _ ≤ 1 := (div_le_one hdenPos).2 hden

theorem mrCofactorLSeriesSummable
    (P : Finset ℕ) {f : ℕ → ℂ}
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable
      (fun n ↦ f n / (mrCommonDenominator P n : ℂ)) s := by
  apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
  · intro n hn
    exact norm_mrCofactorCoefficient_le_one hbound hn
  · exact hs

/-- Exact full-series/truncation comparison, with no asymptotic notation. -/
theorem norm_mrCofactorLSeries_sub_truncation_le_tail
    (P S : Finset ℕ) {f : ℕ → ℂ}
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    ‖mrCofactorLSeries P f s -
        mrCofactorLSeriesTruncation P S f s‖ ≤
      mrCofactorLSeriesTail P S f s := by
  let a : ℕ → ℂ := fun n ↦
    LSeries.term (fun k ↦ f k / (mrCommonDenominator P k : ℂ)) s n
  let b : ℕ → ℂ := (↑S : Set ℕ).indicator a
  let c : ℕ → ℂ := (↑S : Set ℕ)ᶜ.indicator a
  have ha : Summable a := mrCofactorLSeriesSummable P hbound hs
  have hb : Summable b := ha.indicator (↑S : Set ℕ)
  have hc : Summable c := ha.indicator ((↑S : Set ℕ)ᶜ)
  have habc : ∀ n, a n = b n + c n := by
    intro n
    by_cases hn : n ∈ S
    · simp [b, c, hn]
    · simp [b, c, hn]
  have hsumSplit : (∑' n, a n) = (∑' n, b n) + ∑' n, c n := by
    rw [← hb.tsum_add hc]
    apply tsum_congr
    exact habc
  have hbSum : (∑' n, b n) = ∑ n ∈ S, a n := by
    calc
      (∑' n, b n) = ∑ n ∈ S, b n := by
        apply tsum_eq_sum (s := S)
        intro n hn
        simp [b, hn]
      _ = ∑ n ∈ S, a n := by
        apply Finset.sum_congr rfl
        intro n hn
        simp [b, hn]
  have hcNorm : Summable (fun n ↦ ‖c n‖) := hc.norm
  rw [mrCofactorLSeries, LSeries, mrCofactorLSeriesTruncation]
  change ‖(∑' n, a n) - ∑ n ∈ S, a n‖ ≤ _
  rw [hsumSplit, hbSum, add_sub_cancel_left]
  refine (norm_tsum_le_tsum_norm hcNorm).trans_eq ?_
  unfold mrCofactorLSeriesTail
  apply tsum_congr
  intro n
  by_cases hn : n ∈ S <;> simp [c, hn, a]

theorem norm_mrCofactorLSeriesTruncation_le_full_add_tail
    (P S : Finset ℕ) {f : ℕ → ℂ}
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    ‖mrCofactorLSeriesTruncation P S f s‖ ≤
      ‖mrCofactorLSeries P f s‖ + mrCofactorLSeriesTail P S f s := by
  calc
    ‖mrCofactorLSeriesTruncation P S f s‖ ≤
        ‖mrCofactorLSeries P f s‖ +
          ‖mrCofactorLSeries P f s -
            mrCofactorLSeriesTruncation P S f s‖ := by
      exact norm_le_norm_add_norm_sub
        (mrCofactorLSeries P f s)
        (mrCofactorLSeriesTruncation P S f s)
    _ ≤ ‖mrCofactorLSeries P f s‖ +
        mrCofactorLSeriesTail P S f s := by
      gcongr
      exact norm_mrCofactorLSeries_sub_truncation_le_tail P S hbound hs

/-- The norm of a Dirichlet-series term depends only on the real part of
the exponent.  We record the vertical-line form used to make the finite
cofactor tail uniform in the frequency. -/
theorem norm_LSeries_term_sigma_add_I_mul_eq
    (a : ℕ → ℂ) (sigma t u : ℝ) (n : ℕ) :
    ‖LSeries.term a ((sigma : ℂ) + Complex.I * (t : ℂ)) n‖ =
      ‖LSeries.term a ((sigma : ℂ) + Complex.I * (u : ℂ)) n‖ := by
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
      norm_div, norm_div]
    congr 1
    have hnR : (0 : ℝ) < n := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    calc
      ‖(n : ℂ) ^ ((sigma : ℂ) + Complex.I * (t : ℂ))‖ =
          (n : ℝ) ^ (((sigma : ℂ) + Complex.I * (t : ℂ)).re) := by
        simpa only [Complex.ofReal_natCast] using
          Complex.norm_cpow_eq_rpow_re_of_pos hnR
            ((sigma : ℂ) + Complex.I * (t : ℂ))
      _ = (n : ℝ) ^ (((sigma : ℂ) +
          Complex.I * (u : ℂ)).re) := by simp
      _ = ‖(n : ℂ) ^ ((sigma : ℂ) +
          Complex.I * (u : ℂ))‖ := by
        symm
        simpa only [Complex.ofReal_natCast] using
          Complex.norm_cpow_eq_rpow_re_of_pos hnR
            ((sigma : ℂ) + Complex.I * (u : ℂ))

/-- The absolute truncation tail is constant on a vertical line. -/
theorem mrCofactorLSeriesTail_sigma_add_I_mul_eq
    (P S : Finset ℕ) (f : ℕ → ℂ) (sigma t u : ℝ) :
    mrCofactorLSeriesTail P S f
        ((sigma : ℂ) + Complex.I * (t : ℂ)) =
      mrCofactorLSeriesTail P S f
        ((sigma : ℂ) + Complex.I * (u : ℂ)) := by
  unfold mrCofactorLSeriesTail
  apply tsum_congr
  intro n
  by_cases hn : n ∈ S
  · simp [hn]
  · simp only [hn, if_false]
    exact norm_LSeries_term_sigma_add_I_mul_eq
      (fun k ↦ f k / (mrCommonDenominator P k : ℂ)) sigma t u n

theorem mrCofactorLSeriesTail_halaszPoint_eq_zero
    (P S : Finset ℕ) (f : ℕ → ℂ) (Y : ℕ) (t : ℝ) :
    mrCofactorLSeriesTail P S f (MRHalaszEuler.halaszPoint Y t) =
      mrCofactorLSeriesTail P S f (MRHalaszEuler.halaszPoint Y 0) := by
  unfold MRHalaszEuler.halaszPoint
  exact mrCofactorLSeriesTail_sigma_add_I_mul_eq P S f
    (EulerResidue.taoExponent Y) t 0

/-- Parameter-ready finite cofactor endpoint: beta-averaged Euler
suppression plus the exact finite truncation tail. -/
theorem exists_uniform_norm_mrCofactorLSeriesTruncation_lower_halaszPoint_le :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {P S : Finset ℕ}, (∀ p ∈ P, p.Prime) →
      ∀ {f : ℕ → ℂ} {A X Y : ℕ},
        IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) →
        2 ≤ Y → Y < X →
        MRArchimedeanNonpretentious f A X →
        ∀ t : ℝ, |t| ≤ X →
          ‖mrCofactorLSeriesTruncation P S f
              (MRHalaszEuler.halaszPoint Y t)‖ ≤
            Real.exp
              (Real.log (riemannZeta (EulerResidue.taoExponent Y : ℂ)).re -
                Real.exp (-1) *
                  ((A : ℝ) -
                    2 * (Real.log ((X : ℝ) / (Y + 1 : ℝ)) + C) /
                      Real.log (Y + 1 : ℝ) -
                    mrSelectedPrimeReciprocalMass P Y) +
                3 * EulerQuantitative.primeQuadraticConstant) +
              mrCofactorLSeriesTail P S f
                (MRHalaszEuler.halaszPoint Y t) := by
  obtain ⟨C, hC, hfull⟩ :=
    exists_uniform_norm_mrCofactorLSeries_lower_halaszPoint_le
  refine ⟨C, hC, ?_⟩
  intro P S hP f A X Y hmul hbound hY hYX hnonpret t ht
  have hsline : 1 < (MRHalaszEuler.halaszPoint Y t).re := by
    rw [MRHalaszEuler.halaszPoint_re]
    exact EulerResidue.one_lt_taoExponent (show 1 < Y by omega)
  have htrunc := norm_mrCofactorLSeriesTruncation_le_full_add_tail
    (s := MRHalaszEuler.halaszPoint Y t) P S hbound hsline
  exact htrunc.trans (add_le_add
    (hfull hP hmul hbound hY hYX hnonpret t ht) le_rfl)

/-- Uniform finite Perron-cofactor bound on the Halász vertical line.
The error is the exact absolute tail at height zero; vertical invariance
above makes this a genuinely frequency-uniform quantity. -/
theorem exists_uniform_norm_mrCofactorPerronPolynomial_lower_halaszPoint_le :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {P S : Finset ℕ}, (∀ p ∈ P, p.Prime) →
      ∀ {f : ℕ → ℂ} {A X Y : ℕ},
        IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) →
        (∀ n ∈ S, 0 < n) →
        2 ≤ Y → Y < X →
        MRArchimedeanNonpretentious f A X →
        ∀ t : ℝ, |t| ≤ X →
          ‖mrCofactorPerronPolynomial P S f
              (EulerResidue.taoExponent Y) t‖ ≤
            Real.exp
              (Real.log (riemannZeta (EulerResidue.taoExponent Y : ℂ)).re -
                Real.exp (-1) *
                  ((A : ℝ) -
                    2 * (Real.log ((X : ℝ) / (Y + 1 : ℝ)) + C) /
                      Real.log (Y + 1 : ℝ) -
                    mrSelectedPrimeReciprocalMass P Y) +
                3 * EulerQuantitative.primeQuadraticConstant) +
              mrCofactorLSeriesTail P S f
                (MRHalaszEuler.halaszPoint Y 0) := by
  obtain ⟨C, hC, htrunc⟩ :=
    exists_uniform_norm_mrCofactorLSeriesTruncation_lower_halaszPoint_le
  refine ⟨C, hC, ?_⟩
  intro P S hP f A X Y hmul hbound hSpos hY hYX hnonpret t ht
  rw [mrCofactorPerronPolynomial_eq_LSeriesTruncation
    P S f (EulerResidue.taoExponent Y) t hSpos]
  change ‖mrCofactorLSeriesTruncation P S f
      (MRHalaszEuler.halaszPoint Y t)‖ ≤ _
  simpa only [mrCofactorLSeriesTail_halaszPoint_eq_zero] using
    htrunc hP hmul hbound hY hYX hnonpret t ht

/-- Prime factor at the same Perron exponent as the cofactor factor. -/
def ramarePrimePerronFactorAt
    (sigma : ℝ) (I : ℕ × ℕ) (f : ℕ → ℂ) (t : ℝ) : ℂ :=
  logarithmicDirichletPolynomial (primesInBlock I)
    (weightedPrimeCoefficient f sigma) (-t)

/-- Exact finite product expansion.  In particular, the corrected
denominator remains attached to the cofactor rather than being silently
replaced by the original `LSeries`. -/
theorem ramarePrimePerronFactorAt_mul_mrCofactorPerronPolynomial
    (sigma : ℝ) (I : ℕ × ℕ) (S : Finset ℕ)
    (f : ℕ → ℂ) (t : ℝ) (hSpos : ∀ k ∈ S, 0 < k) :
    ramarePrimePerronFactorAt sigma I f t *
        mrCofactorPerronPolynomial (primesInBlock I) S f sigma t =
      ∑ p ∈ primesInBlock I, ∑ k ∈ S,
        (f p * f k / (mrCommonDenominator (primesInBlock I) k : ℂ)) *
          Complex.ofReal ((p : ℝ) ^ (-sigma)) *
          Complex.ofReal ((k : ℝ) ^ (-sigma)) *
          logarithmicPhase (p * k) (-t) := by
  unfold ramarePrimePerronFactorAt mrCofactorPerronPolynomial
    logarithmicDirichletPolynomial weightedPrimeCoefficient
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk0 : k ≠ 0 := (hSpos k hk).ne'
  have hphase : logarithmicPhase p (-t) * logarithmicPhase k (-t) =
      logarithmicPhase (p * k) (-t) := by
    unfold logarithmicPhase
    rw [← Complex.exp_add]
    congr 1
    rw [Nat.cast_mul, Real.log_mul
      (by exact_mod_cast (mem_primesInBlock.mp hp).1.ne_zero)
      (by exact_mod_cast hk0)]
    push_cast
    ring
  rw [← hphase]
  ring

end

end Erdos67b
