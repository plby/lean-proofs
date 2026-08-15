import ErdosProblems.Erdos448.HalberstamLean
import ErdosProblems.Erdos448.MertensEulerProduct448
import UnitFractions.ForMathlib.BasicEstimates

open scoped BigOperators ArithmeticFunction.omega
open Filter Finset

namespace Prop3ShiftedMean448

/-- The standard positive multiplicative majorant for reciprocal divisor
count, formulated directly with Mathlib's distinct-prime-factor arithmetic
function. -/
noncomputable def halfOmega (n : ℕ) : ℝ :=
  if n = 0 then 0 else
    ((1 : ℝ) / 2) ^ ArithmeticFunction.cardDistinctFactors n

@[simp] lemma halfOmega_zero : halfOmega 0 = 0 := by
  simp [halfOmega]

@[simp] lemma halfOmega_one : halfOmega 1 = 1 := by
  simp [halfOmega]

lemma halfOmega_nonneg (n : ℕ) : 0 ≤ halfOmega n := by
  simp only [halfOmega]
  split_ifs
  · exact le_rfl
  · positivity

lemma halfOmega_le_one (n : ℕ) : halfOmega n ≤ 1 := by
  simp only [halfOmega]
  split_ifs
  · norm_num
  · exact pow_le_one₀ (by norm_num) (by norm_num)

lemma halfOmega_mul_of_coprime {m n : ℕ} (hmn : m.Coprime n) :
    halfOmega (m * n) = halfOmega m * halfOmega n := by
  by_cases hm : m = 0
  · subst m
    have hn : n = 1 := by simpa using hmn
    subst n
    simp
  by_cases hn : n = 0
  · subst n
    have hm1 : m = 1 := by simpa [Nat.coprime_comm] using hmn
    subst m
    simp
  simp only [halfOmega, if_neg hm, if_neg hn, if_neg (Nat.mul_ne_zero hm hn)]
  rw [ArithmeticFunction.cardDistinctFactors_mul hmn, pow_add]

lemma halfOmega_antitone_dvd {m n : ℕ} (hmn : m ∣ n) (hn : n ≠ 0) :
    halfOmega n ≤ halfOmega m := by
  have hm : m ≠ 0 := by
    intro hm0
    subst m
    exact hn (zero_dvd_iff.mp hmn)
  have hpf : m.primeFactors ⊆ n.primeFactors :=
    Nat.primeFactors_mono hmn hn
  have hcard : ArithmeticFunction.cardDistinctFactors m ≤
      ArithmeticFunction.cardDistinctFactors n := by
    simp only [ArithmeticFunction.cardDistinctFactors_apply,
      ← List.card_toFinset, Nat.toFinset_factors]
    exact Finset.card_le_card hpf
  simp only [halfOmega, if_neg hn, if_neg hm]
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hcard

/-- The same weight packaged as an arithmetic function. -/
noncomputable def halfOmegaAF : ArithmeticFunction ℝ :=
  ⟨halfOmega, halfOmega_zero⟩

@[simp] lemma halfOmegaAF_apply (n : ℕ) : halfOmegaAF n = halfOmega n := rfl

/-- The summatory von Mangoldt function on positive naturals. -/
noncomputable def psiNat (Q : ℕ) : ℝ :=
  ∑ d ∈ Finset.Ioc 0 Q, ArithmeticFunction.vonMangoldt d

lemma psiNat_eq_chebyshev (Q : ℕ) : psiNat Q = Chebyshev.psi Q := by
  simp [psiNat, Chebyshev.psi]

lemma psiNat_le_linear (Q : ℕ) :
    psiNat Q ≤ (Real.log 4 + 4) * (Q : ℝ) := by
  rw [psiNat_eq_chebyshev]
  simpa using Chebyshev.psi_le_const_mul_self (x := (Q : ℝ)) (by positivity)

lemma Icc_one_eq_Ioc_zero (N : ℕ) : Finset.Icc 1 N = Finset.Ioc 0 N := by
  ext n
  simp [Nat.succ_le_iff]

lemma halfOmega_mul_log_le_convolution {n : ℕ} (hn : n ≠ 0) :
    halfOmega n * Real.log (n : ℝ) ≤
      (halfOmegaAF * ArithmeticFunction.vonMangoldt) n := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal'
      (fun a b => halfOmegaAF a * ArithmeticFunction.vonMangoldt b)]
  rw [← ArithmeticFunction.vonMangoldt_sum (n := n), Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro d hd
  have hdvd : n / d ∣ n := by
    exact ⟨d, (Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)).symm⟩
  exact mul_le_mul_of_nonneg_right
    (halfOmega_antitone_dvd hdvd hn)
    ArithmeticFunction.vonMangoldt_nonneg

theorem halfOmega_log_moment_convolution (N : ℕ) :
    HalberstamScratch.logPartialSum halfOmega N ≤
      ∑ m ∈ Finset.Icc 1 N, halfOmega m * psiNat (N / m) := by
  have hpoint : ∀ n ∈ Finset.Ioc 0 N,
      halfOmega n * Real.log (n : ℝ) ≤
        (halfOmegaAF * ArithmeticFunction.vonMangoldt) n := by
    intro n hn
    exact halfOmega_mul_log_le_convolution
      (Nat.ne_of_gt (Finset.mem_Ioc.mp hn).1)
  calc
    HalberstamScratch.logPartialSum halfOmega N =
        ∑ n ∈ Finset.Ioc 0 N, halfOmega n * Real.log (n : ℝ) := by
      rw [HalberstamScratch.logPartialSum, Icc_one_eq_Ioc_zero]
    _ ≤ ∑ n ∈ Finset.Ioc 0 N,
        (halfOmegaAF * ArithmeticFunction.vonMangoldt) n :=
      Finset.sum_le_sum hpoint
    _ = ∑ m ∈ Finset.Ioc 0 N, halfOmegaAF m *
        ∑ d ∈ Finset.Ioc 0 (N / m), ArithmeticFunction.vonMangoldt d :=
      ArithmeticFunction.sum_Ioc_mul_eq_sum_sum
        halfOmegaAF ArithmeticFunction.vonMangoldt N
    _ = ∑ m ∈ Finset.Icc 1 N, halfOmega m * psiNat (N / m) := by
      rw [Icc_one_eq_Ioc_zero]
      rfl

theorem halfOmega_mean_le_euler_product (N : ℕ) (hN : 2 ≤ N) :
    HalberstamScratch.partialSum halfOmega N ≤
      ((Real.log 4 + 4) + 1) * (N : ℝ) / Real.log (N : ℝ) *
        ∏ p ∈ (N + 1).primesBelow,
          ∑' j : ℕ, halfOmega (p ^ j) / ((p ^ j : ℕ) : ℝ) := by
  apply HalberstamScratch.halberstam_richert_of_mass_convolution
    halfOmega halfOmega_zero halfOmega_one
    (fun {_ _} hcop => halfOmega_mul_of_coprime hcop)
    halfOmega_nonneg (W := psiNat) (K := Real.log 4 + 4) (N := N)
  · intro p hp
    change Summable (fun j : ℕ =>
      ‖halfOmega (p ^ j) / ((p ^ j : ℕ) : ℝ)‖)
    apply Summable.of_nonneg_of_le
      (fun j => norm_nonneg _)
      (fun j => ?_)
      (summable_geometric_of_norm_lt_one
        (show ‖((p : ℝ)⁻¹)‖ < 1 by
          rw [norm_inv, Real.norm_natCast]
          exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)))
    have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    have hpjpos : 0 < (((p ^ j : ℕ) : ℝ)) := by
      norm_num
      exact pow_pos hpR j
    rw [Real.norm_of_nonneg (div_nonneg (halfOmega_nonneg _) hpjpos.le)]
    calc
      halfOmega (p ^ j) / (((p ^ j : ℕ) : ℝ))
          ≤ 1 / (((p ^ j : ℕ) : ℝ)) :=
        div_le_div_of_nonneg_right (halfOmega_le_one _) hpjpos.le
      _ = ((p : ℝ)⁻¹) ^ j := by
        norm_num [one_div, inv_pow]
  · positivity
  · exact hN
  · exact halfOmega_log_moment_convolution N
  · exact psiNat_le_linear

lemma halfOmega_prime_pow_succ {p j : ℕ} (hp : p.Prime) :
    halfOmega (p ^ (j + 1)) = (1 : ℝ) / 2 := by
  rw [halfOmega, if_neg (pow_ne_zero _ hp.ne_zero),
    ArithmeticFunction.cardDistinctFactors_apply_prime_pow hp (by omega)]
  norm_num

/-- Reciprocal divisor count is pointwise bounded by `2^-omega`. -/
lemma reciprocal_card_divisors_le_halfOmega {n : ℕ} (hn : n ≠ 0) :
    1 / (n.divisors.card : ℝ) ≤ halfOmega n := by
  have hcountNat :
      2 ^ ArithmeticFunction.cardDistinctFactors n ≤ n.divisors.card := by
    simpa [ArithmeticFunction.sigma_zero_apply] using
      two_pow_card_distinct_divisors_le_divisor_count hn
  have hcount :
      ((2 ^ ArithmeticFunction.cardDistinctFactors n : ℕ) : ℝ) ≤
        (n.divisors.card : ℝ) := by exact_mod_cast hcountNat
  have hpowPos : 0 < ((2 ^ ArithmeticFunction.cardDistinctFactors n : ℕ) : ℝ) := by
    positivity
  calc
    1 / (n.divisors.card : ℝ) ≤
        1 / ((2 ^ ArithmeticFunction.cardDistinctFactors n : ℕ) : ℝ) :=
      one_div_le_one_div_of_le hpowPos hcount
    _ = halfOmega n := by
      rw [halfOmega, if_neg hn, Nat.cast_pow]
      rw [one_div_pow]
      simp [one_div]

/-- Multiplying the argument can only increase the divisor count, so the
shift `q` has no cost in this particular reciprocal-divisor estimate. -/
lemma shifted_reciprocal_card_divisors_le_halfOmega (q m : ℕ) :
    1 / ((q * m).divisors.card : ℝ) ≤ halfOmega m := by
  by_cases hq : q = 0
  · subst q
    simp [halfOmega_nonneg]
  by_cases hm : m = 0
  · subst m
    simp
  have hqm : q * m ≠ 0 := Nat.mul_ne_zero hq hm
  have hsubset : m.divisors ⊆ (q * m).divisors :=
    Nat.divisors_subset_of_dvd hqm (dvd_mul_left m q)
  have hcardsNat : m.divisors.card ≤ (q * m).divisors.card :=
    Finset.card_le_card hsubset
  have hcards : (m.divisors.card : ℝ) ≤ ((q * m).divisors.card : ℝ) := by
    exact_mod_cast hcardsNat
  have hmcardPos : 0 < (m.divisors.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hm⟩
  exact (one_div_le_one_div_of_le hmcardPos hcards).trans
    (reciprocal_card_divisors_le_halfOmega hm)

/-- The standard multiplicative weight of divisor-reciprocal type.  At a
positive prime power it is `2 / (nu + 1)`. -/
noncomputable def shiftedReciprocalWeight (q : ℕ) : ℝ :=
  if q = 0 then 0 else
    ((2 ^ ArithmeticFunction.cardDistinctFactors q : ℕ) : ℝ) /
      (q.divisors.card : ℝ)

@[simp] lemma shiftedReciprocalWeight_zero : shiftedReciprocalWeight 0 = 0 := by
  simp [shiftedReciprocalWeight]

@[simp] lemma shiftedReciprocalWeight_one : shiftedReciprocalWeight 1 = 1 := by
  simp [shiftedReciprocalWeight]

lemma shiftedReciprocalWeight_nonneg (q : ℕ) :
    0 ≤ shiftedReciprocalWeight q := by
  simp only [shiftedReciprocalWeight]
  split_ifs
  · exact le_rfl
  · positivity

lemma shiftedReciprocalWeight_mul_of_coprime {q r : ℕ} (hqr : q.Coprime r) :
    shiftedReciprocalWeight (q * r) =
      shiftedReciprocalWeight q * shiftedReciprocalWeight r := by
  by_cases hq : q = 0
  · subst q
    have hr : r = 1 := by simpa using hqr
    subst r
    simp
  by_cases hr : r = 0
  · subst r
    have hq1 : q = 1 := by simpa [Nat.coprime_comm] using hqr
    subst q
    simp
  simp only [shiftedReciprocalWeight, if_neg hq, if_neg hr,
    if_neg (Nat.mul_ne_zero hq hr)]
  rw [ArithmeticFunction.cardDistinctFactors_mul hqr,
    hqr.card_divisors_mul, pow_add, Nat.cast_mul]
  have hqcard : (q.divisors.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr ⟨1, Nat.one_mem_divisors.mpr hq⟩)
  have hrcard : (r.divisors.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr ⟨1, Nat.one_mem_divisors.mpr hr⟩)
  field_simp [hqcard, hrcard]
  norm_cast

lemma shiftedReciprocalWeight_prime_pow_succ {p nu : ℕ} (hp : p.Prime) :
    shiftedReciprocalWeight (p ^ (nu + 1)) = 2 / (nu + 2 : ℝ) := by
  have hpPow : p ^ (nu + 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
  simp only [shiftedReciprocalWeight, if_neg hpPow]
  have htau : (p ^ (nu + 1)).divisors.card = nu + 2 := by
    rw [← ArithmeticFunction.sigma_zero_apply]
    simpa [Nat.add_assoc] using divisor_function_exact_prime_power (nu + 1) hp
  rw [ArithmeticFunction.cardDistinctFactors_apply_prime_pow hp (by omega), htau]
  norm_num

lemma cardDistinctFactors_eq_card_primeFactors (n : ℕ) :
    ArithmeticFunction.cardDistinctFactors n = n.primeFactors.card := by
  rw [ArithmeticFunction.cardDistinctFactors_apply,
    ← List.card_toFinset, Nat.toFinset_factors]

private lemma factorization_eq_zero_of_not_mem_primeFactors {n p : ℕ}
    (hp : p ∉ n.primeFactors) : n.factorization p = 0 := by
  rw [← Nat.support_factorization] at hp
  exact Finsupp.notMem_support_iff.mp hp

private lemma factorization_pos_of_mem_primeFactors {n p : ℕ}
    (hp : p ∈ n.primeFactors) : 0 < n.factorization p := by
  rw [← Nat.support_factorization] at hp
  exact Nat.pos_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp)

/-- Prime by prime, multiplying by `m` creates enough new divisor choices to
pay for every prime of `m` not already occurring in `q`. -/
lemma card_divisors_mul_two_pow_omega_le (q m : ℕ) (hq : q ≠ 0) (hm : m ≠ 0) :
    q.divisors.card * 2 ^ ArithmeticFunction.cardDistinctFactors m ≤
      (q * m).divisors.card * 2 ^ ArithmeticFunction.cardDistinctFactors q := by
  let U := q.primeFactors ∪ m.primeFactors
  have hqm : q * m ≠ 0 := Nat.mul_ne_zero hq hm
  have hqsub : q.primeFactors ⊆ U := Finset.subset_union_left
  have hmsub : m.primeFactors ⊆ U := Finset.subset_union_right
  have hlocal : ∀ p ∈ U,
      ((if p ∈ q.primeFactors then q.factorization p + 1 else 1) *
        (if p ∈ m.primeFactors then 2 else 1)) ≤
      ((q.factorization p + m.factorization p + 1) *
        (if p ∈ q.primeFactors then 2 else 1)) := by
    intro p hpU
    by_cases hpq : p ∈ q.primeFactors
    · by_cases hpm : p ∈ m.primeFactors
      · simp only [hpq, hpm, if_true]
        omega
      · have hmfac : m.factorization p = 0 :=
          factorization_eq_zero_of_not_mem_primeFactors hpm
        simp only [hpq, hpm, if_true, if_false, hmfac]
        omega
    · have hqfac : q.factorization p = 0 :=
        factorization_eq_zero_of_not_mem_primeFactors hpq
      have hpm : p ∈ m.primeFactors := by
        simpa [U, hpq] using hpU
      have hmfac : 0 < m.factorization p :=
        factorization_pos_of_mem_primeFactors hpm
      simp only [hpq, hpm, if_false, if_true, hqfac]
      omega
  rw [Nat.card_divisors hq, Nat.card_divisors hqm,
    cardDistinctFactors_eq_card_primeFactors,
    cardDistinctFactors_eq_card_primeFactors,
    Nat.primeFactors_mul hq hm, Nat.factorization_mul hq hm]
  change
    (∏ p ∈ q.primeFactors, (q.factorization p + 1)) *
        2 ^ m.primeFactors.card ≤
      (∏ p ∈ U, (q.factorization p + m.factorization p + 1)) *
        2 ^ q.primeFactors.card
  calc
    (∏ p ∈ q.primeFactors, (q.factorization p + 1)) *
        2 ^ m.primeFactors.card =
      (∏ p ∈ U,
        (if p ∈ q.primeFactors then q.factorization p + 1 else 1)) *
      (∏ p ∈ U, (if p ∈ m.primeFactors then 2 else 1)) := by
        rw [Finset.prod_ite_mem, Finset.prod_ite_mem]
        simp [U, Finset.prod_const]
    _ = ∏ p ∈ U,
        ((if p ∈ q.primeFactors then q.factorization p + 1 else 1) *
          (if p ∈ m.primeFactors then 2 else 1)) := by
        rw [Finset.prod_mul_distrib]
    _ ≤ ∏ p ∈ U,
        ((q.factorization p + m.factorization p + 1) *
          (if p ∈ q.primeFactors then 2 else 1)) := by
        exact Finset.prod_le_prod' hlocal
    _ = (∏ p ∈ U, (q.factorization p + m.factorization p + 1)) *
        ∏ p ∈ U, (if p ∈ q.primeFactors then 2 else 1) := by
        rw [Finset.prod_mul_distrib]
    _ = (∏ p ∈ U, (q.factorization p + m.factorization p + 1)) *
        2 ^ q.primeFactors.card := by
        rw [Finset.prod_ite_mem]
        simp [U, Finset.prod_const]

/-- Pointwise majorization which retains the full `q`-dependent
divisor-reciprocal weight. -/
lemma shifted_reciprocal_card_divisors_le_weight_mul_halfOmega (q m : ℕ) :
    1 / ((q * m).divisors.card : ℝ) ≤
      shiftedReciprocalWeight q * halfOmega m := by
  by_cases hq : q = 0
  · subst q
    simp
  by_cases hm : m = 0
  · subst m
    simp
  have hqm : q * m ≠ 0 := Nat.mul_ne_zero hq hm
  have hnat := card_divisors_mul_two_pow_omega_le q m hq hm
  have hreal :
      (q.divisors.card : ℝ) *
          ((2 ^ ArithmeticFunction.cardDistinctFactors m : ℕ) : ℝ) ≤
        ((q * m).divisors.card : ℝ) *
          ((2 ^ ArithmeticFunction.cardDistinctFactors q : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hqcard : 0 < (q.divisors.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hq⟩
  have hqmcard : 0 < ((q * m).divisors.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hqm⟩
  have htwoM : 0 < ((2 ^ ArithmeticFunction.cardDistinctFactors m : ℕ) : ℝ) := by
    positivity
  simp only [shiftedReciprocalWeight, if_neg hq,
    halfOmega, if_neg hm]
  rw [one_div_pow]
  norm_num [Nat.cast_pow] at hreal ⊢
  have htwoMReal : 0 < (2 : ℝ) ^ ArithmeticFunction.cardDistinctFactors m := by
    positivity
  change (((q * m).divisors.card : ℝ)⁻¹) ≤
    (((2 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q) /
      (q.divisors.card : ℝ)) *
      (((2 : ℝ) ^ ArithmeticFunction.cardDistinctFactors m)⁻¹)
  rw [show
    (((2 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q) /
      (q.divisors.card : ℝ)) *
      (((2 : ℝ) ^ ArithmeticFunction.cardDistinctFactors m)⁻¹) =
    ((2 : ℝ) ^ ArithmeticFunction.cardDistinctFactors q) /
      ((q.divisors.card : ℝ) *
        ((2 : ℝ) ^ ArithmeticFunction.cardDistinctFactors m)) by ring]
  rw [← one_div]
  rw [div_le_div_iff₀ hqmcard (mul_pos hqcard htwoMReal)]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hreal

/-- An explicit elementary majorant for each local Euler factor. -/
noncomputable def localMajorant (p : ℕ) : ℝ :=
  1 + ((1 : ℝ) / 2) / ((p : ℝ) - 1)

lemma halfOmega_localFactor_le {p : ℕ} (hp : p.Prime) :
    (∑' j : ℕ, halfOmega (p ^ j) / ((p ^ j : ℕ) : ℝ)) ≤ localMajorant p := by
  have h := HalberstamScratch.prime_power_local_mass
    halfOmega p ((1 : ℝ) / 2) 1 hp
    halfOmega_nonneg halfOmega_one (by norm_num) (by norm_num) (by norm_num)
    (fun j => by rw [halfOmega_prime_pow_succ hp]; norm_num)
  have hbound := h.2
  change (∑' j : ℕ,
      ‖halfOmega (p ^ j) / ((p ^ j : ℕ) : ℝ)‖) ≤
        1 + ((1 : ℝ) / 2) / ((p : ℝ) - 1) at hbound
  calc
    (∑' j : ℕ, halfOmega (p ^ j) / ((p ^ j : ℕ) : ℝ)) =
        ∑' j : ℕ, ‖halfOmega (p ^ j) / ((p ^ j : ℕ) : ℝ)‖ := by
      apply tsum_congr
      intro j
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact div_nonneg (halfOmega_nonneg _) (by positivity)
    _ ≤ localMajorant p := by simpa [localMajorant] using hbound

/-- The correction produced by squaring a local factor. -/
noncomputable def localCorrection (p : ℕ) : ℝ :=
  1 + 1 / (4 * (p : ℝ) * ((p : ℝ) - 1))

lemma localMajorant_sq {p : ℕ} (hp : p.Prime) :
    localMajorant p ^ 2 =
      (1 - 1 / (p : ℝ))⁻¹ * localCorrection p := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1R : (p : ℝ) - 1 ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr (by exact_mod_cast hp.one_lt))
  unfold localMajorant localCorrection
  field_simp [hpR, hp1R]
  ring

lemma localCorrection_nonneg (p : ℕ) : 0 ≤ localCorrection p := by
  unfold localCorrection
  by_cases hp : p ≤ 1
  · interval_cases p <;> norm_num
  · have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (show 1 < p by omega)
    have : (0 : ℝ) < (p : ℝ) - 1 := sub_pos.mpr hpR
    positivity

lemma localCorrection_le_exp {p : ℕ} (hp : p.Prime) :
    localCorrection p ≤
      Real.exp (1 / (4 * (p : ℝ) * ((p : ℝ) - 1))) := by
  unfold localCorrection
  simpa [add_comm] using
    (Real.add_one_le_exp (1 / (4 * (p : ℝ) * ((p : ℝ) - 1))))

/-- The reciprocal telescoping sum containing all prime corrections is at
most one. -/
lemma sum_Ico_reciprocal_mul_pred_le_one (N : ℕ) :
    (∑ n ∈ Finset.Ico 2 (N + 1),
      1 / ((n : ℝ) * ((n : ℝ) - 1))) ≤ 1 := by
  by_cases hN : N = 0
  · subst N
    simp
  have htel :
      (∑ i ∈ Finset.Ico 1 N,
        (1 / (i : ℝ) - 1 / ((i + 1 : ℕ) : ℝ))) =
        1 - 1 / (N : ℝ) := by
    have hraw := Finset.sum_Ico_sub (fun i : ℕ => 1 / (i : ℝ))
      (show 1 ≤ N from Nat.one_le_iff_ne_zero.mpr hN)
    rw [Finset.sum_sub_distrib] at hraw ⊢
    linarith
  have hreindex :
      (∑ n ∈ Finset.Ico 2 (N + 1),
        1 / ((n : ℝ) * ((n : ℝ) - 1))) =
      ∑ i ∈ Finset.Ico 1 N,
        (1 / (i : ℝ) - 1 / ((i + 1 : ℕ) : ℝ)) := by
    rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    have hiN : i < N - 1 := Finset.mem_range.mp hi
    push_cast
    have hiPos : (0 : ℝ) < 1 + (i : ℝ) := by positivity
    have hiSuccPos : (0 : ℝ) < 2 + (i : ℝ) := by positivity
    have hiPredPos : (0 : ℝ) < 2 + (i : ℝ) - 1 := by
      have hi0 : (0 : ℝ) ≤ (i : ℝ) := by positivity
      linarith
    field_simp [ne_of_gt hiPos, ne_of_gt hiSuccPos, ne_of_gt hiPredPos]
    ring
  rw [hreindex, htel]
  exact sub_le_self _ (by positivity)

lemma sum_prime_localCorrection_exponents_le_quarter (N : ℕ) :
    (∑ p ∈ (N + 1).primesBelow,
      1 / (4 * (p : ℝ) * ((p : ℝ) - 1))) ≤ 1 / 4 := by
  have hsub : (N + 1).primesBelow ⊆ Finset.Ico 2 (N + 1) := by
    intro p hp
    exact Finset.mem_Ico.mpr
      ⟨Nat.two_le_of_mem_primesBelow hp, Nat.lt_of_mem_primesBelow hp⟩
  calc
    (∑ p ∈ (N + 1).primesBelow,
        1 / (4 * (p : ℝ) * ((p : ℝ) - 1)))
        ≤ ∑ p ∈ Finset.Ico 2 (N + 1),
            1 / (4 * (p : ℝ) * ((p : ℝ) - 1)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro p hpI hpNot
          have hp2 := (Finset.mem_Ico.mp hpI).1
          have hpR : (0 : ℝ) < (p : ℝ) := by positivity
          have hpOneR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (show 1 < p by omega)
          have hp1R : (0 : ℝ) < (p : ℝ) - 1 := sub_pos.mpr hpOneR
          positivity
    _ = (1 / 4) *
          ∑ p ∈ Finset.Ico 2 (N + 1),
            1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          have hp2 := (Finset.mem_Ico.mp hp).1
          have hpR : (0 : ℝ) < (p : ℝ) := by positivity
          have hpOneR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (show 1 < p by omega)
          have hp1R : (0 : ℝ) < (p : ℝ) - 1 := sub_pos.mpr hpOneR
          field_simp [ne_of_gt hpR, ne_of_gt hp1R]
    _ ≤ (1 / 4) * 1 := by
          gcongr
          exact sum_Ico_reciprocal_mul_pred_le_one N
    _ = 1 / 4 := by ring

/-- The product of all quadratic correction factors is uniformly bounded. -/
lemma prod_localCorrection_le_two (N : ℕ) :
    (∏ p ∈ (N + 1).primesBelow, localCorrection p) ≤ 2 := by
  calc
    (∏ p ∈ (N + 1).primesBelow, localCorrection p)
        ≤ ∏ p ∈ (N + 1).primesBelow,
            Real.exp (1 / (4 * (p : ℝ) * ((p : ℝ) - 1))) := by
          apply Finset.prod_le_prod
          · intro p hp
            exact localCorrection_nonneg p
          · intro p hp
            exact localCorrection_le_exp (Nat.prime_of_mem_primesBelow hp)
    _ = Real.exp (∑ p ∈ (N + 1).primesBelow,
          1 / (4 * (p : ℝ) * ((p : ℝ) - 1))) := by
          rw [Real.exp_sum]
    _ ≤ Real.exp (1 / 4) := by
          rw [Real.exp_le_exp]
          exact sum_prime_localCorrection_exponents_le_quarter N
    _ ≤ 2 := by
          rw [← Real.exp_log (show (0 : ℝ) < 2 by norm_num), Real.exp_le_exp]
          linarith [Real.log_two_gt_d9]

/- The following earlier explicit derivation is retained as mathematical
documentation only.  Its imported weak Mertens theorem used project-level
limit overrides, so the checked proof below instead uses the clean
`prime_reciprocal` consequence in `MertensEulerProduct448`. -/
/-
/-- Mertens' theorem and the uniformly convergent quadratic correction give
the exact square-root logarithmic size of the local Euler product. -/
lemma prod_localMajorant_sq_le (N : ℕ) (hN : 3 ≤ N) :
    (∏ p ∈ (N + 1).primesBelow, localMajorant p) ^ 2 ≤
      6 * Real.log (N : ℝ) := by
  let S := (N + 1).primesBelow
  have hmertens :
      1 / (3 * Real.log (N : ℝ)) ≤
        ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
    simpa [S, Nat.primesBelow_eq_filter_range] using former_explicit_product_bound N hN
  have hlogPos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hMertensPos : 0 < ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
    apply Finset.prod_pos
    intro p hp
    have hp1 : (1 : ℝ) < p := by
      exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_lt
    have hpR : (0 : ℝ) < p := hp1.trans' zero_lt_one
    exact sub_pos.mpr ((div_lt_one hpR).mpr hp1)
  have hinv :
      (∏ p ∈ S, (1 - 1 / (p : ℝ)))⁻¹ ≤ 3 * Real.log (N : ℝ) := by
    have hsmallPos : 0 < 1 / (3 * Real.log (N : ℝ)) := by positivity
    have hrecip := one_div_le_one_div_of_le hsmallPos hmertens
    simpa [one_div] using hrecip
  calc
    (∏ p ∈ S, localMajorant p) ^ 2 =
        ∏ p ∈ S, localMajorant p ^ 2 := (Finset.prod_pow S 2 localMajorant).symm
    _ = ∏ p ∈ S,
        ((1 - 1 / (p : ℝ))⁻¹ * localCorrection p) := by
          apply Finset.prod_congr rfl
          intro p hp
          exact localMajorant_sq (Nat.prime_of_mem_primesBelow hp)
    _ = (∏ p ∈ S, (1 - 1 / (p : ℝ)))⁻¹ *
          ∏ p ∈ S, localCorrection p := by
          rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    _ ≤ (3 * Real.log (N : ℝ)) * 2 := by
          exact mul_le_mul hinv (prod_localCorrection_le_two N)
            (Finset.prod_nonneg fun p hp => localCorrection_nonneg p)
            (by positivity)
    _ = 6 * Real.log (N : ℝ) := by ring

lemma prod_localMajorant_le_sqrt (N : ℕ) (hN : 3 ≤ N) :
    (∏ p ∈ (N + 1).primesBelow, localMajorant p) ≤
      Real.sqrt (6 * Real.log (N : ℝ)) := by
  have hprodNonneg :
      0 ≤ ∏ p ∈ (N + 1).primesBelow, localMajorant p := by
    apply Finset.prod_nonneg
    intro p hp
    unfold localMajorant
    have hpOneR : (1 : ℝ) < (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_lt
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := sub_pos.mpr hpOneR
    positivity
  rw [← Real.sqrt_sq hprodNonneg]
  exact Real.sqrt_le_sqrt (prod_localMajorant_sq_le N hN)
-/

/-- A threshold after which the clean second-Mertens consequence controls
the half-Euler product. -/
noncomputable def halfEulerThreshold : ℕ :=
  Classical.choose Erdos448.exists_prime_half_euler_product_threshold

lemma halfEulerThreshold_spec (N : ℕ) (hN : halfEulerThreshold ≤ N) :
    ((Finset.Icc 1 N).filter Nat.Prime).prod
        (fun p => 1 + (2 * ((p : ℝ) - 1))⁻¹) ≤
      Erdos448.mertensHalfEulerConstant *
        Real.sqrt (Real.log (N : ℝ)) := by
  exact (Classical.choose_spec
    Erdos448.exists_prime_half_euler_product_threshold) N hN

lemma localMajorant_nonneg_on_primes {p : ℕ} (hp : p.Prime) :
    0 ≤ localMajorant p := by
  unfold localMajorant
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    exact sub_pos.mpr (by exact_mod_cast hp.one_lt)
  positivity

lemma localMajorant_eq_clean_factor {p : ℕ} (hp : p.Prime) :
    localMajorant p = 1 + (2 * ((p : ℝ) - 1))⁻¹ := by
  unfold localMajorant
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr (by exact_mod_cast hp.one_lt))
  field_simp [hp1]

lemma primesBelow_succ_eq_filter_Icc (N : ℕ) :
    (N + 1).primesBelow = (Finset.Icc 1 N).filter Nat.Prime := by
  ext p
  simp only [Nat.mem_primesBelow, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hpN, hp⟩
    exact ⟨⟨hp.one_le, Nat.le_of_lt_succ hpN⟩, hp⟩
  · rintro ⟨⟨_hp1, hpN⟩, hp⟩
    exact ⟨Nat.lt_succ_of_le hpN, hp⟩

/-- A uniform constant obtained by adjoining the finitely many values below
the asymptotic Mertens threshold. -/
noncomputable def localMajorantUniformConstant : ℝ :=
  Erdos448.mertensHalfEulerConstant +
    ∑ N ∈ Finset.Icc 3 halfEulerThreshold,
      ∏ p ∈ (N + 1).primesBelow, localMajorant p

lemma localMajorantUniformConstant_pos :
    0 < localMajorantUniformConstant := by
  unfold localMajorantUniformConstant
  apply add_pos_of_pos_of_nonneg Erdos448.mertensHalfEulerConstant_pos
  apply Finset.sum_nonneg
  intro N hN
  exact Finset.prod_nonneg fun p hp =>
    localMajorant_nonneg_on_primes (Nat.prime_of_mem_primesBelow hp)

/-- Clean uniform square-root-logarithmic Euler-product bound, deduced only
from `prime_reciprocal` (through `MertensEulerProduct448`) and a finite
initial segment absorbed into the constant. -/
lemma prod_localMajorant_le_sqrt (N : ℕ) (hN : 3 ≤ N) :
    (∏ p ∈ (N + 1).primesBelow, localMajorant p) ≤
      localMajorantUniformConstant * Real.sqrt (Real.log (N : ℝ)) := by
  have hprodNonneg :
      0 ≤ ∏ p ∈ (N + 1).primesBelow, localMajorant p := by
    exact Finset.prod_nonneg fun p hp =>
      localMajorant_nonneg_on_primes (Nat.prime_of_mem_primesBelow hp)
  have hsumNonneg :
      0 ≤ ∑ n ∈ Finset.Icc 3 halfEulerThreshold,
          ∏ p ∈ (n + 1).primesBelow, localMajorant p := by
    apply Finset.sum_nonneg
    intro n hn
    exact Finset.prod_nonneg fun p hp =>
      localMajorant_nonneg_on_primes (Nat.prime_of_mem_primesBelow hp)
  by_cases hlarge : halfEulerThreshold ≤ N
  · have hclean := halfEulerThreshold_spec N hlarge
    have heq :
        (∏ p ∈ (N + 1).primesBelow, localMajorant p) =
          ((Finset.Icc 1 N).filter Nat.Prime).prod
            (fun p => 1 + (2 * ((p : ℝ) - 1))⁻¹) := by
      rw [primesBelow_succ_eq_filter_Icc]
      apply Finset.prod_congr rfl
      intro p hp
      exact localMajorant_eq_clean_factor (Finset.mem_filter.mp hp).2
    rw [heq]
    exact hclean.trans (mul_le_mul_of_nonneg_right
      (by
        unfold localMajorantUniformConstant
        exact le_add_of_nonneg_right hsumNonneg)
      (Real.sqrt_nonneg _))
  · have hmem : N ∈ Finset.Icc 3 halfEulerThreshold :=
      Finset.mem_Icc.mpr ⟨hN, Nat.le_of_lt (Nat.lt_of_not_ge hlarge)⟩
    have hterm :
        (∏ p ∈ (N + 1).primesBelow, localMajorant p) ≤
          ∑ n ∈ Finset.Icc 3 halfEulerThreshold,
            ∏ p ∈ (n + 1).primesBelow, localMajorant p := by
      let F : ℕ → ℝ := fun n =>
        ∏ p ∈ (n + 1).primesBelow, localMajorant p
      change F N ≤ ∑ n ∈ Finset.Icc 3 halfEulerThreshold, F n
      exact Finset.single_le_sum (a := N)
        (fun n hn => by
          dsimp only [F]
          exact Finset.prod_nonneg fun p hp =>
            localMajorant_nonneg_on_primes
              (Nat.prime_of_mem_primesBelow hp)) hmem
    have hsum_le_constant :
        (∑ n ∈ Finset.Icc 3 halfEulerThreshold,
            ∏ p ∈ (n + 1).primesBelow, localMajorant p) ≤
          localMajorantUniformConstant := by
      unfold localMajorantUniformConstant
      exact le_add_of_nonneg_left Erdos448.mertensHalfEulerConstant_pos.le
    have hlogOne : (1 : ℝ) ≤ Real.log (N : ℝ) := by
      have hlogThree : (1 : ℝ) ≤ Real.log 3 := by
        linarith [Real.log_three_gt_d9]
      exact hlogThree.trans (Real.log_le_log (by norm_num)
        (by exact_mod_cast hN))
    have hsqrtOne : (1 : ℝ) ≤ Real.sqrt (Real.log (N : ℝ)) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hlogOne
    have hconstantNonneg : 0 ≤ localMajorantUniformConstant :=
      localMajorantUniformConstant_pos.le
    exact hterm.trans (hsum_le_constant.trans
      (by nlinarith))

/- The following coarse unshifted wrappers are superseded by the sharper
normalized-tau theorem below. -/
/-
/-- The assembled `2^-omega` mean estimate. -/
theorem halfOmega_partialSum_le (N : ℕ) (hN : 3 ≤ N) :
    HalberstamScratch.partialSum halfOmega N ≤
      (Real.log 4 + 5) * Real.sqrt 6 * (N : ℝ) /
        Real.sqrt (Real.log (N : ℝ)) := by
  have hmean := halfOmega_mean_le_euler_product N (by omega)
  have hprod :
      (∏ p ∈ (N + 1).primesBelow,
          ∑' j : ℕ, halfOmega (p ^ j) / ((p ^ j : ℕ) : ℝ)) ≤
        ∏ p ∈ (N + 1).primesBelow, localMajorant p := by
    apply Finset.prod_le_prod
    · intro p hp
      exact tsum_nonneg fun j =>
        div_nonneg (halfOmega_nonneg _) (by positivity)
    · intro p hp
      exact halfOmega_localFactor_le (Nat.prime_of_mem_primesBelow hp)
  have hlogPos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hcoeffNonneg :
      0 ≤ (Real.log 4 + 5) * (N : ℝ) / Real.log (N : ℝ) := by positivity
  calc
    HalberstamScratch.partialSum halfOmega N
        ≤ (Real.log 4 + 5) * (N : ℝ) / Real.log (N : ℝ) *
            ∏ p ∈ (N + 1).primesBelow,
              ∑' j : ℕ, halfOmega (p ^ j) / ((p ^ j : ℕ) : ℝ) := by
          convert hmean using 1 <;> ring
    _ ≤ (Real.log 4 + 5) * (N : ℝ) / Real.log (N : ℝ) *
          ∏ p ∈ (N + 1).primesBelow, localMajorant p :=
      mul_le_mul_of_nonneg_left hprod hcoeffNonneg
    _ ≤ (Real.log 4 + 5) * (N : ℝ) / Real.log (N : ℝ) *
          Real.sqrt (6 * Real.log (N : ℝ)) := by
      gcongr
      exact prod_localMajorant_le_sqrt N hN
    _ = (Real.log 4 + 5) * Real.sqrt 6 * (N : ℝ) /
          Real.sqrt (Real.log (N : ℝ)) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 6)]
      have hsqrtPos : 0 < Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_pos.2 hlogPos
      have hsqrtSq : Real.sqrt (Real.log (N : ℝ)) ^ 2 = Real.log (N : ℝ) :=
        Real.sq_sqrt hlogPos.le
      field_simp [hlogPos.ne', hsqrtPos.ne']
      nlinarith

/-- Specialized shifted reciprocal-divisor mean.  The explicit auxiliary
weight is the constant function `w(q)=1`. -/
theorem shifted_reciprocal_divisor_mean (q z : ℕ) (hz : 3 ≤ z) :
    (∑ m ∈ Finset.range z,
      1 / ((q * m).divisors.card : ℝ)) ≤
      (Real.log 4 + 5) * Real.sqrt 12 * (z : ℝ) /
        Real.sqrt (Real.log (2 * (z : ℝ))) := by
  have hpoint :
      (∑ m ∈ Finset.range z, 1 / ((q * m).divisors.card : ℝ)) ≤
        HalberstamScratch.partialSum halfOmega z := by
    unfold HalberstamScratch.partialSum
    have hrange : Finset.range z = {0} ∪ Finset.Ico 1 z := by
      ext m
      simp
      omega
    rw [hrange, Finset.sum_union]
    · simp only [Finset.sum_singleton]
      have hzero : 1 / ((q * 0).divisors.card : ℝ) = 0 := by simp
      rw [hzero, zero_add]
      calc
        (∑ m ∈ Finset.Ico 1 z, 1 / ((q * m).divisors.card : ℝ)) ≤
            ∑ m ∈ Finset.Ico 1 z, halfOmega m := by
              apply Finset.sum_le_sum
              intro m hm
              exact shifted_reciprocal_card_divisors_le_halfOmega q m
        _ ≤ ∑ m ∈ Finset.Icc 1 z, halfOmega m := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro m hm
                exact Finset.mem_Icc.mpr
                  ⟨(Finset.mem_Ico.mp hm).1, (Finset.mem_Ico.mp hm).2.le⟩
              · intro m hm hnot
                exact halfOmega_nonneg m
    · simp
  have hmean := halfOmega_partialSum_le z hz
  have hlogzPos : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hlogTwozPos : 0 < Real.log (2 * (z : ℝ)) := by
    apply Real.log_pos
    have hzR : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
    nlinarith
  have hlogCompare : Real.log (2 * (z : ℝ)) ≤ 2 * Real.log (z : ℝ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (z : ℝ) ≠ 0)]
    have hlog2_le_logz : Real.log 2 ≤ Real.log (z : ℝ) := by
      gcongr
      exact_mod_cast (show 2 ≤ z by omega)
    linarith
  have hsqrtCompare :
      Real.sqrt (Real.log (2 * (z : ℝ))) ≤
        Real.sqrt 2 * Real.sqrt (Real.log (z : ℝ)) := by
    calc
      Real.sqrt (Real.log (2 * (z : ℝ))) ≤
          Real.sqrt (2 * Real.log (z : ℝ)) := Real.sqrt_le_sqrt hlogCompare
      _ = Real.sqrt 2 * Real.sqrt (Real.log (z : ℝ)) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    (∑ m ∈ Finset.range z, 1 / ((q * m).divisors.card : ℝ))
        ≤ HalberstamScratch.partialSum halfOmega z := hpoint
    _ ≤ (Real.log 4 + 5) * Real.sqrt 6 * (z : ℝ) /
          Real.sqrt (Real.log (z : ℝ)) := hmean
    _ ≤ (Real.log 4 + 5) * Real.sqrt 12 * (z : ℝ) /
          Real.sqrt (Real.log (2 * (z : ℝ))) := by
      have hsqrtzPos : 0 < Real.sqrt (Real.log (z : ℝ)) := Real.sqrt_pos.2 hlogzPos
      have hsqrt2Pos : 0 < Real.sqrt (2 : ℝ) := by positivity
      have hsqrtTwozPos : 0 < Real.sqrt (Real.log (2 * (z : ℝ))) :=
        Real.sqrt_pos.2 hlogTwozPos
      have hsqrt12 : Real.sqrt (12 : ℝ) = Real.sqrt 2 * Real.sqrt 6 := by
        rw [show (12 : ℝ) = 2 * 6 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      rw [hsqrt12]
      rw [div_le_div_iff₀ hsqrtzPos hsqrtTwozPos]
      have hbase : 0 ≤ (Real.log 4 + 5) * Real.sqrt 6 * (z : ℝ) := by positivity
      nlinarith

/-- The strengthened shifted estimate with its multiplicative
divisor-reciprocal weight exposed. -/
theorem shifted_reciprocal_divisor_mean_weighted (q z : ℕ) (hz : 3 ≤ z) :
    (∑ m ∈ Finset.range z,
      1 / ((q * m).divisors.card : ℝ)) ≤
      (Real.log 4 + 5) * Real.sqrt 12 * (z : ℝ) *
        shiftedReciprocalWeight q /
          Real.sqrt (Real.log (2 * (z : ℝ))) := by
  have hpoint :
      (∑ m ∈ Finset.range z, 1 / ((q * m).divisors.card : ℝ)) ≤
        shiftedReciprocalWeight q *
          HalberstamScratch.partialSum halfOmega z := by
    unfold HalberstamScratch.partialSum
    have hrange : Finset.range z = {0} ∪ Finset.Ico 1 z := by
      ext m
      simp
      omega
    rw [hrange, Finset.sum_union]
    · simp only [Finset.sum_singleton]
      have hzero : 1 / ((q * 0).divisors.card : ℝ) = 0 := by simp
      rw [hzero, zero_add]
      calc
        (∑ m ∈ Finset.Ico 1 z, 1 / ((q * m).divisors.card : ℝ)) ≤
            ∑ m ∈ Finset.Ico 1 z,
              shiftedReciprocalWeight q * halfOmega m := by
                apply Finset.sum_le_sum
                intro m hm
                exact shifted_reciprocal_card_divisors_le_weight_mul_halfOmega q m
        _ = shiftedReciprocalWeight q *
              ∑ m ∈ Finset.Ico 1 z, halfOmega m := by
                rw [Finset.mul_sum]
        _ ≤ shiftedReciprocalWeight q *
              ∑ m ∈ Finset.Icc 1 z, halfOmega m := by
                apply mul_le_mul_of_nonneg_left
                · apply Finset.sum_le_sum_of_subset_of_nonneg
                  · intro m hm
                    exact Finset.mem_Icc.mpr
                      ⟨(Finset.mem_Ico.mp hm).1, (Finset.mem_Ico.mp hm).2.le⟩
                  · intro m hm hnot
                    exact halfOmega_nonneg m
                · exact shiftedReciprocalWeight_nonneg q
    · simp
  have hmean := halfOmega_partialSum_le z hz
  have hlogzPos : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hlogTwozPos : 0 < Real.log (2 * (z : ℝ)) := by
    apply Real.log_pos
    have hzR : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
    nlinarith
  have hlogCompare : Real.log (2 * (z : ℝ)) ≤ 2 * Real.log (z : ℝ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (z : ℝ) ≠ 0)]
    have hlog2_le_logz : Real.log 2 ≤ Real.log (z : ℝ) := by
      gcongr
      exact_mod_cast (show 2 ≤ z by omega)
    linarith
  have hsqrtCompare :
      Real.sqrt (Real.log (2 * (z : ℝ))) ≤
        Real.sqrt 2 * Real.sqrt (Real.log (z : ℝ)) := by
    calc
      Real.sqrt (Real.log (2 * (z : ℝ))) ≤
          Real.sqrt (2 * Real.log (z : ℝ)) := Real.sqrt_le_sqrt hlogCompare
      _ = Real.sqrt 2 * Real.sqrt (Real.log (z : ℝ)) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hscaled :
      (Real.log 4 + 5) * Real.sqrt 6 * (z : ℝ) /
          Real.sqrt (Real.log (z : ℝ)) ≤
        (Real.log 4 + 5) * Real.sqrt 12 * (z : ℝ) /
          Real.sqrt (Real.log (2 * (z : ℝ))) := by
    have hsqrtzPos : 0 < Real.sqrt (Real.log (z : ℝ)) := Real.sqrt_pos.2 hlogzPos
    have hsqrtTwozPos : 0 < Real.sqrt (Real.log (2 * (z : ℝ))) :=
      Real.sqrt_pos.2 hlogTwozPos
    have hsqrt12 : Real.sqrt (12 : ℝ) = Real.sqrt 2 * Real.sqrt 6 := by
      rw [show (12 : ℝ) = 2 * 6 by norm_num,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hsqrt12, div_le_div_iff₀ hsqrtzPos hsqrtTwozPos]
    have hbase : 0 ≤ (Real.log 4 + 5) * Real.sqrt 6 * (z : ℝ) := by positivity
    nlinarith
  calc
    (∑ m ∈ Finset.range z, 1 / ((q * m).divisors.card : ℝ))
        ≤ shiftedReciprocalWeight q *
            HalberstamScratch.partialSum halfOmega z := hpoint
    _ ≤ shiftedReciprocalWeight q *
          ((Real.log 4 + 5) * Real.sqrt 6 * (z : ℝ) /
            Real.sqrt (Real.log (z : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hmean (shiftedReciprocalWeight_nonneg q)
    _ ≤ shiftedReciprocalWeight q *
          ((Real.log 4 + 5) * Real.sqrt 12 * (z : ℝ) /
            Real.sqrt (Real.log (2 * (z : ℝ)))) := by
      exact mul_le_mul_of_nonneg_left hscaled (shiftedReciprocalWeight_nonneg q)
    _ = (Real.log 4 + 5) * Real.sqrt 12 * (z : ℝ) *
          shiftedReciprocalWeight q /
            Real.sqrt (Real.log (2 * (z : ℝ))) := by ring

-/
/-! ## Sharper `tau⁻¹`-type weight

The preceding pointwise weight is useful but loses a factor two at every
prime dividing the shift.  The Halberstam--Richert argument itself retains
that factor.  We now package the normalized function
`tau(q) / tau(qm)` and expose the sharper correction.
-/

private lemma card_divisors_eq_prod_of_primeFactors_subset
    {n : ℕ} (hn : n ≠ 0) (S : Finset ℕ) (hsub : n.primeFactors ⊆ S) :
    n.divisors.card = ∏ p ∈ S, (n.factorization p + 1) := by
  rw [Nat.card_divisors hn]
  apply Finset.prod_subset hsub
  intro p hpS hpNot
  rw [factorization_eq_zero_of_not_mem_primeFactors hpNot]
  simp

/-- The shifted divisor counts obey the four-term identity needed for
multiplicativity of `tau(q)/tau(qm)`. -/
lemma card_divisors_shifted_coprime_identity
    {q m n : ℕ} (hq : q ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0)
    (hmn : m.Coprime n) :
    (q * m).divisors.card * (q * n).divisors.card =
      q.divisors.card * (q * (m * n)).divisors.card := by
  let U := q.primeFactors ∪ m.primeFactors ∪ n.primeFactors
  have hqm : q * m ≠ 0 := Nat.mul_ne_zero hq hm
  have hqn : q * n ≠ 0 := Nat.mul_ne_zero hq hn
  have hmn0 : m * n ≠ 0 := Nat.mul_ne_zero hm hn
  have hqmn : q * (m * n) ≠ 0 := Nat.mul_ne_zero hq hmn0
  have hqsub : q.primeFactors ⊆ U := by
    intro p hp
    simp [U, hp]
  have hqmsub : (q * m).primeFactors ⊆ U := by
    rw [Nat.primeFactors_mul hq hm]
    exact fun p hp => by
      unfold U
      exact Finset.mem_union_left _ hp
  have hqnsub : (q * n).primeFactors ⊆ U := by
    rw [Nat.primeFactors_mul hq hn]
    intro p hp
    unfold U
    rcases Finset.mem_union.mp hp with hpq | hpn
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hpq)))
    · exact Finset.mem_union.mpr (Or.inr hpn)
  have hqmnsub : (q * (m * n)).primeFactors ⊆ U := by
    rw [Nat.primeFactors_mul hq hmn0, Nat.primeFactors_mul hm hn]
    intro p hp
    simpa [U, Finset.union_assoc] using hp
  rw [card_divisors_eq_prod_of_primeFactors_subset hqm U hqmsub,
    card_divisors_eq_prod_of_primeFactors_subset hqn U hqnsub,
    card_divisors_eq_prod_of_primeFactors_subset hq U hqsub,
    card_divisors_eq_prod_of_primeFactors_subset hqmn U hqmnsub]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hpU
  rw [Nat.factorization_mul hq hm, Nat.factorization_mul hq hn,
    Nat.factorization_mul hq hmn0, Nat.factorization_mul hm hn]
  have hzero : m.factorization p = 0 ∨ n.factorization p = 0 := by
    by_cases hpm : p ∈ m.primeFactors
    · right
      apply factorization_eq_zero_of_not_mem_primeFactors
      exact fun hpn => (Finset.disjoint_left.mp hmn.disjoint_primeFactors) hpm hpn
    · exact Or.inl (factorization_eq_zero_of_not_mem_primeFactors hpm)
  rcases hzero with hzero | hzero <;> simp [hzero] <;> ring

/-- The normalized shifted reciprocal divisor function. -/
noncomputable def normalizedTauRatio (q m : ℕ) : ℝ :=
  if q = 0 ∨ m = 0 then 0 else
    (q.divisors.card : ℝ) / ((q * m).divisors.card : ℝ)

@[simp] lemma normalizedTauRatio_zero_right (q : ℕ) :
    normalizedTauRatio q 0 = 0 := by simp [normalizedTauRatio]

lemma normalizedTauRatio_one {q : ℕ} (hq : q ≠ 0) :
    normalizedTauRatio q 1 = 1 := by
  simp [normalizedTauRatio, hq]

lemma normalizedTauRatio_nonneg (q m : ℕ) : 0 ≤ normalizedTauRatio q m := by
  simp only [normalizedTauRatio]
  split_ifs
  · exact le_rfl
  · positivity

lemma normalizedTauRatio_le_one (q m : ℕ) : normalizedTauRatio q m ≤ 1 := by
  simp only [normalizedTauRatio]
  split_ifs with h
  · norm_num
  · push_neg at h
    have hqm : q * m ≠ 0 := Nat.mul_ne_zero h.1 h.2
    have hsub := Nat.divisors_subset_of_dvd hqm (dvd_mul_right q m)
    have hcard : q.divisors.card ≤ (q * m).divisors.card := Finset.card_le_card hsub
    have hden : 0 < ((q * m).divisors.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hqm⟩
    rw [div_le_iff₀ hden]
    have hcardR : (q.divisors.card : ℝ) ≤ ((q * m).divisors.card : ℝ) := by
      exact_mod_cast hcard
    simpa using hcardR

lemma normalizedTauRatio_mul_of_coprime {q m n : ℕ} (hq : q ≠ 0)
    (hmn : m.Coprime n) :
    normalizedTauRatio q (m * n) =
      normalizedTauRatio q m * normalizedTauRatio q n := by
  by_cases hm : m = 0
  · subst m
    have hn : n = 1 := by simpa using hmn
    subst n
    simp [normalizedTauRatio]
  by_cases hn : n = 0
  · subst n
    have hm1 : m = 1 := by simpa [Nat.coprime_comm] using hmn
    subst m
    simp [normalizedTauRatio]
  have hmn0 : m * n ≠ 0 := Nat.mul_ne_zero hm hn
  have hqm : q * m ≠ 0 := Nat.mul_ne_zero hq hm
  have hqn : q * n ≠ 0 := Nat.mul_ne_zero hq hn
  have hqmn : q * (m * n) ≠ 0 := Nat.mul_ne_zero hq hmn0
  simp only [normalizedTauRatio, if_neg (not_or_intro hq hmn0),
    if_neg (not_or_intro hq hm), if_neg (not_or_intro hq hn)]
  have hqcard : (q.divisors.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr ⟨1, Nat.one_mem_divisors.mpr hq⟩
  have hqmcard : ((q * m).divisors.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr ⟨1, Nat.one_mem_divisors.mpr hqm⟩
  have hqncard : ((q * n).divisors.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr ⟨1, Nat.one_mem_divisors.mpr hqn⟩
  have hqmncard : ((q * (m * n)).divisors.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr ⟨1, Nat.one_mem_divisors.mpr hqmn⟩
  field_simp [hqcard, hqmcard, hqncard, hqmncard]
  have hid := card_divisors_shifted_coprime_identity hq hm hn hmn
  norm_cast

lemma normalizedTauRatio_antitone_dvd {q d n : ℕ} (hq : q ≠ 0)
    (hdn : d ∣ n) (hn : n ≠ 0) :
    normalizedTauRatio q n ≤ normalizedTauRatio q d := by
  have hd : d ≠ 0 := by
    intro hd0
    subst d
    exact hn (zero_dvd_iff.mp hdn)
  have hqd : q * d ≠ 0 := Nat.mul_ne_zero hq hd
  have hqn : q * n ≠ 0 := Nat.mul_ne_zero hq hn
  have hmulDvd : q * d ∣ q * n := Nat.mul_dvd_mul_left q hdn
  have hsub := Nat.divisors_subset_of_dvd hqn hmulDvd
  have hcard : (q * d).divisors.card ≤ (q * n).divisors.card :=
    Finset.card_le_card hsub
  simp only [normalizedTauRatio, if_neg (not_or_intro hq hn),
    if_neg (not_or_intro hq hd)]
  have hqnonneg : 0 ≤ (q.divisors.card : ℝ) := by positivity
  have hqdpos : 0 < ((q * d).divisors.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hqd⟩
  exact div_le_div₀ hqnonneg le_rfl hqdpos (by exact_mod_cast hcard)

noncomputable def normalizedTauRatioAF (q : ℕ) : ArithmeticFunction ℝ :=
  ⟨normalizedTauRatio q, normalizedTauRatio_zero_right q⟩

lemma normalizedTauRatio_mul_log_le_convolution {q n : ℕ}
    (hq : q ≠ 0) (hn : n ≠ 0) :
    normalizedTauRatio q n * Real.log (n : ℝ) ≤
      (normalizedTauRatioAF q * ArithmeticFunction.vonMangoldt) n := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal'
      (fun a b => normalizedTauRatioAF q a * ArithmeticFunction.vonMangoldt b)]
  rw [← ArithmeticFunction.vonMangoldt_sum (n := n), Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro d hd
  have hdvd : n / d ∣ n := by
    exact ⟨d, (Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)).symm⟩
  exact mul_le_mul_of_nonneg_right
    (normalizedTauRatio_antitone_dvd hq hdvd hn)
    ArithmeticFunction.vonMangoldt_nonneg

theorem normalizedTauRatio_log_moment_convolution (q N : ℕ) (hq : q ≠ 0) :
    HalberstamScratch.logPartialSum (normalizedTauRatio q) N ≤
      ∑ m ∈ Finset.Icc 1 N, normalizedTauRatio q m * psiNat (N / m) := by
  have hpoint : ∀ n ∈ Finset.Ioc 0 N,
      normalizedTauRatio q n * Real.log (n : ℝ) ≤
        (normalizedTauRatioAF q * ArithmeticFunction.vonMangoldt) n := by
    intro n hn
    exact normalizedTauRatio_mul_log_le_convolution hq
      (Nat.ne_of_gt (Finset.mem_Ioc.mp hn).1)
  calc
    HalberstamScratch.logPartialSum (normalizedTauRatio q) N =
        ∑ n ∈ Finset.Ioc 0 N,
          normalizedTauRatio q n * Real.log (n : ℝ) := by
      rw [HalberstamScratch.logPartialSum, Icc_one_eq_Ioc_zero]
    _ ≤ ∑ n ∈ Finset.Ioc 0 N,
        (normalizedTauRatioAF q * ArithmeticFunction.vonMangoldt) n :=
      Finset.sum_le_sum hpoint
    _ = ∑ m ∈ Finset.Ioc 0 N, normalizedTauRatioAF q m *
        ∑ d ∈ Finset.Ioc 0 (N / m), ArithmeticFunction.vonMangoldt d :=
      ArithmeticFunction.sum_Ioc_mul_eq_sum_sum
        (normalizedTauRatioAF q) ArithmeticFunction.vonMangoldt N
    _ = ∑ m ∈ Finset.Icc 1 N,
        normalizedTauRatio q m * psiNat (N / m) := by
      rw [Icc_one_eq_Ioc_zero]
      rfl

theorem normalizedTauRatio_mean_le_euler_product
    (q N : ℕ) (hq : q ≠ 0) (hN : 2 ≤ N) :
    HalberstamScratch.partialSum (normalizedTauRatio q) N ≤
      (Real.log 4 + 5) * (N : ℝ) / Real.log (N : ℝ) *
        ∏ p ∈ (N + 1).primesBelow,
          ∑' j : ℕ, normalizedTauRatio q (p ^ j) /
            ((p ^ j : ℕ) : ℝ) := by
  suffices hraw :
      HalberstamScratch.partialSum (normalizedTauRatio q) N ≤
        ((Real.log 4 + 4) + 1) * (N : ℝ) / Real.log (N : ℝ) *
          ∏ p ∈ (N + 1).primesBelow,
            ∑' j : ℕ, normalizedTauRatio q (p ^ j) /
              ((p ^ j : ℕ) : ℝ) by
    convert hraw using 1 <;> ring
  apply HalberstamScratch.halberstam_richert_of_mass_convolution
    (normalizedTauRatio q) (normalizedTauRatio_zero_right q)
    (normalizedTauRatio_one hq)
    (fun {_ _} hcop => normalizedTauRatio_mul_of_coprime hq hcop)
    (normalizedTauRatio_nonneg q)
    (W := psiNat) (K := Real.log 4 + 4) (N := N)
  · intro p hp
    change Summable (fun j : ℕ =>
      ‖normalizedTauRatio q (p ^ j) / ((p ^ j : ℕ) : ℝ)‖)
    apply Summable.of_nonneg_of_le
      (fun j => norm_nonneg _)
      (fun j => ?_)
      (summable_geometric_of_norm_lt_one
        (show ‖((p : ℝ)⁻¹)‖ < 1 by
          rw [Real.norm_of_nonneg (inv_nonneg.mpr (by positivity))]
          exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)))
    have hpjpos : 0 < (((p ^ j : ℕ) : ℝ)) := by
      exact_mod_cast pow_pos hp.pos j
    rw [Real.norm_of_nonneg
      (div_nonneg (normalizedTauRatio_nonneg q _) hpjpos.le)]
    calc
      normalizedTauRatio q (p ^ j) / (((p ^ j : ℕ) : ℝ))
          ≤ 1 / (((p ^ j : ℕ) : ℝ)) :=
        div_le_div_of_nonneg_right (normalizedTauRatio_le_one q _) hpjpos.le
      _ = ((p : ℝ)⁻¹) ^ j := by
        norm_num [one_div, inv_pow]
  · positivity
  · exact hN
  · exact normalizedTauRatio_log_moment_convolution q N hq
  · exact psiNat_le_linear

/-- Euler correction attached to a prime dividing the shift. -/
noncomputable def sharpLocalCorrection (p : ℕ) : ℝ :=
  (2 * (p : ℝ)) / (2 * (p : ℝ) - 1)

/-- The genuine divisor-reciprocal type weight: at `p^nu` it is
`(nu+1)⁻¹ (1 + O(1/p))`. -/
noncomputable def sharpShiftedReciprocalWeight (q : ℕ) : ℝ :=
  if q = 0 then 0 else
    (1 / (q.divisors.card : ℝ)) *
      ∏ p ∈ q.primeFactors, sharpLocalCorrection p

lemma sharpLocalCorrection_nonneg {p : ℕ} (hp : p.Prime) :
    0 ≤ sharpLocalCorrection p := by
  unfold sharpLocalCorrection
  have hp2R : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hden : (0 : ℝ) < 2 * p - 1 := by nlinarith
  positivity

lemma one_le_sharpLocalCorrection {p : ℕ} (hp : p.Prime) :
    1 ≤ sharpLocalCorrection p := by
  unfold sharpLocalCorrection
  have hp2R : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hden : (0 : ℝ) < 2 * p - 1 := by nlinarith
  rw [le_div_iff₀ hden]
  linarith

lemma sharpShiftedReciprocalWeight_nonneg (q : ℕ) :
    0 ≤ sharpShiftedReciprocalWeight q := by
  simp only [sharpShiftedReciprocalWeight]
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (by positivity) (Finset.prod_nonneg fun p hp =>
      sharpLocalCorrection_nonneg (Nat.prime_of_mem_primeFactors hp))

lemma sharpShiftedReciprocalWeight_mul_of_coprime {q r : ℕ}
    (hqr : q.Coprime r) :
    sharpShiftedReciprocalWeight (q * r) =
      sharpShiftedReciprocalWeight q * sharpShiftedReciprocalWeight r := by
  by_cases hq : q = 0
  · subst q
    have hr : r = 1 := by simpa using hqr
    subst r
    simp [sharpShiftedReciprocalWeight]
  by_cases hr : r = 0
  · subst r
    have hq1 : q = 1 := by simpa [Nat.coprime_comm] using hqr
    subst q
    simp [sharpShiftedReciprocalWeight]
  simp only [sharpShiftedReciprocalWeight, if_neg hq, if_neg hr,
    if_neg (Nat.mul_ne_zero hq hr)]
  rw [hqr.card_divisors_mul, Nat.cast_mul, Nat.primeFactors_mul hq hr,
    Finset.prod_union hqr.disjoint_primeFactors]
  have hqcard : (q.divisors.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr ⟨1, Nat.one_mem_divisors.mpr hq⟩
  have hrcard : (r.divisors.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr ⟨1, Nat.one_mem_divisors.mpr hr⟩
  field_simp [hqcard, hrcard]

lemma sharpShiftedReciprocalWeight_prime_pow_succ {p nu : ℕ} (hp : p.Prime) :
    sharpShiftedReciprocalWeight (p ^ (nu + 1)) =
      sharpLocalCorrection p / (nu + 2 : ℝ) := by
  have hpPow : p ^ (nu + 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hpf : (p ^ (nu + 1)).primeFactors = {p} := by
    rw [Nat.primeFactors_pow p (by omega), hp.primeFactors]
  have htau : (p ^ (nu + 1)).divisors.card = nu + 2 := by
    rw [← ArithmeticFunction.sigma_zero_apply]
    simpa [Nat.add_assoc] using divisor_function_exact_prime_power (nu + 1) hp
  simp [sharpShiftedReciprocalWeight, hpf, htau, hp.ne_zero]
  ring

lemma normalizedTauRatio_prime_pow_succ_of_not_dvd
    {q p j : ℕ} (hq : q ≠ 0) (hp : p.Prime) (hpd : ¬p ∣ q) :
    normalizedTauRatio q (p ^ (j + 1)) = 1 / (j + 2 : ℝ) := by
  have hcop : q.Coprime (p ^ (j + 1)) :=
    (hp.coprime_iff_not_dvd.mpr hpd).symm.pow_right _
  have hpPow : p ^ (j + 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hqcard : (q.divisors.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr ⟨1, Nat.one_mem_divisors.mpr hq⟩
  simp only [normalizedTauRatio, if_neg (not_or_intro hq hpPow)]
  rw [hcop.card_divisors_mul, Nat.cast_mul]
  have htau : (p ^ (j + 1)).divisors.card = j + 2 := by
    rw [← ArithmeticFunction.sigma_zero_apply]
    simpa [Nat.add_assoc] using divisor_function_exact_prime_power (j + 1) hp
  rw [htau]
  field_simp [hqcard]
  push_cast
  norm_num

lemma normalizedTauRatio_localFactor_le {q p : ℕ} (hq : q ≠ 0)
    (hp : p.Prime) :
    (∑' j : ℕ, normalizedTauRatio q (p ^ j) /
        ((p ^ j : ℕ) : ℝ)) ≤
      localMajorant p *
        (if p ∈ q.primeFactors then sharpLocalCorrection p else 1) := by
  by_cases hpq : p ∈ q.primeFactors
  · have h := HalberstamScratch.prime_power_local_mass
      (normalizedTauRatio q) p 1 1 hp
      (normalizedTauRatio_nonneg q) (normalizedTauRatio_one hq)
      (by norm_num) (by norm_num) (by norm_num)
      (fun j => by simpa using normalizedTauRatio_le_one q (p ^ (j + 1)))
    have hbound := h.2
    change (∑' j : ℕ,
        ‖normalizedTauRatio q (p ^ j) / ((p ^ j : ℕ) : ℝ)‖) ≤
          1 + 1 / ((p : ℝ) - 1) at hbound
    calc
      (∑' j : ℕ, normalizedTauRatio q (p ^ j) /
          ((p ^ j : ℕ) : ℝ)) =
        ∑' j : ℕ,
          ‖normalizedTauRatio q (p ^ j) / ((p ^ j : ℕ) : ℝ)‖ := by
            apply tsum_congr
            intro j
            rw [Real.norm_eq_abs, abs_of_nonneg]
            exact div_nonneg (normalizedTauRatio_nonneg q _) (by positivity)
      _ ≤ 1 + 1 / ((p : ℝ) - 1) := hbound
      _ = localMajorant p * sharpLocalCorrection p := by
        have hp1R : (p : ℝ) - 1 ≠ 0 := by
          exact ne_of_gt (sub_pos.mpr (by exact_mod_cast hp.one_lt))
        have hp1R' : -1 + (p : ℝ) ≠ 0 := by
          have hp2R : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
          nlinarith
        have hcorr : 2 * (p : ℝ) - 1 ≠ 0 := by
          have hp2R : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
          nlinarith
        have hcorr' : -1 + (p : ℝ) * 2 ≠ 0 := by
          have hp2R : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
          nlinarith
        have hmajor :
            localMajorant p =
              (2 * (p : ℝ) - 1) / (2 * ((p : ℝ) - 1)) := by
          unfold localMajorant
          field_simp [hp1R]
          ring
        rw [hmajor]
        unfold sharpLocalCorrection
        ring_nf
        field_simp [hp1R, hp1R', hcorr, hcorr']
        ring
      _ = localMajorant p *
          (if p ∈ q.primeFactors then sharpLocalCorrection p else 1) := by
        rw [if_pos hpq]
  · have hpd : ¬p ∣ q := by
      intro hpd
      exact hpq (Nat.mem_primeFactors.mpr ⟨hp, hpd, hq⟩)
    have h := HalberstamScratch.prime_power_local_mass
      (normalizedTauRatio q) p ((1 : ℝ) / 2) 1 hp
      (normalizedTauRatio_nonneg q) (normalizedTauRatio_one hq)
      (by norm_num) (by norm_num) (by norm_num)
      (fun j => by
        rw [normalizedTauRatio_prime_pow_succ_of_not_dvd hq hp hpd]
        have hjNat : 2 ≤ j + 2 := by omega
        have hj : (2 : ℝ) ≤ (j : ℝ) + 2 := by exact_mod_cast hjNat
        simpa [one_div] using
          (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hj))
    have hbound := h.2
    change (∑' j : ℕ,
        ‖normalizedTauRatio q (p ^ j) / ((p ^ j : ℕ) : ℝ)‖) ≤
          localMajorant p at hbound
    calc
      (∑' j : ℕ, normalizedTauRatio q (p ^ j) /
          ((p ^ j : ℕ) : ℝ)) =
        ∑' j : ℕ,
          ‖normalizedTauRatio q (p ^ j) / ((p ^ j : ℕ) : ℝ)‖ := by
            apply tsum_congr
            intro j
            rw [Real.norm_eq_abs, abs_of_nonneg]
            exact div_nonneg (normalizedTauRatio_nonneg q _) (by positivity)
      _ ≤ localMajorant p := hbound
      _ = localMajorant p *
          (if p ∈ q.primeFactors then sharpLocalCorrection p else 1) := by
        rw [if_neg hpq, mul_one]

lemma normalizedTauRatio_eulerProduct_le
    (q N : ℕ) (hq : q ≠ 0) :
    (∏ p ∈ (N + 1).primesBelow,
        ∑' j : ℕ, normalizedTauRatio q (p ^ j) /
          ((p ^ j : ℕ) : ℝ)) ≤
      (∏ p ∈ (N + 1).primesBelow, localMajorant p) *
        ∏ p ∈ q.primeFactors, sharpLocalCorrection p := by
  let S := (N + 1).primesBelow
  have hprod :
      (∏ p ∈ S,
          ∑' j : ℕ, normalizedTauRatio q (p ^ j) /
            ((p ^ j : ℕ) : ℝ)) ≤
        ∏ p ∈ S, (localMajorant p *
          (if p ∈ q.primeFactors then sharpLocalCorrection p else 1)) := by
    apply Finset.prod_le_prod
    · intro p hpS
      exact tsum_nonneg fun j =>
        div_nonneg (normalizedTauRatio_nonneg q _) (by positivity)
    · intro p hpS
      exact normalizedTauRatio_localFactor_le hq
        (Nat.prime_of_mem_primesBelow hpS)
  calc
    (∏ p ∈ S,
        ∑' j : ℕ, normalizedTauRatio q (p ^ j) /
          ((p ^ j : ℕ) : ℝ)) ≤
      ∏ p ∈ S, (localMajorant p *
        (if p ∈ q.primeFactors then sharpLocalCorrection p else 1)) := hprod
    _ = (∏ p ∈ S, localMajorant p) *
        ∏ p ∈ S, (if p ∈ q.primeFactors then sharpLocalCorrection p else 1) := by
      rw [Finset.prod_mul_distrib]
    _ = (∏ p ∈ S, localMajorant p) *
        ∏ p ∈ S ∩ q.primeFactors, sharpLocalCorrection p := by
      rw [Finset.prod_ite_mem]
    _ ≤ (∏ p ∈ S, localMajorant p) *
        ∏ p ∈ q.primeFactors, sharpLocalCorrection p := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.prod_le_prod_of_subset_of_one_le
        · exact Finset.inter_subset_right
        · intro p hp
          exact sharpLocalCorrection_nonneg
            (Nat.prime_of_mem_primeFactors (Finset.inter_subset_right hp))
        · intro p hpq hpnot
          exact one_le_sharpLocalCorrection (Nat.prime_of_mem_primeFactors hpq)
      · apply Finset.prod_nonneg
        intro p hpS
        unfold localMajorant
        have hpOneR : (1 : ℝ) < (p : ℝ) := by
          exact_mod_cast (Nat.prime_of_mem_primesBelow hpS).one_lt
        positivity

/-- The absolute constant in the clean shifted reciprocal-divisor mean. -/
noncomputable def shiftedReciprocalMeanConstant : ℝ :=
  (Real.log 4 + 5) * localMajorantUniformConstant * Real.sqrt 2

lemma shiftedReciprocalMeanConstant_pos : 0 < shiftedReciprocalMeanConstant := by
  unfold shiftedReciprocalMeanConstant
  have hlog : 0 < Real.log 4 + 5 := by
    have : 0 < Real.log 4 := Real.log_pos (by norm_num)
    linarith
  exact mul_pos (mul_pos hlog localMajorantUniformConstant_pos)
    (Real.sqrt_pos.2 (by norm_num))

/-- Final shifted reciprocal mean with the genuine `tau⁻¹`-type weight. -/
theorem shifted_reciprocal_divisor_mean_sharp (q z : ℕ) (hz : 3 ≤ z) :
    (∑ m ∈ Finset.range z,
      1 / ((q * m).divisors.card : ℝ)) ≤
      shiftedReciprocalMeanConstant * (z : ℝ) *
        sharpShiftedReciprocalWeight q /
          Real.sqrt (Real.log (2 * (z : ℝ))) := by
  by_cases hq : q = 0
  · subst q
    simp [sharpShiftedReciprocalWeight]
  have hqcardPos : 0 < (q.divisors.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hq⟩
  have hsumEq :
      (∑ m ∈ Finset.range z, 1 / ((q * m).divisors.card : ℝ)) =
        (1 / (q.divisors.card : ℝ)) *
          ∑ m ∈ Finset.range z, normalizedTauRatio q m := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hmRange
    by_cases hm : m = 0
    · subst m
      simp [normalizedTauRatio]
    have hqm : q * m ≠ 0 := Nat.mul_ne_zero hq hm
    simp [normalizedTauRatio, hq, hm]
    field_simp
  have hRange :
      (∑ m ∈ Finset.range z, normalizedTauRatio q m) ≤
        HalberstamScratch.partialSum (normalizedTauRatio q) z := by
    unfold HalberstamScratch.partialSum
    have hrange : Finset.range z = {0} ∪ Finset.Ico 1 z := by
      ext m
      simp
      omega
    rw [hrange, Finset.sum_union]
    · simp only [Finset.sum_singleton, normalizedTauRatio_zero_right, zero_add]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro m hm
        exact Finset.mem_Icc.mpr
          ⟨(Finset.mem_Ico.mp hm).1, (Finset.mem_Ico.mp hm).2.le⟩
      · intro m hm hnot
        exact normalizedTauRatio_nonneg q m
    · simp
  have hmean := normalizedTauRatio_mean_le_euler_product q z hq (by omega)
  have heuler := normalizedTauRatio_eulerProduct_le q z hq
  have hlogzPos : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hcoeffNonneg :
      0 ≤ (Real.log 4 + 5) * (z : ℝ) / Real.log (z : ℝ) := by positivity
  have hnormalized :
      HalberstamScratch.partialSum (normalizedTauRatio q) z ≤
        (Real.log 4 + 5) * localMajorantUniformConstant * (z : ℝ) /
          Real.sqrt (Real.log (z : ℝ)) *
            ∏ p ∈ q.primeFactors, sharpLocalCorrection p := by
    calc
      HalberstamScratch.partialSum (normalizedTauRatio q) z ≤
          (Real.log 4 + 5) * (z : ℝ) / Real.log (z : ℝ) *
            ∏ p ∈ (z + 1).primesBelow,
              ∑' j : ℕ, normalizedTauRatio q (p ^ j) /
                ((p ^ j : ℕ) : ℝ) := hmean
      _ ≤ (Real.log 4 + 5) * (z : ℝ) / Real.log (z : ℝ) *
          ((∏ p ∈ (z + 1).primesBelow, localMajorant p) *
            ∏ p ∈ q.primeFactors, sharpLocalCorrection p) :=
        mul_le_mul_of_nonneg_left heuler hcoeffNonneg
      _ ≤ (Real.log 4 + 5) * (z : ℝ) / Real.log (z : ℝ) *
          ((localMajorantUniformConstant * Real.sqrt (Real.log (z : ℝ))) *
            ∏ p ∈ q.primeFactors, sharpLocalCorrection p) := by
        apply mul_le_mul_of_nonneg_left
        · apply mul_le_mul_of_nonneg_right (prod_localMajorant_le_sqrt z hz)
          exact Finset.prod_nonneg fun p hpq =>
            sharpLocalCorrection_nonneg (Nat.prime_of_mem_primeFactors hpq)
        · exact hcoeffNonneg
      _ = (Real.log 4 + 5) * localMajorantUniformConstant * (z : ℝ) /
          Real.sqrt (Real.log (z : ℝ)) *
            ∏ p ∈ q.primeFactors, sharpLocalCorrection p := by
        have hsqrtPos : 0 < Real.sqrt (Real.log (z : ℝ)) :=
          Real.sqrt_pos.2 hlogzPos
        have hsqrtSq : Real.sqrt (Real.log (z : ℝ)) ^ 2 =
            Real.log (z : ℝ) := Real.sq_sqrt hlogzPos.le
        field_simp [hlogzPos.ne', hsqrtPos.ne']
        rw [hsqrtSq]
        ring
  have hlogTwozPos : 0 < Real.log (2 * (z : ℝ)) := by
    apply Real.log_pos
    have hzR : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
    nlinarith
  have hlogCompare : Real.log (2 * (z : ℝ)) ≤ 2 * Real.log (z : ℝ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (z : ℝ) ≠ 0)]
    have hlog2_le_logz : Real.log 2 ≤ Real.log (z : ℝ) := by
      gcongr
      exact_mod_cast (show 2 ≤ z by omega)
    linarith
  have hsqrtCompare :
      Real.sqrt (Real.log (2 * (z : ℝ))) ≤
        Real.sqrt 2 * Real.sqrt (Real.log (z : ℝ)) := by
    calc
      Real.sqrt (Real.log (2 * (z : ℝ))) ≤
          Real.sqrt (2 * Real.log (z : ℝ)) := Real.sqrt_le_sqrt hlogCompare
      _ = Real.sqrt 2 * Real.sqrt (Real.log (z : ℝ)) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hscaled :
      (Real.log 4 + 5) * localMajorantUniformConstant * (z : ℝ) /
          Real.sqrt (Real.log (z : ℝ)) ≤
        shiftedReciprocalMeanConstant * (z : ℝ) /
          Real.sqrt (Real.log (2 * (z : ℝ))) := by
    have hsqrtzPos : 0 < Real.sqrt (Real.log (z : ℝ)) := Real.sqrt_pos.2 hlogzPos
    have hsqrtTwozPos : 0 < Real.sqrt (Real.log (2 * (z : ℝ))) :=
      Real.sqrt_pos.2 hlogTwozPos
    unfold shiftedReciprocalMeanConstant
    rw [div_le_div_iff₀ hsqrtzPos hsqrtTwozPos]
    have hbase : 0 ≤
        (Real.log 4 + 5) * localMajorantUniformConstant * (z : ℝ) := by
      have hlog : 0 ≤ Real.log 4 + 5 := by
        have : 0 < Real.log 4 := Real.log_pos (by norm_num)
        linarith
      exact mul_nonneg (mul_nonneg hlog localMajorantUniformConstant_pos.le)
        (Nat.cast_nonneg z)
    nlinarith
  rw [hsumEq]
  calc
    (1 / (q.divisors.card : ℝ)) *
        ∑ m ∈ Finset.range z, normalizedTauRatio q m ≤
      (1 / (q.divisors.card : ℝ)) *
        HalberstamScratch.partialSum (normalizedTauRatio q) z := by
          gcongr
    _ ≤ (1 / (q.divisors.card : ℝ)) *
        ((Real.log 4 + 5) * localMajorantUniformConstant * (z : ℝ) /
          Real.sqrt (Real.log (z : ℝ)) *
            ∏ p ∈ q.primeFactors, sharpLocalCorrection p) := by
          gcongr
    _ ≤ (1 / (q.divisors.card : ℝ)) *
        (shiftedReciprocalMeanConstant * (z : ℝ) /
          Real.sqrt (Real.log (2 * (z : ℝ))) *
            ∏ p ∈ q.primeFactors, sharpLocalCorrection p) := by
          apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul_of_nonneg_right hscaled
              (Finset.prod_nonneg fun p hpq =>
                sharpLocalCorrection_nonneg (Nat.prime_of_mem_primeFactors hpq))
          · positivity
    _ = shiftedReciprocalMeanConstant * (z : ℝ) *
        sharpShiftedReciprocalWeight q /
          Real.sqrt (Real.log (2 * (z : ℝ))) := by
      simp only [sharpShiftedReciprocalWeight, if_neg hq]
      ring

/-- Ceiling division is the exact cutoff for a strict product inequality. -/
lemma mem_range_ceilDiv_iff_mul_lt {A x m : ℕ} (hA : 0 < A) :
    m ∈ Finset.range (x ⌈/⌉ A) ↔ A * m < x := by
  rw [Finset.mem_range]
  constructor
  · intro hm
    by_contra hnot
    have hx : x ≤ A * m := by omega
    have hceil : x ⌈/⌉ A ≤ m := (ceilDiv_le_iff_le_mul hA).mpr hx
    omega
  · intro hmul
    by_contra hnot
    have hceil : x ⌈/⌉ A ≤ m := by omega
    have hx : x ≤ A * m := (ceilDiv_le_iff_le_mul hA).mp hceil
    omega

/-- Restricting an ambient range by `A*m < x` produces exactly the ceiling
division range. -/
lemma filter_range_mul_lt_eq_range_ceilDiv {A x : ℕ} (hA : 0 < A) :
    (Finset.range x).filter (fun m => A * m < x) =
      Finset.range (x ⌈/⌉ A) := by
  ext m
  rw [Finset.mem_filter, mem_range_ceilDiv_iff_mul_lt hA]
  constructor
  · exact fun h => h.2
  · intro hmul
    refine ⟨Finset.mem_range.mpr ?_, hmul⟩
    have hmle : m ≤ A * m := by
      calc
        m = 1 * m := by simp
        _ ≤ A * m := Nat.mul_le_mul_right m hA
    exact hmle.trans_lt hmul

/-- Consumer-shaped first ET application for a strict multiplicative
cutoff. -/
theorem shifted_reciprocal_divisor_mean_sharp_mul_cutoff
    (q A x : ℕ) (hA : 0 < A) (hcut : 3 ≤ x ⌈/⌉ A) :
    (∑ m ∈ (Finset.range x).filter (fun m => A * m < x),
      1 / ((q * m).divisors.card : ℝ)) ≤
      shiftedReciprocalMeanConstant * ((x ⌈/⌉ A : ℕ) : ℝ) *
        sharpShiftedReciprocalWeight q /
          Real.sqrt (Real.log (2 * ((x ⌈/⌉ A : ℕ) : ℝ))) := by
  rw [filter_range_mul_lt_eq_range_ceilDiv hA]
  exact shifted_reciprocal_divisor_mean_sharp q (x ⌈/⌉ A) hcut

#print axioms shifted_reciprocal_divisor_mean_sharp

end Prop3ShiftedMean448
