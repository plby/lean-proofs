/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos297.GoodFactorization
import ErdosProblems.Erdos297.Parameters
import ErdosProblems.Erdos285.ProperPrimePowerTail
import UnitFractions.FinalResults

/-!
# Erdős 297: density of denominators with controlled factorization

This is the arithmetic-density part of Liu--Sawhney's Lemma 2.2.  The
integer thresholds used by the finite good set are

* `floor (5 * log (log N))` for the largest prime exponent, and
* `floor (10 * log (log N))` for the number of prime factors with
  multiplicity.

We prove that both exceptional sets have cardinality `o(N)`.  The proof
splits `Omega(n)` into `omega(n)` and the number of proper prime-power
divisors of `n`.  Turan's second-moment estimate controls the first part;
double counting and convergence of the reciprocal sum of proper prime
powers control the second.
-/

namespace Erdos297.FactorDensity

open Filter Finset Real Asymptotics
open scoped ArithmeticFunction.omega ArithmeticFunction.Omega BigOperators Topology

noncomputable section

attribute [local instance] Classical.propDecidable

open Erdos297.GoodFactorization
open Erdos285.PositiveReservoir

/-- Prime-power divisors of exponent at least two. -/
def properPrimePowerDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter fun q ↦ IsPrimePow q ∧ ¬ q.Prime

/-- The number of prime divisors of a positive integer is `omega(n)`. -/
lemma card_prime_divisors {n : ℕ} (hn : n ≠ 0) :
    (n.divisors.filter Nat.Prime).card = ω n := by
  have hEq : n.divisors.filter Nat.Prime = n.primeFactors := by
    ext q
    rw [Finset.mem_filter, Nat.mem_divisors,
      Nat.mem_primeFactors_of_ne_zero hn]
    constructor
    · rintro ⟨⟨hqdvd, -⟩, hq⟩
      exact ⟨hq, hqdvd⟩
    · rintro ⟨hq, hqdvd⟩
      exact ⟨⟨hqdvd, hn⟩, hq⟩
  rw [hEq, ArithmeticFunction.cardDistinctFactors_apply,
    Nat.primeFactors, List.card_toFinset]

/-- `Omega(n)` is `omega(n)` plus one for every proper prime-power divisor. -/
lemma Omega_eq_omega_add_card_properPrimePowerDivisors {n : ℕ} (hn : n ≠ 0) :
    Ω n = ω n + (properPrimePowerDivisors n).card := by
  rw [UnitFractions.Omega_eq_card_prime_pow_divisors hn,
    ← card_prime_divisors hn]
  let all := n.divisors.filter IsPrimePow
  let primes := n.divisors.filter Nat.Prime
  let proper := properPrimePowerDivisors n
  have hall : all = primes ∪ proper := by
    ext q
    simp only [all, primes, properPrimePowerDivisors, proper,
      Finset.mem_filter, Finset.mem_union]
    constructor
    · intro hq
      by_cases hp : q.Prime
      · exact Or.inl ⟨hq.1, hp⟩
      · exact Or.inr ⟨hq.1, hq.2, hp⟩
    · rintro (hq | hq)
      · exact ⟨hq.1, hq.2.isPrimePow⟩
      · exact ⟨hq.1, hq.2.1⟩
  have hdisj : Disjoint primes proper := by
    rw [Finset.disjoint_left]
    intro q hqp hqproper
    exact (Finset.mem_filter.mp hqproper).2.2
      (Finset.mem_filter.mp hqp).2
  change all.card = primes.card + proper.card
  rw [hall, Finset.card_union_of_disjoint hdisj]

lemma omega_le_Omega {n : ℕ} (hn : n ≠ 0) :
    ω n ≤ Ω n := by
  rw [Omega_eq_omega_add_card_properPrimePowerDivisors hn]
  exact Nat.le_add_right _ _

/-! ## Finite divisor incidence estimates

These elementary estimates isolate the averaging step used in the source's
minor-arc supply argument.  If every member of `E` has at most `F` prime
factors, then the total number of incidences `p ∣ n`, for `p` in a finite
prime set `P` and `n` in `E`, is at most `#E * F`.
-/

/-- The primes in `P` which divide at least one member of `E`. -/
def divisorPrimes (P E : Finset ℕ) : Finset ℕ :=
  P.filter fun p ↦ ∃ n ∈ E, p ∣ n

lemma card_primes_dividing_le_Omega {P : Finset ℕ} {n F : ℕ}
    (hn : n ≠ 0) (hP : ∀ p ∈ P, p.Prime) (hnF : Ω n ≤ F) :
    (P.filter fun p ↦ p ∣ n).card ≤ F := by
  have hsub : (P.filter fun p ↦ p ∣ n) ⊆ n.primeFactors := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact (Nat.mem_primeFactors_of_ne_zero hn).mpr ⟨hP p hp'.1, hp'.2⟩
  calc
    (P.filter fun p ↦ p ∣ n).card ≤ n.primeFactors.card :=
      Finset.card_le_card hsub
    _ = ω n := by
      rw [ArithmeticFunction.cardDistinctFactors_apply,
        Nat.primeFactors, List.card_toFinset]
    _ ≤ Ω n := omega_le_Omega hn
    _ ≤ F := hnF

/-- Double-counting prime-divisor incidences. -/
lemma sum_card_divisiblePart_primes_le {P E : Finset ℕ} {F : ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hE0 : ∀ n ∈ E, n ≠ 0)
    (hEF : ∀ n ∈ E, Ω n ≤ F) :
    ∑ p ∈ P, (divisiblePart E p).card ≤ E.card * F := by
  calc
    ∑ p ∈ P, (divisiblePart E p).card =
        ∑ p ∈ P, ∑ n ∈ E, if p ∣ n then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      simp [divisiblePart]
    _ = ∑ n ∈ E, ∑ p ∈ P, if p ∣ n then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ n ∈ E, (P.filter fun p ↦ p ∣ n).card := by
      apply Finset.sum_congr rfl
      intro n hn
      simp
    _ ≤ ∑ n ∈ E, F := by
      apply Finset.sum_le_sum
      intro n hn
      exact card_primes_dividing_le_Omega (hE0 n hn) hP (hEF n hn)
    _ = E.card * F := by simp

/-- A finite averaging corollary: if the total incidence budget is smaller
than `#P * (B+1)`, one prime has at most `B` divisible members. -/
lemma exists_card_divisiblePart_le_of_mul_lt {P E : Finset ℕ} {F B : ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hE0 : ∀ n ∈ E, n ≠ 0)
    (hEF : ∀ n ∈ E, Ω n ≤ F)
    (hbudget : E.card * F < P.card * (B + 1)) :
    ∃ p ∈ P, (divisiblePart E p).card ≤ B := by
  by_contra h
  push_neg at h
  have hlower : P.card * (B + 1) ≤
      ∑ p ∈ P, (divisiblePart E p).card := by
    calc
      P.card * (B + 1) = ∑ p ∈ P, (B + 1) := by simp
      _ ≤ ∑ p ∈ P, (divisiblePart E p).card :=
        Finset.sum_le_sum fun p hp ↦ h p hp
  exact (not_le_of_gt hbudget)
    (hlower.trans (sum_card_divisiblePart_primes_le hP hE0 hEF))

/-- At most `#E * F` primes from `P` divide some member of `E`. -/
lemma card_divisorPrimes_le {P E : Finset ℕ} {F : ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hE0 : ∀ n ∈ E, n ≠ 0)
    (hEF : ∀ n ∈ E, Ω n ≤ F) :
    (divisorPrimes P E).card ≤ E.card * F := by
  have hsub : divisorPrimes P E ⊆
      E.biUnion fun n ↦ P.filter fun p ↦ p ∣ n := by
    intro p hp
    rw [divisorPrimes, Finset.mem_filter] at hp
    obtain ⟨n, hnE, hpn⟩ := hp.2
    exact Finset.mem_biUnion.mpr
      ⟨n, hnE, Finset.mem_filter.mpr ⟨hp.1, hpn⟩⟩
  calc
    (divisorPrimes P E).card ≤
        (E.biUnion fun n ↦ P.filter fun p ↦ p ∣ n).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ n ∈ E, (P.filter fun p ↦ p ∣ n).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ n ∈ E, F := by
      apply Finset.sum_le_sum
      intro n hn
      exact card_primes_dividing_le_Omega (hE0 n hn) hP (hEF n hn)
    _ = E.card * F := by simp

/-- Proper prime powers up to `N`; `2` may be omitted because it is prime. -/
def properPrimePowersUpTo (N : ℕ) : Finset ℕ :=
  (Ioc 2 N).filter fun q ↦ IsPrimePow q ∧ ¬ q.Prime

lemma properPrimePowerDivisors_eq_filter_upTo {N n : ℕ}
    (hn : n ∈ Icc 1 N) :
    properPrimePowerDivisors n =
      (properPrimePowersUpTo N).filter fun q ↦ q ∣ n := by
  ext q
  rw [properPrimePowerDivisors, properPrimePowersUpTo,
    Finset.mem_filter, Nat.mem_divisors, Finset.mem_filter,
    Finset.mem_filter]
  constructor
  · rintro ⟨⟨hqdvd, hn0⟩, hqpp, hqnotprime⟩
    have hqle : q ≤ N :=
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hqdvd).trans
        (Finset.mem_Icc.mp hn).2
    have hqgt : 2 < q := by
      have hqone : 1 < q := hqpp.one_lt
      by_contra h
      have hqeq : q = 2 := by omega
      exact hqnotprime (hqeq ▸ Nat.prime_two)
    exact ⟨⟨Finset.mem_Ioc.mpr ⟨hqgt, hqle⟩,
      hqpp, hqnotprime⟩, hqdvd⟩
  · rintro ⟨⟨hqIoc, hqpp, hqnotprime⟩, hqdvd⟩
    exact ⟨⟨hqdvd, Nat.ne_of_gt (Finset.mem_Icc.mp hn).1⟩,
      hqpp, hqnotprime⟩

lemma properPrimePowersUpTo_reciprocal_sum (N : ℕ) :
    ∑ q ∈ properPrimePowersUpTo N, (q : ℝ)⁻¹ =
      properPrimePowerReciprocalInterval 2 N := by
  rfl

/-- Double counting multiples of proper prime powers. -/
lemma sum_card_properPrimePowerDivisors_le (N : ℕ) :
    ∑ n ∈ Icc 1 N, ((properPrimePowerDivisors n).card : ℝ) ≤
      (N : ℝ) * properPrimePowerReciprocalInterval 2 N := by
  calc
    ∑ n ∈ Icc 1 N, ((properPrimePowerDivisors n).card : ℝ) =
        ∑ n ∈ Icc 1 N,
          ∑ q ∈ properPrimePowersUpTo N,
            if q ∣ n then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [properPrimePowerDivisors_eq_filter_upTo hn,
        Finset.card_eq_sum_ones, Nat.cast_sum]
      simp only [Nat.cast_one, Finset.sum_filter]
    _ = ∑ q ∈ properPrimePowersUpTo N,
          (((Icc 1 N).filter fun n ↦ q ∣ n).card : ℝ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.sum_boole]
    _ ≤ ∑ q ∈ properPrimePowersUpTo N, (N : ℝ) / q := by
      apply Finset.sum_le_sum
      intro q hq
      have hqone : 1 ≤ q := by
        have hqgt : 2 < q :=
          (Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1).1
        omega
      exact UnitFractions.count_multiples''' hqone
    _ = (N : ℝ) * properPrimePowerReciprocalInterval 2 N := by
      rw [← properPrimePowersUpTo_reciprocal_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      rw [div_eq_mul_inv]

/-- A uniform first-moment bound for the excess `Omega(n)-omega(n)`. -/
lemma sum_factor_excess_le (N : ℕ) :
    ∑ n ∈ Icc 1 N, ((Ω n - ω n : ℕ) : ℝ) ≤ 40 * (N : ℝ) := by
  have hsum :
      ∑ n ∈ Icc 1 N, ((Ω n - ω n : ℕ) : ℝ) =
        ∑ n ∈ Icc 1 N, ((properPrimePowerDivisors n).card : ℝ) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := by
      exact Nat.ne_of_gt ((Finset.mem_Icc.mp hn).1.trans_lt' Nat.zero_lt_one)
    rw [Omega_eq_omega_add_card_properPrimePowerDivisors hn0,
      Nat.add_sub_cancel_left]
  by_cases hN : 2 ≤ N
  · rw [hsum]
    calc
      ∑ n ∈ Icc 1 N, ((properPrimePowerDivisors n).card : ℝ) ≤
          (N : ℝ) * properPrimePowerReciprocalInterval 2 N :=
        sum_card_properPrimePowerDivisors_le N
      _ ≤ (N : ℝ) * (40 * (2 : ℝ) ^ (-1 / 4 : ℝ)) := by
        gcongr
        exact properPrimePowerReciprocalInterval_le 2 N (by omega) hN
      _ ≤ 40 * (N : ℝ) := by
        have hpow : (2 : ℝ) ^ (-1 / 4 : ℝ) ≤ 1 := by
          exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
        calc
          (N : ℝ) * (40 * (2 : ℝ) ^ (-1 / 4 : ℝ)) ≤
              (N : ℝ) * (40 * 1) := by gcongr
          _ = 40 * (N : ℝ) := by ring
  · interval_cases N <;>
      norm_num [ArithmeticFunction.cardFactors_one,
        ArithmeticFunction.cardDistinctFactors_one]

/-- Integers below `N` with more than twice the normal order of distinct
prime factors. -/
def omegaExceptional (N : ℕ) : Finset ℕ :=
  (Ico 1 N).filter fun n ↦
    2 * Real.log (Real.log (N : ℝ)) < (ω n : ℝ)

/-- Integers below `N` whose repeated-prime contribution is larger than
`3 log log N`. -/
def factorExcessExceptional (N : ℕ) : Finset ℕ :=
  (Ico 1 N).filter fun n ↦
    3 * Real.log (Real.log (N : ℝ)) < (Ω n - ω n : ℕ)

lemma omegaExceptional_isLittleO :
    (fun N : ℕ ↦ ((omegaExceptional N).card : ℝ)) =o[atTop]
      (fun N : ℕ ↦ (N : ℝ)) := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hreg := UnitFractions.filter_regular (1 / ε) (one_div_pos.mpr hε)
  filter_upwards [hreg, eventually_gt_atTop (0 : ℕ)] with N hNreg hN
  rw [norm_of_nonneg (Nat.cast_nonneg _), norm_of_nonneg (Nat.cast_nonneg _)]
  have hsub : omegaExceptional N ⊆
      (range N).filter fun n : ℕ ↦
        n ≠ 0 ∧
          ¬ (((99 : ℝ) / 100) * Real.log (Real.log (N : ℝ)) ≤ ω n ∧
            (ω n : ℝ) ≤ 2 * Real.log (Real.log (N : ℝ))) := by
    intro n hnmem
    rw [omegaExceptional, Finset.mem_filter, Finset.mem_Ico] at hnmem
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨hnmem.1.2, Nat.ne_of_gt hnmem.1.1, ?_⟩
    rintro ⟨-, hupper⟩
    exact (not_le_of_gt hnmem.2) hupper
  have hcard : ((omegaExceptional N).card : ℝ) ≤ (N : ℝ) / (1 / ε) := by
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (hNreg (range N) (Subset.rfl))
  calc
    ((omegaExceptional N).card : ℝ) ≤ (N : ℝ) / (1 / ε) := hcard
    _ = ε * (N : ℝ) := by field_simp [hε.ne']

lemma factorExcessExceptional_isLittleO :
    (fun N : ℕ ↦ ((factorExcessExceptional N).card : ℝ)) =o[atTop]
      (fun N : ℕ ↦ (N : ℝ)) := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hlogtop : Tendsto (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards
      [hlogtop.eventually_ge_atTop (40 / (3 * ε)),
        hlogtop.eventually (eventually_gt_atTop (0 : ℝ)),
        eventually_gt_atTop (0 : ℕ)] with N hloglarge hlogpos hN
  rw [norm_of_nonneg (Nat.cast_nonneg _), norm_of_nonneg (Nat.cast_nonneg _)]
  let L := Real.log (Real.log (N : ℝ))
  have hpoint : ∀ n ∈ factorExcessExceptional N,
      3 * L ≤ ((Ω n - ω n : ℕ) : ℝ) := by
    intro n hnmem
    exact (Finset.mem_filter.mp hnmem).2.le
  have hmarkov : ((factorExcessExceptional N).card : ℝ) * (3 * L) ≤
      ∑ n ∈ factorExcessExceptional N, ((Ω n - ω n : ℕ) : ℝ) := by
    calc
      ((factorExcessExceptional N).card : ℝ) * (3 * L) =
          ∑ _n ∈ factorExcessExceptional N, 3 * L := by
        simp [nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hpoint
  have hsubset : factorExcessExceptional N ⊆ Icc 1 N := by
    intro n hnmem
    have hnIco := (Finset.mem_filter.mp hnmem).1
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Ico.mp hnIco).1, (Finset.mem_Ico.mp hnIco).2.le⟩
  have hsumsub :
      ∑ n ∈ factorExcessExceptional N, ((Ω n - ω n : ℕ) : ℝ) ≤
        ∑ n ∈ Icc 1 N, ((Ω n - ω n : ℕ) : ℝ) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun n hn hnot ↦ Nat.cast_nonneg _)
  have htotal : ((factorExcessExceptional N).card : ℝ) * (3 * L) ≤
      40 * (N : ℝ) :=
    hmarkov.trans (hsumsub.trans (sum_factor_excess_le N))
  have h3L : 0 < 3 * L := mul_pos (by norm_num) (by simpa [L] using hlogpos)
  have hratio : ((factorExcessExceptional N).card : ℝ) ≤
      (40 * (N : ℝ)) / (3 * L) := (le_div_iff₀ h3L).2 htotal
  have hcoeff : 40 / (3 * L) ≤ ε := by
    have heps3 : 0 < 3 * ε := mul_pos (by norm_num) hε
    have hlarge : 40 / (3 * ε) ≤ L := by simpa [L] using hloglarge
    rw [div_le_iff₀ h3L]
    have := mul_le_mul_of_nonneg_left hlarge (show (0 : ℝ) ≤ 3 * ε by positivity)
    field_simp [hε.ne'] at this ⊢
    nlinarith
  calc
    ((factorExcessExceptional N).card : ℝ) ≤
        (40 * (N : ℝ)) / (3 * L) := hratio
    _ = (40 / (3 * L)) * (N : ℝ) := by ring
    _ ≤ ε * (N : ℝ) :=
      mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg N)

/-- Quantitative Turan bound for the distinct-factor exceptional set.  This
rate, rather than just qualitative little-oh, is useful when the denominator
interval begins at `M = N / sqrt(log log log N)`. -/
lemma exists_omegaExceptional_card_le_div_logLog :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ((omegaExceptional N).card : ℝ) ≤
        C * (N : ℝ) / Real.log (Real.log (N : ℝ)) := by
  obtain ⟨C₀, hTuran⟩ := UnitFractions.turan_primes_estimate
  let C := |C₀| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  have hlogtop : Tendsto (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hTuran, hlogtop.eventually (eventually_gt_atTop (0 : ℝ))] with
      N hTuranN hL
  let L := Real.log (Real.log (N : ℝ))
  have hpoint : ∀ n ∈ omegaExceptional N,
      L ^ 2 ≤ ((ω n : ℝ) - L) ^ 2 := by
    intro n hn
    have homega := (Finset.mem_filter.mp hn).2
    have hdiff : L < (ω n : ℝ) - L := by
      dsimp [L] at homega ⊢
      linarith
    nlinarith [sq_nonneg ((ω n : ℝ) - 2 * L)]
  have hmarkov : ((omegaExceptional N).card : ℝ) * L ^ 2 ≤
      ∑ n ∈ omegaExceptional N, ((ω n : ℝ) - L) ^ 2 := by
    calc
      ((omegaExceptional N).card : ℝ) * L ^ 2 =
          ∑ _n ∈ omegaExceptional N, L ^ 2 := by simp [nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hpoint
  have hsubset : omegaExceptional N ⊆ Icc 1 N := by
    intro n hn
    have hb := Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1
    exact Finset.mem_Icc.mpr ⟨hb.1, hb.2.le⟩
  have hsubsum :
      ∑ n ∈ omegaExceptional N, ((ω n : ℝ) - L) ^ 2 ≤
        ∑ n ∈ Icc 1 N, ((ω n : ℝ) - L) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun _ _ _ ↦ sq_nonneg _)
  have hC₀C : C₀ ≤ C := by dsimp [C]; linarith [le_abs_self C₀]
  have hNL : 0 ≤ (N : ℝ) * L :=
    mul_nonneg (Nat.cast_nonneg N) (by simpa [L] using hL.le)
  have htotal : ((omegaExceptional N).card : ℝ) * L ^ 2 ≤
      C * (N : ℝ) * L := by
    calc
      ((omegaExceptional N).card : ℝ) * L ^ 2 ≤
          ∑ n ∈ omegaExceptional N, ((ω n : ℝ) - L) ^ 2 := hmarkov
      _ ≤ ∑ n ∈ Icc 1 N, ((ω n : ℝ) - L) ^ 2 := hsubsum
      _ ≤ C₀ * (N : ℝ) * L := by simpa [L] using hTuranN
      _ ≤ C * (N : ℝ) * L := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hC₀C (Nat.cast_nonneg N)) hL.le
  have hL' : 0 < L := by simpa [L] using hL
  apply (le_div_iff₀ hL').2
  apply le_of_mul_le_mul_right _ hL'
  calc
    (((omegaExceptional N).card : ℝ) * L) * L =
        ((omegaExceptional N).card : ℝ) * L ^ 2 := by ring
    _ ≤ C * (N : ℝ) * L := htotal
    _ = (C * (N : ℝ)) * L := by ring

/-- The proper-prime-power part has the same `N / log log N` quantitative
exceptional-set bound, with an absolute constant. -/
lemma eventually_factorExcessExceptional_card_le_div_logLog :
    ∀ᶠ N : ℕ in atTop,
      ((factorExcessExceptional N).card : ℝ) ≤
        14 * (N : ℝ) / Real.log (Real.log (N : ℝ)) := by
  have hlogtop : Tendsto (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hlogtop.eventually (eventually_gt_atTop (0 : ℝ))] with N hL
  let L := Real.log (Real.log (N : ℝ))
  have hpoint : ∀ n ∈ factorExcessExceptional N,
      3 * L ≤ ((Ω n - ω n : ℕ) : ℝ) := by
    intro n hn
    exact (Finset.mem_filter.mp hn).2.le
  have hmarkov : ((factorExcessExceptional N).card : ℝ) * (3 * L) ≤
      ∑ n ∈ factorExcessExceptional N, ((Ω n - ω n : ℕ) : ℝ) := by
    calc
      ((factorExcessExceptional N).card : ℝ) * (3 * L) =
          ∑ _n ∈ factorExcessExceptional N, 3 * L := by simp [nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hpoint
  have hsubset : factorExcessExceptional N ⊆ Icc 1 N := by
    intro n hn
    have hb := Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1
    exact Finset.mem_Icc.mpr ⟨hb.1, hb.2.le⟩
  have htotal : ((factorExcessExceptional N).card : ℝ) * (3 * L) ≤
      40 * (N : ℝ) := by
    exact hmarkov.trans <|
      (Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun _ _ _ ↦ Nat.cast_nonneg _)).trans (sum_factor_excess_le N)
  have hL' : 0 < L := by simpa [L] using hL
  apply (le_div_iff₀ hL').2
  apply le_of_mul_le_mul_right _ (show (0 : ℝ) < 3 by norm_num)
  calc
    ((factorExcessExceptional N).card : ℝ) * L * 3 =
        ((factorExcessExceptional N).card : ℝ) * (3 * L) := by ring
    _ ≤ 40 * (N : ℝ) := htotal
    _ ≤ (14 * (N : ℝ)) * 3 := by
      calc
        40 * (N : ℝ) ≤ 42 * (N : ℝ) :=
          mul_le_mul_of_nonneg_right (by norm_num) (Nat.cast_nonneg N)
        _ = (14 * (N : ℝ)) * 3 := by ring

/-- The exact floor-five exceptional set used as a common majorant. -/
def fiveFactorExceptional (N : ℕ) : Finset ℕ :=
  (Icc 1 N).filter fun n ↦ exponentBound N < Ω n

lemma fiveFactorExceptional_card_le_sum {N : ℕ}
    (hL : 0 ≤ Real.log (Real.log (N : ℝ))) :
    (fiveFactorExceptional N).card ≤
      1 + (omegaExceptional N).card + (factorExcessExceptional N).card := by
  have hsub : fiveFactorExceptional N ⊆
      insert N (omegaExceptional N ∪ factorExcessExceptional N) := by
    intro n hnmem
    rw [fiveFactorExceptional, Finset.mem_filter, Finset.mem_Icc] at hnmem
    by_cases hnN : n = N
    · simp [hnN]
    simp only [Finset.mem_insert, Finset.mem_union, hnN, false_or,
      omegaExceptional, factorExcessExceptional, Finset.mem_filter,
      Finset.mem_Ico]
    have hnBounds : 1 ≤ n ∧ n < N :=
      ⟨hnmem.1.1, lt_of_le_of_ne hnmem.1.2 hnN⟩
    have hOmega : 5 * Real.log (Real.log (N : ℝ)) < (Ω n : ℝ) :=
      (Nat.floor_lt (mul_nonneg (by norm_num) hL)).1 hnmem.2
    by_cases hdistinct :
        2 * Real.log (Real.log (N : ℝ)) < (ω n : ℝ)
    · exact Or.inl ⟨hnBounds, hdistinct⟩
    · right
      refine ⟨hnBounds, ?_⟩
      have hn0 : n ≠ 0 := Nat.ne_of_gt hnmem.1.1
      have hdecomp := Omega_eq_omega_add_card_properPrimePowerDivisors hn0
      have homegaLe : (ω n : ℝ) ≤ 2 * Real.log (Real.log (N : ℝ)) :=
        le_of_not_gt hdistinct
      have hcast : (Ω n : ℝ) = (ω n : ℝ) + ((Ω n - ω n : ℕ) : ℝ) := by
        rw [hdecomp, Nat.add_sub_cancel_left, Nat.cast_add]
      linarith
  have hcard := Finset.card_le_card hsub
  have hins := Finset.card_insert_le N
    (omegaExceptional N ∪ factorExcessExceptional N)
  have hunion := Finset.card_union_le (omegaExceptional N) (factorExcessExceptional N)
  omega

/-- Quantitative common bound for both factorization cutoffs. -/
lemma exists_fiveFactorExceptional_card_le_div_logLog :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ((fiveFactorExceptional N).card : ℝ) ≤
        1 + C * (N : ℝ) / Real.log (Real.log (N : ℝ)) := by
  obtain ⟨Cω, hCω, hω⟩ := exists_omegaExceptional_card_le_div_logLog
  let C := Cω + 14
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  have hlognonneg : ∀ᶠ N : ℕ in atTop,
      0 ≤ Real.log (Real.log (N : ℝ)) :=
    (Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop (0 : ℝ))
  filter_upwards [hω, eventually_factorExcessExceptional_card_le_div_logLog,
      hlognonneg] with N hωN hexN hL
  have hcard := fiveFactorExceptional_card_le_sum hL
  have hcardR : ((fiveFactorExceptional N).card : ℝ) ≤
      1 + (omegaExceptional N).card + (factorExcessExceptional N).card := by
    exact_mod_cast hcard
  calc
    ((fiveFactorExceptional N).card : ℝ) ≤
        1 + (omegaExceptional N).card + (factorExcessExceptional N).card := hcardR
    _ ≤ 1 + (Cω * (N : ℝ) / Real.log (Real.log (N : ℝ))) +
          (14 * (N : ℝ) / Real.log (Real.log (N : ℝ))) := by linarith
    _ = 1 + C * (N : ℝ) / Real.log (Real.log (N : ℝ)) := by
      dsimp [C]
      ring

lemma tendsto_nat_M_atTop : Tendsto (fun N : ℕ ↦ (M N : ℝ)) atTop atTop := by
  have hpow : Tendsto almostOnePower atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (9999 : ℝ) / 10000)).comp
      tendsto_natCast_atTop_atTop
  refine tendsto_atTop_mono' atTop ?_ hpow
  filter_upwards [eventually_almostOnePower_le_natS,
    eventually_nat_scale_chain] with N hNS hchain
  exact hNS.trans (hchain.1.trans hchain.2.1)

lemma tendsto_sqrt_logLogLog_div_logLog :
    Tendsto (fun N : ℕ ↦
      Real.sqrt (logLogLogScale N) / logLogScale N) atTop (nhds 0) := by
  have ho : (fun x : ℝ ↦ Real.sqrt (Real.log x)) =o[atTop]
      (fun x : ℝ ↦ x) := by
    simpa [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_rpow_atTop (1 / 2 : ℝ)
        (show (0 : ℝ) < 1 by norm_num))
  have hratio := ho.tendsto_div_nhds_zero.comp tendsto_logLogScale
  convert hratio using 1
  funext N
  rfl

/-- Both factor exceptions are negligible even relative to the lower endpoint
`M = N / sqrt(log log log N)` of the denominator interval. -/
theorem fiveFactorExceptional_card_div_M_tendsto_zero :
    Tendsto (fun N : ℕ ↦
      ((fiveFactorExceptional N).card : ℝ) / (M N : ℝ)) atTop (nhds 0) := by
  obtain ⟨C, hC, hcard⟩ := exists_fiveFactorExceptional_card_le_div_logLog
  have hupper : Tendsto (fun N : ℕ ↦
      (1 : ℝ) / (M N : ℝ) +
        2 * C * (Real.sqrt (logLogLogScale N) / logLogScale N))
      atTop (nhds 0) := by
    convert (tendsto_const_nhds.div_atTop tendsto_nat_M_atTop).add
      (tendsto_sqrt_logLogLog_div_logLog.const_mul (2 * C)) using 1 <;> ring
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun N ↦
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [hcard, eventually_real_scales_ge_two, eventually_pos_scales,
      tendsto_logLogScale.eventually (eventually_gt_atTop (0 : ℝ)),
      tendsto_nat_M_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with
      N hcardN hscales hpos hLL hMpos
    rcases hpos with ⟨hNpos, hlog, hloglog, hlogloglog⟩
    have hMhalf : MReal N / 2 ≤ (M N : ℝ) := half_le_floor hscales.2.2
    have hsqrtpos : 0 < Real.sqrt (logLogLogScale N) :=
      Real.sqrt_pos.2 hlogloglog
    have hMReal : MReal N = (N : ℝ) / Real.sqrt (logLogLogScale N) := rfl
    have hNM : (N : ℝ) / (M N : ℝ) ≤
        2 * Real.sqrt (logLogLogScale N) := by
      rw [div_le_iff₀ hMpos]
      have hNle : (N : ℝ) ≤
          2 * Real.sqrt (logLogLogScale N) * (M N : ℝ) := by
        have := mul_le_mul_of_nonneg_left hMhalf
          (show 0 ≤ 2 * Real.sqrt (logLogLogScale N) by positivity)
        rw [hMReal] at this
        field_simp [hsqrtpos.ne'] at this
        nlinarith
      simpa [mul_assoc] using hNle
    have hdivcard : ((fiveFactorExceptional N).card : ℝ) / (M N : ℝ) ≤
        (1 + C * (N : ℝ) / logLogScale N) / (M N : ℝ) :=
      div_le_div_of_nonneg_right
        (by simpa only [logLogScale, logScale] using hcardN) hMpos.le
    calc
      ((fiveFactorExceptional N).card : ℝ) / (M N : ℝ) ≤
          (1 + C * (N : ℝ) / logLogScale N) / (M N : ℝ) := hdivcard
      _ = (1 : ℝ) / (M N : ℝ) +
          C / logLogScale N * ((N : ℝ) / (M N : ℝ)) := by ring
      _ ≤ (1 : ℝ) / (M N : ℝ) +
          C / logLogScale N * (2 * Real.sqrt (logLogLogScale N)) := by
        gcongr
      _ = (1 : ℝ) / (M N : ℝ) +
          2 * C * (Real.sqrt (logLogLogScale N) / logLogScale N) := by ring
  · exact hupper

lemma fiveFactorExceptional_isLittleO :
    (fun N : ℕ ↦ ((fiveFactorExceptional N).card : ℝ)) =o[atTop]
      (fun N : ℕ ↦ (N : ℝ)) := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hω := (Asymptotics.isLittleO_iff.mp omegaExceptional_isLittleO) (c := ε / 3)
    (div_pos hε (by norm_num))
  have hex := (Asymptotics.isLittleO_iff.mp factorExcessExceptional_isLittleO) (c := ε / 3)
    (div_pos hε (by norm_num))
  have hlogpos : ∀ᶠ N : ℕ in atTop,
      0 ≤ Real.log (Real.log (N : ℝ)) :=
    (Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop (0 : ℝ))
  have hNlarge : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ (ε / 3) * N :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop
      (div_pos hε (by norm_num))).eventually (eventually_ge_atTop 1)
  filter_upwards [hω, hex, hlogpos, hNlarge, eventually_gt_atTop (0 : ℕ)] with
      N hωN hexN hL hOne hN
  rw [norm_of_nonneg (Nat.cast_nonneg _), norm_of_nonneg (Nat.cast_nonneg _)] at hωN hexN ⊢
  have hsub : fiveFactorExceptional N ⊆
      insert N (omegaExceptional N ∪ factorExcessExceptional N) := by
    intro n hnmem
    rw [fiveFactorExceptional, Finset.mem_filter, Finset.mem_Icc] at hnmem
    by_cases hnN : n = N
    · simp [hnN]
    simp only [Finset.mem_insert, Finset.mem_union, hnN, false_or,
      omegaExceptional, factorExcessExceptional, Finset.mem_filter,
      Finset.mem_Ico]
    have hnIco : n ∈ Ico 1 N := Finset.mem_Ico.mpr ⟨hnmem.1.1, lt_of_le_of_ne hnmem.1.2 hnN⟩
    have hnBounds : 1 ≤ n ∧ n < N := Finset.mem_Ico.mp hnIco
    have hOmega : 5 * Real.log (Real.log (N : ℝ)) < (Ω n : ℝ) := by
      exact (Nat.floor_lt (mul_nonneg (by norm_num) hL)).1 hnmem.2
    by_cases hdistinct :
        2 * Real.log (Real.log (N : ℝ)) < (ω n : ℝ)
    · exact Or.inl ⟨hnBounds, hdistinct⟩
    · right
      refine ⟨hnBounds, ?_⟩
      have hn0 : n ≠ 0 := Nat.ne_of_gt hnmem.1.1
      have hdecomp := Omega_eq_omega_add_card_properPrimePowerDivisors hn0
      have homegaLe : (ω n : ℝ) ≤ 2 * Real.log (Real.log (N : ℝ)) :=
        le_of_not_gt hdistinct
      have hcast : (Ω n : ℝ) = (ω n : ℝ) + ((Ω n - ω n : ℕ) : ℝ) := by
        rw [hdecomp, Nat.add_sub_cancel_left, Nat.cast_add]
      linarith
  have hcardNat := Finset.card_le_card hsub
  have hunion := Finset.card_union_le (omegaExceptional N) (factorExcessExceptional N)
  have hcard : ((fiveFactorExceptional N).card : ℝ) ≤
      1 + (omegaExceptional N).card + (factorExcessExceptional N).card := by
    have hins := Finset.card_insert_le N
      (omegaExceptional N ∪ factorExcessExceptional N)
    have hcardNat' : (fiveFactorExceptional N).card ≤
        1 + (omegaExceptional N).card + (factorExcessExceptional N).card := by
      omega
    exact_mod_cast hcardNat'
  calc
    ((fiveFactorExceptional N).card : ℝ) ≤
        1 + (omegaExceptional N).card + (factorExcessExceptional N).card := hcard
    _ ≤ 1 + (ε / 3) * (N : ℝ) + (ε / 3) * (N : ℝ) := by linarith
    _ ≤ ε * (N : ℝ) := by
      linarith

/-- Denominators violating the largest-exponent cutoff. -/
def exponentExceptional (N : ℕ) : Finset ℕ :=
  (Icc 1 N).filter fun n ↦ exponentBound N < maxPrimeExponent n

/-- Denominators violating the total-multiplicity cutoff. -/
def factorExceptional (N : ℕ) : Finset ℕ :=
  (Icc 1 N).filter fun n ↦ factorBound N < Ω n

lemma exponentExceptional_subset_five (N : ℕ) :
    exponentExceptional N ⊆ fiveFactorExceptional N := by
  intro n hn
  simp only [exponentExceptional, fiveFactorExceptional, Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, hn.2.trans_le (maxPrimeExponent_le_Omega n)⟩

lemma factorExceptional_subset_five {N : ℕ}
    (hL : 0 ≤ Real.log (Real.log (N : ℝ))) :
    factorExceptional N ⊆ fiveFactorExceptional N := by
  intro n hn
  simp only [factorExceptional, fiveFactorExceptional, Finset.mem_filter] at hn ⊢
  refine ⟨hn.1, (show exponentBound N ≤ factorBound N from ?_).trans_lt hn.2⟩
  exact Nat.floor_mono (by nlinarith)

theorem exponentExceptional_isLittleO :
    (fun N : ℕ ↦ ((exponentExceptional N).card : ℝ)) =o[atTop]
      (fun N : ℕ ↦ (N : ℝ)) := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hfive := (Asymptotics.isLittleO_iff.mp fiveFactorExceptional_isLittleO) (c := ε) hε
  filter_upwards [hfive] with N hN
  rw [norm_of_nonneg (Nat.cast_nonneg _), norm_of_nonneg (Nat.cast_nonneg _)] at hN ⊢
  exact (Nat.cast_le.mpr
    (Finset.card_le_card (exponentExceptional_subset_five N))).trans hN

theorem factorExceptional_isLittleO :
    (fun N : ℕ ↦ ((factorExceptional N).card : ℝ)) =o[atTop]
      (fun N : ℕ ↦ (N : ℝ)) := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hfive := (Asymptotics.isLittleO_iff.mp fiveFactorExceptional_isLittleO) (c := ε) hε
  have hlogpos : ∀ᶠ N : ℕ in atTop,
      0 ≤ Real.log (Real.log (N : ℝ)) :=
    (Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop (0 : ℝ))
  filter_upwards [hfive, hlogpos] with N hN hL
  rw [norm_of_nonneg (Nat.cast_nonneg _), norm_of_nonneg (Nat.cast_nonneg _)] at hN ⊢
  exact (Nat.cast_le.mpr
    (Finset.card_le_card (factorExceptional_subset_five hL))).trans hN

theorem exponentExceptional_card_div_M_tendsto_zero :
    Tendsto (fun N : ℕ ↦
      ((exponentExceptional N).card : ℝ) / (M N : ℝ)) atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun N ↦
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards with N
    have hcard : ((exponentExceptional N).card : ℝ) ≤
        ((fiveFactorExceptional N).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (exponentExceptional_subset_five N)
    exact div_le_div_of_nonneg_right hcard (Nat.cast_nonneg (M N))
  · exact fiveFactorExceptional_card_div_M_tendsto_zero

theorem factorExceptional_card_div_M_tendsto_zero :
    Tendsto (fun N : ℕ ↦
      ((factorExceptional N).card : ℝ) / (M N : ℝ)) atTop (nhds 0) := by
  have hlognonneg : ∀ᶠ N : ℕ in atTop,
      0 ≤ Real.log (Real.log (N : ℝ)) :=
    (Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop (0 : ℝ))
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun N ↦
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [hlognonneg] with N hL
    have hcard : ((factorExceptional N).card : ℝ) ≤
        ((fiveFactorExceptional N).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (factorExceptional_subset_five hL)
    exact div_le_div_of_nonneg_right hcard (Nat.cast_nonneg (M N))
  · exact fiveFactorExceptional_card_div_M_tendsto_zero

end

end Erdos297.FactorDensity
