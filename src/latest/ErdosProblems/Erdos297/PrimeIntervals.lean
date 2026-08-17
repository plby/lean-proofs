/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import PrimeNumberTheoremAnd.Consequences
import ErdosProblems.Erdos297.GoodFactorization

/-!
# Prime intervals used in the lower bound for Erdős Problem 297

This file extracts the elementary consequences of the prime number theorem
needed in the auxiliary-prime part of Liu--Sawhney's local limit argument.
All the estimates are stated for the actual finite sets used later.  In
particular, the interval endpoints include the natural floor/ceiling
rounding, rather than hiding it in an asymptotic notation.
-/

open scoped BigOperators

namespace Erdos297.PrimeIntervals

open Filter Finset Real Asymptotics
open UnitFractions

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Primes in the closed natural interval `[a,b]`. -/
def primesBetween (a b : ℕ) : Finset ℕ :=
  (Icc a b).filter Nat.Prime

@[simp] lemma mem_primesBetween {a b p : ℕ} :
    p ∈ primesBetween a b ↔ a ≤ p ∧ p ≤ b ∧ p.Prime := by
  simp [primesBetween, and_assoc]

/-- The auxiliary primes of Liu--Sawhney: primes in
`[ceil (20 log N), floor (40 log N)]`. -/
def auxiliaryPrimes (N : ℕ) : Finset ℕ :=
  primesBetween ⌈20 * Real.log (N : ℝ)⌉₊ ⌊40 * Real.log (N : ℝ)⌋₊

@[simp] lemma mem_auxiliaryPrimes {N p : ℕ} :
    p ∈ auxiliaryPrimes N ↔
      ⌈20 * Real.log (N : ℝ)⌉₊ ≤ p ∧
        p ≤ ⌊40 * Real.log (N : ℝ)⌋₊ ∧ p.Prime := by
  simp [auxiliaryPrimes]

/-- The broad interval used when one auxiliary prime may be chosen between
`a` and `50a`. -/
def primesOneFifty (a : ℕ) : Finset ℕ := primesBetween a (50 * a)

/-- The interval `[floor (S/2),S]` used for the second prime in the
two-prime construction. -/
def primesHalfFull (S : ℕ) : Finset ℕ := primesBetween (S / 2) S

@[simp] lemma mem_primesOneFifty {a p : ℕ} :
    p ∈ primesOneFifty a ↔ a ≤ p ∧ p ≤ 50 * a ∧ p.Prime := by
  simp [primesOneFifty]

@[simp] lemma mem_primesHalfFull {S p : ℕ} :
    p ∈ primesHalfFull S ↔ S / 2 ≤ p ∧ p ≤ S ∧ p.Prime := by
  simp [primesHalfFull]

/-! ## Finite counting and avoidance lemmas -/

/-- The primes in `(a,b]` are contained in the closed interval `[a,b]`.
Consequently the difference of the two prime-counting functions is a lower
bound for `primesBetween`. -/
lemma primeCounting_sub_le_card_primesBetween (a b : ℕ) :
    Nat.primeCounting b - Nat.primeCounting a ≤ (primesBetween a b).card := by
  by_cases hab : a ≤ b
  · rw [prime_counting_eq_card_primes, prime_counting_eq_card_primes,
      ← Finset.card_sdiff_of_subset]
    · apply Finset.card_le_card
      intro p hp
      rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc,
        Finset.mem_filter, Finset.mem_Icc] at hp
      rw [mem_primesBetween]
      have hap : a ≤ p := by
        by_contra hpa
        exact hp.2 ⟨⟨hp.1.1.1, Nat.le_of_lt (Nat.lt_of_not_ge hpa)⟩, hp.1.2⟩
      exact ⟨hap, hp.1.1.2, hp.1.2⟩
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
      exact ⟨⟨hp.1.1, hp.1.2.trans hab⟩, hp.2⟩
  · have hba : b ≤ a := Nat.le_of_lt (Nat.lt_of_not_ge hab)
    have hpi := Nat.monotone_primeCounting hba
    simp [Nat.sub_eq_zero_of_le hpi]

/-- Exact strict-endpoint version: the difference `π(b)-π(a)` counts
primes in `[a+1,b]`. -/
lemma primeCounting_sub_le_card_primesBetween_succ (a b : ℕ) :
    Nat.primeCounting b - Nat.primeCounting a ≤
      (primesBetween (a + 1) b).card := by
  by_cases hab : a ≤ b
  · rw [prime_counting_eq_card_primes, prime_counting_eq_card_primes,
      ← Finset.card_sdiff_of_subset]
    · apply Finset.card_le_card
      intro p hp
      rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc,
        Finset.mem_filter, Finset.mem_Icc] at hp
      rw [mem_primesBetween]
      exact ⟨Nat.add_one_le_iff.mpr (lt_of_not_ge fun hpa ↦
        hp.2 ⟨⟨hp.1.1.1, hpa⟩, hp.1.2⟩), hp.1.1.2, hp.1.2⟩
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
      exact ⟨⟨hp.1.1, hp.1.2.trans hab⟩, hp.2⟩
  · have hba : b ≤ a := Nat.le_of_lt (Nat.lt_of_not_ge hab)
    have hpi := Nat.monotone_primeCounting hba
    simp [Nat.sub_eq_zero_of_le hpi]

/-- More elements in the finite set of primes than in an exceptional set
leave a prime outside the exceptional set. -/
lemma exists_prime_le_not_mem {X : ℕ} {E : Finset ℕ}
    (hE : E.card < Nat.primeCounting X) :
    ∃ p : ℕ, p.Prime ∧ p ≤ X ∧ p ∉ E := by
  rw [prime_counting_eq_card_primes] at hE
  obtain ⟨p, hp, hpE⟩ := Finset.exists_mem_notMem_of_card_lt_card hE
  simp only [Finset.mem_filter, Finset.mem_Icc] at hp
  exact ⟨p, hp.2, hp.1.2, hpE⟩

/-- A version of `exists_prime_le_not_mem` specialized to excluding the
prime divisors of `d`. -/
lemma exists_prime_le_not_dvd {X d : ℕ} (hd : d ≠ 0)
    (hcard : d.primeFactors.card < Nat.primeCounting X) :
    ∃ p : ℕ, p.Prime ∧ p ≤ X ∧ ¬p ∣ d := by
  obtain ⟨p, hp, hpX, hpmem⟩ :=
    exists_prime_le_not_mem (X := X) (E := d.primeFactors) hcard
  exact ⟨p, hp, hpX, fun hpd ↦
    hpmem ((Nat.mem_primeFactors.mpr ⟨hp, hpd, hd⟩))⟩

/-- The same pigeonhole argument inside a closed prime interval. -/
lemma exists_prime_in_interval_not_dvd {a b d : ℕ} (hd : d ≠ 0)
    (hcard : d.primeFactors.card < (primesBetween a b).card) :
    ∃ p : ℕ, p.Prime ∧ a ≤ p ∧ p ≤ b ∧ ¬p ∣ d := by
  obtain ⟨p, hp, hpD⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcard
  rw [mem_primesBetween] at hp
  exact ⟨p, hp.2.2, hp.1, hp.2.1, fun hpd ↦
    hpD (Nat.mem_primeFactors.mpr ⟨hp.2.2, hpd, hd⟩)⟩

/-! ## Uniform prime-counting bounds -/

/-- A deliberately loose `10%` form of the prime number theorem, first for
real arguments with the natural floor used by `primeCounting`. -/
theorem eventually_primeCounting_floor_bounds :
    ∀ᶠ x : ℝ in atTop,
      (9 / 10 : ℝ) * (x / Real.log x) ≤ Nat.primeCounting ⌊x⌋₊ ∧
        (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤
          (11 / 10 : ℝ) * (x / Real.log x) := by
  obtain ⟨c, hc, hpi⟩ := pi_alt
  have hcBound := hc.bound (by norm_num : (0 : ℝ) < 1 / 10)
  filter_upwards [hcBound, eventually_gt_atTop (1 : ℝ)] with x hcx hx
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hcabs : |c x| ≤ (1 / 10 : ℝ) := by
    simpa only [norm_eq_abs, norm_one, mul_one] using hcx
  have hcLower : (9 / 10 : ℝ) ≤ 1 + c x := by
    rw [abs_le] at hcabs
    linarith
  have hcUpper : 1 + c x ≤ (11 / 10 : ℝ) := by
    rw [abs_le] at hcabs
    linarith
  have hq : 0 ≤ x / Real.log x := (div_pos hxpos hlog).le
  rw [hpi x]
  constructor
  · simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_right hcLower hq
  · simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_right hcUpper hq

/-- A deliberately loose `10%` form of the prime number theorem.  Keeping
it as one reusable lemma makes all later interval calculations independent
of the particular error function used in the repository's PNT. -/
theorem eventually_primeCounting_bounds :
    ∀ᶠ n : ℕ in atTop,
      (9 / 10 : ℝ) * ((n : ℝ) / Real.log n) ≤ Nat.primeCounting n ∧
        (Nat.primeCounting n : ℝ) ≤
          (11 / 10 : ℝ) * ((n : ℝ) / Real.log n) := by
  simpa using tendsto_natCast_atTop_atTop.eventually
    eventually_primeCounting_floor_bounds

/-- Eventually there are at least `X/(2 log X)` primes at most `X`.
This is the supply estimate used before excluding prime factors. -/
theorem eventually_half_mul_div_log_le_primeCounting :
    ∀ᶠ X : ℕ in atTop,
      (X : ℝ) / (2 * Real.log X) ≤ Nat.primeCounting X := by
  filter_upwards
      [eventually_primeCounting_bounds,
        tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (1 : ℝ))]
      with X hX hX1
  calc
    (X : ℝ) / (2 * Real.log X) =
        (1 / 2 : ℝ) * ((X : ℝ) / Real.log X) := by ring
    _ ≤ (9 / 10 : ℝ) * ((X : ℝ) / Real.log X) := by
      exact mul_le_mul_of_nonneg_right (by norm_num)
        (div_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hX1.le))
    _ ≤ Nat.primeCounting X := hX.1

/-! ## The two broad intervals used for constructing `r` -/

/-- The interval `[a,50a]` eventually contains at least `a/log a` primes. -/
theorem eventually_div_log_le_card_primesOneFifty :
    ∀ᶠ a : ℕ in atTop,
      (a : ℝ) / Real.log a ≤ (primesOneFifty a).card := by
  have ht50 : Tendsto (fun a : ℕ ↦ 50 * a) atTop atTop :=
    tendsto_atTop.2 fun b ↦ by
      filter_upwards [eventually_ge_atTop b] with a ha
      omega
  filter_upwards
      [eventually_primeCounting_bounds,
        ht50.eventually eventually_primeCounting_bounds,
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
          (eventually_ge_atTop (Real.log 50)),
        tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (1 : ℝ))]
      with a ha h50a hlog50 ha1
  dsimp only [Function.comp_apply] at hlog50
  have hloga : 0 < Real.log (a : ℝ) := Real.log_pos ha1
  have hlog50pos : 0 ≤ Real.log (50 : ℝ) := Real.log_nonneg (by norm_num)
  have hlogmul : Real.log (50 * (a : ℝ)) =
      Real.log 50 + Real.log (a : ℝ) := by
    rw [Real.log_mul (by norm_num) (ne_of_gt (lt_trans zero_lt_one ha1))]
  have hden : Real.log (50 * (a : ℝ)) ≤ 2 * Real.log (a : ℝ) := by
    rw [hlogmul]
    linarith
  have hdenpos : 0 < Real.log (50 * (a : ℝ)) := by
    rw [hlogmul]
    positivity
  have hlower :
      (45 / 2 : ℝ) * ((a : ℝ) / Real.log a) ≤
        (Nat.primeCounting (50 * a) : ℝ) := by
    calc
      (45 / 2 : ℝ) * ((a : ℝ) / Real.log a) =
          (9 / 10 : ℝ) * ((50 * (a : ℝ)) /
            (2 * Real.log (a : ℝ))) := by ring
      _ ≤ (9 / 10 : ℝ) * ((50 * (a : ℝ)) /
            Real.log (50 * (a : ℝ))) := by gcongr
      _ = (9 / 10 : ℝ) * (((50 * a : ℕ) : ℝ) /
            Real.log (50 * a : ℕ)) := by norm_num
      _ ≤ Nat.primeCounting (50 * a) := h50a.1
  have hupper :
      (Nat.primeCounting a : ℝ) ≤
        (11 / 10 : ℝ) * ((a : ℝ) / Real.log a) := ha.2
  have hdiff :
      (a : ℝ) / Real.log a ≤
        (Nat.primeCounting (50 * a) : ℝ) - Nat.primeCounting a := by
    have hratio : 0 < (a : ℝ) / Real.log a := by
      exact div_pos (lt_trans zero_lt_one ha1) hloga
    nlinarith
  have hcard := primeCounting_sub_le_card_primesBetween a (50 * a)
  have hpile : Nat.primeCounting a ≤ Nat.primeCounting (50 * a) :=
    Nat.monotone_primeCounting (by omega)
  have hcardR :
      (Nat.primeCounting (50 * a) : ℝ) - Nat.primeCounting a ≤
        ((primesBetween a (50 * a)).card : ℝ) := by
    rw [← Nat.cast_sub hpile]
    exact_mod_cast hcard
  rw [primesOneFifty]
  exact hdiff.trans hcardR

/-- The interval `[floor (S/2),S]` eventually contains at least
`S/(10 log S)` primes. -/
theorem eventually_div_ten_log_le_card_primesHalfFull :
    ∀ᶠ S : ℕ in atTop,
      (S : ℝ) / (10 * Real.log S) ≤ (primesHalfFull S).card := by
  filter_upwards
      [eventually_primeCounting_bounds,
        (Nat.tendsto_div_const_atTop (by norm_num : (2 : ℕ) ≠ 0)).eventually
          eventually_primeCounting_bounds,
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
          (eventually_ge_atTop (20 * Real.log 2)),
        tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (4 : ℝ))]
      with S hS hhalf hlogS hS4
  dsimp only [Function.comp_apply] at hlogS
  have hSpos : (0 : ℝ) < S := by linarith
  have hS4nat : 4 < S := by exact_mod_cast hS4
  have hlogSpos : 0 < Real.log (S : ℝ) := Real.log_pos (by linarith)
  have hhalfPosNat : 0 < S / 2 := by omega
  have hhalfRealLower : (S : ℝ) / 3 ≤ (S / 2 : ℕ) := by
    have hnat : S ≤ 3 * (S / 2) := by omega
    have hnatR : (S : ℝ) ≤ 3 * (S / 2 : ℕ) := by exact_mod_cast hnat
    linarith
  have hloghalfPos : 0 < Real.log (S / 2 : ℕ) :=
    Real.log_pos (by exact_mod_cast (show 1 < S / 2 by omega))
  have hloghalfLower :
      (9 / 10 : ℝ) * Real.log (S : ℝ) ≤ Real.log (S / 2 : ℕ) := by
    have hrough : (S : ℝ) / 4 ≤ (S / 2 : ℕ) := by
      have hnat : S ≤ 4 * (S / 2) := by omega
      have hnatR : (S : ℝ) ≤ 4 * (S / 2 : ℕ) := by exact_mod_cast hnat
      linarith
    have hlogrough := Real.strictMonoOn_log.monotoneOn
      (by positivity : (0 : ℝ) < (S : ℝ) / 4)
      (by exact_mod_cast hhalfPosNat : (0 : ℝ) < (S / 2 : ℕ))
      hrough
    have hlogfour : Real.log ((S : ℝ) / 4) =
        Real.log (S : ℝ) - Real.log 4 := by
      rw [Real.log_div (ne_of_gt hSpos) (by norm_num : (4 : ℝ) ≠ 0)]
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num,
        Real.log_mul (by norm_num) (by norm_num)]
      ring
    rw [hlogfour, hlog4] at hlogrough
    linarith
  have hhalfUpper :
      (Nat.primeCounting (S / 2) : ℝ) ≤
        (11 / 18 : ℝ) * ((S : ℝ) / Real.log S) := by
    calc
      (Nat.primeCounting (S / 2) : ℝ) ≤
          (11 / 10 : ℝ) * (((S / 2 : ℕ) : ℝ) /
            Real.log (S / 2 : ℕ)) := hhalf.2
      _ ≤ (11 / 10 : ℝ) * (((S : ℝ) / 2) /
            ((9 / 10 : ℝ) * Real.log S)) := by
        gcongr
        exact Nat.cast_div_le
      _ = (11 / 18 : ℝ) * ((S : ℝ) / Real.log S) := by ring
  have hfullLower :
      (9 / 10 : ℝ) * ((S : ℝ) / Real.log S) ≤
        Nat.primeCounting S := hS.1
  have hdiff :
      (S : ℝ) / (10 * Real.log S) ≤
        (Nat.primeCounting S : ℝ) - Nat.primeCounting (S / 2) := by
    have hratio : 0 < (S : ℝ) / Real.log S := div_pos hSpos hlogSpos
    have htarget : (S : ℝ) / (10 * Real.log S) =
        (1 / 10 : ℝ) * ((S : ℝ) / Real.log S) := by ring
    rw [htarget]
    nlinarith
  have hcard := primeCounting_sub_le_card_primesBetween (S / 2) S
  have hpile : Nat.primeCounting (S / 2) ≤ Nat.primeCounting S :=
    Nat.monotone_primeCounting (Nat.div_le_self S 2)
  have hcardR :
      (Nat.primeCounting S : ℝ) - Nat.primeCounting (S / 2) ≤
        ((primesBetween (S / 2) S).card : ℝ) := by
    rw [← Nat.cast_sub hpile]
    exact_mod_cast hcard
  rw [primesHalfFull]
  exact hdiff.trans hcardR

/-- A small constant-size form of the dyadic prime supply.  Six primes are
enough for the finite exceptional sets in the smooth-multiplier step. -/
theorem eventually_six_le_card_primesBetween_dyadic :
    ∀ᶠ X : ℕ in atTop, 6 ≤ (primesBetween (X + 1) (2 * X)).card := by
  have hreal := tendsto_by_squeeze (1 : ℝ) (by norm_num)
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  have hsix := hnat.eventually (eventually_ge_atTop (6 : ℝ))
  filter_upwards [hsix] with X hX
  have hfloor2 : ⌊(2 : ℝ) * (X : ℝ)⌋₊ = 2 * X := by
    rw [show (2 : ℝ) * (X : ℝ) = ((2 * X : ℕ) : ℝ) by norm_num,
      Nat.floor_natCast]
  have hfloor1 : ⌊(X : ℝ)⌋₊ = X := by norm_num
  have hX' :
      (6 : ℝ) ≤ (Nat.primeCounting (2 * X) : ℝ) - Nat.primeCounting X := by
    simpa only [Function.comp_apply, show (1 : ℝ) + 1 = 2 by norm_num,
      hfloor2, hfloor1] using hX
  have hcardNat := primeCounting_sub_le_card_primesBetween_succ X (2 * X)
  have hpile : Nat.primeCounting X ≤ Nat.primeCounting (2 * X) :=
    Nat.monotone_primeCounting (by omega)
  have hcardReal :
      (Nat.primeCounting (2 * X) : ℝ) - Nat.primeCounting X ≤
        ((primesBetween (X + 1) (2 * X)).card : ℝ) := by
    rw [← Nat.cast_sub hpile]
    exact_mod_cast hcardNat
  have hfinal : (6 : ℝ) ≤
      ((primesBetween (X + 1) (2 * X)).card : ℝ) := hX'.trans hcardReal
  exact_mod_cast hfinal

/-! ## The source interval `[20 log N,40 log N]` -/

/-- Removing the primes at most `floor (20 log N)` from those at most
`floor (40 log N)` leaves a subset of `auxiliaryPrimes`. -/
lemma primeCounting_log_interval_sub_le_auxiliaryPrimes_card (N : ℕ) :
    Nat.primeCounting ⌊40 * Real.log (N : ℝ)⌋₊ -
        Nat.primeCounting ⌊20 * Real.log (N : ℝ)⌋₊ ≤
      (auxiliaryPrimes N).card := by
  have hbase := primeCounting_sub_le_card_primesBetween_succ
    ⌊20 * Real.log (N : ℝ)⌋₊ ⌊40 * Real.log (N : ℝ)⌋₊
  apply hbase.trans
  apply Finset.card_le_card
  intro p hp
  rw [mem_primesBetween] at hp
  rw [mem_auxiliaryPrimes]
  have hceil : ⌈20 * Real.log (N : ℝ)⌉₊ ≤
      ⌊20 * Real.log (N : ℝ)⌋₊ + 1 := Nat.ceil_le_floor_add_one _
  exact ⟨hceil.trans hp.1, hp.2⟩

/-- There are eventually at least `5 log N / log log N` auxiliary primes.
The true leading constant is `20`; the slack here absorbs both PNT errors
and all endpoint rounding. -/
theorem eventually_five_log_div_loglog_le_card_auxiliaryPrimes :
    ∀ᶠ N : ℕ in atTop,
      5 * Real.log (N : ℝ) / Real.log (Real.log (N : ℝ)) ≤
        (auxiliaryPrimes N).card := by
  let hlog : ℕ → ℝ := fun N ↦ Real.log (N : ℝ)
  have ht20 : Tendsto (fun N : ℕ ↦ 20 * hlog N) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop
      (by norm_num)
  have ht40 : Tendsto (fun N : ℕ ↦ 40 * hlog N) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop
      (by norm_num)
  have hP20 := ht20.eventually eventually_primeCounting_floor_bounds
  have hP40 := ht40.eventually eventually_primeCounting_floor_bounds
  filter_upwards
      [hP20, hP40,
        (Real.tendsto_log_atTop.comp
          (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
          (eventually_ge_atTop (10 * Real.log 40)),
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
          (eventually_gt_atTop 1)]
      with N hp20 hp40 hll hlogN
  dsimp [hlog] at *
  let L := Real.log (N : ℝ)
  let LL := Real.log L
  have hL : 0 < L := by dsimp [L]; linarith
  have hLL : 0 < LL := by exact Real.log_pos hlogN
  have hlog20nonneg : 0 ≤ Real.log (20 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog40nonneg : 0 ≤ Real.log (40 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog20le40 : Real.log (20 : ℝ) ≤ Real.log (40 : ℝ) :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) (by norm_num) (by norm_num)
  have hden40 : Real.log (40 * L) = Real.log 40 + LL := by
    rw [Real.log_mul (by norm_num) hL.ne']
  have hden20 : Real.log (20 * L) = Real.log 20 + LL := by
    rw [Real.log_mul (by norm_num) hL.ne']
  have hden40pos : 0 < Real.log (40 * L) := by
    rw [hden40]
    positivity
  have hden20pos : 0 < Real.log (20 * L) := by
    rw [hden20]
    positivity
  have hden40le : Real.log (40 * L) ≤ (11 / 10 : ℝ) * LL := by
    rw [hden40]
    linarith
  have hLLle20 : LL ≤ Real.log (20 * L) := by
    rw [hden20]
    linarith
  have hlower :
      (360 / 11 : ℝ) * (L / LL) ≤
        (Nat.primeCounting ⌊40 * L⌋₊ : ℝ) := by
    calc
      (360 / 11 : ℝ) * (L / LL) =
          (9 / 10 : ℝ) * ((40 * L) / ((11 / 10 : ℝ) * LL)) := by ring
      _ ≤ (9 / 10 : ℝ) * ((40 * L) / Real.log (40 * L)) := by
        gcongr
      _ ≤ Nat.primeCounting ⌊40 * L⌋₊ := hp40.1
  have hupper :
      (Nat.primeCounting ⌊20 * L⌋₊ : ℝ) ≤ 22 * (L / LL) := by
    calc
      (Nat.primeCounting ⌊20 * L⌋₊ : ℝ) ≤
          (11 / 10 : ℝ) * ((20 * L) / Real.log (20 * L)) := hp20.2
      _ ≤ (11 / 10 : ℝ) * ((20 * L) / LL) := by gcongr
      _ = 22 * (L / LL) := by ring
  have hdiff :
      5 * L / LL ≤
        (Nat.primeCounting ⌊40 * L⌋₊ : ℝ) -
          Nat.primeCounting ⌊20 * L⌋₊ := by
    have hratio : 0 < L / LL := div_pos hL hLL
    have htarget : 5 * L / LL = 5 * (L / LL) := by ring
    rw [htarget]
    nlinarith
  have hcardNat := primeCounting_log_interval_sub_le_auxiliaryPrimes_card N
  have hfloor : ⌊20 * L⌋₊ ≤ ⌊40 * L⌋₊ := by
    exact Nat.floor_mono (by nlinarith)
  have hpile := Nat.monotone_primeCounting hfloor
  have hcardReal :
      (Nat.primeCounting ⌊40 * L⌋₊ : ℝ) -
          Nat.primeCounting ⌊20 * L⌋₊ ≤
        ((auxiliaryPrimes N).card : ℝ) := by
    rw [← Nat.cast_sub hpile]
    exact_mod_cast hcardNat
  exact hdiff.trans hcardReal

/-- Any subset containing at least eighty percent of the auxiliary primes
has product greater than `N`.  This is the exact product input to the
common-nearby-multiple argument. -/
theorem eventually_product_auxiliaryPrimes_dense :
    ∀ᶠ N : ℕ in atTop, ∀ block : Finset ℕ,
      block ⊆ auxiliaryPrimes N →
      4 * (auxiliaryPrimes N).card ≤ 5 * block.card →
      N < block.prod id := by
  filter_upwards
      [eventually_five_log_div_loglog_le_card_auxiliaryPrimes,
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
          (eventually_gt_atTop 1),
        (Real.tendsto_log_atTop.comp
          (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
          (eventually_gt_atTop 0)]
      with N hP hlogN hloglogN
  dsimp only [Function.comp_apply] at hlogN hloglogN
  intro block hblock hdense
  have hNpos : 0 < N := by
    apply Nat.pos_of_ne_zero
    rintro rfl
    norm_num at hlogN
  have hcard :
      4 * Real.log (N : ℝ) / Real.log (Real.log (N : ℝ)) ≤
        (block.card : ℝ) := by
    have hdenseR :
        4 * ((auxiliaryPrimes N).card : ℝ) ≤ 5 * (block.card : ℝ) := by
      exact_mod_cast hdense
    have hP' :
        5 * (Real.log (N : ℝ) / Real.log (Real.log (N : ℝ))) ≤
          ((auxiliaryPrimes N).card : ℝ) := by
      convert hP using 1 <;> ring
    have hnormalized :
        4 * (Real.log (N : ℝ) / Real.log (Real.log (N : ℝ))) ≤
          (block.card : ℝ) := by
      nlinarith
    convert hnormalized using 1 <;> ring
  have hlogProd :
      Real.log (block.prod id : ℕ) = ∑ p ∈ block, Real.log (p : ℝ) := by
    push_cast
    rw [Real.log_prod]
    · simp
    · intro p hp
      have hprime := (mem_auxiliaryPrimes.mp (hblock hp)).2.2
      exact_mod_cast hprime.ne_zero
  have hterm : ∀ p ∈ block,
      Real.log (Real.log (N : ℝ)) ≤ Real.log (p : ℝ) := by
    intro p hp
    have hpAux := mem_auxiliaryPrimes.mp (hblock hp)
    have hpLower : 20 * Real.log (N : ℝ) ≤ (p : ℝ) := by
      calc
        20 * Real.log (N : ℝ) ≤
            (⌈20 * Real.log (N : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ p := by exact_mod_cast hpAux.1
    have hsmall : Real.log (N : ℝ) ≤ (p : ℝ) := by
      have hlogpos : 0 < Real.log (N : ℝ) := by linarith
      nlinarith
    exact Real.strictMonoOn_log.monotoneOn
      (show 0 < Real.log (N : ℝ) by linarith)
      (show (0 : ℝ) < p by exact_mod_cast hpAux.2.2.pos) hsmall
  have hsum :
      (block.card : ℝ) * Real.log (Real.log (N : ℝ)) ≤
        ∑ p ∈ block, Real.log (p : ℝ) := by
    calc
      (block.card : ℝ) * Real.log (Real.log (N : ℝ)) =
          ∑ p ∈ block, Real.log (Real.log (N : ℝ)) := by simp
      _ ≤ _ := Finset.sum_le_sum fun p hp ↦ hterm p hp
  have hlogLt :
      Real.log (N : ℝ) < Real.log (block.prod id : ℕ) := by
    rw [hlogProd]
    have hfour :
        4 * Real.log (N : ℝ) ≤
          (block.card : ℝ) * Real.log (Real.log (N : ℝ)) := by
      have hmul := mul_le_mul_of_nonneg_right hcard hloglogN.le
      have heq :
          (4 * Real.log (N : ℝ) / Real.log (Real.log (N : ℝ))) *
              Real.log (Real.log (N : ℝ)) = 4 * Real.log (N : ℝ) := by
        field_simp [hloglogN.ne']
      rw [heq] at hmul
      exact hmul
    exact lt_of_lt_of_le (by
      have hlogpos : 0 < Real.log (N : ℝ) := by linarith
      nlinarith) (hfour.trans hsum)
  rw [Real.strictMonoOn_log.lt_iff_lt
    (show (0 : ℝ) < N by exact_mod_cast hNpos)
    (by
      have hblockNonempty : block.Nonempty := by
        by_contra hempty
        rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hcard
        simp at hcard
        have hratio : 0 <
            Real.log (N : ℝ) / Real.log (Real.log (N : ℝ)) := by
          exact div_pos (by linarith) hloglogN
        have hcard' :
            4 * (Real.log (N : ℝ) / Real.log (Real.log (N : ℝ))) ≤ 0 := by
          convert hcard using 1 <;> ring
        nlinarith
      show (0 : ℝ) < block.prod id
      exact_mod_cast Finset.prod_pos fun p hp ↦
        (mem_auxiliaryPrimes.mp (hblock hp)).2.2.pos)] at hlogLt
  exact_mod_cast hlogLt

end

end Erdos297.PrimeIntervals
