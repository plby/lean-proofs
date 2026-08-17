/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Ford.Defs
import ErdosProblems.Erdos896.Ford.LowerDefs
import ErdosProblems.Erdos896.Ford.Sieve
import ErdosProblems.Erdos896.Ford.PrimeEstimates
import ErdosProblems.Erdos896.Ford.PrimeIntervalLower
import ErdosProblems.Erdos896.Ford.IsolatedSum

/-!
# The exact-one-divisor construction in Ford's lower bound

This file is the finite arithmetic core of the `r = 1` case of Ford's
Lemma 4.1.  Starting with a divisor `d` of `a` which is isolated at
logarithmic distance `log 2`, a prime `q`, and a rough cofactor `b`, it
constructs

`n = a * q * b`.

The hypotheses say that `q * d` lies in the required divisor window, that
`a` lies below the window, and that every nontrivial divisor of `b` lies
above the window.  They imply that `q * d` is the unique divisor of `n` in
the window.  We give both the ordinary window `(y, 2y]` and the
cross-multiplied window used in Problem 896.

The final finite set uses a literal prime interval and the rough-number set
from `Sieve`.  Its product map is injective once the small part, the prime,
and the rough part are separated.  Consequently its cardinality is a lower
bound for `scaledH1`, with no rounding of `N / (2p)` at either endpoint.
-/

namespace Erdos896.Ford

open scoped BigOperators

/-! ## The natural form of dyadic isolation -/

/-- At the fixed logarithmic width `log 2`, isolation says exactly that `d`
is the unique divisor in the natural window `d < 2e` and `e <= 2d`. -/
theorem dyadicIsolated_unique {a d : ℕ}
    (hd : IsolatedDivisor a d dyadicSigma) :
    ∃! e : ℕ, e ∣ a ∧ d < 2 * e ∧ e ≤ 2 * d := by
  exact (isolatedDivisor_dyadic_iff.mp hd).2.2

/-! ## Rough divisors and coprimality -/

/-- A positive divisor of a rough number is itself rough and, below the
roughness threshold, must be `1`. -/
theorem divisor_eq_one_of_rough_of_lt
    {z b e : ℕ} (hb : IsRough z b) (he : e ∣ b)
    (hepos : 0 < e) (hez : e < z) : e = 1 := by
  by_contra he1
  obtain ⟨r, hr, hre⟩ := Nat.exists_prime_and_dvd he1
  have hrele : r ≤ e := Nat.le_of_dvd hepos hre
  have hrz : r ≤ z - 1 := by omega
  exact hb r hr hrz (hre.trans he)

/-- A positive integer below the roughness threshold is coprime to a rough
integer. -/
theorem coprime_of_lt_of_rough
    {z a b : ℕ} (ha : 0 < a) (haz : a < z)
    (hb : IsRough z b) : Nat.Coprime a b := by
  by_contra hcop
  obtain ⟨r, hr, hra, hrb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  have hra_le : r ≤ a := Nat.le_of_dvd ha hra
  have hrz : r ≤ z - 1 := by omega
  exact hb r hr hrz hrb

private theorem mul_dvd_mul_middle {a d q b : ℕ} (hd : d ∣ a) :
    q * d ∣ a * q * b := by
  rcases hd with ⟨k, rfl⟩
  refine ⟨k * b, ?_⟩
  ac_rfl

/-! ## The unique divisor in a scaled window -/

/-- The arithmetic core of the `r = 1` construction.  The cutoff
`N / p + 1` is the first integer strictly above the upper endpoint of the
scaled divisor window. -/
theorem scaledTau_eq_one_of_isolated
    {N p a d q b : ℕ}
    (hp : 0 < p)
    (haSmall : 2 * p * a ≤ N)
    (hd : IsolatedDivisor a d dyadicSigma)
    (hq : Nat.Prime q)
    (hqd : scaledWindow N p (q * d))
    (hbpos : 0 < b)
    (hbrough : IsRough (N / p + 1) b) :
    scaledTau N p (a * q * b) = 1 := by
  rw [scaledTau_eq_one_iff]
  have ha0 : a ≠ 0 := isolatedDivisor_ne_zero hd
  have hapos : 0 < a := Nat.pos_of_ne_zero ha0
  have hdvd : d ∣ a := isolatedDivisor_dvd hd
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hapos
  have hnpos : 0 < a * q * b :=
    Nat.mul_pos (Nat.mul_pos hapos hq.pos) hbpos
  have hisolated := dyadicIsolated_unique hd
  refine ⟨q * d, ?_, ?_⟩
  · exact ⟨mul_dvd_mul_middle hdvd, hnpos.ne', hqd⟩
  · intro D hD
    rcases hD with ⟨hDdvd, -, hDlower, hDupper⟩
    have hDpos : 0 < D := by
      by_contra h
      have hD0 : D = 0 := Nat.eq_zero_of_not_pos h
      subst D
      simp at hDlower
    have hDle : D ≤ N / p := by
      apply (Nat.le_div_iff_mul_le hp).2
      simpa [mul_comm] using hDupper
    obtain ⟨c, e, hc, he, hce⟩ :=
      exists_dvd_and_dvd_of_dvd_mul (show D ∣ (a * q) * b by
        simpa [mul_assoc] using hDdvd)
    have hepos : 0 < e := by
      rw [hce] at hDpos
      exact Nat.pos_of_mul_pos_left hDpos
    have heD : e ≤ D := by
      have hcpos : 0 < c := by
        rw [hce] at hDpos
        exact Nat.pos_of_mul_pos_right hDpos
      rw [hce]
      exact Nat.le_mul_of_pos_left e hcpos
    have he_lt : e < N / p + 1 := (heD.trans hDle).trans_lt (Nat.lt_succ_self _)
    have he1 : e = 1 :=
      divisor_eq_one_of_rough_of_lt hbrough he hepos he_lt
    subst e
    simp only [mul_one] at hce
    subst c
    obtain ⟨u, v, hu, hv, huv⟩ :=
      exists_dvd_and_dvd_of_dvd_mul hc
    have hv_cases : v = 1 ∨ v = q := (Nat.dvd_prime hq).mp hv
    rcases hv_cases with hv1 | hvq
    · rw [hv1, mul_one] at huv
      subst D
      have hule : u ≤ a := Nat.le_of_dvd hapos hu
      have : 2 * p * u ≤ N := (Nat.mul_le_mul_left (2 * p) hule).trans haSmall
      omega
    · rw [hvq] at huv
      subst D
      have hpq : 0 < p * q := Nat.mul_pos hp hq.pos
      have hdu : d < 2 * u := by
        apply (Nat.mul_lt_mul_left hpq).mp
        calc
          (p * q) * d = p * (q * d) := by ac_rfl
          _ ≤ N := hqd.2
          _ < 2 * p * (u * q) := hDlower
          _ = (p * q) * (2 * u) := by ac_rfl
      have hud : u ≤ 2 * d := by
        have hult : u < 2 * d := by
          apply (Nat.mul_lt_mul_left hpq).mp
          calc
            (p * q) * u = p * (u * q) := by ac_rfl
            _ ≤ N := hDupper
            _ < 2 * p * (q * d) := hqd.1
            _ = (p * q) * (2 * d) := by ac_rfl
        exact hult.le
      have hd_self : d ∣ a ∧ d < 2 * d ∧ d ≤ 2 * d := by
        exact ⟨hdvd, by omega, by omega⟩
      have hud_eq : u = d :=
        hisolated.unique ⟨hu, hdu, hud⟩ hd_self
      subst u
      ac_rfl

/-- The constructed product is a member of the exact scaled `H1` set. -/
theorem mul_mem_scaledH1Set_of_isolated
    {N p X a d q b : ℕ}
    (hp : 0 < p)
    (haSmall : 2 * p * a ≤ N)
    (hd : IsolatedDivisor a d dyadicSigma)
    (hq : Nat.Prime q)
    (hqd : scaledWindow N p (q * d))
    (hbpos : 0 < b)
    (hbrough : IsRough (N / p + 1) b)
    (hnX : a * q * b ≤ X) :
    a * q * b ∈ scaledH1Set N p X := by
  rw [mem_scaledH1Set]
  have hapos : 0 < a := Nat.pos_of_ne_zero (isolatedDivisor_ne_zero hd)
  have hnpos : 0 < a * q * b :=
    Nat.mul_pos (Nat.mul_pos hapos hq.pos) hbpos
  refine ⟨hnpos, hnX, ?_⟩
  obtain ⟨D, hD, hDunique⟩ := scaledTau_eq_one_iff.mp
    (scaledTau_eq_one_of_isolated hp haSmall hd hq hqd hbpos hbrough)
  refine ⟨D, ⟨hD.1, hD.2.2.1, hD.2.2.2⟩, ?_⟩
  intro e he
  exact hDunique e ⟨he.1, hnpos.ne', he.2.1, he.2.2⟩

/-! ## A literal prime-interval/rough-cofactor family -/

/-- The primes in the closed natural interval `[lo, hi]`. -/
def h1PrimeInterval (lo hi : ℕ) : Finset ℕ :=
  (Finset.Icc lo hi).filter Nat.Prime

@[simp]
theorem mem_h1PrimeInterval {lo hi q : ℕ} :
    q ∈ h1PrimeInterval lo hi ↔ lo ≤ q ∧ q ≤ hi ∧ Nat.Prime q := by
  simp [h1PrimeInterval, and_assoc]

/-- The successor-indexed literal interval is exactly the prime set
occurring in the difference of two `primesLE` partial sums. -/
theorem primesLE_sdiff_eq_h1PrimeInterval (U V : ℕ) :
    Nat.primesLE V \ Nat.primesLE U = h1PrimeInterval (U + 1) V := by
  ext q
  simp only [Finset.mem_sdiff, Nat.mem_primesLE, mem_h1PrimeInterval]
  constructor
  · rintro ⟨⟨hqV, hq⟩, hnot⟩
    exact ⟨by
      by_contra h
      exact hnot ⟨by omega, hq⟩, hqV, hq⟩
  · rintro ⟨hU, hqV, hq⟩
    exact ⟨⟨hqV, hq⟩, by
      rintro ⟨hqU, -⟩
      omega⟩

/-- Reciprocal mass in a factor-two interval controls its cardinality. -/
theorem mul_primeReciprocalIntervalSum_le_card_doublePrimeInterval
    (U : ℕ) :
    (U : ℝ) * primeReciprocalIntervalSum U (2 * U) ≤
      ((h1PrimeInterval (U + 1) (2 * U)).card : ℝ) := by
  rw [primeReciprocalIntervalSum,
    primesLE_sdiff_eq_h1PrimeInterval, Finset.mul_sum]
  calc
    (∑ q ∈ h1PrimeInterval (U + 1) (2 * U),
        (U : ℝ) * (1 / (q : ℝ))) ≤
        ∑ _q ∈ h1PrimeInterval (U + 1) (2 * U), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      rw [mem_h1PrimeInterval] at hq
      have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.2.2.pos
      rw [one_div, ← div_eq_mul_inv]
      rw [div_le_one hqpos]
      exact_mod_cast (show U ≤ q by omega)
    _ = ((h1PrimeInterval (U + 1) (2 * U)).card : ℝ) := by simp

/-- Convenient conversion of a reciprocal-mass lower bound into the
corresponding prime-count lower bound. -/
theorem doublePrimeInterval_card_lower_of_reciprocal_lower
    {U : ℕ} {c : ℝ}
    (hrecip : c / Real.log U ≤ primeReciprocalIntervalSum U (2 * U)) :
    c * U / Real.log U ≤
      ((h1PrimeInterval (U + 1) (2 * U)).card : ℝ) := by
  calc
    c * U / Real.log U = (U : ℝ) * (c / Real.log U) := by ring
    _ ≤ (U : ℝ) * primeReciprocalIntervalSum U (2 * U) := by
      exact mul_le_mul_of_nonneg_left hrecip (Nat.cast_nonneg U)
    _ ≤ ((h1PrimeInterval (U + 1) (2 * U)).card : ℝ) :=
      mul_primeReciprocalIntervalSum_le_card_doublePrimeInterval U

/-- A quadruple is stored as `(((a,d),q),b)`. -/
abbrev H1Construction := ((ℕ × ℕ) × ℕ) × ℕ

/-- Ford's finite construction family.  The first two boxes contain `a` and
its isolated divisor `d`; the third coordinate is a prime from `[lo,hi]`;
the last is a cofactor sifted by `roughNumbersUpTo`.

The filter retains precisely the endpoint and size conditions used by the
arithmetic construction. -/
noncomputable def scaledH1Constructions
    (N p lo hi X : ℕ) : Finset H1Construction := by
  classical
  exact (((Finset.Icc 1 X).product (Finset.Icc 1 X)).product
      (h1PrimeInterval lo hi)).product
      (roughNumbersUpTo X (N / p + 1)) |>.filter fun t ↦
        t.1.1.1 < lo ∧
        2 * p * t.1.1.1 ≤ N ∧
        IsolatedDivisor t.1.1.1 t.1.1.2 dyadicSigma ∧
        scaledWindow N p (t.1.2 * t.1.1.2) ∧
        t.1.1.1 * t.1.2 * t.2 ≤ X

/-- The integer produced by a construction quadruple. -/
def h1ConstructionValue (t : H1Construction) : ℕ :=
  t.1.1.1 * t.1.2 * t.2

@[simp]
theorem mem_scaledH1Constructions
    {N p lo hi X a d q b : ℕ} :
    (((a, d), q), b) ∈ scaledH1Constructions N p lo hi X ↔
      1 ≤ a ∧ a ≤ X ∧ 1 ≤ d ∧ d ≤ X ∧
      lo ≤ q ∧ q ≤ hi ∧ Nat.Prime q ∧
      0 < b ∧ b ≤ X ∧ IsRough (N / p + 1) b ∧
      a < lo ∧ 2 * p * a ≤ N ∧
      IsolatedDivisor a d dyadicSigma ∧
      scaledWindow N p (q * d) ∧ a * q * b ≤ X := by
  classical
  simp [scaledH1Constructions, and_assoc]

/-- The small/prime/rough separation makes the product encoding injective.
This is the exact finite substitute for Ford's statement that every counted
integer has a unique representation `a*q*b`. -/
theorem h1ConstructionValue_injOn
    {N p lo hi X : ℕ} (hp : 0 < p) (hhi : hi ≤ N / p) :
    Set.InjOn h1ConstructionValue
      (scaledH1Constructions N p lo hi X : Set H1Construction) := by
  rintro ⟨⟨⟨a, d⟩, q⟩, b⟩ ht ⟨⟨⟨a', d'⟩, q'⟩, b'⟩ ht' heq
  change (((a, d), q), b) ∈ scaledH1Constructions N p lo hi X at ht
  change (((a', d'), q'), b') ∈ scaledH1Constructions N p lo hi X at ht'
  rw [mem_scaledH1Constructions] at ht ht'
  rcases ht with
    ⟨ha1, haX, hd1, hdX, hloq, hqhi, hqprime, hbpos, hbX, hbrough,
      halo, haSmall, hiso, hwindow, hprod⟩
  rcases ht' with
    ⟨ha1', haX', hd1', hdX', hloq', hqhi', hqprime', hbpos', hbX', hbrough',
      halo', haSmall', hiso', hwindow', hprod'⟩
  change a * q * b = a' * q' * b' at heq
  have hq_not_a' : ¬ q ∣ a' := by
    intro hqa
    have hqa_le : q ≤ a' := Nat.le_of_dvd (by omega) hqa
    omega
  have hq_lt_cut : q < N / p + 1 := by omega
  have hq_not_b' : ¬ q ∣ b' :=
    hbrough' q hqprime (by omega)
  have hq_dvd_rhs : q ∣ a' * q' * b' := by
    rw [← heq]
    exact ⟨a * b, by ac_rfl⟩
  have hq_dvd_q' : q ∣ q' := by
    have hleft : q ∣ a' * q' :=
      (hqprime.dvd_mul.mp hq_dvd_rhs).resolve_right hq_not_b'
    exact (hqprime.dvd_mul.mp hleft).resolve_left hq_not_a'
  have hqq' : q = q' := by
    rcases (Nat.dvd_prime hqprime').mp hq_dvd_q' with hq1 | h
    · exact (hqprime.ne_one hq1).elim
    · exact h
  subst q'
  have hab : a * b = a' * b' := by
    apply Nat.mul_left_cancel hqprime.pos
    simpa [mul_assoc, mul_left_comm] using heq
  have ha_cut : a < N / p + 1 := by omega
  have ha'_cut : a' < N / p + 1 := by omega
  have hcop_ab' : Nat.Coprime a b' :=
    coprime_of_lt_of_rough (by omega) ha_cut hbrough'
  have hcop_a'b : Nat.Coprime a' b :=
    coprime_of_lt_of_rough (by omega) ha'_cut hbrough
  have haa' : a = a' := by
    apply Nat.dvd_antisymm
    · apply (hcop_ab'.dvd_mul_right).mp
      exact ⟨b, hab.symm⟩
    · apply (hcop_a'b.dvd_mul_right).mp
      exact ⟨b', hab⟩
  subst a'
  have hbb' : b = b' := Nat.mul_left_cancel (by omega : 0 < a) hab
  subst b'
  have htau := scaledTau_eq_one_of_isolated hp haSmall hiso hqprime
    hwindow hbpos hbrough
  obtain ⟨D, hD, hDunique⟩ := scaledTau_eq_one_iff.mp htau
  have hdvd' : q * d' ∣ a * q * b :=
    mul_dvd_mul_middle (isolatedDivisor_dvd hiso')
  have hn0 : a * q * b ≠ 0 := by
    exact Nat.mul_ne_zero (Nat.mul_ne_zero
      (isolatedDivisor_ne_zero hiso) hqprime.ne_zero) (Nat.ne_of_gt hbpos)
  have hqd' : q * d' = D := hDunique (q * d') ⟨hdvd', hn0,
    hwindow'⟩
  have hqdvd : q * d ∣ a * q * b :=
    mul_dvd_mul_middle (isolatedDivisor_dvd hiso)
  have hqd : q * d = D := hDunique (q * d) ⟨hqdvd, hn0, hwindow⟩
  have hdd' : d = d' := by
    apply Nat.mul_left_cancel hqprime.pos
    rw [hqd, hqd']
  subst d'
  rfl

/-- Products made by the Ford construction. -/
noncomputable def scaledH1ConstructionValues
    (N p lo hi X : ℕ) : Finset ℕ :=
  (scaledH1Constructions N p lo hi X).image h1ConstructionValue

theorem scaledH1ConstructionValues_subset
    {N p lo hi X : ℕ} (hp : 0 < p) :
    scaledH1ConstructionValues N p lo hi X ⊆ scaledH1Set N p X := by
  intro n hn
  obtain ⟨⟨⟨⟨a, d⟩, q⟩, b⟩, ht, rfl⟩ := Finset.mem_image.mp hn
  rw [mem_scaledH1Constructions] at ht
  rcases ht with
    ⟨ha1, haX, hd1, hdX, hloq, hqhi, hqprime, hbpos, hbX, hbrough,
      halo, haSmall, hiso, hwindow, hprod⟩
  exact mul_mem_scaledH1Set_of_isolated hp haSmall hiso hqprime
    hwindow hbpos hbrough hprod

/-- Specialized Ford Lemma 4.1 (`r = 1`), in exact finite cardinality
form.  The left side is built from isolated-divisor data, a prime interval,
and a rough cofactor sieve; the right side is the literal exact-one-divisor
count in the scaled window. -/
theorem scaledH1Constructions_card_le
    {N p lo hi X : ℕ} (hp : 0 < p) (hhi : hi ≤ N / p) :
    (scaledH1Constructions N p lo hi X).card ≤ scaledH1 N p X := by
  have hinj := h1ConstructionValue_injOn (lo := lo) (X := X) hp hhi
  have hcard : (scaledH1ConstructionValues N p lo hi X).card =
      (scaledH1Constructions N p lo hi X).card := by
    exact Finset.card_image_iff.mpr hinj
  rw [← hcard]
  exact Finset.card_le_card (scaledH1ConstructionValues_subset hp)

/-! ## The adaptive two-prime construction

For the lower bound we do not need a lower-bound sieve for the last
cofactor.  We instead take it to be a prime.  The first prime is allowed to
depend on the isolated divisor, and the second prime is allowed to depend on
the first.  This is the form used in the polynomial application range. -/

/-- A prime at least the roughness threshold is rough. -/
theorem prime_isRough_of_threshold_le {z b : ℕ} (hb : b.Prime)
    (hzb : z ≤ b) : IsRough z b := by
  intro r hr hrz hdiv
  rcases (Nat.dvd_prime hb).mp hdiv with hr1 | hrb
  · exact hr.ne_one hr1
  · subst r
    have hbpos := hb.pos
    omega

/-- A datum is stored dependently as `⟨a, d, q, b⟩`.  The dependent
presentation lets its cardinality reduce definitionally to the iterated
prime-interval sum occurring in Ford's argument. -/
abbrev H1PrimeConstruction :=
  Σ _a : ℕ, Σ _d : ℕ, Σ _q : ℕ, ℕ

/-- The primes which put `q*d` in the exact scaled window.  The upper
endpoint `N/p` is redundant mathematically, but makes prime separation
literal in the finite set. -/
def scaledWindowPrimes (N p a d : ℕ) : Finset ℕ :=
  (h1PrimeInterval (a + 1) (N / p)).filter fun q ↦
    scaledWindow N p (q * d)

@[simp] theorem mem_scaledWindowPrimes {N p a d q : ℕ} :
    q ∈ scaledWindowPrimes N p a d ↔
      a < q ∧ q ≤ N / p ∧ q.Prime ∧ scaledWindow N p (q * d) := by
  simp [scaledWindowPrimes, and_assoc]

/-- The second-prime fiber.  Its upper endpoint is chosen so that
`a*q*b ≤ X`; its lower endpoint makes `b` larger than both the small part
and the window prime. -/
def h1SecondPrimeInterval (N p X a q : ℕ) : Finset ℕ :=
  h1PrimeInterval (N / p + 1) (X / (a * q))

@[simp] theorem mem_h1SecondPrimeInterval {N p X a q b : ℕ} :
    b ∈ h1SecondPrimeInterval N p X a q ↔
      N / p < b ∧ b ≤ X / (a * q) ∧ b.Prime := by
  simp [h1SecondPrimeInterval]

/-- In the ordinary dyadic specialization, the literal factor-two prime
interval above `y/d` lies in the exact scaled window.  The condition
`a² ≤ y` is the standard small-part restriction; since `d ∣ a`, it also
ensures that every such prime is larger than `a`. -/
theorem dyadicPrimeInterval_subset_scaledWindowPrimes
    {a d y : ℕ} (ha : a ^ 2 ≤ y)
    (hd : IsolatedDivisor a d dyadicSigma) :
    h1PrimeInterval (y / d + 1) (2 * (y / d)) ⊆
      scaledWindowPrimes (2 * y) 1 a d := by
  intro q hqmem
  rw [mem_h1PrimeInterval] at hqmem
  rcases hqmem with ⟨hqlower, hqupper, hq⟩
  have ha0 := isolatedDivisor_ne_zero hd
  have hapos : 0 < a := Nat.pos_of_ne_zero ha0
  have hdvd := isolatedDivisor_dvd hd
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hapos
  have hda : d ≤ a := Nat.le_of_dvd hapos hdvd
  have had : a * d ≤ y := by
    calc
      a * d ≤ a * a := Nat.mul_le_mul_left a hda
      _ = a ^ 2 := by ring
      _ ≤ y := ha
  have hau : a ≤ y / d := (Nat.le_div_iff_mul_le hdpos).2 had
  have hyqd : y < q * d := by
    apply (Nat.div_lt_iff_lt_mul hdpos).1
    omega
  have hqdy : q * d ≤ 2 * y := by
    calc
      q * d ≤ (2 * (y / d)) * d := Nat.mul_le_mul_right d hqupper
      _ = 2 * ((y / d) * d) := by ring
      _ ≤ 2 * y := Nat.mul_le_mul_left 2 (Nat.div_mul_le_self y d)
  rw [mem_scaledWindowPrimes]
  refine ⟨by omega, ?_, hq, ?_⟩
  · have hydiv : y / d ≤ y := Nat.div_le_self y d
    omega
  · constructor
    · simpa using hyqd
    · simpa using hqdy

/-- A factor-two prime interval based at `X/(4aq)` lies inside the adaptive
second-prime fiber as soon as its base is beyond the divisor window. -/
theorem doublePrimeInterval_subset_secondPrimeInterval
    {N p X a q : ℕ} (haq : 0 < a * q)
    (hbase : N / p ≤ X / (4 * (a * q))) :
    h1PrimeInterval (X / (4 * (a * q)) + 1)
        (2 * (X / (4 * (a * q)))) ⊆
      h1SecondPrimeInterval N p X a q := by
  intro b hbmem
  rw [mem_h1PrimeInterval] at hbmem
  rw [mem_h1SecondPrimeInterval]
  rcases hbmem with ⟨hblower, hbupper, hb⟩
  refine ⟨by omega, ?_, hb⟩
  apply (Nat.le_div_iff_mul_le haq).2
  calc
    b * (a * q) ≤ (2 * (X / (4 * (a * q)))) * (a * q) :=
      Nat.mul_le_mul_right (a * q) hbupper
    _ ≤ (4 * (a * q)) * (X / (4 * (a * q))) := by
      nlinarith
    _ ≤ X := Nat.mul_div_le X (4 * (a * q))

/-- The lower polynomial edge makes the second-prime interval start above
the dyadic divisor window.  This is the elementary band calculation used
after applying the factor-two prime estimate. -/
theorem dyadic_secondPrime_base_ge
    {M y a q : ℕ} (hy : 2 ≤ y) (ha : a ≤ y) (hq : q ≤ 2 * y)
    (ha0 : 0 < a) (hq0 : 0 < q) (hM : 8 * y ^ 3 ≤ M) :
    2 * y ≤ (M * y) / (4 * (a * q)) := by
  have haq : a * q ≤ 2 * y ^ 2 := by nlinarith
  have hsM : 8 * (a * q) ≤ M := by
    have : 16 * y ^ 2 ≤ 8 * y ^ 3 := by nlinarith
    nlinarith
  have hden : 0 < 4 * (a * q) := by positivity
  apply (Nat.le_div_iff_mul_le hden).2
  have hmul := Nat.mul_le_mul_right y hsM
  nlinarith

/-- Losing a factor two absorbs the floor in the base of the second-prime
interval. -/
theorem cast_div_eight_le_cast_div_four
    {X s : ℕ} (hs : 0 < s) (hXs : 8 * s ≤ X) :
    (X : ℝ) / (8 * s) ≤ (X / (4 * s) : ℕ) := by
  have h4s : 0 < 4 * s := by positivity
  have hk2 : 2 ≤ X / (4 * s) := by
    apply (Nat.le_div_iff_mul_le h4s).2
    nlinarith
  have hlt := Nat.lt_div_mul_add (a := X) h4s
  have hnat : X ≤ 8 * s * (X / (4 * s)) := by
    nlinarith
  have hdenR : (0 : ℝ) < 8 * s := by positivity
  apply (div_le_iff₀ hdenR).2
  have hnat' : X ≤ (X / (4 * s)) * (8 * s) := by
    simpa [mul_comm] using hnat
  exact_mod_cast hnat'

/-- On the exact application band, the logarithm of the counting cutoff is
bounded by a fixed multiple of the divisor-window logarithm. -/
theorem log_mul_le_eight_log_of_dyadic_band
    {M y : ℕ} (hy : 2 ≤ y) (hMlow : 8 * y ^ 3 ≤ M)
    (hMhigh : M ^ 7 ≤ (2 * y) ^ 24) :
    Real.log (M * y) ≤ 8 * Real.log y := by
  have hypos : 0 < y := by omega
  have hMpos : 0 < M :=
    (by positivity : 0 < 8 * y ^ 3).trans_le hMlow
  have hpowR : (M : ℝ) ^ 7 ≤ ((2 * y : ℕ) : ℝ) ^ 24 := by
    exact_mod_cast hMhigh
  have h2ypos : (0 : ℝ) < ((2 * y : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_pos (by omega : 0 < 2) hypos)
  have hlogpow : Real.log ((M : ℝ) ^ 7) ≤
      Real.log (((2 * y : ℕ) : ℝ) ^ 24) := by
    exact Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (pow_pos (by exact_mod_cast hMpos) 7))
      (Set.mem_Ioi.mpr (pow_pos h2ypos 24))
      hpowR
  rw [Real.log_pow, Real.log_pow] at hlogpow
  have hlogTwo_le : Real.log 2 ≤ Real.log y := by
    exact Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr (by norm_num))
      (Set.mem_Ioi.mpr (by exact_mod_cast hypos)) (by exact_mod_cast hy)
  have hlogY : 0 < Real.log y := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlog2y : Real.log ((2 * y : ℕ) : ℝ) ≤ 2 * Real.log y := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) (by positivity)]
    linarith
  have hlogM : 7 * Real.log M ≤ 48 * Real.log y := by
    norm_num at hlogpow
    have hlog2y' : Real.log (2 * (y : ℝ)) ≤ 2 * Real.log y := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hlog2y
    linarith
  rw [Real.log_mul (by exact_mod_cast hMpos.ne')
    (by exact_mod_cast hypos.ne')]
  nlinarith

/-- The adaptive prime family used for the lower bound. -/
noncomputable def scaledH1PrimeConstructions
    (N p X : ℕ) (A : Finset ℕ) : Finset H1PrimeConstruction := by
  classical
  exact (A.filter fun a ↦ 2 * p * a ≤ N).sigma fun a ↦
    (isolatedDivisors a dyadicSigma).sigma fun d ↦
      (scaledWindowPrimes N p a d).sigma fun q ↦
        h1SecondPrimeInterval N p X a q

@[simp] theorem mem_scaledH1PrimeConstructions
    {N p X a d q b : ℕ} {A : Finset ℕ} :
    ⟨a, ⟨d, ⟨q, b⟩⟩⟩ ∈ scaledH1PrimeConstructions N p X A ↔
      a ∈ A ∧ 2 * p * a ≤ N ∧
      IsolatedDivisor a d dyadicSigma ∧
      a < q ∧ q ≤ N / p ∧ q.Prime ∧
      scaledWindow N p (q * d) ∧
      N / p < b ∧ b ≤ X / (a * q) ∧ b.Prime := by
  classical
  simp [scaledH1PrimeConstructions, and_assoc]

/-- The integer represented by an adaptive two-prime datum. -/
def h1PrimeConstructionValue (t : H1PrimeConstruction) : ℕ :=
  t.1 * t.2.2.1 * t.2.2.2

/-- Every adaptive two-prime datum produces an integer counted by the
exact scaled `H1`. -/
theorem h1PrimeConstructionValue_mem_scaledH1Set
    {N p X : ℕ} {A : Finset ℕ} (hp : 0 < p)
    {t : H1PrimeConstruction} (ht : t ∈ scaledH1PrimeConstructions N p X A) :
    h1PrimeConstructionValue t ∈ scaledH1Set N p X := by
  rcases t with ⟨a, ⟨d, ⟨q, b⟩⟩⟩
  rw [mem_scaledH1PrimeConstructions] at ht
  rcases ht with
    ⟨haA, haSmall, hd, haq, hqtop, hq, hwindow, hbcut, hbtop, hb⟩
  have hapos : 0 < a := Nat.pos_of_ne_zero (isolatedDivisor_ne_zero hd)
  have haqpos : 0 < a * q := Nat.mul_pos hapos hq.pos
  have hnX : a * q * b ≤ X := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Nat.le_div_iff_mul_le haqpos).mp hbtop
  have hbrough : IsRough (N / p + 1) b :=
    prime_isRough_of_threshold_le hb (by omega)
  exact mul_mem_scaledH1Set_of_isolated hp haSmall hd hq hwindow hb.pos
    hbrough hnX

/-- Prime separation makes the adaptive two-prime encoding injective.
The large prime `b` is recovered first.  After it is cancelled, if `q`
divided the other small part, symmetry would force `q'` below `q` and above
it simultaneously.  Isolation then recovers `d`. -/
theorem h1PrimeConstructionValue_injOn
    {N p X : ℕ} {A : Finset ℕ} (hp : 0 < p) :
    Set.InjOn h1PrimeConstructionValue
      (scaledH1PrimeConstructions N p X A : Set H1PrimeConstruction) := by
  rintro ⟨a, ⟨d, ⟨q, b⟩⟩⟩ ht ⟨a', ⟨d', ⟨q', b'⟩⟩⟩ ht' heq
  change ⟨a, ⟨d, ⟨q, b⟩⟩⟩ ∈ scaledH1PrimeConstructions N p X A at ht
  change ⟨a', ⟨d', ⟨q', b'⟩⟩⟩ ∈ scaledH1PrimeConstructions N p X A at ht'
  rw [mem_scaledH1PrimeConstructions] at ht ht'
  rcases ht with
    ⟨haA, haSmall, hd, haq, hqtop, hq, hwindow, hbcut, hbtop, hb⟩
  rcases ht' with
    ⟨haA', haSmall', hd', haq', hqtop', hq', hwindow', hbcut', hbtop', hb'⟩
  change a * q * b = a' * q' * b' at heq
  have hb_dvd_rhs : b ∣ a' * q' * b' := by
    rw [← heq]
    exact ⟨a * q, by ac_rfl⟩
  have hb_not_a' : ¬ b ∣ a' := by
    intro h
    have hba : b ≤ a' := Nat.le_of_dvd
      (Nat.pos_of_ne_zero (isolatedDivisor_ne_zero hd')) h
    omega
  have hb_not_q' : ¬ b ∣ q' := by
    intro h
    have hbq : b ≤ q' := Nat.le_of_dvd hq'.pos h
    omega
  have hb_dvd_b' : b ∣ b' := by
    have h := hb.dvd_mul.mp hb_dvd_rhs
    rcases h with hab | hbb
    · rcases hb.dvd_mul.mp hab with hba | hbq
      · exact (hb_not_a' hba).elim
      · exact (hb_not_q' hbq).elim
    · exact hbb
  have hbb' : b = b' := by
    rcases (Nat.dvd_prime hb').mp hb_dvd_b' with hb1 | h
    · exact (hb.ne_one hb1).elim
    · exact h
  subst b'
  have haqeq : a * q = a' * q' := by
    apply Nat.mul_right_cancel hb.pos
    simpa [mul_assoc] using heq
  have hq_dvd_rhs : q ∣ a' * q' := by
    rw [← haqeq]
    exact ⟨a, by ac_rfl⟩
  have hqq' : q = q' := by
    rcases hq.dvd_mul.mp hq_dvd_rhs with hqa' | hqq'
    · have hq_lt_q' : q < q' :=
        (Nat.le_of_dvd (Nat.pos_of_ne_zero (isolatedDivisor_ne_zero hd')) hqa').trans_lt haq'
      have hq'_dvd_lhs : q' ∣ a * q := by
        rw [haqeq]
        exact ⟨a', by ac_rfl⟩
      rcases hq'.dvd_mul.mp hq'_dvd_lhs with hq'a | hq'q
      · have : q' ≤ a := Nat.le_of_dvd
          (Nat.pos_of_ne_zero (isolatedDivisor_ne_zero hd)) hq'a
        omega
      · rcases (Nat.dvd_prime hq).mp hq'q with hq'1 | h
        · exact (hq'.ne_one hq'1).elim
        · exact ((Nat.ne_of_lt hq_lt_q') h.symm).elim
    · rcases (Nat.dvd_prime hq').mp hqq' with hq1 | h
      · exact (hq.ne_one hq1).elim
      · exact h
  subst q'
  have haa' : a = a' := Nat.mul_right_cancel hq.pos haqeq
  subst a'
  have hbrough : IsRough (N / p + 1) b :=
    prime_isRough_of_threshold_le hb (by omega)
  have htau := scaledTau_eq_one_of_isolated hp haSmall hd hq hwindow hb.pos hbrough
  obtain ⟨D, hD, hDunique⟩ := scaledTau_eq_one_iff.mp htau
  have hn0 : a * q * b ≠ 0 :=
    Nat.mul_ne_zero (Nat.mul_ne_zero (isolatedDivisor_ne_zero hd) hq.ne_zero)
      hb.ne_zero
  have hqd : q * d = D := hDunique (q * d)
    ⟨mul_dvd_mul_middle (isolatedDivisor_dvd hd), hn0, hwindow⟩
  have hqd' : q * d' = D := hDunique (q * d')
    ⟨mul_dvd_mul_middle (isolatedDivisor_dvd hd'), hn0, hwindow'⟩
  have hdd' : d = d' := by
    apply Nat.mul_left_cancel hq.pos
    rw [hqd, hqd']
  subst d'
  rfl

/-- The cardinality of the adaptive construction is the literal iterated
prime-interval sum. -/
theorem card_scaledH1PrimeConstructions
    (N p X : ℕ) (A : Finset ℕ) :
    (scaledH1PrimeConstructions N p X A).card =
      ∑ a ∈ A.filter (fun a ↦ 2 * p * a ≤ N),
        ∑ d ∈ isolatedDivisors a dyadicSigma,
          ∑ q ∈ scaledWindowPrimes N p a d,
            (h1SecondPrimeInterval N p X a q).card := by
  classical
  simp [scaledH1PrimeConstructions, Finset.card_sigma]

/-- Specialized Ford Lemma 4.1 (`r=1`) with a prime final cofactor.  It is
already in the direct cross-multiplied window required by Problem 896, and
its left side is the exact finite sum to which prime-interval estimates are
applied in the polynomial range. -/
theorem scaledH1PrimeConstruction_sum_le
    {N p X : ℕ} (A : Finset ℕ) (hp : 0 < p) :
    ∑ a ∈ A.filter (fun a ↦ 2 * p * a ≤ N),
        ∑ d ∈ isolatedDivisors a dyadicSigma,
          ∑ q ∈ scaledWindowPrimes N p a d,
            (h1SecondPrimeInterval N p X a q).card ≤
      scaledH1 N p X := by
  rw [← card_scaledH1PrimeConstructions]
  let values := (scaledH1PrimeConstructions N p X A).image
    h1PrimeConstructionValue
  have hinj := h1PrimeConstructionValue_injOn (N := N) (X := X) (A := A) hp
  have hcard : values.card = (scaledH1PrimeConstructions N p X A).card := by
    exact Finset.card_image_iff.mpr hinj
  rw [← hcard]
  apply Finset.card_le_card
  intro n hn
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
  exact h1PrimeConstructionValue_mem_scaledH1Set hp ht

/-- Quantitative aggregation of the prime fibers.  Once an analytic prime
estimate supplies `C/a` constructions for every isolated divisor of `a`,
the exact finite construction gives `C` times the reciprocal weighted
isolated mass.  This theorem is deliberately stated for the direct scaled
window, so applying it to `N` and `p` introduces no floor error. -/
theorem mul_weightedIsolatedSum_le_scaledH1_of_primeFibers
    {N p X : ℕ} (A : Finset ℕ) (hp : 0 < p) (C : ℝ)
    (haSmall : ∀ a ∈ A, 2 * p * a ≤ N)
    (hprime : ∀ a ∈ A, ∀ d ∈ isolatedDivisors a dyadicSigma,
      C / (a : ℝ) ≤
        ((∑ q ∈ scaledWindowPrimes N p a d,
          (h1SecondPrimeInterval N p X a q).card : ℕ) : ℝ)) :
    C * weightedIsolatedSum A dyadicSigma ≤
      (scaledH1 N p X : ℝ) := by
  classical
  have hfilter : A.filter (fun a ↦ 2 * p * a ≤ N) = A := by
    exact Finset.filter_eq_self.mpr haSmall
  have hnat := scaledH1PrimeConstruction_sum_le (N := N) (p := p) (X := X) A hp
  rw [hfilter] at hnat
  have hreal :
      (((∑ a ∈ A, ∑ d ∈ isolatedDivisors a dyadicSigma,
          ∑ q ∈ scaledWindowPrimes N p a d,
            (h1SecondPrimeInterval N p X a q).card : ℕ)) : ℝ) ≤
        (scaledH1 N p X : ℝ) := by
    exact_mod_cast hnat
  calc
    C * weightedIsolatedSum A dyadicSigma =
        ∑ a ∈ A, ∑ _d ∈ isolatedDivisors a dyadicSigma,
          C / (a : ℝ) := by
      unfold weightedIsolatedSum I
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ ∑ a ∈ A, ∑ _d ∈ isolatedDivisors a dyadicSigma,
        (((∑ q ∈ scaledWindowPrimes N p a _d,
          (h1SecondPrimeInterval N p X a q).card : ℕ)) : ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro d hd
      exact hprime a ha d hd
    _ = (((∑ a ∈ A, ∑ d ∈ isolatedDivisors a dyadicSigma,
          ∑ q ∈ scaledWindowPrimes N p a d,
            (h1SecondPrimeInterval N p X a q).card : ℕ)) : ℝ) := by
      push_cast
      rfl
    _ ≤ (scaledH1 N p X : ℝ) := hreal

/-- The specialized `r = 1` lower bound in the exact polynomial band used
by Problem 896.  The final cofactor is prime.  The constant is deliberately
coarse: its purpose is to absorb the two natural floors and the comparison
`log (M*y) ≤ 8 log y` while retaining the required `X/log² y` scale. -/
theorem exists_dyadicBand_weightedIsolatedSum_le_scaledH1 :
    ∃ c : ℝ, 0 < c ∧ ∃ Y₀ : ℕ, ∀ (M y : ℕ) (A : Finset ℕ),
      Y₀ ≤ y → 8 * y ^ 3 ≤ M → M ^ 7 ≤ (2 * y) ^ 24 →
      (∀ a ∈ A, a ^ 2 ≤ y) →
      c * (M * y : ℕ) / Real.log y ^ 2 *
          weightedIsolatedSum A dyadicSigma ≤
        (scaledH1 (2 * y) 1 (M * y) : ℝ) := by
  obtain ⟨Uq₀, hqmass⟩ :=
    eventually_one_sixteenth_div_log_le_primeReciprocalIntervalSum
  obtain ⟨Ub₀, hbcard⟩ :=
    eventually_one_eighth_mul_div_log_le_primeIntervalCard
  let T := max 4 (max Uq₀ Ub₀)
  refine ⟨1 / 8192, by norm_num, max 2 (T ^ 2), ?_⟩
  intro M y A hY hMlow hMhigh haSq
  have hy : 2 ≤ y := (le_max_left 2 (T ^ 2)).trans hY
  have hTsq : T ^ 2 ≤ y := (le_max_right 2 (T ^ 2)).trans hY
  have hypos : 0 < y := by omega
  have hMpos : 0 < M :=
    (by positivity : 0 < 8 * y ^ 3).trans_le hMlow
  have hXpos : 0 < M * y := Nat.mul_pos hMpos hypos
  have hlogy : 0 < Real.log y :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogX : 0 < Real.log (M * y) :=
    Real.log_pos (by exact_mod_cast (show 1 < M * y by
      exact (show 1 < y by omega).trans_le (Nat.le_mul_of_pos_left y hMpos)))
  have hlogCompare := log_mul_le_eight_log_of_dyadic_band hy hMlow hMhigh
  let C : ℝ := (M * y : ℕ) / (8192 * Real.log y ^ 2)
  have haSmall : ∀ a ∈ A, 2 * 1 * a ≤ 2 * y := by
    intro a ha
    have ha2 := haSq a ha
    have hay : a ≤ y := by nlinarith [sq_nonneg (a : ℝ)]
    omega
  have hprime : ∀ a ∈ A, ∀ d ∈ isolatedDivisors a dyadicSigma,
      C / (a : ℝ) ≤
        ((∑ q ∈ scaledWindowPrimes (2 * y) 1 a d,
          (h1SecondPrimeInterval (2 * y) 1 (M * y) a q).card : ℕ) : ℝ) := by
    intro a ha d hdmem
    have hd := mem_isolatedDivisors.mp hdmem
    have ha0 := isolatedDivisor_ne_zero hd
    have hapos : 0 < a := Nat.pos_of_ne_zero ha0
    have hdvd := isolatedDivisor_dvd hd
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hapos
    have hda : d ≤ a := Nat.le_of_dvd hapos hdvd
    have ha2 := haSq a ha
    have hay : a ≤ y := by nlinarith [sq_nonneg (a : ℝ)]
    have hd2 : d ^ 2 ≤ y := (Nat.pow_le_pow_left hda 2).trans ha2
    have hTd : T * d ≤ y := by nlinarith [sq_nonneg ((T : ℝ) - d)]
    have hTU : T ≤ y / d := (Nat.le_div_iff_mul_le hdpos).2 hTd
    have hUq₀ : Uq₀ ≤ y / d :=
      (le_max_left Uq₀ Ub₀).trans ((le_max_right 4 (max Uq₀ Ub₀)).trans hTU)
    have hUpos : 0 < y / d := Nat.div_pos (hda.trans hay) hdpos
    have hlogU : 0 < Real.log ((y / d : ℕ) : ℝ) := by
      have hU4 : 4 ≤ y / d := (le_max_left 4 (max Uq₀ Ub₀)).trans hTU
      exact Real.log_pos (by exact_mod_cast (show 1 < y / d by omega))
    let Q := h1PrimeInterval (y / d + 1) (2 * (y / d))
    have hQsub : Q ⊆ scaledWindowPrimes (2 * y) 1 a d :=
      dyadicPrimeInterval_subset_scaledWindowPrimes ha2 hd
    have hmassQ : (1 / 16 : ℝ) / Real.log y ≤
        ∑ q ∈ Q, (1 : ℝ) / q := by
      have hrec := hqmass (y / d) hUq₀
      have hUle : y / d ≤ y := Nat.div_le_self y d
      have hlogUle : Real.log ((y / d : ℕ) : ℝ) ≤ Real.log y := by
        exact Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr (by exact_mod_cast hUpos))
          (Set.mem_Ioi.mpr (by exact_mod_cast hypos)) (by exact_mod_cast hUle)
      calc
        (1 / 16 : ℝ) / Real.log y ≤
            (1 / 16 : ℝ) / Real.log ((y / d : ℕ) : ℝ) := by
          exact div_le_div_of_nonneg_left (by norm_num) hlogU hlogUle
        _ ≤ primeReciprocalIntervalSum (y / d) (2 * (y / d)) := hrec
        _ = ∑ q ∈ Q, (1 : ℝ) / q := by
          unfold primeReciprocalIntervalSum
          rw [primesLE_sdiff_eq_h1PrimeInterval]
    have hqTerm : ∀ q ∈ Q,
        (M * y : ℕ) /
            (64 * (a : ℝ) * q * Real.log (M * y)) ≤
          ((h1SecondPrimeInterval (2 * y) 1 (M * y) a q).card : ℝ) := by
      intro q hqQ
      have hqdata := (mem_h1PrimeInterval.mp hqQ)
      have hqprime := hqdata.2.2
      have hqtopU := hqdata.2.1
      have hqtop : q ≤ 2 * y := by
        have := Nat.div_le_self y d
        omega
      have haqpos : 0 < a * q := Nat.mul_pos hapos hqprime.pos
      let V := (M * y) / (4 * (a * q))
      have hbase : 2 * y ≤ V :=
        dyadic_secondPrime_base_ge hy hay hqtop hapos hqprime.pos hMlow
      have hTy : T ≤ y := by nlinarith
      have hUb₀ : Ub₀ ≤ V :=
        (le_max_right Uq₀ Ub₀).trans
          ((le_max_right 4 (max Uq₀ Ub₀)).trans (hTy.trans (by omega)))
      have hVpos : 0 < V := by omega
      have hlogV : 0 < Real.log V :=
        Real.log_pos (by exact_mod_cast (show 1 < V by omega))
      have hVleX : V ≤ M * y := Nat.div_le_self (M * y) (4 * (a * q))
      have hlogVle : Real.log V ≤ Real.log (M * y) := by
        exact Real.strictMonoOn_log.monotoneOn
          (Set.mem_Ioi.mpr (by exact_mod_cast hVpos))
          (Set.mem_Ioi.mpr (by exact_mod_cast hXpos)) (by exact_mod_cast hVleX)
      have h8aq : 8 * (a * q) ≤ M * y := by
        have h4aq : 0 < 4 * (a * q) := by positivity
        have := (Nat.le_div_iff_mul_le h4aq).1 hbase
        nlinarith
      have hVfloor : (((M * y : ℕ) : ℝ) /
          (8 * (a : ℝ) * (q : ℝ))) ≤ (V : ℝ) := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using
          (cast_div_eight_le_cast_div_four haqpos h8aq)
      have hbstd := hbcard V hUb₀
      rw [primesLE_sdiff_eq_h1PrimeInterval] at hbstd
      have hbsub := doublePrimeInterval_subset_secondPrimeInterval
        (N := 2 * y) (p := 1) (X := M * y) haqpos (by simpa [V] using hbase)
      calc
        (M * y : ℕ) / (64 * (a : ℝ) * q * Real.log (M * y)) =
            (1 / 8 : ℝ) * ((M * y : ℕ) / (8 * (a * q))) /
              Real.log (M * y) := by ring
        _ ≤ (1 / 8 : ℝ) * V / Real.log (M * y) := by
          apply div_le_div_of_nonneg_right _ hlogX.le
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          simpa only [mul_assoc] using hVfloor
        _ ≤ (1 / 8 : ℝ) * V / Real.log V := by
          exact div_le_div_of_nonneg_left (by positivity) hlogV hlogVle
        _ ≤ ((h1PrimeInterval (V + 1) (2 * V)).card : ℝ) := hbstd
        _ ≤ ((h1SecondPrimeInterval (2 * y) 1 (M * y) a q).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hbsub
    have hsumQ :
        (M * y : ℕ) /
            (64 * (a : ℝ) * Real.log (M * y)) *
              ((1 / 16 : ℝ) / Real.log y) ≤
          ∑ q ∈ Q,
            ((h1SecondPrimeInterval (2 * y) 1 (M * y) a q).card : ℝ) := by
      calc
        (M * y : ℕ) / (64 * (a : ℝ) * Real.log (M * y)) *
              ((1 / 16 : ℝ) / Real.log y) ≤
            (M * y : ℕ) / (64 * (a : ℝ) * Real.log (M * y)) *
              (∑ q ∈ Q, (1 : ℝ) / q) := by
          gcongr
        _ = ∑ q ∈ Q,
            (M * y : ℕ) /
              (64 * (a : ℝ) * q * Real.log (M * y)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q hq
          ring
        _ ≤ ∑ q ∈ Q,
            ((h1SecondPrimeInterval (2 * y) 1 (M * y) a q).card : ℝ) := by
          exact Finset.sum_le_sum fun q hq ↦ hqTerm q hq
    calc
      C / (a : ℝ) ≤
          (M * y : ℕ) /
            (64 * (a : ℝ) * Real.log (M * y)) *
              ((1 / 16 : ℝ) / Real.log y) := by
        dsimp [C]
        have hdena : (0 : ℝ) < a := by exact_mod_cast hapos
        field_simp
        nlinarith
      _ ≤ ∑ q ∈ Q,
          ((h1SecondPrimeInterval (2 * y) 1 (M * y) a q).card : ℝ) := hsumQ
      _ ≤ ∑ q ∈ scaledWindowPrimes (2 * y) 1 a d,
          ((h1SecondPrimeInterval (2 * y) 1 (M * y) a q).card : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hQsub
        intro q hq hnot
        positivity
      _ = ((∑ q ∈ scaledWindowPrimes (2 * y) 1 a d,
          (h1SecondPrimeInterval (2 * y) 1 (M * y) a q).card : ℕ) : ℝ) := by
        push_cast
        rfl
  have h := mul_weightedIsolatedSum_le_scaledH1_of_primeFibers
    (N := 2 * y) (p := 1) (X := M * y) A (by omega) C haSmall hprime
  dsimp [C] at h
  convert h using 1
  ring

end Erdos896.Ford
