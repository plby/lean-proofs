/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Choose.Factorization
import ErdosProblems.Erdos48.PowerSieveFinalAssembly
import ErdosProblems.Erdos48.ShiftedSmoothBadRoots

/-!
# Erdős Problem 48

Ford, Luca, and Pomerance proved that the Euler totient and sum-of-divisors
functions have infinitely many common values.  This file formalizes their
argument and then packages the result in the statement used by the Formal
Conjectures project.
-/

open scoped ArithmeticFunction.sigma BigOperators

namespace Erdos48

/-- The squarefree kernel of a natural number. -/
def radical (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

lemma prime_dvd_radical {p n : ℕ} (hp : p.Prime) (hpn : p ∣ n) (hn : n ≠ 0) :
    p ∣ radical n := by
  exact Finset.dvd_prod_of_mem id ((Nat.mem_primeFactors).2 ⟨hp, hpn, hn⟩)

/-- Multiplying by a number supported on primes already present multiplies
Euler's totient by that number. -/
lemma totient_mul_eq_left_mul_totient {a b : ℕ}
    (h : ∀ p : ℕ, p.Prime → p ∣ a → p ∣ b) :
    (a * b).totient = a * b.totient := by
  induction a using induction_on_primes with
  | zero => simp
  | one => simp
  | prime_mul p a hp ih =>
      rw [mul_assoc]
      rw [Nat.totient_mul_of_prime_of_dvd hp]
      · rw [ih]
        · simp [mul_assoc]
        · intro q hq hqa
          exact h q hq (dvd_mul_of_dvd_right hqa p)
      · exact dvd_mul_of_dvd_right (h p hp (dvd_mul_right p a)) a

/-- The elementary realization criterion used by Ford--Luca--Pomerance:
if `φ(rad v) ∣ v`, then `v` is a totient. -/
lemma totient_realization {v : ℕ} (hv : (radical v).totient ∣ v) :
    ((v / (radical v).totient) * radical v).totient = v := by
  by_cases hv0 : v = 0
  · simp [hv0, radical]
  have hdvd : v / (radical v).totient ∣ v := Nat.div_dvd_of_dvd hv
  rw [totient_mul_eq_left_mul_totient]
  · exact Nat.div_mul_cancel hv
  · intro p hp hpd
    exact prime_dvd_radical hp (dvd_trans hpd hdvd) hv0

/-- The divisor sum of a prime. -/
lemma sigma_one_prime {p : ℕ} (hp : p.Prime) : σ 1 p = p + 1 := by
  simpa [Nat.add_comm] using
    (ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) hp)

/-- On a squarefree product of primes, `σ` is the product of the shifted
primes. -/
lemma sigma_prime_product (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    σ 1 (∏ p ∈ s, p) = ∏ p ∈ s, (p + 1) := by
  rw [ArithmeticFunction.isMultiplicative_sigma.map_prod_of_prime s hs]
  exact Finset.prod_congr rfl fun p hp ↦ sigma_one_prime (hs p hp)

/-- Natural numbers which occur both as a totient and as a divisor sum. -/
def CommonValue : Set ℕ :=
  {v | (∃ n : ℕ, n.totient = v) ∧ ∃ m : ℕ, σ 1 m = v}

/-- The product of the shifted primes in a finite set. -/
def shiftedPrimeProduct (s : Finset ℕ) : ℕ := ∏ p ∈ s, (p + 1)

/-- The squarefree product which realizes `shiftedPrimeProduct s` as a
divisor sum. -/
def primeProduct (s : Finset ℕ) : ℕ := ∏ p ∈ s, p

lemma sigma_primeProduct (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    σ 1 (primeProduct s) = shiftedPrimeProduct s := by
  exact sigma_prime_product s hs

/-- A shifted-prime product satisfying the FLP divisibility certificate is
a common value of `φ` and `σ`. -/
lemma shiftedPrimeProduct_mem_commonValue (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime)
    (hcert : (radical (shiftedPrimeProduct s)).totient ∣ shiftedPrimeProduct s) :
    shiftedPrimeProduct s ∈ CommonValue := by
  refine ⟨⟨(shiftedPrimeProduct s /
      (radical (shiftedPrimeProduct s)).totient) *
        radical (shiftedPrimeProduct s), totient_realization hcert⟩, ?_⟩
  exact ⟨primeProduct s, sigma_primeProduct s hs⟩

lemma shiftedPrimeProduct_pos (s : Finset ℕ) : 0 < shiftedPrimeProduct s := by
  exact Finset.prod_pos fun p _ ↦ Nat.succ_pos p

lemma radical_pos (n : ℕ) : 0 < radical n := by
  exact Finset.prod_pos fun _ hp ↦ (Nat.prime_of_mem_primeFactors hp).pos

/-- Euler's product formula specialized to the squarefree kernel. -/
lemma totient_radical_eq (v : ℕ) :
    (radical v).totient = ∏ p ∈ v.primeFactors, (p - 1) := by
  rw [Nat.totient_eq_div_primeFactors_mul]
  rw [show (radical v).primeFactors = v.primeFactors by
    exact Nat.primeFactors_prod_primeFactors v]
  rw [show ∏ p ∈ v.primeFactors, p = radical v by rfl]
  rw [Nat.div_self (radical_pos v)]
  simp

/-- The product of the predecessors of distinct primes bounded by `u`
divides `u!`.  Distinctness is essential here: the predecessors form a
subset of `1, ..., u`. -/
lemma prod_pred_dvd_factorial (s : Finset ℕ) (u : ℕ)
    (hprime : ∀ p ∈ s, p.Prime) (hs : ∀ p ∈ s, p ≤ u) :
    (∏ p ∈ s, (p - 1)) ∣ Nat.factorial u := by
  let t := s.image (fun p ↦ p - 1)
  have hinj : Set.InjOn (fun p : ℕ ↦ p - 1) s := by
    intro p hp q hq hpq
    have hpTwo := (hprime p hp).two_le
    have hqTwo := (hprime q hq).two_le
    change p - 1 = q - 1 at hpq
    calc
      p = (p - 1) + 1 := (Nat.sub_add_cancel (by omega)).symm
      _ = (q - 1) + 1 := congrArg (fun n ↦ n + 1) hpq
      _ = q := Nat.sub_add_cancel (by omega)
  have htSub : t ⊆ Finset.Ico 1 (u + 1) := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    simp only [Finset.mem_Ico]
    constructor
    · have := (hprime p hp).two_le
      omega
    · have := hs p hp
      omega
  have hprodEq : (∏ p ∈ s, (p - 1)) = ∏ n ∈ t, n := by
    dsimp [t]
    rw [Finset.prod_image]
    exact hinj
  rw [hprodEq]
  have hsubDvd :
      (∏ n ∈ t, n) ∣ ∏ n ∈ Finset.Ico 1 (u + 1), n := by
    exact Finset.prod_dvd_prod_of_subset t (Finset.Ico 1 (u + 1))
      (fun n : ℕ ↦ n) htSub
  simpa only [Finset.prod_Ico_id_eq_factorial] using hsubDvd

/-- If all prime divisors of `v` are at most `u`, the totient of its
squarefree kernel divides `u!`. -/
lemma radical_totient_dvd_factorial {v u : ℕ}
    (h : ∀ q : ℕ, q.Prime → q ∣ v → q ≤ u) :
    (radical v).totient ∣ Nat.factorial u := by
  rw [totient_radical_eq]
  apply prod_pred_dvd_factorial
  · intro q hq
    exact Nat.prime_of_mem_primeFactors hq
  · intro q hq
    exact h q (Nat.prime_of_mem_primeFactors hq)
      ((Nat.mem_primeFactors.mp hq).2.1)

/-- Every selected shifted prime divisible by `q` contributes at least one
to the `q`-adic valuation of their product. -/
lemma card_filter_dvd_le_factorization (s : Finset ℕ) {q : ℕ}
    (hq : q.Prime) :
    (s.filter fun p ↦ q ∣ p + 1).card ≤
      (shiftedPrimeProduct s).factorization q := by
  induction s using Finset.induction with
  | empty => simp [shiftedPrimeProduct]
  | @insert a s ha ih =>
      have haPos : a + 1 ≠ 0 := by omega
      have hsPos : shiftedPrimeProduct s ≠ 0 :=
        (shiftedPrimeProduct_pos s).ne'
      rw [show shiftedPrimeProduct (insert a s) =
        (a + 1) * shiftedPrimeProduct s by
          simp [shiftedPrimeProduct, ha]]
      rw [Nat.factorization_mul haPos hsPos]
      simp only [Finsupp.coe_add, Pi.add_apply]
      by_cases hqa : q ∣ a + 1
      · have hfactor : 1 ≤ (a + 1).factorization q :=
          (hq.dvd_iff_one_le_factorization haPos).mp hqa
        simp [Finset.filter_insert, ha, hqa]
        omega
      · simp [Finset.filter_insert, hqa]
        omega

/-- Divisibility can be checked only at prime coordinates of the
factorization. -/
lemma dvd_of_factorization_le_on_primes {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ q : ℕ, q.Prime → a.factorization q ≤ b.factorization q) :
    a ∣ b := by
  apply (Nat.factorization_le_iff_dvd ha hb).mp
  intro q
  by_cases hq : q.Prime
  · exact h q hq
  · rw [Nat.factorization_eq_zero_of_not_prime a hq]
    exact Nat.zero_le _

/-- Legendre's estimate plus a shifted-prime count converts the analytic
lower bounds directly into the factorial divisibility used by the finite
assembly. -/
lemma factorial_dvd_shiftedPrimeProduct_of_counts (s : Finset ℕ) (u : ℕ)
    (hcount : ∀ q : ℕ, q.Prime →
      u / (q - 1) ≤ (s.filter fun p ↦ q ∣ p + 1).card) :
    Nat.factorial u ∣ shiftedPrimeProduct s := by
  apply dvd_of_factorization_le_on_primes
  · exact Nat.factorial_ne_zero u
  · exact (shiftedPrimeProduct_pos s).ne'
  · intro q hq
    exact (Nat.factorization_factorial_le_div_pred hq u).trans
      ((hcount q hq).trans (card_filter_dvd_le_factorization s hq))

/-- Factorization-coordinate form of the FLP realization certificate. -/
lemma totient_radical_dvd_of_factorization_le {v : ℕ} (hv : v ≠ 0)
    (h : ∀ q : ℕ, q.Prime →
      (radical v).totient.factorization q ≤ v.factorization q) :
    (radical v).totient ∣ v := by
  apply dvd_of_factorization_le_on_primes
  · exact (Nat.totient_pos.mpr (radical_pos v)).ne'
  · exact hv
  · exact h

/-- Omitting one member from a finite set produces pairwise distinct shifted
products. -/
lemma erase_shiftedPrimeProduct_injective (s : Finset ℕ) :
    Function.Injective
      (fun p : {p // p ∈ s} ↦ shiftedPrimeProduct (s.erase p)) := by
  intro p q hpq
  apply Subtype.ext
  change shiftedPrimeProduct (s.erase (p : ℕ)) =
    shiftedPrimeProduct (s.erase (q : ℕ)) at hpq
  have hpTotal := Finset.prod_erase_mul s (fun r : ℕ ↦ r + 1) p.2
  have hqTotal := Finset.prod_erase_mul s (fun r : ℕ ↦ r + 1) q.2
  have hmul :
      shiftedPrimeProduct (s.erase p) * (p + 1) =
        shiftedPrimeProduct (s.erase p) * (q + 1) := by
    calc
      shiftedPrimeProduct (s.erase p) * (p + 1) = shiftedPrimeProduct s := hpTotal
      _ = shiftedPrimeProduct (s.erase q) * (q + 1) := hqTotal.symm
      _ = shiftedPrimeProduct (s.erase p) * (q + 1) := by rw [hpq]
  have hadd : (p : ℕ) + 1 = (q : ℕ) + 1 :=
    Nat.mul_left_cancel (shiftedPrimeProduct_pos (s.erase p)) hmul
  omega

/-- A finite prime set is FLP-admissible if every product obtained by
omitting one prime satisfies the totient-realization certificate. -/
def FLPAdmissible (s : Finset ℕ) : Prop :=
  (∀ p ∈ s, p.Prime) ∧
    ∀ p ∈ s,
      (radical (shiftedPrimeProduct (s.erase p))).totient ∣
        shiftedPrimeProduct (s.erase p)

/-- The exact finite data delivered by one FLP good scale.  The smoothness
condition bounds the radical.  The excluded set is upward closed along prime
chains and avoided by every shifted prime; outside it, the uniform count
dominates Legendre's bound even after any one selected prime is omitted. -/
structure FLPGoodData (K : ℕ) where
  primes : Finset ℕ
  smoothBound : ℕ
  excluded : Set ℕ
  card_ge : K ≤ primes.card
  isPrime : ∀ p ∈ primes, p.Prime
  smooth : ∀ p ∈ primes, ∀ q : ℕ, q.Prime → q ∣ p + 1 → q ≤ smoothBound
  excluded_upward : ∀ q t : ℕ, q ∈ excluded → q.Prime → t.Prime →
    q ∣ t - 1 → t ∈ excluded
  avoids_excluded : ∀ p ∈ primes, ∀ q : ℕ, q.Prime → q ∣ p + 1 →
    q ∉ excluded
  count : ∀ p ∈ primes, ∀ q : ℕ, q.Prime → q ∉ excluded →
    q ≤ smoothBound →
    smoothBound / (q - 1) ≤
      ((primes.erase p).filter fun r ↦ q ∣ r + 1).card

/-- Package the pre-erasure analytic count into `FLPGoodData`.  Reserving
one extra shifted prime makes the count uniform after deleting any chosen
member. -/
def FLPGoodData.of_raw_counts {K u : ℕ} {E : Set ℕ} {s : Finset ℕ}
    (hcard : K ≤ s.card)
    (hprime : ∀ p ∈ s, p.Prime)
    (hsmooth : ∀ p ∈ s, ∀ q : ℕ, q.Prime → q ∣ p + 1 → q ≤ u)
    (hupward : ∀ q t : ℕ, q ∈ E → q.Prime → t.Prime → q ∣ t - 1 → t ∈ E)
    (havoid : ∀ p ∈ s, ∀ q : ℕ, q.Prime → q ∣ p + 1 → q ∉ E)
    (hcount : ∀ q : ℕ, q.Prime → q ∉ E → q ≤ u →
      u / (q - 1) + 1 ≤ (s.filter fun p ↦ q ∣ p + 1).card) :
    FLPGoodData K := by
  refine
    { primes := s
      smoothBound := u
      excluded := E
      card_ge := hcard
      isPrime := hprime
      smooth := hsmooth
      excluded_upward := hupward
      avoids_excluded := havoid
      count := ?_ }
  intro p hp q hq hqE hqu
  rw [Finset.filter_erase]
  exact (Nat.le_sub_of_add_le (hcount q hq hqE hqu)).trans
    Finset.pred_card_le_card_erase

/-- Finite good-branch assembly in factorial form.  Smoothness bounds every
prime divisor of an omitted shifted product by `u`; the analytic lower
bounds are consumed only through the assertion that the product contains
all of `u!`. -/
lemma flpAdmissible_of_factorial (s : Finset ℕ) (u : ℕ)
    (hsPrime : ∀ p ∈ s, p.Prime)
    (hsSmooth : ∀ p ∈ s, ∀ q : ℕ, q.Prime → q ∣ p + 1 → q ≤ u)
    (hfactorial : ∀ p ∈ s,
      Nat.factorial u ∣ shiftedPrimeProduct (s.erase p)) :
    FLPAdmissible s := by
  refine ⟨hsPrime, ?_⟩
  intro p hp
  apply (radical_totient_dvd_factorial ?_).trans (hfactorial p hp)
  intro q hq hqv
  change q ∣ ∏ r ∈ s.erase p, (r + 1) at hqv
  obtain ⟨r, hr, hqr⟩ := (hq.prime.dvd_finsetProd_iff
    (fun r : ℕ ↦ r + 1)).mp hqv
  exact hsSmooth r (Finset.mem_of_mem_erase hr) q hq hqr

lemma FLPGoodData.admissible {K : ℕ} (d : FLPGoodData K) :
    FLPAdmissible d.primes := by
  refine ⟨d.isPrime, ?_⟩
  intro p hp
  let v := shiftedPrimeProduct (d.primes.erase p)
  have hvPos : 0 < v := shiftedPrimeProduct_pos _
  have hsmooth : ∀ q : ℕ, q.Prime → q ∣ v → q ≤ d.smoothBound := by
    intro q hq hqv
    change q ∣ ∏ r ∈ d.primes.erase p, (r + 1) at hqv
    obtain ⟨r, hr, hqr⟩ := (hq.prime.dvd_finsetProd_iff
      (fun r : ℕ ↦ r + 1)).mp hqv
    exact d.smooth r (Finset.mem_of_mem_erase hr) q hq hqr
  have htotFac : (radical v).totient ∣ Nat.factorial d.smoothBound :=
    radical_totient_dvd_factorial hsmooth
  apply totient_radical_dvd_of_factorization_le hvPos.ne'
  intro q hq
  by_cases hqExcluded : q ∈ d.excluded
  · have hqNotDvd : ¬q ∣ (radical v).totient := by
      intro hqDvd
      rw [totient_radical_eq] at hqDvd
      obtain ⟨t, ht, hqt⟩ := (hq.prime.dvd_finsetProd_iff
        (fun t : ℕ ↦ t - 1)).mp hqDvd
      have htPrime := Nat.prime_of_mem_primeFactors ht
      have htDvdV := (Nat.mem_primeFactors.mp ht).2.1
      change t ∣ ∏ r ∈ d.primes.erase p, (r + 1) at htDvdV
      obtain ⟨r, hr, htr⟩ := (htPrime.prime.dvd_finsetProd_iff
        (fun r : ℕ ↦ r + 1)).mp htDvdV
      exact (d.avoids_excluded r (Finset.mem_of_mem_erase hr) t htPrime htr)
        (d.excluded_upward q t hqExcluded hq htPrime hqt)
    rw [Nat.factorization_eq_zero_of_not_dvd hqNotDvd]
    exact Nat.zero_le _
  · have hfacLe :
        (radical v).totient.factorization q ≤
          (Nat.factorial d.smoothBound).factorization q :=
      (Nat.factorization_le_iff_dvd
        (Nat.totient_pos.mpr (radical_pos v)).ne'
        (Nat.factorial_ne_zero d.smoothBound)).2 htotFac q
    by_cases hqu : q ≤ d.smoothBound
    · exact hfacLe.trans <|
        (Nat.factorization_factorial_le_div_pred hq d.smoothBound).trans <|
          (d.count p hp q hq hqExcluded hqu).trans <|
            card_filter_dvd_le_factorization (d.primes.erase p) hq
    · have hqNotDvd : ¬q ∣ Nat.factorial d.smoothBound := by
        rw [hq.dvd_factorial]
        omega
      rw [Nat.factorization_eq_zero_of_not_dvd hqNotDvd] at hfacLe
      exact hfacLe.trans (Nat.zero_le _)

lemma commonValue_of_mem_FLPAdmissible {s : Finset ℕ}
    (hs : FLPAdmissible s) {p : ℕ} (hp : p ∈ s) :
    shiftedPrimeProduct (s.erase p) ∈ CommonValue := by
  apply shiftedPrimeProduct_mem_commonValue
  · intro q hq
    exact hs.1 q (Finset.mem_of_mem_erase hq)
  · exact hs.2 p hp

/-- Unbounded finite FLP-admissible sets imply infinitely many common
values.  This is the finite-to-infinite compactness step used in the good
branch of the analytic proof. -/
lemma infinite_commonValues_of_unbounded_admissible
    (h : ∀ K : ℕ, ∃ s : Finset ℕ, K ≤ s.card ∧ FLPAdmissible s) :
    CommonValue.Infinite := by
  by_contra hfinite'
  have hfinite : CommonValue.Finite := not_not.mp hfinite'
  let _ : Fintype CommonValue := hfinite.fintype
  obtain ⟨s, hsCard, hs⟩ := h (Fintype.card CommonValue + 1)
  let f : {p // p ∈ s} → CommonValue := fun p ↦
    ⟨shiftedPrimeProduct (s.erase p),
      commonValue_of_mem_FLPAdmissible hs p.2⟩
  have hf : Function.Injective f := by
    intro p q hpq
    apply erase_shiftedPrimeProduct_injective s
    exact congrArg Subtype.val hpq
  have hle := Fintype.card_le_of_injective f hf
  have hcardSubtype : Fintype.card {p // p ∈ s} = s.card := by simp
  rw [hcardSubtype] at hle
  omega

lemma infinite_commonValues_of_unbounded_goodData
    (h : ∀ K : ℕ, Nonempty (FLPGoodData K)) :
    CommonValue.Infinite := by
  apply infinite_commonValues_of_unbounded_admissible
  intro K
  obtain ⟨d⟩ := h K
  exact ⟨d.primes, d.card_ge, d.admissible⟩

/-- Assemble one FLP good scale from the raw shifted-smooth-prime counts and
the reciprocal mass of a finite bad-root prime-chain closure.  This is the
exact interface between the analytic estimates and `FLPGoodData`. -/
noncomputable def FLPGoodData.of_smooth_selection
    {K x u : ℕ} {bad : Finset ℕ}
    (_hbad : ∀ q ∈ bad, q.Prime ∧ q ≤ u)
    (hcard : K ≤ (avoidingShiftedDivisors
      (smoothShiftedPrimes x u) (primeChainClosureTargets u bad)).card)
    (hraw : ∀ q : ℕ, q.Prime →
      q ∉ primeChainClosure (bad : Set ℕ) →
      q ≤ u →
      ((u / (q - 1) + 1 : ℕ) : ℝ) +
          ((x + 1 : ℕ) : ℝ) / (q : ℝ) *
            ∑ t ∈ primeChainClosureTargets u bad, (t : ℝ)⁻¹ ≤
        ((((smoothShiftedPrimes x u).filter
          fun p ↦ q ∣ p + 1).card : ℕ) : ℝ)) :
    FLPGoodData K := by
  classical
  let T := primeChainClosureTargets u bad
  let s := avoidingShiftedDivisors (smoothShiftedPrimes x u) T
  apply FLPGoodData.of_raw_counts
      (u := u) (E := primeChainClosure (bad : Set ℕ)) (s := s)
  · simpa only [s, T] using hcard
  · intro p hp
    have hpData := mem_avoidingShiftedDivisors.mp hp
    exact (mem_smoothShiftedPrimes.mp hpData.1).2.1
  · intro p hp q hq hqp
    have hpData := mem_avoidingShiftedDivisors.mp hp
    have hsmooth := (mem_smoothShiftedPrimes.mp hpData.1).2.2
    exact (smoothAtMost_iff_prime_dvd (by omega : p + 1 ≠ 0)).mp hsmooth q hq hqp
  · intro q t hqClosure hq ht hqt
    exact mem_primeChainClosure_of_step hqClosure ⟨hq, ht, hqt⟩
  · intro p hp q hq hqp hqClosure
    have hpData := mem_avoidingShiftedDivisors.mp hp
    have hsmooth := (mem_smoothShiftedPrimes.mp hpData.1).2.2
    have hqu : q ≤ u :=
      (smoothAtMost_iff_prime_dvd (by omega : p + 1 ≠ 0)).mp hsmooth q hq hqp
    obtain ⟨_, r, hrBad, hrq⟩ := hqClosure
    have hrFin : r ∈ bad := hrBad
    have hqT : q ∈ T := by
      change q ∈ primeChainClosureTargets u bad
      rw [mem_primeChainClosureTargets]
      exact ⟨r, hrFin, hqu, hq, hrq⟩
    exact hpData.2 q hqT hqp
  · intro q hq hqClosure hqu
    have hqT : q ∉ T := by
      intro hqT
      change q ∈ primeChainClosureTargets u bad at hqT
      rw [mem_primeChainClosureTargets] at hqT
      obtain ⟨r, hrBad, hqu, hqPrime, hrq⟩ := hqT
      exact hqClosure ⟨hqPrime, r, hrBad, hrq⟩
    apply le_card_avoiding_filter_of_real_harmonic_loss_le
      (A := smoothShiftedPrimes x u) (T := T) (x := x)
      (q := q) (N := u / (q - 1) + 1)
    · intro p hp
      exact (mem_smoothShiftedPrimes.mp hp).1
    · exact hq
    · intro t ht
      change t ∈ primeChainClosureTargets u bad at ht
      rw [mem_primeChainClosureTargets] at ht
      obtain ⟨r, hrBad, htu, htPrime, hrt⟩ := ht
      exact htPrime
    · exact hqT
    · simpa only [T] using hraw q hq hqClosure hqu

/-- The exact analytic scale record converts without loss into the finite
admissibility data consumed by the arithmetic core. -/
noncomputable def FLPAnalyticScale.toGoodData {K : ℕ}
    (d : FLPAnalyticScale K) : FLPGoodData K :=
  FLPGoodData.of_smooth_selection d.badRoots_prime_bound d.usable_card
    d.raw_counts

lemma infinite_commonValues_of_unbounded_analyticScales
    (h : ∀ K : ℕ, Nonempty (FLPAnalyticScale K)) :
    CommonValue.Infinite := by
  apply infinite_commonValues_of_unbounded_goodData
  intro K
  obtain ⟨d⟩ := h K
  exact ⟨d.toGoodData⟩

/-- A prime which begins a twin-prime pair. -/
def TwinPrimeStart (p : ℕ) : Prop := p.Prime ∧ (p + 2).Prime

lemma twinPrime_commonValue {p : ℕ} (hp : TwinPrimeStart p) :
    p + 1 ∈ CommonValue := by
  refine ⟨⟨p + 2, ?_⟩, ⟨p, sigma_one_prime hp.1⟩⟩
  rw [Nat.totient_prime hp.2]
  omega

/-- The standard one-line conditional implication from the twin-prime
conjecture.  FLP's exceptional-zero branch eventually feeds this lemma. -/
lemma infinite_commonValues_of_infinite_twinPrimes
    (h : {p : ℕ | TwinPrimeStart p}.Infinite) :
    CommonValue.Infinite := by
  let _ : Infinite {p : ℕ // TwinPrimeStart p} := h.to_subtype
  let f : {p : ℕ // TwinPrimeStart p} → ℕ := fun p ↦ p + 1
  have hf : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    have : (p : ℕ) + 1 = (q : ℕ) + 1 := hpq
    omega
  exact (Set.infinite_range_of_injective hf).mono fun v hv ↦ by
    obtain ⟨p, rfl⟩ := hv
    exact twinPrime_commonValue p.2

/-- The common finite endpoint of FLP's analytic dichotomy.  At every
requested cardinality the exceptional branch supplies that many twin-prime
starts, or the good branch supplies an admissible shifted-prime set. -/
lemma infinite_commonValues_of_unbounded_FLP_dichotomy
    (h : ∀ K : ℕ,
      (∃ s : Finset ℕ, K ≤ s.card ∧ ∀ p ∈ s, TwinPrimeStart p) ∨
      (∃ s : Finset ℕ, K ≤ s.card ∧ FLPAdmissible s)) :
    CommonValue.Infinite := by
  by_contra hfinite'
  have hfinite : CommonValue.Finite := not_not.mp hfinite'
  let _ : Fintype CommonValue := hfinite.fintype
  obtain hTwin | hGood := h (Fintype.card CommonValue + 1)
  · obtain ⟨s, hsCard, hsTwin⟩ := hTwin
    let f : {p // p ∈ s} → CommonValue := fun p ↦
      ⟨p + 1, twinPrime_commonValue (hsTwin p p.2)⟩
    have hf : Function.Injective f := by
      intro p q hpq
      apply Subtype.ext
      have hval : (p : ℕ) + 1 = (q : ℕ) + 1 :=
        congrArg Subtype.val hpq
      omega
    have hle := Fintype.card_le_of_injective f hf
    have hcardSubtype : Fintype.card {p // p ∈ s} = s.card := by simp
    rw [hcardSubtype] at hle
    omega
  · obtain ⟨s, hsCard, hs⟩ := hGood
    let f : {p // p ∈ s} → CommonValue := fun p ↦
      ⟨shiftedPrimeProduct (s.erase p),
        commonValue_of_mem_FLPAdmissible hs p.2⟩
    have hf : Function.Injective f := by
      intro p q hpq
      apply erase_shiftedPrimeProduct_injective s
      exact congrArg Subtype.val hpq
    have hle := Fintype.card_le_of_injective f hf
    have hcardSubtype : Fintype.card {p // p ∈ s} = s.card := by simp
    rw [hcardSubtype] at hle
    omega

lemma infinite_solution_pairs_of_infinite_commonValues
    (h : CommonValue.Infinite) :
    {(n, m) : ℕ × ℕ | n.totient = σ 1 m}.Infinite := by
  let _ : Infinite CommonValue := h.to_subtype
  choose tn htn using fun v : CommonValue ↦ v.2.1
  choose sm hsm using fun v : CommonValue ↦ v.2.2
  let pair : CommonValue → ℕ × ℕ := fun v ↦ (tn v, sm v)
  have hpair : Function.Injective pair := by
    intro v w hvw
    apply Subtype.ext
    have hleft : tn v = tn w := congrArg Prod.fst hvw
    calc
      (v : ℕ) = (tn v).totient := (htn v).symm
      _ = (tn w).totient := congrArg Nat.totient hleft
      _ = (w : ℕ) := htn w
  have himage : (Set.range pair).Infinite := Set.infinite_range_of_injective hpair
  apply himage.mono
  rintro z ⟨v, rfl⟩
  exact htn v |>.trans (hsm v).symm

end Erdos48

/-- Erdős Problem 48: Euler's totient and the sum-of-divisors function have
infinitely many common values. -/
theorem erdos_48 :
    answer(True) ↔ {(n, m) : ℕ × ℕ | n.totient = σ 1 m}.Infinite := by
  constructor
  · intro _
    exact Erdos48.infinite_solution_pairs_of_infinite_commonValues
      (Erdos48.infinite_commonValues_of_unbounded_analyticScales
        Erdos48.all_nonempty_FLPAnalyticScale)
  · intro _
    trivial

#print axioms erdos_48
