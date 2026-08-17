/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos586.Core

/-!
# Prime stages for Erdős Problem 586

The distortion sieve exposes prime coordinates in increasing order.  The
paper numbers primes from one, so this file uses the same convention:
`stagePrime 1 = 2`, `stagePrime 2 = 3`, and `stagePrime 3 = 5`.  Stage zero is
reserved for the empty product and no primality assertion is made there.

For a positive period `Q`, `stageExponent Q r` is the exponent of the stage
prime in `Q`, and `partialPeriod Q r` is the product of the complete prime
powers in `Q` whose primes have appeared by stage `r`.  The deliberately
generous finite horizon `stageHorizon Q = max 10000 Q` contains every prime
factor of `Q`; consequently the partial period at that horizon is exactly
`Q`.  This gives the finite stopping statement needed by the sieve.
-/

open scoped BigOperators

namespace Erdos586

noncomputable section

/-! ## One-indexed primes and stage exponents -/

/-- The prime exposed at stage `r`, numbered from one.  Stage zero is a
dummy stage and happens to have the same value as stage one; all theorems
using primality or order therefore assume `0 < r`. -/
def stagePrime (r : ℕ) : ℕ := Nat.nth Nat.Prime (r - 1)

@[simp] lemma stagePrime_one : stagePrime 1 = 2 := by
  simp [stagePrime, Nat.nth_prime_zero_eq_two]

@[simp] lemma stagePrime_two : stagePrime 2 = 3 := by
  simp [stagePrime, Nat.nth_prime_one_eq_three]

@[simp] lemma stagePrime_three : stagePrime 3 = 5 := by
  simp [stagePrime, Nat.nth_prime_two_eq_five]

lemma stagePrime_prime {r : ℕ} (_hr : 0 < r) : Nat.Prime (stagePrime r) := by
  simpa [stagePrime] using Nat.prime_nth_prime (r - 1)

lemma stagePrime_two_le {r : ℕ} (hr : 0 < r) : 2 ≤ stagePrime r :=
  (stagePrime_prime hr).two_le

lemma stagePrime_pos {r : ℕ} (hr : 0 < r) : 0 < stagePrime r :=
  (stagePrime_prime hr).pos

lemma stagePrime_one_lt {r : ℕ} (hr : 0 < r) : 1 < stagePrime r :=
  (stagePrime_prime hr).one_lt

lemma stagePrime_strictMonoOn :
    StrictMonoOn stagePrime (Set.Ici 1) := by
  intro a ha b hb hab
  have ha' : a - 1 < b - 1 := Nat.sub_lt_sub_right ha hab
  exact Nat.nth_strictMono Nat.infinite_setOfPred_prime ha'

lemma stagePrime_mono {a b : ℕ} (_ha : 0 < a) (hab : a ≤ b) :
    stagePrime a ≤ stagePrime b := by
  exact (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone
    (Nat.sub_le_sub_right hab 1)

/-- The exponent of the stage prime in `Q`. -/
def stageExponent (Q r : ℕ) : ℕ := Q.factorization (stagePrime r)

lemma stagePrime_pow_stageExponent_dvd {Q r : ℕ} (hQ : Q ≠ 0)
    (hr : 0 < r) :
    stagePrime r ^ stageExponent Q r ∣ Q := by
  rw [(stagePrime_prime hr).pow_dvd_iff_le_factorization hQ]
  exact le_rfl

/-! ## Partial periods -/

/-- Prime factors of `Q` which have appeared by stage `r`. -/
def activePrimeFactors (Q r : ℕ) : Finset ℕ :=
  if r = 0 then ∅ else Q.primeFactors.filter (fun p => p ≤ stagePrime r)

/-- The part of `Q` supported on the prime coordinates exposed by stage `r`.
Each active coordinate occurs to its full exponent in `Q`. -/
def partialPeriod (Q r : ℕ) : ℕ :=
  ∏ p ∈ activePrimeFactors Q r, p ^ Q.factorization p

@[simp] lemma activePrimeFactors_zero (Q : ℕ) : activePrimeFactors Q 0 = ∅ := by
  simp [activePrimeFactors]

@[simp] lemma partialPeriod_zero (Q : ℕ) : partialPeriod Q 0 = 1 := by
  simp [partialPeriod]

lemma activePrimeFactors_subset (Q r : ℕ) :
    activePrimeFactors Q r ⊆ Q.primeFactors := by
  intro p hp
  simp only [activePrimeFactors] at hp
  split at hp
  · simp at hp
  · exact (Finset.mem_filter.mp hp).1

lemma mem_activePrimeFactors_iff {Q r p : ℕ} (hr : 0 < r) :
    p ∈ activePrimeFactors Q r ↔ p ∈ Q.primeFactors ∧ p ≤ stagePrime r := by
  simp [activePrimeFactors, hr.ne']

lemma activePrimeFactors_mono {Q a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    activePrimeFactors Q a ⊆ activePrimeFactors Q b := by
  intro p hp
  rw [mem_activePrimeFactors_iff ha] at hp
  rw [mem_activePrimeFactors_iff (ha.trans_le hab)]
  exact ⟨hp.1, hp.2.trans (stagePrime_mono ha hab)⟩

lemma partialPeriod_dvd (Q r : ℕ) (hQ : Q ≠ 0) :
    partialPeriod Q r ∣ Q := by
  calc
    partialPeriod Q r ∣ ∏ p ∈ Q.primeFactors, p ^ Q.factorization p :=
      Finset.prod_dvd_prod_of_subset
        (activePrimeFactors Q r) Q.primeFactors
        (fun p => p ^ Q.factorization p) (activePrimeFactors_subset Q r)
    _ = Q := (Nat.prod_primeFactors_pow_factorization hQ).symm

lemma partialPeriod_pos (Q r : ℕ) : 0 < partialPeriod Q r := by
  apply Finset.prod_pos
  intro p hp
  exact pow_pos
    (Nat.pos_of_mem_primeFactors (activePrimeFactors_subset Q r hp)) _

lemma primeFactors_partialPeriod_subset_active (Q r : ℕ) :
    (partialPeriod Q r).primeFactors ⊆ activePrimeFactors Q r := by
  intro p hp
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpdvd : p ∣ partialPeriod Q r := Nat.dvd_of_mem_primeFactors hp
  rw [partialPeriod, hpprime.prime.dvd_finsetProd_iff] at hpdvd
  obtain ⟨q, hq, hpq⟩ := hpdvd
  have hqprime : q.Prime :=
    Nat.prime_of_mem_primeFactors (activePrimeFactors_subset Q r hq)
  have hpq' : p ∣ q := hpprime.dvd_of_dvd_pow hpq
  have heq : p = q :=
    ((hqprime.dvd_iff_eq hpprime.ne_one).mp hpq').symm
  simpa [heq] using hq

lemma partialPeriod_mono_dvd {Q a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    partialPeriod Q a ∣ partialPeriod Q b := by
  exact Finset.prod_dvd_prod_of_subset
    (activePrimeFactors Q a) (activePrimeFactors Q b)
    (fun p => p ^ Q.factorization p) (activePrimeFactors_mono ha hab)

/-- A fixed finite stage beyond both the analytic cutoff and the numerical
size of the period. -/
def stageHorizon (Q : ℕ) : ℕ := max 10000 Q

lemma stageHorizon_pos (Q : ℕ) : 0 < stageHorizon Q := by
  simp [stageHorizon]

lemma le_stageHorizon (Q : ℕ) : Q ≤ stageHorizon Q := by
  exact le_max_right _ _

lemma stageHorizon_le_stagePrime (Q : ℕ) :
    stageHorizon Q ≤ stagePrime (stageHorizon Q) := by
  have hN : 0 < stageHorizon Q := stageHorizon_pos Q
  have h := Nat.add_two_le_nth_prime (stageHorizon Q - 1)
  rw [show stageHorizon Q - 1 + 2 = stageHorizon Q + 1 by omega] at h
  exact h.trans' (Nat.le_succ _)

lemma activePrimeFactors_horizon (Q : ℕ) :
    activePrimeFactors Q (stageHorizon Q) = Q.primeFactors := by
  apply Finset.Subset.antisymm (activePrimeFactors_subset Q (stageHorizon Q))
  intro p hp
  rw [mem_activePrimeFactors_iff (stageHorizon_pos Q)]
  refine ⟨hp, ?_⟩
  exact (Nat.le_of_mem_primeFactors hp).trans
    ((le_stageHorizon Q).trans (stageHorizon_le_stagePrime Q))

/-- At the finite horizon every prime-power coordinate of a positive period
has appeared. -/
theorem partialPeriod_horizon {Q : ℕ} (hQ : Q ≠ 0) :
    partialPeriod Q (stageHorizon Q) = Q := by
  rw [partialPeriod, activePrimeFactors_horizon]
  exact (Nat.prod_primeFactors_pow_factorization hQ).symm

/-- Every divisor of `Q` is processed by the finite horizon. -/
theorem dvd_partialPeriod_horizon {Q d : ℕ} (hQ : Q ≠ 0) (hd : d ∣ Q) :
    d ∣ partialPeriod Q (stageHorizon Q) := by
  simpa [partialPeriod_horizon hQ] using hd

/-- Every modulus in a covering family is processed by the horizon of its
common period. -/
theorem modulus_dvd_partialPeriod_horizon (A : CoveringFamily)
    (i : Fin A.length) :
    (A.get i).modulus ∣
      partialPeriod (commonPeriod A) (stageHorizon (commonPeriod A)) := by
  exact dvd_partialPeriod_horizon (commonPeriod_pos A).ne'
    (modulus_dvd_commonPeriod A i)

lemma dvd_partialPeriod_of_primeFactors_subset {Q d r : ℕ}
    (hQ : Q ≠ 0) (hd0 : d ≠ 0) (hdQ : d ∣ Q)
    (hsupport : d.primeFactors ⊆ activePrimeFactors Q r) :
    d ∣ partialPeriod Q r := by
  rw [Nat.prod_primeFactors_pow_factorization hd0]
  calc
    (∏ p ∈ d.primeFactors, p ^ d.factorization p) ∣
        ∏ p ∈ d.primeFactors, p ^ Q.factorization p := by
      exact Finset.prod_dvd_prod_of_dvd
        (fun p => p ^ d.factorization p)
        (fun p => p ^ Q.factorization p) fun p hp =>
          Nat.pow_dvd_pow p
            (((Nat.factorization_le_iff_dvd hd0 hQ).2 hdQ) p)
    _ ∣ ∏ p ∈ activePrimeFactors Q r, p ^ Q.factorization p :=
      Finset.prod_dvd_prod_of_subset d.primeFactors
        (activePrimeFactors Q r) (fun p => p ^ Q.factorization p) hsupport
    _ = partialPeriod Q r := by rfl

/-! ## The moduli newly assigned to a stage -/

/-- Remove the complete `stagePrime r`-power from `d`. -/
def oldPart (d r : ℕ) : ℕ :=
  d / stagePrime r ^ d.factorization (stagePrime r)

/-- A divisor `d` is assigned to stage `r` when its stage-prime exponent is
positive and the remaining factor has already appeared.  The explicit old
part condition is the form consumed by the fibre decomposition in the sieve.
-/
def IsNewModulus (Q r d : ℕ) : Prop :=
  0 < r ∧ d ∣ Q ∧
    0 < d.factorization (stagePrime r) ∧
    oldPart d r ∣ partialPeriod Q (r - 1)

lemma newModulus_stageExponent_pos {Q r d : ℕ}
    (hnew : IsNewModulus Q r d) :
    0 < d.factorization (stagePrime r) := hnew.2.2.1

lemma newModulus_stageExponent_le {Q r d : ℕ} (hQ : Q ≠ 0)
    (hnew : IsNewModulus Q r d) :
    d.factorization (stagePrime r) ≤ stageExponent Q r := by
  have hd0 : d ≠ 0 := by
    intro hd
    subst d
    simpa using hnew.2.2.1
  exact ((Nat.factorization_le_iff_dvd hd0 hQ).2 hnew.2.1) (stagePrime r)

lemma oldPart_not_dvd_stagePrime {d r : ℕ} (hr : 0 < r) (hd : d ≠ 0) :
    ¬ stagePrime r ∣ oldPart d r := by
  simpa [oldPart] using Nat.not_dvd_ordCompl (stagePrime_prime hr) hd

/-- The exact `m * p_r^j` form of a modulus newly assigned to stage `r`.
This is the interface used by the bad-fibre and moment calculations. -/
theorem newModulus_eq_oldPart_mul_pow {Q r d : ℕ} (hQ : Q ≠ 0)
    (hnew : IsNewModulus Q r d) :
    d = oldPart d r * stagePrime r ^ d.factorization (stagePrime r) ∧
      oldPart d r ∣ partialPeriod Q (r - 1) ∧
      0 < d.factorization (stagePrime r) ∧
      d.factorization (stagePrime r) ≤ stageExponent Q r := by
  refine ⟨?_, hnew.2.2.2, hnew.2.2.1,
    newModulus_stageExponent_le hQ hnew⟩
  rw [mul_comm]
  simpa [oldPart] using
    (Nat.ordProj_mul_ordCompl_eq_self d (stagePrime r)).symm

/-- Existential version of `newModulus_eq_oldPart_mul_pow`, convenient when
the old part and exponent should receive local names. -/
theorem newModulus_exists_oldPart_pow {Q r d : ℕ} (hQ : Q ≠ 0)
    (hnew : IsNewModulus Q r d) :
    ∃ m j : ℕ,
      m ∣ partialPeriod Q (r - 1) ∧
      0 < j ∧ j ≤ stageExponent Q r ∧
      ¬ stagePrime r ∣ m ∧
      d = m * stagePrime r ^ j := by
  refine ⟨oldPart d r, d.factorization (stagePrime r), hnew.2.2.2,
    hnew.2.2.1, newModulus_stageExponent_le hQ hnew, ?_, ?_⟩
  · have hd0 : d ≠ 0 := by
      intro hd
      subst d
      simpa using hnew.2.2.1
    exact oldPart_not_dvd_stagePrime hnew.1 hd0
  · exact (newModulus_eq_oldPart_mul_pow hQ hnew).1

/-! ## Canonical largest-prime assignment -/

/-- The largest prime factor of a nontrivial natural number.  The default
value is used only when the prime-factor finset is empty. -/
noncomputable def largestPrimeFactor (d : ℕ) : ℕ :=
  if h : d.primeFactors.Nonempty then d.primeFactors.max' h else 1

lemma primeFactors_nonempty_of_one_lt {d : ℕ} (hd : 1 < d) :
    d.primeFactors.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  have := Nat.primeFactors_eq_empty.mp hempty
  omega

lemma largestPrimeFactor_mem {d : ℕ} (hd : 1 < d) :
    largestPrimeFactor d ∈ d.primeFactors := by
  classical
  have hne := primeFactors_nonempty_of_one_lt hd
  simpa [largestPrimeFactor, hne] using
    Finset.max'_mem d.primeFactors hne

lemma largestPrimeFactor_prime {d : ℕ} (hd : 1 < d) :
    Nat.Prime (largestPrimeFactor d) :=
  Nat.prime_of_mem_primeFactors (largestPrimeFactor_mem hd)

lemma largestPrimeFactor_dvd {d : ℕ} (hd : 1 < d) :
    largestPrimeFactor d ∣ d :=
  Nat.dvd_of_mem_primeFactors (largestPrimeFactor_mem hd)

lemma primeFactor_le_largestPrimeFactor {d q : ℕ} (hd : 1 < d)
    (hq : q ∈ d.primeFactors) : q ≤ largestPrimeFactor d := by
  classical
  have hne := primeFactors_nonempty_of_one_lt hd
  simpa [largestPrimeFactor, hne] using
    Finset.le_max' d.primeFactors q hq

/-- The one-indexed stage occupied by a prime. -/
def primeStage (p : ℕ) : ℕ := Nat.count Nat.Prime p + 1

lemma primeStage_pos (p : ℕ) : 0 < primeStage p := by
  simp [primeStage]

lemma stagePrime_primeStage {p : ℕ} (hp : p.Prime) :
    stagePrime (primeStage p) = p := by
  simp [stagePrime, primeStage, Nat.nth_count hp]

lemma primeStage_stagePrime {r : ℕ} (_hr : 0 < r) :
    primeStage (stagePrime r) = r := by
  unfold primeStage stagePrime
  rw [Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime]
  omega

private lemma prime_mem_active_before_primeStage {Q p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hqQ : q ∣ Q) (hQ : Q ≠ 0)
    (hqp : q < p) :
    q ∈ activePrimeFactors Q (primeStage p - 1) := by
  have hqmem : q ∈ Q.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hq, hqQ, hQ⟩
  have hp_nth : Nat.nth Nat.Prime (Nat.count Nat.Prime p) = p :=
    Nat.nth_count hp
  have hq_nth : Nat.nth Nat.Prime (Nat.count Nat.Prime q) = q :=
    Nat.nth_count hq
  have hindex : Nat.count Nat.Prime q < Nat.count Nat.Prime p := by
    apply (Nat.nth_strictMono Nat.infinite_setOfPred_prime).lt_iff_lt.mp
    simpa [hq_nth, hp_nth] using hqp
  cases hcp : Nat.count Nat.Prime p with
  | zero =>
      have hp2 : p = 2 := by
        rw [← hp_nth, hcp, Nat.nth_prime_zero_eq_two]
      have : 2 ≤ q := hq.two_le
      omega
  | succ k =>
      have hq_le : q ≤ Nat.nth Nat.Prime k := by
        rw [← hq_nth]
        exact (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone
          (by omega)
      rw [mem_activePrimeFactors_iff]
      · refine ⟨hqmem, ?_⟩
        simpa [stagePrime, primeStage, hcp] using hq_le
      · simp [primeStage, hcp]

private lemma stagePrime_not_mem_active_previous {Q r : ℕ} (hr : 0 < r) :
    stagePrime r ∉ activePrimeFactors Q (r - 1) := by
  by_cases hprev : 0 < r - 1
  · intro hmem
    have hle := (mem_activePrimeFactors_iff hprev).mp hmem |>.2
    have hlt : stagePrime (r - 1) < stagePrime r := by
      unfold stagePrime
      apply Nat.nth_strictMono Nat.infinite_setOfPred_prime
      omega
    omega
  · have hz : r - 1 = 0 := Nat.eq_zero_of_not_pos hprev
    simp [hz]

private lemma activePrimeFactors_insert_stage {Q r : ℕ} (hr : 0 < r)
    (hmem : stagePrime r ∈ Q.primeFactors) :
    activePrimeFactors Q r =
      insert (stagePrime r) (activePrimeFactors Q (r - 1)) := by
  apply Finset.Subset.antisymm
  · intro q hq
    have hqr := (mem_activePrimeFactors_iff hr).mp hq
    by_cases heq : q = stagePrime r
    · simpa [heq]
    · apply Finset.mem_insert_of_mem
      have hqprime := Nat.prime_of_mem_primeFactors hqr.1
      have hqQ := Nat.dvd_of_mem_primeFactors hqr.1
      have hlt : q < stagePrime r := lt_of_le_of_ne hqr.2 heq
      have hbefore := prime_mem_active_before_primeStage
        (stagePrime_prime hr) hqprime hqQ
        (Nat.mem_primeFactors.mp hmem).2.2 hlt
      rwa [primeStage_stagePrime hr] at hbefore
  · intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hqold
    · exact (mem_activePrimeFactors_iff hr).mpr ⟨hmem, le_rfl⟩
    · by_cases hprev : 0 < r - 1
      · exact activePrimeFactors_mono hprev (Nat.sub_le r 1) hqold
      · have hz : r - 1 = 0 := Nat.eq_zero_of_not_pos hprev
        simpa [hz] using hqold

private lemma activePrimeFactors_eq_previous_of_stage_not_mem {Q r : ℕ}
    (hr : 0 < r) (hmem : stagePrime r ∉ Q.primeFactors) :
    activePrimeFactors Q r = activePrimeFactors Q (r - 1) := by
  apply Finset.Subset.antisymm
  · intro q hq
    have hqr := (mem_activePrimeFactors_iff hr).mp hq
    have hne : q ≠ stagePrime r := by
      intro heq
      exact hmem (heq ▸ hqr.1)
    have hlt : q < stagePrime r := lt_of_le_of_ne hqr.2 hne
    have hbefore := prime_mem_active_before_primeStage
      (stagePrime_prime hr) (Nat.prime_of_mem_primeFactors hqr.1)
      (Nat.dvd_of_mem_primeFactors hqr.1)
      (Nat.mem_primeFactors.mp hqr.1).2.2 hlt
    rwa [primeStage_stagePrime hr] at hbefore
  · intro q hq
    by_cases hprev : 0 < r - 1
    · exact activePrimeFactors_mono hprev (Nat.sub_le r 1) hq
    · have hz : r - 1 = 0 := Nat.eq_zero_of_not_pos hprev
      simpa [hz] using hq

/-- Successive partial periods differ by exactly the full power of the new
stage prime. -/
theorem partialPeriod_stage {Q r : ℕ} (hr : 0 < r) :
    partialPeriod Q r = partialPeriod Q (r - 1) *
      stagePrime r ^ stageExponent Q r := by
  by_cases hmem : stagePrime r ∈ Q.primeFactors
  · rw [partialPeriod, activePrimeFactors_insert_stage hr hmem,
      Finset.prod_insert (stagePrime_not_mem_active_previous hr)]
    simp only [partialPeriod, stageExponent]
    ac_rfl
  · have hfactor : Q.factorization (stagePrime r) = 0 := by
      apply Finsupp.notMem_support_iff.mp
      simpa using hmem
    rw [partialPeriod, activePrimeFactors_eq_previous_of_stage_not_mem hr hmem,
      partialPeriod, stageExponent, hfactor, pow_zero, mul_one]

lemma partialPeriod_previous_coprime_stagePower {Q r : ℕ} (hr : 0 < r) :
    Nat.Coprime (partialPeriod Q (r - 1))
      (stagePrime r ^ stageExponent Q r) := by
  apply (stagePrime_prime hr).coprime_pow_of_not_dvd
  intro hdvd
  rw [partialPeriod, (stagePrime_prime hr).prime.dvd_finsetProd_iff] at hdvd
  obtain ⟨q, hq, hpq⟩ := hdvd
  have hqprime : q.Prime :=
    Nat.prime_of_mem_primeFactors (activePrimeFactors_subset Q (r - 1) hq)
  have hpq' : stagePrime r ∣ q :=
    (stagePrime_prime hr).dvd_of_dvd_pow hpq
  have heq : stagePrime r = q :=
    ((hqprime.dvd_iff_eq (stagePrime_prime hr).ne_one).mp hpq').symm
  subst q
  exact stagePrime_not_mem_active_previous hr hq

/-- CRT coordinates for a single prime stage. -/
noncomputable def stageCRT (Q r : ℕ) (hr : 0 < r) :
    ZMod (partialPeriod Q r) ≃+*
      ZMod (partialPeriod Q (r - 1)) ×
        ZMod (stagePrime r ^ stageExponent Q r) :=
  (ZMod.ringEquivCongr (partialPeriod_stage hr)).trans
    (ZMod.chineseRemainder (partialPeriod_previous_coprime_stagePower hr))

/-- Zero-indexed wrapper for the recursive law used by the sieve. -/
theorem partialPeriod_succ (Q r : ℕ) :
    partialPeriod Q (r + 1) = partialPeriod Q r *
      stagePrime (r + 1) ^ stageExponent Q (r + 1) := by
  simpa using partialPeriod_stage (Q := Q) (r := r + 1) (by omega)

/-- The old and new coordinates at the successor stage are coprime. -/
lemma partialPeriod_coprime_stagePow (Q r : ℕ) :
    Nat.Coprime (partialPeriod Q r)
      (stagePrime (r + 1) ^ stageExponent Q (r + 1)) := by
  simpa using partialPeriod_previous_coprime_stagePower
    (Q := Q) (r := r + 1) (by omega)

/-- The equality transport from the stage modulus to the product modulus. -/
noncomputable def stageCRTInput (Q r : ℕ) :
    ZMod (partialPeriod Q (r + 1)) →
      ZMod (partialPeriod Q r *
        stagePrime (r + 1) ^ stageExponent Q (r + 1)) :=
  ZMod.ringEquivCongr (partialPeriod_succ Q r)

/-- CRT coordinates in the successor-indexed form consumed by the recursive
probability construction. -/
noncomputable def stageCRTRingEquiv (Q r : ℕ) :
    ZMod (partialPeriod Q (r + 1)) ≃+*
      ZMod (partialPeriod Q r) ×
        ZMod (stagePrime (r + 1) ^ stageExponent Q (r + 1)) :=
  (ZMod.ringEquivCongr (partialPeriod_succ Q r)).trans
    (ZMod.chineseRemainder (partialPeriod_coprime_stagePow Q r))

@[simp] lemma stageCRTRingEquiv_fst (Q r : ℕ)
    (x : ZMod (partialPeriod Q (r + 1))) :
    (stageCRTRingEquiv Q r x).1 =
      ZMod.castHom (Nat.dvd_mul_right (partialPeriod Q r)
        (stagePrime (r + 1) ^ stageExponent Q (r + 1)))
        (ZMod (partialPeriod Q r)) (stageCRTInput Q r x) := by
  simp [stageCRTRingEquiv, stageCRTInput, ZMod.chineseRemainder]

@[simp] lemma stageCRTRingEquiv_snd (Q r : ℕ)
    (x : ZMod (partialPeriod Q (r + 1))) :
    (stageCRTRingEquiv Q r x).2 =
      ZMod.castHom (Nat.dvd_mul_left
        (stagePrime (r + 1) ^ stageExponent Q (r + 1))
        (partialPeriod Q r))
        (ZMod (stagePrime (r + 1) ^ stageExponent Q (r + 1)))
        (stageCRTInput Q r x) := by
  simp [stageCRTRingEquiv, stageCRTInput, ZMod.chineseRemainder]

/-- Every nontrivial divisor of a positive period is assigned to exactly the
stage of its largest prime factor (existence is the part needed by the sieve).
The stage is automatically no later than the finite horizon. -/
theorem divisor_isNewModulus_at_largestPrimeStage {Q d : ℕ}
    (hQ : Q ≠ 0) (hdQ : d ∣ Q) (hd : 1 < d) :
    IsNewModulus Q (primeStage (largestPrimeFactor d)) d := by
  let p := largestPrimeFactor d
  have hp : p.Prime := largestPrimeFactor_prime hd
  have hpd : p ∣ d := largestPrimeFactor_dvd hd
  have hd0 : d ≠ 0 := by omega
  have hstage : stagePrime (primeStage p) = p := stagePrime_primeStage hp
  refine ⟨primeStage_pos p, hdQ, ?_, ?_⟩
  · rw [hstage]
    exact hp.factorization_pos_of_dvd hd0 hpd
  · have hm0 : oldPart d (primeStage p) ≠ 0 := by
      rw [oldPart, hstage]
      exact (Nat.ordCompl_pos p hd0).ne'
    have hmd : oldPart d (primeStage p) ∣ d := by
      rw [oldPart, hstage]
      exact Nat.ordCompl_dvd d p
    apply dvd_partialPeriod_of_primeFactors_subset hQ hm0 (hmd.trans hdQ)
    intro q hqm
    have hq : q.Prime := Nat.prime_of_mem_primeFactors hqm
    have hqd : q ∣ d :=
      (Nat.dvd_of_mem_primeFactors hqm).trans hmd
    have hqmemd : q ∈ d.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hq, hqd, hd0⟩
    have hqle : q ≤ p := primeFactor_le_largestPrimeFactor hd hqmemd
    have hqne : q ≠ p := by
      intro h
      subst q
      have hnot : ¬ p ∣ oldPart d (primeStage p) := by
        simpa [hstage] using
          (oldPart_not_dvd_stagePrime (d := d) (primeStage_pos p) hd0)
      exact hnot (Nat.dvd_of_mem_primeFactors hqm)
    exact prime_mem_active_before_primeStage hp hq
      (hqd.trans hdQ) hQ (lt_of_le_of_ne hqle hqne)

theorem isNewModulus_stage_eq_primeStage_largest {Q r d : ℕ}
    (hQ : Q ≠ 0) (hd : 1 < d) (hnew : IsNewModulus Q r d) :
    r = primeStage (largestPrimeFactor d) := by
  let p := stagePrime r
  have hr : 0 < r := hnew.1
  have hp : p.Prime := stagePrime_prime hr
  have hd0 : d ≠ 0 := by omega
  have hpd : p ∣ d :=
    Nat.dvd_of_factorization_pos (ne_of_gt hnew.2.2.1)
  have hpmem : p ∈ d.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hpd, hd0⟩
  have hm0 : oldPart d r ≠ 0 := by
    simpa [oldPart, p] using (Nat.ordCompl_pos p hd0).ne'
  have hall : ∀ q ∈ d.primeFactors, q ≤ p := by
    intro q hq
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqd : q ∣ d := Nat.dvd_of_mem_primeFactors hq
    have hdecomp := (newModulus_eq_oldPart_mul_pow hQ hnew).1
    have hqprod : q ∣ oldPart d r * p ^ d.factorization p := by
      simpa [p] using hdecomp ▸ hqd
    rcases hqprime.dvd_mul.mp hqprod with hqm | hqpow
    · have hqmemm : q ∈ (oldPart d r).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hqprime, hqm, hm0⟩
      have hqmemPartial :
          q ∈ (partialPeriod Q (r - 1)).primeFactors :=
        Nat.primeFactors_mono hnew.2.2.2
          (partialPeriod_pos Q (r - 1)).ne' hqmemm
      have hqactive : q ∈ activePrimeFactors Q (r - 1) :=
        primeFactors_partialPeriod_subset_active Q (r - 1) hqmemPartial
      by_cases hprev : 0 < r - 1
      · have hqle := (mem_activePrimeFactors_iff hprev).mp hqactive |>.2
        have hlt : stagePrime (r - 1) < p := by
          unfold p stagePrime
          apply Nat.nth_strictMono Nat.infinite_setOfPred_prime
          omega
        exact hqle.trans hlt.le
      · have hz : r - 1 = 0 := Nat.eq_zero_of_not_pos hprev
        simpa [hz] using hqactive
    · have hqp : q ∣ p := hqprime.dvd_of_dvd_pow hqpow
      exact (Nat.le_of_dvd hp.pos hqp)
  have hlargest_le : largestPrimeFactor d ≤ p :=
    hall _ (largestPrimeFactor_mem hd)
  have hp_le : p ≤ largestPrimeFactor d :=
    primeFactor_le_largestPrimeFactor hd hpmem
  have hlargest : largestPrimeFactor d = p :=
    Nat.le_antisymm hlargest_le hp_le
  calc
    r = primeStage p := (primeStage_stagePrime hr).symm
    _ = primeStage (largestPrimeFactor d) := by rw [hlargest]

/-- Exact uniqueness of the largest-prime stage assignment. -/
theorem isNewModulus_iff_primeStage_largest {Q r d : ℕ}
    (hQ : Q ≠ 0) (hdQ : d ∣ Q) (hd : 1 < d) :
    IsNewModulus Q r d ↔ r = primeStage (largestPrimeFactor d) := by
  constructor
  · exact isNewModulus_stage_eq_primeStage_largest hQ hd
  · intro hr
    subst r
    exact divisor_isNewModulus_at_largestPrimeStage hQ hdQ hd

theorem divisor_processed_by_horizon_at_largestPrimeStage {Q d : ℕ}
    (hQ : Q ≠ 0) (hdQ : d ∣ Q) (hd : 1 < d) :
    primeStage (largestPrimeFactor d) ≤ stageHorizon Q ∧
      IsNewModulus Q (primeStage (largestPrimeFactor d)) d := by
  refine ⟨?_, divisor_isNewModulus_at_largestPrimeStage hQ hdQ hd⟩
  let p := largestPrimeFactor d
  have hpQ : p ≤ Q :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hQ) ((largestPrimeFactor_dvd hd).trans hdQ)
  have hstage_le_prime : primeStage p ≤ p := by
    have hprime := largestPrimeFactor_prime hd
    have hnth := Nat.add_two_le_nth_prime (Nat.count Nat.Prime p)
    rw [Nat.nth_count hprime] at hnth
    simp [primeStage]
    omega
  exact hstage_le_prime.trans (hpQ.trans (le_stageHorizon Q))

end

end Erdos586
