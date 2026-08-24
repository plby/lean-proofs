/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos360.Core

/-!
# The structured lower-bound set for Erdős 360

This file gives the finite, exact part of the structured test set used in
CFP Section 5.  The analytic input is deliberately separated into the final
theorems: the already formalized filtered beta sieve supplies a lower bound
for every relaxed divisor fibre, while `targetPrimeBadQuotients` records the
only loss that is not controlled by that sieve alone.
-/

namespace Erdos360

open Filter
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Divisors of the target which are allowed in the structured
factorization.  In the CFP application `U` is the integer version of
`y^(1/16)`. -/
def boundedTargetDivisors (n U : ℕ) : Finset ℕ :=
  n.divisors.filter fun u ↦ u ≤ U

@[simp] lemma mem_boundedTargetDivisors {n U u : ℕ} :
    u ∈ boundedTargetDivisors n U ↔ u ∣ n ∧ n ≠ 0 ∧ u ≤ U := by
  simp [boundedTargetDivisors, Nat.mem_divisors, and_assoc]

lemma boundedTargetDivisor_pos {n U u : ℕ}
    (hu : u ∈ boundedTargetDivisors n U) : 0 < u := by
  exact Nat.pos_of_dvd_of_pos (mem_boundedTargetDivisors.mp hu).1
    (Nat.pos_of_ne_zero (mem_boundedTargetDivisors.mp hu).2.1)

/-- The dyadic part `(X, 2X]` of the interval sifted by the odd primes at
most `r` which do not divide the target. -/
def relaxedDyadicQuotients (n r X : ℕ) : Finset ℕ :=
  selectedSiftedInterval n r (2 * X) \ selectedSiftedInterval n r X

@[simp] lemma mem_relaxedDyadicQuotients {n r X q : ℕ} :
    q ∈ relaxedDyadicQuotients n r X ↔
      X < q ∧ q ≤ 2 * X ∧
        Nat.Coprime q (missingPrimeProduct n r) := by
  constructor
  · intro hq
    obtain ⟨hqBig, hqSmall⟩ := Finset.mem_sdiff.mp hq
    obtain ⟨hqIoc, hqcop⟩ := Finset.mem_filter.mp hqBig
    have hqpos : 0 < q := (Finset.mem_Ioc.mp hqIoc).1
    have hq2X : q ≤ 2 * X := (Finset.mem_Ioc.mp hqIoc).2
    have hqnot : ¬(0 < q ∧ q ≤ X) := by
      intro hqX
      exact hqSmall (Finset.mem_filter.mpr
        ⟨Finset.mem_Ioc.mpr hqX, hqcop⟩)
    exact ⟨by omega, hq2X, hqcop⟩
  · rintro ⟨hXq, hq2X, hqcop⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨by omega, hq2X⟩, hqcop⟩, ?_⟩
    intro hsmall
    have hqX := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hsmall).1).2
    omega

/-- The exact quotient fibre in CFP: in addition to avoiding the selected
small primes, the quotient is coprime to the full target. -/
def targetCoprimeDyadicQuotients (n r X : ℕ) : Finset ℕ :=
  (relaxedDyadicQuotients n r X).filter fun q ↦ Nat.Coprime q n

/-- The exact modulus whose coprimality is imposed on structured
quotients.  Its two factors are coprime by construction. -/
def structuredSieveModulus (n r : ℕ) : ℕ :=
  missingPrimeProduct n r * n

lemma missingPrimeProduct_mul_target_coprime (n r : ℕ) :
    Nat.Coprime (missingPrimeProduct n r) n :=
  missingPrimeProduct_coprime_target n r

@[simp] lemma mem_targetCoprimeDyadicQuotients {n r X q : ℕ} :
    q ∈ targetCoprimeDyadicQuotients n r X ↔
      X < q ∧ q ≤ 2 * X ∧
        Nat.Coprime q (missingPrimeProduct n r) ∧ Nat.Coprime q n := by
  simp only [targetCoprimeDyadicQuotients, Finset.mem_filter,
    mem_relaxedDyadicQuotients]
  aesop

lemma mem_targetCoprimeDyadicQuotients_modulus {n r X q : ℕ} :
    q ∈ targetCoprimeDyadicQuotients n r X ↔
      X < q ∧ q ≤ 2 * X ∧ Nat.Coprime q (structuredSieveModulus n r) := by
  rw [mem_targetCoprimeDyadicQuotients]
  simp only [structuredSieveModulus, Nat.coprime_mul_iff_right]

/-- Quotients deleted from a relaxed fibre because they still contain a
prime factor of the target.  Controlling the sum of these finite errors is
the remaining target-prime estimate, separate from the beta sieve. -/
def targetPrimeBadQuotients (n r X : ℕ) : Finset ℕ :=
  (relaxedDyadicQuotients n r X).filter fun q ↦ ¬Nat.Coprime q n

lemma targetCoprime_card_add_bad_card (n r X : ℕ) :
    (targetCoprimeDyadicQuotients n r X).card +
        (targetPrimeBadQuotients n r X).card =
      (relaxedDyadicQuotients n r X).card := by
  rw [targetCoprimeDyadicQuotients, targetPrimeBadQuotients]
  exact (relaxedDyadicQuotients n r X).card_filter_add_card_filter_not
    (fun q ↦ Nat.Coprime q n)

/-- The structured fibre belonging to a divisor `u`: multiply the exact
quotient fibre at scale `y/u` by `u`. -/
def structuredDivisorFiber (n r y u : ℕ) : Finset ℕ :=
  (targetCoprimeDyadicQuotients n r (y / u)).image fun q ↦ u * q

/-- CFP's finite structured test set, with an explicit divisor cutoff `U`.
Every element has a representation `u*q`, where `u ∣ n`, `u ≤ U`, and the
quotient is coprime to both the selected sieve product and `n`. -/
def structuredTestSet (n r y U : ℕ) : Finset ℕ :=
  (boundedTargetDivisors n U).biUnion fun u ↦
    structuredDivisorFiber n r y u

lemma mem_structuredDivisorFiber {n r y u a : ℕ} :
    a ∈ structuredDivisorFiber n r y u ↔
      ∃ q, q ∈ targetCoprimeDyadicQuotients n r (y / u) ∧ a = u * q := by
  simp [structuredDivisorFiber, eq_comm]

lemma mem_structuredTestSet {n r y U a : ℕ} :
    a ∈ structuredTestSet n r y U ↔
      ∃ u, u ∣ n ∧ n ≠ 0 ∧ u ≤ U ∧
        ∃ q, y / u < q ∧ q ≤ 2 * (y / u) ∧
          Nat.Coprime q (missingPrimeProduct n r) ∧ Nat.Coprime q n ∧
          a = u * q := by
  constructor
  · intro ha
    obtain ⟨u, hu, hau⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨q, hq, rfl⟩ := mem_structuredDivisorFiber.mp hau
    obtain ⟨huy, hq2, hqM, hqn⟩ :=
      mem_targetCoprimeDyadicQuotients.mp hq
    exact ⟨u, (mem_boundedTargetDivisors.mp hu).1,
      (mem_boundedTargetDivisors.mp hu).2.1,
      (mem_boundedTargetDivisors.mp hu).2.2,
      q, huy, hq2, hqM, hqn, rfl⟩
  · rintro ⟨u, hun, hn0, huU, q, hyq, hq2, hqM, hqn, rfl⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨u, mem_boundedTargetDivisors.mpr ⟨hun, hn0, huU⟩, ?_⟩
    exact mem_structuredDivisorFiber.mpr
      ⟨q, mem_targetCoprimeDyadicQuotients.mpr
        ⟨hyq, hq2, hqM, hqn⟩, rfl⟩

lemma structuredTestSet_pos {n r y U a : ℕ}
    (ha : a ∈ structuredTestSet n r y U) : 0 < a := by
  obtain ⟨u, _hun, hn0, _huU, q, hyq, _hq2, _hqM, _hqn, rfl⟩ :=
    mem_structuredTestSet.mp ha
  exact Nat.mul_pos (Nat.pos_of_dvd_of_pos _hun (Nat.pos_of_ne_zero hn0))
    (by omega)

lemma structuredTestSet_gt_scale {n r y U a : ℕ}
    (ha : a ∈ structuredTestSet n r y U) : y < a := by
  obtain ⟨u, hun, hn0, _huU, q, hyq, _hq2, _hqM, _hqn, rfl⟩ :=
    mem_structuredTestSet.mp ha
  have hu : 0 < u := Nat.pos_of_dvd_of_pos hun (Nat.pos_of_ne_zero hn0)
  have hnext : y < u * (y / u + 1) := Nat.lt_mul_div_succ y hu
  have hquotient : y / u + 1 ≤ q := by omega
  exact hnext.trans_le (Nat.mul_le_mul_left u hquotient)

lemma structuredTestSet_le_two_mul {n r y U a : ℕ}
    (ha : a ∈ structuredTestSet n r y U) : a ≤ 2 * y := by
  obtain ⟨u, _hun, hn0, _huU, q, _hyq, hq2, _hqM, _hqn, rfl⟩ :=
    mem_structuredTestSet.mp ha
  have hu : 0 < u := Nat.pos_of_dvd_of_pos _hun (Nat.pos_of_ne_zero hn0)
  calc
    u * q ≤ u * (2 * (y / u)) := Nat.mul_le_mul_left u hq2
    _ = 2 * ((y / u) * u) := by ac_rfl
    _ ≤ 2 * y := Nat.mul_le_mul_left 2 (Nat.div_mul_le_self y u)

lemma structuredTestSet_subset_dyadic (n r y U : ℕ) :
    structuredTestSet n r y U ⊆ Finset.Ioc y (2 * y) := by
  intro a ha
  exact Finset.mem_Ioc.mpr
    ⟨structuredTestSet_gt_scale ha, structuredTestSet_le_two_mul ha⟩

/-- The divisor coordinate is canonical: it is exactly the gcd of the
structured integer with the target. -/
lemma structuredTestSet_divisor_eq_gcd {n r y U a : ℕ}
    (ha : a ∈ structuredTestSet n r y U) :
    ∃ u, u ∣ n ∧ u ≤ U ∧ u = Nat.gcd a n := by
  obtain ⟨u, hun, _hn0, huU, q, _hyq, _hq2, _hqM, hqn, haq⟩ :=
    mem_structuredTestSet.mp ha
  obtain ⟨k, hk⟩ := hun
  have hunAgain : u ∣ n := ⟨k, hk⟩
  have hkn : k ∣ n := ⟨u, by simpa [mul_comm] using hk⟩
  have hqk : Nat.Coprime q k := Nat.Coprime.of_dvd_right hkn hqn
  refine ⟨u, hunAgain, huU, ?_⟩
  rw [haq, hk, Nat.gcd_mul_left, hqk.gcd_eq_one, mul_one]

/-- Under the application-side inequality `2*y < n`, every structured
integer is a legal member of `{1, ..., n-1}`. -/
lemma structuredTestSet_subset_Ico {n r y U : ℕ} (hy : 2 * y < n) :
    structuredTestSet n r y U ⊆ Finset.Ico 1 n := by
  intro a ha
  exact Finset.mem_Ico.mpr
    ⟨structuredTestSet_pos ha, (structuredTestSet_le_two_mul ha).trans_lt hy⟩

lemma mul_injectiveOn_structuredFibers {n r y U : ℕ} :
    (boundedTargetDivisors n U : Set ℕ).PairwiseDisjoint
      (structuredDivisorFiber n r y) := by
  intro u hu v hv huv
  change Disjoint (structuredDivisorFiber n r y u)
    (structuredDivisorFiber n r y v)
  rw [Finset.disjoint_left]
  intro a hau hav
  obtain ⟨q, hq, haq⟩ := mem_structuredDivisorFiber.mp hau
  obtain ⟨s, hs, has⟩ := mem_structuredDivisorFiber.mp hav
  have huData := mem_boundedTargetDivisors.mp hu
  have hvData := mem_boundedTargetDivisors.mp hv
  have hqn := (mem_targetCoprimeDyadicQuotients.mp hq).2.2.2
  have hsn := (mem_targetCoprimeDyadicQuotients.mp hs).2.2.2
  have hus : Nat.Coprime u s :=
    (Nat.Coprime.of_dvd_right huData.1 hsn).symm
  have hvq : Nat.Coprime v q :=
    (Nat.Coprime.of_dvd_right hvData.1 hqn).symm
  have heq : u * q = v * s := haq.symm.trans has
  have huvDvd : u ∣ v := by
    apply hus.dvd_of_dvd_mul_right
    exact heq ▸ dvd_mul_right u q
  have hvuDvd : v ∣ u := by
    apply hvq.dvd_of_dvd_mul_right
    exact heq.symm ▸ dvd_mul_right v s
  exact huv (Nat.dvd_antisymm huvDvd hvuDvd)

lemma card_structuredDivisorFiber {n r y U u : ℕ}
    (hu : u ∈ boundedTargetDivisors n U) :
    (structuredDivisorFiber n r y u).card =
      (targetCoprimeDyadicQuotients n r (y / u)).card := by
  unfold structuredDivisorFiber
  rw [Finset.card_image_iff]
  intro q hq s hs hqs
  exact Nat.eq_of_mul_eq_mul_left (boundedTargetDivisor_pos hu) hqs

/-- Exact cardinality of the structured set as a sum over its divisor
fibres.  No multiplicity loss occurs. -/
theorem card_structuredTestSet (n r y U : ℕ) :
    (structuredTestSet n r y U).card =
      ∑ u ∈ boundedTargetDivisors n U,
        (targetCoprimeDyadicQuotients n r (y / u)).card := by
  rw [structuredTestSet,
    Finset.card_biUnion mul_injectiveOn_structuredFibers]
  apply Finset.sum_congr rfl
  intro u hu
  exact card_structuredDivisorFiber hu

lemma selectedSiftedInterval_mono_length (n r : ℕ) {X Z : ℕ}
    (hXZ : X ≤ Z) :
    selectedSiftedInterval n r X ⊆ selectedSiftedInterval n r Z := by
  intro q hq
  obtain ⟨hqIoc, hqcop⟩ := Finset.mem_filter.mp hq
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Ioc.mpr
      ⟨(Finset.mem_Ioc.mp hqIoc).1,
        (Finset.mem_Ioc.mp hqIoc).2.trans hXZ⟩,
      hqcop⟩

lemma relaxedDyadic_card_add_initial (n r X : ℕ) :
    (relaxedDyadicQuotients n r X).card +
        (selectedSiftedInterval n r X).card =
      (selectedSiftedInterval n r (2 * X)).card := by
  have hsub : selectedSiftedInterval n r X ⊆
      selectedSiftedInterval n r (2 * X) :=
    selectedSiftedInterval_mono_length n r (by omega)
  rw [relaxedDyadicQuotients, Finset.card_sdiff_of_subset hsub]
  have hcard := Finset.card_le_card hsub
  omega

/-- Direct consequence of the two finite beta-sieve bounds already proved
in `Core`: subtract the upper bound for `(0,X]` from the lower bound for
`(0,2X]`.  The result is a completely explicit lower bound for the relaxed
dyadic quotient fibre. -/
theorem exists_relaxedDyadicQuotients_card_lower_bound :
    ∃ Aup Alo : ℝ, 1 ≤ Aup ∧ 1 ≤ Alo ∧
      ∀ n r X S : ℕ, 2 ≤ r → 101 ≤ S →
        Real.log Aup ≤ 2 * (S - 100 : ℕ) / 99 →
        Real.log Alo ≤ 2 * (S - 100 : ℕ) / 99 →
        let V := missingEulerProduct n r
        let etaUp := (4 * Aup / 3) * (1 / 4 : ℝ) ^ (S - 100)
        let etaLo := (4 * Alo / 3) * (1 / 4 : ℝ) ^ (S - 100)
        let D := r ^ S
        (2 * X : ℕ) * ((1 - etaLo) * V) - (D : ℝ) ^ 2 -
            ((X : ℝ) * ((1 + etaUp) * V) + (D : ℝ) ^ 2) ≤
          ((relaxedDyadicQuotients n r X).card : ℝ) := by
  obtain ⟨Aup, hAup, hupper⟩ := exists_selectedSiftedInterval_card_bound
  obtain ⟨Alo, hAlo, hlower⟩ :=
    exists_selectedSiftedInterval_card_lower_bound
  refine ⟨Aup, Alo, hAup, hAlo, ?_⟩
  intro n r X S hr hS hlogUp hlogLo
  dsimp only
  have hU := hupper n X r S hr hS hlogUp
  have hL := hlower n (2 * X) r S hr hS hlogLo
  dsimp only at hU hL
  have hcardNat := relaxedDyadic_card_add_initial n r X
  have hcardReal :
      ((relaxedDyadicQuotients n r X).card : ℝ) +
          ((selectedSiftedInterval n r X).card : ℝ) =
        ((selectedSiftedInterval n r (2 * X)).card : ℝ) := by
    exact_mod_cast hcardNat
  nlinarith

/-- The exact target-coprime fibre has the beta-sieve lower bound, minus
the explicit finite set of quotients rejected because of a target prime.
This statement pinpoints the analytic estimate still needed for the full
CFP structured-count constant. -/
theorem exists_targetCoprimeDyadicQuotients_card_lower_bound :
    ∃ Aup Alo : ℝ, 1 ≤ Aup ∧ 1 ≤ Alo ∧
      ∀ n r X S : ℕ, 2 ≤ r → 101 ≤ S →
        Real.log Aup ≤ 2 * (S - 100 : ℕ) / 99 →
        Real.log Alo ≤ 2 * (S - 100 : ℕ) / 99 →
        let V := missingEulerProduct n r
        let etaUp := (4 * Aup / 3) * (1 / 4 : ℝ) ^ (S - 100)
        let etaLo := (4 * Alo / 3) * (1 / 4 : ℝ) ^ (S - 100)
        let D := r ^ S
        (2 * X : ℕ) * ((1 - etaLo) * V) - (D : ℝ) ^ 2 -
            ((X : ℝ) * ((1 + etaUp) * V) + (D : ℝ) ^ 2) -
            ((targetPrimeBadQuotients n r X).card : ℝ) ≤
          ((targetCoprimeDyadicQuotients n r X).card : ℝ) := by
  obtain ⟨Aup, Alo, hAup, hAlo, hrelaxed⟩ :=
    exists_relaxedDyadicQuotients_card_lower_bound
  refine ⟨Aup, Alo, hAup, hAlo, ?_⟩
  intro n r X S hr hS hlogUp hlogLo
  dsimp only
  have hbound := hrelaxed n r X S hr hS hlogUp hlogLo
  dsimp only at hbound
  have hpartitionNat := targetCoprime_card_add_bad_card n r X
  have hpartitionReal :
      ((targetCoprimeDyadicQuotients n r X).card : ℝ) +
          ((targetPrimeBadQuotients n r X).card : ℝ) =
        ((relaxedDyadicQuotients n r X).card : ℝ) := by
    exact_mod_cast hpartitionNat
  linarith

/-- Divisor-summed lower bound for the complete structured test set.  Its
main term and square-level errors come from the formal beta sieve.  The sum
of `targetPrimeBadQuotients` is the isolated target-prime tail which the
number-theoretic parameter argument must dominate. -/
theorem exists_structuredTestSet_card_lower_bound :
    ∃ Aup Alo : ℝ, 1 ≤ Aup ∧ 1 ≤ Alo ∧
      ∀ n r y U S : ℕ, 2 ≤ r → 101 ≤ S →
        Real.log Aup ≤ 2 * (S - 100 : ℕ) / 99 →
        Real.log Alo ≤ 2 * (S - 100 : ℕ) / 99 →
        let V := missingEulerProduct n r
        let etaUp := (4 * Aup / 3) * (1 / 4 : ℝ) ^ (S - 100)
        let etaLo := (4 * Alo / 3) * (1 / 4 : ℝ) ^ (S - 100)
        let D := r ^ S
        (∑ u ∈ boundedTargetDivisors n U,
          (((2 * (y / u) : ℕ) : ℝ) * ((1 - etaLo) * V) - (D : ℝ) ^ 2 -
            (((y / u : ℕ) : ℝ) * ((1 + etaUp) * V) + (D : ℝ) ^ 2) -
            ((targetPrimeBadQuotients n r (y / u)).card : ℝ))) ≤
          ((structuredTestSet n r y U).card : ℝ) := by
  obtain ⟨Aup, Alo, hAup, hAlo, hfiber⟩ :=
    exists_targetCoprimeDyadicQuotients_card_lower_bound
  refine ⟨Aup, Alo, hAup, hAlo, ?_⟩
  intro n r y U S hr hS hlogUp hlogLo
  dsimp only
  rw [card_structuredTestSet]
  push_cast
  apply Finset.sum_le_sum
  intro u hu
  have huBound := hfiber n r (y / u) S hr hS hlogUp hlogLo
  norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] at huBound ⊢
  exact huBound

/-- The exact pigeonhole interface used after the structured-count bound:
every `k`-coloring of the test set has a class of size at least the integer
average. -/
theorem exists_large_colorClass_in_structuredTestSet
    {n r y U k : ℕ} (hk : 0 < k) (c : ℕ → Fin k) :
    ∃ i : Fin k,
      (structuredTestSet n r y U).card / k ≤
        ((structuredTestSet n r y U).filter fun a ↦ c a = i).card := by
  have huniv : (Finset.univ : Finset (Fin k)).Nonempty := by
    exact Finset.univ_nonempty_iff.mpr ⟨⟨0, hk⟩⟩
  have havg : (Finset.univ : Finset (Fin k)).card *
      ((structuredTestSet n r y U).card / k) ≤
        (structuredTestSet n r y U).card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    simpa [mul_comm] using
      Nat.div_mul_le_self (structuredTestSet n r y U).card k
  obtain ⟨i, _hi, hcard⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s := structuredTestSet n r y U)
      (t := Finset.univ)
      (f := c)
      (n := (structuredTestSet n r y U).card / k)
      (fun _ _ ↦ Finset.mem_univ _) huniv havg
  exact ⟨i, hcard⟩

end Erdos360
