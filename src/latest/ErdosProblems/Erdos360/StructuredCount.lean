/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.LowerParameters
import ErdosProblems.Erdos360.InitialMertens
import ErdosProblems.Erdos360.BadQuotients
import ErdosProblems.Erdos446.PrimeDyadic
import ErdosProblems.Erdos387.BrunSieve

/-!
# Erdős 360: the structured test-set count via prime quotients

The beta-sieve lower bound in `BadQuotients` has a level error which is not
useful when its cutoff is the number of colours.  The source count has a
cleaner proof in the diagonal range: in each divisor fibre retain only prime
quotients larger than the last of the selected initial primes.  Such a prime
is automatically coprime to the initial-prime product, and deleting the
prime divisors of the target makes it coprime to the target as well.

This file first gives the exact finite injection and cardinal inequality.
The remaining sections establish the divisor-reciprocal and truncation
estimates needed to sum the prime-number-theorem lower bounds.
-/

namespace Erdos360

open Filter
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Prime quotients in `(X,2X]` which are not prime divisors of the target. -/
def primeStructuredQuotients (n X : ℕ) : Finset ℕ :=
  Erdos446.dyadicPrimes X \ n.primeFactors

/-- The divisor fibre obtained by retaining only prime quotients. -/
def primeStructuredDivisorFiber (n y u : ℕ) : Finset ℕ :=
  (primeStructuredQuotients n (y / u)).image fun q ↦ u * q

/-- The prime-only source set.  Unlike the odd-prime beta-sieve set, every
quotient here is coprime to the *complete* initial primorial. -/
def primeStructuredTestSet (n y U : ℕ) : Finset ℕ :=
  (boundedTargetDivisors n U).biUnion fun u ↦
    primeStructuredDivisorFiber n y u

@[simp] lemma mem_primeStructuredQuotients {n X q : ℕ} :
    q ∈ primeStructuredQuotients n X ↔
      X < q ∧ q ≤ 2 * X ∧ q.Prime ∧ q ∉ n.primeFactors := by
  simp only [primeStructuredQuotients, Finset.mem_sdiff,
    Erdos446.mem_dyadicPrimes]
  aesop

/-- A retained prime quotient belongs to the exact quotient fibre. -/
lemma primeStructuredQuotients_subset_targetCoprime
    {n h X : ℕ} (hn : n ≠ 0) (hh : 0 < h)
    (hcut : primeAt (h - 1) ≤ X) :
    primeStructuredQuotients n X ⊆
      targetCoprimeDyadicQuotients n (primeAt (h - 1)) X := by
  intro q hq
  obtain ⟨hXq, hq2X, hqPrime, hqNot⟩ :=
    mem_primeStructuredQuotients.mp hq
  apply mem_targetCoprimeDyadicQuotients.mpr
  refine ⟨hXq, hq2X, ?_, ?_⟩
  · apply Nat.Coprime.of_dvd_right
      (missingPrimeProduct_dvd_primorial n (primeAt (h - 1)))
    rw [hqPrime.coprime_iff_not_dvd]
    intro hqDvd
    have hqle : q ≤ primeAt (h - 1) :=
      hqPrime.dvd_primorial_iff.mp hqDvd
    omega
  · rw [hqPrime.coprime_iff_not_dvd]
    intro hqDvd
    exact hqNot (Nat.mem_primeFactors.mpr ⟨hqPrime, hqDvd, hn⟩)

@[simp] lemma mem_primeStructuredDivisorFiber {n y u a : ℕ} :
    a ∈ primeStructuredDivisorFiber n y u ↔
      ∃ q, q ∈ primeStructuredQuotients n (y / u) ∧ a = u * q := by
  simp [primeStructuredDivisorFiber, eq_comm]

@[simp] lemma mem_primeStructuredTestSet {n y U a : ℕ} :
    a ∈ primeStructuredTestSet n y U ↔
      ∃ u, u ∣ n ∧ n ≠ 0 ∧ u ≤ U ∧
        ∃ q, y / u < q ∧ q ≤ 2 * (y / u) ∧ q.Prime ∧
          q ∉ n.primeFactors ∧ a = u * q := by
  constructor
  · intro ha
    obtain ⟨u, hu, hau⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨q, hq, rfl⟩ := mem_primeStructuredDivisorFiber.mp hau
    obtain ⟨hun, hn, huU⟩ := mem_boundedTargetDivisors.mp hu
    obtain ⟨hyq, hq2, hp, hpn⟩ := mem_primeStructuredQuotients.mp hq
    exact ⟨u, hun, hn, huU, q, hyq, hq2, hp, hpn, rfl⟩
  · rintro ⟨u, hun, hn, huU, q, hyq, hq2, hp, hpn, rfl⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨u, mem_boundedTargetDivisors.mpr ⟨hun, hn, huU⟩, ?_⟩
    exact mem_primeStructuredDivisorFiber.mpr
      ⟨q, mem_primeStructuredQuotients.mpr ⟨hyq, hq2, hp, hpn⟩, rfl⟩

/-- Source-facing factorization: if `B ≤ y/U`, every prime quotient in the
test set is strictly larger than `B`. -/
lemma primeStructuredTestSet_factorization_above
    {n y U B a : ℕ} (hU : 0 < U) (hB : B ≤ y / U)
    (ha : a ∈ primeStructuredTestSet n y U) :
    ∃ u q : ℕ, u ∣ n ∧ q.Prime ∧ B < q ∧ a = u * q := by
  obtain ⟨u, hun, hn, huU, q, hyq, _hq2, hp, _hpn, rfl⟩ :=
    mem_primeStructuredTestSet.mp ha
  have hu : 0 < u := Nat.pos_of_dvd_of_pos hun (Nat.pos_of_ne_zero hn)
  have hdiv : y / U ≤ y / u := Nat.div_le_div_left huU hu
  exact ⟨u, q, hun, hp, (hB.trans hdiv).trans_lt hyq, rfl⟩

/-- Every test integer has the source factorization with its prime quotient
above the last selected initial prime, provided the latter lies below every
divisor-fibre scale. -/
lemma primeStructuredTestSet_factorization_above_primeAt
    {n h y U a : ℕ}
    (hcut : ∀ u ∈ boundedTargetDivisors n U,
      primeAt (h - 1) ≤ y / u)
    (ha : a ∈ primeStructuredTestSet n y U) :
    ∃ u q : ℕ, u ∣ n ∧ q.Prime ∧ primeAt (h - 1) < q ∧ a = u * q := by
  obtain ⟨u, hun, hn, huU, q, hyq, _hq2, hp, _hpn, rfl⟩ :=
    mem_primeStructuredTestSet.mp ha
  have hu : u ∈ boundedTargetDivisors n U :=
    mem_boundedTargetDivisors.mpr ⟨hun, hn, huU⟩
  exact ⟨u, q, hun, hp, (hcut u hu).trans_lt hyq, rfl⟩

lemma primeStructuredTestSet_gt_scale {n y U a : ℕ}
    (ha : a ∈ primeStructuredTestSet n y U) : y < a := by
  obtain ⟨u, hun, hn, _huU, q, hyq, _hq2, _hp, _hpn, rfl⟩ :=
    mem_primeStructuredTestSet.mp ha
  have hu : 0 < u := Nat.pos_of_dvd_of_pos hun (Nat.pos_of_ne_zero hn)
  have hnext : y < u * (y / u + 1) := Nat.lt_mul_div_succ y hu
  exact hnext.trans_le (Nat.mul_le_mul_left u (by omega))

lemma primeStructuredTestSet_le_two_mul {n y U a : ℕ}
    (ha : a ∈ primeStructuredTestSet n y U) : a ≤ 2 * y := by
  obtain ⟨u, hun, hn, _huU, q, _hyq, hq2, _hp, _hpn, rfl⟩ :=
    mem_primeStructuredTestSet.mp ha
  have hu : 0 < u := Nat.pos_of_dvd_of_pos hun (Nat.pos_of_ne_zero hn)
  calc
    u * q ≤ u * (2 * (y / u)) := Nat.mul_le_mul_left u hq2
    _ = 2 * ((y / u) * u) := by ac_rfl
    _ ≤ 2 * y := Nat.mul_le_mul_left 2 (Nat.div_mul_le_self y u)

lemma primeStructuredTestSet_subset_Ico {n y U : ℕ} (hy : 2 * y < n) :
    primeStructuredTestSet n y U ⊆ Finset.Ico 1 n := by
  intro a ha
  exact Finset.mem_Ico.mpr
    ⟨by have := primeStructuredTestSet_gt_scale ha; omega,
      (primeStructuredTestSet_le_two_mul ha).trans_lt hy⟩

lemma primeStructuredDivisorFiber_subset_structured
    {n h y u : ℕ} (hn : n ≠ 0) (hh : 0 < h)
    (hcut : primeAt (h - 1) ≤ y / u) :
    primeStructuredDivisorFiber n y u ⊆
      structuredDivisorFiber n (primeAt (h - 1)) y u := by
  intro a ha
  obtain ⟨q, hq, rfl⟩ := mem_primeStructuredDivisorFiber.mp ha
  exact mem_structuredDivisorFiber.mpr
    ⟨q, primeStructuredQuotients_subset_targetCoprime hn hh hcut hq, rfl⟩

lemma primeStructuredTestSet_subset_structured
    {n h y U : ℕ} (hn : n ≠ 0) (hh : 0 < h)
    (hcut : ∀ u ∈ boundedTargetDivisors n U,
      primeAt (h - 1) ≤ y / u) :
    primeStructuredTestSet n y U ⊆
      structuredTestSet n (primeAt (h - 1)) y U := by
  intro a ha
  obtain ⟨u, hu, hau⟩ := Finset.mem_biUnion.mp ha
  exact Finset.mem_biUnion.mpr
    ⟨u, hu, primeStructuredDivisorFiber_subset_structured hn hh
      (hcut u hu) hau⟩

lemma primeStructuredFibers_pairwiseDisjoint (n y U : ℕ) :
    (boundedTargetDivisors n U : Set ℕ).PairwiseDisjoint
      (primeStructuredDivisorFiber n y) := by
  intro u hu v hv huv
  change Disjoint (primeStructuredDivisorFiber n y u)
    (primeStructuredDivisorFiber n y v)
  rw [Finset.disjoint_left]
  intro a hau hav
  obtain ⟨q, hq, haq⟩ := mem_primeStructuredDivisorFiber.mp hau
  obtain ⟨s, hs, has⟩ := mem_primeStructuredDivisorFiber.mp hav
  have huData := mem_boundedTargetDivisors.mp hu
  have hvData := mem_boundedTargetDivisors.mp hv
  have hqData := mem_primeStructuredQuotients.mp hq
  have hsData := mem_primeStructuredQuotients.mp hs
  have hqCop : Nat.Coprime q n := by
    rw [hqData.2.2.1.coprime_iff_not_dvd]
    intro hqn
    exact hqData.2.2.2
      (Nat.mem_primeFactors.mpr ⟨hqData.2.2.1, hqn, huData.2.1⟩)
  have hsCop : Nat.Coprime s n := by
    rw [hsData.2.2.1.coprime_iff_not_dvd]
    intro hsn
    exact hsData.2.2.2
      (Nat.mem_primeFactors.mpr ⟨hsData.2.2.1, hsn, hvData.2.1⟩)
  have hus : Nat.Coprime u s :=
    (Nat.Coprime.of_dvd_right huData.1 hsCop).symm
  have hvq : Nat.Coprime v q :=
    (Nat.Coprime.of_dvd_right hvData.1 hqCop).symm
  have heq : u * q = v * s := haq.symm.trans has
  have huvDvd : u ∣ v := by
    apply hus.dvd_of_dvd_mul_right
    exact heq ▸ dvd_mul_right u q
  have hvuDvd : v ∣ u := by
    apply hvq.dvd_of_dvd_mul_right
    exact heq.symm ▸ dvd_mul_right v s
  exact huv (Nat.dvd_antisymm huvDvd hvuDvd)

lemma card_primeStructuredDivisorFiber {n y U u : ℕ}
    (hu : u ∈ boundedTargetDivisors n U) :
    (primeStructuredDivisorFiber n y u).card =
      (primeStructuredQuotients n (y / u)).card := by
  unfold primeStructuredDivisorFiber
  rw [Finset.card_image_iff]
  intro q hq s hs hqs
  exact Nat.eq_of_mul_eq_mul_left (boundedTargetDivisor_pos hu) hqs

theorem card_primeStructuredTestSet (n y U : ℕ) :
    (primeStructuredTestSet n y U).card =
      ∑ u ∈ boundedTargetDivisors n U,
        (primeStructuredQuotients n (y / u)).card := by
  rw [primeStructuredTestSet,
    Finset.card_biUnion (primeStructuredFibers_pairwiseDisjoint n y U)]
  apply Finset.sum_congr rfl
  intro u hu
  exact card_primeStructuredDivisorFiber hu

/-- Every retained quotient is coprime to the complete initial primorial.
This is the parity invariant needed after common-divisor extraction. -/
lemma primeStructured_quotient_coprime_primorial
    {n h X q : ℕ} (hh : 0 < h)
    (hcut : primeAt (h - 1) ≤ X)
    (hq : q ∈ primeStructuredQuotients n X) :
    Nat.Coprime q (primorial (primeAt (h - 1))) := by
  have hqData := mem_primeStructuredQuotients.mp hq
  rw [hqData.2.2.1.coprime_iff_not_dvd]
  intro hqdvd
  have hqle := hqData.2.2.1.dvd_primorial_iff.mp hqdvd
  omega

/-- Deleting target prime factors loses at most their number. -/
lemma dyadicPrimes_card_sub_primeFactors_le_primeStructured
    (n X : ℕ) :
    (Erdos446.dyadicPrimes X).card - n.primeFactors.card ≤
      (primeStructuredQuotients n X).card := by
  unfold primeStructuredQuotients
  have hcard := Finset.card_sdiff_add_card_inter
    (Erdos446.dyadicPrimes X) n.primeFactors
  have hinter : ((Erdos446.dyadicPrimes X) ∩ n.primeFactors).card ≤
      n.primeFactors.card :=
    Finset.card_le_card (Finset.inter_subset_right)
  omega

/-- Real-valued form convenient for subtracting the target-prime error. -/
lemma dyadicPrimes_card_cast_sub_primeFactors_le_primeStructured
    (n X : ℕ) :
    ((Erdos446.dyadicPrimes X).card : ℝ) - n.primeFactors.card ≤
      ((primeStructuredQuotients n X).card : ℝ) := by
  have hnat := dyadicPrimes_card_sub_primeFactors_le_primeStructured n X
  have hinter : ((Erdos446.dyadicPrimes X) ∩ n.primeFactors).card ≤
      n.primeFactors.card :=
    Finset.card_le_card (Finset.inter_subset_right)
  have hcard := Finset.card_sdiff_add_card_inter
    (Erdos446.dyadicPrimes X) n.primeFactors
  have hcardR :
      (((Erdos446.dyadicPrimes X \ n.primeFactors).card : ℕ) : ℝ) +
          (((Erdos446.dyadicPrimes X ∩ n.primeFactors).card : ℕ) : ℝ) =
        ((Erdos446.dyadicPrimes X).card : ℝ) := by
    exact_mod_cast hcard
  have hinterR :
      (((Erdos446.dyadicPrimes X ∩ n.primeFactors).card : ℕ) : ℝ) ≤
        (n.primeFactors.card : ℝ) := by
    exact_mod_cast hinter
  change ((Erdos446.dyadicPrimes X).card : ℝ) - n.primeFactors.card ≤
    (((Erdos446.dyadicPrimes X \ n.primeFactors).card : ℕ) : ℝ)
  linarith

/-- Summing the prime-only subfibres gives a beta-error-free lower bound for
the exact structured set. -/
theorem sum_primeStructuredQuotients_card_le_structuredTestSet
    {n h y U : ℕ} (hn : n ≠ 0) (hh : 0 < h)
    (hcut : ∀ u ∈ boundedTargetDivisors n U,
      primeAt (h - 1) ≤ y / u) :
    ∑ u ∈ boundedTargetDivisors n U,
        (primeStructuredQuotients n (y / u)).card ≤
      (structuredTestSet n (primeAt (h - 1)) y U).card := by
  rw [card_structuredTestSet]
  apply Finset.sum_le_sum
  intro u hu
  exact Finset.card_le_card
    (primeStructuredQuotients_subset_targetCoprime hn hh (hcut u hu))

/-- PNT-ready real form of the preceding divisor-fibre count. -/
theorem sum_dyadicPrime_lower_le_structuredTestSet
    {n h y U : ℕ} (hn : n ≠ 0) (hh : 0 < h)
    (hcut : ∀ u ∈ boundedTargetDivisors n U,
      primeAt (h - 1) ≤ y / u) :
    (∑ u ∈ boundedTargetDivisors n U,
      (((Erdos446.dyadicPrimes (y / u)).card : ℝ) -
        n.primeFactors.card)) ≤
      ((structuredTestSet n (primeAt (h - 1)) y U).card : ℝ) := by
  calc
    (∑ u ∈ boundedTargetDivisors n U,
      (((Erdos446.dyadicPrimes (y / u)).card : ℝ) -
        n.primeFactors.card)) ≤
        ∑ u ∈ boundedTargetDivisors n U,
          ((primeStructuredQuotients n (y / u)).card : ℝ) := by
      apply Finset.sum_le_sum
      intro u hu
      exact dyadicPrimes_card_cast_sub_primeFactors_le_primeStructured n _
    _ = ((∑ u ∈ boundedTargetDivisors n U,
          (primeStructuredQuotients n (y / u)).card : ℕ) : ℝ) := by
      norm_cast
    _ ≤ ((structuredTestSet n (primeAt (h - 1)) y U).card : ℝ) := by
      exact_mod_cast
        sum_primeStructuredQuotients_card_le_structuredTestSet hn hh hcut

/-- A concrete threshold form of the PNT estimate used in every fibre. -/
theorem exists_dyadicPrimes_card_lower_threshold :
    ∃ T : ℕ, ∀ X : ℕ, T ≤ X →
      (1 / 2 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)) ≤
        ((Erdos446.dyadicPrimes X).card : ℝ) := by
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
    Erdos446.eventually_dyadicPrimes_card_bounds
  exact ⟨T, fun X hX ↦ (hT X hX).1⟩

/-- Prime-number-theorem lower bound for the cardinality of the prime-only
test set, before any asymptotic simplification of the divisor sum. -/
theorem sum_primeNumberTheorem_lower_le_primeStructuredTestSet
    {n y U T : ℕ}
    (hPNT : ∀ X : ℕ, T ≤ X →
      (1 / 2 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)) ≤
        ((Erdos446.dyadicPrimes X).card : ℝ))
    (hscale : ∀ u ∈ boundedTargetDivisors n U, T ≤ y / u) :
    (∑ u ∈ boundedTargetDivisors n U,
      ((1 / 2 : ℝ) * (((y / u : ℕ) : ℝ) /
          Real.log ((y / u : ℕ) : ℝ)) - n.primeFactors.card)) ≤
      ((primeStructuredTestSet n y U).card : ℝ) := by
  rw [card_primeStructuredTestSet]
  push_cast
  apply Finset.sum_le_sum
  intro u hu
  exact (sub_le_sub_right (hPNT _ (hscale u hu)) _).trans
    (dyadicPrimes_card_cast_sub_primeFactors_le_primeStructured n _)

private lemma quarter_y_log_inv_le_dyadic_main
    {y u : ℕ} (hu : 0 < u) (hsmall : 2 * u ≤ y) :
    ((y : ℝ) / (4 * Real.log (y : ℝ))) * (u : ℝ)⁻¹ ≤
      (1 / 2 : ℝ) * (((y / u : ℕ) : ℝ) /
        Real.log ((y / u : ℕ) : ℝ)) := by
  have hXtwo : 2 ≤ y / u := by
    apply (Nat.le_div_iff_mul_le hu).2
    simpa [Nat.mul_comm] using hsmall
  have hyTwo : 2 ≤ y := hsmall.trans' (Nat.le_mul_of_pos_right 2 hu)
  have hlogX : 0 < Real.log ((y / u : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y / u by omega))
  have hlogY : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hXY : y / u ≤ y := Nat.div_le_self _ _
  have hlogle : Real.log ((y / u : ℕ) : ℝ) ≤ Real.log (y : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hXY
  have hfloor : (y : ℝ) / (2 * u : ℝ) ≤ (y / u : ℕ) := by
    have hltNat : y < u * (y / u + 1) := Nat.lt_mul_div_succ y hu
    have hlt : (y : ℝ) < (u : ℝ) * ((y / u : ℕ) + 1) := by
      exact_mod_cast hltNat
    have hXone : (1 : ℝ) ≤ (y / u : ℕ) := by exact_mod_cast (show 1 ≤ y / u by omega)
    have huR : (0 : ℝ) < u := by exact_mod_cast hu
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hratio : ((y : ℝ) / (2 * u : ℝ)) / Real.log (y : ℝ) ≤
      ((y / u : ℕ) : ℝ) / Real.log ((y / u : ℕ) : ℝ) := by
    exact div_le_div₀ (by positivity) hfloor hlogX hlogle
  calc
    ((y : ℝ) / (4 * Real.log (y : ℝ))) * (u : ℝ)⁻¹ =
        (1 / 2 : ℝ) *
          (((y : ℝ) / (2 * u : ℝ)) / Real.log (y : ℝ)) := by
            field_simp [show (u : ℝ) ≠ 0 by exact_mod_cast hu.ne']
            <;> ring
    _ ≤ (1 / 2 : ℝ) * (((y / u : ℕ) : ℝ) /
        Real.log ((y / u : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hratio (by norm_num)

/-! ## A uniform divisor-reciprocal lower bound -/

private lemma inv_sq_le_telescope (k : ℕ) (hk : 3 ≤ k) :
    ((k : ℝ) ^ 2)⁻¹ ≤ ((k - 1 : ℕ) : ℝ)⁻¹ - (k : ℝ)⁻¹ := by
  have hkR : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hkmNat : 0 < k - 1 := by omega
  have hkmR : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast hkmNat
  rw [inv_sub_inv hkmR.ne' (zero_lt_one.trans hkR).ne']
  have hkCast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hkCast]
  have hnum : (k : ℝ) - ((k : ℝ) - 1) = 1 := by ring
  rw [hnum, one_div]
  have hkpos : (0 : ℝ) < k := zero_lt_one.trans hkR
  have hden : 0 < ((k : ℝ) - 1) * k :=
    mul_pos (sub_pos.mpr hkR) hkpos
  simp only [inv_eq_one_div]
  rw [div_le_div_iff₀ (sq_pos_of_pos hkpos) hden]
  nlinarith

private lemma sum_range_add_three_inv_sq_le_half (N : ℕ) :
    (∑ j ∈ Finset.range N, ((((j + 3 : ℕ) : ℝ) ^ 2)⁻¹)) ≤ 1 / 2 := by
  have hstrong : ∀ N : ℕ,
      (∑ j ∈ Finset.range N, ((((j + 3 : ℕ) : ℝ) ^ 2)⁻¹)) ≤
        1 / 2 - (((N + 2 : ℕ) : ℝ))⁻¹ := by
    intro M
    induction M with
    | zero => norm_num
    | succ M ih =>
        rw [Finset.sum_range_succ]
        have hterm := inv_sq_le_telescope (M + 3) (by omega)
        have hcast : ((M + 3 - 1 : ℕ) : ℝ) = (M + 2 : ℕ) := by
          norm_num
        rw [hcast] at hterm
        norm_num only [Nat.cast_add, Nat.cast_ofNat] at ih hterm ⊢
        calc
          (∑ j ∈ Finset.range M, ((↑j + (3 : ℝ)) ^ 2)⁻¹) +
                ((↑M + (3 : ℝ)) ^ 2)⁻¹ ≤
              ((1 / 2 : ℝ) - (↑M + (2 : ℝ))⁻¹) +
                ((↑M + (2 : ℝ))⁻¹ - (↑M + (3 : ℝ))⁻¹) :=
            add_le_add ih hterm
          _ = (1 / 2 : ℝ) - (↑M + 1 + 2)⁻¹ := by ring
  exact (hstrong N).trans (sub_le_self _ (by positivity))

private lemma sum_prime_inv_sq_le_three_four (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    ∑ p ∈ s, (((p : ℝ) ^ 2)⁻¹) ≤ 3 / 4 := by
  by_cases hempty : s = ∅
  · subst s
    norm_num
  have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  let t := s.erase 2
  have ht : t ⊆ Finset.Icc 3 (s.max' hsne) := by
    intro p hp
    have hps : p ∈ s := Finset.mem_of_mem_erase hp
    have hpne : p ≠ 2 := (Finset.mem_erase.mp hp).1
    have hp3 : 3 ≤ p := by
      have := (hs p hps).two_le
      omega
    exact Finset.mem_Icc.mpr
      ⟨hp3,
        Finset.le_max' s p hps⟩
  have hIcc :
      (∑ k ∈ Finset.Icc 3 (s.max' hsne), (((k : ℝ) ^ 2)⁻¹)) ≤ 1 / 2 := by
    let M := s.max' hsne + 1 - 3
    have hrewrite : Finset.Icc 3 (s.max' hsne) =
        (Finset.range M).image (fun j ↦ j + 3) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range, M]
      constructor
      · rintro ⟨hk3, hkmax⟩
        refine ⟨k - 3, ?_, by omega⟩
        omega
      · rintro ⟨j, hj, rfl⟩
        omega
    rw [hrewrite, Finset.sum_image]
    · exact sum_range_add_three_inv_sq_le_half M
    · intro a ha b hb hab
      change a + 3 = b + 3 at hab
      omega
  have htSum : (∑ p ∈ t, (((p : ℝ) ^ 2)⁻¹)) ≤ 1 / 2 := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg ht
      (fun p hp hpt ↦ inv_nonneg.mpr (sq_nonneg (p : ℝ)))).trans hIcc
  by_cases htwo : 2 ∈ s
  · rw [← Finset.sum_erase_add _ _ htwo]
    change (∑ p ∈ t, (((p : ℝ) ^ 2)⁻¹)) + ((2 : ℝ) ^ 2)⁻¹ ≤ 3 / 4
    norm_num
    linarith
  · have hterase : t = s := Finset.erase_eq_self.mpr htwo
    rw [hterase] at htSum
    exact htSum.trans (by norm_num)

private lemma one_sub_sum_le_prod_one_sub
    {s : Finset ℕ} {a : ℕ → ℝ}
    (ha0 : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      have hai0 := ha0 i (by simp)
      have hai1 := ha1 i (by simp)
      have hs0 : 0 ≤ ∑ j ∈ s, a j :=
        Finset.sum_nonneg (fun j hj ↦ ha0 j (by simp [hj]))
      have hih := ih (fun j hj ↦ ha0 j (by simp [hj]))
        (fun j hj ↦ ha1 j (by simp [hj]))
      calc
        1 - (a i + ∑ j ∈ s, a j) ≤
            (1 - a i) * (1 - ∑ j ∈ s, a j) := by nlinarith
        _ ≤ (1 - a i) * ∏ j ∈ s, (1 - a j) :=
          mul_le_mul_of_nonneg_left hih (sub_nonneg.mpr hai1)

private lemma primeFactors_squareEulerProduct_lower (n : ℕ) :
    1 / 4 ≤ ∏ p ∈ n.primeFactors, (1 - (((p : ℝ) ^ 2)⁻¹)) := by
  have hsum := sum_prime_inv_sq_le_three_four n.primeFactors
    (fun p hp ↦ Nat.prime_of_mem_primeFactors hp)
  have hprod := one_sub_sum_le_prod_one_sub
    (s := n.primeFactors) (a := fun p ↦ (((p : ℝ) ^ 2)⁻¹))
    (by
      intro p hp
      exact inv_nonneg.mpr (sq_nonneg (p : ℝ)))
    (by
      intro p hp
      have hp2 : (2 : ℝ) ≤ p := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      have hp0 : (0 : ℝ) < p := by positivity
      rw [inv_le_one₀ (sq_pos_of_pos hp0)]
      nlinarith)
  linarith

private lemma prod_one_add_inv_eq_ratio_mul_squareEuler
    {n : ℕ} (hn : 0 < n) :
    (∏ p ∈ n.primeFactors, (1 + (p : ℝ)⁻¹)) =
      ((n : ℝ) / Nat.totient n) *
        ∏ p ∈ n.primeFactors, (1 - (((p : ℝ) ^ 2)⁻¹)) := by
  rw [Erdos4.cofactor_ratio_eq_primeFactors_product n hn.ne',
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpPrime := Nat.prime_of_mem_primeFactors hp
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpPrime.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hpPrime.ne_one)
  field_simp [hp0, hp1]
  ring

/-- The full reciprocal divisor sum is at least a fixed fraction of the
totient ratio.  The constant `1/4` is deliberately elementary. -/
theorem totientRatio_quarter_le_sum_divisors_inv
    {n : ℕ} (hn : 0 < n) :
    (1 / 4 : ℝ) * ((n : ℝ) / Nat.totient n) ≤
      ∑ u ∈ n.divisors, (u : ℝ)⁻¹ := by
  let P := ∏ p ∈ n.primeFactors, p
  have hPdvd : P ∣ n := Nat.prod_primeFactors_dvd n
  have hP0 : P ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hPsq : Squarefree P := by
    dsimp [P]
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro p hp q hq hpq
      change IsRelPrime p q
      exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes
        (Nat.prime_of_mem_primeFactors hp)
        (Nat.prime_of_mem_primeFactors hq)).mpr hpq)
    · intro p hp
      exact (Nat.prime_of_mem_primeFactors hp).squarefree
  have hPpf : P.primeFactors = n.primeFactors := by
    dsimp [P]
    exact Nat.primeFactors_prod
      (fun p hp ↦ Nat.prime_of_mem_primeFactors hp)
  have hEuler :
      (∑ d ∈ P.divisors, (d : ℝ)⁻¹) =
        ∏ p ∈ n.primeFactors, (1 + (p : ℝ)⁻¹) := by
    rw [Erdos387.divisors_eq_image_prod_primeFactorSubsets hPsq,
      Finset.sum_image (Erdos387.prod_primeFactorSubsets_injOn P),
      hPpf, Finset.prod_one_add]
    apply Finset.sum_congr rfl
    intro T hT
    push_cast
    exact (Finset.prod_inv_distrib (s := T) (fun p : ℕ ↦ (p : ℝ))).symm
  have hsub : P.divisors ⊆ n.divisors :=
    Nat.divisors_subset_of_dvd hn.ne' hPdvd
  have hsumle : (∑ d ∈ P.divisors, (d : ℝ)⁻¹) ≤
      ∑ d ∈ n.divisors, (d : ℝ)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun d hdP hdn ↦ inv_nonneg.mpr (Nat.cast_nonneg d))
  rw [hEuler] at hsumle
  have hprod := primeFactors_squareEulerProduct_lower n
  have hratio0 : 0 ≤ (n : ℝ) / Nat.totient n := by positivity
  rw [prod_one_add_inv_eq_ratio_mul_squareEuler hn]
    at hsumle
  simpa [mul_comm] using
    (mul_le_mul_of_nonneg_left hprod hratio0).trans hsumle

/-- Reciprocal mass of divisors above `U` is bounded by their number times
`1/(U+1)`. -/
lemma sum_large_divisors_inv_le (n U : ℕ) :
    (∑ u ∈ n.divisors.filter (fun u ↦ U < u), (u : ℝ)⁻¹) ≤
      (n.divisors.card : ℝ) / (U + 1) := by
  calc
    (∑ u ∈ n.divisors.filter (fun u ↦ U < u), (u : ℝ)⁻¹) ≤
        ∑ _u ∈ n.divisors.filter (fun u ↦ U < u),
          (((U + 1 : ℕ) : ℝ))⁻¹ := by
      apply Finset.sum_le_sum
      intro u hu
      have huU : U + 1 ≤ u := by
        exact Nat.add_one_le_iff.mpr (Finset.mem_filter.mp hu).2
      exact inv_anti₀ (by positivity) (by exact_mod_cast huU)
    _ = ((n.divisors.filter (fun u ↦ U < u)).card : ℝ) /
          (U + 1) := by
      simp [div_eq_mul_inv]
    _ ≤ (n.divisors.card : ℝ) / (U + 1) := by
      exact div_le_div_of_nonneg_right
        (by exact_mod_cast Finset.card_filter_le n.divisors (fun u ↦ U < u))
        (by positivity)

lemma sum_divisors_inv_eq_bounded_add_large {n U : ℕ} (hn : n ≠ 0) :
    (∑ u ∈ n.divisors, (u : ℝ)⁻¹) =
      (∑ u ∈ boundedTargetDivisors n U, (u : ℝ)⁻¹) +
        ∑ u ∈ n.divisors.filter (fun u ↦ U < u), (u : ℝ)⁻¹ := by
  rw [boundedTargetDivisors]
  have hsplit := Finset.sum_filter_add_sum_filter_not n.divisors
    (fun u ↦ u ≤ U) (fun u ↦ (u : ℝ)⁻¹)
  simpa only [not_le] using hsplit.symm

/-- Once the standard divisor-count tail is at most one eighth of the
totient ratio, the bounded divisors retain one eighth of that ratio. -/
theorem totientRatio_eighth_le_sum_boundedTargetDivisors_inv
    {n U : ℕ} (hn : 0 < n)
    (htail : (n.divisors.card : ℝ) / (U + 1) ≤
      (1 / 8 : ℝ) * ((n : ℝ) / Nat.totient n)) :
    (1 / 8 : ℝ) * ((n : ℝ) / Nat.totient n) ≤
      ∑ u ∈ boundedTargetDivisors n U, (u : ℝ)⁻¹ := by
  have hfull := totientRatio_quarter_le_sum_divisors_inv hn
  have hlarge := sum_large_divisors_inv_le n U
  rw [sum_divisors_inv_eq_bounded_add_large (U := U) hn.ne'] at hfull
  have hratio0 : 0 ≤ (n : ℝ) / Nat.totient n := by positivity
  nlinarith

lemma card_boundedTargetDivisors_le (n U : ℕ) :
    (boundedTargetDivisors n U).card ≤ U := by
  have hsub : boundedTargetDivisors n U ⊆ Finset.Icc 1 U := by
    intro u hu
    have hdata := mem_boundedTargetDivisors.mp hu
    exact Finset.mem_Icc.mpr
      ⟨Nat.pos_of_dvd_of_pos hdata.1 (Nat.pos_of_ne_zero hdata.2.1),
        hdata.2.2⟩
  exact (Finset.card_le_card hsub).trans_eq (by simp)

lemma primeFactors_card_le_divisors_card {n : ℕ} (hn : n ≠ 0) :
    n.primeFactors.card ≤ n.divisors.card := by
  apply Finset.card_le_card
  intro p hp
  exact Nat.mem_divisors.mpr
    ⟨Nat.dvd_of_mem_primeFactors hp, hn⟩

/-- Two polynomial inequalities imply both error budgets used by the direct
prime count.  This is the convenient finite interface for asymptotic
discharge: `τ(n)=n^{o(1)}` and `U=y^{1/16}` make both inequalities immediate. -/
lemma directPrime_error_budgets_of_divisor_bounds
    {n y U : ℕ} (hn : 0 < n) (hlogy : 0 < Real.log (y : ℝ))
    (htailSimple : (8 : ℝ) * n.divisors.card ≤ U + 1)
    (hdeleteSimple : (64 : ℝ) * U * n.divisors.card *
      Real.log (y : ℝ) ≤ y) :
    (n.divisors.card : ℝ) / (U + 1) ≤
        (1 / 8 : ℝ) * ((n : ℝ) / Nat.totient n) ∧
      ((boundedTargetDivisors n U).card : ℝ) *
          n.primeFactors.card ≤
        ((n : ℝ) / Nat.totient n) * (y : ℝ) /
          (64 * Real.log (y : ℝ)) := by
  have hphi : Nat.totient n ≤ n := Nat.totient_le n
  have hphiPos : (0 : ℝ) < Nat.totient n := by
    exact_mod_cast Nat.totient_pos.mpr hn
  have hratio : (1 : ℝ) ≤ (n : ℝ) / Nat.totient n := by
    rw [le_div_iff₀ hphiPos]
    simpa only [one_mul] using
      (Nat.cast_le.mpr hphi : (Nat.totient n : ℝ) ≤ n)
  have hUden : (0 : ℝ) < U + 1 := by positivity
  constructor
  · calc
      (n.divisors.card : ℝ) / (U + 1) ≤ 1 / 8 := by
        rw [div_le_iff₀ hUden]
        nlinarith
      _ ≤ (1 / 8 : ℝ) * ((n : ℝ) / Nat.totient n) := by
        nlinarith
  · have hcardB : ((boundedTargetDivisors n U).card : ℝ) ≤ U := by
      exact_mod_cast card_boundedTargetDivisors_le n U
    have hcardP : (n.primeFactors.card : ℝ) ≤ n.divisors.card := by
      exact_mod_cast primeFactors_card_le_divisors_card hn.ne'
    have hprod : ((boundedTargetDivisors n U).card : ℝ) *
        n.primeFactors.card ≤ (U : ℝ) * n.divisors.card := by
      exact mul_le_mul hcardB hcardP (by positivity) (by positivity)
    have hbase : (U : ℝ) * n.divisors.card ≤
        (y : ℝ) / (64 * Real.log (y : ℝ)) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    calc
      ((boundedTargetDivisors n U).card : ℝ) * n.primeFactors.card ≤
          (U : ℝ) * n.divisors.card := hprod
      _ ≤ (y : ℝ) / (64 * Real.log (y : ℝ)) := hbase
      _ ≤ ((n : ℝ) / Nat.totient n) * (y : ℝ) /
          (64 * Real.log (y : ℝ)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hfactor : (0 : ℝ) ≤ (y : ℝ) * (64 * Real.log (y : ℝ)) := by
          positivity
        simpa only [one_mul, mul_assoc] using
          (mul_le_mul_of_nonneg_right hratio hfactor)

/-- Finite analytic closure of the direct-prime count.  The only remaining
side conditions are transparent range conditions: PNT is valid in every
fibre, every retained divisor is at most `y/2`, the divisor-reciprocal tail
is small, and the deletion of target prime factors fits in half the main
term. -/
theorem ratio_y_div_log_le_primeStructuredTestSet_card
    {n y U T : ℕ} (hn : 0 < n) (hU : 0 < U)
    (hPNT : ∀ X : ℕ, T ≤ X →
      (1 / 2 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)) ≤
        ((Erdos446.dyadicPrimes X).card : ℝ))
    (hscale : ∀ u ∈ boundedTargetDivisors n U, T ≤ y / u)
    (hsmall : ∀ u ∈ boundedTargetDivisors n U, 2 * u ≤ y)
    (htail : (n.divisors.card : ℝ) / (U + 1) ≤
      (1 / 8 : ℝ) * ((n : ℝ) / Nat.totient n))
    (herror : ((boundedTargetDivisors n U).card : ℝ) *
        n.primeFactors.card ≤
      ((n : ℝ) / Nat.totient n) * (y : ℝ) /
        (64 * Real.log (y : ℝ))) :
    ((n : ℝ) / Nat.totient n) * (y : ℝ) /
        (64 * Real.log (y : ℝ)) ≤
      ((primeStructuredTestSet n y U).card : ℝ) := by
  have hsum := sum_primeNumberTheorem_lower_le_primeStructuredTestSet
    hPNT hscale
  have hrecip :=
    totientRatio_eighth_le_sum_boundedTargetDivisors_inv hn htail
  have hone : 1 ∈ boundedTargetDivisors n U :=
    mem_boundedTargetDivisors.mpr ⟨one_dvd n, hn.ne', hU⟩
  have hlogY : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by
      exact_mod_cast (show 1 < y by
        have := hsmall 1 hone
        omega))
  have hmain :
      ((n : ℝ) / Nat.totient n) * (y : ℝ) /
          (32 * Real.log (y : ℝ)) ≤
        ∑ u ∈ boundedTargetDivisors n U,
          (1 / 2 : ℝ) * (((y / u : ℕ) : ℝ) /
            Real.log ((y / u : ℕ) : ℝ)) := by
    calc
      ((n : ℝ) / Nat.totient n) * (y : ℝ) /
            (32 * Real.log (y : ℝ)) =
          ((y : ℝ) / (4 * Real.log (y : ℝ))) *
            ((1 / 8 : ℝ) * ((n : ℝ) / Nat.totient n)) := by ring
      _ ≤ ((y : ℝ) / (4 * Real.log (y : ℝ))) *
            (∑ u ∈ boundedTargetDivisors n U, (u : ℝ)⁻¹) := by
        exact mul_le_mul_of_nonneg_left hrecip (by positivity)
      _ = ∑ u ∈ boundedTargetDivisors n U,
            (((y : ℝ) / (4 * Real.log (y : ℝ))) * (u : ℝ)⁻¹) := by
        simp [Finset.mul_sum]
      _ ≤ ∑ u ∈ boundedTargetDivisors n U,
          (1 / 2 : ℝ) * (((y / u : ℕ) : ℝ) /
            Real.log ((y / u : ℕ) : ℝ)) := by
        apply Finset.sum_le_sum
        intro u hu
        exact quarter_y_log_inv_le_dyadic_main
          (boundedTargetDivisor_pos hu) (hsmall u hu)
  rw [Finset.sum_sub_distrib] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  have hdouble :
      2 * (((n : ℝ) / Nat.totient n) * (y : ℝ) /
        (64 * Real.log (y : ℝ))) =
      ((n : ℝ) / Nat.totient n) * (y : ℝ) /
        (32 * Real.log (y : ℝ)) := by ring
  linarith

/-- CFP Lemma 5.2-sized form of the prime-only count.  The harmless constant
`512` leaves room for the divisor truncation and for deleting the prime
divisors of the target.  The logarithmic comparison is separated because it
is supplied by the canonical diagonal parameter estimates. -/
theorem initialMissingEulerProduct_mul_y_div_le_primeStructuredTestSet_card
    {n h y U T : ℕ} (hn : 0 < n) (hU : 0 < U)
    (hMertens : InitialMissingMertensBounds n h)
    (hlog : Real.log (y : ℝ) ≤ 4 * Real.log (h : ℝ))
    (hPNT : ∀ X : ℕ, T ≤ X →
      (1 / 2 : ℝ) * ((X : ℝ) / Real.log (X : ℝ)) ≤
        ((Erdos446.dyadicPrimes X).card : ℝ))
    (hscale : ∀ u ∈ boundedTargetDivisors n U, T ≤ y / u)
    (hsmall : ∀ u ∈ boundedTargetDivisors n U, 2 * u ≤ y)
    (htail : (n.divisors.card : ℝ) / (U + 1) ≤
      (1 / 8 : ℝ) * ((n : ℝ) / Nat.totient n))
    (herror : ((boundedTargetDivisors n U).card : ℝ) *
        n.primeFactors.card ≤
      ((n : ℝ) / Nat.totient n) * (y : ℝ) /
        (64 * Real.log (y : ℝ))) :
    initialMissingEulerProduct n h * (y : ℝ) / 512 ≤
      ((primeStructuredTestSet n y U).card : ℝ) := by
  have hcount := ratio_y_div_log_le_primeStructuredTestSet_card
    hn hU hPNT hscale hsmall htail herror
  have hV := hMertens.2.2
  have hlogh : 0 < Real.log (h : ℝ) := hMertens.1
  have hone : 1 ∈ boundedTargetDivisors n U :=
    mem_boundedTargetDivisors.mpr ⟨one_dvd n, hn.ne', hU⟩
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by
      exact_mod_cast (show 1 < y by
        have := hsmall 1 hone
        omega))
  have hratio : 0 < (n : ℝ) / Nat.totient n := by positivity
  have hy0 : (0 : ℝ) ≤ y := by positivity
  calc
    initialMissingEulerProduct n h * (y : ℝ) / 512 ≤
        (2 * ((n : ℝ) / Nat.totient n) /
          Real.log (h : ℝ)) * (y : ℝ) / 512 := by
      gcongr
    _ = ((n : ℝ) / Nat.totient n) * (y : ℝ) /
          (256 * Real.log (h : ℝ)) := by field_simp; ring
    _ ≤ ((n : ℝ) / Nat.totient n) * (y : ℝ) /
          (64 * Real.log (y : ℝ)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg hratio.le hy0]
    _ ≤ ((primeStructuredTestSet n y U).card : ℝ) := hcount

end Erdos360
