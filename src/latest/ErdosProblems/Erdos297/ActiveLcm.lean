/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos297.GoodFactorization

/-!
# Erdős Problem 297: the active common denominator

The Fourier argument must use only the prime powers which actually occur as
exact prime-power parts of a denominator in the selected set `A`.  In
particular, it must not replace this set by all prime powers below the global
smoothness cutoff before performing the fixed-`D` count.

This file packages that correction.  `activePrimePowers A` is the set called
`ppowers_in_set A` in the unit-fraction library, and `activeLcm A` is its LCM.
For a positive set `A`, this is exactly the ordinary LCM of `A`.  We also give
the denominator-clearing and omitted-prime-power divisibility statements used
on the minor arcs.
-/

namespace Erdos297.ActiveLcm

open Finset
open Erdos285.PrimePowers
open Erdos297.GoodFactorization
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The exact prime-power parts which occur in at least one denominator of
`A`.  These are the *active* prime powers in the Fourier argument. -/
def activePrimePowers (A : Finset ℕ) : Finset ℕ :=
  UnitFractions.ppowers_in_set A

/-- The common denominator made from the active prime powers. -/
def activeLcm (A : Finset ℕ) : ℕ :=
  (activePrimePowers A).lcm id

@[simp] lemma mem_activePrimePowers {A : Finset ℕ} {q : ℕ} :
    q ∈ activePrimePowers A ↔
      IsPrimePow q ∧ ∃ n ∈ A, q ∣ n ∧ Nat.Coprime q (n / q) := by
  rw [activePrimePowers, UnitFractions.mem_ppowers_in_set]
  constructor
  · rintro ⟨hq, ⟨n, hn⟩⟩
    exact ⟨hq, n, (mem_exactLocalPart.mp hn).1,
      (mem_exactLocalPart.mp hn).2.1, (mem_exactLocalPart.mp hn).2.2⟩
  · rintro ⟨hq, n, hnA, hqn, hcop⟩
    exact ⟨hq, ⟨n, mem_exactLocalPart.mpr ⟨hnA, hqn, hcop⟩⟩⟩

lemma activePrimePower_isPrimePow {A : Finset ℕ} {q : ℕ}
    (hq : q ∈ activePrimePowers A) : IsPrimePow q :=
  (mem_activePrimePowers.mp hq).1

/-- Every active prime power has a denominator in which it occurs as the
exact part; in particular it divides that denominator. -/
lemma exists_mem_and_dvd_of_mem_activePrimePowers {A : Finset ℕ} {q : ℕ}
    (hq : q ∈ activePrimePowers A) : ∃ n ∈ A, q ∣ n := by
  obtain ⟨_, n, hn, hqn, _⟩ := mem_activePrimePowers.mp hq
  exact ⟨n, hn, hqn⟩

lemma zero_not_mem_activePrimePowers (A : Finset ℕ) :
    0 ∉ activePrimePowers A := by
  intro h0
  exact (activePrimePower_isPrimePow h0).ne_zero rfl

/-- The active LCM is positive, including when the active set is empty (whose
finite LCM is `1`). -/
lemma activeLcm_pos (A : Finset ℕ) : 0 < activeLcm A := by
  rw [activeLcm]
  exact Nat.pos_iff_ne_zero.mpr
    (UnitFractions.lcm_ne_zero_of_zero_not_mem
      (zero_not_mem_activePrimePowers A))

lemma activeLcm_ne_zero (A : Finset ℕ) : activeLcm A ≠ 0 :=
  (activeLcm_pos A).ne'

/-- For a set without zero, taking the LCM of its exact prime-power parts is
the same as taking the LCM of the original denominators. -/
lemma activeLcm_eq_lcm {A : Finset ℕ} (hA0 : 0 ∉ A) :
    activeLcm A = A.lcm id := by
  change UnitFractions.lcmA (UnitFractions.ppowers_in_set A) =
    UnitFractions.lcmA A
  exact UnitFractions.lcm_Q hA0

lemma dvd_activeLcm_of_mem {A : Finset ℕ} (hA0 : 0 ∉ A)
    {n : ℕ} (hn : n ∈ A) : n ∣ activeLcm A := by
  rw [activeLcm_eq_lcm hA0]
  exact Finset.dvd_lcm hn

lemma dvd_activeLcm_of_mem_of_pos {A : Finset ℕ}
    (hApos : ∀ n ∈ A, 0 < n) {n : ℕ} (hn : n ∈ A) :
    n ∣ activeLcm A := by
  apply dvd_activeLcm_of_mem
  · intro h0
    have := hApos 0 h0
    omega
  · exact hn

/-! ## Bounds inherited from the selected good denominators -/

lemma activePrimePowers_subset_smoothPrimePowers {N M S : ℕ}
    {A : Finset ℕ} (hM : 1 ≤ M)
    (hA : A ⊆ goodDenominators N M S) :
    activePrimePowers A ⊆ smoothPrimePowers S := by
  intro q hq
  obtain ⟨hqpp, n, hnA, hqn, _⟩ := mem_activePrimePowers.mp hq
  have hnGood := hA hnA
  exact mem_primePowersUpTo.mpr ⟨hqpp,
    primePowerDivisor_le_of_smooth
      (goodDenominator_pos hM hnGood).ne'
      (goodDenominator_smooth hnGood) hqpp hqn⟩

lemma activePrimePower_le_smoothCutoff {N M S : ℕ} {A : Finset ℕ}
    (hM : 1 ≤ M) (hA : A ⊆ goodDenominators N M S)
    {q : ℕ} (hq : q ∈ activePrimePowers A) : q ≤ S :=
  (mem_primePowersUpTo.mp
    (activePrimePowers_subset_smoothPrimePowers hM hA hq)).2

lemma activePrimePower_le_N {N M S : ℕ} {A : Finset ℕ}
    (hM : 1 ≤ M) (hA : A ⊆ goodDenominators N M S)
    {q : ℕ} (hq : q ∈ activePrimePowers A) : q ≤ N := by
  obtain ⟨n, hnA, hqn⟩ := exists_mem_and_dvd_of_mem_activePrimePowers hq
  have hnGood := hA hnA
  exact (Nat.le_of_dvd (goodDenominator_pos hM hnGood) hqn).trans
    (mem_goodDenominators.mp hnGood).2.1

/-- The exponent of every active prime power respects the pointwise exponent
bound imposed on the selected good denominators. -/
lemma activePrimePower_exponent_le {N M S : ℕ} {A : Finset ℕ}
    (hM : 1 ≤ M) (hA : A ⊆ goodDenominators N M S)
    {q : ℕ} (hq : q ∈ activePrimePowers A) :
    ∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ q = p ^ k ∧ k ≤ exponentBound N := by
  obtain ⟨hqpp, n, hnA, hqn, hcop⟩ := mem_activePrimePowers.mp hq
  obtain ⟨p, k, hp, hk, hqpow⟩ := (isPrimePow_nat_iff q).mp hqpp
  have hnGood := hA hnA
  have hfac : n.factorization p = k := by
    apply (UnitFractions.factorization_eq_iff hp hk.ne').mp
    simpa [hqpow] using And.intro hqn hcop
  have hpSupport : p ∈ n.factorization.support := by
    rw [Finsupp.mem_support_iff, hfac]
    omega
  have hkle : k ≤ maxPrimeExponent n := by
    rw [maxPrimeExponent]
    rw [← hfac]
    exact Finset.le_sup (f := fun r ↦ n.factorization r) hpSupport
  exact ⟨p, k, hp, hk, hqpow.symm,
    hkle.trans (goodDenominator_exponentBound hnGood)⟩

lemma activeLcm_dvd_smoothLcm {N M S : ℕ} {A : Finset ℕ}
    (hM : 1 ≤ M) (hA : A ⊆ goodDenominators N M S) :
    activeLcm A ∣ smoothLcm S := by
  have hA0 : 0 ∉ A := by
    intro h0
    have := goodDenominator_pos hM (hA h0)
    omega
  rw [activeLcm_eq_lcm hA0]
  exact lcm_dvd_smoothLcm hM hA

lemma activeLcm_le_smoothLcm {N M S : ℕ} {A : Finset ℕ}
    (hM : 1 ≤ M) (hA : A ⊆ goodDenominators N M S) :
    activeLcm A ≤ smoothLcm S := by
  apply Nat.le_of_dvd
  · exact Nat.pos_of_ne_zero (by simp [smoothLcm, initialLcm])
  · exact activeLcm_dvd_smoothLcm hM hA

/-! ## Exact denominator clearing with the active LCM -/

lemma activeLcm_mul_one_div {A : Finset ℕ} {n : ℕ}
    (hn0 : n ≠ 0) (hn : n ∣ activeLcm A) :
    (activeLcm A : ℚ) * ((1 : ℚ) / n) =
      (activeLcm A / n : ℕ) := by
  field_simp [hn0]
  exact_mod_cast (by
    simpa [Nat.mul_comm] using (Nat.div_mul_cancel hn).symm)

lemma activeLcm_mul_recSum {A B : Finset ℕ} (hA0 : 0 ∉ A)
    (hBA : B ⊆ A) :
    (activeLcm A : ℚ) * UnitFractions.rec_sum B =
      ∑ n ∈ B, ((activeLcm A / n : ℕ) : ℚ) := by
  rw [UnitFractions.rec_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hnB
  exact activeLcm_mul_one_div
    (fun hn0 ↦ hA0 (hn0 ▸ hBA hnB))
    (dvd_activeLcm_of_mem hA0 (hBA hnB))

lemma activeLcm_mul_recSum_good {N M S : ℕ} {A B : Finset ℕ}
    (hM : 1 ≤ M) (hA : A ⊆ goodDenominators N M S) (hBA : B ⊆ A) :
    (activeLcm A : ℚ) * UnitFractions.rec_sum B =
      ∑ n ∈ B, ((activeLcm A / n : ℕ) : ℚ) := by
  apply activeLcm_mul_recSum
  · intro h0
    have := goodDenominator_pos hM (hA h0)
    omega
  · exact hBA

/-! ## Removing a fixed family of active prime powers -/

lemma lcm_subset_dvd_activeLcm {A D : Finset ℕ}
    (hD : D ⊆ activePrimePowers A) : D.lcm id ∣ activeLcm A := by
  rw [activeLcm]
  exact Finset.lcm_dvd fun q hq ↦ Finset.dvd_lcm (hD hq)

/-- Omitting the active prime powers in `D` costs at most the product of the
remaining active prime powers.  This is the exact divisibility statement
behind fixed-`D` minor-arc counting. -/
lemma activeLcm_dvd_complement_prod_mul_lcm (A D : Finset ℕ) :
    activeLcm A ∣ (activePrimePowers A \ D).prod id * D.lcm id := by
  rw [activeLcm]
  apply Finset.lcm_dvd
  intro q hq
  by_cases hqD : q ∈ D
  · exact dvd_mul_of_dvd_right (Finset.dvd_lcm hqD) _
  · exact dvd_mul_of_dvd_left
      (dvd_prod_of_mem id (Finset.mem_sdiff.mpr ⟨hq, hqD⟩)) _

lemma activeLcm_div_lcm_le_complement_prod {A D : Finset ℕ}
    (hD : D ⊆ activePrimePowers A) :
    activeLcm A / D.lcm id ≤ (activePrimePowers A \ D).prod id := by
  apply Nat.div_le_of_le_mul
  have hpos : 0 < (activePrimePowers A \ D).prod id * D.lcm id := by
    apply Nat.mul_pos
    · exact Finset.prod_pos fun q hq ↦
        (activePrimePower_isPrimePow (Finset.mem_sdiff.mp hq).1).pos
    · apply Nat.pos_iff_ne_zero.mpr
      apply UnitFractions.lcm_ne_zero_of_zero_not_mem
      intro h0
      exact (activePrimePower_isPrimePow (hD h0)).ne_zero rfl
  simpa [Nat.mul_comm] using Nat.le_of_dvd hpos
    (activeLcm_dvd_complement_prod_mul_lcm A D)

lemma complement_prod_le_pow {N : ℕ} {A D : Finset ℕ}
    (hN : ∀ q ∈ activePrimePowers A, q ≤ N) :
    (activePrimePowers A \ D).prod id ≤
      N ^ (activePrimePowers A \ D).card := by
  simpa using Finset.prod_le_pow_card
    (s := activePrimePowers A \ D) (f := id) (n := N)
    (fun q hq ↦ hN q (Finset.mem_sdiff.mp hq).1)

lemma complement_prod_good_le_pow {N M S : ℕ} {A D : Finset ℕ}
    (hM : 1 ≤ M) (hA : A ⊆ goodDenominators N M S) :
    (activePrimePowers A \ D).prod id ≤
      N ^ (activePrimePowers A \ D).card := by
  exact complement_prod_le_pow
    (fun q hq ↦ activePrimePower_le_N hM hA hq)

end

end Erdos297.ActiveLcm

#print axioms Erdos297.ActiveLcm.activeLcm_mul_recSum_good
#print axioms Erdos297.ActiveLcm.activeLcm_div_lcm_le_complement_prod
