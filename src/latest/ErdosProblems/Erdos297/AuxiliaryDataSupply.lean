/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos297.AuxiliarySupply
import ErdosProblems.Erdos297.MinorArc
import ErdosProblems.Erdos297.PrimeIntervals
import ErdosProblems.Erdos297.SmoothMultiple

/-!
# Finite assembly of auxiliary-prime data for Erdős Problem 297

This file joins the exact finite inputs of the repaired auxiliary-prime
sieve.  For each active prime power it chooses the averaged prime `p'`,
extends `q * p'` to a base modulus, keeps the eligible primes in one common
prime band, and uses a genuine nearby multiple for every eligible prime.
The interval-width argument then shows that all these multiples give the
same integer.  The result is exactly the `AuxiliaryData` object consumed by
`MinorArc.commonNearbyMultiple_of_auxiliaryData`.
-/

namespace Erdos297.AuxiliaryDataSupply

open Finset
open scoped ArithmeticFunction.Omega BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

open ActiveLcm AuxiliarySupply GoodFactorization MinorArc NearbyMultiple

/-- Distinct natural primes which all divide an integer have a product
which divides that integer. -/
lemma int_coe_prod_dvd_of_primes
    {P : Finset ℕ} {z : ℤ}
    (hprime : ∀ p ∈ P, p.Prime)
    (hdvd : ∀ p ∈ P, (p : ℤ) ∣ z) :
    (((P.prod id : ℕ) : ℤ)) ∣ z := by
  have hpair : (P : Set ℕ).Pairwise (Function.onFun Nat.Coprime id) := by
    intro p hp r hr hne
    exact (Nat.coprime_primes (hprime p hp) (hprime r hr)).mpr hne
  rw [← Finset.lcm_eq_prod hpair]
  exact int_coe_lcm_dvd_of_forall P id z hdvd

/-- The exact finite conversion from the repaired sieve inputs to the
package used by the common-nearby-multiple theorem.

`hactive` is the finite certificate carried by every active prime power.
`hcandidateBudget` is the repaired strict pigeonhole inequality; in
particular, no asymptotic prime count is hidden in this theorem.
`hgoodMultiple` is the nonvacuity input: every prime which survives the
coprimality filter has an actual multiple in `A`. -/
theorem exists_auxiliaryData_of_card_conditions
    {N S K X F B : ℕ} {A D P : Finset ℕ}
    {h lower upper : ℤ}
    (hactive : ∀ q ∈ D, ∃ a k : ℕ,
      a.Prime ∧ 1 ≤ k ∧ q = a ^ k ∧
        k ≤ exponentBound N ∧ q ≤ S)
    (hE : 1 ≤ exponentBound N)
    (hA0 : ∀ n ∈ A, n ≠ 0)
    (hAF : ∀ n ∈ A, Ω n ≤ F)
    (hcandidateBudget : ∀ q ∈ D,
      (divisiblePart A q \ nearbySet A h K q).card * F <
        (smallPrimeCandidates X q).card * (B + 1))
    (hXS : X ≤ S)
    (hqXK : ∀ q ∈ D, q * X ≤ K)
    (hcards : ∀ q ∈ D, ∀ p' ∈ smallPrimeCandidates X q,
      ExtensionCardConditions S K (q * p'))
    (hPprime : ∀ p ∈ P, p.Prime)
    (hdensity :
      10 * (F * B + (exponentBound N + 3)) ≤ P.card)
    (hgoodMultiple : ∀ q ∈ D,
      ∀ base : BaseExtension N S K q, ∀ p ∈ P,
        p.Coprime base.base →
          (divisiblePart A (base.base * p)).Nonempty)
    (hnearbyDivisibility : ∀ q ∈ D, ∀ n ∈ nearbySet A h K q,
      ∃ x : ℤ, InHalfOpenInterval lower upper x ∧ (n : ℤ) ∣ x)
    (hintervalExists : ∃ x : ℤ, InHalfOpenInterval lower upper x)
    (hwidthK : upper - lower ≤ (K : ℤ))
    (hKN : K ≤ N)
    (hlargeProduct : ∀ block ⊆ P,
      4 * P.card ≤ 5 * block.card → N < block.prod id) :
    Nonempty (MinorArc.AuxiliaryData D lower upper N) := by
  have hlocal : ∀ q ∈ D, ∃ x : ℤ, ∃ aux : Finset ℕ,
      InHalfOpenInterval lower upper x ∧
        (q : ℤ) ∣ x ∧
        aux ⊆ P ∧
        9 * P.card ≤ 10 * aux.card ∧
        (((aux.prod id : ℕ) : ℤ)) ∣ x := by
    intro q hqD
    let Uq := nearbySet A h K q
    obtain ⟨p', hp'Candidate, hp'Bad⟩ :=
      exists_smallPrimeCandidate_badFiber_le hA0 hAF
        (hcandidateBudget q hqD)
    obtain ⟨a, k, ha, hk, hqpow, hkE, hqS⟩ := hactive q hqD
    have hp'Data := mem_smallPrimeCandidates.mp hp'Candidate
    have hp'S : p' ≤ S := hp'Data.2.1.trans hXS
    have hqp'K : q * p' ≤ K :=
      (Nat.mul_le_mul_left q hp'Data.2.1).trans (hqXK q hqD)
    obtain ⟨base, hbaseSmall⟩ :=
      exists_baseExtension_of_card_conditions ha hk hqpow hkE hE hqS
        hp'Data.2.2.1 hp'Data.2.2.2 hp'S hqp'K
        (hcards q hqD p' hp'Candidate)
    have hseedDvd : q * p' ∣ base.base := by
      simpa [hbaseSmall] using base.source_dvd
    have hbadSubset : divisiblePart A base.base \ Uq ⊆
        badPrimeFiber A Uq q p' := by
      intro n hn
      rw [Finset.mem_sdiff, mem_divisiblePart] at hn
      rw [badPrimeFiber, Finset.mem_sdiff, mem_divisiblePart]
      exact ⟨⟨hn.1.1, dvd_trans hseedDvd hn.1.2⟩, hn.2⟩
    have hbaseBad : (divisiblePart A base.base \ Uq).card ≤ B :=
      (Finset.card_le_card hbadSubset).trans hp'Bad
    have hbase0 : base.base ≠ 0 :=
      Nat.ne_of_gt (Nat.zero_le K |>.trans_lt base.lower)
    let aux := eligibleAuxiliaryPrimes P A Uq base.base
    have hauxSubset : aux ⊆ P :=
      eligibleAuxiliaryPrimes_subset P A Uq base.base
    have hauxDense : 9 * P.card ≤ 10 * aux.card := by
      exact nine_mul_card_le_ten_mul_card_eligibleAuxiliaryPrimes
        hPprime hA0 hAF hbase0 base.factors hbaseBad hdensity
    have hPpos : 0 < P.card := by
      have hpositive : 0 < 10 * (F * B + (exponentBound N + 3)) := by
        positivity
      exact hpositive.trans_le hdensity
    have hauxNonempty : aux.Nonempty := by
      apply Finset.card_pos.mp
      omega
    obtain ⟨p₀, hp₀aux⟩ := hauxNonempty
    have hp₀Data := mem_eligibleAuxiliaryPrimes.mp hp₀aux
    obtain ⟨n₀, hn₀Part⟩ :=
      hgoodMultiple q hqD base p₀ hp₀Data.1 hp₀Data.2.1
    have hn₀U : n₀ ∈ Uq := hp₀Data.2.2 hn₀Part
    obtain ⟨x, hxInterval, hn₀x⟩ :=
      hnearbyDivisibility q hqD n₀ (by simpa [Uq] using hn₀U)
    have hbaseN₀ : base.base ∣ n₀ :=
      dvd_trans (dvd_mul_right base.base p₀) (mem_divisiblePart.mp hn₀Part).2
    have hbaseX : (base.base : ℤ) ∣ x :=
      (Int.natCast_dvd_natCast.mpr hbaseN₀).trans hn₀x
    have hqX : (q : ℤ) ∣ x :=
      (Int.natCast_dvd_natCast.mpr base.q_dvd).trans hbaseX
    have hauxDvd : ∀ p ∈ aux, (p : ℤ) ∣ x := by
      intro p hpaux
      have hpData := mem_eligibleAuxiliaryPrimes.mp hpaux
      obtain ⟨n, hnPart⟩ :=
        hgoodMultiple q hqD base p hpData.1 hpData.2.1
      have hnU : n ∈ Uq := hpData.2.2 hnPart
      obtain ⟨y, hyInterval, hny⟩ :=
        hnearbyDivisibility q hqD n (by simpa [Uq] using hnU)
      have hbaseN : base.base ∣ n :=
        dvd_trans (dvd_mul_right base.base p) (mem_divisiblePart.mp hnPart).2
      have hbaseY : (base.base : ℤ) ∣ y :=
        (Int.natCast_dvd_natCast.mpr hbaseN).trans hny
      have hyx : y = x :=
        eq_of_large_dvd_sub_of_mem_halfOpen hyInterval hxInterval hwidthK
          base.lower (dvd_sub hbaseY hbaseX)
      have hpN : p ∣ n :=
        dvd_trans (dvd_mul_left p base.base) (mem_divisiblePart.mp hnPart).2
      have hpY : (p : ℤ) ∣ y :=
        (Int.natCast_dvd_natCast.mpr hpN).trans hny
      simpa [hyx] using hpY
    refine ⟨x, aux, hxInterval, hqX, hauxSubset, hauxDense, ?_⟩
    exact int_coe_prod_dvd_of_primes
      (fun p hp ↦ hPprime p (hauxSubset hp)) hauxDvd
  let pickX (q : ℕ) (hq : q ∈ D) := Classical.choose (hlocal q hq)
  let pickAux (q : ℕ) (hq : q ∈ D) :=
    Classical.choose (Classical.choose_spec (hlocal q hq))
  let chosen (q : ℕ) : ℤ := if hq : q ∈ D then pickX q hq else 0
  let aux (q : ℕ) : Finset ℕ := if hq : q ∈ D then pickAux q hq else ∅
  refine ⟨{
    chosen := chosen
    primes := P
    aux := aux
    intervalExists := hintervalExists
    width := hwidthK.trans (by exact_mod_cast hKN)
    chosen_mem := ?_
    modulus_dvd := ?_
    aux_subset := ?_
    aux_dense := ?_
    aux_prod_dvd := ?_
    large_product := hlargeProduct }⟩
  · intro q hq
    simpa [chosen, pickX, pickAux, hq] using
      (Classical.choose_spec (Classical.choose_spec (hlocal q hq))).1
  · intro q hq
    simpa [chosen, pickX, pickAux, hq] using
      (Classical.choose_spec (Classical.choose_spec (hlocal q hq))).2.1
  · intro q hq
    simpa [aux, pickX, pickAux, hq] using
      (Classical.choose_spec (Classical.choose_spec (hlocal q hq))).2.2.1
  · intro q hq
    simpa [aux, pickX, pickAux, hq] using
      (Classical.choose_spec (Classical.choose_spec (hlocal q hq))).2.2.2.1
  · intro q hq
    simpa [chosen, aux, pickX, pickAux, hq] using
      (Classical.choose_spec (Classical.choose_spec (hlocal q hq))).2.2.2.2

end

end Erdos297.AuxiliaryDataSupply

#print axioms Erdos297.AuxiliaryDataSupply.exists_auxiliaryData_of_card_conditions
