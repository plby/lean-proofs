import ErdosProblems.Erdos67b.MRHalaszOrdinaryBands
import Mathlib.NumberTheory.LSeries.Linearity

/-!
# Finite prime-mask inclusion-exclusion

The typical coefficient is a finite alternating sum of multiplicative
prime-band restrictions. The identity is stated on positive integers,
which is exactly the domain used by an L-series.
-/

open scoped BigOperators Classical
open Finset

namespace Erdos67b

open MRHalaszBands

noncomputable section

def mrPrimeBlockHit (B : Finset ℕ) (n : ℕ) : Prop := ∃ p ∈ B, p ∣ n

def mrIndexedTypicalCoefficient {ι : Type*} (J : Finset ι) (B : ι → Finset ℕ)
    (f : ℕ → ℂ) (n : ℕ) : ℂ := by
  classical
  exact if ∀ j ∈ J, mrPrimeBlockHit (B j) n then f n else 0

theorem mrPrimeMask_supported_iff {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (B : ι → Finset ℕ)
    (hB : ∀ j ∈ S, ∀ p ∈ B j, p.Prime) {n : ℕ} (hn : 0 < n) :
    PrimeSupported (fun p ↦ p ∉ S.biUnion B) n ↔
      ∀ j ∈ S, ¬mrPrimeBlockHit (B j) n := by
  constructor
  · intro hs j hj hhit
    obtain ⟨p, hpB, hpn⟩ := hhit
    have hpf : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hB j hj p hpB, hpn, hn.ne'⟩
    exact hs.2 p hpf (Finset.mem_biUnion.mpr ⟨j, hj, hpB⟩)
  · intro hs
    refine ⟨hn.ne', ?_⟩
    intro p hp hmem
    obtain ⟨j, hj, hpB⟩ := Finset.mem_biUnion.mp hmem
    exact hs j hj ⟨p, hpB, Nat.dvd_of_mem_primeFactors hp⟩

theorem mrProd_missing_prime_indicators {ι : Type*} (S : Finset ι) (B : ι → Finset ℕ) (n : ℕ) :
    (∏ j ∈ S, (if mrPrimeBlockHit (B j) n then (0 : ℂ) else 1)) =
      if ∀ j ∈ S, ¬mrPrimeBlockHit (B j) n then 1 else 0 := by
  classical
  by_cases h : ∀ j ∈ S, ¬mrPrimeBlockHit (B j) n
  · rw [if_pos h]
    exact Finset.prod_eq_one (fun j hj ↦ if_neg (h j hj))
  · rw [if_neg h]
    push Not at h
    obtain ⟨j, hj, hhit⟩ := h
    exact Finset.prod_eq_zero_iff.mpr ⟨j, hj, if_pos hhit⟩

theorem mrProd_hit_prime_indicators {ι : Type*} (J : Finset ι) (B : ι → Finset ℕ) (n : ℕ) :
    (∏ j ∈ J, (1 - (if mrPrimeBlockHit (B j) n then (0 : ℂ) else 1))) =
      if ∀ j ∈ J, mrPrimeBlockHit (B j) n then 1 else 0 := by
  classical
  by_cases h : ∀ j ∈ J, mrPrimeBlockHit (B j) n
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro j hj
    simp [h j hj]
  · rw [if_neg h]
    push Not at h
    obtain ⟨j, hj, hmiss⟩ := h
    apply Finset.prod_eq_zero_iff.mpr
    exact ⟨j, hj, by simp [hmiss]⟩

theorem mrPrimeBandCoefficient_eq_missing_product {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (B : ι → Finset ℕ)
    (hB : ∀ j ∈ S, ∀ p ∈ B j, p.Prime) (f : ℕ → ℂ) {n : ℕ} (hn : 0 < n) :
    primeBandCoefficient f (fun p ↦ p ∉ S.biUnion B) n =
      (∏ j ∈ S, (if mrPrimeBlockHit (B j) n then (0 : ℂ) else 1)) * f n := by
  classical
  rw [mrProd_missing_prime_indicators]
  unfold primeBandCoefficient
  rw [mrPrimeMask_supported_iff S B hB hn]
  split_ifs <;> simp

theorem mrIndexedTypicalCoefficient_eq_mask_sum {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (B : ι → Finset ℕ)
    (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime) (f : ℕ → ℂ) {n : ℕ} (hn : 0 < n) :
    mrIndexedTypicalCoefficient J B f n =
      ∑ S ∈ J.powerset, (-1 : ℂ) ^ S.card *
        primeBandCoefficient f (fun p ↦ p ∉ S.biUnion B) n := by
  classical
  calc
    _ = (∏ j ∈ J, (1 - (if mrPrimeBlockHit (B j) n then (0 : ℂ) else 1))) * f n := by
      rw [mrProd_hit_prime_indicators]
      unfold mrIndexedTypicalCoefficient
      split_ifs <;> simp
    _ = ∑ S ∈ J.powerset, (-1 : ℂ) ^ S.card *
        ((∏ j ∈ S, (if mrPrimeBlockHit (B j) n then (0 : ℂ) else 1)) * f n) := by
      rw [Finset.prod_sub, Finset.sum_mul]
      simp only [Finset.prod_const_one, mul_one, mul_assoc]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [mrPrimeBandCoefficient_eq_missing_product S B
        (fun j hj p hp ↦ hB j (Finset.mem_powerset.mp hS hj) p hp) f hn]

theorem mrIndexedTypicalCoefficient_norm_le {ι : Type*} (J : Finset ι) (B : ι → Finset ℕ)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) {n : ℕ} (hn : 0 < n) :
    ‖mrIndexedTypicalCoefficient J B f n‖ ≤ 1 := by
  classical
  unfold mrIndexedTypicalCoefficient
  split_ifs
  · exact hbound n hn
  · simp

theorem mrLSeries_indexedTypical_eq_mask_sum {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (B : ι → Finset ℕ)
    (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    LSeries (mrIndexedTypicalCoefficient J B f) s =
      ∑ S ∈ J.powerset, (-1 : ℂ) ^ S.card *
        LSeries (primeBandCoefficient f (fun p ↦ p ∉ S.biUnion B)) s := by
  classical
  let F : Finset ι → ℕ → ℂ := fun S ↦ (-1 : ℂ) ^ S.card •
    primeBandCoefficient f (fun p ↦ p ∉ S.biUnion B)
  have hcoef : LSeries (mrIndexedTypicalCoefficient J B f) s =
      LSeries (∑ S ∈ J.powerset, F S) s := by
    apply LSeries_congr
    intro n hn
    simpa only [F, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
      mrIndexedTypicalCoefficient_eq_mask_sum J B hB f (Nat.pos_of_ne_zero hn)
  have hsum : ∀ S ∈ J.powerset, LSeriesSummable (F S) s := by
    intro S hS
    apply LSeriesSummable.smul
    apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1) _ hs
    intro n hn
    exact norm_primeBandCoefficient_le_one hbound _ (Nat.pos_of_ne_zero hn)
  rw [hcoef, LSeries_sum hsum]
  simp only [F, LSeries_smul]

theorem mrNorm_LSeries_indexedTypical_le_mask_norm_sum {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (B : ι → Finset ℕ)
    (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    ‖LSeries (mrIndexedTypicalCoefficient J B f) s‖ ≤
      ∑ S ∈ J.powerset, ‖LSeries (primeBandCoefficient f (fun p ↦ p ∉ S.biUnion B)) s‖ := by
  rw [mrLSeries_indexedTypical_eq_mask_sum J B hB hbound hs]
  apply (norm_sum_le _ _).trans_eq
  apply Finset.sum_congr rfl
  intro S hS
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]

end

end Erdos67b
