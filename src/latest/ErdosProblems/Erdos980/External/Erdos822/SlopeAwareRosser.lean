/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos980.External.Erdos822.SlopeAwareSieve
import ErdosProblems.Erdos980.External.Erdos822.AffinePrimePairs
import ErdosProblems.Erdos851.ConcreteBetaCardinality

/-!
# Rosser upper bound after removing slope primes

This is the finite combinatorial upper sieve for the filtered prime list.
The remaining analytic task is to compare its upper main term with the full
pair-shift Euler product times the controlled slope-prime loss.
-/

namespace Erdos822

open Erdos851.FiniteCombinatorialSieve
open Erdos851.FiniteSieveApplication
open List

def ascendingSlopeAwareSievePrimes (a b z Y : ℕ) : List ℕ :=
  (Erdos851.ascendingSievePrimes z (Y - 1)).filter fun p ↦
    decide (¬ p ∣ a ∨ ¬ p ∣ b)

theorem ascendingSlopeAwareSievePrimes_prod (a b z Y : ℕ) :
    (ascendingSlopeAwareSievePrimes a b z Y).prod =
      slopeAwareSievePrimeProduct a b z Y := by
  classical
  unfold ascendingSlopeAwareSievePrimes slopeAwareSievePrimeProduct
  have hprod := List.prod_toFinset id
    ((Erdos851.ascendingSievePrimes_nodup z (Y - 1)).filter
      fun p ↦ decide (¬ p ∣ a ∨ ¬ p ∣ b))
  calc
    ((Erdos851.ascendingSievePrimes z (Y - 1)).filter fun p ↦
        decide (¬ p ∣ a ∨ ¬ p ∣ b)).prod =
        (((Erdos851.ascendingSievePrimes z (Y - 1)).filter fun p ↦
          decide (¬ p ∣ a ∨ ¬ p ∣ b)).toFinset).prod id := by
      simpa using hprod.symm
    _ = ∏ p ∈ slopeAwareSievePrimes a b z Y, p := by
      congr 1
      ext p
      simp [slopeAwareSievePrimes, Erdos387.mem_sievePrimes,
        Erdos851.mem_sievePrimes]
      intro _hslope
      constructor <;> intro h
      · exact ⟨h.2.2, h.1, by omega⟩
      · exact ⟨h.2.1, by omega, h.1⟩

theorem ascendingSlopeAwareSievePrimes_pairwise (a b z Y : ℕ) :
    (ascendingSlopeAwareSievePrimes a b z Y).Pairwise (· ≤ ·) :=
  (Erdos851.ascendingSievePrimes_pairwise z (Y - 1)).filter _

theorem ascendingSlopeAwareSievePrimes_nodup (a b z Y : ℕ) :
    (ascendingSlopeAwareSievePrimes a b z Y).Nodup :=
  (Erdos851.ascendingSievePrimes_nodup z (Y - 1)).filter _

@[simp]
theorem mem_ascendingSlopeAwareSievePrimes_iff
    {a b z Y p : ℕ} :
    p ∈ ascendingSlopeAwareSievePrimes a b z Y ↔
      p ∈ slopeAwareSievePrimes a b z Y := by
  simp [ascendingSlopeAwareSievePrimes, slopeAwareSievePrimes,
    Erdos387.mem_sievePrimes, Erdos851.mem_sievePrimes]
  intro _hslope
  constructor <;> intro h
  · exact ⟨h.2.2, h.1, by omega⟩
  · exact ⟨h.2.1, by omega, h.1⟩

theorem ascendingSlopeAwareSievePrimes_prime {a b z Y : ℕ} :
    ∀ p ∈ ascendingSlopeAwareSievePrimes a b z Y, p.Prime := by
  intro p hp
  exact (mem_slopeAwareSievePrimes_iff.mp
    (mem_ascendingSlopeAwareSievePrimes_iff.mp hp)).1

/-- Rosser's upper main term bounds the slope-aware sifted set with the
usual square distribution-level loss. -/
theorem slopeAwareTwoAffine_cardinality_le_upperMain
    {a s b t X z Y S : ℕ} (hz : 2 ≤ z) (hY : 2 ≤ Y) (hS : 1 ≤ S)
    (hconstants : ∀ p ∈ slopeAwareSievePrimes a b z Y,
      ¬ p ∣ s ∧ ¬ p ∣ t) :
    let P := ascendingSlopeAwareSievePrimes a b z Y
    let D := (Y - 1) ^ S
    let stop := rosserStoppingPredicate 100 D
    ((slopeAwareSiftedTwoAffineCandidates a s b t X z Y).card : ℝ) ≤
      (X : ℝ) * upperMainTerm stop (twoAffineNu a s b t) P +
        (D : ℝ) ^ 2 := by
  classical
  dsimp only
  let P := ascendingSlopeAwareSievePrimes a b z Y
  let D := (Y - 1) ^ S
  let stop := rosserStoppingPredicate 100 D
  let sieve := slopeAwareTwoAffineBoundingSieve a s b t X z Y hz hconstants
  have hprod : P.prod = sieve.prodPrimes := by
    change P.prod = slopeAwareSievePrimeProduct a b z Y
    exact ascendingSlopeAwareSievePrimes_prod a b z Y
  have hsort : P.Pairwise (· ≤ ·) :=
    ascendingSlopeAwareSievePrimes_pairwise a b z Y
  have hnodup : P.Nodup :=
    ascendingSlopeAwareSievePrimes_nodup a b z Y
  have hprime : ∀ p ∈ P, p.Prime :=
    ascendingSlopeAwareSievePrimes_prime
  have hD : 1 ≤ D := by
    dsimp [D]
    exact one_le_pow₀ (by omega)
  have hrem : ∀ d : ℕ, d ∣ sieve.prodPrimes → d ≤ D →
      |sieve.rem d| ≤ (d : ℝ) := by
    intro d hd _hdD
    have hsq : Squarefree d :=
      Squarefree.squarefree_of_dvd hd sieve.prodPrimes_squarefree
    exact (slopeAwareTwoAffineBoundingSieve_abs_rem_le_nuClasses
      (a := a) (s := s) (b := b) (t := t) (X := X) (z := z) (Y := Y)
      hd).trans (by exact_mod_cast twoAffineNuClasses_le hsq)
  have hupper := boundingSieve_siftedSum_le_upperMain_add_sq
    sieve P stop D hprod hsort hnodup hprime
    (by
      intro u hu hadm
      apply prod_le_of_upperAdmissible_rosserStoppingPredicate
        (by norm_num : 1 ≤ 100) hD
        (hsort.sublist (List.mem_sublists.mp hu))
        (by
          intro p hp
          exact (hprime p ((List.mem_sublists.mp hu).subset hp)).one_le)
        hadm)
    hrem
  change _ ≤ sieve.totalMass *
      upperMainTerm stop (fun p ↦ sieve.nu p) P + (D : ℝ) ^ 2 at hupper
  rw [show sieve.totalMass = (X : ℝ) by
      exact slopeAwareTwoAffineBoundingSieve_totalMass,
    show sieve.siftedSum =
        ((slopeAwareSiftedTwoAffineCandidates a s b t X z Y).card : ℝ) by
      exact slopeAwareTwoAffineBoundingSieve_siftedSum] at hupper
  exact hupper

/-- Genuine prime pairs above the sieving ceiling survive the slope-aware
sieve as well. -/
theorem mem_slopeAwareSifted_of_mem_twoAffinePrimeCandidates
    {a s b t X z y n : ℕ}
    (hn : n ∈ twoAffinePrimeCandidates a s b t X y) :
    n ∈ slopeAwareSiftedTwoAffineCandidates a s b t X z (y + 1) := by
  rw [mem_twoAffinePrimeCandidates_iff] at hn
  rw [slopeAwareSiftedTwoAffineCandidates, Finset.mem_filter]
  refine ⟨Finset.mem_range.mpr hn.1, ?_⟩
  by_contra hcop
  obtain ⟨p, hp, hpProd, hpAffine⟩ :=
    Nat.Prime.not_coprime_iff_dvd.mp hcop
  have hpMem :=
    prime_mem_slopeAwareSievePrimes_of_dvd_product hp hpProd
  have hpy : p ≤ y := by
    have := (mem_slopeAwareSievePrimes_iff.mp hpMem).2.2.1
    omega
  rw [twoAffineProduct] at hpAffine
  rcases hp.dvd_mul.mp hpAffine with hleft | hright
  · have hpeq : p = a * n + s :=
      ((hn.2.1.dvd_iff_eq hp.ne_one).mp hleft).symm
    omega
  · have hpeq : p = b * n + t :=
      ((hn.2.2.1.dvd_iff_eq hp.ne_one).mp hright).symm
    omega

theorem twoAffinePrimeCandidates_subset_slopeAwareSifted
    (a s b t X z y : ℕ) :
    twoAffinePrimeCandidates a s b t X y ⊆
      slopeAwareSiftedTwoAffineCandidates a s b t X z (y + 1) := by
  intro n hn
  exact mem_slopeAwareSifted_of_mem_twoAffinePrimeCandidates hn

/-- If the two constants are themselves primes above y, they are nonzero
modulo every slope-aware sieving prime in (z,y]. -/
theorem constants_not_dvd_on_slopeAware_of_prime_gt
    {a b q q' z y : ℕ} (hq : q.Prime) (hq' : q'.Prime)
    (hyq : y < q) (hyq' : y < q') :
    ∀ p ∈ slopeAwareSievePrimes a b z (y + 1),
      ¬ p ∣ q ∧ ¬ p ∣ q' := by
  intro p hpMem
  have hp := (mem_slopeAwareSievePrimes_iff.mp hpMem).1
  have hpy : p ≤ y := by
    have := (mem_slopeAwareSievePrimes_iff.mp hpMem).2.2.1
    omega
  constructor
  · intro hpq
    have hpeq : p = q := ((hq.dvd_iff_eq hp.ne_one).mp hpq).symm
    omega
  · intro hpq'
    have hpeq : p = q' := ((hq'.dvd_iff_eq hp.ne_one).mp hpq').symm
    omega

/-- Rosser upper bound for genuine affine prime pairs when the constant
terms are large primes. -/
theorem twoAffinePrimeCandidates_card_le_slopeAware_upperMain
    {a b q q' X z y S : ℕ}
    (hq : q.Prime) (hq' : q'.Prime) (hyq : y < q) (hyq' : y < q')
    (hz : 2 ≤ z) (hy : 1 < y) (hS : 1 ≤ S) :
    let P := ascendingSlopeAwareSievePrimes a b z (y + 1)
    let D := y ^ S
    let stop := rosserStoppingPredicate 100 D
    ((twoAffinePrimeCandidates a q b q' X y).card : ℝ) ≤
      (X : ℝ) * upperMainTerm stop (twoAffineNu a q b q') P +
        (D : ℝ) ^ 2 := by
  dsimp only
  calc
    ((twoAffinePrimeCandidates a q b q' X y).card : ℝ) ≤
        ((slopeAwareSiftedTwoAffineCandidates
          a q b q' X z (y + 1)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card
        (twoAffinePrimeCandidates_subset_slopeAwareSifted
          a q b q' X z y)
    _ ≤ (X : ℝ) *
          upperMainTerm (rosserStoppingPredicate 100 (y ^ S))
            (twoAffineNu a q b q')
            (ascendingSlopeAwareSievePrimes a b z (y + 1)) +
          ((y ^ S : ℕ) : ℝ) ^ 2 := by
      exact slopeAwareTwoAffine_cardinality_le_upperMain
        (a := a) (s := q) (b := b) (t := q') (X := X)
        (z := z) (Y := y + 1) (S := S) hz (by omega)
        hS (constants_not_dvd_on_slopeAware_of_prime_gt hq hq' hyq hyq')

end Erdos822
