/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos980.ElliottTail.RayNormPrimeSieve

/-!
# A level-restricted Rosser remainder bridge

Rosser's upper coefficients are supported on squarefree products at most the
sieve level.  Consequently the geometric remainder estimate is needed only
for those divisors, not for every divisor of the full primorial.  This file
records that sharper interface and its specialization to the conductor-norm
sieve data.
-/

open scoped BigOperators

namespace Erdos980.ElliottTail.LevelRestrictedRosser

open Erdos851.FiniteCombinatorialSieve
open Erdos851.FiniteSieveApplication
open Erdos387.FiniteBetaSieveBridge
open RayNormPrimeSieve

/-- Upper finite-sieve bound when the individual remainder estimate is known
only on products at most the Rosser level. -/
theorem boundingSieve_siftedSum_le_upperMain_add_levelEuler_restricted
    (s : BoundingSieve) (P : List ℕ) (A : List ℕ → Prop)
    (C : ℝ) (k D : ℕ)
    (hprod : P.prod = s.prodPrimes)
    (hnodup : P.Nodup) (hprime : ∀ p ∈ P, p.Prime)
    (hsupport : ∀ t ∈ P.sublists, UpperAdmissible A t → t.prod ≤ D)
    (hrem : ∀ d : ℕ, d ∣ s.prodPrimes → d ≤ D →
      |s.rem d| ≤ C * (k : ℝ) ^ d.primeFactors.card)
    (hC : 0 ≤ C) :
    s.siftedSum ≤
      s.totalMass * upperMainTerm A (fun p ↦ s.nu p) P +
        C * D * (P.map fun p ↦ 1 + (k : ℝ) / p).prod := by
  have happrox : ∀ t ∈ P.sublists,
      intersectionMass s.support s.weights (fun n p ↦ p ∣ n) t =
        s.totalMass * chainWeight (fun p ↦ s.nu p) t + s.rem t.prod := by
    intro t ht
    have htsub := List.mem_sublists.mp ht
    have htnodup := hnodup.sublist htsub
    have htprime : ∀ p ∈ t, p.Prime := by
      intro p hp
      exact hprime p (htsub.subset hp)
    rw [intersectionMass_dvd_eq_multSum s t htnodup htprime,
      s.multSum_eq_main_err, nu_prod_eq_chainWeight s t htnodup htprime]
    ring
  have hbase := siftedMass_le_upperMain_add_remainder
    s.support s.weights s.weights_nonneg (fun n p ↦ p ∣ n) A
    (fun p ↦ s.nu p) s.totalMass (fun t ↦ s.rem t.prod) P happrox
  have herror :
      admissibleRemainderAbs (UpperAdmissible A) (fun t ↦ s.rem t.prod) P ≤
        C * D * (P.map fun p ↦ 1 + (k : ℝ) / p).prod := by
    apply admissibleRemainderAbs_le_level_mul_euler P (UpperAdmissible A)
      (fun t ↦ s.rem t.prod) C k D hC hprime hsupport
    intro t ht hadm
    have htsub := List.mem_sublists.mp ht
    have htnodup := hnodup.sublist htsub
    have htprime : ∀ p ∈ t, p.Prime := by
      intro p hp
      exact hprime p (htsub.subset hp)
    have hpf : t.prod.primeFactors = t.toFinset := by
      have htprod : t.toFinset.prod id = t.prod := by
        simpa using List.prod_toFinset id htnodup
      rw [← htprod]
      simpa using Nat.primeFactors_prod
        (s := t.toFinset) (fun p hp ↦ htprime p (List.mem_toFinset.mp hp))
    have hcard : t.prod.primeFactors.card = t.length := by
      rw [hpf, List.toFinset_card_of_nodup htnodup]
    rw [← hcard]
    apply hrem t.prod
    · rw [← hprod]
      exact htsub.prod_dvd_prod
    · exact hsupport t ht hadm
  have hsift := siftedMass_dvd_eq_siftedSum s P hprod hprime
  rw [hsift] at hbase
  linarith

/-- Rosser upper bound with the same level-restricted individual remainder
hypothesis. -/
theorem boundingSieve_siftedSum_le_rosserUpperMain_add_levelEuler_restricted
    (s : BoundingSieve) (P : List ℕ) (C : ℝ) (k β D : ℕ)
    (hprod : P.prod = s.prodPrimes)
    (hsort : P.Pairwise (· ≤ ·)) (hnodup : P.Nodup)
    (hprime : ∀ p ∈ P, p.Prime)
    (hβ : 1 ≤ β) (hD : 1 ≤ D)
    (hrem : ∀ d : ℕ, d ∣ s.prodPrimes → d ≤ D →
      |s.rem d| ≤ C * (k : ℝ) ^ d.primeFactors.card)
    (hC : 0 ≤ C) :
    s.siftedSum ≤
      s.totalMass *
          upperMainTerm (rosserStoppingPredicate β D) (fun p ↦ s.nu p) P +
        C * D * (P.map fun p ↦ 1 + (k : ℝ) / p).prod := by
  apply boundingSieve_siftedSum_le_upperMain_add_levelEuler_restricted
    s P (rosserStoppingPredicate β D) C k D hprod hnodup hprime
  · intro t ht hadm
    have hsub := List.mem_sublists.mp ht
    exact prod_le_of_upperAdmissible_rosserStoppingPredicate hβ hD
      (hsort.sublist hsub)
      (fun p hp ↦ (hprime p (hsub.subset hp)).one_le) hadm
  · exact hrem
  · exact hC

/-- The conductor-norm specialization.  Its geometric remainder is required
only for squarefree divisor products at most `level`. -/
theorem normSiftedMass_le_sortedRosserUpperMain_add_levelEuler_restricted
    {K A : Type*} [Field K] [NumberField K]
    [DecidableEq A] (D : Data K A) (C : ℝ) (k β level : ℕ)
    (hβ : 1 ≤ β) (hlevel : 1 ≤ level)
    (hrem : ∀ d : ℕ, d ∣ D.sievePrimes.prod id → d ≤ level →
      |normDivisorMass D d - D.nu d * D.totalMass| ≤
        C * (k : ℝ) ^ d.primeFactors.card)
    (hC : 0 ≤ C) :
    normSiftedMass D ≤
      D.totalMass *
          upperMainTerm (rosserStoppingPredicate β level)
            (fun p ↦ D.nu p) (ascendingSievePrimes D) +
        C * level *
          ((ascendingSievePrimes D).map fun p ↦ 1 + (k : ℝ) / p).prod := by
  have hrem' : ∀ d : ℕ, d ∣ (boundingSieve D).prodPrimes → d ≤ level →
      |(boundingSieve D).rem d| ≤
        C * (k : ℝ) ^ d.primeFactors.card := by
    intro d hd hdl
    rw [boundingSieve_rem_eq]
    exact hrem d hd hdl
  have hsieve :=
    boundingSieve_siftedSum_le_rosserUpperMain_add_levelEuler_restricted
      (boundingSieve D) (ascendingSievePrimes D) C k β level
      (ascendingSievePrimes_prod D) (ascendingSievePrimes_pairwise D)
      (ascendingSievePrimes_nodup D) (ascendingSievePrimes_prime D)
      hβ hlevel hrem' hC
  rw [boundingSieve_siftedSum] at hsieve
  exact hsieve

end Erdos980.ElliottTail.LevelRestrictedRosser
