/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.FixedLowerSizeRetention
import ErdosProblems.Erdos446.FixedMultiplicityExactFamily
import ErdosProblems.Erdos446.IsolatedPrimeSelectionMass

/-!
# Erdős Problem 446: the size-closed fixed-multiplicity assembly

This file connects the concrete positive block family retained by the two
finite Markov truncations to the exact-multiplicity CRT construction.  All
families below are explicit finite sets.  In particular, the density theorem
does not pass through either of the abstract model interfaces in
`FixedMultiplicityReduction`.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- Ford-positive block-count vectors which also obey the product-size cap. -/
noncomputable def fordPositiveSizedCompositions
    (M k : ℕ) (E : ℝ) : Finset (Fin k → ℕ) :=
  (fordPositiveCompositions M k E).filter fun c ↦
    c ∈ sizedCappedCompositions M k

/-- The corresponding explicit family of squarefree small factors. -/
noncomputable def fordPositiveSizedBlockFamily
    (M k : ℕ) (E : ℝ) : Finset ℕ :=
  (fordPositiveSizedCompositions M k E).biUnion
    (compositionBlockFamily M)

theorem mem_fordPositiveSizedCompositions
    {M k : ℕ} {E : ℝ} {c : Fin k → ℕ} :
    c ∈ fordPositiveSizedCompositions M k E ↔
      c ∈ fordPositiveCompositions M k E ∧
        c ∈ sizedCappedCompositions M k := by
  simp [fordPositiveSizedCompositions]

theorem fordPositiveSizedBlockFamilies_pairwiseDisjoint
    (M k : ℕ) (E : ℝ) :
    ((fordPositiveSizedCompositions M k E : Finset (Fin k → ℕ)) :
      Set (Fin k → ℕ)).PairwiseDisjoint (compositionBlockFamily M) := by
  intro b hb c hc hbc
  exact cappedBlockFamilies_pairwiseDisjoint M k
    (mem_fordPositiveCompositions.mp
      (mem_fordPositiveSizedCompositions.mp hb).1).1
    (mem_fordPositiveCompositions.mp
      (mem_fordPositiveSizedCompositions.mp hc).1).1 hbc

/-- The strict Ford-positive cutoff is contained in the slightly larger
isolated-family cutoff used by the one-vector power-mass theorem. -/
theorem fordPositiveCompositions_subset_positiveIsolated
    (M k : ℕ) (E : ℝ) :
    fordPositiveCompositions M k E ⊆
      positiveIsolatedCompositions M k E := by
  intro c hc
  rw [mem_positiveIsolatedCompositions]
  have h := mem_fordPositiveCompositions.mp hc
  refine ⟨h.1, h.2.trans ?_⟩
  norm_num

/-- Every member of the size-closed block family has all the arithmetic
metadata needed by the exact-multiplicity construction. -/
theorem fordPositiveSizedBlockFamily_metadata
    {M k : ℕ} {E : ℝ} {a : ℕ}
    (ha : a ∈ fordPositiveSizedBlockFamily M k E) :
    0 < a ∧ Squarefree a ∧ a.primeFactors.card = k ∧
      a ≤ fordConstructionBound M k := by
  obtain ⟨c, hc, hac⟩ := Finset.mem_biUnion.mp ha
  have hc' := mem_fordPositiveSizedCompositions.mp hc
  have hmeta := compositionBlockFamily_squarefree_card
    (mem_fordPositiveCompositions.mp hc'.1).1 hac
  exact ⟨hmeta.1, hmeta.2.1, hmeta.2.2,
    sizedBlockFamily_le_constructionBound hc'.2 hac⟩

/-- Prime factors in the small block family lie below the common terminal
block endpoint. -/
theorem fordPositiveSizedBlockFamily_primeFactor_le_endpoint
    {M k : ℕ} {E : ℝ} {a p : ℕ}
    (ha : a ∈ fordPositiveSizedBlockFamily M k E)
    (hp : p ∈ a.primeFactors) :
    p ≤ blockEndpoint (M + k) := by
  obtain ⟨c, hc, hac⟩ := Finset.mem_biUnion.mp ha
  obtain ⟨S, hS, hprod⟩ := mem_blockFamily.mp hac
  rw [← hprod, selectionProduct_primeFactors hS] at hp
  obtain ⟨i, hi, hpBlock⟩ := mem_blockPool.mp
    ((mem_blockSelectionSets.mp hS).1 hp)
  exact (mem_primeBlock.mp hpBlock).2.2.trans
    (blockEndpoint_mono (by omega))

theorem blockEndpoint_le_fordConstructionBound (M k : ℕ) :
    blockEndpoint (M + k) ≤ fordConstructionBound M k := by
  dsimp [blockEndpoint, fordConstructionBound]
  apply Nat.pow_le_pow_right (by omega)
  have hpos : 0 < 2 ^ (M + k) := by positivity
  omega

/-- The fourth-power construction scale has enough slack for the strict
`2a^2 < y` separation used by the exact divisor-count lemma. -/
theorem two_mul_fordConstructionBound_sq_lt_scale (M k : ℕ) :
    2 * fordConstructionBound M k * fordConstructionBound M k <
      fordConstructionScale M k := by
  let B := fordConstructionBound M k
  have hB : 2 ≤ B := fordConstructionBound_one_lt M k
  rw [fordConstructionScale_eq_pow]
  change 2 * B * B < B ^ 4
  have htwo : 2 < B ^ 2 := by
    have hfour : 4 ≤ B ^ 2 := by
      simpa using Nat.pow_le_pow_left hB 2
    omega
  nlinarith [Nat.zero_le (B ^ 2)]

/-! ## Isolated moment on the retained block family -/

/-- The isolated-divisor power mass survives the product-size truncation.
The reciprocal-factorial mass on the left is exactly the filtered mass
supplied by `FixedLowerSizeRetention`. -/
theorem fordPositiveSizedBlockFamily_isolatedPowerMass_lower
    {N M k r : ℕ} {C E : ℝ}
    (hM : 1 ≤ M) (hk : 0 < k) (hC : 0 ≤ C) (hr : 1 ≤ r)
    (hmass : ∀ i : Fin k,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val))
    (hselect : ∀ c ∈ fordPositiveSizedCompositions M k E,
      ∀ i : Fin k,
        (c i : ℝ) * (1 / (blockEndpoint (M + i) : ℝ)) ≤
          primeBlockMass (M + i))
    (hbudget :
      (4 * (M * M) * C + 12 * (M * M) ^ 2) /
          (Real.log 2 * (2 : ℝ) ^ M) ≤ 1 / 100)
    (hhalf : ∀ i : Fin k,
      Real.log 2 / 2 ≤ primeBlockMass (M + i))
    (hE : 4 * (M * M) * (C / Real.log 2) / (2 : ℝ) ^ M ≤ E)
    (hN : 3 ≤ N) (hendpoint : ∀ i : Fin k,
      N ≤ blockEndpoint (M + i))
    (hprime : ∀ t : ℕ, N ≤ t →
      dyadicPrimeMass t ≤ 3 / Real.log (t : ℝ)) :
    ((((2 : ℝ) ^ k) / 2) ^ (r - 1)) * (91 / 600 : ℝ) *
        (2 * Real.log 2 : ℝ) ^ k *
        (∑ c ∈ fordPositiveSizedCompositions M k E,
          1 / compositionFactorial c) ≤
      ∑ a ∈ fordPositiveSizedBlockFamily M k E,
        ((sigmaIsolatedCount a (Real.log 2) : ℝ) ^ r) / (a : ℝ) := by
  rw [fordPositiveSizedBlockFamily,
    Finset.sum_biUnion
      (fordPositiveSizedBlockFamilies_pairwiseDisjoint M k E)]
  calc
    ((((2 : ℝ) ^ k) / 2) ^ (r - 1)) * (91 / 600 : ℝ) *
          (2 * Real.log 2 : ℝ) ^ k *
          (∑ c ∈ fordPositiveSizedCompositions M k E,
            1 / compositionFactorial c) =
        ∑ c ∈ fordPositiveSizedCompositions M k E,
          ((((2 : ℝ) ^ k) / 2) ^ (r - 1)) *
            ((91 / 600 : ℝ) *
              ((2 * Real.log 2 : ℝ) ^ k /
                compositionFactorial c)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro c hc
      exact compositionBlockFamily_isolatedPowerMass_lower
        hM hk hC hr
        (fordPositiveCompositions_subset_positiveIsolated M k E
          (mem_fordPositiveSizedCompositions.mp hc).1)
        hmass (hselect c hc) hbudget hhalf hE hN hendpoint hprime

/-! ## Exact-multiplicity density with the uniform atom cutoff -/

/-- Variant of the exact-family bridge using the uniform atom condition
`r a/y ≤ 1/(8 log y)`.  Unlike a direct comparison with the total isolated
prime mass, this formulation also handles the zero-isolated-count case. -/
theorem isolatedPowerMass_density_lower_of_uniform_atom
    {N y r L : ℕ} (A : Finset ℕ)
    (hy : 0 < y) (hr : 1 ≤ r)
    (hN : 3 ≤ N)
    (hprime : ∀ x : ℕ, N ≤ x →
      (1 / 4 : ℝ) / Real.log (x : ℝ) ≤ dyadicPrimeMass x)
    (hApos : ∀ a ∈ A, 0 < a)
    (hAsq : ∀ a ∈ A, Squarefree a)
    (hAsmall : ∀ a ∈ A, 2 * a * a < y)
    (hAbound : ∀ a ∈ A, a ≤ 2 * y)
    (hAcut : ∀ a ∈ A, ∀ p ∈ a.primeFactors, p ≤ L)
    (houter : ∀ a ∈ A, ∀ p ∈ isolatedDyadicPrimeSupport y a,
      L < p)
    (hscale : ∀ a ∈ A, ∀ d ∈ a.divisors,
      N ≤ y / d ∧ y ≤ (y / d) ^ 2)
    (hatom : ∀ a ∈ A,
      (r : ℝ) * ((a : ℝ) / (y : ℝ)) ≤
        1 / (8 * Real.log (y : ℝ))) :
    smallPrimeEulerDensity (2 * y) *
        ((((1 : ℝ) / (8 * Real.log (y : ℝ))) ^ r /
            (r.factorial : ℝ)) *
          (∑ a ∈ A,
            ((sigmaIsolatedCount a (Real.log 2) : ℝ) ^ r) /
              (a : ℝ))) ≤
      epsilonR r y (2 * y) := by
  let F : ℕ → Finset (Finset ℕ) :=
    fun a ↦ isolatedOuterPrimeSets y a r
  have hinj : Set.InjOn smallOuterModulus (smallOuterPairs A F) := by
    exact isolatedExactModuli_factorization_injective
      y r L A hApos hAsq hAcut houter
  have hmass :
      (((1 : ℝ) / (8 * Real.log (y : ℝ))) ^ r /
          (r.factorial : ℝ)) *
          (∑ a ∈ A,
            ((sigmaIsolatedCount a (Real.log 2) : ℝ) ^ r) /
              (a : ℝ)) ≤
        ∑ c ∈ isolatedExactModuli y r A, 1 / (c : ℝ) := by
    change _ ≤ ∑ c ∈ smallOuterModuli A F, 1 / (c : ℝ)
    apply isolatedPowerMass_le_sum_reciprocal_smallOuterModuli
      A F r
      ((((1 : ℝ) / (8 * Real.log (y : ℝ))) ^ r) /
        (r.factorial : ℝ)) hinj hApos
    intro a ha
    have hpoint := isolatedPrimeSubsetMass_lower hN hprime hy
      (hApos a ha) hr (hscale a ha) (hatom a ha)
    calc
      (((1 : ℝ) / (8 * Real.log (y : ℝ))) ^ r /
            (r.factorial : ℝ)) *
          (sigmaIsolatedCount a (Real.log 2) : ℝ) ^ r =
        (((sigmaIsolatedCount a (Real.log 2) : ℝ) /
            (8 * Real.log (y : ℝ))) ^ r) /
          (r.factorial : ℝ) := by
        simp only [div_eq_mul_inv, mul_pow, inv_pow]
        ring
      _ ≤ ∑ P ∈ F a, ∏ p ∈ P, 1 / (p : ℝ) := by
        simpa only [F, isolatedPrimeSubsets, isolatedOuterPrimeSets]
          using hpoint
  have heuler : 0 ≤ smallPrimeEulerDensity (2 * y) :=
    smallPrimeEulerDensity_nonneg _
  calc
    smallPrimeEulerDensity (2 * y) *
        ((((1 : ℝ) / (8 * Real.log (y : ℝ))) ^ r /
            (r.factorial : ℝ)) *
          (∑ a ∈ A,
            ((sigmaIsolatedCount a (Real.log 2) : ℝ) ^ r) /
              (a : ℝ))) ≤
      smallPrimeEulerDensity (2 * y) *
        (∑ c ∈ isolatedExactModuli y r A, 1 / (c : ℝ)) :=
      mul_le_mul_of_nonneg_left hmass heuler
    _ ≤ epsilonR r y (2 * y) :=
      isolatedExactModuli_density_lower A hy hApos hAsq hAsmall
        hAbound hAcut houter

/-! ## The concrete finite Ford lower bound -/

/-- Complete finite assembly at an arbitrary ambient scale above the
construction scale.  Every hypothesis is a numerical or pointwise estimate
on an explicitly defined function; in particular there is no model-density
or family-existence assumption in this statement. -/
theorem fordFixedMultiplicitySized_finite_lower
    {N M k r y : ℕ} {C E Q D : ℝ}
    (hM : 1 ≤ M) (hk : 2 ≤ k) (hr : 1 ≤ r)
    (hN : 3 ≤ N) (hNM : N ≤ M)
    (hC : 0 ≤ C) (hD : 0 < D)
    (hprime : ∀ x : ℕ, N ≤ x →
      (1 / 4 : ℝ) / Real.log (x : ℝ) ≤ dyadicPrimeMass x ∧
        dyadicPrimeMass x ≤ 3 / Real.log (x : ℝ))
    (hmass : ∀ j : ℕ, M ≤ j →
      |primeBlockMass j - Real.log 2| ≤ C / (2 : ℝ) ^ j)
    (hsmallSelect :
      2 * (M : ℝ) ^ 2 / (2 : ℝ) ^ M ≤ Real.log 2 / 2)
    (hbudget :
      (4 * (M * M) * C + 12 * (M * M) ^ 2) /
          (Real.log 2 * (2 : ℝ) ^ M) ≤ 1 / 100)
    (hhalf : ∀ i : Fin k,
      Real.log 2 / 2 ≤ primeBlockMass (M + i))
    (hE : 4 * (M * M) * (C / Real.log 2) / (2 : ℝ) ^ M ≤ E)
    (hQ : 0 ≤ Q)
    (hquality : Real.exp E * (1 + Q * (2 * D)) ≤ 13 / 10)
    (hQdef : Q = 56 / (Real.log 2 ^ 2 * (2 : ℝ) ^ M))
    (henergy : fixedLowerPrefixEnergyMoment k ≤
      D * ((k : ℝ) ^ k / ((k + 1).factorial : ℝ)))
    (hyScale : fordConstructionScale M k ≤ y)
    (hNB : N ≤ fordConstructionBound M k)
    (hatom :
      (r : ℝ) *
          ((fordConstructionBound M k : ℝ) / (y : ℝ)) ≤
        1 / (8 * Real.log (y : ℝ))) :
    smallPrimeEulerDensity (2 * y) *
        ((((1 : ℝ) / (8 * Real.log (y : ℝ))) ^ r /
            (r.factorial : ℝ)) *
          (((((2 : ℝ) ^ k) / 2) ^ (r - 1)) *
            (91 / 600 : ℝ) * (2 * Real.log 2 : ℝ) ^ k *
            ((1 / 8 : ℝ) *
              ((k : ℝ) ^ k / ((k + 1).factorial : ℝ))))) ≤
      epsilonR r y (2 * y) := by
  let A := fordPositiveSizedBlockFamily M k E
  let B := fordConstructionBound M k
  let L := blockEndpoint (M + k)
  have hy : 0 < y := by
    have hspos : 0 < fordConstructionScale M k := by
      dsimp [fordConstructionScale]
      positivity
    omega
  have hcompMass :
      (1 / 8 : ℝ) *
          ((k : ℝ) ^ k / ((k + 1).factorial : ℝ)) ≤
        ∑ c ∈ fordPositiveSizedCompositions M k E,
          1 / compositionFactorial c := by
    have hretained := fixedLowerSizedRestrictedMass_eighth_scale_of_moments
      hM hk hD henergy
    exact fordPositive_sized_mass_lower_of_fixedLower hM hQ hquality hQdef
      hretained
  have hselect : ∀ c ∈ fordPositiveSizedCompositions M k E,
      ∀ i : Fin k,
        (c i : ℝ) * (1 / (blockEndpoint (M + i) : ℝ)) ≤
          primeBlockMass (M + i) := by
    intro c hc
    apply capped_selection_condition hM hsmallSelect hhalf
    exact (mem_fordPositiveCompositions.mp
      (mem_fordPositiveSizedCompositions.mp hc).1).1
  have hendpoint : ∀ i : Fin k, N ≤ blockEndpoint (M + i) := by
    intro i
    exact hNM.trans ((Nat.le_add_right M i).trans
      (blockEndpoint_ge_index (M + i)))
  have hisolated :
      ((((2 : ℝ) ^ k) / 2) ^ (r - 1)) * (91 / 600 : ℝ) *
          (2 * Real.log 2 : ℝ) ^ k *
          ((1 / 8 : ℝ) *
            ((k : ℝ) ^ k / ((k + 1).factorial : ℝ))) ≤
        ∑ a ∈ A,
          ((sigmaIsolatedCount a (Real.log 2) : ℝ) ^ r) /
            (a : ℝ) := by
    calc
      ((((2 : ℝ) ^ k) / 2) ^ (r - 1)) * (91 / 600 : ℝ) *
          (2 * Real.log 2 : ℝ) ^ k *
          ((1 / 8 : ℝ) *
            ((k : ℝ) ^ k / ((k + 1).factorial : ℝ))) ≤
        ((((2 : ℝ) ^ k) / 2) ^ (r - 1)) * (91 / 600 : ℝ) *
          (2 * Real.log 2 : ℝ) ^ k *
          (∑ c ∈ fordPositiveSizedCompositions M k E,
            1 / compositionFactorial c) := by
        exact mul_le_mul_of_nonneg_left hcompMass (by positivity)
      _ ≤ ∑ a ∈ A,
          ((sigmaIsolatedCount a (Real.log 2) : ℝ) ^ r) /
            (a : ℝ) := by
        exact fordPositiveSizedBlockFamily_isolatedPowerMass_lower
          hM (by omega) hC hr
          (fun i ↦ hmass (M + i) (Nat.le_add_right M i)) hselect
          hbudget hhalf hE hN
          hendpoint (fun t ht ↦ (hprime t ht).2)
  have hApos : ∀ a ∈ A, 0 < a := by
    intro a ha
    exact (fordPositiveSizedBlockFamily_metadata ha).1
  have hAsq : ∀ a ∈ A, Squarefree a := by
    intro a ha
    exact (fordPositiveSizedBlockFamily_metadata ha).2.1
  have hAsmall : ∀ a ∈ A, 2 * a * a < y := by
    intro a ha
    have haB := (fordPositiveSizedBlockFamily_metadata ha).2.2.2
    exact (Nat.mul_le_mul (Nat.mul_le_mul_left 2 haB) haB).trans_lt
      ((two_mul_fordConstructionBound_sq_lt_scale M k).trans_le hyScale)
  have hAbound : ∀ a ∈ A, a ≤ 2 * y := by
    intro a ha
    exact (fordPositiveSizedBlockFamily_metadata ha).2.2.2.trans
      ((fordConstructionBound_le_two_scale M k).trans
        (Nat.mul_le_mul_left 2 hyScale))
  have hAcut : ∀ a ∈ A, ∀ p ∈ a.primeFactors, p ≤ L := by
    intro a ha p hp
    exact fordPositiveSizedBlockFamily_primeFactor_le_endpoint ha hp
  have houter : ∀ a ∈ A, ∀ p ∈ isolatedDyadicPrimeSupport y a,
      L < p := by
    intro a ha p hp
    obtain ⟨c, hc, hac⟩ := Finset.mem_biUnion.mp ha
    have hcSized := (mem_fordPositiveSizedCompositions.mp hc).2
    rw [isolatedDyadicPrimeSupport, Finset.mem_biUnion] at hp
    obtain ⟨d, hdIso, hpd⟩ := hp
    have hscaleL := sizedBlockFamily_scale_of_le
      (blockEndpoint_le_fordConstructionBound M k) hyScale hcSized hac
      (mem_sigmaIsolatedDivisors.mp hdIso).1
    exact lt_of_le_of_lt hscaleL.1 (mem_dyadicPrimes.mp hpd).1
  have hscale : ∀ a ∈ A, ∀ d ∈ a.divisors,
      N ≤ y / d ∧ y ≤ (y / d) ^ 2 := by
    intro a ha d hd
    obtain ⟨c, hc, hac⟩ := Finset.mem_biUnion.mp ha
    exact sizedBlockFamily_scale_of_le hNB hyScale
      (mem_fordPositiveSizedCompositions.mp hc).2 hac hd
  have hAatom : ∀ a ∈ A,
      (r : ℝ) * ((a : ℝ) / (y : ℝ)) ≤
        1 / (8 * Real.log (y : ℝ)) := by
    intro a ha
    have haBR : (a : ℝ) ≤ (fordConstructionBound M k : ℝ) := by
      exact_mod_cast
        (fordPositiveSizedBlockFamily_metadata ha).2.2.2
    apply (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right
        haBR
        (Nat.cast_nonneg y)) (Nat.cast_nonneg r)).trans
    simpa [B] using hatom
  have hexact := isolatedPowerMass_density_lower_of_uniform_atom
    A hy hr hN (fun x hx ↦ (hprime x hx).1)
    hApos hAsq hAsmall hAbound hAcut houter hscale hAatom
  have hcoeff :
      0 ≤ smallPrimeEulerDensity (2 * y) *
        (((1 : ℝ) / (8 * Real.log (y : ℝ))) ^ r /
          (r.factorial : ℝ)) := by
    have hy2 : 2 ≤ y := by
      have hB2 : 2 ≤ fordConstructionBound M k :=
        fordConstructionBound_one_lt M k
      have hBscale : fordConstructionBound M k ≤
          fordConstructionScale M k := by
        rw [fordConstructionScale_eq_pow]
        simpa using Nat.pow_le_pow_right (by omega :
          0 < fordConstructionBound M k) (by omega : 1 ≤ 4)
      omega
    have hylog : 0 < Real.log (y : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < y by omega))
    exact mul_nonneg (smallPrimeEulerDensity_nonneg _)
      (div_nonneg (pow_nonneg (by positivity) r) (by positivity))
  calc
    smallPrimeEulerDensity (2 * y) *
        ((((1 : ℝ) / (8 * Real.log (y : ℝ))) ^ r /
            (r.factorial : ℝ)) *
          (((((2 : ℝ) ^ k) / 2) ^ (r - 1)) *
            (91 / 600 : ℝ) * (2 * Real.log 2 : ℝ) ^ k *
            ((1 / 8 : ℝ) *
              ((k : ℝ) ^ k / ((k + 1).factorial : ℝ))))) =
      (smallPrimeEulerDensity (2 * y) *
        (((1 : ℝ) / (8 * Real.log (y : ℝ))) ^ r /
          (r.factorial : ℝ))) *
        (((((2 : ℝ) ^ k) / 2) ^ (r - 1)) *
          (91 / 600 : ℝ) * (2 * Real.log 2 : ℝ) ^ k *
          ((1 / 8 : ℝ) *
            ((k : ℝ) ^ k / ((k + 1).factorial : ℝ)))) := by ring
    _ ≤ (smallPrimeEulerDensity (2 * y) *
        (((1 : ℝ) / (8 * Real.log (y : ℝ))) ^ r /
          (r.factorial : ℝ))) *
        (∑ a ∈ A,
          ((sigmaIsolatedCount a (Real.log 2) : ℝ) ^ r) /
            (a : ℝ)) := mul_le_mul_of_nonneg_left hisolated hcoeff
    _ = smallPrimeEulerDensity (2 * y) *
        ((((1 : ℝ) / (8 * Real.log (y : ℝ))) ^ r /
            (r.factorial : ℝ)) *
          (∑ a ∈ A,
            ((sigmaIsolatedCount a (Real.log 2) : ℝ) ^ r) /
              (a : ℝ))) := by ring
    _ ≤ epsilonR r y (2 * y) := hexact

end Erdos446
