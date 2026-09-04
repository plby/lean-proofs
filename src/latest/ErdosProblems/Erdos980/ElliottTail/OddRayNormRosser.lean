/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos980.ElliottTail.LocalNormRootBound
import ErdosProblems.Erdos980.ElliottTail.LevelRestrictedRosser
import ErdosProblems.Erdos980.ElliottTail.OddMediumParameters
import ErdosProblems.Erdos980.ElliottTail.RayNormRemainder

/-!
# The fixed-ray-cell natural-norm Rosser estimate

This file is the finite assembly point for one correction ideal and one
allowed ray cell in the odd-prime medium argument.  The concrete algebraic
norm form supplies the local estimate `D * p^(D-1)`.  The growing-modulus
lattice theorem turns it into a uniform squarefree remainder, and the
finite Rosser sieve then gives its usual main term plus endpoint Euler
error.

The final theorem performs the numerical conversion to the precise shape
consumed by `primeExponentMediumEstimate_of_rosserCellEnvelope`.  The only
information deliberately left to the final arithmetic assembly is that the
exceptional rational primes inject into the chosen finite generator family,
and the two exact realization identities saying that its divisor masses are
the corresponding ray/norm lattice-cell counts.
-/

open Filter
open scoped BigOperators NumberField nonZeroDivisors

noncomputable section

namespace Erdos980.ElliottTail.OddRayNormRosser

open NumberField
open NumberField.mixedEmbedding
open IdealGeneratorCongruenceCount
open RayNormPrimeSieve
open RayNormRemainder
open LocalNormRootBound
open LevelRestrictedRosser
open OddMediumParameters
open Erdos851.FiniteCombinatorialSieve
open Erdos387.FiniteBetaSieveBridge

private theorem mem_sievePrimes_of_mem_primeFactors_of_dvd
    {K α : Type*} [Field K] [NumberField K]
    (D : Data K α) {d p : ℕ} (hd : d ∣ D.sievePrimes.prod id)
    (hp : p ∈ d.primeFactors) : p ∈ D.sievePrimes := by
  classical
  have hprod0 : D.sievePrimes.prod id ≠ 0 :=
    (sievePrimes_product_squarefree D).ne_zero
  have hmem := Nat.primeFactors_mono hd hprod0 hp
  have heq : (D.sievePrimes.prod id).primeFactors = D.sievePrimes :=
    Nat.primeFactors_prod D.sievePrimes_prime
  rw [heq] at hmem
  exact hmem

/-- For one fixed correction ideal and ray cell, the concrete algebraic
norm form supplies the complete finite Rosser estimate.  The two
`hdivisor`/`hmain` hypotheses are literal realization identities: the final
exceptional-prime encoding proves them by identifying its candidate family
with the indicated lattice points.  No analytic estimate is hidden in
them. -/
theorem exists_fixedIdeal_oneCell_normSiftedMass_bound
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰) :
    ∃ Cgeom : ℝ, 0 ≤ Cgeom ∧
      ∀ {α : Type*} [DecidableEq α] (D : Data K α)
        {ell j f unitResidueCount β level : ℕ}
        (rayAllowed : Finset (index K → ZMod f)) (height : ℝ),
        (hell0 : ell ≠ 0) → (hf0 : f ≠ 0) →
        (hfprod : f.Coprime (D.sievePrimes.prod id)) →
        (hgood : ∀ p ∈ D.sievePrimes,
          p.Coprime (Ideal.absNorm (J : Ideal (RingOfIntegers K)))) →
        (hray : ell ^ j * rayAllowed.card = unitResidueCount) →
        (hβ : 1 ≤ β) → (hlevel : 1 ≤ level) →
        (hheight : ∀ (d : ℕ) [NeZero d], d ∣ D.sievePrimes.prod id →
          d ≤ level → ((f * d : ℕ) : ℝ) ≤ height) →
        (hdivisor : ∀ (d : ℕ) [NeZero d] [NeZero (f * d)]
          (hd : d ∣ D.sievePrimes.prod id),
          normDivisorMass D d =
            (allowedGeneratorResidueCellCount J (f * d)
              (combinedCoordinateResidues K
                (Nat.Coprime.of_dvd_right hd hfprod)
                rayAllowed
                (normDivisibleResidues K d
                  ((coordinateAlgebraNormResidueSystem K J).normMod d)))
              height : ℕ)) →
        (hmain : ∀ (d : ℕ) [NeZero d], d ∣ D.sievePrimes.prod id →
          D.nu d * D.totalMass =
            combinedRayUnitNormDensity K ell j f d unitResidueCount
                ((coordinateAlgebraNormResidueSystem K J).normMod d) *
              (generatorCellMainConstant K J *
                height ^ Nat.card (index K))) →
        normSiftedMass D ≤
          D.totalMass *
              upperMainTerm (rosserStoppingPredicate β level)
                (fun p ↦ D.nu p) (ascendingSievePrimes D) +
            (Cgeom * rayAllowed.card *
                (height / f) ^ (Nat.card (index K) - 1)) *
              level *
                ((ascendingSievePrimes D).map
                  fun p ↦ 1 + (Nat.card (index K) : ℝ) / p).prod := by
  classical
  obtain ⟨Cgeom, hCgeom, hgeom⟩ :=
    exists_uniform_combinedRayUnitNormCellCount_of_primeBounds K J
  refine ⟨Cgeom, hCgeom, ?_⟩
  intro α _ D ell j f unitResidueCount β level rayAllowed height
    hell0 hf0 hfprod hgood hray hβ hlevel hheight hdivisor hmain
  let M := coordinateAlgebraNormResidueSystem K J
  let Crem : ℝ := Cgeom * rayAllowed.card *
    (height / f) ^ (Nat.card (index K) - 1)
  have hheight0 : 0 ≤ height := by
    have h := hheight 1 (one_dvd _) hlevel
    have : (0 : ℝ) ≤ ((f * 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    exact this.trans h
  have hCrem : 0 ≤ Crem := by
    dsimp [Crem]
    positivity
  apply normSiftedMass_le_sortedRosserUpperMain_add_levelEuler_restricted
    D Crem (Nat.card (index K)) β level hβ hlevel
  · intro d hd hdl
    have hprod0 : D.sievePrimes.prod id ≠ 0 :=
      (sievePrimes_product_squarefree D).ne_zero
    have hd0 : d ≠ 0 := by
      intro hdz
      subst d
      exact hprod0 (zero_dvd_iff.mp hd)
    let : NeZero d := ⟨hd0⟩
    let : NeZero (f * d) := ⟨mul_ne_zero hf0 hd0⟩
    have hfd : f.Coprime d := Nat.Coprime.of_dvd_right hd hfprod
    have hsq : Squarefree d :=
      Squarefree.squarefree_of_dvd hd (sievePrimes_product_squarefree D)
    have hlocal : ∀ p ∈ d.primeFactors,
        M.rootCount K p ≤
          Nat.card (index K) * p ^ (Nat.card (index K) - 1) := by
      intro p hp
      have hpS : p ∈ D.sievePrimes :=
        mem_sievePrimes_of_mem_primeFactors_of_dvd D hd hp
      exact coordinateAlgebraNormResidueSystem_rootCount_le K J p
        (D.sievePrimes_prime p hpS) (hgood p hpS)
    have hg := hgeom M hell0 hfd rayAllowed height (hheight d hd hdl)
      hray hsq hlocal
    rw [← hdivisor d hd, ← hmain d hd] at hg
    dsimp only [Crem]
    convert hg using 1 <;> ring
  · exact hCrem

/-- A finite cover reduces a global exceptional family to the sum of its
correction fibres.  Disjointness is not needed for this upper bound. -/
theorem exceptional_card_le_sum_fibreCards
    {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (indices : Finset ι) (fibre : ι → Finset σ) (exceptional : Finset σ)
    (hcover : exceptional ⊆ indices.biUnion fibre) :
    exceptional.card ≤ ∑ i ∈ indices, (fibre i).card :=
  (Finset.card_le_card hcover).trans Finset.card_biUnion_le

/-- Final one-cell estimate in the exact form consumed by
`primeExponentMediumEstimate_of_rosserCellEnvelope`.

`hfibre` is the intentionally exposed finite hypothesis: the final odd
assembly supplies it from the injective correction-fibre-to-generator map.
The global exceptional set is recovered only afterwards, using
`exceptional_card_le_sum_fibreCards` over the finite correction family.
The remaining hypotheses are transparent scale bounds for the Rosser main
term, lattice boundary, level, and endpoint Euler factor. -/
theorem exists_fixedIdeal_oneCell_exceptional_card_bound
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰) :
    ∃ Cgeom : ℝ, 0 ≤ Cgeom ∧
      ∀ {α : Type*} [DecidableEq α] (D : Data K α)
        {ell j f unitResidueCount β level x t : ℕ}
        {eta C A : ℝ}
        (rayAllowed : Finset (index K → ZMod f)) (height : ℝ),
        (hell : 2 ≤ ell) → (hf0 : f ≠ 0) → (hx : 1 < x) →
        (hfprod : f.Coprime (D.sievePrimes.prod id)) →
        (hgood : ∀ p ∈ D.sievePrimes,
          p.Coprime (Ideal.absNorm (J : Ideal (RingOfIntegers K)))) →
        (hray : ell ^ j * rayAllowed.card = unitResidueCount) →
        (hj : j = oddTensorDepth t) →
        (hβ : 1 ≤ β) → (hlevel : 1 ≤ level) →
        (hheight : ∀ (d : ℕ) [NeZero d], d ∣ D.sievePrimes.prod id →
          d ≤ level → ((f * d : ℕ) : ℝ) ≤ height) →
        (hdivisor : ∀ (d : ℕ) [NeZero d] [NeZero (f * d)]
          (hd : d ∣ D.sievePrimes.prod id),
          normDivisorMass D d =
            (allowedGeneratorResidueCellCount J (f * d)
              (combinedCoordinateResidues K
                (Nat.Coprime.of_dvd_right hd hfprod)
                rayAllowed
                (normDivisibleResidues K d
                  ((coordinateAlgebraNormResidueSystem K J).normMod d)))
              height : ℕ)) →
        (hmain : ∀ (d : ℕ) [NeZero d], d ∣ D.sievePrimes.prod id →
          D.nu d * D.totalMass =
            combinedRayUnitNormDensity K ell j f d unitResidueCount
                ((coordinateAlgebraNormResidueSystem K J).normMod d) *
              (generatorCellMainConstant K J *
                height ^ Nat.card (index K))) →
        (fibreCard : ℕ) →
        (hfibre : (fibreCard : ℝ) ≤ normSiftedMass D) →
        D.totalMass *
            upperMainTerm (rosserStoppingPredicate β level)
              (fun p ↦ D.nu p) (ascendingSievePrimes D) ≤
          A * ((ell : ℝ)⁻¹) ^ j *
            ((x : ℝ) / Real.log (x : ℝ)) →
        (Cgeom * rayAllowed.card *
            (height / f) ^ (Nat.card (index K) - 1)) * level ≤
          C * (x : ℝ) ^
            (1 - (Nat.card (index K) : ℝ)⁻¹ + eta) →
        0 ≤ ((ascendingSievePrimes D).map
            fun p ↦ 1 + (Nat.card (index K) : ℝ) / p).prod →
        ((ascendingSievePrimes D).map
            fun p ↦ 1 + (Nat.card (index K) : ℝ) / p).prod ≤
          Real.log (x : ℝ) ^ (Nat.card (index K) : ℝ) →
        0 ≤ C →
        0 ≤ A →
        (fibreCard : ℝ) ≤
          A * ((x : ℝ) / Real.log (x : ℝ)) /
              (((t + 1 : ℕ) : ℝ) ^ 2) +
            realRosserCellEnvelope (Nat.card (index K))
              (Nat.card (index K)) eta C (x : ℝ) := by
  classical
  obtain ⟨Cgeom, hCgeom, hsift⟩ :=
    exists_fixedIdeal_oneCell_normSiftedMass_bound K J
  refine ⟨Cgeom, hCgeom, ?_⟩
  intro α _ D ell j f unitResidueCount β level x t eta C A
    rayAllowed height hell hf0 hx hfprod hgood hray hj hβ hlevel
    hheight hdivisor hmain fibreCard hfibre hmainScale hboundaryScale
    hEuler0 hEulerGrowth hC0 hA
  have hell0 : ell ≠ 0 := by omega
  have hsift' := hsift D rayAllowed height hell0
    hf0 hfprod hgood hray hβ hlevel hheight hdivisor hmain
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hlogx : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast hx)
  have hscale : 0 ≤ (x : ℝ) / Real.log (x : ℝ) := by positivity
  have htensor : ((ell : ℝ)⁻¹) ^ j ≤
      1 / (((t + 1 : ℕ) : ℝ) ^ 2) := by
    rw [hj]
    exact oddTensorDepth_geometric_le_inverseSquare hell t
  have hmainFinal :
      D.totalMass *
          upperMainTerm (rosserStoppingPredicate β level)
            (fun p ↦ D.nu p) (ascendingSievePrimes D) ≤
        A * ((x : ℝ) / Real.log (x : ℝ)) /
          (((t + 1 : ℕ) : ℝ) ^ 2) := by
    refine hmainScale.trans ?_
    have hnonneg : 0 ≤ A * ((x : ℝ) / Real.log (x : ℝ)) :=
      mul_nonneg hA hscale
    calc
      A * ((ell : ℝ)⁻¹) ^ j *
            ((x : ℝ) / Real.log (x : ℝ)) =
          (A * ((x : ℝ) / Real.log (x : ℝ))) *
            ((ell : ℝ)⁻¹) ^ j := by ring
      _ ≤ (A * ((x : ℝ) / Real.log (x : ℝ))) *
            (1 / (((t + 1 : ℕ) : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left htensor hnonneg
      _ = A * ((x : ℝ) / Real.log (x : ℝ)) /
            (((t + 1 : ℕ) : ℝ) ^ 2) := by ring
  have hboundary :
      (Cgeom * rayAllowed.card *
          (height / f) ^ (Nat.card (index K) - 1)) *
          level *
            ((ascendingSievePrimes D).map
              fun p ↦ 1 + (Nat.card (index K) : ℝ) / p).prod ≤
        realRosserCellEnvelope (Nat.card (index K))
          (Nat.card (index K)) eta C (x : ℝ) := by
    calc
      (Cgeom * rayAllowed.card *
          (height / f) ^ (Nat.card (index K) - 1)) *
          level *
            ((ascendingSievePrimes D).map
              fun p ↦ 1 + (Nat.card (index K) : ℝ) / p).prod ≤
        (C * (x : ℝ) ^
          (1 - (Nat.card (index K) : ℝ)⁻¹ + eta)) *
            Real.log (x : ℝ) ^ (Nat.card (index K) : ℝ) :=
        mul_le_mul hboundaryScale hEulerGrowth hEuler0
          (mul_nonneg hC0 (Real.rpow_nonneg hx0.le _))
      _ = realRosserCellEnvelope (Nat.card (index K))
          (Nat.card (index K)) eta C (x : ℝ) := by
        unfold realRosserCellEnvelope
        ring
  exact hfibre.trans <| hsift'.trans <|
    add_le_add hmainFinal hboundary

/-- Logarithmic-modulus-aware version of the one-cell estimate.

The natural Mertens bound for a sieve interval whose lower endpoint contains
the moving ray modulus contributes an additional factor `log f`.  The
strengthened tensor depth supplies an inverse-fourth density; two powers
absorb this logarithm and the remaining two give the same public
inverse-square cutoff as above. -/
theorem exists_fixedIdeal_oneCell_exceptional_card_bound_logModulus
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (RingOfIntegers K))⁰) :
    ∃ Cgeom : ℝ, 0 ≤ Cgeom ∧
      ∀ {α : Type*} [DecidableEq α] (D : Data K α)
        {ell j f unitResidueCount β level x t : ℕ}
        {eta C A : ℝ}
        (rayAllowed : Finset (index K → ZMod f)) (height : ℝ),
        (hell : 2 ≤ ell) → (hf0 : f ≠ 0) → (hx : 1 < x) →
        (hfmodulus : f ≤ (t + 1) ^ j) →
        (hfprod : f.Coprime (D.sievePrimes.prod id)) →
        (hgood : ∀ p ∈ D.sievePrimes,
          p.Coprime (Ideal.absNorm (J : Ideal (RingOfIntegers K)))) →
        (hray : ell ^ j * rayAllowed.card = unitResidueCount) →
        (hj : j = oddTensorDepth t) →
        (hβ : 1 ≤ β) → (hlevel : 1 ≤ level) →
        (hheight : ∀ (d : ℕ) [NeZero d], d ∣ D.sievePrimes.prod id →
          d ≤ level → ((f * d : ℕ) : ℝ) ≤ height) →
        (hdivisor : ∀ (d : ℕ) [NeZero d] [NeZero (f * d)]
          (hd : d ∣ D.sievePrimes.prod id),
          normDivisorMass D d =
            (allowedGeneratorResidueCellCount J (f * d)
              (combinedCoordinateResidues K
                (Nat.Coprime.of_dvd_right hd hfprod)
                rayAllowed
                (normDivisibleResidues K d
                  ((coordinateAlgebraNormResidueSystem K J).normMod d)))
              height : ℕ)) →
        (hmain : ∀ (d : ℕ) [NeZero d], d ∣ D.sievePrimes.prod id →
          D.nu d * D.totalMass =
            combinedRayUnitNormDensity K ell j f d unitResidueCount
                ((coordinateAlgebraNormResidueSystem K J).normMod d) *
              (generatorCellMainConstant K J *
                height ^ Nat.card (index K))) →
        (fibreCard : ℕ) →
        (hfibre : (fibreCard : ℝ) ≤ normSiftedMass D) →
        D.totalMass *
            upperMainTerm (rosserStoppingPredicate β level)
              (fun p ↦ D.nu p) (ascendingSievePrimes D) ≤
          A * ((ell : ℝ)⁻¹) ^ j * Real.log (f : ℝ) *
            ((x : ℝ) / Real.log (x : ℝ)) →
        (Cgeom * rayAllowed.card *
            (height / f) ^ (Nat.card (index K) - 1)) * level ≤
          C * (x : ℝ) ^
            (1 - (Nat.card (index K) : ℝ)⁻¹ + eta) →
        0 ≤ ((ascendingSievePrimes D).map
            fun p ↦ 1 + (Nat.card (index K) : ℝ) / p).prod →
        ((ascendingSievePrimes D).map
            fun p ↦ 1 + (Nat.card (index K) : ℝ) / p).prod ≤
          Real.log (x : ℝ) ^ (Nat.card (index K) : ℝ) →
        0 ≤ C →
        0 ≤ A →
        (fibreCard : ℝ) ≤
          (4 * A) * ((x : ℝ) / Real.log (x : ℝ)) /
              (((t + 1 : ℕ) : ℝ) ^ 2) +
            realRosserCellEnvelope (Nat.card (index K))
              (Nat.card (index K)) eta C (x : ℝ) := by
  classical
  obtain ⟨Cgeom, hCgeom, hsift⟩ :=
    exists_fixedIdeal_oneCell_normSiftedMass_bound K J
  refine ⟨Cgeom, hCgeom, ?_⟩
  intro α _ D ell j f unitResidueCount β level x t eta C A
    rayAllowed height hell hf0 hx hfmodulus hfprod hgood hray hj hβ hlevel
    hheight hdivisor hmain fibreCard hfibre hmainScale hboundaryScale
    hEuler0 hEulerGrowth hC0 hA
  have hell0 : ell ≠ 0 := by omega
  have hsift' := hsift D rayAllowed height hell0
    hf0 hfprod hgood hray hβ hlevel hheight hdivisor hmain
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hlogx : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast hx)
  have hscale : 0 ≤ (x : ℝ) / Real.log (x : ℝ) := by positivity
  have hfmodulus' : f ≤ (t + 1) ^ oddTensorDepth t := by
    simpa only [hj] using hfmodulus
  have htensorLog :
      ((ell : ℝ)⁻¹) ^ j * Real.log (f : ℝ) ≤
        4 / (((t + 1 : ℕ) : ℝ) ^ 2) := by
    rw [hj]
    exact oddTensorDepth_geometric_mul_log_modulus_le_inverseSquare
      hell hf0 hfmodulus'
  have hmainFinal :
      D.totalMass *
          upperMainTerm (rosserStoppingPredicate β level)
            (fun p ↦ D.nu p) (ascendingSievePrimes D) ≤
        (4 * A) * ((x : ℝ) / Real.log (x : ℝ)) /
          (((t + 1 : ℕ) : ℝ) ^ 2) := by
    refine hmainScale.trans ?_
    have hnonneg : 0 ≤ A * ((x : ℝ) / Real.log (x : ℝ)) :=
      mul_nonneg hA hscale
    calc
      A * ((ell : ℝ)⁻¹) ^ j * Real.log (f : ℝ) *
            ((x : ℝ) / Real.log (x : ℝ)) =
          (A * ((x : ℝ) / Real.log (x : ℝ))) *
            (((ell : ℝ)⁻¹) ^ j * Real.log (f : ℝ)) := by ring
      _ ≤ (A * ((x : ℝ) / Real.log (x : ℝ))) *
            (4 / (((t + 1 : ℕ) : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left htensorLog hnonneg
      _ = (4 * A) * ((x : ℝ) / Real.log (x : ℝ)) /
            (((t + 1 : ℕ) : ℝ) ^ 2) := by ring
  have hboundary :
      (Cgeom * rayAllowed.card *
          (height / f) ^ (Nat.card (index K) - 1)) *
          level *
            ((ascendingSievePrimes D).map
              fun p ↦ 1 + (Nat.card (index K) : ℝ) / p).prod ≤
        realRosserCellEnvelope (Nat.card (index K))
          (Nat.card (index K)) eta C (x : ℝ) := by
    calc
      (Cgeom * rayAllowed.card *
          (height / f) ^ (Nat.card (index K) - 1)) *
          level *
            ((ascendingSievePrimes D).map
              fun p ↦ 1 + (Nat.card (index K) : ℝ) / p).prod ≤
        (C * (x : ℝ) ^
          (1 - (Nat.card (index K) : ℝ)⁻¹ + eta)) *
            Real.log (x : ℝ) ^ (Nat.card (index K) : ℝ) :=
        mul_le_mul hboundaryScale hEulerGrowth hEuler0
          (mul_nonneg hC0 (Real.rpow_nonneg hx0.le _))
      _ = realRosserCellEnvelope (Nat.card (index K))
          (Nat.card (index K)) eta C (x : ℝ) := by
        unfold realRosserCellEnvelope
        ring
  exact hfibre.trans <| hsift'.trans <|
    add_le_add hmainFinal hboundary

end Erdos980.ElliottTail.OddRayNormRosser
