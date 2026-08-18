/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.GreedyBookkeeping
import ErdosProblems.Erdos186.CFP.PreprocessingBilu
import ErdosProblems.Erdos186.CFP.WitnessAssembly

/-!
# From CFP preprocessing to a fixed-scale witness

This file packages the exact boundary after the deterministic preprocessing
and greedy bookkeeping.  The remaining input is a finite random-partition
certificate: pairwise disjoint reserves whose heterogeneous subset sums cover
a translated proper dilate.  In particular, neither an `HApproximation`
family nor a dyadic-bin certificate occurs in the source-facing theorem.
-/

namespace Erdos186.CFP

open scoped BigOperators

noncomputable section

namespace Stability

/-- The one-dimensional integer embedding is injective. -/
theorem integerPoint_injective : Function.Injective integerPoint := by
  intro a b hab
  have hcomponent := congrFun hab (0 : Fin 1)
  simpa using hcomponent

/-- Passing to one-dimensional lattice points preserves cardinality. -/
@[simp]
theorem card_integerPoints (A : Finset ℤ) :
    (integerPoints A).card = A.card := by
  classical
  exact Finset.card_image_of_injective A integerPoint_injective

/-- Passing to one-dimensional lattice points preserves inclusion. -/
theorem integerPoints_mono {A B : Finset ℤ} (hAB : A ⊆ B) :
    integerPoints A ⊆ integerPoints B := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := mem_integerPoints_iff.mp hx
  exact integerPoint_mem_integerPoints_iff.mpr (hAB ha)

end Stability

/-- The deterministic cardinality loss in CFP Lemma 2.38. -/
def preprocessingCardinalityLoss
    (A : Finset ℤ) (stableBudget maxRank : ℕ) : ℕ :=
  (2 * stableBudget) * Preprocessing.boxPotential A maxRank + stableBudget

/-- The exact finite output still required after preprocessing and the
outer greedy bookkeeping.  This is the random-partition/dense-coverage
boundary: every field is concrete finite data consumed directly by
`enhancedCFPWitness_of_disjoint_reserveFamily`.

`integerCore` permits the structured core to be the unselected part of the
stable core.  Its extra loss is kept separate from the deterministic
preprocessing loss. -/
structure PreprocessedReserveCertificate (stableCore : Finset ℤ)
    (s D extraLoss scaleNum scaleDen : ℕ) where
  integerCore : Finset ℤ
  integerCore_subset : integerCore ⊆ stableCore
  stableCore_large : stableCore.card ≤ integerCore.card + extraLoss
  ell : ℕ
  rank : ℕ
  k : ℕ
  reserve : Fin ell → Finset (LatticePoint 1)
  progression : GAP 1 rank
  translatePoint : LatticePoint 1
  reserve_pairwiseDisjoint :
    (Set.univ : Set (Fin ell)).PairwiseDisjoint reserve
  rank_le : rank ≤ D
  reserve_subset_core :
    ∀ i, reserve i ⊆ Stability.integerPoints integerCore
  reserve_small : (∑ i, (reserve i).card) ≤ s
  core_zero_subset :
    insert 0 (Stability.integerPoints integerCore) ⊆ progression.carrier
  homogeneous : progression.Homogeneous
  covered :
    translate translatePoint (progression.dilate k).carrier ⊆
      heterogeneousSumset (fun i ↦ GAP.subsetSums (reserve i))
  dilate_proper : (progression.dilate k).Proper
  k_pos : 0 < k
  scaleNum_pos : 0 < scaleNum
  scaleDen_pos : 0 < scaleDen
  scale_lower : scaleNum * s ≤ scaleDen * k
  scale_upper : k ≤ s
  progression_proper : progression.Proper
  progression_symmetric : progression.Symmetric
  progression_nondegenerate : progression.Nondegenerate
  covered_translate_homogeneous :
    ∃ z : Fin rank → ℤ,
      translatePoint + (progression.dilate k).offset =
        (fun j ↦ ∑ i, z i * progression.steps i j)

namespace PreprocessedReserveCertificate

variable {stableCore A : Finset ℤ}
    {s D extraLoss scaleNum scaleDen preprocessingLoss : ℕ}

/-- Assemble an enhanced witness once preprocessing has embedded the stable
core in the source. -/
noncomputable def enhanced
    (C : PreprocessedReserveCertificate stableCore s D extraLoss
      scaleNum scaleDen)
    (hstableSource : stableCore ⊆ A)
    (hsourceLarge : A.card ≤ stableCore.card + preprocessingLoss) :
    EnhancedCFPWitness (Stability.integerPoints A) s D C.k
      (preprocessingLoss + extraLoss) := by
  apply enhancedCFPWitness_of_disjoint_reserveFamily
    C.reserve C.progression C.translatePoint
    C.reserve_pairwiseDisjoint C.rank_le
    (Stability.integerPoints_mono
      (C.integerCore_subset.trans hstableSource))
    C.reserve_subset_core
  · have hcoreLarge := C.stableCore_large
    simpa only [Stability.card_integerPoints] using
      (show A.card ≤ C.integerCore.card +
          (preprocessingLoss + extraLoss) by omega)
  · exact C.reserve_small
  · exact C.core_zero_subset
  · exact C.homogeneous
  · exact C.covered
  · exact C.dilate_proper
  · exact C.k_pos
  · exact C.scaleNum_pos
  · exact C.scaleDen_pos
  · exact C.scale_lower
  · exact C.scale_upper
  · exact C.progression_proper
  · exact C.progression_symmetric
  · exact C.progression_nondegenerate
  · exact C.covered_translate_homogeneous

/-- The same assembly with the two externally fixed scale constants exposed
by the `FixedScaleWitness` subtype. -/
noncomputable def fixed
    (C : PreprocessedReserveCertificate stableCore s D extraLoss
      scaleNum scaleDen)
    (hstableSource : stableCore ⊆ A)
    (hsourceLarge : A.card ≤ stableCore.card + preprocessingLoss) :
    FixedScaleWitness (Stability.integerPoints A) s D C.k
      (preprocessingLoss + extraLoss) scaleNum scaleDen :=
  ⟨C.enhanced hstableSource hsourceLarge, rfl, rfl⟩

end PreprocessedReserveCertificate

/-- The sole post-preprocessing boundary.  It receives the actual stable core
and the canonical minimal-box stability derived from the fixed-reference
preprocessing result, and returns the concrete reserve/coverage certificate.
There is no approximation family or dyadic certification in this interface.
-/
abbrev PreprocessedReserveCoverageInput (A : Finset ℤ)
    (stableBudget D n C0 s extraLoss scaleNum scaleDen : ℕ) : Prop :=
  ∀ (W B : Finset ℤ) (relevant : Finset ℕ)
    (hproper : Stability.RelevantBoxesProper W relevant),
    B ⊆ W → W ⊆ A → 0 ∈ B →
    Stability.StronglyStableFor B (Stability.minimalBoxFamily W)
      stableBudget D (n ^ 2) relevant
      (Stability.minimalIdentificationFamily hproper) C0 →
    Stability.WeaklyStableMinimalFor B stableBudget D n →
    Nonempty
      (PreprocessedReserveCertificate B s D extraLoss scaleNum scaleDen)

/-- Join a concrete CFP preprocessing approximation argument to the exact
reserve/coverage boundary.  The dyadic bins do not appear: their construction
has already been discharged in `GreedyBookkeeping`. -/
theorem exists_fixedScaleWitness_of_preprocessing
    {A : Finset ℤ}
    {stableBudget D n C0 preprocessingScaleNum preprocessingScaleDen
      s extraLoss scaleNum scaleDen : ℕ}
    (hzero : 0 ∈ A) (hC0 : 0 < C0)
    (hA : ∀ z ∈ A, 0 ≤ z ∧ z < (n : ℤ))
    (happrox : PreprocessingBilu.PreprocessingHApproximationArgument A
      stableBudget D n C0 preprocessingScaleNum preprocessingScaleDen)
    (hcoverage : PreprocessedReserveCoverageInput A stableBudget D n C0
      s extraLoss scaleNum scaleDen) :
    ∃ k, Nonempty
      (FixedScaleWitness (Stability.integerPoints A) s D k
        (preprocessingCardinalityLoss A stableBudget D + extraLoss)
        scaleNum scaleDen) := by
  obtain ⟨W, B, relevant, hproper, hBW, hWA, hzeroB, hcard, hstable⟩ :=
    Preprocessing.preprocessing_lemma238 hzero hC0 hA happrox
  have hcanonical :
      Stability.WeaklyStableMinimalFor B stableBudget D n :=
    Greedy.weaklyStableMinimalFor_of_fixed_minimalBox hBW hstable.weaklyStable
  let C := Classical.choice
    (hcoverage W B relevant hproper hBW hWA hzeroB hstable hcanonical)
  refine ⟨C.k, ⟨C.fixed (hBW.trans hWA) ?_⟩⟩
  simpa only [preprocessingCardinalityLoss, Nat.add_assoc] using hcard

/-- Source-facing constructor.  Bilu--Freiman supplies all approximation
families and all preprocessing constants uniformly.  The only remaining
argument is the concrete post-preprocessing reserve/coverage event.

The final scale numerator and denominator are parameters outside the source
set quantifier, so the result really is a `FixedScaleWitness` family. -/
theorem exists_uniform_preprocessedFixedScaleWitness_of_biluFreiman
    (hBF : BiluFreiman.BiluFreimanStatement)
    (D : ℕ) (hD : 2 ≤ D)
    (s extraLoss scaleNum scaleDen : ℕ) :
    ∃ first horizonFactor propernessDenominator C0 : ℕ,
      0 < first ∧ 0 < horizonFactor ∧ 0 < propernessDenominator ∧
      0 < C0 ∧
      C0 = PreprocessingBilu.preprocessingRobustnessDenominator D
        propernessDenominator ∧
      ∀ {A : Finset ℤ} {n h last stableBudget : ℕ},
        0 ∈ A →
        A ⊆ Finset.Icc (0 : ℤ) ((n : ℤ) - 1) →
        h = horizonFactor * 2 ^ last →
        h ≤ n →
        n ≤ h ^ (D - 1) →
        first < last →
        (2 * D + 1) * first +
            2 * horizonFactor * (D - 1) < last →
        PreprocessingBilu.preprocessingIndexBound D
            propernessDenominator ≤ h →
        PreprocessedReserveCoverageInput A stableBudget D n C0 s
          extraLoss scaleNum scaleDen →
        ∃ k, Nonempty
          (FixedScaleWitness (Stability.integerPoints A) s D k
            (preprocessingCardinalityLoss A stableBudget D + extraLoss)
            scaleNum scaleDen) := by
  obtain ⟨first, horizonFactor, propernessDenominator, C0, hfirst,
      hhorizon, hdenominator, hC0, hC0eq, happrox⟩ :=
    PreprocessingBilu.exists_preprocessingHApproximationArgument_of_biluFreiman
      hBF D hD
  refine ⟨first, horizonFactor, propernessDenominator, C0, hfirst,
    hhorizon, hdenominator, hC0, hC0eq, ?_⟩
  intro A n h last stableBudget hzero hinterval hh hhle hnpower
    hfirstLast hlastLarge hlarge hcoverage
  apply exists_fixedScaleWitness_of_preprocessing
    (A := A) (stableBudget := stableBudget) (D := D) (n := n) (C0 := C0)
    (preprocessingScaleNum := 1)
    (preprocessingScaleDen :=
      PreprocessingBilu.preprocessingScaleDen propernessDenominator)
    (s := s) (extraLoss := extraLoss) (scaleNum := scaleNum)
    (scaleDen := scaleDen)
    hzero hC0
  · intro z hz
    have hzIcc := Finset.mem_Icc.mp (hinterval hz)
    exact ⟨hzIcc.1, by omega⟩
  · exact happrox hzero hinterval hh hhle hnpower hfirstLast hlastLarge hlarge
  · exact hcoverage

/-! Axiom audit for the terminal handoff. -/

#print axioms PreprocessedReserveCertificate.enhanced
#print axioms exists_fixedScaleWitness_of_preprocessing
#print axioms exists_uniform_preprocessedFixedScaleWitness_of_biluFreiman

end

end Erdos186.CFP
