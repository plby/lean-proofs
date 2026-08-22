/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.MarkedSkeletonPartitionUpper
import ErdosProblems.Erdos1165.MarkedBridgeFactorization

/-!
# Asymmetric marked insertion partitions for the far-pair upper bound

In HLOZ (A.16), the complete successful history at the first point is
retained, while only the post-separation continuation at the second point is
regenerated.  Consequently the union of unmarked insertion atoms need not
equal the two-point successful event.  What is needed is the sound pair of
one-sided statements:

* the thick-pair event is contained in the selected marked insertion union;
* the whole unmarked insertion union is contained in the retained one-point
  event.

This module converts those pathwise facts and literal prefix-free insertion
atoms into `MarkedStoppedDataUpperDecomposition`.  Both atom-mass identities
are proved here from stopped-word factorization; no probability estimate is
accepted as a premise.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.AsymmetricPairPartitionUpper

open MarkedBridgeFactorization MarkedSkeletonPartition
open MarkedSkeletonPartitionUpper MarkedTerminalDisintegration

noncomputable section

/-- The common retained-word weight of an unmarked complementary skeleton. -/
def asymmetricSkeletonWeight
    {m : ℕ} {Data Entrance Exit : Type*}
    (Complement : Data → (Fin m → Entrance) → (Fin m → Exit) → Type*)
    (Bridge : Fin m → Entrance → Exit → Type*)
    (factor : ∀ data entrance exit,
      ComplementarySkeletonAtom m (Complement data entrance exit)
        (fun j ↦ Bridge j (entrance j) (exit j)))
    (data : Data) (entrance : Fin m → Entrance)
    (exit : Fin m → Exit) : ℝ≥0∞ :=
  (factor data entrance exit).weight

/-- The literal unmarked insertion union associated with an asymmetric
factorization.  Exposing this definition lets the two-stage radial-word
summation use exactly the same successful event as the marked upper
decomposition. -/
def asymmetricSuccessful
    {Data Entrance Exit : Type*} {m : ℕ}
    (skeletonAtom : Data → (Fin m → Entrance) →
      (Fin m → Exit) → Set StepPath) : Set StepPath :=
  ⋃ i : SkeletonIndex Data Entrance Exit m,
    indexedSkeletonAtom skeletonAtom i

/-- Direct, non-existential form of the asymmetric stopped-data
decomposition.  Its successful event is definitionally the full unmarked
insertion union. -/
theorem markedStoppedDataUpperDecomposition_of_asymmetric_factorization
    {Data Entrance Exit : Type*}
    [Countable Data] [Countable Entrance] [Countable Exit]
    {m : ℕ}
    (pairEvent : Set StepPath)
    (skeletonAtom : Data → (Fin m → Entrance) →
      (Fin m → Exit) → Set StepPath)
    (markedAtom : Data → (Fin m → Entrance) →
      (Fin m → Exit) → (Fin m → ℕ) → Set StepPath)
    (skeletonKernel : Fin m → Entrance → Exit → ℝ≥0∞)
    (markedKernel : Fin m → Entrance → ℕ → Exit → ℝ≥0∞)
    (visitEvent : Set (Fin m → ℕ))
    (Complement : Data → (Fin m → Entrance) →
      (Fin m → Exit) → Type*)
    (UnmarkedBridge : Fin m → Entrance → Exit → Type*)
    (MarkedBridge : Fin m → Entrance → ℕ → Exit → Type*)
    [∀ data entrance exit, Countable (Complement data entrance exit)]
    [∀ j entrance exit, Countable (UnmarkedBridge j entrance exit)]
    [∀ j entrance visits exit,
      Countable (MarkedBridge j entrance visits exit)]
    (unmarkedFactor : ∀ data entrance exit,
      ComplementarySkeletonAtom m (Complement data entrance exit)
        (fun j ↦ UnmarkedBridge j (entrance j) (exit j)))
    (markedFactor : ∀ data entrance exit visits,
      ComplementarySkeletonAtom m (Complement data entrance exit)
        (fun j ↦ MarkedBridge j (entrance j) (visits j) (exit j)))
    (hskeleton_event : ∀ data entrance exit,
      skeletonAtom data entrance exit =
        (unmarkedFactor data entrance exit).event)
    (hmarked_event : ∀ data entrance exit visits,
      markedAtom data entrance exit visits =
        (markedFactor data entrance exit visits).event)
    (hcomplementWord : ∀ data entrance exit visits complement,
      (markedFactor data entrance exit visits).complementWord complement =
        (unmarkedFactor data entrance exit).complementWord complement)
    (hunmarkedKernel : ∀ data entrance exit j,
      (unmarkedFactor data entrance exit).kernel j =
        skeletonKernel j (entrance j) (exit j))
    (hmarkedKernel : ∀ data entrance exit visits j,
      (markedFactor data entrance exit visits).kernel j =
        markedKernel j (entrance j) (visits j) (exit j))
    (hskeleton_disjoint : Pairwise fun
      i j : SkeletonIndex Data Entrance Exit m ↦
        Disjoint (indexedSkeletonAtom skeletonAtom i)
          (indexedSkeletonAtom skeletonAtom j))
    (hmarked_disjoint : Pairwise fun
      i j : MarkedIndex Data Entrance Exit m ↦
        Disjoint (indexedMarkedAtom markedAtom i)
          (indexedMarkedAtom markedAtom j))
    (hpair_union : pairEvent ⊆
      ⋃ i : MarkedIndex Data Entrance Exit m,
        restrictedMarkedAtom visitEvent markedAtom i) :
    AppendixPairMoment.MarkedStoppedDataUpperDecomposition fairSteps
      pairEvent (asymmetricSuccessful skeletonAtom)
      (asymmetricSkeletonWeight Complement UnmarkedBridge unmarkedFactor)
      skeletonKernel markedKernel visitEvent := by
  classical
  apply markedStoppedDataUpperDecomposition_of_atom_partition fairSteps
    pairEvent (asymmetricSuccessful skeletonAtom)
    (asymmetricSkeletonWeight Complement UnmarkedBridge unmarkedFactor)
    skeletonKernel markedKernel visitEvent skeletonAtom markedAtom
  · intro data entrance exit
    rw [hskeleton_event]
    exact measurableSet_stoppedWordEvent _
  · intro data entrance exit visits
    rw [hmarked_event]
    exact measurableSet_stoppedWordEvent _
  · exact hskeleton_disjoint
  · exact hmarked_disjoint
  · rfl
  · exact hpair_union
  · intro data entrance exit
    rw [hskeleton_event, fairSteps_event_eq_weight_mul_prod_kernel]
    apply congrArg ((unmarkedFactor data entrance exit).weight * ·)
    unfold skeletonProduct
    apply Finset.prod_congr rfl
    intro j _hj
    exact hunmarkedKernel data entrance exit j
  · intro data entrance exit visits
    rw [hmarked_event, fairSteps_event_eq_weight_mul_prod_kernel]
    have hweight : (markedFactor data entrance exit visits).weight =
        (unmarkedFactor data entrance exit).weight := by
      unfold ComplementarySkeletonAtom.weight
      apply tsum_congr
      intro complement
      rw [hcomplementWord data entrance exit visits complement]
    rw [hweight]
    apply congrArg ((unmarkedFactor data entrance exit).weight * ·)
    unfold markedProduct
    apply Finset.prod_congr rfl
    intro j _hj
    exact hmarkedKernel data entrance exit visits j

/-- Literal asymmetric insertion atoms construct an upper stopped-data
decomposition whose retained event is automatically bounded by the chosen
one-point event. -/
theorem exists_markedStoppedDataUpperDecomposition_of_asymmetric_factorization
    {Data Entrance Exit : Type*}
    [Countable Data] [Countable Entrance] [Countable Exit]
    {m : ℕ}
    (pairEvent retainedEvent : Set StepPath)
    (skeletonAtom : Data → (Fin m → Entrance) →
      (Fin m → Exit) → Set StepPath)
    (markedAtom : Data → (Fin m → Entrance) →
      (Fin m → Exit) → (Fin m → ℕ) → Set StepPath)
    (skeletonKernel : Fin m → Entrance → Exit → ℝ≥0∞)
    (markedKernel : Fin m → Entrance → ℕ → Exit → ℝ≥0∞)
    (visitEvent : Set (Fin m → ℕ))
    (Complement : Data → (Fin m → Entrance) →
      (Fin m → Exit) → Type*)
    (UnmarkedBridge : Fin m → Entrance → Exit → Type*)
    (MarkedBridge : Fin m → Entrance → ℕ → Exit → Type*)
    [∀ data entrance exit, Countable (Complement data entrance exit)]
    [∀ j entrance exit, Countable (UnmarkedBridge j entrance exit)]
    [∀ j entrance visits exit,
      Countable (MarkedBridge j entrance visits exit)]
    (unmarkedFactor : ∀ data entrance exit,
      ComplementarySkeletonAtom m (Complement data entrance exit)
        (fun j ↦ UnmarkedBridge j (entrance j) (exit j)))
    (markedFactor : ∀ data entrance exit visits,
      ComplementarySkeletonAtom m (Complement data entrance exit)
        (fun j ↦ MarkedBridge j (entrance j) (visits j) (exit j)))
    (hskeleton_event : ∀ data entrance exit,
      skeletonAtom data entrance exit =
        (unmarkedFactor data entrance exit).event)
    (hmarked_event : ∀ data entrance exit visits,
      markedAtom data entrance exit visits =
        (markedFactor data entrance exit visits).event)
    (hcomplementWord : ∀ data entrance exit visits complement,
      (markedFactor data entrance exit visits).complementWord complement =
        (unmarkedFactor data entrance exit).complementWord complement)
    (hunmarkedKernel : ∀ data entrance exit j,
      (unmarkedFactor data entrance exit).kernel j =
        skeletonKernel j (entrance j) (exit j))
    (hmarkedKernel : ∀ data entrance exit visits j,
      (markedFactor data entrance exit visits).kernel j =
        markedKernel j (entrance j) (visits j) (exit j))
    (hskeleton_disjoint : Pairwise fun
      i j : SkeletonIndex Data Entrance Exit m ↦
        Disjoint (indexedSkeletonAtom skeletonAtom i)
          (indexedSkeletonAtom skeletonAtom j))
    (hmarked_disjoint : Pairwise fun
      i j : MarkedIndex Data Entrance Exit m ↦
        Disjoint (indexedMarkedAtom markedAtom i)
          (indexedMarkedAtom markedAtom j))
    (hunmarked_retained :
      (⋃ i : SkeletonIndex Data Entrance Exit m,
        indexedSkeletonAtom skeletonAtom i) ⊆ retainedEvent)
    (hpair_union : pairEvent ⊆
      ⋃ i : MarkedIndex Data Entrance Exit m,
        restrictedMarkedAtom visitEvent markedAtom i) :
    ∃ successful : Set StepPath,
      AppendixPairMoment.MarkedStoppedDataUpperDecomposition fairSteps
        pairEvent successful
        (asymmetricSkeletonWeight Complement UnmarkedBridge unmarkedFactor)
        skeletonKernel markedKernel visitEvent ∧
      fairSteps.real successful ≤ fairSteps.real retainedEvent := by
  classical
  refine ⟨asymmetricSuccessful skeletonAtom, ?_,
    measureReal_mono hunmarked_retained⟩
  exact markedStoppedDataUpperDecomposition_of_asymmetric_factorization
    pairEvent skeletonAtom markedAtom skeletonKernel markedKernel visitEvent
    Complement UnmarkedBridge MarkedBridge unmarkedFactor markedFactor
    hskeleton_event hmarked_event hcomplementWord hunmarkedKernel hmarkedKernel
    hskeleton_disjoint hmarked_disjoint hpair_union

end

end Erdos1165.AsymmetricPairPartitionUpper
