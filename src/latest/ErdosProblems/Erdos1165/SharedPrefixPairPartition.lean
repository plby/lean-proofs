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
# A shared-prefix partition for a two-branch stopped skeleton

The far-pair argument has one retained prefix and two collections of
post-split stopped bridges.  This file provides the bookkeeping adapter which
stores the common prefix datum only once.  Coordinates `0, ..., mLeft - 1`
belong to the left branch and the remaining coordinates belong to the right
branch.

The final constructor is deliberately pathwise.  Its atom masses are not
hypotheses: they are proved from concrete prefix-free finite-word insertion
objects using `MarkedBridgeFactorization`.  The hypotheses left to an annular
instantiation are exactly event coverage/disjointness, equality of the
literal insertion events with the annular atoms, and identification of each
stopped-word bridge sum with the desired annular kernel.  In particular, no
two-point probability estimate is assumed here.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.SharedPrefixPairPartition

open MarkedBridgeFactorization MarkedSkeletonPartition
open MarkedSkeletonPartitionUpper MarkedTerminalDisintegration

noncomputable section

/-- A two-branch data code in which the common prefix datum occurs once. -/
abbrev PairData (Shared LeftData RightData : Type*) :=
  Shared × (LeftData × RightData)

/-- Restrict a total coordinate vector to its left branch. -/
def leftCoordinates {mLeft mRight : ℕ} {A : Type*}
    (v : Fin (mLeft + mRight) → A) : Fin mLeft → A :=
  fun j ↦ v (Fin.castAdd mRight j)

/-- Restrict a total coordinate vector to its right branch. -/
def rightCoordinates {mLeft mRight : ℕ} {A : Type*}
    (v : Fin (mLeft + mRight) → A) : Fin mRight → A :=
  fun j ↦ v (Fin.natAdd mLeft j)

/-- Repackage a branch-indexed unmarked atom as the atom family expected by
`MarkedSkeletonPartitionUpper`. -/
def pairSkeletonAtom
    {Omega Shared LeftData RightData Entrance Exit : Type*}
    {mLeft mRight : ℕ}
    (atom : Shared → LeftData → RightData →
      (Fin mLeft → Entrance) → (Fin mLeft → Exit) →
      (Fin mRight → Entrance) → (Fin mRight → Exit) → Set Omega)
    (data : PairData Shared LeftData RightData)
    (entrance : Fin (mLeft + mRight) → Entrance)
    (exit : Fin (mLeft + mRight) → Exit) : Set Omega :=
  atom data.1 data.2.1 data.2.2
    (leftCoordinates entrance) (leftCoordinates exit)
    (rightCoordinates entrance) (rightCoordinates exit)

/-- Marked analogue of `pairSkeletonAtom`; the visit vector is split at the
same deterministic branch boundary as the endpoint vectors. -/
def pairMarkedAtom
    {Omega Shared LeftData RightData Entrance Exit : Type*}
    {mLeft mRight : ℕ}
    (atom : Shared → LeftData → RightData →
      (Fin mLeft → Entrance) → (Fin mLeft → Exit) →
      (Fin mLeft → ℕ) →
      (Fin mRight → Entrance) → (Fin mRight → Exit) →
      (Fin mRight → ℕ) → Set Omega)
    (data : PairData Shared LeftData RightData)
    (entrance : Fin (mLeft + mRight) → Entrance)
    (exit : Fin (mLeft + mRight) → Exit)
    (visits : Fin (mLeft + mRight) → ℕ) : Set Omega :=
  atom data.1 data.2.1 data.2.2
    (leftCoordinates entrance) (leftCoordinates exit) (leftCoordinates visits)
    (rightCoordinates entrance) (rightCoordinates exit) (rightCoordinates visits)

/-! ## Disjointness and coverage from extracted pair codes -/

/-- If each unmarked pair atom is the singleton fiber of an extracted
complete pair code, distinct atoms are automatically disjoint. -/
theorem pairSkeletonAtom_pairwise_of_codingFiber
    {Omega Shared LeftData RightData Entrance Exit : Type*}
    {mLeft mRight : ℕ}
    (source : Set Omega)
    (code : Omega → SkeletonIndex (PairData Shared LeftData RightData)
      Entrance Exit (mLeft + mRight))
    (atom : Shared → LeftData → RightData →
      (Fin mLeft → Entrance) → (Fin mLeft → Exit) →
      (Fin mRight → Entrance) → (Fin mRight → Exit) → Set Omega)
    (hatom : ∀ i,
      indexedSkeletonAtom (pairSkeletonAtom atom) i =
        codingFiber source code i) :
    Pairwise fun
      i j : SkeletonIndex (PairData Shared LeftData RightData)
          Entrance Exit (mLeft + mRight) ↦
        Disjoint
          (indexedSkeletonAtom (pairSkeletonAtom atom) i)
          (indexedSkeletonAtom (pairSkeletonAtom atom) j) := by
  intro i j hij
  rw [hatom i, hatom j]
  exact codingFiber_pairwise source code hij

/-- The corresponding marked fibers are also pairwise disjoint. -/
theorem pairMarkedAtom_pairwise_of_codingFiber
    {Omega Shared LeftData RightData Entrance Exit : Type*}
    {mLeft mRight : ℕ}
    (source : Set Omega)
    (code : Omega → MarkedIndex (PairData Shared LeftData RightData)
      Entrance Exit (mLeft + mRight))
    (atom : Shared → LeftData → RightData →
      (Fin mLeft → Entrance) → (Fin mLeft → Exit) →
      (Fin mLeft → ℕ) →
      (Fin mRight → Entrance) → (Fin mRight → Exit) →
      (Fin mRight → ℕ) → Set Omega)
    (hatom : ∀ i,
      indexedMarkedAtom (pairMarkedAtom atom) i =
        codingFiber source code i) :
    Pairwise fun
      i j : MarkedIndex (PairData Shared LeftData RightData)
          Entrance Exit (mLeft + mRight) ↦
        Disjoint
          (indexedMarkedAtom (pairMarkedAtom atom) i)
          (indexedMarkedAtom (pairMarkedAtom atom) j) := by
  intro i j hij
  rw [hatom i, hatom j]
  exact codingFiber_pairwise source code hij

/-- Singleton fibers of the complete extracted pair code cover their source
event exactly. -/
theorem iUnion_pairSkeletonAtom_eq_of_codingFiber
    {Omega Shared LeftData RightData Entrance Exit : Type*}
    {mLeft mRight : ℕ}
    (source : Set Omega)
    (code : Omega → SkeletonIndex (PairData Shared LeftData RightData)
      Entrance Exit (mLeft + mRight))
    (atom : Shared → LeftData → RightData →
      (Fin mLeft → Entrance) → (Fin mLeft → Exit) →
      (Fin mRight → Entrance) → (Fin mRight → Exit) → Set Omega)
    (hatom : ∀ i,
      indexedSkeletonAtom (pairSkeletonAtom atom) i =
        codingFiber source code i) :
    (⋃ i : SkeletonIndex (PairData Shared LeftData RightData)
        Entrance Exit (mLeft + mRight),
      indexedSkeletonAtom (pairSkeletonAtom atom) i) = source := by
  simp_rw [hatom]
  exact iUnion_codingFiber source code

/-- The retained-word mass supplied by the unmarked insertion atom. -/
def factorizedSkeletonWeight
    {m : ℕ} {Data Entrance Exit : Type*}
    (Complement : Data → (Fin m → Entrance) → (Fin m → Exit) → Type*)
    (Bridge : Fin m → Entrance → Exit → Type*)
    (factor : ∀ data entrance exit,
      ComplementarySkeletonAtom m (Complement data entrance exit)
        (fun j ↦ Bridge j (entrance j) (exit j)))
    (data : Data) (entrance : Fin m → Entrance)
    (exit : Fin m → Exit) : ℝ≥0∞ :=
  (factor data entrance exit).weight

/-- A common-prefix two-branch atom family gives the upper stopped-data
decomposition under the fair walk.

Unlike the lower-level partition constructor, the two exact atom-mass
identities are derived here from literal `ComplementarySkeletonAtom`s.  The
marked and unmarked insertion objects use the same retained code type, and
`hcomplementWord` says that adding visit marks does not change that retained
word.  Thus the common prefix weight occurs exactly once in both masses. -/
theorem markedStoppedDataUpperDecomposition_of_sharedPrefix_factorization
    {Shared LeftData RightData Entrance Exit : Type*}
    [Countable Shared] [Countable LeftData] [Countable RightData]
    [Countable Entrance] [Countable Exit]
    {mLeft mRight : ℕ}
    (pairEvent successful : Set StepPath)
    (skeletonAtom : Shared → LeftData → RightData →
      (Fin mLeft → Entrance) → (Fin mLeft → Exit) →
      (Fin mRight → Entrance) → (Fin mRight → Exit) → Set StepPath)
    (markedAtom : Shared → LeftData → RightData →
      (Fin mLeft → Entrance) → (Fin mLeft → Exit) →
      (Fin mLeft → ℕ) →
      (Fin mRight → Entrance) → (Fin mRight → Exit) →
      (Fin mRight → ℕ) → Set StepPath)
    (skeletonKernel : Fin (mLeft + mRight) → Entrance → Exit → ℝ≥0∞)
    (markedKernel : Fin (mLeft + mRight) → Entrance → ℕ → Exit → ℝ≥0∞)
    (visitEvent : Set (Fin (mLeft + mRight) → ℕ))
    (Complement : PairData Shared LeftData RightData →
      (Fin (mLeft + mRight) → Entrance) →
      (Fin (mLeft + mRight) → Exit) → Type*)
    (UnmarkedBridge : Fin (mLeft + mRight) → Entrance → Exit → Type*)
    (MarkedBridge : Fin (mLeft + mRight) → Entrance → ℕ → Exit → Type*)
    [∀ data entrance exit, Countable (Complement data entrance exit)]
    [∀ j entrance exit, Countable (UnmarkedBridge j entrance exit)]
    [∀ j entrance visits exit,
      Countable (MarkedBridge j entrance visits exit)]
    (unmarkedFactor : ∀ data entrance exit,
      ComplementarySkeletonAtom (mLeft + mRight)
        (Complement data entrance exit)
        (fun j ↦ UnmarkedBridge j (entrance j) (exit j)))
    (markedFactor : ∀ data entrance exit visits,
      ComplementarySkeletonAtom (mLeft + mRight)
        (Complement data entrance exit)
        (fun j ↦ MarkedBridge j (entrance j) (visits j) (exit j)))
    (hskeleton_event : ∀ data entrance exit,
      pairSkeletonAtom skeletonAtom data entrance exit =
        (unmarkedFactor data entrance exit).event)
    (hmarked_event : ∀ data entrance exit visits,
      pairMarkedAtom markedAtom data entrance exit visits =
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
      i j : SkeletonIndex (PairData Shared LeftData RightData)
          Entrance Exit (mLeft + mRight) ↦
        Disjoint
          (indexedSkeletonAtom (pairSkeletonAtom skeletonAtom) i)
          (indexedSkeletonAtom (pairSkeletonAtom skeletonAtom) j))
    (hmarked_disjoint : Pairwise fun
      i j : MarkedIndex (PairData Shared LeftData RightData)
          Entrance Exit (mLeft + mRight) ↦
        Disjoint
          (indexedMarkedAtom (pairMarkedAtom markedAtom) i)
          (indexedMarkedAtom (pairMarkedAtom markedAtom) j))
    (hsuccessful : successful =
      ⋃ i : SkeletonIndex (PairData Shared LeftData RightData)
          Entrance Exit (mLeft + mRight),
        indexedSkeletonAtom (pairSkeletonAtom skeletonAtom) i)
    (hpair_union : pairEvent ⊆
      ⋃ i : MarkedIndex (PairData Shared LeftData RightData)
          Entrance Exit (mLeft + mRight),
        restrictedMarkedAtom visitEvent (pairMarkedAtom markedAtom) i) :
    AppendixPairMoment.MarkedStoppedDataUpperDecomposition fairSteps
      pairEvent successful
      (factorizedSkeletonWeight Complement UnmarkedBridge unmarkedFactor)
      skeletonKernel markedKernel visitEvent := by
  classical
  apply markedStoppedDataUpperDecomposition_of_atom_partition fairSteps
    pairEvent successful
    (factorizedSkeletonWeight Complement UnmarkedBridge unmarkedFactor)
    skeletonKernel markedKernel visitEvent
    (pairSkeletonAtom skeletonAtom) (pairMarkedAtom markedAtom)
  · intro data entrance exit
    rw [hskeleton_event]
    exact measurableSet_stoppedWordEvent _
  · intro data entrance exit visits
    rw [hmarked_event]
    exact measurableSet_stoppedWordEvent _
  · exact hskeleton_disjoint
  · exact hmarked_disjoint
  · exact hsuccessful
  · exact hpair_union
  · intro data entrance exit
    rw [hskeleton_event,
      fairSteps_event_eq_weight_mul_prod_kernel]
    apply congrArg ((unmarkedFactor data entrance exit).weight * ·)
    unfold skeletonProduct
    apply Finset.prod_congr rfl
    intro j _hj
    exact hunmarkedKernel data entrance exit j
  · intro data entrance exit visits
    rw [hmarked_event,
      fairSteps_event_eq_weight_mul_prod_kernel]
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

end

end Erdos1165.SharedPrefixPairPartition
