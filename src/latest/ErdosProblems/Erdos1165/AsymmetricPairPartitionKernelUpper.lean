/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricPairPartitionUpper
import ErdosProblems.Erdos1165.MarkedSkeletonPartitionKernelUpper

/-!
# Asymmetric factorization with a dominated marked bridge family

At the split scanner the erased right bridge is restricted to a compatible
subtype.  Its kernel is generally only bounded by the canonical terminal
kernel.  This file turns precisely that one-sided comparison into the marked
stopped-data upper decomposition; no false event or kernel equality is used.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.AsymmetricPairPartitionKernelUpper

open AppendixPairMoment AsymmetricPairPartitionUpper
open MarkedBridgeFactorization MarkedSkeletonPartition
open MarkedSkeletonPartitionKernelUpper MarkedTerminalDisintegration

noncomputable section

/-- Literal asymmetric insertion atoms where the unmarked comparison family
has its exact canonical kernel and the selected marked family is merely
dominated coordinatewise by the canonical marked kernel. -/
theorem markedStoppedDataUpperDecomposition_of_asymmetric_kernelUpper
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
      (markedFactor data entrance exit visits).kernel j ≤
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
    MarkedStoppedDataUpperDecomposition fairSteps pairEvent
      (asymmetricSuccessful skeletonAtom)
      (asymmetricSkeletonWeight Complement UnmarkedBridge unmarkedFactor)
      skeletonKernel markedKernel visitEvent := by
  classical
  apply markedStoppedDataUpperDecomposition_of_atom_partition_kernelUpper
    fairSteps pairEvent (asymmetricSuccessful skeletonAtom)
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
    have hproduct :
        ∏ j, (markedFactor data entrance exit visits).kernel j ≤
          markedProduct markedKernel entrance exit visits := by
      unfold markedProduct
      apply Finset.prod_le_prod
      · intro j _hj
        exact bot_le
      · intro j _hj
        exact hmarkedKernel data entrance exit visits j
    exact mul_le_mul le_rfl hproduct bot_le bot_le

end

end Erdos1165.AsymmetricPairPartitionKernelUpper
