/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricCoarseNormalizedCompletionRows
import ErdosProblems.Erdos1165.AsymmetricTerminalPartitionAdapter

/-!
# Successful-event containment forced by concrete coarse completion rows

This file records the precise event represented by the unrestricted terminal
adapter, and the containment forced by any concrete coarse completion-tail
family.  It is useful when checking that the successful event supplied to the
final pair constructor is the pair-success event rather than unrestricted
success at the right centre.
-/

open Set

namespace Erdos1165.AsymmetricCompletionSuccessfulContainment

open AsymmetricCoarseCompletionCode
open AsymmetricCoarseNormalizedCompletionRows
open AsymmetricPairPartitionUpper AsymmetricTerminalPartitionAdapter
open Proposition13Assembly
open TerminalMarkedSkeletonDecomposition TerminalSkeletonWords

noncomputable section

/-- The unrestricted terminal adapter indexes exactly the complete stopped
successful event at its centre. -/
theorem asymmetricSuccessful_terminalSkeletonAtom_eq
    (start scale : ℕ) (profileDelta : ℝ) (y : Point)
    (hscale : 1 ≤ scale) :
    asymmetricSuccessful (skeletonAtom start scale profileDelta y) =
      stoppedSuccessfulPointEvent start scale profileDelta y := by
  exact (stoppedSuccessfulPointEvent_eq_iUnion_supportedSkeletonAtoms
    start scale profileDelta y hscale).symm

/-- Every successful event covered by concrete coarse completion tails is
necessarily contained in the retained left successful event. -/
theorem CoarseCompletionTailRows.successful_subset_left
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} {returnBoundary globalBoundary : Set Point}
    {globalStart : Point} {successful : Set StepPath} {radialTail : ℝ}
    (rows : CoarseCompletionTailRows (start := start) hk profileDelta x y
      returnBoundary globalBoundary globalStart successful radialTail) :
    successful ⊆ stoppedSuccessfulPointEvent start n profileDelta x := by
  intro omega homega
  obtain ⟨r, hr⟩ := Set.mem_iUnion.mp (rows.successful_subset homega)
  obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hr
  exact coarseRetainedAtom_subset_stoppedSuccessfulPointEvent r
    (rows.tail_subset r t ht)

/-- Consequently, using the unrestricted right terminal union as the
successful event in concrete coarse rows forces all right-successful paths
to be left-successful.  The sound pair construction must instead cover a
genuine pair-success (or equivalent left-compatible restricted) event. -/
theorem CoarseCompletionTailRows.unrestricted_right_subset_left
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} {returnBoundary globalBoundary : Set Point}
    {globalStart : Point} {radialTail : ℝ}
    (hn : 1 ≤ n)
    (rows : CoarseCompletionTailRows (start := start) hk profileDelta x y
      returnBoundary globalBoundary globalStart
      (asymmetricSuccessful (skeletonAtom start n profileDelta y))
      radialTail) :
    stoppedSuccessfulPointEvent start n profileDelta y ⊆
      stoppedSuccessfulPointEvent start n profileDelta x := by
  rw [← asymmetricSuccessful_terminalSkeletonAtom_eq
    start n profileDelta y hn]
  exact successful_subset_left rows

end

end Erdos1165.AsymmetricCompletionSuccessfulContainment
