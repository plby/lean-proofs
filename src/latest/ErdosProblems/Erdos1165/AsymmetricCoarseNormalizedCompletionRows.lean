/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricCoarseCompletionCode
import ErdosProblems.Erdos1165.AsymmetricNormalizedRadialCompletionFamily

/-!
# Normalized tails over the concrete coarse asymmetric completion

This adapter freezes the pathwise half of the lower pair construction.  The
retained codes and atoms are exactly the source-independent coarse split
completion codes.  Consequently measurability, pairwise disjointness, source
coverage and containment in the left successful event are inherited from the
coarse extractor.

The only remaining input is the genuinely deeper right-hand refinement: its
atoms must lie inside their coarse atom, cover the successful right event,
and satisfy the aggregate conditional mass upper.  Normalization then gives
the exact tail-mass factorization required by the final constructor.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.AsymmetricCoarseNormalizedCompletionRows

open AnnularProfileClocks AsymmetricCoarseCompletionCode
open AsymmetricCompatibleRadialCompletionFamily
open AsymmetricNormalizedRadialCompletionFamily
open AppendixPair BufferedStoppedSuccessfulPointEvent
open Proposition13Assembly ThickPoint

noncomputable section

/-- The genuine union of coarse retained completion atoms. -/
def coarseRetainedEvent
    {start n k : ℕ} (hk : k + 1 ≤ n) (profileDelta : ℝ)
    (x y : Point) (returnBoundary globalBoundary : Set Point)
    (globalStart : Point) : Set StepPath :=
  ⋃ code : SuccessfullyRootedCoarseSplitCompletionCode
      start n k hk profileDelta x y
      returnBoundary globalBoundary globalStart,
    coarseRetainedAtom code.1

/-- A genuinely deeper right-hand tail over every concrete coarse atom.
No mass identity with a stopped cylinder is part of this interface. -/
structure CoarseCompletionTailRows
    {start n k : ℕ} (hk : k + 1 ≤ n) (profileDelta : ℝ)
    (x y : Point) (returnBoundary globalBoundary : Set Point)
    (globalStart : Point) (successful : Set StepPath)
    (radialTail : ℝ) : Type 2 where
  TailCode : SuccessfullyRootedCoarseSplitCompletionCode
      start n k hk profileDelta x y
      returnBoundary globalBoundary globalStart → Type
  tailCode_countable : ∀ r, Countable (TailCode r)
  tailAtom : ∀ r, TailCode r → Set StepPath
  successful_subset : successful ⊆ ⋃ r, ⋃ t, tailAtom r t
  tail_subset : ∀ r t, tailAtom r t ⊆ coarseRetainedAtom r.1
  tail_sum_le : ∀ r,
    ∑' t, fairSteps (tailAtom r t) ≤
      ENNReal.ofReal radialTail * fairSteps (coarseRetainedAtom r.1)

attribute [instance] CoarseCompletionTailRows.tailCode_countable

/-- The concrete coarse pathwise facts turn a deeper-tail estimate into the
generic normalized rows. -/
def CoarseCompletionTailRows.toNormalizedCompletionRows
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} {returnBoundary globalBoundary : Set Point}
    {globalStart : Point} {successful : Set StepPath} {radialTail : ℝ}
    (rows : CoarseCompletionTailRows (start := start) hk profileDelta x y
      returnBoundary globalBoundary globalStart successful radialTail)
    (gammaX : Set StepPath)
    (hretainedSubset :
      coarseRetainedEvent (start := start) hk profileDelta x y returnBoundary
        globalBoundary globalStart ⊆ gammaX) :
    NormalizedCompletionRows successful
      (coarseRetainedEvent (start := start) hk profileDelta x y returnBoundary
        globalBoundary globalStart)
      gammaX radialTail where
  RetainedCode := SuccessfullyRootedCoarseSplitCompletionCode
    start n k hk profileDelta x y
    returnBoundary globalBoundary globalStart
  retainedCode_countable := inferInstance
  TailCode := rows.TailCode
  tailCode_countable := rows.tailCode_countable
  retainedAtom := fun r ↦ coarseRetainedAtom r.1
  tailAtom := rows.tailAtom
  successful_subset := rows.successful_subset
  retained_eq := rfl
  retained_measurable := fun r ↦ measurableSet_coarseRetainedAtom r.1
  retained_pairwise := successfullyRooted_coarseRetainedAtom_pairwise
  tail_subset := rows.tail_subset
  tail_sum_le := rows.tail_sum_le
  retained_subset := hretainedSubset

/-- Final completion family over the concrete coarse retained event. -/
def CoarseCompletionTailRows.toCompatibleRadialCompletionFamily
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} {returnBoundary globalBoundary : Set Point}
    {globalStart : Point} {successful : Set StepPath} {radialTail : ℝ}
    (rows : CoarseCompletionTailRows (start := start) hk profileDelta x y
      returnBoundary globalBoundary globalStart successful radialTail)
    (gammaX : Set StepPath)
    (hretainedSubset :
      coarseRetainedEvent (start := start) hk profileDelta x y returnBoundary
        globalBoundary globalStart ⊆ gammaX) :
    CompatibleRadialCompletionFamily successful
      (coarseRetainedEvent (start := start) hk profileDelta x y returnBoundary
        globalBoundary globalStart)
      gammaX radialTail :=
  (rows.toNormalizedCompletionRows gammaX
    hretainedSubset).toCompatibleRadialCompletionFamily

end

end Erdos1165.AsymmetricCoarseNormalizedCompletionRows
