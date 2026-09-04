/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricCoarseScanSignature
import ErdosProblems.Erdos1165.AsymmetricSplitCompletionWitness

/-!
# Coarse asymmetric split-completion atoms

The fine source code records both complete profiles of every erased return.
For the retained denominator this is too much: it already contains the
right-hand radial tail.  The coarse code below keeps only the left scanner
signature through separation and the single right split-clock transition.
The remaining right coordinates are available for the fine tail code.
-/

open MeasureTheory Set

namespace Erdos1165.AsymmetricCoarseSplitCompletion

open AnnularBoundaryExcursionKernel AnnularProfileClocks
open AsymmetricCoarseScanSignature AsymmetricExtractedReturnCompletion
open AsymmetricPairTwoStageMass
open AsymmetricSplitCompletionCode AsymmetricSplitCompletionPreservation
open AsymmetricSplitLevelSplice MarkedBridgeFactorization
open TerminalGlobalExitSplice TerminalSkeletonInvariance
open TerminalSequentialVisitLaw TerminalSkeletonWords ThickPoint

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Source-independent data retained before exposing the deeper `y` tail. -/
structure CoarseSplitCompletionData (start n splitLevel : ℕ) where
  returnCount : ℕ
  pre : Fin start → Direction
  skeleton : TerminalSkeletonCode returnCount
  signature : Fin returnCount →
    PrefixXProfileScanSignatureData n splitLevel × SingleScanSignatureData

noncomputable instance coarseSplitCompletionDataCountable
    (start n splitLevel : ℕ) :
    Countable (CoarseSplitCompletionData start n splitLevel) := by
  let : Countable (PrefixXProfileScanSignatureData n splitLevel) :=
    inferInstance
  let : Countable SingleScanSignatureData := inferInstance
  exact (show Function.Injective
      (fun data : CoarseSplitCompletionData start n splitLevel ↦
        (⟨data.returnCount,
          (data.pre, data.skeleton, data.signature)⟩ :
          Σ q : ℕ, (Fin start → Direction) × TerminalSkeletonCode q ×
            (Fin q → PrefixXProfileScanSignatureData n splitLevel ×
              SingleScanSignatureData))) by
    intro left right h
    cases left
    cases right
    simp only [Sigma.mk.injEq] at h
    cases h.1
    cases h.2
    rfl).countable

/-- Endpoint-matched return codes with precisely the retained coarse
signature. -/
abbrev CoarseSignatureReturnCode
    {start n splitLevel : ℕ} (x y : Point) (returnBoundary : Set Point)
    (data : CoarseSplitCompletionData start n splitLevel)
    (j : Fin data.returnCount) :=
  {bridge : BoundaryExitWordCode returnBoundary
      (data.skeleton.2.1 j) (data.skeleton.2.2 j) //
    PrefixXProfileScanSignature n splitLevel x (data.skeleton.2.1 j)
        (List.ofFn bridge.1.2) = (data.signature j).1 ∧
      SingleScanSignature
        (profileOuterBoundary n (splitLevel + 1) y)
        (profileInnerBoundary n (splitLevel + 1) y)
        (data.skeleton.2.1 j) (List.ofFn bridge.1.2) =
          (data.signature j).2}

/-- Fixed-prefix completion restricted only by the coarse signature. -/
def coarseSplitCompletionAtomOfData
    {start n splitLevel : ℕ} {x y : Point}
    (returnBoundary globalBoundary : Set Point) (globalStart : Point)
    (data : CoarseSplitCompletionData start n splitLevel)
    (hfirst : ∀ bridges : (j : Fin data.returnCount) →
        BoundaryExitWordCode returnBoundary
          (data.skeleton.2.1 j) (data.skeleton.2.2 j),
      AbsoluteBoundaryFirstAt globalBoundary globalStart
        (assembledTerminalPath data.skeleton
          (fun j ↦ List.ofFn (bridges j).1.2))
        (assembledTerminalHorizon data.skeleton
          (fun j ↦ List.ofFn (bridges j).1.2))) :
    ComplementarySkeletonAtom data.returnCount Unit
      (fun j ↦ CoarseSignatureReturnCode x y returnBoundary data j) :=
  fixComplement
    (restrictBridges
      (boundaryReturnCompletionAtom (start := start) data.skeleton
        returnBoundary globalBoundary globalStart hfirst)
      (fun j bridge ↦
        PrefixXProfileScanSignature n splitLevel x
            (data.skeleton.2.1 j) (List.ofFn bridge.1.2) =
              (data.signature j).1 ∧
          SingleScanSignature
            (profileOuterBoundary n (splitLevel + 1) y)
            (profileInnerBoundary n (splitLevel + 1) y)
            (data.skeleton.2.1 j) (List.ofFn bridge.1.2) =
              (data.signature j).2))
    data.pre

/-- A stopped cylinder with the recorded coarse signatures belongs to its
coarse completion atom. -/
theorem mem_coarseSplitCompletionAtomOfData_of_stoppedWordCylinder
    {start n splitLevel : ℕ} {x y : Point}
    {returnBoundary globalBoundary : Set Point} {globalStart : Point}
    {data : CoarseSplitCompletionData start n splitLevel}
    (hfirst : ∀ bridges : (j : Fin data.returnCount) →
        BoundaryExitWordCode returnBoundary
          (data.skeleton.2.1 j) (data.skeleton.2.2 j),
      AbsoluteBoundaryFirstAt globalBoundary globalStart
        (assembledTerminalPath data.skeleton
          (fun j ↦ List.ofFn (bridges j).1.2))
        (assembledTerminalHorizon data.skeleton
          (fun j ↦ List.ofFn (bridges j).1.2)))
    (bridges : (j : Fin data.returnCount) →
      BoundaryExitWordCode returnBoundary
        (data.skeleton.2.1 j) (data.skeleton.2.2 j))
    (hcompat : ∀ j,
      PrefixXProfileScanSignature n splitLevel x (data.skeleton.2.1 j)
          (List.ofFn (bridges j).1.2) = (data.signature j).1 ∧
        SingleScanSignature
          (profileOuterBoundary n (splitLevel + 1) y)
          (profileInnerBoundary n (splitLevel + 1) y)
          (data.skeleton.2.1 j) (List.ofFn (bridges j).1.2) =
            (data.signature j).2)
    {omega : StepPath}
    (homega : omega ∈ stoppedWordCylinder
      (assembleAfterPrefix data.pre data.skeleton
        (fun j ↦ List.ofFn (bridges j).1.2))) :
    omega ∈ (coarseSplitCompletionAtomOfData (x := x) (y := y)
      returnBoundary globalBoundary globalStart data hfirst).event := by
  rw [ComplementarySkeletonAtom.event, stoppedWordEvent]
  apply Set.mem_iUnion.mpr
  refine ⟨(Unit.unit, fun j ↦ ⟨bridges j, hcompat j⟩), ?_⟩
  simpa only [coarseSplitCompletionAtomOfData, fixComplement, restrictBridges,
    boundaryReturnCompletionAtom] using homega

/-- Membership in a coarse atom exposes the literal endpoint-matched return
tuple and its assembled stopped cylinder. -/
theorem exists_coarseSignatureReturnCodes_of_mem
    {start n splitLevel : ℕ} {x y : Point}
    {returnBoundary globalBoundary : Set Point} {globalStart : Point}
    {data : CoarseSplitCompletionData start n splitLevel}
    (hfirst : ∀ bridges : (j : Fin data.returnCount) →
        BoundaryExitWordCode returnBoundary
          (data.skeleton.2.1 j) (data.skeleton.2.2 j),
      AbsoluteBoundaryFirstAt globalBoundary globalStart
        (assembledTerminalPath data.skeleton
          (fun j ↦ List.ofFn (bridges j).1.2))
        (assembledTerminalHorizon data.skeleton
          (fun j ↦ List.ofFn (bridges j).1.2)))
    {omega : StepPath}
    (homega : omega ∈ (coarseSplitCompletionAtomOfData (x := x) (y := y)
      returnBoundary globalBoundary globalStart data hfirst).event) :
    ∃ bridges : (j : Fin data.returnCount) →
        CoarseSignatureReturnCode x y returnBoundary data j,
      omega ∈ stoppedWordCylinder
        (assembleAfterPrefix data.pre data.skeleton
          (fun j ↦ List.ofFn (bridges j).1.1.2)) := by
  rw [ComplementarySkeletonAtom.event, stoppedWordEvent] at homega
  obtain ⟨index, hindex⟩ := Set.mem_iUnion.mp homega
  exact ⟨index.2, hindex⟩

/-- Forget all fine right-hand coordinates except the split scanner, and
forget the automatic strictly post-separation left coordinates. -/
def coarsenSplitCompletionData
    {start n splitLevel : ℕ} (hsplit : splitLevel + 1 ≤ n)
    (data : SplitCompletionData start n) :
    CoarseSplitCompletionData start n splitLevel := by
  let splitIndex : {k : Fin (n + 2) // (k : ℕ) ≠ 0} :=
    ⟨⟨splitLevel + 1,
        Nat.lt_of_le_of_lt hsplit (by omega : n < n + 2)⟩,
      Nat.succ_ne_zero splitLevel⟩
  exact
    { returnCount := data.returnCount
      pre := data.pre
      skeleton := data.skeleton
      signature := fun j ↦
        (fun _ _ ↦ ((0, 0), TerminalBoundaryScan.initialState),
          fun _ ↦ ((0, 0), TerminalBoundaryScan.initialState)) }

/-- Coarse data extracted from an actual stopped path. -/
noncomputable def sourceCoarseSplitCompletionData
    (start n splitLevel : ℕ) (hsplit : splitLevel + 1 ≤ n)
    (x y : Point) (omega : StepPath) :
    CoarseSplitCompletionData start n splitLevel :=
  coarsenSplitCompletionData hsplit
    (splitCompletionDataAt start n splitLevel x y omega)

/-- The original fine pair-signature atom is nested inside its coarse
retained completion atom. -/
theorem splitCompletionAtomOfData_subset_coarse
    {start n splitLevel : ℕ} {x y : Point}
    (hsplit : splitLevel + 1 ≤ n)
    {returnBoundary globalBoundary : Set Point} {globalStart : Point}
    (data : SplitCompletionData start n)
    (hfirst : ∀ bridges : (j : Fin data.returnCount) →
        BoundaryExitWordCode returnBoundary
          (data.skeleton.2.1 j) (data.skeleton.2.2 j),
      AbsoluteBoundaryFirstAt globalBoundary globalStart
        (assembledTerminalPath data.skeleton
          (fun j ↦ List.ofFn (bridges j).1.2))
        (assembledTerminalHorizon data.skeleton
          (fun j ↦ List.ofFn (bridges j).1.2))) :
    (splitCompletionAtomOfData (x := x) (y := y)
        returnBoundary globalBoundary globalStart data hfirst).event ⊆
      (coarseSplitCompletionAtomOfData (x := x) (y := y)
        returnBoundary globalBoundary globalStart
        (coarsenSplitCompletionData hsplit data) hfirst).event := by
  intro omega homega
  obtain ⟨bridges, hcylinder⟩ :=
    exists_signatureCompatibleReturnCodes_of_mem_splitCompletionAtomOfData
      hfirst homega
  apply mem_coarseSplitCompletionAtomOfData_of_stoppedWordCylinder
    hfirst (fun j ↦ (bridges j).1)
  · intro j
    constructor
    · rfl
    · rfl
  · exact hcylinder

end

end Erdos1165.AsymmetricCoarseSplitCompletion
