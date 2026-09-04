/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricExtractedReturnCompletion

/-!
# Countable source-independent codes for asymmetric split completion

A retained code records exactly the data invariant under replacement:
the deterministic block prefix, compressed complementary skeleton, and the
finite transition signature of every erased return on all `x` scanners.
It does not record a representative source return word.

Validity is pathwise.  It certifies the common global first exit, inclusion
of the resulting completion event in `Γ_x`, and recovery of the same code
from every assembled cylinder.  The last field makes distinct valid atoms
pairwise disjoint without identifying them with synthetic complement
cylinders.
-/

open MeasureTheory Set

namespace Erdos1165.AsymmetricSplitCompletionCode

open AnnularProfileClocks AsymmetricExtractedReturnCompletion
open AnnularBoundaryExcursionKernel AsymmetricPairTwoStageMass
open AsymmetricSplitCompletionPreservation AsymmetricSplitLevelSplice
open MarkedBridgeFactorization TerminalSkeletonInvariance
open TerminalSkeletonWords ThickPoint TerminalSequentialVisitLaw

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Data which is literally unchanged by a scanner-compatible split
completion. -/
structure SplitCompletionData (start n : ℕ) where
  returnCount : ℕ
  pre : Fin start → Direction
  skeleton : TerminalSkeletonCode returnCount
  /-- The first component preserves every `x` scanner.  The second records
  the `y` scanners, so in particular the split-level completed-return count
  is recoverable after replacement. -/
  signature : Fin returnCount →
    XProfileScanSignatureData n × XProfileScanSignatureData n

noncomputable instance splitCompletionDataCountable (start n : ℕ) :
    Countable (SplitCompletionData start n) := by
  let : Countable (XProfileScanSignatureData n) := inferInstance
  exact (show Function.Injective
      (fun data : SplitCompletionData start n ↦
        (⟨data.returnCount,
          (data.pre, data.skeleton, data.signature)⟩ :
          Σ q : ℕ, (Fin start → Direction) ×
            TerminalSkeletonCode q ×
              (Fin q → XProfileScanSignatureData n ×
                XProfileScanSignatureData n))) by
    intro left right h
    cases left
    cases right
    simp only [Sigma.mk.injEq] at h
    cases h.1
    cases h.2
    rfl).countable

/-- Candidate return codes represented by one source-independent scanner
signature. -/
abbrev SignatureCompatibleReturnCode
    {start n : ℕ} (x y : Point) (returnBoundary : Set Point)
    (data : SplitCompletionData start n) (j : Fin data.returnCount) :=
  {bridge : BoundaryExitWordCode returnBoundary
      (data.skeleton.2.1 j) (data.skeleton.2.2 j) //
    XProfileScanSignature n x (data.skeleton.2.1 j)
        (List.ofFn bridge.1.2) = (data.signature j).1 ∧
      XProfileScanSignature n y (data.skeleton.2.1 j)
        (List.ofFn bridge.1.2) = (data.signature j).2}

/-- Opaque box for one endpoint-matched bridge.  Source constructors use
this declaration boundary to avoid unfolding the complete extracted
skeleton while Lean elaborates their result type. -/
structure BoundaryExitCodeAt
    {q : ℕ} (returnBoundary : Set Point)
    (code : TerminalSkeletonCode q) (j : Fin q) where
  val : BoundaryExitWordCode returnBoundary (code.2.1 j) (code.2.2 j)

/-- Opaque box for one scanner-compatible endpoint-matched bridge. -/
structure SignatureCompatibleReturnCodeAt
    {start n : ℕ} (x y : Point) (returnBoundary : Set Point)
    (data : SplitCompletionData start n) (j : Fin data.returnCount) where
  val : SignatureCompatibleReturnCode x y returnBoundary data j

/-- One literal index of the fixed-prefix, signature-compatible completion
atom.  Naming it keeps source constructors from repeatedly normalizing the
dependent bridge family. -/
structure SplitCompletionAtomIndex
    {start n : ℕ} (x y : Point) (returnBoundary : Set Point)
    (data : SplitCompletionData start n) where
  bridges : (j : Fin data.returnCount) →
    SignatureCompatibleReturnCode x y returnBoundary data j

/-- Opaque wrapper used by source-facing constructors to avoid eagerly
normalizing the full extracted dependent bridge family in their headers. -/
structure SplitCompletionAtomIndexBox
    {start n : ℕ} (x y : Point) (returnBoundary : Set Point)
    (data : SplitCompletionData start n) where
  val : SplitCompletionAtomIndex x y returnBoundary data

def SplitCompletionAtomIndex.toProduct
    {start n : ℕ} {x y : Point} {returnBoundary : Set Point}
    {data : SplitCompletionData start n}
    (index : SplitCompletionAtomIndex x y returnBoundary data) :
    PUnit × ((j : Fin data.returnCount) →
      SignatureCompatibleReturnCode x y returnBoundary data j) :=
  (PUnit.unit, index.bridges)

/-- The finite insertion family determined by one code and one proof that
all unrestricted endpoint-matched returns share the global stopping
boundary.  Its complement is fixed to the recorded deterministic prefix. -/
def splitCompletionAtomOfData
    {start n : ℕ} {x y : Point} (returnBoundary globalBoundary : Set Point)
    (globalStart : Point) (data : SplitCompletionData start n)
    (hfirst : ∀ bridges : (j : Fin data.returnCount) →
        BoundaryExitWordCode returnBoundary
          (data.skeleton.2.1 j) (data.skeleton.2.2 j),
      AbsoluteBoundaryFirstAt globalBoundary globalStart
        (assembledTerminalPath data.skeleton
          (fun j ↦ List.ofFn (bridges j).1.2))
        (assembledTerminalHorizon data.skeleton
          (fun j ↦ List.ofFn (bridges j).1.2))) :
    ComplementarySkeletonAtom data.returnCount Unit
      (fun j ↦ SignatureCompatibleReturnCode x y returnBoundary data j) :=
  fixComplement
    (restrictBridges
      (boundaryReturnCompletionAtom (start := start) data.skeleton
        returnBoundary globalBoundary globalStart hfirst)
      (fun j bridge ↦
        XProfileScanSignature n x (data.skeleton.2.1 j)
            (List.ofFn bridge.1.2) = (data.signature j).1 ∧
          XProfileScanSignature n y (data.skeleton.2.1 j)
            (List.ofFn bridge.1.2) = (data.signature j).2))
    data.pre

/-- A literal assembled cylinder belongs to the restricted completion atom
as soon as each inserted bridge has the recorded pair of scanner
signatures.  Keeping the dependent union normalization here makes
source-facing coverage proofs small. -/
theorem mem_splitCompletionAtomOfData_of_stoppedWordCylinder
    {start n : ℕ} {x y : Point} {returnBoundary globalBoundary : Set Point}
    {globalStart : Point} {data : SplitCompletionData start n}
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
      XProfileScanSignature n x (data.skeleton.2.1 j)
          (List.ofFn (bridges j).1.2) = (data.signature j).1 ∧
        XProfileScanSignature n y (data.skeleton.2.1 j)
          (List.ofFn (bridges j).1.2) = (data.signature j).2)
    {omega : StepPath}
    (homega : omega ∈ stoppedWordCylinder
      (assembleAfterPrefix data.pre data.skeleton
        (fun j ↦ List.ofFn (bridges j).1.2))) :
    omega ∈ (splitCompletionAtomOfData (x := x) (y := y)
      returnBoundary globalBoundary globalStart data hfirst).event := by
  rw [ComplementarySkeletonAtom.event, stoppedWordEvent]
  apply Set.mem_iUnion.mpr
  refine ⟨(Unit.unit, fun j ↦ ⟨bridges j, hcompat j⟩), ?_⟩
  simpa only [splitCompletionAtomOfData, fixComplement, restrictBridges,
    boundaryReturnCompletionAtom] using homega

/-- Membership in a split-completion atom exposes one literal family of
scanner-compatible return codes and its assembled stopped cylinder. -/
theorem exists_signatureCompatibleReturnCodes_of_mem_splitCompletionAtomOfData
    {start n : ℕ} {x y : Point} {returnBoundary globalBoundary : Set Point}
    {globalStart : Point} {data : SplitCompletionData start n}
    (hfirst : ∀ bridges : (j : Fin data.returnCount) →
        BoundaryExitWordCode returnBoundary
          (data.skeleton.2.1 j) (data.skeleton.2.2 j),
      AbsoluteBoundaryFirstAt globalBoundary globalStart
        (assembledTerminalPath data.skeleton
          (fun j ↦ List.ofFn (bridges j).1.2))
        (assembledTerminalHorizon data.skeleton
          (fun j ↦ List.ofFn (bridges j).1.2)))
    {omega : StepPath}
    (homega : omega ∈ (splitCompletionAtomOfData (x := x) (y := y)
      returnBoundary globalBoundary globalStart data hfirst).event) :
    ∃ bridges : (j : Fin data.returnCount) →
        SignatureCompatibleReturnCode x y returnBoundary data j,
      omega ∈ stoppedWordCylinder
        (assembleAfterPrefix data.pre data.skeleton
          (fun j ↦ List.ofFn (bridges j).1.1.2)) := by
  rw [ComplementarySkeletonAtom.event, stoppedWordEvent] at homega
  obtain ⟨index, hindex⟩ := Set.mem_iUnion.mp homega
  exact ⟨index.2, hindex⟩

/-- Fixed-prefix completion restricted by the pair of scanner signatures of
an explicit source word family. -/
def pairedSignatureFixedCompletionAtom
    {start m n : ℕ} (x y : Point) (code : TerminalSkeletonCode m)
    (sourceWords : TerminalSegmentWords m)
    (returnBoundary globalBoundary : Set Point) (globalStart : Point)
    (pre : Fin start → Direction)
    (hfirst : ∀ bridges : (j : Fin m) → BoundaryExitWordCode returnBoundary
        (code.2.1 j) (code.2.2 j),
      AbsoluteBoundaryFirstAt globalBoundary globalStart
        (assembledTerminalPath code (fun j ↦ List.ofFn (bridges j).1.2))
        (assembledTerminalHorizon code
          (fun j ↦ List.ofFn (bridges j).1.2))) :=
  fixComplement
    (restrictBridges
      (boundaryReturnCompletionAtom (start := start) code returnBoundary
        globalBoundary globalStart hfirst)
      (fun j bridge ↦
        XProfileScanSignature n x (code.2.1 j) (List.ofFn bridge.1.2) =
            XProfileScanSignature n x (code.2.1 j) (sourceWords j) ∧
          XProfileScanSignature n y (code.2.1 j) (List.ofFn bridge.1.2) =
            XProfileScanSignature n y (code.2.1 j) (sourceWords j)))
    pre

theorem mem_pairedSignatureFixedCompletionAtom_of_sourceCylinder
    {start m n : ℕ} {x y : Point} {code : TerminalSkeletonCode m}
    {sourceWords : TerminalSegmentWords m}
    {returnBoundary globalBoundary : Set Point} {globalStart : Point}
    {pre : Fin start → Direction}
    (hfirst : ∀ bridges : (j : Fin m) → BoundaryExitWordCode returnBoundary
        (code.2.1 j) (code.2.2 j),
      AbsoluteBoundaryFirstAt globalBoundary globalStart
        (assembledTerminalPath code (fun j ↦ List.ofFn (bridges j).1.2))
        (assembledTerminalHorizon code
          (fun j ↦ List.ofFn (bridges j).1.2)))
    (bridges : (j : Fin m) → BoundaryExitWordCode returnBoundary
      (code.2.1 j) (code.2.2 j))
    (hwords : ∀ j, List.ofFn (bridges j).1.2 = sourceWords j)
    {omega : StepPath}
    (homega : omega ∈ stoppedWordCylinder
      (assembleAfterPrefix pre code sourceWords)) :
    omega ∈ (pairedSignatureFixedCompletionAtom (n := n) x y code sourceWords
      returnBoundary globalBoundary globalStart pre hfirst).event := by
  rw [ComplementarySkeletonAtom.event, stoppedWordEvent]
  apply Set.mem_iUnion.mpr
  refine ⟨(PUnit.unit, fun j ↦ ⟨bridges j, ?_⟩), ?_⟩
  · constructor <;> rw [hwords j]
  · have hfamily : (fun j ↦ List.ofFn (bridges j).1.2) = sourceWords := by
      funext j
      exact hwords j
    change omega ∈ stoppedWordCylinder
      (assembleAfterPrefix pre code (fun j ↦ List.ofFn (bridges j).1.2))
    rw [hfamily]
    exact homega

/-- Deterministic code extracted from a stopped path at one split level.
This definition needs no success hypothesis; those hypotheses are used only
to prove that its code is valid and covers the source. -/
def splitCompletionDataAt
    (start n k : ℕ) (x y : Point) (omega : StepPath) :
    SplitCompletionData start n := by
  let horizon := stoppedOuterExitHorizon start n omega
  let sigma := shiftSteps start omega
  let middle := profileInnerBoundary n k y
  let inner := profileInnerBoundary n (k + 1) y
  let q := boundaryExcursionCount middle inner (0, 0) sigma horizon
  let t := extractTimedReturnSkeleton sigma (0, 0) middle inner horizon q
  exact
    { returnCount := q
      pre := stepPrefix start omega
      skeleton := compressTimedSkeleton sigma t
      signature := fun j ↦
        (XProfileScanSignature n x (t.entrancePoint j)
            (intervalWords sigma t.entrance t.exit j),
          XProfileScanSignature n y (t.entrancePoint j)
            (intervalWords sigma t.entrance t.exit j)) }

/-- Pathwise validity of one source-independent code.  The recovery field is
the global prefix-free cover statement; `gammaX` is discharged from the
atom-level scanner/global-exit theorem, not from a probability premise. -/
structure SplitCompletionWitness
    {start n k : ℕ} {profileDelta : ℝ} (x y : Point)
    (returnBoundary globalBoundary : Set Point) (globalStart : Point)
    (data : SplitCompletionData start n) : Prop where
  globalFirst : ∀ bridges : (j : Fin data.returnCount) →
      BoundaryExitWordCode returnBoundary
        (data.skeleton.2.1 j) (data.skeleton.2.2 j),
    AbsoluteBoundaryFirstAt globalBoundary globalStart
      (assembledTerminalPath data.skeleton
        (fun j ↦ List.ofFn (bridges j).1.2))
      (assembledTerminalHorizon data.skeleton
        (fun j ↦ List.ofFn (bridges j).1.2))
  gammaX :
    (splitCompletionAtomOfData (x := x) (y := y) returnBoundary globalBoundary
      globalStart data globalFirst).event ⊆
      Proposition13Assembly.stoppedSuccessfulPointEvent
        start n profileDelta x
  recovered :
    (splitCompletionAtomOfData (x := x) (y := y) returnBoundary globalBoundary
      globalStart data globalFirst).event ⊆
      {omega | splitCompletionDataAt start n k x y omega = data}

/-- Countable type of all genuinely valid retained completion atoms. -/
abbrev SplitCompletionCode
    (start n k : ℕ) (profileDelta : ℝ) (x y : Point)
    (returnBoundary globalBoundary : Set Point) (globalStart : Point) :=
  {data : SplitCompletionData start n //
    SplitCompletionWitness (k := k) (profileDelta := profileDelta) x y
      returnBoundary globalBoundary globalStart data}

attribute [instance] splitCompletionDataCountable

/-- The genuine retained atom represented by a valid split-completion code. -/
def retainedAtom
    {start n k : ℕ} {profileDelta : ℝ} {x y : Point}
    {returnBoundary globalBoundary : Set Point} {globalStart : Point}
    (code : SplitCompletionCode start n k profileDelta x y
      returnBoundary globalBoundary globalStart) : Set StepPath :=
  (splitCompletionAtomOfData (x := x) (y := y) returnBoundary globalBoundary
    globalStart code.1 code.2.globalFirst).event

theorem measurableSet_retainedAtom
    {start n k : ℕ} {profileDelta : ℝ} {x y : Point}
    {returnBoundary globalBoundary : Set Point} {globalStart : Point}
    (code : SplitCompletionCode start n k profileDelta x y
      returnBoundary globalBoundary globalStart) :
    MeasurableSet (retainedAtom code) :=
  by
    unfold retainedAtom ComplementarySkeletonAtom.event
    exact measurableSet_stoppedWordEvent _

/-- Recovery of the invariant code makes the global retained family
pairwise disjoint. -/
theorem retainedAtom_pairwise
    {start n k : ℕ} {profileDelta : ℝ} {x y : Point}
    {returnBoundary globalBoundary : Set Point} {globalStart : Point} :
    Pairwise fun left right :
        SplitCompletionCode start n k profileDelta x y
          returnBoundary globalBoundary globalStart ↦
      Disjoint (retainedAtom left) (retainedAtom right) := by
  intro left right hne
  rw [Set.disjoint_left]
  intro omega hleft hright
  have hl := left.2.recovered hleft
  have hr := right.2.recovered hright
  apply hne
  apply Subtype.ext
  exact hl.symm.trans hr

/-- Every retained completion atom is pathwise contained in `Γ_x`. -/
theorem retainedAtom_subset_stoppedSuccessfulPointEvent
    {start n k : ℕ} {profileDelta : ℝ} {x y : Point}
    {returnBoundary globalBoundary : Set Point} {globalStart : Point}
    (code : SplitCompletionCode start n k profileDelta x y
      returnBoundary globalBoundary globalStart) :
    retainedAtom code ⊆
      Proposition13Assembly.stoppedSuccessfulPointEvent
        start n profileDelta x :=
  code.2.gammaX

/-- The global retained union is therefore a genuine one-point event. -/
theorem iUnion_retainedAtom_subset_stoppedSuccessfulPointEvent
    {start n k : ℕ} {profileDelta : ℝ} {x y : Point}
    {returnBoundary globalBoundary : Set Point} {globalStart : Point} :
    (⋃ code : SplitCompletionCode start n k profileDelta x y
        returnBoundary globalBoundary globalStart, retainedAtom code) ⊆
      Proposition13Assembly.stoppedSuccessfulPointEvent
        start n profileDelta x := by
  intro omega homega
  obtain ⟨code, hcode⟩ := Set.mem_iUnion.mp homega
  exact code.2.gammaX hcode

end

end Erdos1165.AsymmetricSplitCompletionCode
