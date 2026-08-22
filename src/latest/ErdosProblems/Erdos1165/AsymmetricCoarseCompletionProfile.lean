/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricCoarseSplitCompletionSource

/-!
# Profile preservation for coarse completion codes

This file keeps the profile argument independent of the walk extractor.
Once endpoint geometry for two return tuples over the same coarse skeleton
is supplied, equality of their retained prefix signatures and strict
post-separation geometry preserve the complete left profile.
-/

namespace Erdos1165.AsymmetricCoarseCompletionProfile

open AnnularProfileClocks AppendixPair
open AsymmetricCoarseScanSignature AsymmetricCoarseSplitCompletion
open AsymmetricCoarseSplitCompletionSource
open AsymmetricSplitCompletionSource
open AsymmetricSplitCompletionPreservation
open Proposition13Assembly TerminalProfileClockEquivalence
open TerminalGlobalExitSplice
open TerminalSkeletonInvariance TerminalSkeletonWords ThickPoint

noncomputable section

/-- Two coarse-compatible return tuples over one skeleton produce the same
complete left profile, provided the retained pieces connect their common
endpoints. -/
theorem assembledTerminalPath_profile_eq_of_coarseReturnCodes_of_separation_le
    {start n k : ℕ} {x y : Point}
    (hn : 2 ≤ n)
    (hseparation : separationLevel n x y ≤ k)
    (hlevel : k ≤ n)
    (data : CoarseSplitCompletionData start n k)
    (hstarts : ∀ j : Fin data.returnCount,
      data.skeleton.2.1 j ∈ disc y (scaleRadius n k))
    (left right : (j : Fin data.returnCount) →
      CoarseSignatureReturnCode x y (profileInnerBoundary n k y) data j)
    (geometry : EndpointMatchedAlternatingGeometry data.returnCount (0, 0)
      data.skeleton.1.retainedPiece
      (fun j ↦ List.ofFn (left j).1.1.2)
      (fun j ↦ List.ofFn (right j).1.1.2))
    (hwordStart : ∀ j, geometry.wordStart j = data.skeleton.2.1 j) :
    excursionProfile
        (trajectory (assembledTerminalPath data.skeleton
          (fun j ↦ List.ofFn (left j).1.1.2))) n
        (assembledTerminalHorizon data.skeleton
          (fun j ↦ List.ofFn (left j).1.1.2)) x =
      excursionProfile
        (trajectory (assembledTerminalPath data.skeleton
          (fun j ↦ List.ofFn (right j).1.1.2))) n
        (assembledTerminalHorizon data.skeleton
          (fun j ↦ List.ofFn (right j).1.1.2)) x := by
  let leftWords : TerminalSegmentWords data.returnCount :=
    fun j ↦ List.ofFn (left j).1.1.2
  let rightWords : TerminalSegmentWords data.returnCount :=
    fun j ↦ List.ofFn (right j).1.1.2
  have hword :=
    excursionProfile_alternatingConcat_eq_of_xProfileScanCompatible
      hn geometry (fun j ↦ by
        rw [hwordStart j]
        exact xProfileScanCompatible_of_coarseReturnCodes_of_separation_le
          (hseparation.trans hlevel) hseparation hlevel j (hstarts j)
          (left j) (right j))
  have hword' :
      excursionProfile
          (wordWalk (0, 0)
            (reconstructTerminalPacket (data.skeleton, leftWords))) n
          (assembledTerminalHorizon data.skeleton leftWords) x =
        excursionProfile
          (wordWalk (0, 0)
            (reconstructTerminalPacket (data.skeleton, rightWords))) n
          (assembledTerminalHorizon data.skeleton rightWords) x := by
    simpa only [leftWords, rightWords, reconstructTerminalPacket,
      assembledTerminalHorizon_eq_alternatingConcat_length] using hword
  exact (assembledTerminalPath_excursionProfile_eq_wordWalk
    (n := n) (z := x) data.skeleton leftWords).trans
      (hword'.trans
      (assembledTerminalPath_excursionProfile_eq_wordWalk
        (n := n) (z := x) data.skeleton rightWords).symm)

/-- Equality-level wrapper for the original geometric split. -/
theorem assembledTerminalPath_profile_eq_of_coarseReturnCodes
    {start n k : ℕ} {x y : Point}
    (hn : 2 ≤ n)
    (hseparation : k = separationLevel n x y)
    (hlevel : k ≤ n)
    (data : CoarseSplitCompletionData start n k)
    (hstarts : ∀ j : Fin data.returnCount,
      data.skeleton.2.1 j ∈ disc y (scaleRadius n k))
    (left right : (j : Fin data.returnCount) →
      CoarseSignatureReturnCode x y (profileInnerBoundary n k y) data j)
    (geometry : EndpointMatchedAlternatingGeometry data.returnCount (0, 0)
      data.skeleton.1.retainedPiece
      (fun j ↦ List.ofFn (left j).1.1.2)
      (fun j ↦ List.ofFn (right j).1.1.2))
    (hwordStart : ∀ j, geometry.wordStart j = data.skeleton.2.1 j) :
    excursionProfile
        (trajectory (assembledTerminalPath data.skeleton
          (fun j ↦ List.ofFn (left j).1.1.2))) n
        (assembledTerminalHorizon data.skeleton
          (fun j ↦ List.ofFn (left j).1.1.2)) x =
      excursionProfile
        (trajectory (assembledTerminalPath data.skeleton
          (fun j ↦ List.ofFn (right j).1.1.2))) n
        (assembledTerminalHorizon data.skeleton
          (fun j ↦ List.ofFn (right j).1.1.2)) x := by
  apply assembledTerminalPath_profile_eq_of_coarseReturnCodes_of_separation_le
    hn (by omega) hlevel data hstarts left right geometry hwordStart

end

end Erdos1165.AsymmetricCoarseCompletionProfile
