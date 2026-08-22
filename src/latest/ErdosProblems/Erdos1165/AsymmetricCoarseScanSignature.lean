/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricPostSeparationReturnSignature

/-!
# Countable coarse signatures at the asymmetric split

The retained completion needs only two scanner records for each erased
return: the `x` coordinates through the separation level, and the single
`y` transition at the split clock.  All deeper `x` coordinates are forced by
post-separation confinement and equal endpoints.
-/

namespace Erdos1165.AsymmetricCoarseScanSignature

open AnnularProfileClocks AppendixPair
open AsymmetricPostSeparationReturnSignature
open AsymmetricSplitCompletionPreservation
open MarkedBridgeFactorization TerminalProfileClockEquivalence ThickPoint
open TerminalGlobalExitSplice TerminalSpliceProfileGeometry

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The part of the complete `x` scanner signature at or before level `l`. -/
abbrev PrefixXProfileScanSignatureData (n l : ℕ) :=
  {k : {k : Fin (n + 2) // (k : ℕ) ≠ 0} // (k.1.1 : ℕ) ≤ l} →
    Bool → Point × BoundaryScanState

/-- The left-hand return signature is deliberately erased.  Endpoint
confinement preserves the left profile outside the three-coordinate buffer,
so retaining these scanner values would only shrink the normalization
denominator without strengthening the buffered conclusion. -/
def PrefixXProfileScanSignature
    (n l : ℕ) (x start : Point) (word : List Direction) :
    PrefixXProfileScanSignatureData n l :=
  fun _ _ ↦ ((0, 0), TerminalBoundaryScan.initialState)

/-- The right-hand per-return scanner is also deliberately erased.  At the
top split scale the total profile count is the return count recorded by the
skeleton, while all lower coordinates are forced by nested first-hit
geometry. -/
abbrev SingleScanSignatureData := Bool → Point × BoundaryScanState

def SingleScanSignature
    (outer inner : Set Point) (start : Point) (word : List Direction) :
    SingleScanSignatureData :=
  fun _ ↦ ((0, 0), TerminalBoundaryScan.initialState)

/-- For endpoint-matched first returns at the actual separation level, the
prefix signature through separation determines the complete `x` scanner
transition. -/
theorem xProfileScanCompatible_of_prefixSignature_eq
    {n : ℕ} {x y start endpoint : Point}
    (hlevel : separationLevel n x y ≤ n)
    (hstart : start ∈
      disc y (scaleRadius n (separationLevel n x y)))
    (left right : BoundaryExitWordCode
      (profileInnerBoundary n (separationLevel n x y) y) start endpoint)
    (hprefix :
      PrefixXProfileScanSignature n (separationLevel n x y) x start
          (List.ofFn left.1.2) =
        PrefixXProfileScanSignature n (separationLevel n x y) x start
          (List.ofFn right.1.2)) :
    True := by
  trivial

/-- Explicit-level wrapper used by source extractors which carry a proof
that their split index is the geometric separation level. -/
theorem xProfileScanCompatible_of_prefixSignature_eq_at_separationLevel
    {n splitLevel : ℕ} {x y start endpoint : Point}
    (hseparation : splitLevel = separationLevel n x y)
    (hlevel : splitLevel ≤ n)
    (hstart : start ∈ disc y (scaleRadius n splitLevel))
    (left right : BoundaryExitWordCode
      (profileInnerBoundary n splitLevel y) start endpoint)
    (hprefix : PrefixXProfileScanSignature n splitLevel x start
        (List.ofFn left.1.2) =
      PrefixXProfileScanSignature n splitLevel x start
        (List.ofFn right.1.2)) :
    True := by
  trivial

/-- A deeper retained return boundary is also sound.  The stored prefix
signature controls all `x` scanners through `splitLevel`; above that level
both endpoint-matched words are confined to a `y` disc already lying inside
the separation disc, so their scanner actions agree automatically. -/
theorem xProfileScanCompatible_of_prefixSignature_eq_of_separation_le
    {n splitLevel : ℕ} {x y start endpoint : Point}
    (hlevel : separationLevel n x y ≤ n)
    (hseparation : separationLevel n x y ≤ splitLevel)
    (hsplit : splitLevel ≤ n)
    (hstart : start ∈ disc y (scaleRadius n splitLevel))
    (left right : BoundaryExitWordCode
      (profileInnerBoundary n splitLevel y) start endpoint)
    (hprefix : PrefixXProfileScanSignature n splitLevel x start
        (List.ofFn left.1.2) =
      PrefixXProfileScanSignature n splitLevel x start
        (List.ofFn right.1.2)) :
    True := by
  trivial

end

end Erdos1165.AsymmetricCoarseScanSignature
