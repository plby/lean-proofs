/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularLiteralNestedProfileTailUpper
import ErdosProblems.Erdos1165.AsymmetricCompatibleFullProfileRows

/-!
# From literal nested kernels to asymmetric compatible rows

`AsymmetricSplitLevelSplice` already supplies the scanner restriction and
the comparison of a restricted bridge row with its unrestricted row.  The
only analytic identification still needed from a source extractor is that
the latter row is a summand of the literal nested profile kernel.  This file
packages precisely that identification and derives the
`FullProfileCompatibleRows.unrestricted_row` field from the checked A.6 tail
upper bound.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.AsymmetricNestedKernelCompatibleRows

open AppendixFirstMoment AppendixPair AppendixPairCrossingTail
open AppendixPairMoment AnnularLiteralNestedProfileTailUpper
open AnnularNestedProfileKernel
open AnnularProfileNestedEdge AsymmetricActualFarPairData
open AsymmetricCompatibleFullProfileRows AsymmetricSplitLevelSplice
open MarkedBridgeFactorization ProfileGapChain ProfileListExponent
open ProfileSmallBall ProfileWeightUpper Proposition13Scales

noncomputable section

/-- The eventual nested-profile estimate specialized at one scale. -/
def LiteralNestedProfileTailUpperAt (scale : ℕ) : Prop :=
  ∀ (center : Point) (profileDelta : ℝ) (m : Profile scale),
    IsConstrainedProfile profileDelta m → profileDelta ≤ 1 →
    ∀ (start : ℕ), 2 ≤ start → start ≤ scale →
    ∀ (a : ℕ) (rest : List ℕ),
      profileSegmentValues m start = a :: rest →
    ∀ entrance : BoundaryVector (ProfileNestedState scale center)
        (start - 2) a,
      (∑ chain : GapChain (a :: rest),
        nestedGapChainKernelENNReal
          (literalProfileNestedEdgeKernelENNReal scale center)
          (start - 2) a rest entrance chain).toReal ≤
        Real.exp 1 * transitionSegmentProduct
          start (scale - start) (profileAtScale m)

theorem eventually_literalNestedProfileTailUpperAt :
    ∀ᶠ scale : ℕ in Filter.atTop,
      LiteralNestedProfileTailUpperAt scale := by
  simpa only [LiteralNestedProfileTailUpperAt] using
    eventually_literalNestedProfileTailSum_toReal_le

/-- Source-facing rows before the final A.6 estimate.  All pathwise fields
are exactly those of `FullProfileCompatibleRows`; `unrestricted_row` is
replaced by the literal statement that the row is dominated by one nested
profile-kernel sum. -/
structure NestedKernelCompatibleRows
    {delta : ℝ} {n : ℕ} {x y : Point}
    (successful retained : Set StepPath)
    (certificate : ProfileRadialTailCertificate delta n x y) : Type 2 where
  RetainedCode : Type
  retainedCode_countable : Countable RetainedCode
  coordinateCount : RetainedCode → ℕ
  Bridge : (r : RetainedCode) → Fin (coordinateCount r) → Type
  bridge_countable : ∀ r j, Countable (Bridge r j)
  atom : (r : RetainedCode) → ComplementarySkeletonAtom
    (coordinateCount r) Unit (Bridge r)
  admissible : (r : RetainedCode) → (j : Fin (coordinateCount r)) →
    Bridge r j → Prop
  profile : RetainedCode → Profile (scaleIndex delta n)
  profile_mem : ∀ r,
    profile r ∈ constrainedProfiles (scaleIndex delta n) profileUpperDelta
  successful_subset : successful ⊆ ⋃ r,
    (restrictBridges (atom r) (admissible r)).event
  retained_eq : retained = ⋃ r,
    stoppedWordCylinder ((atom r).complementWord Unit.unit)
  retained_prefixFree : PrefixFree fun r ↦
    (atom r).complementWord Unit.unit
  unrestricted_ne_top : ∀ r, (∏ j, (atom r).kernel j) ≠ ∞
  segmentHead : RetainedCode → ℕ
  segmentTail : RetainedCode → List ℕ
  segment_eq : ∀ r,
    profileSegmentValues (profile r)
        (pairPrefixScale (scaleIndex delta n)
          (separationLevel (scaleIndex delta n) x y)) =
      segmentHead r :: segmentTail r
  entrance : ∀ r,
    BoundaryVector
      (ProfileNestedState (scaleIndex delta n) y)
      (pairPrefixScale (scaleIndex delta n)
        (separationLevel (scaleIndex delta n) x y) - 2)
      (segmentHead r)
  unrestricted_le_nested : ∀ r,
    (∏ j, (atom r).kernel j).toReal ≤
      (∑ chain : GapChain (segmentHead r :: segmentTail r),
        nestedGapChainKernelENNReal
          (literalProfileNestedEdgeKernelENNReal (scaleIndex delta n) y)
          (pairPrefixScale (scaleIndex delta n)
            (separationLevel (scaleIndex delta n) x y) - 2)
          (segmentHead r) (segmentTail r) (entrance r) chain).toReal
  coefficient_eq : certificate.coefficient = Real.exp 1

attribute [instance] NestedKernelCompatibleRows.retainedCode_countable
attribute [instance] NestedKernelCompatibleRows.bridge_countable

/-- Apply the eventual literal nested-kernel estimate; scanner restriction
is subsequently performed by `FullProfileCompatibleRows.toCompatibleRadialFamily`.
-/
def NestedKernelCompatibleRows.toFullProfileCompatibleRows
    {delta : ℝ} {n : ℕ} {x y : Point}
    {successful retained : Set StepPath}
    {certificate : ProfileRadialTailCertificate delta n x y}
    (rows : NestedKernelCompatibleRows successful retained certificate)
    (hupper : LiteralNestedProfileTailUpperAt (scaleIndex delta n)) :
    FullProfileCompatibleRows successful retained certificate where
  RetainedCode := rows.RetainedCode
  retainedCode_countable := rows.retainedCode_countable
  coordinateCount := rows.coordinateCount
  Bridge := rows.Bridge
  bridge_countable := rows.bridge_countable
  atom := rows.atom
  admissible := rows.admissible
  profile := rows.profile
  profile_mem := rows.profile_mem
  successful_subset := rows.successful_subset
  retained_eq := rows.retained_eq
  retained_prefixFree := rows.retained_prefixFree
  unrestricted_ne_top := rows.unrestricted_ne_top
  unrestricted_row := by
    intro r
    let start := pairPrefixScale (scaleIndex delta n)
      (separationLevel (scaleIndex delta n) x y)
    have hstart : 2 ≤ start :=
      ((show 2 ≤ profileUpperTailStart by
        norm_num [profileUpperTailStart]).trans certificate.tailStart)
    have hm : IsConstrainedProfile profileUpperDelta (rows.profile r) :=
      mem_constrainedProfiles.mp (rows.profile_mem r)
    have hdelta : profileUpperDelta ≤ 1 := by
      norm_num [profileUpperDelta]
    have hkernel := hupper y profileUpperDelta (rows.profile r)
      hm hdelta start hstart certificate.start_le_scale
      (rows.segmentHead r) (rows.segmentTail r) (rows.segment_eq r)
      (rows.entrance r)
    calc
      (∏ j, (rows.atom r).kernel j).toReal ≤
          (∑ chain : GapChain (rows.segmentHead r :: rows.segmentTail r),
            nestedGapChainKernelENNReal
              (literalProfileNestedEdgeKernelENNReal (scaleIndex delta n) y)
              (start - 2) (rows.segmentHead r) (rows.segmentTail r)
              (rows.entrance r) chain).toReal := rows.unrestricted_le_nested r
      _ ≤ Real.exp 1 * transitionSegmentProduct
          start (scaleIndex delta n - start)
            (profileAtScale (rows.profile r)) := hkernel
      _ = certificate.coefficient * transitionSegmentProduct
          start (scaleIndex delta n - start)
            (profileAtScale (rows.profile r)) := by rw [rows.coefficient_eq]

end

end Erdos1165.AsymmetricNestedKernelCompatibleRows
