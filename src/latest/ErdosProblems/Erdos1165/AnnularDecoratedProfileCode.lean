/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularDecoratedRenewalCode
import ErdosProblems.Erdos1165.AnnularDecoratedProfileRow

/-!
# Literal chronological codes for one decorated profile gap

The retained pieces of a profile gap are canonical first-hit words at the
union of the next inner boundary and the current outer boundary.  Between
successive retained inward pieces we insert exactly one recursively refined
child return.  This file specializes the generic decorated-renewal code and
identifies its total literal stopped-word mass with
`profileDecoratedGapKernelENNReal`.
-/

open scoped ENNReal

namespace Erdos1165.AnnularDecoratedProfileCode

open AnnularDecoratedProfileRow AnnularDecoratedRenewalCode
open AnnularOffspringKernelRadial AnnularProfileClocks
open MarkedBoundaryVisitKernel MarkedBridgeFactorization ThickPoint

noncomputable section

private theorem tsum_stoppedWordMass_boundaryExitWordCode
    (boundary : Set Point) (start endpoint : Point) :
    (∑' code : BoundaryExitWordCode boundary start endpoint,
        stoppedWordMass code.1) =
      skeletonExitKernel boundary start endpoint := by
  rw [skeletonExitKernel_eq_canonical]
  symm
  exact (boundaryExitStoppedEventCode boundary start endpoint).mass_eq

/-- Canonical retained middle-to-inner word of one profile cycle. -/
abbrev ProfileInwardWordCode
    (n k : ℕ) (center : Point)
    (u : ProfileCycleMiddlePoint n k center)
    (z : ProfileCycleInnerPoint n k center) :=
  BoundaryExitWordCode
    (profileInnerBoundary n (k + 1) center ∪
      profileOuterBoundary n k center) u.1 z.1

/-- Canonical retained final middle-to-outer word of one profile gap. -/
abbrev ProfileEscapeWordCode
    (n k : ℕ) (center : Point)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center) :=
  BoundaryExitWordCode
    (profileInnerBoundary n (k + 1) center ∪
      profileOuterBoundary n k center) u.1 w.1

/-- Literal chronological code for a profile gap with arbitrary recursively
refined child-return codes. -/
abbrev ProfileDecoratedGapCode
    {Child : Type} (n k : ℕ) (center : Point)
    (ChildCode : Child → ProfileCycleInnerPoint n k center →
      ProfileCycleMiddlePoint n k center → Type)
    (children : List Child)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center) :=
  DecoratedRenewalCode
    (ProfileInwardWordCode n k center) ChildCode
    (ProfileEscapeWordCode n k center) children u w

/-- Product stopped-word mass of a literal decorated profile-gap code. -/
def profileDecoratedGapCodeMass
    {Child : Type} {n k : ℕ} {center : Point}
    {ChildCode : Child → ProfileCycleInnerPoint n k center →
      ProfileCycleMiddlePoint n k center → Type}
    (childMass : ∀ child z v, ChildCode child z v → ℝ≥0∞)
    (children : List Child)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center) :
    ProfileDecoratedGapCode n k center ChildCode children u w → ℝ≥0∞ :=
  decoratedRenewalCodeMass
    (fun _ _ code ↦ stoppedWordMass code.1) childMass
    (fun _ _ code ↦ stoppedWordMass code.1) children u w

/-- Exact literal mass of one recursively decorated profile gap.  Every
child interval is present in exactly one `ChildCode` coordinate. -/
theorem tsum_profileDecoratedGapCodeMass
    {Child : Type} {n k : ℕ} {center : Point}
    {ChildCode : Child → ProfileCycleInnerPoint n k center →
      ProfileCycleMiddlePoint n k center → Type}
    (childMass : ∀ child z v, ChildCode child z v → ℝ≥0∞)
    (childKernel : Child → ProfileCycleInnerPoint n k center →
      ProfileCycleMiddlePoint n k center → ℝ≥0∞)
    (hchild : ∀ child z v,
      ∑' code, childMass child z v code = childKernel child z v)
    (children : List Child)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center) :
    (∑' code : ProfileDecoratedGapCode n k center ChildCode
        children u w,
      profileDecoratedGapCodeMass childMass children u w code) =
      profileDecoratedGapKernelENNReal n k center childKernel
        children u w := by
  have hinward : ∀ u' z,
      (∑' code : ProfileInwardWordCode n k center u' z,
        stoppedWordMass code.1) =
        profileInwardKernelENNReal n k center u' z := by
    intro u' z
    simpa only [ProfileInwardWordCode, profileInwardKernelENNReal] using
      tsum_stoppedWordMass_boundaryExitWordCode
        (profileInnerBoundary n (k + 1) center ∪
          profileOuterBoundary n k center) u'.1 z.1
  have hescape : ∀ u' w',
      (∑' code : ProfileEscapeWordCode n k center u' w',
        stoppedWordMass code.1) =
        profileEscapeKernelENNReal n k center u' w' := by
    intro u' w'
    simpa only [ProfileEscapeWordCode, profileEscapeKernelENNReal,
      AnnularOffspringKernel.annularEscapeKernel] using
      tsum_stoppedWordMass_boundaryExitWordCode
        (profileInnerBoundary n (k + 1) center ∪
          profileOuterBoundary n k center) u'.1 w'.1
  simpa only [ProfileDecoratedGapCode, profileDecoratedGapCodeMass,
      profileDecoratedGapKernelENNReal] using
    (tsum_decoratedRenewalCodeMass
      (InwardCode := ProfileInwardWordCode n k center)
      (ChildCode := ChildCode)
      (EscapeCode := ProfileEscapeWordCode n k center)
      (fun _ _ code ↦ stoppedWordMass code.1) childMass
      (fun _ _ code ↦ stoppedWordMass code.1)
      (profileInwardKernelENNReal n k center) childKernel
      (profileEscapeKernelENNReal n k center)
      hinward hchild hescape children u w)

end

end Erdos1165.AnnularDecoratedProfileCode
