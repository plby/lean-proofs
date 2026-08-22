/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricCoarseRecursiveTailEncoding
import ErdosProblems.Erdos1165.AsymmetricPaddedParsedBridgeCode
import ErdosProblems.Erdos1165.AnnularRecursiveBoundaryParserActual

/-!
# Padded literal codes attached to successful coarse tails

The successful coarse source already supplies supported endpoints and a
literal first-exit word at every erased coordinate.  This file merely views
those coordinates as the preliminary segments of the padded renewal.  The
resulting parsed padded code has exactly the original bridge product mass.

The separate tree-identification theorem, proved in the following clock
module, will identify its chronological tree list with the canonical
fixed-profile genealogy at the padded scale.
-/

open scoped BigOperators ENNReal

namespace Erdos1165.AsymmetricPaddedSuccessfulTailCode

open AnnularOffspringKernelRadial AnnularProfileClocks
open AnnularRecursiveProfileShape
open AnnularRecursiveProfileCodeAssembly
open AsymmetricCoarseCompletionCode AsymmetricCoarseRecursiveSourceCode
open AsymmetricCoarseRecursiveTailEncoding
open AsymmetricCoarseSuccessfulTailAtoms
open AsymmetricPaddedBridgeCode AsymmetricPaddedParsedBridgeCode
open AsymmetricPaddedPreludeCode
open AsymmetricPaddedRemoteRenewal
open MarkedBridgeFactorization ThickPoint

noncomputable section

/-- One successful recursive coordinate viewed as a padded coarse bridge. -/
def successfulPaddedCoarseBridge
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code)
    (j : Fin code.1.returnCount) : PaddedCoarseBridge n k y :=
  { start := coarseSuccessfulRecursiveEntrance
        hn hkTwo hdelta code tail j
    endpoint := coarseSuccessfulRecursiveEndpoint
        hn hkTwo hdelta code tail j
    bridge := by
      let assembled := recursiveProfileGapBoundaryExitWordCode n (k + 1) y hn
        (by omega)
        (profileRefinementTrees code.1.returnCount
          (coarseSuccessfulProfileRest code tail)
          (coarseSuccessfulGapChain hn hkTwo hdelta code tail) j)
        (coarseSuccessfulCanonicalRecursiveTree_fits
          hn hkTwo hdelta code tail j)
        (coarseSuccessfulRecursiveEntrance hn hkTwo hdelta code tail j)
        (coarseSuccessfulRecursiveEndpoint hn hkTwo hdelta code tail j)
        (coarseSuccessfulCanonicalRecursiveCode
          hn hkTwo hdelta code tail j)
      refine ⟨assembled.1, ?_⟩
      simpa only [profileOuterBoundary, profileInnerBoundary,
        Nat.add_sub_cancel] using assembled.2 }

/-- The chronological coarse bridges of a successful tail, now carrying
the endpoint types expected by the padded renewal. -/
def successfulPaddedCoarseBridges
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code) :
    List (PaddedCoarseBridge n k y) :=
  List.ofFn (successfulPaddedCoarseBridge hn hkTwo hdelta code tail)

@[simp] theorem successfulPaddedCoarseBridge_bridge
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code)
    (j : Fin code.1.returnCount) :
    (successfulPaddedCoarseBridge hn hkTwo hdelta code tail j).bridge.1 =
      (tail.1 j).1.1 := by
  exact coarseSuccessfulCanonicalRecursiveBoundaryCode_eq_bridge
    hn hkTwo hdelta code tail j

/-- Product mass of the padded source list is the original successful
bridge product. -/
theorem successfulPaddedCoarseBridges_mass
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code) :
    paddedCoarseBridgeMass
        (successfulPaddedCoarseBridges hn hkTwo hdelta code tail) =
      ∏ j, stoppedWordMass (tail.1 j).1.1 := by
  classical
  unfold paddedCoarseBridgeMass successfulPaddedCoarseBridges
  simp only [List.map_ofFn, List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro j _hj
  simp

/-- Hence the canonical parsed padded code has exactly the successful
bridge product mass. -/
theorem parsedSuccessfulPaddedBridgeCode_mass
    {start n k p : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hkp : k + 1 < p) (hp : p ≤ n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code) :
    paddedPreludeMultiCodeMass n k p y
        (parsedPaddedBridgeCode hn hkp hp
          (successfulPaddedCoarseBridges hn hkTwo hdelta code tail)) =
      ∏ j, stoppedWordMass (tail.1 j).1.1 := by
  rw [parsedPaddedBridgeCode_mass,
    successfulPaddedCoarseBridges_mass hn hkTwo hdelta code tail]

end

end Erdos1165.AsymmetricPaddedSuccessfulTailCode
