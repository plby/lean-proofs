/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricPaddedSuccessfulTailRow
import ErdosProblems.Erdos1165.CoarseProfileTailUpper

/-!
# Constrained coarse tails in the padded recursive row

This is the prefix-free padded encoding for a coarse completion whose
continuation is constrained only from the retained scale onward.  Unlike the
successful-tail row, no level-one return condition is imposed.  The padding
still exposes the exact unmarked kernel of the retained coarse skeleton.
-/

open scoped BigOperators ENNReal

namespace Erdos1165.AsymmetricPaddedConstrainedTailRow

open AnnularErasedParentSpineRowPartition
open AnnularLiteralNestedProfileTailUpper AnnularOffspringKernelRadial
open AnnularProfileClocks
open AnnularRecursiveBoundaryParser AnnularRecursiveBoundaryParserActual
open AnnularRecursiveProfileEndpointTail
open AnnularRecursiveProfileShape
open AnnularRecursiveProfileCodeAssembly
open AnnularRecursiveWeightedRenewal AppendixFirstMoment AppendixPairMoment
open AlternatingConcatPrefixFree
open AsymmetricPaddedRecursiveFrontier
open AsymmetricCoarseCompletionCode AsymmetricCoarseRecursiveSourceCode
open AsymmetricCoarseRightProfilePrefix
open AsymmetricCoarseSuccessfulTailAtoms
open AsymmetricPaddedBridgeCode AsymmetricPaddedParsedBridgeCode
open AsymmetricPaddedPrefixMultiplicity
open AsymmetricPaddedPreludeCode AsymmetricPaddedRecursiveRenewal
open AsymmetricPaddedRemoteRenewal
open AsymmetricPaddedSuccessfulTailRow
open AsymmetricCoarseScanSignature AsymmetricCoarseSplitCompletion
open AsymmetricPairTwoStageMass AsymmetricSplitLevelSplice
open MarkedBoundaryVisitKernel
open CoarseProfileTailUpper MarkedBridgeFactorization ThickPoint
open ProfileGapChain ProfileListExponent ProfileWeightUpper
open PlanarPotential
open TerminalSkeletonWords

noncomputable section

attribute [local instance] Classical.propDecidable

/-- One constrained recursive coordinate viewed as a padded coarse bridge. -/
def constrainedPaddedCoarseBridge
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseConstrainedTailReturnTuple code)
    (j : Fin code.1.returnCount) : PaddedCoarseBridge n k y :=
  { start := coarseConstrainedTailRecursiveEntrance
        hn hkTwo hdelta hy code tail j
    endpoint := coarseConstrainedTailRecursiveEndpoint
        hn hkTwo hdelta hy code tail j
    bridge := by
      let assembled := recursiveProfileGapBoundaryExitWordCode n (k + 1) y hn
        (by omega)
        (profileRefinementTrees code.1.returnCount
          (coarseConstrainedTailProfileRest tail)
          (coarseConstrainedTailGapChain hn hkTwo hdelta hy code tail) j)
        (coarseConstrainedTailCanonicalRecursiveTree_fits
          hn hkTwo hdelta hy code tail j)
        (coarseConstrainedTailRecursiveEntrance
          hn hkTwo hdelta hy code tail j)
        (coarseConstrainedTailRecursiveEndpoint
          hn hkTwo hdelta hy code tail j)
        (coarseConstrainedTailCanonicalRecursiveCode
          hn hkTwo hdelta hy code tail j)
      refine ⟨assembled.1, ?_⟩
      simpa only [profileOuterBoundary, profileInnerBoundary,
        Nat.add_sub_cancel] using assembled.2 }

/-- Chronological padded bridges of a constrained coarse tail. -/
def constrainedPaddedCoarseBridges
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseConstrainedTailReturnTuple code) :
    List (PaddedCoarseBridge n k y) :=
  List.ofFn
    (constrainedPaddedCoarseBridge hn hkTwo hdelta hy code tail)

@[simp] theorem constrainedPaddedCoarseBridge_bridge
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseConstrainedTailReturnTuple code)
    (j : Fin code.1.returnCount) :
    (constrainedPaddedCoarseBridge
      hn hkTwo hdelta hy code tail j).bridge.1 = (tail.1 j).1.1 := by
  exact coarseConstrainedTailCanonicalRecursiveBoundaryCode_eq_bridge
    hn hkTwo hdelta hy code tail j

theorem constrainedPaddedCoarseBridges_mass
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseConstrainedTailReturnTuple code) :
    paddedCoarseBridgeMass
        (constrainedPaddedCoarseBridges
          hn hkTwo hdelta hy code tail) =
      ∏ j, stoppedWordMass (tail.1 j).1.1 := by
  classical
  unfold paddedCoarseBridgeMass constrainedPaddedCoarseBridges
  simp only [List.map_ofFn, List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro j _hj
  simp

theorem parsedConstrainedPaddedBridgeCode_mass
    {start n k p : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (hkp : k + 1 < p) (hp : p ≤ n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseConstrainedTailReturnTuple code) :
    paddedPreludeMultiCodeMass n k p y
        (parsedPaddedBridgeCode hn hkp hp
          (constrainedPaddedCoarseBridges
            hn hkTwo hdelta hy code tail)) =
      ∏ j, stoppedWordMass (tail.1 j).1.1 := by
  rw [parsedPaddedBridgeCode_mass,
    constrainedPaddedCoarseBridges_mass hn hkTwo hdelta hy code tail]

/-- The root parser recovers the canonical constrained-tail tree. -/
theorem constrainedPaddedCoarseBridge_root_tree_eq
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseConstrainedTailReturnTuple code)
    (j : Fin code.1.returnCount) :
    (parseBoundaryGap n y hn (n - (k + 1)) (k + 1) (by omega) (by omega)
      (constrainedPaddedCoarseBridge
        hn hkTwo hdelta hy code tail j).start
      (constrainedPaddedCoarseBridge
        hn hkTwo hdelta hy code tail j).endpoint
      (constrainedPaddedCoarseBridge
        hn hkTwo hdelta hy code tail j).bridge).tree =
      profileRefinementTrees code.1.returnCount
        (coarseConstrainedTailProfileRest tail)
        (coarseConstrainedTailGapChain hn hkTwo hdelta hy code tail) j := by
  let data := coarseConstrainedTailProfileSegmentData
    hn hkTwo hdelta hy code tail
  let u := coarseConstrainedTailRecursiveEntrance
    hn hkTwo hdelta hy code tail j
  let w := coarseConstrainedTailRecursiveEndpoint
    hn hkTwo hdelta hy code tail j
  let actual := actualBoundaryExitWordCodeAt
    (data.headComplete j j.isLt) u w
    (coarseConstrainedTailRecursiveEntrance_val
      hn hkTwo hdelta hy code tail j).symm
    (coarseConstrainedTailRecursiveEndpoint_val
      hn hkTwo hdelta hy code tail j).symm
  have hsource :
      (constrainedPaddedCoarseBridge
        hn hkTwo hdelta hy code tail j).bridge = actual := by
    apply Subtype.ext
    rw [constrainedPaddedCoarseBridge_bridge,
      actualBoundaryExitWordCodeAt_val]
    exact coarseReturnBridge_eq_profileGapStoppedWord hn code tail.1 j
  have hrestLength :
      (coarseConstrainedTailProfileRest tail).length = n - (k + 1) := by
    have hlength := profileSegmentValues_length
      (coarseTailProfile code tail.1) (k + 1)
    rw [coarseConstrainedTailProfileSegment_eq hn hkTwo code tail] at hlength
    simp only [List.length_cons] at hlength
    omega
  change
    (parseBoundaryGap n y hn (n - (k + 1)) (k + 1) (by omega) (by omega)
      u w (constrainedPaddedCoarseBridge
        hn hkTwo hdelta hy code tail j).bridge).tree = _
  rw [hsource]
  have hparsed := parseBoundaryGap_actual_tree hn hy
    (coarseConstrainedTailProfileRest tail) (by omega)
    (coarseConstrainedTailProfileRest_depth hkTwo code tail) data j u w
    (coarseConstrainedTailRecursiveEntrance_val
      hn hkTwo hdelta hy code tail j).symm
    (coarseConstrainedTailRecursiveEndpoint_val
      hn hkTwo hdelta hy code tail j).symm
  simpa only [hrestLength] using hparsed.trans
    (coarseConstrainedTailParsedProfileGap_tree_eq
      hn hkTwo hdelta hy code tail j)

/-- Parsed constrained bridge trees form the corresponding fixed-depth
frontier of the high-tail gap chain. -/
theorem parsedConstrainedPaddedBridgeTrees_eq_atDepth
    {start n k p : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (hkp : k + 1 < p) (hp : p ≤ n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseConstrainedTailReturnTuple code) :
    (parsedPaddedBridgeDecorationList hn hkp hp
      (constrainedPaddedCoarseBridges
        hn hkTwo hdelta hy code tail)).1 =
      profileRefinementTreesAtDepth
        (coarseConstrainedTailProfileRest tail)
        (coarseConstrainedTailGapChain hn hkTwo hdelta hy code tail)
        (p - (k + 1)) (by
          have hlength := profileSegmentValues_length
            (coarseTailProfile code tail.1) (k + 1)
          rw [coarseConstrainedTailProfileSegment_eq
            hn hkTwo code tail] at hlength
          simp only [List.length_cons] at hlength
          omega) := by
  rw [parsedPaddedBridgeDecorationList_trees_eq_flatMap_frontier
    hn hkp hp]
  unfold constrainedPaddedCoarseBridges
  calc
    (List.ofFn (constrainedPaddedCoarseBridge
        hn hkTwo hdelta hy code tail)).flatMap
          (fun source => profileRefinementTreeFrontier (p - (k + 1))
            (parseBoundaryGap n y hn (n - (k + 1)) (k + 1)
              (by omega) (by omega) source.start source.endpoint
              source.bridge).tree) =
        (List.ofFn (fun j : Fin code.1.returnCount =>
          profileRefinementTrees code.1.returnCount
            (coarseConstrainedTailProfileRest tail)
            (coarseConstrainedTailGapChain
              hn hkTwo hdelta hy code tail) j)).flatMap
              (profileRefinementTreeFrontier (p - (k + 1))) := by
        simp only [List.flatMap_def, List.map_ofFn]
        apply congrArg List.flatten
        rw [List.ofFn_inj]
        funext j
        simpa only [Function.comp_apply] using congrArg
          (profileRefinementTreeFrontier (p - (k + 1)))
          (constrainedPaddedCoarseBridge_root_tree_eq
            hn hkTwo hdelta hy code tail j)
    _ = profileRefinementTreesAtDepth
          (coarseConstrainedTailProfileRest tail)
          (coarseConstrainedTailGapChain hn hkTwo hdelta hy code tail)
          (p - (k + 1)) (by
            have hlength := profileSegmentValues_length
              (coarseTailProfile code tail.1) (k + 1)
            rw [coarseConstrainedTailProfileSegment_eq
              hn hkTwo code tail] at hlength
            simp only [List.length_cons] at hlength
            omega) :=
      flatMap_profileRefinementTreeFrontier_profileRefinementTrees
        (coarseConstrainedTailProfileRest tail)
        (coarseConstrainedTailGapChain hn hkTwo hdelta hy code tail)
        (p - (k + 1)) (by
          have hlength := profileSegmentValues_length
            (coarseTailProfile code tail.1) (k + 1)
          rw [coarseConstrainedTailProfileSegment_eq
            hn hkTwo code tail] at hlength
          simp only [List.length_cons] at hlength
          omega)

theorem exists_paddedGapChain_parsedConstrainedPaddedBridgeTrees_eq
    {start n k p : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (hkp : k + 1 < p) (hp : p ≤ n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseConstrainedTailReturnTuple code) :
    ∃ chain : GapChain
        (profileAtScale (coarseTailProfile code tail.1) p ::
          (profileSegmentValues (coarseTailProfile code tail.1) p).tail),
      (parsedPaddedBridgeDecorationList hn hkp hp
        (constrainedPaddedCoarseBridges
          hn hkTwo hdelta hy code tail)).1 =
        List.ofFn fun i : Fin
            (profileAtScale (coarseTailProfile code tail.1) p) =>
          profileRefinementTrees
            (profileAtScale (coarseTailProfile code tail.1) p)
            (profileSegmentValues (coarseTailProfile code tail.1) p).tail
            chain i := by
  let m := coarseTailProfile code tail.1
  let depth := p - (k + 1)
  have hdepth : depth ≤ (coarseConstrainedTailProfileRest tail).length := by
    have hlength := profileSegmentValues_length m (k + 1)
    rw [coarseConstrainedTailProfileSegment_eq hn hkTwo code tail] at hlength
    simp only [List.length_cons] at hlength
    omega
  have hdrop :
      (code.1.returnCount :: coarseConstrainedTailProfileRest tail).drop depth =
        profileAtScale m p :: (profileSegmentValues m p).tail := by
    calc
      (code.1.returnCount :: coarseConstrainedTailProfileRest tail).drop depth =
          (profileSegmentValues m (k + 1)).drop depth := by
            rw [coarseConstrainedTailProfileSegment_eq hn hkTwo code tail]
      _ = profileSegmentValues m p := by
            exact profileSegmentValues_drop m (by omega) hp
      _ = profileAtScale m p :: (profileSegmentValues m p).tail :=
            profileSegmentValues_eq_head_cons_tail hp m
  obtain ⟨chain, htrees⟩ :=
    exists_gapChain_profileRefinementTreesAtDepth
      (coarseConstrainedTailProfileRest tail)
      (coarseConstrainedTailGapChain hn hkTwo hdelta hy code tail)
      depth hdepth hdrop
  refine ⟨chain, ?_⟩
  exact (parsedConstrainedPaddedBridgeTrees_eq_atDepth
    hn hkTwo hdelta hy hkp hp code tail).trans htrees

/-- Canonical padded-scale chain selected from the constrained source
parser. -/
noncomputable def constrainedPaddedGapChain
    {start n k p : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (hkp : k + 1 < p) (hp : p ≤ n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseConstrainedTailReturnTuple code) :
    GapChain (profileAtScale (coarseTailProfile code tail.1) p ::
      (profileSegmentValues (coarseTailProfile code tail.1) p).tail) :=
  Classical.choose
    (exists_paddedGapChain_parsedConstrainedPaddedBridgeTrees_eq
      hn hkTwo hdelta hy hkp hp code tail)

theorem parsedConstrainedPaddedBridgeTrees_eq_constrainedPaddedGapChain
    {start n k p : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (hkp : k + 1 < p) (hp : p ≤ n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseConstrainedTailReturnTuple code) :
    (parsedPaddedBridgeDecorationList hn hkp hp
      (constrainedPaddedCoarseBridges
        hn hkTwo hdelta hy code tail)).1 =
      List.ofFn fun i : Fin
          (profileAtScale (coarseTailProfile code tail.1) p) =>
        profileRefinementTrees
          (profileAtScale (coarseTailProfile code tail.1) p)
          (profileSegmentValues (coarseTailProfile code tail.1) p).tail
          (constrainedPaddedGapChain
            hn hkTwo hdelta hy hkp hp code tail) i :=
  Classical.choose_spec
    (exists_paddedGapChain_parsedConstrainedPaddedBridgeTrees_eq
      hn hkTwo hdelta hy hkp hp code tail)

/-- Segment endpoints of a constrained padded tail. -/
def constrainedPaddedCoarseBridgeSegments
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (p : ℕ) (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseConstrainedTailReturnTuple code) :
    List ((PaddedNearPoint n k y ⊕ PaddedMiddlePoint n p y) ×
      PaddedOuterPoint n k y) :=
  paddedCoarseBridgeSegments n k p y
    (constrainedPaddedCoarseBridges hn hkTwo hdelta hy code tail)

/-- Segment endpoints depend only on the retained skeleton. -/
theorem constrainedPaddedCoarseBridgeSegments_eq
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (p : ℕ) (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (left right : CoarseConstrainedTailReturnTuple code) :
    constrainedPaddedCoarseBridgeSegments
        p hn hkTwo hdelta hy code left =
      constrainedPaddedCoarseBridgeSegments
        p hn hkTwo hdelta hy code right := by
  unfold constrainedPaddedCoarseBridgeSegments
  rw [paddedCoarseBridgeSegments_eq_map,
    paddedCoarseBridgeSegments_eq_map]
  unfold constrainedPaddedCoarseBridges
  simp only [List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  apply Prod.ext
  · apply congrArg Sum.inl
    apply Subtype.ext
    exact (coarseConstrainedTailRecursiveEntrance_eq_skeleton
      hn hkTwo hdelta hy code left j).trans
        (coarseConstrainedTailRecursiveEntrance_eq_skeleton
          hn hkTwo hdelta hy code right j).symm
  · apply Subtype.ext
    exact (coarseConstrainedTailRecursiveEndpoint_eq_skeleton
      hn hkTwo hdelta hy code left j).trans
        (coarseConstrainedTailRecursiveEndpoint_eq_skeleton
          hn hkTwo hdelta hy code right j).symm

theorem constrainedPaddedCoarseBridgeSegments_length
    {start n k p : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseConstrainedTailReturnTuple code) :
    (constrainedPaddedCoarseBridgeSegments
      p hn hkTwo hdelta hy code tail).length = code.1.returnCount := by
  unfold constrainedPaddedCoarseBridgeSegments
  rw [paddedCoarseBridgeSegments_eq_map]
  simp [constrainedPaddedCoarseBridges]

/-- Ambient padded key over the canonical low prefix. -/
def PaddedConstrainedTailKey
    {start n k p : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (reference : CoarseConstrainedTailReturnTuple code) :=
  Σ profile : {m : Profile n //
      IsConstrainedProfile profileDelta m ∧
        profilePrefix hkTwo hk m = coarseConstrainedTailPrefix code},
    Σ chain : GapChain
        (profileAtScale profile.1 p ::
          (profileSegmentValues profile.1 p).tail),
      PaddedPreludeMultiCode n k p y
        (constrainedPaddedCoarseBridgeSegments
          p hn hkTwo hdelta hy code reference)
        (List.ofFn fun i : Fin (profileAtScale profile.1 p) =>
          profileRefinementTrees (profileAtScale profile.1 p)
            (profileSegmentValues profile.1 p).tail chain i)

def PaddedConstrainedTailKey.mass
    {start n k p : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} {hn : 2 ≤ n} {hkTwo : 2 ≤ k + 1}
    {hdelta : profileDelta ≤ 1} {hy : y ∈ candidateBox n}
    {code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)}
    {reference : CoarseConstrainedTailReturnTuple code}
    (key : PaddedConstrainedTailKey
      (p := p) hn hkTwo hdelta hy code reference) : ℝ≥0∞ :=
  paddedPreludeMultiCodeMass n k p y key.2.2

/-- A constrained tail mapped into its proof-free padded key. -/
noncomputable def paddedKeyOfConstrainedTail
    {start n k p : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (hkp : k + 1 < p) (hp : p ≤ n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (reference tail : CoarseConstrainedTailReturnTuple code) :
    PaddedConstrainedTailKey
      (p := p) hn hkTwo hdelta hy code reference :=
  ⟨⟨coarseTailProfile code tail.1, tail.2,
      profilePrefix_coarseTailProfile_eq hn hkTwo code tail.1⟩,
    constrainedPaddedGapChain hn hkTwo hdelta hy hkp hp code tail,
    transportPaddedPreludeMultiCode
      (constrainedPaddedCoarseBridgeSegments_eq
        p hn hkTwo hdelta hy code tail reference)
      (parsedConstrainedPaddedBridgeTrees_eq_constrainedPaddedGapChain
        hn hkTwo hdelta hy hkp hp code tail)
      (parsedPaddedBridgeCode hn hkp hp
        (constrainedPaddedCoarseBridges
          hn hkTwo hdelta hy code tail))⟩

theorem mass_paddedKeyOfConstrainedTail
    {start n k p : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (hkp : k + 1 < p) (hp : p ≤ n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (reference tail : CoarseConstrainedTailReturnTuple code) :
    (paddedKeyOfConstrainedTail
      hn hkTwo hdelta hy hkp hp code reference tail).mass =
      ∏ j, stoppedWordMass (tail.1 j).1.1 := by
  let hsegments := constrainedPaddedCoarseBridgeSegments_eq
    p hn hkTwo hdelta hy code tail reference
  change paddedCoarseBridgeSegments n k p y
      (constrainedPaddedCoarseBridges hn hkTwo hdelta hy code tail) =
    paddedCoarseBridgeSegments n k p y
      (constrainedPaddedCoarseBridges hn hkTwo hdelta hy code reference)
    at hsegments
  let htrees :=
    parsedConstrainedPaddedBridgeTrees_eq_constrainedPaddedGapChain
      hn hkTwo hdelta hy hkp hp code tail
  change paddedPreludeMultiCodeMass n k p y
      (transportPaddedPreludeMultiCode hsegments htrees
        (parsedPaddedBridgeCode hn hkp hp
          (constrainedPaddedCoarseBridges
            hn hkTwo hdelta hy code tail))) = _
  rw [paddedPreludeMultiCodeMass_transport]
  exact parsedConstrainedPaddedBridgeCode_mass
    hn hkTwo hdelta hy hkp hp code tail

theorem paddedCoarseBridgeWords_constrained
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseConstrainedTailReturnTuple code) :
    paddedCoarseBridgeWords
        (constrainedPaddedCoarseBridges hn hkTwo hdelta hy code tail) =
      List.ofFn fun j : Fin code.1.returnCount =>
        List.ofFn (tail.1 j).1.1.2 := by
  rw [paddedCoarseBridgeWords_eq_map]
  unfold constrainedPaddedCoarseBridges
  simp only [List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  exact congrArg (fun word : StoppedWord => List.ofFn word.2)
    (constrainedPaddedCoarseBridge_bridge
      hn hkTwo hdelta hy code tail j)

theorem paddedKeyOfConstrainedTail_words
    {start n k p : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (hkp : k + 1 < p) (hp : p ≤ n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (reference tail : CoarseConstrainedTailReturnTuple code) :
    paddedPreludeMultiCodeWords n k p y
        (paddedKeyOfConstrainedTail
          hn hkTwo hdelta hy hkp hp code reference tail).2.2 =
      List.ofFn fun j : Fin code.1.returnCount =>
        List.ofFn (tail.1 j).1.1.2 := by
  let hsegments := constrainedPaddedCoarseBridgeSegments_eq
    p hn hkTwo hdelta hy code tail reference
  change paddedCoarseBridgeSegments n k p y
      (constrainedPaddedCoarseBridges hn hkTwo hdelta hy code tail) =
    paddedCoarseBridgeSegments n k p y
      (constrainedPaddedCoarseBridges hn hkTwo hdelta hy code reference)
    at hsegments
  let htrees :=
    parsedConstrainedPaddedBridgeTrees_eq_constrainedPaddedGapChain
      hn hkTwo hdelta hy hkp hp code tail
  change paddedPreludeMultiCodeWords n k p y
      (transportPaddedPreludeMultiCode hsegments htrees
        (parsedPaddedBridgeCode hn hkp hp
          (constrainedPaddedCoarseBridges
            hn hkTwo hdelta hy code tail))) = _
  rw [paddedPreludeMultiCodeWords_transport,
    parsedPaddedBridgeCode_words]
  exact paddedCoarseBridgeWords_constrained
    hn hkTwo hdelta hy code tail

theorem paddedKeyOfConstrainedTail_injective
    {start n k p : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (hkp : k + 1 < p) (hp : p ≤ n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (reference : CoarseConstrainedTailReturnTuple code) :
    Function.Injective
      (paddedKeyOfConstrainedTail
        hn hkTwo hdelta hy hkp hp code reference) := by
  intro left right hkey
  have hwords := congrArg
    (fun key : PaddedConstrainedTailKey
        (p := p) hn hkTwo hdelta hy code reference =>
      paddedPreludeMultiCodeWords n k p y key.2.2) hkey
  rw [paddedKeyOfConstrainedTail_words
      hn hkTwo hdelta hy hkp hp code reference left,
    paddedKeyOfConstrainedTail_words
      hn hkTwo hdelta hy hkp hp code reference right] at hwords
  have hfunctions := List.ofFn_injective hwords
  apply Subtype.ext
  funext j
  apply Subtype.ext
  apply Subtype.ext
  let leftWord : StoppedWord := (left.1 j).1.1
  let rightWord : StoppedWord := (right.1 j).1.1
  have hj : List.ofFn leftWord.2 = List.ofFn rightWord.2 :=
    congrFun hfunctions j
  exact calc
    leftWord = listStoppedWord (List.ofFn leftWord.2) :=
      (listStoppedWord_ofFn leftWord).symm
    _ = listStoppedWord (List.ofFn rightWord.2) :=
      congrArg listStoppedWord hj
    _ = rightWord := listStoppedWord_ofFn rightWord

theorem tsum_constrainedBridgeMass_le_paddedConstrainedTailKeyMass
    {start n k p : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (hkp : k + 1 < p) (hp : p ≤ n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (reference : CoarseConstrainedTailReturnTuple code) :
    (∑' tail : CoarseConstrainedTailReturnTuple code,
        ∏ j, stoppedWordMass (tail.1 j).1.1) ≤
      ∑' key : PaddedConstrainedTailKey
        (p := p) hn hkTwo hdelta hy code reference, key.mass := by
  calc
    _ = ∑' tail : CoarseConstrainedTailReturnTuple code,
        (paddedKeyOfConstrainedTail
          hn hkTwo hdelta hy hkp hp code reference tail).mass := by
            apply tsum_congr
            intro tail
            exact (mass_paddedKeyOfConstrainedTail
              hn hkTwo hdelta hy hkp hp code reference tail).symm
    _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective
      (paddedKeyOfConstrainedTail_injective
        hn hkTwo hdelta hy hkp hp code reference) _

/-- Tonelli expansion of the ambient constrained-tail padded keys. -/
theorem tsum_paddedConstrainedTailKeyMass_eq_sum_fixedPrefix_continuation
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (reference : CoarseConstrainedTailReturnTuple code) :
    let segments : List
        ((PaddedNearPoint n k y ⊕
            PaddedMiddlePoint n (pairPrefixScale n k) y) ×
          PaddedOuterPoint n k y) :=
      constrainedPaddedCoarseBridgeSegments
        (pairPrefixScale n k) hn hkTwo hdelta hy code reference
    (∑' key : PaddedConstrainedTailKey
        (p := pairPrefixScale n k) hn hkTwo hdelta hy code reference,
        key.mass) =
      ∑ m ∈ (constrainedProfiles n profileDelta).filter
          (fun m ↦ profilePrefix hkTwo hk m =
            coarseConstrainedTailPrefix code),
        paddedPreludeMultiRecursiveProfileContinuation n k y m segments := by
  dsimp only
  let P := {m : Profile n //
    IsConstrainedProfile profileDelta m ∧
      profilePrefix hkTwo hk m = coarseConstrainedTailPrefix code}
  let F := (constrainedProfiles n profileDelta).filter
    (fun m ↦ profilePrefix hkTwo hk m = coarseConstrainedTailPrefix code)
  let e : {m : Profile n // m ∈ F} ≃ P :=
    { toFun := fun m ↦ ⟨m.1,
        mem_constrainedProfiles.mp (Finset.mem_filter.mp m.2).1,
        (Finset.mem_filter.mp m.2).2⟩
      invFun := fun m ↦ ⟨m.1, Finset.mem_filter.mpr
        ⟨mem_constrainedProfiles.mpr m.2.1, m.2.2⟩⟩
      left_inv := by intro m; apply Subtype.ext; rfl
      right_inv := by intro m; apply Subtype.ext; rfl }
  let segments := constrainedPaddedCoarseBridgeSegments
    (pairPrefixScale n k) hn hkTwo hdelta hy code reference
  have hrow (profile : P) :
      (∑' chain : GapChain
          (profileAtScale profile.1 (pairPrefixScale n k) ::
            (profileSegmentValues profile.1 (pairPrefixScale n k)).tail),
        ∑' value : PaddedPreludeMultiCode n k (pairPrefixScale n k) y
          segments
          (List.ofFn fun i : Fin
              (profileAtScale profile.1 (pairPrefixScale n k)) ↦
            profileRefinementTrees
              (profileAtScale profile.1 (pairPrefixScale n k))
              (profileSegmentValues profile.1
                (pairPrefixScale n k)).tail chain i),
          paddedPreludeMultiCodeMass n k (pairPrefixScale n k) y value) =
        paddedPreludeMultiRecursiveProfileContinuation
          n k y profile.1 segments := by
    rw [tsum_fintype]
    unfold paddedPreludeMultiRecursiveProfileContinuation
    apply Finset.sum_congr rfl
    intro chain _hchain
    exact tsum_paddedPreludeMultiCodeMass_eq
      n k (pairPrefixScale n k) y _ _
  simp only [PaddedConstrainedTailKey.mass, PaddedConstrainedTailKey]
  rw [ENNReal.tsum_sigma']
  simp_rw [ENNReal.tsum_sigma']
  change (∑' profile : P, _) = _
  calc
    (∑' profile : P, _) =
        ∑' profile : P,
          paddedPreludeMultiRecursiveProfileContinuation
            n k y profile.1 segments := by
      apply tsum_congr
      exact hrow
    _ = ∑' m : {m : Profile n // m ∈ F},
          paddedPreludeMultiRecursiveProfileContinuation
            n k y m.1 segments := by
      symm
      calc
        (∑' m : {m : Profile n // m ∈ F},
            paddedPreludeMultiRecursiveProfileContinuation
              n k y m.1 segments) =
            ∑' m : {m : Profile n // m ∈ F},
              paddedPreludeMultiRecursiveProfileContinuation
                n k y (e m).1 segments := by
          apply tsum_congr
          intro m
          rfl
        _ = _ := e.tsum_eq
          (fun profile : P ↦
            paddedPreludeMultiRecursiveProfileContinuation
              n k y profile.1 segments)
    _ = ∑ m ∈ F,
          paddedPreludeMultiRecursiveProfileContinuation
            n k y m segments := by
      rw [tsum_fintype]
      exact (Finset.sum_subtype F (fun _ ↦ Iff.rfl)
        (fun m ↦ paddedPreludeMultiRecursiveProfileContinuation
          n k y m segments)).symm
    _ = _ := by rfl

/-- Every unmarked bridge over the retained endpoints has the constant erased
scan signature carried by an inhabited constrained coarse code. -/
def coarseSignatureReturnCodeEquiv_of_constrainedReference
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point}
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (reference : CoarseConstrainedTailReturnTuple code)
    (j : Fin code.1.returnCount) :
    BoundaryExitWordCode (profileInnerBoundary n k y)
        (code.1.skeleton.2.1 j) (code.1.skeleton.2.2 j) ≃
      CoarseSignatureReturnCode x y
        (profileInnerBoundary n k y) code.1 j where
  toFun bridge := ⟨bridge, by
    constructor
    · change (fun _ _ ↦ ((0, 0),
          TerminalBoundaryScan.initialState)) = (code.1.signature j).1
      have href := (reference.1 j).2.1
      change (fun _ _ ↦ ((0, 0),
        TerminalBoundaryScan.initialState)) = (code.1.signature j).1 at href
      exact href
    · change (fun _ ↦ ((0, 0),
          TerminalBoundaryScan.initialState)) = (code.1.signature j).2
      have href := (reference.1 j).2.2
      change (fun _ ↦ ((0, 0),
        TerminalBoundaryScan.initialState)) = (code.1.signature j).2 at href
      exact href⟩
  invFun bridge := bridge.1
  left_inv _ := rfl
  right_inv bridge := Subtype.ext rfl

theorem coarseAtom_kernel_eq_unmarked_of_constrainedReference
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point}
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (reference : CoarseConstrainedTailReturnTuple code)
    (j : Fin code.1.returnCount) :
    (coarseAtom code).kernel j =
      skeletonExitKernel (profileInnerBoundary n k y)
        (code.1.skeleton.2.1 j) (code.1.skeleton.2.2 j) := by
  unfold coarseAtom coarseSplitCompletionAtomOfData
  rw [fixComplement_kernel]
  unfold ComplementarySkeletonAtom.kernel restrictBridges
  calc
    (∑' b : CoarseSignatureReturnCode x y
          (profileInnerBoundary n k y) code.1 j,
        stoppedWordMass b.1.1) =
        ∑' b : BoundaryExitWordCode (profileInnerBoundary n k y)
          (code.1.skeleton.2.1 j) (code.1.skeleton.2.2 j),
          stoppedWordMass b.1 := by
            exact
              ((coarseSignatureReturnCodeEquiv_of_constrainedReference
                code reference j).tsum_eq
                (fun b : CoarseSignatureReturnCode x y
                  (profileInnerBoundary n k y) code.1 j ↦
                    stoppedWordMass b.1.1)).symm
    _ = _ := tsum_stoppedWordMass_boundaryExitWordCode _ _ _

/-- Unmarked endpoint product exposed by the padded constrained renewal. -/
def paddedConstrainedUnmarkedKernelProduct
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (reference : CoarseConstrainedTailReturnTuple code) : ℝ≥0∞ :=
  ∏ j, paddedNearUnmarkedKernelENNReal n k y
    (coarseConstrainedTailRecursiveEntrance
      hn hkTwo hdelta hy code reference j)
    (coarseConstrainedTailRecursiveEndpoint
      hn hkTwo hdelta hy code reference j)

theorem coarseAtom_kernel_prod_eq_paddedConstrainedUnmarkedKernelProduct
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (reference : CoarseConstrainedTailReturnTuple code) :
    (∏ j, (coarseAtom code).kernel j) =
      paddedConstrainedUnmarkedKernelProduct
        hn hkTwo hdelta hy code reference := by
  unfold paddedConstrainedUnmarkedKernelProduct
  apply Finset.prod_congr rfl
  intro j _hj
  rw [coarseAtom_kernel_eq_unmarked_of_constrainedReference
    code reference j]
  unfold paddedNearUnmarkedKernelENNReal
  rw [coarseConstrainedTailRecursiveEntrance_eq_skeleton
      hn hkTwo hdelta hy code reference j,
    coarseConstrainedTailRecursiveEndpoint_eq_skeleton
      hn hkTwo hdelta hy code reference j]

theorem constrainedPaddedCoarseBridgeSegments_unmarked_prod_eq
    {start n k p : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (reference : CoarseConstrainedTailReturnTuple code) :
    ((constrainedPaddedCoarseBridgeSegments
        p hn hkTwo hdelta hy code reference).map
      fun segment ↦ match segment.1 with
        | Sum.inl initial =>
            paddedNearUnmarkedKernelENNReal n k y initial segment.2
        | Sum.inr u =>
            paddedUnmarkedKernelENNReal n k p y u segment.2).prod =
      paddedConstrainedUnmarkedKernelProduct
        hn hkTwo hdelta hy code reference := by
  unfold constrainedPaddedCoarseBridgeSegments
  rw [paddedCoarseBridgeSegments_eq_map]
  unfold constrainedPaddedCoarseBridges
    paddedConstrainedUnmarkedKernelProduct
  simp only [List.map_map, List.map_ofFn, Function.comp_apply,
    List.prod_ofFn]
  rfl

theorem tsum_constrainedBridgeMass_le_radialTail_mul_unmarked
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta radialTail : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hy : y ∈ candidateBox n)
    (hkp : k + 1 < pairPrefixScale n k)
    (hp : pairPrefixScale n k ≤ n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (reference : CoarseConstrainedTailReturnTuple code)
    (hrow :
      (∑ m ∈ (constrainedProfiles n profileDelta).filter
          (fun m ↦ profilePrefix hkTwo hk m =
            coarseConstrainedTailPrefix code),
        paddedPreludeMultiRecursiveProfileContinuation n k y m
          (constrainedPaddedCoarseBridgeSegments
            (pairPrefixScale n k) hn hkTwo hdelta hy code reference)) ≤
        ENNReal.ofReal radialTail *
          paddedConstrainedUnmarkedKernelProduct
            hn hkTwo hdelta hy code reference) :
    (∑' tail : CoarseConstrainedTailReturnTuple code,
        ∏ j, stoppedWordMass (tail.1 j).1.1) ≤
      ENNReal.ofReal radialTail *
        paddedConstrainedUnmarkedKernelProduct
          hn hkTwo hdelta hy code reference := by
  calc
    _ ≤ ∑' key : PaddedConstrainedTailKey
        (p := pairPrefixScale n k) hn hkTwo hdelta hy code reference,
        key.mass :=
      tsum_constrainedBridgeMass_le_paddedConstrainedTailKeyMass
        hn hkTwo hdelta hy hkp hp code reference
    _ = ∑ m ∈ (constrainedProfiles n profileDelta).filter
          (fun m ↦ profilePrefix hkTwo hk m =
            coarseConstrainedTailPrefix code),
        paddedPreludeMultiRecursiveProfileContinuation n k y m
          (constrainedPaddedCoarseBridgeSegments
            (pairPrefixScale n k) hn hkTwo hdelta hy code reference) :=
      tsum_paddedConstrainedTailKeyMass_eq_sum_fixedPrefix_continuation
        hn hkTwo hdelta hy code reference
    _ ≤ _ := hrow

/-- Eventually every inhabited coarse completion has its constrained
high-tail bridge row bounded by the public radial envelope times its exact
normalizing kernel product. -/
theorem eventually_constrainedBridgeMass_le_radialTail_mul_kernel :
    ∀ᶠ q : ℕ in Filter.atTop, ∀ k ≤ decorrelationCutoff q,
      ∀ (hk : k + 1 ≤ q) (hkTwo : 2 ≤ k + 1)
        (hkp : k + 1 < pairPrefixScale q k)
        (htail : profileUpperTailStart ≤ pairPrefixScale q k),
      ∀ {start : ℕ} {x y : Point}
        (code : CoarseSplitCompletionCode start q k hk profileUpperDelta x y
          (profileInnerBoundary q k y)
          (discBoundary (0, 0) (outerScale q)) (0, 0))
        (reference : CoarseConstrainedTailReturnTuple code),
        (∑' tail : CoarseConstrainedTailReturnTuple code,
            ∏ j, stoppedWordMass (tail.1 j).1.1) ≤
          ENNReal.ofReal (Real.exp 1 *
            Real.exp (-(2 * (q - pairPrefixScale q k : ℕ) : ℝ) +
              (profileUpperCoreConstant + 101) *
                (q : ℝ) ^ (3 / 5 : ℝ))) *
            ∏ j, (coarseAtom code).kernel j := by
  filter_upwards
      [eventually_sum_earlierFixedPrefix_paddedPreludeContinuation_le_sharp]
      with q hrow
  intro k hkLevel hk hkTwo hkp htail start x y code reference
  have hn : 2 ≤ q := by omega
  have hdelta : profileUpperDelta ≤ 1 := by
    norm_num [profileUpperDelta]
  obtain ⟨_origin, _hdata, hy, _hexit⟩ := code.2.origin_exists
  let segments := constrainedPaddedCoarseBridgeSegments
    (pairPrefixScale q k) hn hkTwo hdelta hy code reference
  have hpq : pairPrefixScale q k ≤ q := by
    unfold pairPrefixScale
    exact min_le_left _ _
  have hpadded := hrow k hkLevel hkTwo hkp.le hpq htail
    (coarseConstrainedTailPrefix code) y segments
  have hprod :
      (segments.map fun segment :
          ((PaddedNearPoint q k y ⊕
              PaddedMiddlePoint q (pairPrefixScale q k) y) ×
            PaddedOuterPoint q k y) ↦ match segment.1 with
        | Sum.inl initial =>
            paddedNearUnmarkedKernelENNReal q k y initial segment.2
        | Sum.inr u =>
            paddedUnmarkedKernelENNReal q k (pairPrefixScale q k)
              y u segment.2).prod =
        paddedConstrainedUnmarkedKernelProduct
          hn hkTwo hdelta hy code reference := by
    dsimp only [segments]
    convert
      (constrainedPaddedCoarseBridgeSegments_unmarked_prod_eq
        (p := pairPrefixScale q k)
        hn hkTwo hdelta hy code reference)
    rename_i segment
    cases segment.1 <;> rfl
  have hcontinuation :
      (∑ m ∈ (constrainedProfiles q profileUpperDelta).filter
          (fun m ↦ profilePrefix hkTwo hk m =
            coarseConstrainedTailPrefix code),
        paddedPreludeMultiRecursiveProfileContinuation q k y m segments) ≤
        ENNReal.ofReal (Real.exp 1 *
          Real.exp (-(2 * (q - pairPrefixScale q k : ℕ) : ℝ) +
            (profileUpperCoreConstant + 101) *
              (q : ℝ) ^ (3 / 5 : ℝ))) *
          paddedConstrainedUnmarkedKernelProduct
            hn hkTwo hdelta hy code reference := by
    rw [← hprod]
    convert hpadded using 1 <;> simp only [segments] <;> rfl
  have hbridge := tsum_constrainedBridgeMass_le_radialTail_mul_unmarked
    hn hkTwo hdelta hy hkp hpq code reference hcontinuation
  calc
    _ ≤ ENNReal.ofReal (Real.exp 1 *
          Real.exp (-(2 * (q - pairPrefixScale q k : ℕ) : ℝ) +
            (profileUpperCoreConstant + 101) *
              (q : ℝ) ^ (3 / 5 : ℝ))) *
        paddedConstrainedUnmarkedKernelProduct
          hn hkTwo hdelta hy code reference := hbridge
    _ = _ := by
      rw [←
        coarseAtom_kernel_prod_eq_paddedConstrainedUnmarkedKernelProduct
          hn hkTwo hdelta hy code reference]

/-- Reference-free form of the normalized constrained high-tail row. -/
theorem eventually_constrainedBridgeMass_le_radialTail_mul_kernel_all :
    ∀ᶠ q : ℕ in Filter.atTop, ∀ k ≤ decorrelationCutoff q,
      ∀ (hk : k + 1 ≤ q) (hkTwo : 2 ≤ k + 1)
        (hkp : k + 1 < pairPrefixScale q k)
        (htail : profileUpperTailStart ≤ pairPrefixScale q k),
      ∀ {start : ℕ} {x y : Point}
        (code : CoarseSplitCompletionCode start q k hk profileUpperDelta x y
          (profileInnerBoundary q k y)
          (discBoundary (0, 0) (outerScale q)) (0, 0)),
        (∑' tail : CoarseConstrainedTailReturnTuple code,
            ∏ j, stoppedWordMass (tail.1 j).1.1) ≤
          ENNReal.ofReal (Real.exp 1 *
            Real.exp (-(2 * (q - pairPrefixScale q k : ℕ) : ℝ) +
              (profileUpperCoreConstant + 101) *
                (q : ℝ) ^ (3 / 5 : ℝ))) *
            ∏ j, (coarseAtom code).kernel j := by
  filter_upwards
      [eventually_constrainedBridgeMass_le_radialTail_mul_kernel]
      with q hrow
  intro k hkLevel hk hkTwo hkp htail start x y code
  classical
  by_cases h : Nonempty (CoarseConstrainedTailReturnTuple code)
  · exact hrow k hkLevel hk hkTwo hkp htail code (Classical.choice h)
  · have : IsEmpty (CoarseConstrainedTailReturnTuple code) :=
      not_nonempty_iff.mp h
    simp

end

end Erdos1165.AsymmetricPaddedConstrainedTailRow
