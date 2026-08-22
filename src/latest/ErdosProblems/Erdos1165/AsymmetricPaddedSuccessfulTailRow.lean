/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricPaddedBridgeFrontier
import ErdosProblems.Erdos1165.AsymmetricPaddedSuccessfulTailCode
import ErdosProblems.Erdos1165.AsymmetricPaddedRecursiveRenewal
import ErdosProblems.Erdos1165.AsymmetricPaddedPrefixMultiplicity

/-!
# Successful coarse tails in the padded recursive row

The padded bridge parser cuts each canonical successful coarse bridge at the
common padded-prefix scale.  This file identifies the resulting chronological
tree list with the corresponding fixed-depth frontier of the successful
profile's canonical gap chain.  Consequently its literal bridge product is
one summand of the padded recursive continuation row.
-/

open scoped BigOperators ENNReal

namespace Erdos1165.AsymmetricPaddedSuccessfulTailRow

open AnnularLiteralNestedProfileTailUpper AnnularOffspringKernelRadial
open AnnularErasedParentSpineRowPartition
open AnnularProfileLiteralAtoms
open AnnularProfileClocks AnnularRecursiveBoundaryParser
open AnnularRecursiveBoundaryParserActual
open AnnularRecursiveProfileEndpointTail
open AnnularRecursiveDecoratedProfileCode AnnularRecursiveProfileShape
open AnnularRecursiveWeightedRenewal
open AppendixFirstMoment AppendixPairMoment
open AlternatingConcatPrefixFree
open AsymmetricCoarseCompletionCode AsymmetricCoarseRecursiveSourceCode
open AsymmetricCoarseRightProfilePrefix AsymmetricCoarseScanSignature
open AsymmetricCoarseSplitCompletion
open AsymmetricCoarseSuccessfulTailAtoms
open AsymmetricPaddedBridgeCode AsymmetricPaddedBridgeFrontier
open AsymmetricPaddedPrefixMultiplicity
open AsymmetricPaddedParsedBridgeCode AsymmetricPaddedPreludeCode
open AsymmetricPaddedRecursiveFrontier AsymmetricPaddedRecursiveRenewal
open AsymmetricPaddedRemoteRenewal
open AsymmetricPaddedSuccessfulTailCode
open AsymmetricPairTwoStageMass AsymmetricSplitLevelSplice
open MarkedBoundaryVisitKernel MarkedBridgeFactorization
open ProfileGapChain ThickPoint
open ProfileListExponent ProfileWeightUpper
open PlanarPotential TerminalSkeletonInvariance TerminalSkeletonWords

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The tree read at the root of a successful padded bridge is the canonical
tree selected by the successful profile's gap chain. -/
theorem successfulPaddedCoarseBridge_root_tree_eq
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code)
    (j : Fin code.1.returnCount) :
    (parseBoundaryGap n y hn (n - (k + 1)) (k + 1) (by omega) (by omega)
      (successfulPaddedCoarseBridge hn hkTwo hdelta code tail j).start
      (successfulPaddedCoarseBridge hn hkTwo hdelta code tail j).endpoint
      (successfulPaddedCoarseBridge hn hkTwo hdelta code tail j).bridge).tree =
      profileRefinementTrees code.1.returnCount
        (coarseSuccessfulProfileRest code tail)
        (coarseSuccessfulGapChain hn hkTwo hdelta code tail) j := by
  let data := coarseSuccessfulProfileSegmentData hn hkTwo hdelta code tail
  let u := coarseSuccessfulRecursiveEntrance hn hkTwo hdelta code tail j
  let w := coarseSuccessfulRecursiveEndpoint hn hkTwo hdelta code tail j
  let actual := actualBoundaryExitWordCodeAt
    (data.headComplete j j.isLt) u w
    (coarseSuccessfulRecursiveEntrance_val
      hn hkTwo hdelta code tail j).symm
    (coarseSuccessfulRecursiveEndpoint_val
      hn hkTwo hdelta code tail j).symm
  have hsource :
      (successfulPaddedCoarseBridge hn hkTwo hdelta code tail j).bridge =
        actual := by
    apply Subtype.ext
    rw [successfulPaddedCoarseBridge_bridge, actualBoundaryExitWordCodeAt_val]
    exact coarseSuccessfulBridge_eq_profileGapStoppedWord hn code tail j
  have hrestLength :
      (coarseSuccessfulProfileRest code tail).length = n - (k + 1) := by
    have hlength := profileSegmentValues_length
      (coarseSuccessfulProfile code tail) (k + 1)
    rw [coarseSuccessfulProfileSegment_eq hkTwo code tail] at hlength
    simp only [List.length_cons] at hlength
    omega
  change
    (parseBoundaryGap n y hn (n - (k + 1)) (k + 1) (by omega) (by omega)
      u w (successfulPaddedCoarseBridge
        hn hkTwo hdelta code tail j).bridge).tree = _
  rw [hsource]
  have hparsed := parseBoundaryGap_actual_tree hn tail.2.1
    (coarseSuccessfulProfileRest code tail) (by omega)
    (coarseSuccessfulProfileRest_depth hkTwo code tail) data j u w
    (coarseSuccessfulRecursiveEntrance_val
      hn hkTwo hdelta code tail j).symm
    (coarseSuccessfulRecursiveEndpoint_val
      hn hkTwo hdelta code tail j).symm
  simpa only [hrestLength] using hparsed.trans
      (coarseSuccessfulParsedProfileGap_tree_eq
        hn hkTwo hdelta code tail j)

/-- Parsing a list of padded bridges concatenates the parsed tree lists in
the same chronological order. -/
theorem parsedPaddedBridgeDecorationList_trees_eq_flatMap_frontier
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n) :
    ∀ sources : List (PaddedCoarseBridge n l center),
      (parsedPaddedBridgeDecorationList hn hlp hp sources).1 =
        sources.flatMap fun source =>
          profileRefinementTreeFrontier (p - (l + 1))
            (parseBoundaryGap n center hn (n - (l + 1)) (l + 1)
              (by omega) (by omega) source.start source.endpoint
              source.bridge).tree
  | [] => rfl
  | source :: sources => by
      simp only [parsedPaddedBridgeDecorationList, List.flatMap_cons]
      exact congrArg₂ (· ++ ·)
        (parsedPaddedBridgeTrees_eq_frontier hn hlp hp source)
        (parsedPaddedBridgeDecorationList_trees_eq_flatMap_frontier
          hn hlp hp sources)

/-- Dropping the initial scales from a profile segment gives the segment
beginning at the later scale. -/
theorem profileSegmentValues_drop
    {n first later : ℕ} (m : Profile n)
    (hfirst : first ≤ later) (hlater : later ≤ n) :
    (profileSegmentValues m first).drop (later - first) =
      profileSegmentValues m later := by
  apply List.ext_getElem
  · simp only [List.length_drop, profileSegmentValues_length]
    omega
  · intro i hiLeft hiRight
    rw [List.getElem_drop]
    simp only [profileSegmentValues, List.getElem_ofFn]
    congr 1
    omega

/-- A fixed-depth canonical frontier is again the root forest of the suffix
gap chain, transported along any prescribed description of that suffix. -/
theorem exists_gapChain_profileRefinementTreesAtDepth
    {a : ℕ} (rest : List ℕ) (chain : GapChain (a :: rest))
    (depth : ℕ) (hdepth : depth ≤ rest.length)
    {b : ℕ} {targetRest : List ℕ}
    (hdrop : (a :: rest).drop depth = b :: targetRest) :
    ∃ targetChain : GapChain (b :: targetRest),
      profileRefinementTreesAtDepth rest chain depth hdepth =
        List.ofFn fun i : Fin b =>
          profileRefinementTrees b targetRest targetChain i := by
  induction depth generalizing a rest b targetRest with
  | zero =>
      simp only [List.drop_zero] at hdrop
      cases hdrop
      exact ⟨chain, rfl⟩
  | succ depth ih =>
      cases rest with
      | nil => simp at hdepth
      | cons next rest =>
          have hdepth' : depth ≤ rest.length := by
            simpa only [List.length_cons, Nat.succ_le_succ_iff] using hdepth
          have hdrop' : (next :: rest).drop depth = b :: targetRest := by
            simpa only [List.drop_succ_cons] using hdrop
          exact ih rest chain.2 hdepth' hdrop'

/-- The parsed tree list of a successful tuple is the canonical frontier of
its original level-`k+1` gap chain. -/
theorem parsedSuccessfulPaddedBridgeTrees_eq_atDepth
    {start n k p : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hkp : k + 1 < p) (hp : p ≤ n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code) :
    (parsedPaddedBridgeDecorationList hn hkp hp
      (successfulPaddedCoarseBridges hn hkTwo hdelta code tail)).1 =
      profileRefinementTreesAtDepth
        (coarseSuccessfulProfileRest code tail)
        (coarseSuccessfulGapChain hn hkTwo hdelta code tail)
        (p - (k + 1)) (by
          have hlength := profileSegmentValues_length
            (coarseSuccessfulProfile code tail) (k + 1)
          rw [coarseSuccessfulProfileSegment_eq hkTwo code tail] at hlength
          simp only [List.length_cons] at hlength
          omega) := by
  rw [parsedPaddedBridgeDecorationList_trees_eq_flatMap_frontier
    hn hkp hp]
  unfold successfulPaddedCoarseBridges
  calc
    (List.ofFn (successfulPaddedCoarseBridge
        hn hkTwo hdelta code tail)).flatMap
          (fun source => profileRefinementTreeFrontier (p - (k + 1))
            (parseBoundaryGap n y hn (n - (k + 1)) (k + 1)
              (by omega) (by omega) source.start source.endpoint
              source.bridge).tree) =
        (List.ofFn (fun j : Fin code.1.returnCount =>
          profileRefinementTrees code.1.returnCount
            (coarseSuccessfulProfileRest code tail)
            (coarseSuccessfulGapChain hn hkTwo hdelta code tail) j)).flatMap
              (profileRefinementTreeFrontier (p - (k + 1))) := by
        simp only [List.flatMap_def, List.map_ofFn]
        apply congrArg List.flatten
        rw [List.ofFn_inj]
        funext j
        simpa only [Function.comp_apply] using congrArg
          (profileRefinementTreeFrontier (p - (k + 1)))
          (successfulPaddedCoarseBridge_root_tree_eq
            hn hkTwo hdelta code tail j)
    _ = profileRefinementTreesAtDepth
          (coarseSuccessfulProfileRest code tail)
          (coarseSuccessfulGapChain hn hkTwo hdelta code tail)
          (p - (k + 1)) (by
            have hlength := profileSegmentValues_length
              (coarseSuccessfulProfile code tail) (k + 1)
            rw [coarseSuccessfulProfileSegment_eq
              hkTwo code tail] at hlength
            simp only [List.length_cons] at hlength
            omega) :=
      flatMap_profileRefinementTreeFrontier_profileRefinementTrees
        (coarseSuccessfulProfileRest code tail)
        (coarseSuccessfulGapChain hn hkTwo hdelta code tail)
        (p - (k + 1)) (by
          have hlength := profileSegmentValues_length
            (coarseSuccessfulProfile code tail) (k + 1)
          rw [coarseSuccessfulProfileSegment_eq hkTwo code tail] at hlength
          simp only [List.length_cons] at hlength
          omega)

/-- At the padded scale, the parsed successful code has exactly the tree
list indexed by one gap chain of the same full successful profile. -/
theorem exists_paddedGapChain_parsedSuccessfulPaddedBridgeTrees_eq
    {start n k p : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hkp : k + 1 < p) (hp : p ≤ n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code) :
    ∃ chain : GapChain
        (profileAtScale (coarseSuccessfulProfile code tail) p ::
          (profileSegmentValues
            (coarseSuccessfulProfile code tail) p).tail),
      (parsedPaddedBridgeDecorationList hn hkp hp
        (successfulPaddedCoarseBridges hn hkTwo hdelta code tail)).1 =
        List.ofFn fun i : Fin
            (profileAtScale (coarseSuccessfulProfile code tail) p) =>
          profileRefinementTrees
            (profileAtScale (coarseSuccessfulProfile code tail) p)
            (profileSegmentValues
              (coarseSuccessfulProfile code tail) p).tail chain i := by
  let m := coarseSuccessfulProfile code tail
  let depth := p - (k + 1)
  have hdepth : depth ≤ (coarseSuccessfulProfileRest code tail).length := by
    have hlength := profileSegmentValues_length m (k + 1)
    rw [coarseSuccessfulProfileSegment_eq hkTwo code tail] at hlength
    simp only [List.length_cons] at hlength
    omega
  have hdrop :
      (code.1.returnCount :: coarseSuccessfulProfileRest code tail).drop depth =
        profileAtScale m p :: (profileSegmentValues m p).tail := by
    calc
      (code.1.returnCount :: coarseSuccessfulProfileRest code tail).drop depth =
          (profileSegmentValues m (k + 1)).drop depth := by
            rw [coarseSuccessfulProfileSegment_eq hkTwo code tail]
      _ = profileSegmentValues m p := by
            exact profileSegmentValues_drop m (by omega) hp
      _ = profileAtScale m p :: (profileSegmentValues m p).tail :=
            profileSegmentValues_eq_head_cons_tail hp m
  obtain ⟨chain, htrees⟩ :=
    exists_gapChain_profileRefinementTreesAtDepth
      (coarseSuccessfulProfileRest code tail)
      (coarseSuccessfulGapChain hn hkTwo hdelta code tail)
      depth hdepth hdrop
  refine ⟨chain, ?_⟩
  exact (parsedSuccessfulPaddedBridgeTrees_eq_atDepth
    hn hkTwo hdelta hkp hp code tail).trans htrees

/-- Segment endpoints of the successful padded bridges, kept opaque to avoid
re-elaborating the complete source bridge construction at every use. -/
def successfulPaddedCoarseBridgeSegments
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (p : ℕ) (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code) :
    List ((PaddedNearPoint n k y ⊕ PaddedMiddlePoint n p y) ×
      PaddedOuterPoint n k y) :=
  paddedCoarseBridgeSegments n k p y
    (successfulPaddedCoarseBridges hn hkTwo hdelta code tail)

theorem paddedCoarseBridgeSegments_eq_map
    (n l p : ℕ) (center : Point) :
    ∀ sources : List (PaddedCoarseBridge n l center),
      paddedCoarseBridgeSegments n l p center sources =
        sources.map fun source => (Sum.inl source.start, source.endpoint)
  | [] => rfl
  | source :: sources => by
      simp only [paddedCoarseBridgeSegments, List.map_cons,
        paddedCoarseBridgeSegments_eq_map n l p center sources]

/-- Segment endpoints depend only on the retained coarse skeleton, not on
the successful continuation chosen over it. -/
theorem successfulPaddedCoarseBridgeSegments_eq
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (p : ℕ) (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (left right : CoarseSuccessfulReturnTuple code) :
    successfulPaddedCoarseBridgeSegments
        p hn hkTwo hdelta code left =
      successfulPaddedCoarseBridgeSegments
        p hn hkTwo hdelta code right := by
  unfold successfulPaddedCoarseBridgeSegments
  rw [paddedCoarseBridgeSegments_eq_map,
    paddedCoarseBridgeSegments_eq_map]
  unfold successfulPaddedCoarseBridges
  simp only [List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  apply Prod.ext
  · apply congrArg Sum.inl
    apply Subtype.ext
    exact (coarseSuccessfulRecursiveEntrance_eq_skeleton
      hn hkTwo hdelta code left j).trans
        (coarseSuccessfulRecursiveEntrance_eq_skeleton
          hn hkTwo hdelta code right j).symm
  · apply Subtype.ext
    exact (coarseSuccessfulRecursiveEndpoint_eq_skeleton
      hn hkTwo hdelta code left j).trans
        (coarseSuccessfulRecursiveEndpoint_eq_skeleton
          hn hkTwo hdelta code right j).symm

/-- There is one padded segment for each retained return coordinate. -/
theorem successfulPaddedCoarseBridgeSegments_length
    {start n k p : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code) :
    (successfulPaddedCoarseBridgeSegments
      p hn hkTwo hdelta code tail).length = code.1.returnCount := by
  unfold successfulPaddedCoarseBridgeSegments
  rw [paddedCoarseBridgeSegments_eq_map]
  simp [successfulPaddedCoarseBridges]

/-- Transport a literal padded code along equalities of its two list
indices. -/
def transportPaddedPreludeMultiCode
    {n l p : ℕ} {center : Point}
    {leftSegments rightSegments : List
      ((PaddedNearPoint n l center ⊕ PaddedMiddlePoint n p center) ×
        PaddedOuterPoint n l center)}
    {leftTrees rightTrees : List ProfileRefinementTree}
    (hsegments : leftSegments = rightSegments)
    (htrees : leftTrees = rightTrees)
    (value : PaddedPreludeMultiCode n l p center leftSegments leftTrees) :
    PaddedPreludeMultiCode n l p center rightSegments rightTrees := by
  subst rightSegments
  subst rightTrees
  exact value

@[simp] theorem paddedPreludeMultiCodeWords_transport
    {n l p : ℕ} {center : Point}
    {leftSegments rightSegments : List
      ((PaddedNearPoint n l center ⊕ PaddedMiddlePoint n p center) ×
        PaddedOuterPoint n l center)}
    {leftTrees rightTrees : List ProfileRefinementTree}
    (hsegments : leftSegments = rightSegments)
    (htrees : leftTrees = rightTrees)
    (value : PaddedPreludeMultiCode n l p center leftSegments leftTrees) :
    paddedPreludeMultiCodeWords n l p center
        (transportPaddedPreludeMultiCode hsegments htrees value) =
      paddedPreludeMultiCodeWords n l p center value := by
  subst rightSegments
  subst rightTrees
  rfl

@[simp] theorem paddedPreludeMultiCodeMass_transport
    {n l p : ℕ} {center : Point}
    {leftSegments rightSegments : List
      ((PaddedNearPoint n l center ⊕ PaddedMiddlePoint n p center) ×
        PaddedOuterPoint n l center)}
    {leftTrees rightTrees : List ProfileRefinementTree}
    (hsegments : leftSegments = rightSegments)
    (htrees : leftTrees = rightTrees)
    (value : PaddedPreludeMultiCode n l p center leftSegments leftTrees) :
    paddedPreludeMultiCodeMass n l p center
        (transportPaddedPreludeMultiCode hsegments htrees value) =
      paddedPreludeMultiCodeMass n l p center value := by
  subst rightSegments
  subst rightTrees
  rfl

/-- Canonical padded-scale chain selected from the successful source
parser. -/
noncomputable def successfulPaddedGapChain
    {start n k p : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hkp : k + 1 < p) (hp : p ≤ n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code) :
    GapChain (profileAtScale (coarseSuccessfulProfile code tail) p ::
      (profileSegmentValues (coarseSuccessfulProfile code tail) p).tail) :=
  Classical.choose
    (exists_paddedGapChain_parsedSuccessfulPaddedBridgeTrees_eq
      hn hkTwo hdelta hkp hp code tail)

theorem parsedSuccessfulPaddedBridgeTrees_eq_successfulPaddedGapChain
    {start n k p : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hkp : k + 1 < p) (hp : p ≤ n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code) :
    (parsedPaddedBridgeDecorationList hn hkp hp
      (successfulPaddedCoarseBridges hn hkTwo hdelta code tail)).1 =
      List.ofFn fun i : Fin
          (profileAtScale (coarseSuccessfulProfile code tail) p) =>
        profileRefinementTrees
          (profileAtScale (coarseSuccessfulProfile code tail) p)
          (profileSegmentValues
            (coarseSuccessfulProfile code tail) p).tail
          (successfulPaddedGapChain
            hn hkTwo hdelta hkp hp code tail) i :=
  Classical.choose_spec
    (exists_paddedGapChain_parsedSuccessfulPaddedBridgeTrees_eq
      hn hkTwo hdelta hkp hp code tail)

/-- Ambient padded key used to reindex successful tails without duplicating
their literal code mass. -/
def PaddedSuccessfulTailKey
    {start n k p : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (reference : CoarseSuccessfulReturnTuple code) :=
  Σ profile : {m : Profile n //
      IsConstrainedProfile profileDelta m ∧
        profilePrefix hkTwo hk m =
          retainedYProfilePrefix hn hkTwo hdelta code},
    Σ chain : GapChain
        (profileAtScale profile.1 p ::
          (profileSegmentValues profile.1 p).tail),
      PaddedPreludeMultiCode n k p y
        (successfulPaddedCoarseBridgeSegments
          p hn hkTwo hdelta code reference)
        (List.ofFn fun i : Fin (profileAtScale profile.1 p) =>
          profileRefinementTrees (profileAtScale profile.1 p)
            (profileSegmentValues profile.1 p).tail chain i)

/-- The bridge-word tuple carried by a padded key.  The segment list has
exactly the retained coarse arity, so no padding coordinate is invented. -/
def PaddedSuccessfulTailKey.words
    {start n k p : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (reference : CoarseSuccessfulReturnTuple code)
    (key : PaddedSuccessfulTailKey
      (p := p) hn hkTwo hdelta code reference) :
    TerminalSkeletonWords.TerminalSegmentWords
      code.1.returnCount :=
  let wordList := paddedPreludeMultiCodeWords n k p y key.2.2
  let hlength : wordList.length = code.1.returnCount :=
    (paddedPreludeMultiCodeWords_length n k p y key.2.2).trans
      (successfulPaddedCoarseBridgeSegments_length
        hn hkTwo hdelta code reference)
  fun j ↦ wordList.get (Fin.cast hlength.symm j)

/-- Re-listing the word tuple of a padded key recovers its literal code
words exactly. -/
theorem PaddedSuccessfulTailKey.ofFn_words
    {start n k p : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (reference : CoarseSuccessfulReturnTuple code)
    (key : PaddedSuccessfulTailKey
      (p := p) hn hkTwo hdelta code reference) :
    List.ofFn (key.words hn hkTwo hdelta code reference) =
      paddedPreludeMultiCodeWords n k p y key.2.2 := by
  let wordList := paddedPreludeMultiCodeWords n k p y key.2.2
  let hlength : wordList.length = code.1.returnCount :=
    (paddedPreludeMultiCodeWords_length n k p y key.2.2).trans
      (successfulPaddedCoarseBridgeSegments_length
        hn hkTwo hdelta code reference)
  change List.ofFn (fun j ↦ wordList.get (Fin.cast hlength.symm j)) = wordList
  have hrecover : ∀ (m : ℕ) (h : wordList.length = m),
      List.ofFn (fun j : Fin m ↦ wordList.get (Fin.cast h.symm j)) =
        wordList := by
    intro m h
    subst m
    exact List.ofFn_get wordList
  exact hrecover code.1.returnCount hlength

/-- The full right-hand excursion profile reconstructed from the literal
bridge words stored in a padded key and the retained coarse skeleton. -/
def PaddedSuccessfulTailKey.reconstructedProfile
    {start n k p : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (reference : CoarseSuccessfulReturnTuple code)
    (key : PaddedSuccessfulTailKey
      (p := p) hn hkTwo hdelta code reference) : Profile n :=
  internalProfile (excursionProfile
    (trajectory (assembledTerminalPath code.1.skeleton
      (key.words hn hkTwo hdelta code reference))) n
    (assembledTerminalHorizon code.1.skeleton
      (key.words hn hkTwo hdelta code reference)) y)

/-- A successful tail mapped into the proof-free padded ambient key. -/
noncomputable def paddedKeyOfSuccessfulTail
    {start n k p : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hkp : k + 1 < p) (hp : p ≤ n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (reference tail : CoarseSuccessfulReturnTuple code) :
    PaddedSuccessfulTailKey (p := p) hn hkTwo hdelta code reference :=
  ⟨⟨coarseSuccessfulProfile code tail,
      internalProfile_isConstrained tail.2.2,
      profilePrefix_coarseSuccessfulProfile_eq_retained
        hn hkTwo hdelta code tail⟩,
    successfulPaddedGapChain hn hkTwo hdelta hkp hp code tail,
    transportPaddedPreludeMultiCode
      (successfulPaddedCoarseBridgeSegments_eq
        p hn hkTwo hdelta code tail reference)
      (parsedSuccessfulPaddedBridgeTrees_eq_successfulPaddedGapChain
        hn hkTwo hdelta hkp hp code tail)
      (parsedPaddedBridgeCode hn hkp hp
        (successfulPaddedCoarseBridges hn hkTwo hdelta code tail))⟩

/-- Literal mass of an ambient padded key. -/
def PaddedSuccessfulTailKey.mass
    {start n k p : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} {hn : 2 ≤ n} {hkTwo : 2 ≤ k + 1}
    {hdelta : profileDelta ≤ 1}
    {code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0)}
    {reference : CoarseSuccessfulReturnTuple code}
    (key : PaddedSuccessfulTailKey
      (p := p) hn hkTwo hdelta code reference) : ℝ≥0∞ :=
  paddedPreludeMultiCodeMass n k p y key.2.2

theorem mass_paddedKeyOfSuccessfulTail
    {start n k p : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hkp : k + 1 < p) (hp : p ≤ n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (reference tail : CoarseSuccessfulReturnTuple code) :
    (paddedKeyOfSuccessfulTail
      hn hkTwo hdelta hkp hp code reference tail).mass =
      ∏ j, stoppedWordMass (tail.1 j).1.1 := by
  let hsegments := successfulPaddedCoarseBridgeSegments_eq
    p hn hkTwo hdelta code tail reference
  change paddedCoarseBridgeSegments n k p y
      (successfulPaddedCoarseBridges hn hkTwo hdelta code tail) =
    paddedCoarseBridgeSegments n k p y
      (successfulPaddedCoarseBridges hn hkTwo hdelta code reference)
    at hsegments
  let htrees :=
    parsedSuccessfulPaddedBridgeTrees_eq_successfulPaddedGapChain
      hn hkTwo hdelta hkp hp code tail
  change paddedPreludeMultiCodeMass n k p y
      (transportPaddedPreludeMultiCode
        hsegments htrees
        (parsedPaddedBridgeCode hn hkp hp
          (successfulPaddedCoarseBridges
            hn hkTwo hdelta code tail))) = _
  rw [paddedPreludeMultiCodeMass_transport]
  exact parsedSuccessfulPaddedBridgeCode_mass
    hn hkTwo hdelta hkp hp code tail

theorem paddedCoarseBridgeWords_eq_map
    {n l : ℕ} {center : Point} :
    ∀ sources : List (PaddedCoarseBridge n l center),
      paddedCoarseBridgeWords sources =
        sources.map fun source => List.ofFn source.bridge.1.2
  | [] => rfl
  | source :: sources => by
      simp only [paddedCoarseBridgeWords, List.map_cons,
        paddedCoarseBridgeWords_eq_map sources]

theorem paddedCoarseBridgeWords_successful
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code) :
    paddedCoarseBridgeWords
        (successfulPaddedCoarseBridges hn hkTwo hdelta code tail) =
      List.ofFn fun j : Fin code.1.returnCount =>
        List.ofFn (tail.1 j).1.1.2 := by
  rw [paddedCoarseBridgeWords_eq_map]
  unfold successfulPaddedCoarseBridges
  simp only [List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  exact congrArg (fun word : StoppedWord => List.ofFn word.2)
    (successfulPaddedCoarseBridge_bridge
      hn hkTwo hdelta code tail j)

theorem paddedKeyOfSuccessfulTail_words
    {start n k p : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hkp : k + 1 < p) (hp : p ≤ n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (reference tail : CoarseSuccessfulReturnTuple code) :
    paddedPreludeMultiCodeWords n k p y
        (paddedKeyOfSuccessfulTail
          hn hkTwo hdelta hkp hp code reference tail).2.2 =
      List.ofFn fun j : Fin code.1.returnCount =>
        List.ofFn (tail.1 j).1.1.2 := by
  let hsegments := successfulPaddedCoarseBridgeSegments_eq
    p hn hkTwo hdelta code tail reference
  change paddedCoarseBridgeSegments n k p y
      (successfulPaddedCoarseBridges hn hkTwo hdelta code tail) =
    paddedCoarseBridgeSegments n k p y
      (successfulPaddedCoarseBridges hn hkTwo hdelta code reference)
    at hsegments
  let htrees :=
    parsedSuccessfulPaddedBridgeTrees_eq_successfulPaddedGapChain
      hn hkTwo hdelta hkp hp code tail
  change paddedPreludeMultiCodeWords n k p y
      (transportPaddedPreludeMultiCode
        hsegments htrees
        (parsedPaddedBridgeCode hn hkp hp
          (successfulPaddedCoarseBridges
            hn hkTwo hdelta code tail))) = _
  rw [paddedPreludeMultiCodeWords_transport,
    parsedPaddedBridgeCode_words]
  exact paddedCoarseBridgeWords_successful
    hn hkTwo hdelta code tail

/-- Reconstructing the profile from a source tail's padded key returns the
source tail's actual successful profile. -/
theorem reconstructedProfile_paddedKeyOfSuccessfulTail
    {start n k p : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hkp : k + 1 < p) (hp : p ≤ n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (reference tail : CoarseSuccessfulReturnTuple code) :
    (paddedKeyOfSuccessfulTail
      hn hkTwo hdelta hkp hp code reference tail).reconstructedProfile
        hn hkTwo hdelta code reference =
      coarseSuccessfulProfile code tail := by
  let key := paddedKeyOfSuccessfulTail
    hn hkTwo hdelta hkp hp code reference tail
  have hlists :
      List.ofFn (key.words hn hkTwo hdelta code reference) =
        List.ofFn (coarseTupleWords code tail.1) := by
    calc
      List.ofFn (key.words hn hkTwo hdelta code reference) =
          paddedPreludeMultiCodeWords n k p y key.2.2 :=
        key.ofFn_words hn hkTwo hdelta code reference
      _ = List.ofFn fun j : Fin code.1.returnCount ↦
          List.ofFn (tail.1 j).1.1.2 :=
        paddedKeyOfSuccessfulTail_words
          hn hkTwo hdelta hkp hp code reference tail
      _ = List.ofFn (coarseTupleWords code tail.1) := by
        rfl
  have hwords :
      key.words hn hkTwo hdelta code reference =
        coarseTupleWords code tail.1 :=
    List.ofFn_injective hlists
  change internalProfile (excursionProfile
      (trajectory (assembledTerminalPath code.1.skeleton
        (key.words hn hkTwo hdelta code reference))) n
      (assembledTerminalHorizon code.1.skeleton
        (key.words hn hkTwo hdelta code reference)) y) = _
  rw [hwords]
  rfl

/-- Padded keys whose declared profile is the profile genuinely reconstructed
from their own bridge words.  Restricting to this fibre prevents an arbitrary
profile prefix from being paired with the same literal bridge code. -/
def CompatiblePaddedSuccessfulTailKey
    {start n k p : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (reference : CoarseSuccessfulReturnTuple code) :=
  {key : PaddedSuccessfulTailKey
      (p := p) hn hkTwo hdelta code reference //
    key.1.1 = key.reconstructedProfile hn hkTwo hdelta code reference}

/-- Every actual successful tail gives a compatible padded key. -/
noncomputable def compatiblePaddedKeyOfSuccessfulTail
    {start n k p : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hkp : k + 1 < p) (hp : p ≤ n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (reference tail : CoarseSuccessfulReturnTuple code) :
    CompatiblePaddedSuccessfulTailKey
      (p := p) hn hkTwo hdelta code reference :=
  ⟨paddedKeyOfSuccessfulTail
      hn hkTwo hdelta hkp hp code reference tail,
    (reconstructedProfile_paddedKeyOfSuccessfulTail
      hn hkTwo hdelta hkp hp code reference tail).symm⟩

/-- The literal padded key remembers every source bridge word, hence no two
successful tails are identified by the reindexing map. -/
theorem paddedKeyOfSuccessfulTail_injective
    {start n k p : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hkp : k + 1 < p) (hp : p ≤ n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (reference : CoarseSuccessfulReturnTuple code) :
    Function.Injective
      (paddedKeyOfSuccessfulTail
        hn hkTwo hdelta hkp hp code reference) := by
  intro left right hkey
  have hwords := congrArg
    (fun key : PaddedSuccessfulTailKey
        (p := p) hn hkTwo hdelta code reference =>
      paddedPreludeMultiCodeWords n k p y key.2.2) hkey
  rw [paddedKeyOfSuccessfulTail_words
      hn hkTwo hdelta hkp hp code reference left,
    paddedKeyOfSuccessfulTail_words
      hn hkTwo hdelta hkp hp code reference right] at hwords
  have hfunctions := List.ofFn_injective hwords
  apply Subtype.ext
  funext j
  apply Subtype.ext
  apply Subtype.ext
  let leftWord : StoppedWord := (left.1 j).1.1
  let rightWord : StoppedWord := (right.1 j).1.1
  have hj : List.ofFn leftWord.2 = List.ofFn rightWord.2 := by
    exact congrFun hfunctions j
  exact calc
    leftWord = listStoppedWord (List.ofFn leftWord.2) :=
      (listStoppedWord_ofFn leftWord).symm
    _ = listStoppedWord (List.ofFn rightWord.2) :=
      congrArg listStoppedWord hj
    _ = rightWord := listStoppedWord_ofFn rightWord

theorem compatiblePaddedKeyOfSuccessfulTail_injective
    {start n k p : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hkp : k + 1 < p) (hp : p ≤ n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (reference : CoarseSuccessfulReturnTuple code) :
    Function.Injective
      (compatiblePaddedKeyOfSuccessfulTail
        hn hkTwo hdelta hkp hp code reference) := by
  intro left right hkey
  apply paddedKeyOfSuccessfulTail_injective
    hn hkTwo hdelta hkp hp code reference
  exact congrArg Subtype.val hkey

/-- Reindexing by the literal padded key loses no successful bridge mass. -/
theorem tsum_successfulBridgeMass_le_paddedSuccessfulTailKeyMass
    {start n k p : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hkp : k + 1 < p) (hp : p ≤ n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (reference : CoarseSuccessfulReturnTuple code) :
    (∑' tail : CoarseSuccessfulReturnTuple code,
        ∏ j, stoppedWordMass (tail.1 j).1.1) ≤
      ∑' key : PaddedSuccessfulTailKey
        (p := p) hn hkTwo hdelta code reference,
        key.mass := by
  calc
    (∑' tail : CoarseSuccessfulReturnTuple code,
        ∏ j, stoppedWordMass (tail.1 j).1.1) =
      ∑' tail : CoarseSuccessfulReturnTuple code,
        (paddedKeyOfSuccessfulTail
          hn hkTwo hdelta hkp hp code reference tail).mass := by
            apply tsum_congr
            intro tail
            exact (mass_paddedKeyOfSuccessfulTail
              hn hkTwo hdelta hkp hp code reference tail).symm
    _ ≤ ∑' key : PaddedSuccessfulTailKey
        (p := p) hn hkTwo hdelta code reference,
        key.mass :=
      ENNReal.tsum_comp_le_tsum_of_injective
        (paddedKeyOfSuccessfulTail_injective
          hn hkTwo hdelta hkp hp code reference) _

/-- Reindexing can be restricted to keys whose own words reconstruct their
declared profile, so no spurious profile copy is charged. -/
theorem tsum_successfulBridgeMass_le_compatiblePaddedSuccessfulTailKeyMass
    {start n k p : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1) (hkp : k + 1 < p) (hp : p ≤ n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (reference : CoarseSuccessfulReturnTuple code) :
    (∑' tail : CoarseSuccessfulReturnTuple code,
        ∏ j, stoppedWordMass (tail.1 j).1.1) ≤
      ∑' key : CompatiblePaddedSuccessfulTailKey
        (p := p) hn hkTwo hdelta code reference,
        key.1.mass := by
  calc
    (∑' tail : CoarseSuccessfulReturnTuple code,
        ∏ j, stoppedWordMass (tail.1 j).1.1) =
      ∑' tail : CoarseSuccessfulReturnTuple code,
        (compatiblePaddedKeyOfSuccessfulTail
          hn hkTwo hdelta hkp hp code reference tail).1.mass := by
            apply tsum_congr
            intro tail
            exact (mass_paddedKeyOfSuccessfulTail
              hn hkTwo hdelta hkp hp code reference tail).symm
    _ ≤ ∑' key : CompatiblePaddedSuccessfulTailKey
        (p := p) hn hkTwo hdelta code reference,
        key.1.mass :=
      ENNReal.tsum_comp_le_tsum_of_injective
        (compatiblePaddedKeyOfSuccessfulTail_injective
          hn hkTwo hdelta hkp hp code reference) _

/-- Tonelli expansion of all ambient padded keys over one retained profile
prefix.  The inner literal-code sum is exactly the padded recursive renewal
row, and the outer subtype is exactly the finite constrained-profile filter.
This is the weighted regrouping which avoids charging an intermediate
profile prefix uniformly. -/
theorem tsum_paddedSuccessfulTailKeyMass_eq_sum_fixedPrefix_continuation
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (reference : CoarseSuccessfulReturnTuple code) :
    let segments : List
        ((PaddedNearPoint n k y ⊕
            PaddedMiddlePoint n (pairPrefixScale n k) y) ×
          PaddedOuterPoint n k y) :=
      successfulPaddedCoarseBridgeSegments
        (pairPrefixScale n k) hn hkTwo hdelta code reference
    (∑' key : PaddedSuccessfulTailKey
        (p := pairPrefixScale n k) hn hkTwo hdelta code reference,
        key.mass) =
      ∑ m ∈ (constrainedProfiles n profileDelta).filter
          (fun m ↦ profilePrefix hkTwo hk m =
            retainedYProfilePrefix hn hkTwo hdelta code),
        paddedPreludeMultiRecursiveProfileContinuation n k y m segments := by
  dsimp only
  let P := {m : Profile n //
    IsConstrainedProfile profileDelta m ∧
      profilePrefix hkTwo hk m =
        retainedYProfilePrefix hn hkTwo hdelta code}
  let F := (constrainedProfiles n profileDelta).filter
    (fun m ↦ profilePrefix hkTwo hk m =
      retainedYProfilePrefix hn hkTwo hdelta code)
  let e : {m : Profile n // m ∈ F} ≃ P :=
    { toFun := fun m ↦ ⟨m.1,
        mem_constrainedProfiles.mp (Finset.mem_filter.mp m.2).1,
        (Finset.mem_filter.mp m.2).2⟩
      invFun := fun m ↦ ⟨m.1, Finset.mem_filter.mpr
        ⟨mem_constrainedProfiles.mpr m.2.1, m.2.2⟩⟩
      left_inv := by intro m; apply Subtype.ext; rfl
      right_inv := by intro m; apply Subtype.ext; rfl }
  let segments := successfulPaddedCoarseBridgeSegments
    (pairPrefixScale n k) hn hkTwo hdelta code reference
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
  simp only [PaddedSuccessfulTailKey.mass, PaddedSuccessfulTailKey]
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

/-- The literal successful bridge product is one code summand of the
profile's padded recursive continuation. -/
theorem successfulBridgeProduct_le_paddedPreludeMultiRecursiveProfileContinuation
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (hkp : k + 1 < pairPrefixScale n k)
    (hp : pairPrefixScale n k ≤ n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (tail : CoarseSuccessfulReturnTuple code) :
    (∏ j, stoppedWordMass (tail.1 j).1.1) ≤
      paddedPreludeMultiRecursiveProfileContinuation n k y
        (coarseSuccessfulProfile code tail)
        (successfulPaddedCoarseBridgeSegments
          (pairPrefixScale n k) hn hkTwo hdelta code tail) := by
  let p := pairPrefixScale n k
  let sources := successfulPaddedCoarseBridges
    hn hkTwo hdelta code tail
  let segments := successfulPaddedCoarseBridgeSegments
    p hn hkTwo hdelta code tail
  let trees := (parsedPaddedBridgeDecorationList hn hkp hp sources).1
  let literal := parsedPaddedBridgeCode hn hkp hp sources
  obtain ⟨chain, htrees⟩ :=
    exists_paddedGapChain_parsedSuccessfulPaddedBridgeTrees_eq
      hn hkTwo hdelta hkp hp code tail
  calc
    (∏ j, stoppedWordMass (tail.1 j).1.1) =
        paddedPreludeMultiCodeMass n k p y literal := by
          symm
          exact parsedSuccessfulPaddedBridgeCode_mass
            hn hkTwo hdelta hkp hp code tail
    _ ≤ ∑' value : PaddedPreludeMultiCode n k p y segments trees,
          paddedPreludeMultiCodeMass n k p y value := by
            exact ENNReal.le_tsum literal
    _ = heterogeneousPreludeMultiRenewalKernel
          (paddedPreludeEntryKernelENNReal n k p y)
          (paddedPreludeDirectKernelENNReal n k p y)
          (paddedInwardKernelENNReal n k p y)
          (recursiveProfileGapKernelENNReal n p y)
          (paddedEscapeKernelENNReal n k p y) segments trees := by
            exact tsum_paddedPreludeMultiCodeMass_eq n k p y segments trees
    _ = heterogeneousPreludeMultiRenewalKernel
          (paddedPreludeEntryKernelENNReal n k p y)
          (paddedPreludeDirectKernelENNReal n k p y)
          (paddedInwardKernelENNReal n k p y)
          (recursiveProfileGapKernelENNReal n p y)
          (paddedEscapeKernelENNReal n k p y) segments
          (List.ofFn fun i : Fin
              (profileAtScale (coarseSuccessfulProfile code tail) p) =>
            profileRefinementTrees
              (profileAtScale (coarseSuccessfulProfile code tail) p)
              (profileSegmentValues
                (coarseSuccessfulProfile code tail) p).tail chain i) := by
            rw [← htrees]
    _ ≤ ∑' selected : GapChain
          (profileAtScale (coarseSuccessfulProfile code tail) p ::
            (profileSegmentValues
              (coarseSuccessfulProfile code tail) p).tail),
          heterogeneousPreludeMultiRenewalKernel
            (paddedPreludeEntryKernelENNReal n k p y)
            (paddedPreludeDirectKernelENNReal n k p y)
            (paddedInwardKernelENNReal n k p y)
            (recursiveProfileGapKernelENNReal n p y)
            (paddedEscapeKernelENNReal n k p y) segments
            (List.ofFn fun i : Fin
                (profileAtScale (coarseSuccessfulProfile code tail) p) =>
              profileRefinementTrees
                (profileAtScale (coarseSuccessfulProfile code tail) p)
                (profileSegmentValues
                  (coarseSuccessfulProfile code tail) p).tail selected i) := by
            exact ENNReal.le_tsum chain
    _ = paddedPreludeMultiRecursiveProfileContinuation n k y
          (coarseSuccessfulProfile code tail) segments := by
            rw [tsum_fintype]
            simp only [p, paddedPreludeMultiRecursiveProfileContinuation]

/-- Once both artificial scanner records have been erased, every canonical
first-return word is a coarse-compatible return code.  A successful tuple is
used only to identify the stored (necessarily constant) record. -/
def coarseSignatureReturnCodeEquiv_of_successfulReference
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point}
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (reference : CoarseSuccessfulReturnTuple code)
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

/-- The kernel of an inhabited coarse atom is the full unmarked first-exit
kernel at its retained endpoint data. -/
theorem coarseAtom_kernel_eq_unmarked_of_successfulReference
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point}
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (reference : CoarseSuccessfulReturnTuple code)
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
              ((coarseSignatureReturnCodeEquiv_of_successfulReference
                code reference j).tsum_eq
                (fun b : CoarseSignatureReturnCode x y
                  (profileInnerBoundary n k y) code.1 j ↦
                    stoppedWordMass b.1.1)).symm
    _ = _ := tsum_stoppedWordMass_boundaryExitWordCode _ _ _

/-- The original unmarked bridge-product exposed after the padded recursive
continuation has been summed.  Its endpoints depend only on the retained
coarse skeleton, so any one successful reference tuple may be used. -/
def paddedSuccessfulUnmarkedKernelProduct
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (reference : CoarseSuccessfulReturnTuple code) : ℝ≥0∞ :=
  ∏ j, paddedNearUnmarkedKernelENNReal n k y
    (coarseSuccessfulRecursiveEntrance hn hkTwo hdelta code reference j)
    (coarseSuccessfulRecursiveEndpoint hn hkTwo hdelta code reference j)

/-- The normalization denominator of an inhabited coarse atom is exactly
the unmarked product exposed by padded renewal. -/
theorem coarseAtom_kernel_prod_eq_paddedSuccessfulUnmarkedKernelProduct
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (reference : CoarseSuccessfulReturnTuple code) :
    (∏ j, (coarseAtom code).kernel j) =
      paddedSuccessfulUnmarkedKernelProduct
        hn hkTwo hdelta code reference := by
  unfold paddedSuccessfulUnmarkedKernelProduct
  apply Finset.prod_congr rfl
  intro j _hj
  rw [coarseAtom_kernel_eq_unmarked_of_successfulReference code reference j]
  unfold paddedNearUnmarkedKernelENNReal
  rw [coarseSuccessfulRecursiveEntrance_eq_skeleton
      hn hkTwo hdelta code reference j,
    coarseSuccessfulRecursiveEndpoint_eq_skeleton
      hn hkTwo hdelta code reference j]

/-- The product of unmarked kernels appearing in the padded multi-renewal
row is exactly the coordinate product attached to the retained coarse
skeleton. -/
theorem successfulPaddedCoarseBridgeSegments_unmarked_prod_eq
    {start n k p : ℕ} {hk : k + 1 ≤ n} {profileDelta : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (reference : CoarseSuccessfulReturnTuple code) :
    ((successfulPaddedCoarseBridgeSegments
        p hn hkTwo hdelta code reference).map
      fun segment ↦ match segment.1 with
        | Sum.inl initial =>
            paddedNearUnmarkedKernelENNReal n k y initial segment.2
        | Sum.inr u =>
            paddedUnmarkedKernelENNReal n k p y u segment.2).prod =
      paddedSuccessfulUnmarkedKernelProduct
        hn hkTwo hdelta code reference := by
  unfold successfulPaddedCoarseBridgeSegments
  rw [paddedCoarseBridgeSegments_eq_map]
  unfold successfulPaddedCoarseBridges
    paddedSuccessfulUnmarkedKernelProduct
  simp only [List.map_map, List.map_ofFn, Function.comp_apply,
    List.prod_ofFn]
  rfl

/-- If the checked padded fixed-prefix continuation row has its radial-tail
bound, the literal successful coarse bridges inherit precisely that bound,
with the original unmarked coarse bridge product left visible. -/
theorem tsum_successfulBridgeMass_le_radialTail_mul_unmarked
    {start n k : ℕ} {hk : k + 1 ≤ n} {profileDelta radialTail : ℝ}
    {x y : Point} (hn : 2 ≤ n) (hkTwo : 2 ≤ k + 1)
    (hdelta : profileDelta ≤ 1)
    (hkp : k + 1 < pairPrefixScale n k)
    (hp : pairPrefixScale n k ≤ n)
    (code : CoarseSplitCompletionCode start n k hk profileDelta x y
      (profileInnerBoundary n k y)
      (discBoundary (0, 0) (outerScale n)) (0, 0))
    (reference : CoarseSuccessfulReturnTuple code)
    (hrow :
      (∑ m ∈ (constrainedProfiles n profileDelta).filter
          (fun m ↦ profilePrefix hkTwo hk m =
            retainedYProfilePrefix hn hkTwo hdelta code),
        paddedPreludeMultiRecursiveProfileContinuation n k y m
          (successfulPaddedCoarseBridgeSegments
            (pairPrefixScale n k) hn hkTwo hdelta code reference)) ≤
        ENNReal.ofReal radialTail *
          paddedSuccessfulUnmarkedKernelProduct
            hn hkTwo hdelta code reference) :
    (∑' tail : CoarseSuccessfulReturnTuple code,
        ∏ j, stoppedWordMass (tail.1 j).1.1) ≤
      ENNReal.ofReal radialTail *
        paddedSuccessfulUnmarkedKernelProduct
          hn hkTwo hdelta code reference := by
  calc
    _ ≤ ∑' key : PaddedSuccessfulTailKey
        (p := pairPrefixScale n k) hn hkTwo hdelta code reference,
        key.mass :=
      tsum_successfulBridgeMass_le_paddedSuccessfulTailKeyMass
        hn hkTwo hdelta hkp hp code reference
    _ = ∑ m ∈ (constrainedProfiles n profileDelta).filter
          (fun m ↦ profilePrefix hkTwo hk m =
            retainedYProfilePrefix hn hkTwo hdelta code),
        paddedPreludeMultiRecursiveProfileContinuation n k y m
          (successfulPaddedCoarseBridgeSegments
            (pairPrefixScale n k) hn hkTwo hdelta code reference) :=
      tsum_paddedSuccessfulTailKeyMass_eq_sum_fixedPrefix_continuation
        hn hkTwo hdelta code reference
    _ ≤ _ := hrow

/-- Eventually, every inhabited coarse completion atom has its successful
bridge mass bounded by the public radial envelope times its exact unmarked
kernel product. -/
theorem eventually_successfulBridgeMass_le_radialTail_mul_kernel :
    ∀ᶠ q : ℕ in Filter.atTop, ∀ k ≤ decorrelationCutoff q,
      ∀ (hk : k + 1 ≤ q) (hkTwo : 2 ≤ k + 1)
        (hkp : k + 1 < pairPrefixScale q k)
        (htail : profileUpperTailStart ≤ pairPrefixScale q k),
      ∀ {start : ℕ} {x y : Point}
        (code : CoarseSplitCompletionCode start q k hk profileUpperDelta x y
          (profileInnerBoundary q k y)
          (discBoundary (0, 0) (outerScale q)) (0, 0))
        (reference : CoarseSuccessfulReturnTuple code),
        (∑' tail : CoarseSuccessfulReturnTuple code,
            ∏ j, stoppedWordMass (tail.1 j).1.1) ≤
          ENNReal.ofReal (Real.exp 1 *
            Real.exp (-(2 * (q - pairPrefixScale q k : ℕ) : ℝ) +
              profileUpperConstant * (q : ℝ) ^ (3 / 5 : ℝ))) *
            ∏ j, (coarseAtom code).kernel j := by
  filter_upwards
      [eventually_sum_earlierFixedPrefix_paddedPreludeContinuation_le]
      with q hrow
  intro k hkLevel hk hkTwo hkp htail start x y code reference
  have hn : 2 ≤ q := by omega
  have hdelta : profileUpperDelta ≤ 1 := by
    norm_num [profileUpperDelta]
  let segments := successfulPaddedCoarseBridgeSegments
    (pairPrefixScale q k) hn hkTwo hdelta code reference
  have hpq : pairPrefixScale q k ≤ q := by
    unfold pairPrefixScale
    exact min_le_left _ _
  have hpadded := hrow k hkLevel hkTwo hkp.le hpq htail
    (retainedYProfilePrefix hn hkTwo hdelta code) y segments
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
        paddedSuccessfulUnmarkedKernelProduct
          hn hkTwo hdelta code reference := by
    dsimp only [segments]
    convert
      (successfulPaddedCoarseBridgeSegments_unmarked_prod_eq
        (p := pairPrefixScale q k) hn hkTwo hdelta code reference)
    rename_i segment
    cases segment.1 <;> rfl
  have hcontinuation :
      (∑ m ∈ (constrainedProfiles q profileUpperDelta).filter
          (fun m ↦ profilePrefix hkTwo hk m =
            retainedYProfilePrefix hn hkTwo hdelta code),
        paddedPreludeMultiRecursiveProfileContinuation q k y m segments) ≤
        ENNReal.ofReal (Real.exp 1 *
          Real.exp (-(2 * (q - pairPrefixScale q k : ℕ) : ℝ) +
            profileUpperConstant * (q : ℝ) ^ (3 / 5 : ℝ))) *
          paddedSuccessfulUnmarkedKernelProduct
            hn hkTwo hdelta code reference := by
    rw [← hprod]
    convert hpadded using 1 <;> simp only [segments] <;> rfl
  have hbridge := tsum_successfulBridgeMass_le_radialTail_mul_unmarked
    hn hkTwo hdelta hkp hpq code reference hcontinuation
  calc
    _ ≤ ENNReal.ofReal (Real.exp 1 *
          Real.exp (-(2 * (q - pairPrefixScale q k : ℕ) : ℝ) +
            profileUpperConstant * (q : ℝ) ^ (3 / 5 : ℝ))) *
        paddedSuccessfulUnmarkedKernelProduct
          hn hkTwo hdelta code reference := hbridge
    _ = _ := by
      rw [← coarseAtom_kernel_prod_eq_paddedSuccessfulUnmarkedKernelProduct
        hn hkTwo hdelta code reference]

/-- The same normalized successful-row estimate for every coarse code.  If a
code has no successful continuation, its row is empty; otherwise any one
successful continuation supplies the harmless reference used by the padded
parser. -/
theorem eventually_successfulBridgeMass_le_radialTail_mul_kernel_all :
    ∀ᶠ q : ℕ in Filter.atTop, ∀ k ≤ decorrelationCutoff q,
      ∀ (hk : k + 1 ≤ q) (hkTwo : 2 ≤ k + 1)
        (hkp : k + 1 < pairPrefixScale q k)
        (htail : profileUpperTailStart ≤ pairPrefixScale q k),
      ∀ {start : ℕ} {x y : Point}
        (code : CoarseSplitCompletionCode start q k hk profileUpperDelta x y
          (profileInnerBoundary q k y)
          (discBoundary (0, 0) (outerScale q)) (0, 0)),
        (∑' tail : CoarseSuccessfulReturnTuple code,
            ∏ j, stoppedWordMass (tail.1 j).1.1) ≤
          ENNReal.ofReal (Real.exp 1 *
            Real.exp (-(2 * (q - pairPrefixScale q k : ℕ) : ℝ) +
              profileUpperConstant * (q : ℝ) ^ (3 / 5 : ℝ))) *
            ∏ j, (coarseAtom code).kernel j := by
  filter_upwards
      [eventually_successfulBridgeMass_le_radialTail_mul_kernel]
      with q hrow
  intro k hkLevel hk hkTwo hkp htail start x y code
  classical
  by_cases h : Nonempty (CoarseSuccessfulReturnTuple code)
  · exact hrow k hkLevel hk hkTwo hkp htail code (Classical.choice h)
  · haveI : IsEmpty (CoarseSuccessfulReturnTuple code) :=
      not_nonempty_iff.mp h
    simp

end

end Erdos1165.AsymmetricPaddedSuccessfulTailRow
