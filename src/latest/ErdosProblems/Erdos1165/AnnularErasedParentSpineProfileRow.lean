/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularErasedParentSpineRowPartition
import ErdosProblems.Erdos1165.AnnularErasedParentSpineProfile

/-!
# Profile geometry for the erased-parent assembly row

The generic erased-parent row enumerates retained inward words, deleted
child-return words, and the retained final escape word.  Its measure theorem
asks only that the fully reassembled word first hit the parent outer boundary
at its recorded endpoint.  This file derives those pathwise facts from the
canonical profile-boundary word codes.
-/

open MeasureTheory Set

namespace Erdos1165.AnnularErasedParentSpineProfileRow

open AlternatingConcatPrefixFree AnnularErasedParentSpineRowPartition
open AnnularDecoratedProfileRow AnnularProfileClocks
open AnnularOffspringKernelRadial
open MarkedBoundaryVisitKernel MarkedBridgeFactorization
open TerminalGlobalExitSplice
open RealDiscFinite
open TerminalProfileBoundarySeparation TerminalSpliceProfileGeometry
open TerminalProfileClockEquivalence TerminalSequentialVisitLaw
open TerminalSkeletonInvariance TerminalSkeletonWords
open TerminalVisitSpliceInvariance ThickPoint

noncomputable section

/-- A canonical first-boundary word code has the corresponding literal
finite-word first-hit property. -/
theorem wordFirstHitsAtEnd_boundaryExitWordCode
    {boundary : Set Point} {start endpoint : Point}
    (code : BoundaryExitWordCode boundary start endpoint) :
    WordFirstHitsAtEnd boundary start (List.ofFn code.1.2) := by
  apply WordFirstHitsAtEnd.of_isFirstHit
  · rw [List.length_ofFn, wordWalk]
    rw [← stepPrefix_extendStoppedWord code.1]
    rw [wordPosition_ofFn_stepPrefix start (extendStoppedWord code.1)
      (show code.1.1 ≤ code.1.1 from le_rfl)]
    exact code.2.1.1
  · intro t ht
    have htN : t ≤ code.1.1 := by
      simpa only [List.length_ofFn] using ht.le
    rw [wordWalk]
    rw [← stepPrefix_extendStoppedWord code.1]
    rw [wordPosition_ofFn_stepPrefix start (extendStoppedWord code.1) htN]
    exact code.2.1.2 t (by simpa using ht)

/-- A word which first hits a larger boundary and whose endpoint is outside a
smaller boundary avoids the smaller boundary throughout. -/
theorem WordFirstHitsAtEnd.avoids_of_subset_of_endpoint_not_mem
    {large small : Set Point} {start : Point} {word : List Direction}
    (h : WordFirstHitsAtEnd large start word) (hsub : small ⊆ large)
    (hend : wordEndpoint start word ∉ small) :
    WordAvoids small start word := by
  apply WordAvoids.of_forall_wordWalk
  intro t ht
  by_cases hlt : t < word.length
  · intro hsmall
    exact h.before_endpoint_not_mem t hlt (hsub hsmall)
  · have htEq : t = word.length := by omega
    subst t
    simpa only [wordWalk_length, wordEndpoint] using hend

/-- Every level-`k+1` profile point lies in the level-`k` disc. -/
theorem profileCycleInnerPoint_mem_parentDisc
    {n k : ℕ} {center : Point} (hk : k + 1 ≤ n)
    (z : ProfileCycleInnerPoint n k center) :
    z.1 ∈ disc center (scaleRadius n k) :=
  (mem_discBoundaryFinset.mp z.2).1.trans
    (scaleRadius_antitone_of_le (by omega : k ≤ k + 1) hk)

/-- The parent disc does not meet the profile outer boundary. -/
theorem parentDisc_disjoint_profileOuterBoundary
    {n k : ℕ} {center z : Point} (hn : 2 ≤ n) (hk0 : 0 < k)
    (hk : k + 1 ≤ n) (hz : z ∈ disc center (scaleRadius n k)) :
    z ∉ profileOuterBoundary n k center := by
  apply not_mem_discBoundary_of_mem_disc_of_add_one_le hz
  exact scaleRadius_add_one_le_previous hn hk0 (by omega : k ≤ n + 1)

/-- A retained middle-to-inner word avoids the parent outer boundary, including
its inner endpoint. -/
theorem profileInwardWord_avoids_outer
    {n k : ℕ} {center : Point} (hn : 2 ≤ n) (hk0 : 0 < k)
    (hk : k + 1 ≤ n) (start : Point)
    (inner : ProfileCycleInnerPoint n k center)
    (code : BoundaryExitWordCode
      (profileInnerBoundary n (k + 1) center ∪
        profileOuterBoundary n k center) start inner.1) :
    WordAvoids (profileOuterBoundary n k center) start
      (List.ofFn code.1.2) := by
  apply WordFirstHitsAtEnd.avoids_of_subset_of_endpoint_not_mem
    (wordFirstHitsAtEnd_boundaryExitWordCode code)
  · exact fun _ hz ↦ Or.inr hz
  · rw [boundaryExitWordCode_wordEndpoint code]
    exact parentDisc_disjoint_profileOuterBoundary hn hk0 hk
      (profileCycleInnerPoint_mem_parentDisc hk inner)

/-- A retained final word whose recorded endpoint is on the parent outer
boundary first hits that outer boundary at its end. -/
theorem profileEscapeWord_firstHits_outer
    {n k : ℕ} {center : Point} (start : Point)
    (outer : ProfileCycleOuterPoint n k center)
    (code : BoundaryExitWordCode
      (profileInnerBoundary n (k + 1) center ∪
        profileOuterBoundary n k center) start outer.1) :
    WordFirstHitsAtEnd (profileOuterBoundary n k center) start
      (List.ofFn code.1.2) := by
  have hlarge := wordFirstHitsAtEnd_boundaryExitWordCode code
  apply WordFirstHitsAtEnd.of_isFirstHit
  · rw [wordWalk_length]
    change wordEndpoint start (List.ofFn code.1.2) ∈
      profileOuterBoundary n k center
    rw [boundaryExitWordCode_wordEndpoint code]
    exact mem_discBoundaryFinset.mp outer.2
  · intro t ht houter
    exact hlarge.before_endpoint_not_mem t ht (Or.inr houter)

/-- A canonical child return stays inside the parent disc. -/
theorem profileChildWord_within_parentDisc
    {n k : ℕ} {center : Point} (hk : k + 1 ≤ n)
    (inner : ProfileCycleInnerPoint n k center) (returnPoint : Point)
    (code : BoundaryExitWordCode (profileInnerBoundary n k center)
      inner.1 returnPoint) :
    WordWithin (disc center (scaleRadius n k)) inner.1
      (List.ofFn code.1.2) := by
  exact (boundaryExitWordCode_wordWithin_and_endpoint
    (profileCycleInnerPoint_mem_parentDisc hk inner) code).1

/-- The chronological list used by the erased-parent row is the standard
alternating terminal concatenation with the escape word in the last slot. -/
theorem interleavedErasedParentList_eq_alternatingConcat :
    ∀ (q : ℕ) (inward child : Fin q → List Direction)
      (escape : List Direction),
      interleavedErasedParentList q inward child escape =
        alternatingConcat q (Fin.lastCases escape inward) child := by
  intro q
  induction q with
  | zero =>
      intro inward child escape
      rfl
  | succ q ih =>
      intro inward child escape
      simp only [interleavedErasedParentList, alternatingConcat]
      rw [ih]
      have hzero : Fin.lastCases escape inward (0 : Fin (q + 2)) =
          inward 0 := by
        rw [show (0 : Fin (q + 2)) = (0 : Fin (q + 1)).castSucc by rfl,
          Fin.lastCases_castSucc]
      have htail :
          (fun j : Fin (q + 1) ↦ Fin.lastCases escape inward j.succ) =
            Fin.lastCases escape (fun j : Fin q ↦ inward j.succ) := by
        funext j
        refine Fin.lastCases ?_ (fun i ↦ ?_) j
        · rw [show (Fin.last q).succ = Fin.last (q + 1) by ext; simp,
            Fin.lastCases_last, Fin.lastCases_last]
        · rw [show i.castSucc.succ = i.succ.castSucc by ext; simp,
            Fin.lastCases_castSucc, Fin.lastCases_castSucc]
      rw [hzero, htail]

@[simp] theorem middleStage_succ_castSucc
    {q : ℕ} (start : Point) (returnPoint : Fin (q + 1) → Point)
    (j : Fin q) :
    middleStage start returnPoint j.succ.castSucc = returnPoint j.castSucc := by
  unfold middleStage
  rw [show j.succ.castSucc = j.castSucc.succ by ext; simp, Fin.cons_succ]

@[simp] theorem middleStage_last_succ
    {q : ℕ} (start : Point) (returnPoint : Fin (q + 1) → Point) :
    middleStage start returnPoint (Fin.last (q + 1)) =
      returnPoint (Fin.last q) := by
  unfold middleStage
  rw [show Fin.last (q + 1) = (Fin.last q).succ by ext; simp,
    Fin.cons_succ]

/-- Structural first-hit lemma for a chronological retained/child assembly.
It is stated for raw finite words so its recursion never transports dependent
boundary-code types. -/
theorem wordFirstHitsAtEnd_interleavedErasedParentList :
    ∀ (q : ℕ) (B D : Set Point) (start : Point)
      (innerPoint returnPoint : Fin q → Point)
      (inward child : Fin q → List Direction) (escape : List Direction),
      (∀ j, WordAvoids B (middleStage start returnPoint j.castSucc)
        (inward j)) →
      (∀ j, wordEndpoint (middleStage start returnPoint j.castSucc)
        (inward j) = innerPoint j) →
      (∀ j, WordWithin D (innerPoint j) (child j)) →
      (∀ j, wordEndpoint (innerPoint j) (child j) = returnPoint j) →
      (∀ z, z ∈ D → z ∉ B) →
      WordFirstHitsAtEnd B
        (middleStage start returnPoint (Fin.last q)) escape →
      WordFirstHitsAtEnd B start
        (interleavedErasedParentList q inward child escape) := by
  intro q
  induction q with
  | zero =>
      intro B D start innerPoint returnPoint inward child escape
        _hinward _hinwardEnd _hchild _hchildEnd _hdisjoint hescape
      simpa [interleavedErasedParentList, middleStage] using hescape
  | succ q ih =>
      intro B D start innerPoint returnPoint inward child escape
        hinward hinwardEnd hchild hchildEnd hdisjoint hescape
      have hinwardZero : WordAvoids B start (inward 0) := by
        simpa [middleStage] using hinward 0
      have hchildZero : WordAvoids B (innerPoint 0) (child 0) :=
        (hchild 0).avoids hdisjoint
      have hinwardZeroEnd : wordEndpoint start (inward 0) = innerPoint 0 := by
        simpa [middleStage] using hinwardEnd 0
      have hprefix : WordAvoids B start (inward 0 ++ child 0) := by
        apply WordAvoids.append hinwardZero
        rw [hinwardZeroEnd]
        exact hchildZero
      simp only [interleavedErasedParentList]
      apply WordFirstHitsAtEnd.append hprefix
      rw [wordEndpoint_append, hinwardZeroEnd, hchildEnd 0]
      have hreturn : Fin.cons (returnPoint 0)
          (fun j : Fin q ↦ returnPoint j.succ) = returnPoint :=
        Fin.cons_self_tail returnPoint
      apply ih B D (returnPoint 0) (fun j ↦ innerPoint j.succ)
        (fun j ↦ returnPoint j.succ) (fun j ↦ inward j.succ)
        (fun j ↦ child j.succ) escape
      · intro j
        have hj := hinward j.succ
        rw [middleStage_succ_castSucc] at hj
        unfold middleStage
        rw [hreturn]
        exact hj
      · intro j
        have hj := hinwardEnd j.succ
        rw [middleStage_succ_castSucc] at hj
        unfold middleStage
        rw [hreturn]
        exact hj
      · exact fun j ↦ hchild j.succ
      · exact fun j ↦ hchildEnd j.succ
      · exact hdisjoint
      · have hlast := hescape
        rw [middleStage_last_succ] at hlast
        unfold middleStage
        rw [hreturn]
        exact hlast

/-- Endpoint form of the same raw chronological assembly. -/
theorem wordEndpoint_interleavedErasedParentList :
    ∀ (q : ℕ) (start : Point) (innerPoint returnPoint : Fin q → Point)
      (outerPoint : Point) (inward child : Fin q → List Direction)
      (escape : List Direction),
      (∀ j, wordEndpoint (middleStage start returnPoint j.castSucc)
        (inward j) = innerPoint j) →
      (∀ j, wordEndpoint (innerPoint j) (child j) = returnPoint j) →
      wordEndpoint (middleStage start returnPoint (Fin.last q)) escape =
        outerPoint →
      wordEndpoint start
        (interleavedErasedParentList q inward child escape) = outerPoint := by
  intro q
  induction q with
  | zero =>
      intro start innerPoint returnPoint outerPoint inward child escape
        _hinwardEnd _hchildEnd hescape
      simpa [interleavedErasedParentList, middleStage] using hescape
  | succ q ih =>
      intro start innerPoint returnPoint outerPoint inward child escape
        hinwardEnd hchildEnd hescape
      have hinwardZeroEnd : wordEndpoint start (inward 0) = innerPoint 0 := by
        simpa [middleStage] using hinwardEnd 0
      simp only [interleavedErasedParentList, wordEndpoint_append]
      rw [hinwardZeroEnd, hchildEnd 0]
      have hreturn : Fin.cons (returnPoint 0)
          (fun j : Fin q ↦ returnPoint j.succ) = returnPoint :=
        Fin.cons_self_tail returnPoint
      apply ih (returnPoint 0) (fun j ↦ innerPoint j.succ)
        (fun j ↦ returnPoint j.succ) outerPoint (fun j ↦ inward j.succ)
        (fun j ↦ child j.succ) escape
      · intro j
        have hj := hinwardEnd j.succ
        rw [middleStage_succ_castSucc] at hj
        unfold middleStage
        rw [hreturn]
        exact hj
      · exact fun j ↦ hchildEnd j.succ
      · have hlast := hescape
        rw [middleStage_last_succ] at hlast
        unfold middleStage
        rw [hreturn]
        exact hlast

/-- Reassembling every retained inward word with its deleted child return
first hits the profile outer boundary at the end of the retained escape. -/
theorem profileInterleavedAssembly_firstHits_outer
    {q n k : ℕ} {center : Point} (hn : 2 ≤ n) (hk0 : 0 < k)
    (hk : k + 1 ≤ n)
    (start : ProfileCycleMiddlePoint n k center)
    (innerPoint : Fin q → ProfileCycleInnerPoint n k center)
    (returnPoint : Fin q → ProfileCycleMiddlePoint n k center)
    (outerPoint : ProfileCycleOuterPoint n k center)
    (code : ErasedParentAssemblyCode q
      (profileInnerBoundary n (k + 1) center ∪
        profileOuterBoundary n k center)
      (profileInnerBoundary n k center) start.1
      (fun j ↦ (innerPoint j).1) (fun j ↦ (returnPoint j).1)
      outerPoint.1) :
    WordFirstHitsAtEnd (profileOuterBoundary n k center) start.1
      (interleavedErasedParentList q
        (fun j ↦ List.ofFn (code.1 j).1.2)
        (fun j ↦ List.ofFn (code.2.1 j).1.2)
        (List.ofFn code.2.2.1.2)) := by
  apply wordFirstHitsAtEnd_interleavedErasedParentList q
    (profileOuterBoundary n k center) (disc center (scaleRadius n k))
    start.1 (fun j ↦ (innerPoint j).1) (fun j ↦ (returnPoint j).1)
  · intro j
    exact profileInwardWord_avoids_outer hn hk0 hk _ (innerPoint j)
      (code.1 j)
  · exact fun j ↦ boundaryExitWordCode_wordEndpoint (code.1 j)
  · intro j
    exact profileChildWord_within_parentDisc hk (innerPoint j)
      (returnPoint j).1 (code.2.1 j)
  · exact fun j ↦ boundaryExitWordCode_wordEndpoint (code.2.1 j)
  · exact fun _ hz ↦ parentDisc_disjoint_profileOuterBoundary hn hk0 hk hz
  · exact profileEscapeWord_firstHits_outer _ outerPoint code.2.2

/-- The endpoint of every fully reassembled profile row is its recorded
outer endpoint. -/
theorem profileInterleavedAssembly_endpoint
    {q n k : ℕ} {center : Point}
    (start : ProfileCycleMiddlePoint n k center)
    (innerPoint : Fin q → ProfileCycleInnerPoint n k center)
    (returnPoint : Fin q → ProfileCycleMiddlePoint n k center)
    (outerPoint : ProfileCycleOuterPoint n k center)
    (code : ErasedParentAssemblyCode q
      (profileInnerBoundary n (k + 1) center ∪
        profileOuterBoundary n k center)
      (profileInnerBoundary n k center) start.1
      (fun j ↦ (innerPoint j).1) (fun j ↦ (returnPoint j).1)
      outerPoint.1) :
    wordEndpoint start.1
      (interleavedErasedParentList q
        (fun j ↦ List.ofFn (code.1 j).1.2)
        (fun j ↦ List.ofFn (code.2.1 j).1.2)
        (List.ofFn code.2.2.1.2)) = outerPoint.1 := by
  apply wordEndpoint_interleavedErasedParentList q start.1
    (fun j ↦ (innerPoint j).1) (fun j ↦ (returnPoint j).1) outerPoint.1
  · exact fun j ↦ boundaryExitWordCode_wordEndpoint (code.1 j)
  · exact fun j ↦ boundaryExitWordCode_wordEndpoint (code.2.1 j)
  · exact boundaryExitWordCode_wordEndpoint code.2.2

/-- Convert a finite-list first-hit certificate to the stopped extension of
the corresponding literal list word. -/
theorem absoluteBoundaryFirstAt_listStoppedWord
    {boundary : Set Point} {start : Point} {word : List Direction}
    (hfirst : WordFirstHitsAtEnd boundary start word) :
    AbsoluteBoundaryFirstAt boundary start
      (extendStoppedWord (listStoppedWord word)) word.length := by
  have hsemantic := hfirst.isFirstHit
  have hpath (t : ℕ) (ht : t ≤ word.length) :
      PlanarPotential.trajectoryFrom start
          (extendStoppedWord (listStoppedWord word)) t =
        wordWalk start word t := by
    symm
    simpa only [TerminalVisitSpliceInvariance.stoppedWordOfList,
      AlternatingConcatPrefixFree.listStoppedWord] using
      wordWalk_eq_trajectoryFrom_extendStoppedWord start word ht
  constructor
  · rw [hpath word.length le_rfl]
    exact hsemantic.1
  · intro t ht
    rw [hpath t ht.le]
    exact hsemantic.2 t ht

/-- Endpoint conversion for the same literal list word. -/
theorem trajectoryFrom_listStoppedWord_endpoint
    {start endpoint : Point} {word : List Direction}
    (hend : wordEndpoint start word = endpoint) :
    PlanarPotential.trajectoryFrom start
        (extendStoppedWord (listStoppedWord word)) word.length = endpoint := by
  calc
    PlanarPotential.trajectoryFrom start
        (extendStoppedWord (listStoppedWord word)) word.length =
        wordWalk start word word.length := by
      symm
      simpa only [TerminalVisitSpliceInvariance.stoppedWordOfList,
        AlternatingConcatPrefixFree.listStoppedWord] using
        wordWalk_eq_trajectoryFrom_extendStoppedWord start word le_rfl
    _ = wordEndpoint start word := by
      simp only [wordWalk_length, wordEndpoint]
    _ = endpoint := hend

/-- The generic first-boundary hypothesis of the erased-parent row is
automatic for the literal profile geometry. -/
theorem profileErasedParentAssemblyWord_first
    {q n k : ℕ} {center : Point} (hn : 2 ≤ n) (hk0 : 0 < k)
    (hk : k + 1 ≤ n)
    (start : ProfileCycleMiddlePoint n k center)
    (innerPoint : Fin q → ProfileCycleInnerPoint n k center)
    (returnPoint : Fin q → ProfileCycleMiddlePoint n k center)
    (outerPoint : ProfileCycleOuterPoint n k center)
    (code : ErasedParentAssemblyCode q
      (profileInnerBoundary n (k + 1) center ∪
        profileOuterBoundary n k center)
      (profileInnerBoundary n k center) start.1
      (fun j ↦ (innerPoint j).1) (fun j ↦ (returnPoint j).1)
      outerPoint.1) :
    AbsoluteBoundaryFirstAt (profileOuterBoundary n k center) start.1
      (extendStoppedWord (erasedParentAssemblyWord code))
      (erasedParentAssemblyWord code).1 := by
  unfold erasedParentAssemblyWord
  exact absoluteBoundaryFirstAt_listStoppedWord
    (profileInterleavedAssembly_firstHits_outer hn hk0 hk start innerPoint
      returnPoint outerPoint code)

/-- The generic endpoint hypothesis of the erased-parent row is automatic
for the literal profile geometry. -/
theorem profileErasedParentAssemblyWord_endpoint
    {q n k : ℕ} {center : Point}
    (start : ProfileCycleMiddlePoint n k center)
    (innerPoint : Fin q → ProfileCycleInnerPoint n k center)
    (returnPoint : Fin q → ProfileCycleMiddlePoint n k center)
    (outerPoint : ProfileCycleOuterPoint n k center)
    (code : ErasedParentAssemblyCode q
      (profileInnerBoundary n (k + 1) center ∪
        profileOuterBoundary n k center)
      (profileInnerBoundary n k center) start.1
      (fun j ↦ (innerPoint j).1) (fun j ↦ (returnPoint j).1)
      outerPoint.1) :
    PlanarPotential.trajectoryFrom start.1
      (extendStoppedWord (erasedParentAssemblyWord code))
      (erasedParentAssemblyWord code).1 = outerPoint.1 := by
  unfold erasedParentAssemblyWord
  exact trajectoryFrom_listStoppedWord_endpoint
    (profileInterleavedAssembly_endpoint start innerPoint returnPoint
      outerPoint code)

/-- Prefix-free stopped-event code for every fully assembled profile row.
All geometry premises are discharged internally. -/
def profileErasedParentAssemblyStoppedEventCode
    {q n k : ℕ} {center : Point} (hn : 2 ≤ n) (hk0 : 0 < k)
    (hk : k + 1 ≤ n)
    (start : ProfileCycleMiddlePoint n k center)
    (innerPoint : Fin q → ProfileCycleInnerPoint n k center)
    (returnPoint : Fin q → ProfileCycleMiddlePoint n k center)
    (outerPoint : ProfileCycleOuterPoint n k center) :
    StoppedEventCode (stoppedWordEvent
      (erasedParentAssemblyWord (q := q)
        (retainedBoundary := profileInnerBoundary n (k + 1) center ∪
          profileOuterBoundary n k center)
        (childBoundary := profileInnerBoundary n k center)
        (start := start.1) (innerPoint := fun j ↦ (innerPoint j).1)
        (returnPoint := fun j ↦ (returnPoint j).1)
        (outerPoint := outerPoint.1))) :=
  erasedParentAssemblyStoppedEventCode
    (fun code ↦ profileErasedParentAssemblyWord_first hn hk0 hk start
      innerPoint returnPoint outerPoint code)
    (fun code ↦ profileErasedParentAssemblyWord_endpoint start innerPoint
      returnPoint outerPoint code)

/-- Exact fair-walk mass of a complete fixed-endpoint profile row.  This is
the profile-specialized row theorem with no exposed first-hit or endpoint
hypotheses. -/
theorem fairSteps_profileErasedParentAssemblyEvent
    {q n k : ℕ} {center : Point} (hn : 2 ≤ n) (hk0 : 0 < k)
    (hk : k + 1 ≤ n)
    (start : ProfileCycleMiddlePoint n k center)
    (innerPoint : Fin q → ProfileCycleInnerPoint n k center)
    (returnPoint : Fin q → ProfileCycleMiddlePoint n k center)
    (outerPoint : ProfileCycleOuterPoint n k center) :
    fairSteps (stoppedWordEvent
      (erasedParentAssemblyWord (q := q)
        (retainedBoundary := profileInnerBoundary n (k + 1) center ∪
          profileOuterBoundary n k center)
        (childBoundary := profileInnerBoundary n k center)
        (start := start.1) (innerPoint := fun j ↦ (innerPoint j).1)
        (returnPoint := fun j ↦ (returnPoint j).1)
        (outerPoint := outerPoint.1))) =
      (∏ j, profileInwardKernelENNReal n k center
          (profileMiddleStage start returnPoint j.castSucc) (innerPoint j)) *
        (∏ j, skeletonExitKernel (profileInnerBoundary n k center)
          (innerPoint j).1 (returnPoint j).1) *
        profileEscapeKernelENNReal n k center
          (profileMiddleStage start returnPoint (Fin.last q)) outerPoint := by
  simpa only [profileInwardKernelENNReal, profileEscapeKernelENNReal,
    AnnularOffspringKernel.annularEscapeKernel, coe_profileMiddleStage] using
      fairSteps_erasedParentAssemblyEvent
        (fun code ↦ profileErasedParentAssemblyWord_first hn hk0 hk start
          innerPoint returnPoint outerPoint code)
        (fun code ↦ profileErasedParentAssemblyWord_endpoint start innerPoint
          returnPoint outerPoint code)


end

end Erdos1165.AnnularErasedParentSpineProfileRow
