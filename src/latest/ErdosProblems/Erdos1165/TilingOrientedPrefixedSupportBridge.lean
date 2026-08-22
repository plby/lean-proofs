/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingOrientedRetainedCoordinateSupport
import ErdosProblems.Erdos1165.TilingOrientedSupportAwayCoordinates
import ErdosProblems.Erdos1165.TilingPrefixedStoppedProductDisintegration
import ErdosProblems.Erdos1165.TilingTypedFavoriteTrace

/-!
# Oriented source support is represented by a physical-prefix insertion fibre

The shifted temporal pairing is represented by a genuine one-step physical
prefix followed by a stateful tiling-insertion suffix.  This file proves the
deterministic fact needed by the conditional candidate product: every
base-dominant `V₂` base in the selected endpoint orientation is one of the
retained word's insertion coordinates.  The proof does not identify the
shifted suffix with an origin-started walk.
-/

open Set

namespace Erdos1165.TilingOrientedPrefixedSupportBridge

open LazyDecomposition PathInsertion SpatialInsertionFiber StoppedInsertion
open HLOZPathEvents
open PreStoppingFiber VariableStoppedFiber ShiftedPrefixBridge
open VariableStoppedTracePartition
open ExternalCountTransport TilingLazyDecomposition
open ExternalThickCount
open TilingSpatialInsertionFiber TilingInsertedLocalTime
open TilingOrientedRetainedCoordinateSupport
open TilingOrientedShellZeroSourcePartition
open TilingShellZeroSourcePartition
open TilingPrefixedStoppedProductDisintegration
open TilingTypedFavoriteTrace

noncomputable section

abbrev DominoTiling := Tilings.Tiling

private theorem get_pairDirectionList (suffix : List Direction) (n : ℕ)
    (hn : n < (pairDirectionList suffix).length) :
    (pairDirectionList suffix).get ⟨n, hn⟩ =
      (suffix.get ⟨2 * n, by
          rw [pairDirectionList_length] at hn
          omega⟩,
        suffix.get ⟨2 * n + 1, by
          rw [pairDirectionList_length] at hn
          omega⟩) := by
  induction suffix using List.twoStepInduction generalizing n with
  | nil => simp [pairDirectionList] at hn
  | singleton a => simp [pairDirectionList] at hn
  | cons_cons a b rest ih _ =>
      cases n with
      | zero => rfl
      | succ n =>
          simpa [pairDirectionList, Nat.mul_succ, Nat.add_assoc] using
            ih n (by simpa [pairDirectionList] using hn)

/-- The complete blocks of the physical segment after `pre` are exactly the
ordinary pairs of `suffix`. -/
theorem completeSegmentBlocks_extendPrefix_append
    (pre suffix : List Direction) :
    completeSegmentBlocks
        (extendPrefix (directionVectorOfList (pre ++ suffix)))
        pre.length suffix.length = pairDirectionList suffix := by
  apply List.ext_get
  · simp [completeSegmentBlocks, pairDirectionList_length]
  · intro n hnleft hnright
    rw [get_pairDirectionList suffix n hnright]
    simp only [completeSegmentBlocks, List.get_ofFn]
    unfold directionVectorOfList extendPrefix
    simp only [List.get_eq_getElem]
    have hfirst : pre.length + 2 * n < (pre ++ suffix).length := by
      simp only [List.length_append]
      rw [pairDirectionList_length] at hnright
      omega
    have hsecond : pre.length + 2 * n + 1 <
        (pre ++ suffix).length := by
      simp only [List.length_append]
      rw [pairDirectionList_length] at hnright
      omega
    have hsuffixFirst : 2 * n < suffix.length := by
      rw [pairDirectionList_length] at hnright
      omega
    have hsuffixSecond : 2 * n + 1 < suffix.length := by
      rw [pairDirectionList_length] at hnright
      omega
    change
      ((if h : pre.length + 2 * n < (pre ++ suffix).length then
          (pre ++ suffix)[pre.length + 2 * n] else 0),
        (if h : pre.length + 2 * n + 1 < (pre ++ suffix).length then
          (pre ++ suffix)[pre.length + 2 * n + 1] else 0)) =
        (suffix[2 * n]'hsuffixFirst, suffix[2 * n + 1]'hsuffixSecond)
    rw [dif_pos hfirst, dif_pos hsecond]
    simp only [List.getElem_append_right (by omega : pre.length ≤
      pre.length + 2 * n), Nat.add_sub_cancel_left]
    rw [List.getElem_append_right (by omega : pre.length ≤
      pre.length + 2 * n + 1)]
    congr 2
    omega

/-- Deleting state-dependent removable return blocks does not change the set
of two-step endpoints. -/
theorem blockEndpointPath_deleteTilingBlocks_toFinset
    (t : DominoTiling) (x : Point) : ∀ bs : List Block,
    (blockEndpointPath x (deleteTilingBlocks t x bs)).toFinset =
      (blockEndpointPath x bs).toFinset := by
  intro bs
  induction bs generalizing x with
  | nil => rfl
  | cons b bs ih =>
      by_cases hb : b = tilingRemovableBlock t x
      · subst b
        simp only [deleteTilingBlocks, if_true,
          blockEnd_tilingRemovableBlock, blockEndpointPath_cons]
        rw [ih]
        have hxmem : x ∈ (blockEndpointPath x bs).toFinset := by
          cases bs <;> simp [blockEndpointPath]
        rw [List.toFinset_cons]
        exact (Finset.insert_eq_of_mem hxmem).symm
      · simp only [deleteTilingBlocks, if_neg hb,
          blockEndpointPath_cons, List.toFinset_cons]
        rw [ih]

theorem mem_blockEndpointPath_deleteTilingBlocks_iff
    (t : DominoTiling) (x : Point) (bs : List Block) (y : Point) :
    y ∈ blockEndpointPath x (deleteTilingBlocks t x bs) ↔
      y ∈ blockEndpointPath x bs := by
  rw [← List.mem_toFinset, ← List.mem_toFinset,
    blockEndpointPath_deleteTilingBlocks_toFinset]

/-- If the stateful deletion of a raw block word is a fixed retained word,
the word has insertion coordinates in that very retained carrier. -/
theorem exists_tilingInsertGapVector_of_delete_eq
    {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (w : List Block)
    (hdelete : deleteTilingBlocks t x w = List.ofFn r.1) :
    ∃ q : Fin (i + 1) → ℕ, tilingInsertGapVector t x r q = w := by
  obtain ⟨j, r', q, hq⟩ := exists_tilingInsertGapVector t x w
  have hdeleted := congrArg (deleteTilingBlocks t x) hq
  rw [deleteTilingBlocks_tilingInsertGapVector] at hdeleted
  have hlists : List.ofFn r'.1 = List.ofFn r.1 :=
    hdeleted.trans hdelete
  have hji : j = i := by
    simpa using congrArg List.length hlists
  subst j
  have hr : r' = r := by
    apply Subtype.ext
    exact List.ofFn_injective hlists
  subst r'
  exact ⟨q, hq⟩

/-- The oriented external code reconstructs the literal physical prefix,
including the one-step prefix in the shifted endpoint class. -/
theorem exists_prefixedTilingInsertionPrefixList_eq_incrementPrefixList
    (t : DominoTiling) (o : Orientation) (n : ℕ) (s : WalkPath)
    (z : OrientedTilingTypedExternalWordCode t)
    (hcode : fixedOrientedTypedExternalWordCode t o n s = z) :
    ∃ q : Fin (z.retainedCount + 1) → ℕ,
      prefixedTilingInsertionPrefixList z.initial.1 t z.start z.retained q
          z.tail.1 =
        incrementPrefixList n (stepsOfWalk s) := by
  subst z
  let ds := orientedIncrementPrefixList o n s
  let initial := orientedInitialPrefix o n s
  let x := trajectory (extendPrefix (directionVectorOfList initial.1))
    initial.1.length
  let blocks := pairDirectionList ds
  let r := deletedTilingRetainedWord t x blocks
  have hdelete : deleteTilingBlocks t x blocks = List.ofFn r.1 := by
    dsimp only [r]
    exact (List.ofFn_get (deleteTilingBlocks t x blocks)).symm
  obtain ⟨q, hq⟩ :=
    exists_tilingInsertGapVector_of_delete_eq t x r blocks hdelete
  refine ⟨q, ?_⟩
  have hsuffix : tilingInsertionPrefixList t x r q
      (unpairedDirectionTail ds) = ds := by
    unfold tilingInsertionPrefixList
    rw [hq]
    exact pairDirectionList_flatten_append_tail ds
  change initial.1 ++ tilingInsertionPrefixList t x r q
      (unpairedDirectionTail ds) = incrementPrefixList n (stepsOfWalk s)
  rw [hsuffix]
  cases o with
  | even => rfl
  | shifted =>
      change (incrementPrefixList n (stepsOfWalk s)).take 1 ++
          (incrementPrefixList n (stepsOfWalk s)).drop 1 = _
      exact List.take_append_drop 1 _

private theorem not_orientationCompatible_trajectory_add_of_odd
    {o : Orientation} (omega : StepPath) (a n : ℕ)
    (hx : OrientationCompatible o (trajectory omega a))
    (hn : n % 2 = 1) :
    ¬OrientationCompatible o (trajectory omega (a + n)) := by
  have hncast : (n : ZMod 2) = 1 := by
    rw [← ZMod.natCast_mod n 2, hn]
    rfl
  cases o with
  | even =>
      change pointParity (trajectory omega a) = 0 at hx
      change ¬pointParity (trajectory omega (a + n)) = 0
      rw [pointParity_trajectory] at hx ⊢
      rw [Nat.cast_add, hncast, hx]
      decide
  | shifted =>
      change pointParity (trajectory omega a) = 1 at hx
      change ¬pointParity (trajectory omega (a + n)) = 1
      rw [pointParity_trajectory] at hx ⊢
      rw [Nat.cast_add, hncast, hx]
      decide

/-- A support window not containing zero makes every oriented `V₂` base a
literal retained endpoint, hence an insertion coordinate.  The only prefix
assumptions are the source ones: the physical prefix has length at most one,
its endpoint is the retained start, and that start has the selected temporal
orientation. -/
theorem orientedTilingVTwoBases_prefixedInsertion_subset_externalDominoBases
    {i : ℕ} (t : DominoTiling) (o : Orientation) (window : Finset ℕ)
    (initial : BoundaryTail) (x : Point) (r : TilingRetainedWord t x i)
    (q : Fin (i + 1) → ℕ) (tail : BoundaryTail)
    (hstart :
      trajectory
          (extendPrefix (directionVectorOfList
            (prefixedTilingInsertionPrefixList initial.1 t x r q tail.1)))
          initial.1.length = x)
    (hx : OrientationCompatible o x) (hzero : 0 ∉ window) :
    let v := prefixedTilingInsertionPrefixList initial.1 t x r q tail.1
    let s := trajectory (extendPrefix (directionVectorOfList v))
    orientedTilingVTwoBases t o window s v.length ⊆
      tilingExternalDominoBases t x r := by
  classical
  let suffix := tilingInsertionPrefixList t x r q tail.1
  let v := prefixedTilingInsertionPrefixList initial.1 t x r q tail.1
  let omega := extendPrefix (directionVectorOfList v)
  let s := trajectory omega
  dsimp only
  intro b hb
  have hbmem : b ∈ tilingVTwoBases t window s v.length :=
    (mem_orientedTilingVTwoBases_iff t o window s v.length b).1 hb |>.1
  have hbcompat : OrientationCompatible o b :=
    (mem_orientedTilingVTwoBases_iff t o window s v.length b).1 hb |>.2
  have hbdata := Finset.mem_filter.mp hbmem
  have hbwindow : localTime s v.length b ∈ window := hbdata.2.2
  have hlocal : 0 < localTime s v.length b := by
    have hne : localTime s v.length b ≠ 0 := by
      intro h
      apply hzero
      simpa [h] using hbwindow
    omega
  have hvisited : b ∈ visitedSites s v.length :=
    (mem_visitedSites_iff_localTime_pos s v.length b).2 hlocal
  rw [visitedSites, mem_visitedPrefix_iff] at hvisited
  obtain ⟨j, hj⟩ := hvisited
  change s (j : ℕ) = b at hj
  have hvlength : v.length = initial.1.length + suffix.length := by
    simp [v, suffix, prefixedTilingInsertionPrefixList]
  have haj : initial.1.length ≤ (j : ℕ) := by
    have ha : initial.1.length = 0 ∨ initial.1.length = 1 := by
      omega
    rcases ha with ha | ha
    · omega
    · rw [ha] at hstart ⊢
      by_contra h
      have hjzero : (j : ℕ) = 0 := by omega
      cases o with
      | even =>
          change pointParity x = 0 at hx
          have hpar := pointParity_trajectory omega 1
          change pointParity (trajectory omega 1) = 1 at hpar
          rw [hstart] at hpar
          exact zero_ne_one (hx.symm.trans hpar)
      | shifted =>
          change pointParity b = 1 at hbcompat
          have hpar := pointParity_trajectory omega 0
          change pointParity (trajectory omega 0) = 0 at hpar
          rw [hjzero] at hj
          change trajectory omega 0 = b at hj
          rw [hj] at hpar
          exact one_ne_zero (hbcompat.symm.trans hpar)
  let d := (j : ℕ) - initial.1.length
  have hdlt : d < suffix.length + 1 := by
    dsimp only [d]
    have hjlt : (j : ℕ) < v.length + 1 := j.2
    omega
  have had : initial.1.length + d = (j : ℕ) := by
    dsimp only [d]
    omega
  have hsegment : b ∈ segmentPath omega initial.1.length suffix.length := by
    rw [segmentPath, List.mem_ofFn]
    refine ⟨⟨d, hdlt⟩, ?_⟩
    change trajectory omega (initial.1.length + d) = b
    rw [had]
    exact hj
  have hblocks : completeSegmentBlocks omega initial.1.length suffix.length =
      tilingInsertGapVector t x r q := by
    calc
      completeSegmentBlocks omega initial.1.length suffix.length =
          pairDirectionList suffix := by
        simpa [omega, v, suffix, prefixedTilingInsertionPrefixList] using
          completeSegmentBlocks_extendPrefix_append initial.1 suffix
      _ = tilingInsertGapVector t x r q :=
        pairDirectionList_flatten_append_shortTail
          (tilingInsertGapVector t x r q) tail.1 tail.2
  rw [segmentPath_eq_blockPath_append_remainder, hstart, hblocks] at hsegment
  rcases List.mem_append.mp hsegment with hpath | hremainder
  · have hfiltered : b ∈
        (blockPath x (tilingInsertGapVector t x r q)).filter
          (orientationClass o) := by
      rw [List.mem_filter]
      exact ⟨hpath, by
        simpa only [decide_eq_true_eq] using
          (orientationClass_iff_compatible o b).2 hbcompat⟩
    rw [blockPath_filter_orientationClass x hx] at hfiltered
    have hdeleted : b ∈ blockEndpointPath x (List.ofFn r.1) := by
      rw [← deleteTilingBlocks_tilingInsertGapVector t x r q]
      exact (mem_blockEndpointPath_deleteTilingBlocks_iff t x
        (tilingInsertGapVector t x r q) b).2 hfiltered
    rw [blockEndpointPath_eq_rawExternalBaseList, List.mem_ofFn] at hdeleted
    obtain ⟨k, hk⟩ := hdeleted
    apply Finset.mem_image.mpr
    refine ⟨k, Finset.mem_univ _, ?_⟩
    obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hbdata.1
    have hbbase : tilingBase t b = b := by
      rw [← hy, TilingSpatialInsertionFiber.tilingBase_idem]
    rw [hk, hbbase]
  · have htailmod : suffix.length % 2 = tail.1.length := by
      rw [tilingInsertionPrefixList_length]
      have htaille := tail.2
      omega
    have hodd : suffix.length % 2 = 1 := by
      by_contra h
      have heven : suffix.length % 2 = 0 := by omega
      simp [segmentRemainder, heven] at hremainder
    have hxomega :
        OrientationCompatible o (trajectory omega initial.1.length) := by
      change trajectory omega initial.1.length = x at hstart
      rw [hstart]
      exact hx
    have hnot := not_orientationCompatible_trajectory_add_of_odd
      omega initial.1.length suffix.length hxomega hodd
    simp only [segmentRemainder, hodd, one_ne_zero, if_false,
      List.mem_singleton] at hremainder
    exact (hnot (hremainder ▸ hbcompat)).elim

end

end Erdos1165.TilingOrientedPrefixedSupportBridge
