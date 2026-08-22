/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingOrientedAllCreationConcreteFamily
import ErdosProblems.Erdos1165.TilingOrientedPrefixedSupportBridge
import ErdosProblems.Erdos1165.HLOZTypedStoppedCandidateObservability

/-!
# Retained support of a visited oriented tiling base

A tiling base in the temporal endpoint class cannot occur only as a block
midpoint.  If it has positive physical local time, it is therefore a literal
base in the retained endpoint carrier of the same oriented prefix.  This is
the dominance-free support fact needed by the broad source screen.
-/

open Set

namespace Erdos1165.TilingOrientedVisitedBaseExternalSupport

open HLOZPathEvents HLOZTypedStoppedCandidateObservability
open LazyDecomposition PathInsertion ShiftedPrefixBridge
open SpatialInsertionFiber
open PreStoppingFiber StoppedInsertion VariableStoppedFiber
open ExternalCountTransport ExternalThickCount
open TilingLazyDecomposition TilingSpatialInsertionFiber
open TilingInsertedLocalTime TilingOrientedRetainedCoordinateSupport
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedPrefixedSupportBridge VariableStoppedTracePartition
open TilingOrientedShellZeroSourcePartition
open TilingPrefixedStoppedProductDisintegration
open TilingTypedFavoriteTrace

noncomputable section

abbrev DominoTiling := Tilings.Tiling

private theorem trajectory_extendPrefix_directionVectorOfList_append_left
    (initial suffix : List Direction) :
    trajectory
        (extendPrefix (directionVectorOfList (initial ++ suffix)))
        initial.length =
      trajectory (extendPrefix (directionVectorOfList initial))
        initial.length := by
  unfold trajectory
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < initial.length := Finset.mem_range.mp hj
  have hjapp : j < (initial ++ suffix).length := by simp; omega
  simp only [extendPrefix, hjlt, hjapp, dif_pos]
  congr 1
  simp only [directionVectorOfList, List.get_eq_getElem]
  rw [List.getElem_append_left hjlt]

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

/-- A positive-time point in the selected orientation of a literal prefixed
insertion has its canonical domino base in the retained external carrier. -/
theorem tilingBase_mem_externalDominoBases_of_prefixedInsertion_of_positive
    {i : ℕ} (t : DominoTiling) (o : Orientation)
    (initial : BoundaryTail) (x : Point) (r : TilingRetainedWord t x i)
    (q : Fin (i + 1) → ℕ) (tail : BoundaryTail)
    (hstart :
      trajectory
          (extendPrefix (directionVectorOfList
            (prefixedTilingInsertionPrefixList initial.1 t x r q tail.1)))
          initial.1.length = x)
    (hx : OrientationCompatible o x) (b : Point)
    (hcompat : OrientationCompatible o b)
    (hpositive : 0 <
      let v := prefixedTilingInsertionPrefixList initial.1 t x r q tail.1
      let s := trajectory (extendPrefix (directionVectorOfList v))
      localTime s v.length b) :
    tilingBase t b ∈ tilingExternalDominoBases t x r := by
  classical
  let suffix := tilingInsertionPrefixList t x r q tail.1
  let v := prefixedTilingInsertionPrefixList initial.1 t x r q tail.1
  let omega := extendPrefix (directionVectorOfList v)
  let s := trajectory omega
  have hvisited : b ∈ visitedSites s v.length :=
    (mem_visitedSites_iff_localTime_pos s v.length b).2 hpositive
  rw [visitedSites, mem_visitedPrefix_iff] at hvisited
  obtain ⟨j, hj⟩ := hvisited
  change s (j : ℕ) = b at hj
  have hvlength : v.length = initial.1.length + suffix.length := by
    simp [v, suffix, prefixedTilingInsertionPrefixList]
  have haj : initial.1.length ≤ (j : ℕ) := by
    have ha : initial.1.length = 0 ∨ initial.1.length = 1 := by omega
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
          change pointParity b = 1 at hcompat
          have hpar := pointParity_trajectory omega 0
          change pointParity (trajectory omega 0) = 0 at hpar
          rw [hjzero] at hj
          change trajectory omega 0 = b at hj
          rw [hj] at hpar
          exact one_ne_zero (hcompat.symm.trans hpar)
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
          (orientationClass_iff_compatible o b).2 hcompat⟩
    rw [blockPath_filter_orientationClass x hx] at hfiltered
    have hdeleted : b ∈ blockEndpointPath x (List.ofFn r.1) := by
      rw [← deleteTilingBlocks_tilingInsertGapVector t x r q]
      exact (mem_blockEndpointPath_deleteTilingBlocks_iff t x
        (tilingInsertGapVector t x r q) b).2 hfiltered
    rw [blockEndpointPath_eq_rawExternalBaseList, List.mem_ofFn] at hdeleted
    obtain ⟨j, hj⟩ := hdeleted
    apply Finset.mem_image.mpr
    refine ⟨j, Finset.mem_univ _, ?_⟩
    rw [hj]
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
    exact (hnot (hremainder ▸ hcompat)).elim

/-- A positive-time oriented tiling base in a literal prefixed insertion is
one of the retained external domino bases. -/
theorem tilingBase_mem_externalDominoBases_of_prefixedInsertion
    {i : ℕ} (t : DominoTiling) (o : Orientation)
    (initial : BoundaryTail) (x : Point) (r : TilingRetainedWord t x i)
    (q : Fin (i + 1) → ℕ) (tail : BoundaryTail)
    (hstart :
      trajectory
          (extendPrefix (directionVectorOfList
            (prefixedTilingInsertionPrefixList initial.1 t x r q tail.1)))
          initial.1.length = x)
    (hx : OrientationCompatible o x) (b : Point)
    (hbase : tilingBase t b = b) (hcompat : OrientationCompatible o b)
    (hpositive : 0 <
      let v := prefixedTilingInsertionPrefixList initial.1 t x r q tail.1
      let s := trajectory (extendPrefix (directionVectorOfList v))
      localTime s v.length b) :
    b ∈ tilingExternalDominoBases t x r := by
  rw [← hbase]
  exact tilingBase_mem_externalDominoBases_of_prefixedInsertion_of_positive
    t o initial x r q tail hstart hx b hcompat hpositive

/-- Walk-prefix form for an arbitrary positive point in the selected endpoint
orientation. -/
theorem tilingBase_mem_fixedExternalDominoBases_of_positive_point
    (t : DominoTiling) (o : Orientation) (s : WalkPath) (n : ℕ)
    (hvalid : s ∈ validStepWalk) (hn : 0 < n) (b : Point)
    (hcompat : OrientationCompatible o b)
    (hpositive : 0 < localTime s n b) :
    tilingBase t b ∈ tilingExternalDominoBases t
      (fixedOrientedTypedExternalWordCode t o n s).start
      (fixedOrientedTypedExternalWordCode t o n s).retained := by
  let z := fixedOrientedTypedExternalWordCode t o n s
  obtain ⟨q, hq⟩ :=
    exists_prefixedTilingInsertionPrefixList_eq_incrementPrefixList
      t o n s z rfl
  let v := prefixedTilingInsertionPrefixList z.initial.1 t z.start
    z.retained q z.tail.1
  let sq := trajectory (extendPrefix (directionVectorOfList v))
  have hvlen : v.length = n := by
    dsimp only [v]
    rw [hq]
    simp [incrementPrefixList]
  have hstart :
      trajectory (extendPrefix (directionVectorOfList v))
          z.initial.1.length = z.start := by
    change trajectory
        (extendPrefix (directionVectorOfList
          (z.initial.1 ++ tilingInsertionPrefixList t z.start z.retained q
            z.tail.1))) z.initial.1.length =
      trajectory (extendPrefix (directionVectorOfList z.initial.1))
        z.initial.1.length
    exact trajectory_extendPrefix_directionVectorOfList_append_left _ _
  have hp := pathPrefix_canonical_eq_of_prefixedInsertionPrefix_eq
    s z.initial.1 z.start z.retained q z.tail.1 hvalid hq
  have hpositiveQ : 0 < localTime sq v.length b := by
    rw [hvlen]
    exact (localTime_eq_of_pathPrefix_eq hp b).symm ▸ hpositive
  have hx : OrientationCompatible o z.start := by
    simpa only [z] using
      orientationCompatible_fixedOrientedTypedExternalWordCode_start
        t o n s hn
  exact tilingBase_mem_externalDominoBases_of_prefixedInsertion_of_positive
    t o z.initial z.start z.retained q z.tail hstart hx b hcompat
      (by simpa only [sq, v] using hpositiveQ)

/-- Walk-prefix form of the dominance-free retained support theorem. -/
theorem tilingBase_mem_fixedExternalDominoBases_of_positive
    (t : DominoTiling) (o : Orientation) (s : WalkPath) (n : ℕ)
    (hvalid : s ∈ validStepWalk) (hn : 0 < n) (b : Point)
    (hbase : tilingBase t b = b) (hcompat : OrientationCompatible o b)
    (hpositive : 0 < localTime s n b) :
    b ∈ tilingExternalDominoBases t
      (fixedOrientedTypedExternalWordCode t o n s).start
      (fixedOrientedTypedExternalWordCode t o n s).retained := by
  rw [← hbase]
  exact tilingBase_mem_fixedExternalDominoBases_of_positive_point
    t o s n hvalid hn b hcompat hpositive

end

end Erdos1165.TilingOrientedVisitedBaseExternalSupport
