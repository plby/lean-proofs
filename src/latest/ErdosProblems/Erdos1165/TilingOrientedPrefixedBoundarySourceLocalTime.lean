/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaAcceptedCreationPath
import ErdosProblems.Erdos1165.TilingOrientedRetainedDominoEndpoint
import ErdosProblems.Erdos1165.TilingOrientedRetainedSourceLocalTime

/-!
# Prefix-correct oriented retained local time

The retained-coordinate multiplicity is the local time of the endpoint chain.
For the physical prefixed fibre this is also its fixed boundary local time:
the optional initial point and terminal remainder lie in the opposite temporal
class and therefore contribute nothing at an orientation-compatible base.
-/

open Set

namespace Erdos1165.TilingOrientedPrefixedBoundarySourceLocalTime

open HLOZPathEvents HLOZSourceOrientedThetaAcceptedCreationPath
open LazyDecomposition
open TilingOrientedAllRepresentedExternalFiber
open TilingOrientedRetainedCoordinateSupport
open TilingOrientedRetainedDominoEndpoint
open TilingOrientedRetainedSourceLocalTime
open TilingOrientedShellZeroSourcePartition
open TilingPrefixedFavoriteTraceSupport TilingPrefixedInsertedLocalTime
open PathInsertion PreStoppingFiber SpatialInsertionFiber StoppedInsertion
open TilingPrefixedStoppedProductDisintegration TilingSpatialInsertionFiber
open VariableStoppedTracePartition
open ExternalCountTransport ExternalThickCount ExternalWeightedOnePoint

noncomputable section

attribute [local instance] Classical.propDecidable

abbrev DominoTiling := Tilings.Tiling

private theorem filter_prefixedBoundary_eq_endpointPath
    {o : Orientation} (initial : List Direction) (x : Point)
    (bs : List PathInsertion.Block) (terminal : Option Point)
    (hx : OrientationCompatible o x)
    (hinitial :
      (finitePathList (pathPrefix
        (trajectory (extendPrefix (directionVectorOfList initial)))
          initial.length)).filter (fun y ↦ decide (orientationClass o y)) = [x])
    (hterminal : ∀ y, terminal = some y → ¬ OrientationCompatible o y) :
    (prefixedTilingPrefixPointPath initial x bs terminal).filter
        (fun y ↦ decide (orientationClass o y)) = blockEndpointPath x bs := by
  unfold prefixedTilingPrefixPointPath
  rw [List.filter_append, hinitial]
  have hblock := blockPath_filter_orientationClass x hx bs
  have hxclass : orientationClass o x :=
    (orientationClass_iff_compatible o x).2 hx
  have hblockTail :
      x :: (blockPathTail x bs).filter
        (fun y ↦ decide (orientationClass o y)) = blockEndpointPath x bs := by
    simpa only [blockPath, List.filter_cons, decide_eq_true hxclass, if_true]
      using hblock
  cases terminal with
  | none =>
      simpa [TilingInsertedLocalTime.tilingPrefixPointPath, blockPath]
        using hblockTail
  | some y =>
      have hy : ¬orientationClass o y := by
        intro hy
        exact hterminal y rfl ((orientationClass_iff_compatible o y).1 hy)
      simpa [TilingInsertedLocalTime.tilingPrefixPointPath, blockPath, hy]
        using hblockTail

private theorem filter_orientedInitialPrefix_eq_endpoint
    (o : Orientation) (initial : List Direction)
    (hlen : initial.length = match o with | .even => 0 | .shifted => 1) :
    (finitePathList (pathPrefix
      (trajectory (extendPrefix (directionVectorOfList initial)))
        initial.length)).filter (fun y ↦ decide (orientationClass o y)) =
      [trajectory (extendPrefix (directionVectorOfList initial))
        initial.length] := by
  cases o with
  | even =>
      cases initial with
      | nil =>
          simp [finitePathList, pathPrefix, trajectory, extendPrefix,
            orientationClass, EvenPoint, pointParity]
      | cons d ds => simp at hlen
  | shifted =>
      cases initial with
      | nil => simp at hlen
      | cons d ds =>
          cases ds with
          | nil =>
              have hodd : OddPoint (directionVector d) := by
                exact pointParity_directionVector d
              simp [finitePathList, pathPrefix, trajectory, extendPrefix,
                directionVectorOfList, orientationClass]
              have hzero : ¬ OddPoint (0 : Point) := by
                norm_num [OddPoint, pointParity]
              simp [hzero, hodd]
          | cons e es => simp at hlen

private theorem orientedTerminal_incompatible
    (t : DominoTiling) (o : Orientation)
    (z : OrientedTilingTypedExternalWordCode t)
    (hinitial : z.initial.1.length =
      match o with | .even => 0 | .shifted => 1)
    (q : Fin (z.retainedCount + 1) → ℕ) (y : Point)
    (hy : prefixedTilingInsertionTerminal
      z.initial t z.start z.retained q z.tail = some y) :
    ¬ OrientationCompatible o y := by
  classical
  rcases z with ⟨initial, retainedCount, retained, tailCode⟩
  rcases tailCode with ⟨tail, htail⟩
  cases tail with
  | nil =>
      simp [prefixedTilingInsertionTerminal] at hy
  | cons d ds =>
      cases ds with
      | cons e es => simp at htail
      | nil =>
          let v := prefixedTilingInsertionPrefixList initial.1 t
            (trajectory (extendPrefix (directionVectorOfList initial.1))
              initial.1.length) retained q [d]
          have heq : trajectory
              (extendPrefix (directionVectorOfList v)) v.length = y := by
            change some (trajectory
              (extendPrefix (directionVectorOfList v)) v.length) = some y at hy
            exact Option.some.inj hy
          have hvlen : v.length = initial.1.length +
              2 * (retainedCount + ∑ j, q j) + 1 := by
            simp [v, prefixedTilingInsertionPrefixList,
              tilingInsertionPrefixList_length]
            omega
          cases o with
          | even =>
              have hvmod : v.length % 2 = 1 := by
                simp at hinitial
                simp [hvlen, hinitial, Nat.add_mod]
              have hvcast : (v.length : ZMod 2) = 1 := by
                rw [← ZMod.natCast_mod v.length 2, hvmod]
                rfl
              change ¬ EvenPoint y
              rw [← heq, EvenPoint, pointParity_trajectory, hvcast]
              decide
          | shifted =>
              have hvmod : v.length % 2 = 0 := by
                simp at hinitial
                simp [hvlen, hinitial, Nat.add_mod]
              have hvcast : (v.length : ZMod 2) = 0 := by
                rw [← ZMod.natCast_mod v.length 2, hvmod]
                rfl
              change ¬ OddPoint y
              rw [← heq, OddPoint, pointParity_trajectory, hvcast]
              decide

theorem prefixedBoundaryLocalTime_eq_coordinateCard
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SupportedIndex t o m k) (hm : 1 < m) (hk : 0 < k)
    (q : Fin (eta.1.retainedCount + 1) → ℕ)
    (b : TilingExternalDomino t eta.1.start eta.1.retained)
    (hb : OrientationCompatible o b.1) :
    prefixedTilingFixedBoundaryLocalTime eta.1.initial.1 eta.1.start
        eta.1.retained
        (prefixedTilingInsertionTerminal eta.1.initial t eta.1.start
          eta.1.retained q eta.1.tail) b.1 =
      Fintype.card (TilingCoordinatesAt t eta.1.start eta.1.retained b) := by
  classical
  rcases eta with ⟨z, hz⟩
  rcases hz with ⟨s, hs⟩
  rw [allRepresentedExternalCreationTraceAtom] at hs
  have hvalid := hs.1
  have hcode := hs.2.2
  have hn : 0 < creationTimeNat m k s := by
    by_contra h
    have hn0 : creationTimeNat m k s = 0 := by omega
    have hcreation : ThresholdCreation s m k (creationTimeNat m k s) := by
      simpa [creationTimeNat, hs.2.1] using thresholdCreation_natFind hs.2.1
    rw [hn0] at hcreation
    have hlocal := position_mem_thresholdSites_of_creation hk hcreation
    have hle := (mem_thresholdSites s 0 m (s 0)).mp hlocal |>.2
    have hzero : localTime s 0 (s 0) = 1 := by
      unfold localTime localTimePrefix pathPrefix
      simp
    rw [hzero] at hle
    omega
  subst z
  unfold validStepWalk at hvalid
  change trajectory (stepsOfWalk s) = s at hvalid
  generalize homega : stepsOfWalk s = omega at hvalid
  subst s
  let terminal := prefixedTilingInsertionTerminal
    (fixedOrientedTypedExternalWordCode t o
      (creationTimeNat m k (trajectory omega)) (trajectory omega)).initial
    t (fixedOrientedTypedExternalWordCode t o
      (creationTimeNat m k (trajectory omega)) (trajectory omega)).start
    (fixedOrientedTypedExternalWordCode t o
      (creationTimeNat m k (trajectory omega)) (trajectory omega)).retained q
    (fixedOrientedTypedExternalWordCode t o
      (creationTimeNat m k (trajectory omega)) (trajectory omega)).tail
  let p := prefixedTilingPrefixPointPath
    (fixedOrientedTypedExternalWordCode t o
      (creationTimeNat m k (trajectory omega)) (trajectory omega)).initial.1
    (fixedOrientedTypedExternalWordCode t o
      (creationTimeNat m k (trajectory omega)) (trajectory omega)).start
    (List.ofFn (fixedOrientedTypedExternalWordCode t o
      (creationTimeNat m k (trajectory omega))
        (trajectory omega)).retained.1) terminal
  have hfilter : p.filter (fun y ↦ decide (orientationClass o y)) =
      blockEndpointPath
        (fixedOrientedTypedExternalWordCode t o
          (creationTimeNat m k (trajectory omega)) (trajectory omega)).start
        (List.ofFn (fixedOrientedTypedExternalWordCode t o
          (creationTimeNat m k (trajectory omega))
            (trajectory omega)).retained.1) := by
    apply filter_prefixedBoundary_eq_endpointPath
    · exact orientationCompatible_fixedOrientedTypedExternalWordCode_start
        t o (creationTimeNat m k (trajectory omega)) (trajectory omega) hn
    · cases o with
      | even =>
          apply filter_orientedInitialPrefix_eq_endpoint
          rfl
      | shifted =>
          apply filter_orientedInitialPrefix_eq_endpoint
          change (List.take 1
            (incrementPrefixList (creationTimeNat m k (trajectory omega))
              (stepsOfWalk (trajectory omega)))).length = 1
          rw [List.length_take]
          simp only [incrementPrefixList, List.length_ofFn]
          omega
    · intro y hy
      apply orientedTerminal_incompatible t o
        (fixedOrientedTypedExternalWordCode t o
          (creationTimeNat m k (trajectory omega)) (trajectory omega))
      · cases o with
        | even => rfl
        | shifted =>
            change (List.take 1
              (incrementPrefixList (creationTimeNat m k (trajectory omega))
                (stepsOfWalk (trajectory omega)))).length = 1
            rw [List.length_take]
            simp only [incrementPrefixList, List.length_ofFn]
            omega
      · exact hy
  rw [card_tilingCoordinatesAt_eq_endpointLocalTime_of_compatible
    t (fixedOrientedTypedExternalWordCode t o
      (creationTimeNat m k (trajectory omega)) (trajectory omega)).start
    (orientationCompatible_fixedOrientedTypedExternalWordCode_start
      t o (creationTimeNat m k (trajectory omega)) (trajectory omega) hn)
    (fixedOrientedTypedExternalWordCode t o
      (creationTimeNat m k (trajectory omega)) (trajectory omega)).retained b hb]
  change listLocalTime p b.1 = _
  have hcount : listLocalTime
      (p.filter (fun y ↦ decide (orientationClass o y))) b.1 =
      listLocalTime p b.1 := by
    unfold listLocalTime
    exact List.count_filter
      (p := fun y ↦ decide (orientationClass o y))
      (decide_eq_true ((orientationClass_iff_compatible o b.1).2 hb))
  rw [← hcount, hfilter]

/-- The prefix-correct fixed local time at the orientation-selected endpoint
of a represented domino is its retained coordinate multiplicity.  Unlike
`prefixedBoundaryLocalTime_eq_coordinateCard`, this statement does not assume
that the canonical tiling base itself lies in the selected checkerboard
class; for column tilings the represented endpoint can be its partner. -/
theorem prefixedBoundaryLocalTime_orientedEndpoint_eq_coordinateCard
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SupportedIndex t o m k) (hm : 1 < m) (hk : 0 < k)
    (q : Fin (eta.1.retainedCount + 1) → ℕ)
    (b : TilingExternalDomino t eta.1.start eta.1.retained) :
    prefixedTilingFixedBoundaryLocalTime eta.1.initial.1 eta.1.start
        eta.1.retained
        (prefixedTilingInsertionTerminal eta.1.initial t eta.1.start
          eta.1.retained q eta.1.tail)
        (orientedDominoEndpoint t o b.1) =
      Fintype.card (TilingCoordinatesAt t eta.1.start eta.1.retained b) := by
  classical
  rcases eta with ⟨z, hz⟩
  rcases hz with ⟨s, hs⟩
  rw [allRepresentedExternalCreationTraceAtom] at hs
  have hvalid := hs.1
  have hcode := hs.2.2
  have hn : 0 < creationTimeNat m k s := by
    by_contra h
    have hn0 : creationTimeNat m k s = 0 := by omega
    have hcreation : ThresholdCreation s m k (creationTimeNat m k s) := by
      simpa [creationTimeNat, hs.2.1] using thresholdCreation_natFind hs.2.1
    rw [hn0] at hcreation
    have hlocal := position_mem_thresholdSites_of_creation hk hcreation
    have hle := (mem_thresholdSites s 0 m (s 0)).mp hlocal |>.2
    have hzero : localTime s 0 (s 0) = 1 := by
      unfold localTime localTimePrefix pathPrefix
      simp
    rw [hzero] at hle
    omega
  subst z
  unfold validStepWalk at hvalid
  change trajectory (stepsOfWalk s) = s at hvalid
  generalize homega : stepsOfWalk s = omega at hvalid
  subst s
  let terminal := prefixedTilingInsertionTerminal
    (fixedOrientedTypedExternalWordCode t o
      (creationTimeNat m k (trajectory omega)) (trajectory omega)).initial
    t (fixedOrientedTypedExternalWordCode t o
      (creationTimeNat m k (trajectory omega)) (trajectory omega)).start
    (fixedOrientedTypedExternalWordCode t o
      (creationTimeNat m k (trajectory omega)) (trajectory omega)).retained q
    (fixedOrientedTypedExternalWordCode t o
      (creationTimeNat m k (trajectory omega)) (trajectory omega)).tail
  let p := prefixedTilingPrefixPointPath
    (fixedOrientedTypedExternalWordCode t o
      (creationTimeNat m k (trajectory omega)) (trajectory omega)).initial.1
    (fixedOrientedTypedExternalWordCode t o
      (creationTimeNat m k (trajectory omega)) (trajectory omega)).start
    (List.ofFn (fixedOrientedTypedExternalWordCode t o
      (creationTimeNat m k (trajectory omega))
        (trajectory omega)).retained.1) terminal
  have hfilter : p.filter (fun y ↦ decide (orientationClass o y)) =
      blockEndpointPath
        (fixedOrientedTypedExternalWordCode t o
          (creationTimeNat m k (trajectory omega)) (trajectory omega)).start
        (List.ofFn (fixedOrientedTypedExternalWordCode t o
          (creationTimeNat m k (trajectory omega))
            (trajectory omega)).retained.1) := by
    apply filter_prefixedBoundary_eq_endpointPath
    · exact orientationCompatible_fixedOrientedTypedExternalWordCode_start
        t o (creationTimeNat m k (trajectory omega)) (trajectory omega) hn
    · cases o with
      | even =>
          apply filter_orientedInitialPrefix_eq_endpoint
          rfl
      | shifted =>
          apply filter_orientedInitialPrefix_eq_endpoint
          change (List.take 1
            (incrementPrefixList (creationTimeNat m k (trajectory omega))
              (stepsOfWalk (trajectory omega)))).length = 1
          rw [List.length_take]
          simp only [incrementPrefixList, List.length_ofFn]
          omega
    · intro y hy
      apply orientedTerminal_incompatible t o
        (fixedOrientedTypedExternalWordCode t o
          (creationTimeNat m k (trajectory omega)) (trajectory omega))
      · cases o with
        | even => rfl
        | shifted =>
            change (List.take 1
              (incrementPrefixList (creationTimeNat m k (trajectory omega))
                (stepsOfWalk (trajectory omega)))).length = 1
            rw [List.length_take]
            simp only [incrementPrefixList, List.length_ofFn]
            omega
      · exact hy
  rw [card_tilingCoordinatesAt_eq_orientedEndpointLocalTime
    t (fixedOrientedTypedExternalWordCode t o
      (creationTimeNat m k (trajectory omega)) (trajectory omega)).start
    (orientationCompatible_fixedOrientedTypedExternalWordCode_start
      t o (creationTimeNat m k (trajectory omega)) (trajectory omega) hn)
    (fixedOrientedTypedExternalWordCode t o
      (creationTimeNat m k (trajectory omega)) (trajectory omega)).retained b]
  change listLocalTime p (orientedDominoEndpoint t o b.1) = _
  have hcount : listLocalTime
      (p.filter (fun y ↦ decide (orientationClass o y)))
          (orientedDominoEndpoint t o b.1) =
      listLocalTime p (orientedDominoEndpoint t o b.1) := by
    unfold listLocalTime
    exact List.count_filter
      (p := fun y ↦ decide (orientationClass o y))
      (decide_eq_true ((orientationClass_iff_compatible o
        (orientedDominoEndpoint t o b.1)).2
          (orientedDominoEndpoint_compatible t o b.1)))
  rw [← hcount, hfilter]

end

end Erdos1165.TilingOrientedPrefixedBoundarySourceLocalTime
