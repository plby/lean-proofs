/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingOrientedAllCreationConcreteFamily
import ErdosProblems.Erdos1165.TilingShellZeroAllCreationTraceBridge
import ErdosProblems.Erdos1165.HLOZThetaSourceBalance

/-!
# Concrete oriented shell support selectors

The source and replacement support sets are prefix observables and, on a
valid physical walk, every selected base is represented by the retained
endpoint carrier of the same dominant orientation.  This supplies the last
deterministic input to the concrete all-creation stopped-coordinate family.
-/

open MeasureTheory Set

namespace Erdos1165.TilingOrientedShellSupportSelector

open HLOZPathEvents HLOZThetaSourceBalance HLOZShellZeroReplacementWindows
open HLOZProposition48Candidates
open LazyDecomposition PathInsertion SpatialInsertionFiber
open PreStoppingFiber StoppedInsertion VariableStoppedFiber
open TilingLazyDecomposition TilingSpatialInsertionFiber
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedPrefixedSupportBridge
open TilingOrientedRetainedCoordinateSupport
open TilingOrientedShellZeroSourcePartition
open TilingShellZeroAllCreationTraceBridge
open TilingShellZeroSourcePartition
open TilingPrefixedStoppedProductDisintegration
open VariableStoppedTracePartition

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

private theorem orientedTilingVTwoBases_subset_fixedExternalDominoBases_of_start
    (t : DominoTiling) (o : Orientation) (window : Finset ℕ)
    (s : WalkPath) (n : ℕ) (hvalid : s ∈ validStepWalk)
    (hzero : 0 ∉ window)
    (hx : OrientationCompatible o
      (fixedOrientedTypedExternalWordCode t o n s).start) :
    orientedTilingVTwoBases t o window s n ⊆
      tilingExternalDominoBases t
        (fixedOrientedTypedExternalWordCode t o n s).start
        (fixedOrientedTypedExternalWordCode t o n s).retained := by
  let z := fixedOrientedTypedExternalWordCode t o n s
  obtain ⟨q, hq⟩ :=
    exists_prefixedTilingInsertionPrefixList_eq_incrementPrefixList
      t o n s z rfl
  let v := prefixedTilingInsertionPrefixList z.initial.1 t z.start
    z.retained q z.tail.1
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
  have hsub :=
    orientedTilingVTwoBases_prefixedInsertion_subset_externalDominoBases
      t o window z.initial z.start z.retained q z.tail hstart
        (by simpa only [z] using hx) hzero
  change prefixOrientedTilingVTwoBases t o window (pathPrefix s n) ⊆
    tilingExternalDominoBases t z.start z.retained
  rw [← hp]
  change orientedTilingVTwoBases t o window
      (trajectory (extendPrefix (directionVectorOfList v))) n ⊆
    tilingExternalDominoBases t z.start z.retained
  change orientedTilingVTwoBases t o window
      (trajectory (extendPrefix (directionVectorOfList v))) v.length ⊆
    tilingExternalDominoBases t z.start z.retained at hsub
  simpa only [hvlen] using hsub

/-- Every oriented `V₂` base of a valid physical prefix is a coordinate of
the canonical retained endpoint word of that same orientation. -/
theorem orientedTilingVTwoBases_subset_fixedExternalDominoBases
    (t : DominoTiling) (o : Orientation) (window : Finset ℕ)
    (s : WalkPath) (n : ℕ) (hvalid : s ∈ validStepWalk)
    (hzero : 0 ∉ window) :
    orientedTilingVTwoBases t o window s n ⊆
      tilingExternalDominoBases t
        (fixedOrientedTypedExternalWordCode t o n s).start
        (fixedOrientedTypedExternalWordCode t o n s).retained := by
  by_cases hn : 0 < n
  · have hx : OrientationCompatible o
        (fixedOrientedTypedExternalWordCode t o n s).start := by
      exact orientationCompatible_fixedOrientedTypedExternalWordCode_start
        t o n s hn
    exact orientedTilingVTwoBases_subset_fixedExternalDominoBases_of_start
      t o window s n hvalid hzero hx
  · have hnzero : n = 0 := by omega
    subst n
    cases o with
    | even =>
        have hx : OrientationCompatible Orientation.even
            (fixedOrientedTypedExternalWordCode t .even 0 s).start := by
          dsimp only [fixedOrientedTypedExternalWordCode,
            orientedInitialPrefix, OrientedTilingTypedExternalWordCode.start]
          rfl
        exact orientedTilingVTwoBases_subset_fixedExternalDominoBases_of_start
          t .even window s 0 hvalid hzero hx
    | shifted =>
        intro b hb
        exfalso
        have hb' := (mem_orientedTilingVTwoBases_iff
          t .shifted window s 0 b).1 hb
        simp [tilingVTwoBases, visitedTilingBases, tilingVTwoAt,
          visitedSites, visitedPrefix, localTime, localTimePrefix] at hb'
        have hs0 : s 0 = (0, 0) := by
          rw [← hvalid]
          rfl
        have hs0' : pathPrefix s 0 0 = (0, 0) := hs0
        rw [hs0'] at hb'
        have hbase : b = tilingBase t (0, 0) := by
          exact hb'.1.1
        have hbcompat : pointParity b = 1 := hb'.2
        rcases point_eq_tilingBase_or_partner_base t (0, 0) with h | h
        · have hbzero : b = (0, 0) := hbase.trans h.symm
          rw [hbzero] at hbcompat
          change (0 : ZMod 2) = 1 at hbcompat
          exact zero_ne_one hbcompat
        · have hbne : b ≠ (0, 0) := by
            intro hbzero
            rw [hbzero] at hbcompat
            change (0 : ZMod 2) = 1 at hbcompat
            exact zero_ne_one hbcompat
          have hpartner : tilingPartner t b = (0, 0) := by
            rw [hbase]
            exact h.symm
          have hineq := hb'.1.2.1
          have hne' : (0, 0) ≠ b := Ne.symm hbne
          have hall : ∀ j : Fin 1, pathPrefix s 0 j = (0, 0) := by
            intro j
            simpa only [Fin.eq_zero j] using hs0'
          have hnone : ∀ j : Fin 1, pathPrefix s 0 j ≠ b := by
            intro j
            rw [hall j]
            exact hne'
          simp [hpartner, hall, hnone] at hineq
          rw [if_neg hne'] at hineq
          exact Finset.not_nonempty_empty hineq

/-- Generic fixed-window selector package at a creation rank. -/
noncomputable def orientedTilingVTwoSupportSelectorData
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (window : Finset ℕ) (hzero : 0 ∉ window) :
    OrientedAllCreationSupportSelectorData t o m k
      (fun s n ↦ orientedTilingVTwoBases t o window s n) where
  measurableAtCreation := by
    exact measurable_natIndexed (creationTimeNat m k)
      (measurable_creationTimeNat m k)
      (fun n s ↦ orientedTilingVTwoBases t o window s n)
      (measurable_fixedOrientedTilingVTwoBases t o window)
  prefix_invariant := by
    intro s s' n hp
    rw [← prefixOrientedTilingVTwoBases_pathPrefix t o window n s,
      ← prefixOrientedTilingVTwoBases_pathPrefix t o window n s', hp]
  represented := fun s n hvalid ↦
    orientedTilingVTwoBases_subset_fixedExternalDominoBases
      t o window s n hvalid hzero

/-- Concrete selector for the exact source support `V₂(I₁)`. -/
noncomputable def orientedShellZeroSourceSupportSelectorData
    (t : DominoTiling) (o : Orientation) (m k : ℕ) :
    OrientedAllCreationSupportSelectorData t o m k
      (orientedShellZeroSourceSupportAt t o m) := by
  apply orientedTilingVTwoSupportSelectorData t o m k
    (shellZeroSourceTotalWindow m (shellWidth48 m))
  simp only [HLOZShellZeroReplacementWindows.mem_shellZeroSourceTotalWindow]
  omega

/-- Concrete selector for the common union support at the raised
fixed-central replacement rank. -/
noncomputable def orientedShellZeroReplacementSupportSelectorData
    (t : DominoTiling) (o : Orientation) (m rank : ℕ) :
    OrientedAllCreationSupportSelectorData t o m rank
      (orientedShellZeroReplacementSupportAt t o m) := by
  apply orientedTilingVTwoSupportSelectorData t o m rank
    (shellZeroSourceTotalWindow m (shellWidth48 m) ∪
      shellZeroReplacementTotalWindow m (shellWidth48 m))
  simp only [Finset.mem_union,
    HLOZShellZeroReplacementWindows.mem_shellZeroSourceTotalWindow,
    HLOZShellZeroReplacementWindows.mem_shellZeroReplacementTotalWindow]
  omega

/-- Fully concrete source-clock all-creation stopped-coordinate family. -/
noncomputable def orientedShellZeroSourceConcreteFamily
    (t : DominoTiling) (o : Orientation) (m k : ℕ) :
    OrientedAllCreationPrefixedStoppedCoordinateFamily t o m k
      (orientedShellZeroSourceSupportAt t o m) :=
  orientedAllCreationConcreteFamily t o m k
    (orientedShellZeroSourceSupportAt t o m)
    (orientedShellZeroSourceSupportSelectorData t o m k)

/-- Fully concrete replacement-clock all-creation stopped-coordinate
family, with the raised rank supplied explicitly. -/
noncomputable def orientedShellZeroReplacementConcreteFamily
    (t : DominoTiling) (o : Orientation) (m rank : ℕ) :
    OrientedAllCreationPrefixedStoppedCoordinateFamily t o m rank
      (orientedShellZeroReplacementSupportAt t o m) :=
  orientedAllCreationConcreteFamily t o m rank
    (orientedShellZeroReplacementSupportAt t o m)
    (orientedShellZeroReplacementSupportSelectorData t o m rank)

end

end Erdos1165.TilingOrientedShellSupportSelector
