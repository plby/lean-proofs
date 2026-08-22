/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaAcceptedCreationMass
import ErdosProblems.Erdos1165.TilingPrefixedFavoriteTraceSupport

/-!
# Path recovery for the accepted oriented Theta screen

The quantitative product estimate is useful only after the physical
creation atom has been identified with its finite away-total screen.  This
file supplies that deterministic identification.  In particular, the
external retained word is unchanged when insertion coordinates are
redistributed inside the same represented domino, while the creation clock
is recovered from the complete terminal local-time profile.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZSourceOrientedThetaAcceptedCreationPath

open HLOZPathEvents LazyDecomposition
open HLOZSourceOrientedThetaAcceptedCreation
open HLOZSourceOrientedThetaExternalProduct
open TilingCappedMarginalization TilingConditionalCappedMarginalization
open TilingDistinguishedTraceInvariant
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedAllRepresentedExternalFiber
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedPrefixedSupportBridge
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedFavoriteTraceSupport TilingPrefixedInsertedLocalTime
open TilingPrefixedStoppedProductDisintegration
open TilingLazyDecomposition TilingSpatialInsertionFiber
open TilingInsertionTerminalInvariant
open PreStoppingSpatialLaw
open PreStoppingFiber SpatialInsertionFiber StoppedInsertion VariableStoppedFiber
open PathInsertion
open TilingVariableStoppedTracePartition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

private abbrev Fiber
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SupportedIndex t o m k) := allRepresentedFiber eta

private theorem orientedExternalCode_eq_of_lists
    {t : DominoTiling} (z z' : OrientedTilingTypedExternalWordCode t)
    (hinitial : z.initial.1 = z'.initial.1)
    (hretained : List.ofFn z.retained.1 = List.ofFn z'.retained.1)
    (htail : z.tail.1 = z'.tail.1) : z = z' := by
  rcases z with ⟨initial, i, r, tail⟩
  rcases z' with ⟨initial', i', r', tail'⟩
  have hi : initial = initial' := Subtype.ext hinitial
  subst initial'
  have hii : i = i' := by
    simpa using congrArg List.length hretained
  subst i'
  have hr : r = r' := by
    apply Subtype.ext
    exact List.ofFn_injective hretained
  subst r'
  have ht : tail = tail' := Subtype.ext htail
  subst tail'
  rfl

private theorem fixedCode_even_prefixedInsertion
    {t : DominoTiling} (z : OrientedTilingTypedExternalWordCode t)
    (hinitial : z.initial.1 = [])
    (q : Fin (z.retainedCount + 1) → ℕ) :
    let v := prefixedTilingInsertionPrefixList z.initial.1 t z.start
      z.retained q z.tail.1
    fixedOrientedTypedExternalWordCode t .even v.length
        (trajectory (extendPrefix (directionVectorOfList v))) = z := by
  rcases z with ⟨initial, i, r, tail⟩
  have hi : initial = (⟨[], by simp⟩ : BoundaryTail) := by
    apply Subtype.ext
    exact hinitial
  subst initial
  let v := prefixedTilingInsertionPrefixList [] t
    (trajectory (extendPrefix (directionVectorOfList [])) 0) r q tail.1
  have hinc : incrementPrefixList v.length
      (stepsOfWalk (trajectory
        (extendPrefix (directionVectorOfList v)))) = v := by
    unfold incrementPrefixList
    rw [stepsOfWalk_trajectory, stepPrefix_extendPrefix,
      ofFn_directionVectorOfList]
  change fixedOrientedTypedExternalWordCode t .even v.length
      (trajectory (extendPrefix (directionVectorOfList v))) = _
  rw [fixedOrientedTypedExternalWordCode_eq_ofPrefix, hinc]
  unfold orientedTypedExternalWordCodeOfPrefix
  dsimp only
  have hpairs : pairDirectionList v = tilingInsertGapVector t
      (trajectory (extendPrefix (directionVectorOfList [])) 0) r q := by
    unfold v prefixedTilingInsertionPrefixList tilingInsertionPrefixList
    simp only [List.nil_append]
    exact pairDirectionList_flatten_append_shortTail _ tail.1 tail.2
  simp only [List.length_nil]
  rw [hpairs]
  apply orientedExternalCode_eq_of_lists
  · rfl
  · simp only [TilingTypedFavoriteTrace.deletedTilingRetainedWord,
      List.ofFn_get]
    exact deleteTilingBlocks_tilingInsertGapVector _ _ _ _
  · unfold v prefixedTilingInsertionPrefixList tilingInsertionPrefixList
    simp only [List.nil_append]
    exact unpairedDirectionTail_flatten_append_shortTail _ tail.1 tail.2

private theorem fixedCode_shifted_prefixedInsertion
    {t : DominoTiling} (z : OrientedTilingTypedExternalWordCode t)
    (hinitial : z.initial.1.length = 1)
    (q : Fin (z.retainedCount + 1) → ℕ) :
    let v := prefixedTilingInsertionPrefixList z.initial.1 t z.start
      z.retained q z.tail.1
    fixedOrientedTypedExternalWordCode t .shifted v.length
        (trajectory (extendPrefix (directionVectorOfList v))) = z := by
  rcases z with ⟨initial, i, r, tail⟩
  obtain ⟨d, hd⟩ := List.length_eq_one_iff.mp hinitial
  have hi : initial = (⟨[d], by simp⟩ : BoundaryTail) := by
    apply Subtype.ext
    exact hd
  subst initial
  let suffix := tilingInsertionPrefixList t
    (trajectory (extendPrefix (directionVectorOfList [d])) 1) r q tail.1
  let v := [d] ++ suffix
  have hinc : incrementPrefixList v.length
      (stepsOfWalk (trajectory
        (extendPrefix (directionVectorOfList v)))) = v := by
    unfold incrementPrefixList
    rw [stepsOfWalk_trajectory, stepPrefix_extendPrefix,
      ofFn_directionVectorOfList]
  change fixedOrientedTypedExternalWordCode t .shifted v.length
      (trajectory (extendPrefix (directionVectorOfList v))) = _
  rw [fixedOrientedTypedExternalWordCode_eq_ofPrefix, hinc]
  unfold orientedTypedExternalWordCodeOfPrefix
  dsimp only
  have htake : v.take 1 = [d] := by simp [v]
  have hdrop : v.drop 1 = suffix := by simp [v]
  have hpairs : pairDirectionList (v.drop 1) = tilingInsertGapVector t
      (trajectory (extendPrefix (directionVectorOfList [d])) 1) r q := by
    rw [hdrop]
    unfold suffix tilingInsertionPrefixList
    exact pairDirectionList_flatten_append_shortTail _ tail.1 tail.2
  apply orientedExternalCode_eq_of_lists
  · exact htake
  · simp only [TilingTypedFavoriteTrace.deletedTilingRetainedWord,
      List.ofFn_get]
    simp only [htake, List.length_singleton]
    rw [hpairs]
    exact deleteTilingBlocks_tilingInsertGapVector _ _ _ _
  · rw [hdrop]
    unfold suffix tilingInsertionPrefixList
    exact unpairedDirectionTail_flatten_append_shortTail _ tail.1 tail.2

/-- Every nonempty external creation atom is orientation-coherent.  Hence
reconstructing any insertion vector in its retained carrier gives back the
same oriented external word. -/
theorem fixedCode_prefixedInsertion
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SupportedIndex t o m k) (hm : 1 < m) (hk : 0 < k)
    (q : Fin (eta.1.retainedCount + 1) → ℕ) :
    let v := prefixedTilingInsertionPrefixList eta.1.initial.1 t eta.1.start
      eta.1.retained q eta.1.tail.1
    fixedOrientedTypedExternalWordCode t o v.length
        (trajectory (extendPrefix (directionVectorOfList v))) = eta.1 := by
  rcases eta.2 with ⟨s, hs⟩
  rw [allRepresentedExternalCreationTraceAtom] at hs
  have hcode := hs.2.2
  cases o with
  | even =>
      apply fixedCode_even_prefixedInsertion
      have hinitial := congrArg
        (fun z : OrientedTilingTypedExternalWordCode t ↦ z.initial.1) hcode
      simpa [fixedOrientedTypedExternalWordCode, orientedInitialPrefix] using
        hinitial.symm
  | shifted =>
      apply fixedCode_shifted_prefixedInsertion
      have hcreation : ThresholdCreation s m k (creationTimeNat m k s) := by
        simpa [creationTimeNat, hs.2.1] using thresholdCreation_natFind hs.2.1
      have hnpos : 0 < creationTimeNat m k s := by
        by_contra hn
        have hnzero : creationTimeNat m k s = 0 := Nat.eq_zero_of_not_pos hn
        have hlocal := position_mem_thresholdSites_of_creation hk hcreation
        have hle := (mem_thresholdSites s _ m _).mp hlocal |>.2
        have hlocalZero : localTime s 0 (s 0) = 1 := by
          unfold localTime localTimePrefix pathPrefix
          simp
        rw [hnzero, hlocalZero] at hle
        omega
      have hinitial := congrArg
        (fun z : OrientedTilingTypedExternalWordCode t ↦ z.initial.1.length)
          hcode
      have hwordLength :
          (incrementPrefixList (creationTimeNat m k s)
            (stepsOfWalk s)).length = creationTimeNat m k s := by
        simp [incrementPrefixList]
      calc
        eta.1.initial.1.length =
            (fixedOrientedTypedExternalWordCode t .shifted
              (creationTimeNat m k s) s).initial.1.length := hinitial.symm
        _ = ((incrementPrefixList (creationTimeNat m k s)
              (stepsOfWalk s)).take 1).length := rfl
        _ = 1 := by rw [List.length_take, hwordLength]; omega

private theorem finitePathList_getLast?
    (s : WalkPath) (n : ℕ) :
    (finitePathList (pathPrefix s n)).getLast? = some (s n) := by
  unfold finitePathList pathPrefix
  rw [List.ofFn_succ_last, List.getLast?_concat]
  congr 2

private theorem trajectory_append_left (v tail : List Direction) :
    trajectory (extendPrefix (directionVectorOfList (v ++ tail))) v.length =
      trajectory (extendPrefix (directionVectorOfList v)) v.length := by
  unfold trajectory
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < v.length := Finset.mem_range.mp hj
  have hjapp : j < (v ++ tail).length := by simp; omega
  simp only [extendPrefix, hjlt, hjapp, dif_pos]
  congr 1
  simp only [directionVectorOfList, List.get_eq_getElem]
  rw [List.getElem_append_left hjlt]

private theorem blockPath_getLast? (x : Point) (bs : List Block) :
    (blockPath x bs).getLast? = some (followBlocks x bs) := by
  induction bs generalizing x with
  | nil => simp [blockPath, blockPathTail, followBlocks]
  | cons b bs ih =>
      simpa [blockPath, blockPathTail, followBlocks] using ih (blockEnd x b)

private theorem getLast?_append_tail_eq
    {alpha : Type*} {as bs : List alpha} {x : alpha}
    (has : as.getLast? = some x) (hbs : bs.head? = some x) :
    (as ++ bs.tail).getLast? = bs.getLast? := by
  cases bs with
  | nil => simp at hbs
  | cons y ys =>
      simp only [List.head?_cons, Option.some.injEq] at hbs
      subst y
      cases ys with
      | nil => simpa using has
      | cons z zs =>
          have hne : z :: zs ≠ [] := by simp
          rw [List.getLast?_append]
          change (z :: zs).getLast?.or as.getLast? = (z :: zs).getLast?
          rw [List.getLast?_eq_some_getLast hne]
          simp

private theorem prefixed_endpoint_eq_no_tail
    (initial : BoundaryTail) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q q' : Fin (i + 1) → ℕ)
    (hstart : trajectory
      (extendPrefix (directionVectorOfList initial.1)) initial.1.length = x) :
    let v := prefixedTilingInsertionPrefixList initial.1 t x r q []
    let v' := prefixedTilingInsertionPrefixList initial.1 t x r q' []
    trajectory (extendPrefix (directionVectorOfList v)) v.length =
      trajectory (extendPrefix (directionVectorOfList v')) v'.length := by
  let emptyTail : BoundaryTail := ⟨[], by simp⟩
  let v := prefixedTilingInsertionPrefixList initial.1 t x r q []
  let v' := prefixedTilingInsertionPrefixList initial.1 t x r q' []
  have hpath := finitePathList_prefixedTilingInsertionPrefix
    initial t x r q emptyTail hstart
  have hpath' := finitePathList_prefixedTilingInsertionPrefix
    initial t x r q' emptyTail hstart
  have hlast := congrArg List.getLast? hpath
  have hlast' := congrArg List.getLast? hpath'
  have hinitialLast :
      (finitePathList (pathPrefix
        (trajectory (extendPrefix (directionVectorOfList initial.1)))
          initial.1.length)).getLast? = some x := by
    rw [finitePathList_getLast?, hstart]
  have hjoin := getLast?_append_tail_eq hinitialLast
    (show (blockPath x (tilingInsertGapVector t x r q)).head? =
      some x by simp [blockPath])
  have hjoin' := getLast?_append_tail_eq hinitialLast
    (show (blockPath x (tilingInsertGapVector t x r q')).head? =
      some x by simp [blockPath])
  change trajectory (extendPrefix (directionVectorOfList v)) v.length =
    trajectory (extendPrefix (directionVectorOfList v')) v'.length
  have hq : some
      (trajectory (extendPrefix (directionVectorOfList v)) v.length) =
        some (followBlocks x (List.ofFn r.1)) := by
    have hlastClean :
        (finitePathList (pathPrefix
          (trajectory (extendPrefix (directionVectorOfList v)))
            v.length)).getLast? =
          (finitePathList (pathPrefix
            (trajectory (extendPrefix
              (directionVectorOfList initial.1))) initial.1.length) ++
            (blockPath x (tilingInsertGapVector t x r q)).tail).getLast? := by
      simpa only [emptyTail, prefixedTilingInsertionTerminal,
        prefixedTilingPrefixPointPath,
        TilingInsertedLocalTime.tilingPrefixPointPath] using hlast
    rw [finitePathList_getLast?, hjoin, blockPath_getLast?,
      followBlocks_tilingInsertGapVector] at hlastClean
    exact hlastClean
  have hq' : some
      (trajectory (extendPrefix (directionVectorOfList v')) v'.length) =
        some (followBlocks x (List.ofFn r.1)) := by
    have hlastClean :
        (finitePathList (pathPrefix
          (trajectory (extendPrefix (directionVectorOfList v')))
            v'.length)).getLast? =
          (finitePathList (pathPrefix
            (trajectory (extendPrefix
              (directionVectorOfList initial.1))) initial.1.length) ++
            (blockPath x (tilingInsertGapVector t x r q')).tail).getLast? := by
      simpa only [emptyTail, prefixedTilingInsertionTerminal,
        prefixedTilingPrefixPointPath,
        TilingInsertedLocalTime.tilingPrefixPointPath] using hlast'
    rw [finitePathList_getLast?, hjoin', blockPath_getLast?,
      followBlocks_tilingInsertGapVector] at hlastClean
    exact hlastClean
  exact Option.some.inj (hq.trans hq'.symm)

private theorem prefixed_endpoint_eq_of_coordinates
    (initial : BoundaryTail) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q q' : Fin (i + 1) → ℕ)
    (tail : BoundaryTail)
    (hstart : trajectory
      (extendPrefix (directionVectorOfList initial.1)) initial.1.length = x) :
    let v := prefixedTilingInsertionPrefixList initial.1 t x r q tail.1
    let v' := prefixedTilingInsertionPrefixList initial.1 t x r q' tail.1
    trajectory (extendPrefix (directionVectorOfList v)) v.length =
      trajectory (extendPrefix (directionVectorOfList v')) v'.length := by
  rcases tail with ⟨tailList, htail⟩
  cases tailList with
  | nil => exact prefixed_endpoint_eq_no_tail initial t x r q q' hstart
  | cons d ds =>
      cases ds with
      | nil =>
          let v0 := prefixedTilingInsertionPrefixList initial.1 t x r q []
          let v0' := prefixedTilingInsertionPrefixList initial.1 t x r q' []
          let v := prefixedTilingInsertionPrefixList initial.1 t x r q [d]
          let v' := prefixedTilingInsertionPrefixList initial.1 t x r q' [d]
          have hv : v = v0 ++ [d] := by
            simp [v, v0, prefixedTilingInsertionPrefixList,
              tilingInsertionPrefixList]
          have hv' : v' = v0' ++ [d] := by
            simp [v', v0', prefixedTilingInsertionPrefixList,
              tilingInsertionPrefixList]
          have hbase := prefixed_endpoint_eq_no_tail
            initial t x r q q' hstart
          change trajectory (extendPrefix (directionVectorOfList v)) v.length =
            trajectory (extendPrefix (directionVectorOfList v')) v'.length
          rw [hv, hv']
          simp only [List.length_append, List.length_singleton,
            trajectory_succ]
          have hstep :
              extendPrefix (directionVectorOfList (v0 ++ [d])) v0.length = d := by
            simp [extendPrefix, directionVectorOfList]
          have hstep' :
              extendPrefix (directionVectorOfList (v0' ++ [d])) v0'.length = d := by
            simp [extendPrefix, directionVectorOfList]
          rw [hstep, hstep']
          rw [trajectory_append_left v0 [d],
            trajectory_append_left v0' [d]]
          exact congrArg (fun y ↦ y + directionVector d) hbase
      | cons e es => simp at htail

private theorem prefixed_terminal_eq_of_coordinates
    (initial : BoundaryTail) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q q' : Fin (i + 1) → ℕ)
    (tail : BoundaryTail)
    (hstart : trajectory
      (extendPrefix (directionVectorOfList initial.1)) initial.1.length = x) :
    prefixedTilingInsertionTerminal initial t x r q tail =
      prefixedTilingInsertionTerminal initial t x r q' tail := by
  rcases tail with ⟨tailList, htail⟩
  cases tailList with
  | nil => rfl
  | cons d ds =>
      cases ds with
      | nil =>
          unfold prefixedTilingInsertionTerminal
          exact congrArg some
            (prefixed_endpoint_eq_of_coordinates initial t x r q q'
              ⟨[d], htail⟩ hstart)
      | cons e es => simp at htail

private theorem prefixed_localTime_eq_of_dominoTotals
    (initial : BoundaryTail) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q q' : Fin (i + 1) → ℕ)
    (terminal : Option Point)
    (htotal : ∀ b : TilingExternalDomino t x r,
      tilingDominoTotal t x r q b = tilingDominoTotal t x r q' b)
    (y : Point) :
    listLocalTime
        (prefixedTilingPrefixPointPath initial.1 x
          (tilingInsertGapVector t x r q) terminal) y =
      listLocalTime
        (prefixedTilingPrefixPointPath initial.1 x
          (tilingInsertGapVector t x r q') terminal) y := by
  by_cases hy : tilingBase t y ∈ tilingExternalDominoBases t x r
  · let b : TilingExternalDomino t x r := ⟨tilingBase t y, hy⟩
    rw [prefixedTilingInsertedPrefix_localTime_at_dominoPoint
        initial.1 t x r q terminal b y rfl,
      prefixedTilingInsertedPrefix_localTime_at_dominoPoint
        initial.1 t x r q' terminal b y rfl,
      htotal b]
  · rw [prefixedTilingInsertedPrefix_localTime_of_base_not_mem
        initial.1 t x r q terminal y hy,
      prefixedTilingInsertedPrefix_localTime_of_base_not_mem
        initial.1 t x r q' terminal y hy]

private theorem prefixed_length_eq_of_dominoTotals
    (initial : List Direction) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q q' : Fin (i + 1) → ℕ)
    (tail : List Direction)
    (htotal : ∀ b : TilingExternalDomino t x r,
      tilingDominoTotal t x r q b = tilingDominoTotal t x r q' b) :
    (prefixedTilingInsertionPrefixList initial t x r q tail).length =
      (prefixedTilingInsertionPrefixList initial t x r q' tail).length := by
  have hsum : ∑ j, q j = ∑ j, q' j := by
    calc
      ∑ j, q j = ∑ b : TilingExternalDomino t x r,
          tilingDominoTotal t x r q b :=
        (sum_tilingDominoTotal t x r q).symm
      _ = ∑ b : TilingExternalDomino t x r,
          tilingDominoTotal t x r q' b := by
        apply Finset.sum_congr rfl
        intro b _hb
        exact htotal b
      _ = ∑ j, q' j := sum_tilingDominoTotal t x r q'
  simp only [prefixedTilingInsertionPrefixList_length, hsum]

private theorem canonical_localTime_eq_of_dominoTotals
    (initial : BoundaryTail) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q q' : Fin (i + 1) → ℕ)
    (tail : BoundaryTail)
    (hstart : trajectory
      (extendPrefix (directionVectorOfList initial.1)) initial.1.length = x)
    (htotal : ∀ b : TilingExternalDomino t x r,
      tilingDominoTotal t x r q b = tilingDominoTotal t x r q' b)
    (y : Point) :
    let v := prefixedTilingInsertionPrefixList initial.1 t x r q tail.1
    let v' := prefixedTilingInsertionPrefixList initial.1 t x r q' tail.1
    localTime (trajectory (extendPrefix (directionVectorOfList v)))
        v.length y =
      localTime (trajectory (extendPrefix (directionVectorOfList v')))
        v'.length y := by
  let terminal := prefixedTilingInsertionTerminal initial t x r q tail
  let v := prefixedTilingInsertionPrefixList initial.1 t x r q tail.1
  let v' := prefixedTilingInsertionPrefixList initial.1 t x r q' tail.1
  have hpath := finitePathList_prefixedTilingInsertionPrefix
    initial t x r q tail hstart
  have hpath' := finitePathList_prefixedTilingInsertionPrefix
    initial t x r q' tail hstart
  have hterminal := prefixed_terminal_eq_of_coordinates
    initial t x r q q' tail hstart
  change localTime (trajectory (extendPrefix (directionVectorOfList v)))
      v.length y =
    localTime (trajectory (extendPrefix (directionVectorOfList v')))
      v'.length y
  rw [localTime_eq_listLocalTime, localTime_eq_listLocalTime, hpath, hpath']
  change listLocalTime
      (prefixedTilingPrefixPointPath initial.1 x
        (tilingInsertGapVector t x r q) terminal) y = _
  rw [← hterminal]
  exact prefixed_localTime_eq_of_dominoTotals
    initial t x r q q' terminal htotal y

private theorem thresholdCreation_of_dominoTotals
    (initial : BoundaryTail) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q q' : Fin (i + 1) → ℕ)
    (tail : BoundaryTail) (m k : ℕ) (hm : 1 < m) (hk : 0 < k)
    (hstart : trajectory
      (extendPrefix (directionVectorOfList initial.1)) initial.1.length = x)
    (htotal : ∀ b : TilingExternalDomino t x r,
      tilingDominoTotal t x r q b = tilingDominoTotal t x r q' b)
    (hcreation :
      let v := prefixedTilingInsertionPrefixList initial.1 t x r q tail.1
      ThresholdCreation (trajectory
        (extendPrefix (directionVectorOfList v))) m k v.length) :
    let v' := prefixedTilingInsertionPrefixList initial.1 t x r q' tail.1
    ThresholdCreation (trajectory
      (extendPrefix (directionVectorOfList v'))) m k v'.length := by
  let v := prefixedTilingInsertionPrefixList initial.1 t x r q tail.1
  let v' := prefixedTilingInsertionPrefixList initial.1 t x r q' tail.1
  let s := trajectory (extendPrefix (directionVectorOfList v))
  let s' := trajectory (extendPrefix (directionVectorOfList v'))
  have hlen : v.length = v'.length :=
    prefixed_length_eq_of_dominoTotals initial.1 t x r q q' tail.1 htotal
  have hnpos : 0 < v.length := by
    by_contra hn
    have hnzero : v.length = 0 := Nat.eq_zero_of_not_pos hn
    have hlocal := position_mem_thresholdSites_of_creation hk hcreation
    have hle := (mem_thresholdSites s v.length m (s v.length)).mp hlocal |>.2
    have hlocalZero : localTime s 0 (s 0) = 1 := by
      unfold localTime localTimePrefix pathPrefix
      simp
    rw [hnzero, hlocalZero] at hle
    omega
  have hterminal :=
    (thresholdCreation_iff_terminal_count_and_new_localTime
      s m k v.length (by omega) hk hnpos).mp hcreation
  have hlocal : ∀ y,
      localTime s v.length y = localTime s' v'.length y := by
    intro y
    exact canonical_localTime_eq_of_dominoTotals
      initial t x r q q' tail hstart htotal y
  have hsites : thresholdSites s v.length m = thresholdSites s' v'.length m := by
    ext y
    rw [mem_thresholdSites_iff s v.length m y (by omega),
      mem_thresholdSites_iff s' v'.length m y (by omega), hlocal y]
  have hcount : thresholdCount s' v'.length m = k := by
    unfold thresholdCount
    rw [← hsites]
    exact hterminal.1
  have hendpoint : s v.length = s' v'.length :=
    prefixed_endpoint_eq_of_coordinates initial t x r q q' tail hstart
  have hnew : localTime s' v'.length (s' v'.length) = m := by
    rw [← hendpoint, ← hlocal (s v.length)]
    exact hterminal.2
  exact (thresholdCreation_iff_terminal_count_and_new_localTime
    s' m k v'.length (by omega) hk (by omega)).mpr ⟨hcount, hnew⟩

private theorem prefixedStoppingAccepted_of_dominoTotals
    (initial : BoundaryTail) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q q' : Fin (i + 1) → ℕ)
    (tail : BoundaryTail) (m k cutoff : ℕ) (hm : 1 < m) (hk : 0 < k)
    (hstart : trajectory
      (extendPrefix (directionVectorOfList initial.1)) initial.1.length = x)
    (htotal : ∀ b : TilingExternalDomino t x r,
      tilingDominoTotal t x r q b = tilingDominoTotal t x r q' b)
    (hlt : (prefixedTilingInsertionPrefixList initial.1 t x r q tail.1).length <
      cutoff)
    (hlt' : (prefixedTilingInsertionPrefixList initial.1 t x r q' tail.1).length <
      cutoff)
    (haccepted : PrefixedTilingStoppingAccepted
      (truncatedLevelTime m k cutoff) initial.1 t x r q tail.1) :
    PrefixedTilingStoppingAccepted
      (truncatedLevelTime m k cutoff) initial.1 t x r q' tail.1 := by
  let v := prefixedTilingInsertionPrefixList initial.1 t x r q tail.1
  let v' := prefixedTilingInsertionPrefixList initial.1 t x r q' tail.1
  have hcreation : ThresholdCreation
      (trajectory (extendPrefix (directionVectorOfList v))) m k v.length :=
    (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m k cutoff v.length _ hlt).mp haccepted
  have hcreation' := thresholdCreation_of_dominoTotals
    initial t x r q q' tail m k hm hk hstart htotal hcreation
  exact (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
    m k cutoff v'.length _ hlt').mpr hcreation'

/-- On an all-represented external-word fibre, stopping acceptance and the
fixed retained word already force the full stopped cylinder into the exact
external creation atom. -/
theorem allRepresented_atomPredicate_of_accepted
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SupportedIndex t o m k) (hm : 1 < m) (hk : 0 < k)
    (cap : ℕ)
    (q : TilingCappedCoordinates eta.1.retainedCount
      ((Fiber eta).coordinateCap cap))
    (haccepted : PrefixedTilingStoppingAccepted
      ((Fiber eta).stoppingTime cap) eta.1.initial.1 t eta.1.start
        eta.1.retained (fun j ↦ (q j : ℕ)) eta.1.tail.1) :
    (Fiber eta).atomPredicate cap q := by
  let z := eta.1
  let actualCap := (Fiber eta).coordinateCap cap
  let qNat : Fin (z.retainedCount + 1) → ℕ := fun j ↦ (q j : ℕ)
  let v := prefixedTilingInsertionPrefixList z.initial.1 t z.start
    z.retained qNat z.tail.1
  let s := trajectory (extendPrefix (directionVectorOfList v))
  let favorite := (fixedOrientedAllCreationTraceCode t o v.length s).favorite
  have hlt : v.length < externalCoordinateCutoff z actualCap := by
    have hraw := prefixedInsertion_lt_orientedAllCreationCoordinateCutoff
      (withFavorite z favorite) actualCap q
    rw [orientedAllCreationCoordinateCutoff_withFavorite] at hraw
    exact hraw
  have hstop : (Fiber eta).stoppingTime cap =
      truncatedLevelTime m k (externalCoordinateCutoff z actualCap) := by
    rfl
  have hcreation : ThresholdCreation s m k v.length := by
    apply (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m k (externalCoordinateCutoff z actualCap) v.length _ hlt).mp
    rw [hstop] at haccepted
    exact haccepted
  have hcode : fixedOrientedTypedExternalWordCode t o v.length s = z := by
    simpa only [z, v, s, qNat] using
      fixedCode_prefixedInsertion eta hm hk qNat
  change externalStoppedAtomPredicate o m k
    (allRepresentedSupportAt t o)
    (tilingExternalDominoBases t z.start z.retained) z actualCap q
  refine ⟨favorite, ?_⟩
  intro omega homega
  let somega := trajectory omega
  have hp : pathPrefix somega v.length = pathPrefix s v.length := by
    simpa only [somega, s, v, qNat, z] using
      (pathPrefix_eq_canonical_of_mem_prefixedTilingStoppedInsertionAtom
        z.initial.1 z.start z.retained qNat z.tail.1 omega homega)
  have homegaCreation : ThresholdCreation somega m k v.length :=
    (thresholdCreation_iff_of_pathPrefix_eq hp
      (Nat.le_refl v.length)).mpr hcreation
  have homegaTime : creationTimeNat m k somega = v.length :=
    creationTimeNat_eq_of_creation homegaCreation
  refine ⟨⟨trajectory_mem_validStepWalk omega,
    ⟨v.length, homegaCreation.1⟩, ?_⟩, ?_⟩
  · change fixedOrientedAllCreationTraceCode t o
      (creationTimeNat m k somega) somega = withFavorite z favorite
    rw [homegaTime]
    have htrace := fixedOrientedAllCreationTraceCode_eq_of_pathPrefix_eq
      t o hp
    calc
      fixedOrientedAllCreationTraceCode t o v.length somega =
      fixedOrientedAllCreationTraceCode t o v.length s := htrace
      _ = withFavorite z favorite := by
        rw [OrientedAllCreationTraceCode.mk.injEq]
        exact ⟨hcode, rfl⟩
  · change allRepresentedSupportAt t o somega
      (creationTimeNat m k somega) =
        tilingExternalDominoBases t z.start z.retained
    rw [homegaTime]
    unfold allRepresentedSupportAt
    rw [fixedOrientedTypedExternalWordCode_eq_of_pathPrefix_eq t o hp, hcode]

/-- The actual total vector of an accepted all-represented coordinate is an
honest accepted-creation class: every redistribution with the same domino
totals has the same terminal rank-creation profile. -/
theorem acceptedCreationAtTotals_of_coordinates
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SupportedIndex t o m k) (hm : 1 < m) (hk : 0 < k)
    (cap : ℕ)
    (q : TilingCappedCoordinates eta.1.retainedCount
      ((Fiber eta).coordinateCap cap))
    (haccepted : PrefixedTilingStoppingAccepted
      ((Fiber eta).stoppingTime cap) eta.1.initial.1 t eta.1.start
        eta.1.retained (fun j ↦ (q j : ℕ)) eta.1.tail.1)
    (ell : FiniteDominoProductLaw.TruncatedTotals ((Fiber eta).upper cap))
    (hell : ∀ b, tilingAwayTotal t eta.1.start eta.1.retained
      (supportComplementDistinguished t eta.1.start eta.1.retained
        (tilingExternalDominoBases t eta.1.start eta.1.retained))
      ((splitTilingCoordinatesEquiv t eta.1.start eta.1.retained
        (supportComplementDistinguished t eta.1.start eta.1.retained
          (tilingExternalDominoBases t eta.1.start eta.1.retained)) q).2) b =
        ell b) :
    acceptedCreationAtTotals eta cap ell := by
  intro q' _hselected htotal'
  let D := supportComplementDistinguished t eta.1.start eta.1.retained
    (tilingExternalDominoBases t eta.1.start eta.1.retained)
  have hD : D = ∅ := by
    exact allRepresentedFiber_distinguished eta
  have htotals : ∀ b : TilingExternalDomino t eta.1.start eta.1.retained,
      tilingDominoTotal t eta.1.start eta.1.retained
          (fun j ↦ (q j : ℕ)) b =
        tilingDominoTotal t eta.1.start eta.1.retained
          (fun j ↦ (q' j : ℕ)) b := by
    intro b
    let ba : TilingAwayDomino t eta.1.start eta.1.retained D :=
      ⟨b, by simp [hD]⟩
    calc
      tilingDominoTotal t eta.1.start eta.1.retained
          (fun j ↦ (q j : ℕ)) b =
          tilingAwayTotal t eta.1.start eta.1.retained D
            ((splitTilingCoordinatesEquiv t eta.1.start eta.1.retained
              D q).2) ba := by
        symm
        exact tilingAwayTotal_split_eq_dominoTotal
          t eta.1.start eta.1.retained D q ba
      _ = ell ba := by
        simpa only [D] using hell ba
      _ = tilingAwayTotal t eta.1.start eta.1.retained D
            ((splitTilingCoordinatesEquiv t eta.1.start eta.1.retained
              D q').2) ba := by
        symm
        simpa only [D] using htotal' ba
      _ = tilingDominoTotal t eta.1.start eta.1.retained
          (fun j ↦ (q' j : ℕ)) b :=
        tilingAwayTotal_split_eq_dominoTotal
          t eta.1.start eta.1.retained D q' ba
  let actualCap := (Fiber eta).coordinateCap cap
  let dummy : TilingCreationFavoriteData :=
    ((∅, ∅), (eta.1.start, eta.1.start))
  have hlt : (prefixedTilingInsertionPrefixList eta.1.initial.1 t
      eta.1.start eta.1.retained (fun j ↦ (q j : ℕ))
      eta.1.tail.1).length < externalCoordinateCutoff eta.1 actualCap := by
    have hraw := prefixedInsertion_lt_orientedAllCreationCoordinateCutoff
      (withFavorite eta.1 dummy) actualCap q
    rw [orientedAllCreationCoordinateCutoff_withFavorite] at hraw
    exact hraw
  have hlt' : (prefixedTilingInsertionPrefixList eta.1.initial.1 t
      eta.1.start eta.1.retained (fun j ↦ (q' j : ℕ))
      eta.1.tail.1).length < externalCoordinateCutoff eta.1 actualCap := by
    have hraw := prefixedInsertion_lt_orientedAllCreationCoordinateCutoff
      (withFavorite eta.1 dummy) actualCap q'
    rw [orientedAllCreationCoordinateCutoff_withFavorite] at hraw
    exact hraw
  have hstart : trajectory
      (extendPrefix (directionVectorOfList eta.1.initial.1))
        eta.1.initial.1.length = eta.1.start := rfl
  have hstop : (Fiber eta).stoppingTime cap =
      truncatedLevelTime m k (externalCoordinateCutoff eta.1 actualCap) := by
    rfl
  have haccepted' : PrefixedTilingStoppingAccepted
      ((Fiber eta).stoppingTime cap) eta.1.initial.1 t eta.1.start
        eta.1.retained (fun j ↦ (q' j : ℕ)) eta.1.tail.1 := by
    rw [hstop] at haccepted ⊢
    exact prefixedStoppingAccepted_of_dominoTotals
      eta.1.initial t eta.1.start eta.1.retained
      (fun j ↦ (q j : ℕ)) (fun j ↦ (q' j : ℕ)) eta.1.tail
      m k (externalCoordinateCutoff eta.1 actualCap) hm hk hstart htotals
      hlt hlt' haccepted
  exact ⟨allRepresented_atomPredicate_of_accepted
    eta hm hk cap q' haccepted', haccepted'⟩

/-- A physical accepted coordinate whose actual total vector lies in the
absolute Theta union belongs to the honest accepted-Theta stopped screen. -/
theorem acceptedThetaPredicate_of_coordinates
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    (eta : SupportedIndex t o m k) (hm : 1 < m) (hk : 0 < k)
    (w externalLow externalHigh cap : ℕ)
    (q : TilingCappedCoordinates eta.1.retainedCount
      ((Fiber eta).coordinateCap cap))
    (haccepted : PrefixedTilingStoppingAccepted
      ((Fiber eta).stoppingTime cap) eta.1.initial.1 t eta.1.start
        eta.1.retained (fun j ↦ (q j : ℕ)) eta.1.tail.1)
    (ell : FiniteDominoProductLaw.TruncatedTotals ((Fiber eta).upper cap))
    (hell : ∀ b, tilingAwayTotal t eta.1.start eta.1.retained
      (supportComplementDistinguished t eta.1.start eta.1.retained
        (tilingExternalDominoBases t eta.1.start eta.1.retained))
      ((splitTilingCoordinatesEquiv t eta.1.start eta.1.retained
        (supportComplementDistinguished t eta.1.start eta.1.retained
          (tilingExternalDominoBases t eta.1.start eta.1.retained)) q).2) b =
        ell b)
    (htheta : externalThetaAccepts (Fiber eta) w externalLow externalHigh
      cap ell = true) :
    acceptedThetaPredicate eta w externalLow externalHigh cap q := by
  refine ⟨allRepresented_atomPredicate_of_accepted
    eta hm hk cap q haccepted, ?_⟩
  exact ⟨ell, ⟨acceptedCreationAtTotals_of_coordinates
    eta hm hk cap q haccepted ell hell, htheta⟩, hell⟩

end

end Erdos1165.HLOZSourceOrientedThetaAcceptedCreationPath
