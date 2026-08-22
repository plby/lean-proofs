/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingFavoriteTraceSupport
import ErdosProblems.Erdos1165.TilingOrientedPrefixedSupportBridge
import ErdosProblems.Erdos1165.TilingPrefixedInsertedLocalTime

/-!
# Distinguished-coordinate invariance on physical prefixed tiling fibres

The origin-started favorite-trace invariance lemmas do not apply directly to
the shifted oriented fibres: those fibres contain a genuine initial direction
word.  This file supplies the path reconstruction and the first local-time
invariance layer with that prefix retained literally.
-/

open Set

namespace Erdos1165.TilingPrefixedFavoriteTraceSupport

open LazyDecomposition PathInsertion PreStoppingFiber SpatialInsertionFiber
open PreStoppingSpatialLaw
open StoppedInsertion VariableStoppedFiber VariableStoppedTracePartition
open ShiftedPrefixBridge
open TilingCappedMarginalization TilingFavoriteTraceSupport
open TilingInsertedLocalTime TilingInsertionTerminalInvariant
open TilingLazyDecomposition TilingOrientedPrefixedSupportBridge
open TilingPrefixedInsertedLocalTime
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber
open TilingStoppedAcceptanceFactorization

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Split a finite point prefix at an arbitrary deterministic time.  The
joining point occurs in the left prefix, so the segment contributes its
tail. -/
theorem finitePathList_add_eq_append_segmentPath_tail
    (omega : StepPath) (a n : Nat) :
    finitePathList (pathPrefix (trajectory omega) (a + n)) =
      finitePathList (pathPrefix (trajectory omega) a) ++
        (segmentPath omega a n).tail := by
  unfold finitePathList pathPrefix segmentPath
  rw [show a + n + 1 = (a + 1) + n by omega, List.ofFn_add]
  have htail :
      (List.ofFn fun j : Fin (n + 1) ↦ trajectory omega (a + (j : Nat))).tail =
        List.ofFn fun j : Fin n ↦ trajectory omega (a + (j : Nat) + 1) := by
    rw [List.ofFn_succ]
    rfl
  rw [htail]
  congr 1
  exact congrArg List.ofFn (by
    funext j
    change trajectory omega ((a + 1) + (j : Nat)) =
      trajectory omega (a + (j : Nat) + 1)
    congr 1
    omega)

/-- The physical terminal singleton is independent of the insertion totals.
It is expressed relative to the retained endpoint chain rather than by
running an origin-started suffix in isolation. -/
def prefixedTilingInsertionTerminal (initial : BoundaryTail) {i : Nat}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (q : Fin (i + 1) → Nat) (tail : BoundaryTail) : Option Point :=
  match tail.1 with
  | [] => none
  | _ :: _ =>
      let v := prefixedTilingInsertionPrefixList initial.1 t x r q tail.1
      some (trajectory (extendPrefix (directionVectorOfList v)) v.length)

/-- Exact point-list reconstruction of a physically prefixed tiling word.
The hypothesis on `x` says that the retained suffix starts at the endpoint
of the displayed initial word. -/
theorem finitePathList_prefixedTilingInsertionPrefix
    (initial : BoundaryTail) {i : Nat} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q : Fin (i + 1) → Nat)
    (tail : BoundaryTail)
    (hstart : trajectory
      (extendPrefix (directionVectorOfList initial.1)) initial.1.length = x) :
    let v := prefixedTilingInsertionPrefixList initial.1 t x r q tail.1
    finitePathList
        (pathPrefix (trajectory
          (extendPrefix (directionVectorOfList v))) v.length) =
      prefixedTilingPrefixPointPath initial.1 x
        (tilingInsertGapVector t x r q)
        (prefixedTilingInsertionTerminal initial t x r q tail) := by
  rcases tail with ⟨tailList, htailShort⟩
  let suffix := tilingInsertionPrefixList t x r q tailList
  let v := prefixedTilingInsertionPrefixList initial.1 t x r q tailList
  let omega := extendPrefix (directionVectorOfList v)
  have hv : v = initial.1 ++ suffix := rfl
  have hvlen : v.length = initial.1.length + suffix.length := by
    rw [hv, List.length_append]
  have homegaStart : trajectory omega initial.1.length = x := by
    change trajectory
        (extendPrefix (directionVectorOfList (initial.1 ++ suffix)))
          initial.1.length = x
    calc
      trajectory
          (extendPrefix (directionVectorOfList (initial.1 ++ suffix)))
            initial.1.length =
          trajectory (extendPrefix (directionVectorOfList initial.1))
            initial.1.length := by
        unfold trajectory
        apply Finset.sum_congr rfl
        intro j hj
        have hjlt : j < initial.1.length := Finset.mem_range.mp hj
        have hjapp : j < (initial.1 ++ suffix).length := by simp; omega
        simp only [extendPrefix, hjlt, hjapp, dif_pos]
        congr 1
        simp only [directionVectorOfList, List.get_eq_getElem]
        rw [List.getElem_append_left hjlt]
      _ = x := hstart
  have hprefix : finitePathList
      (pathPrefix (trajectory omega) initial.1.length) =
      finitePathList (pathPrefix
        (trajectory (extendPrefix (directionVectorOfList initial.1)))
          initial.1.length) := by
    have hstep : stepPrefix initial.1.length omega =
        directionVectorOfList initial.1 := by
      funext j
      simp only [stepPrefix, omega, extendPrefix]
      have hjv : (j : Nat) < v.length := by rw [hvlen]; omega
      rw [dif_pos hjv]
      unfold directionVectorOfList
      simp only [List.get_eq_getElem]
      unfold v prefixedTilingInsertionPrefixList
      rw [List.getElem_append_left j.isLt]
    congr 1
    calc
      pathPrefix (trajectory omega) initial.1.length =
          trajectoryPrefix (stepPrefix initial.1.length omega) :=
        (trajectoryPrefix_stepPrefix omega initial.1.length).symm
      _ = trajectoryPrefix (directionVectorOfList initial.1) := by
        rw [hstep]
      _ = pathPrefix
          (trajectory (extendPrefix (directionVectorOfList initial.1)))
            initial.1.length := by
        simpa only [stepPrefix_extendPrefix] using
          trajectoryPrefix_stepPrefix
            (extendPrefix (directionVectorOfList initial.1)) initial.1.length
  have hblocks : completeSegmentBlocks omega initial.1.length suffix.length =
      tilingInsertGapVector t x r q := by
    calc
      completeSegmentBlocks omega initial.1.length suffix.length =
          pairDirectionList suffix := by
        change completeSegmentBlocks
            (extendPrefix (directionVectorOfList v)) initial.1.length
              suffix.length = pairDirectionList suffix
        rw [hv]
        exact completeSegmentBlocks_extendPrefix_append initial.1 suffix
      _ = tilingInsertGapVector t x r q := by
        unfold suffix tilingInsertionPrefixList
        exact pairDirectionList_flatten_append_shortTail
          (tilingInsertGapVector t x r q) tailList htailShort
  change finitePathList (pathPrefix (trajectory omega) v.length) =
    prefixedTilingPrefixPointPath initial.1 x
      (tilingInsertGapVector t x r q)
      (prefixedTilingInsertionTerminal initial t x r q ⟨tailList, htailShort⟩)
  rw [hvlen, finitePathList_add_eq_append_segmentPath_tail]
  rw [segmentPath_eq_blockPath_append_remainder, homegaStart, hblocks]
  rw [hprefix]
  unfold prefixedTilingPrefixPointPath prefixedTilingInsertionTerminal
  cases tailList with
  | nil =>
      have hsuffixEven : suffix.length % 2 = 0 := by
        simp [suffix, tilingInsertionPrefixList]
      simp [segmentRemainder, hsuffixEven, tilingPrefixPointPath]
  | cons d ds =>
      cases ds with
      | nil =>
          simp [segmentRemainder, tilingPrefixPointPath,
            suffix, v, omega]
      | cons e es =>
          simp at htailShort

/-! ## Prefix-correct frozen local time -/

/-- Outside the represented external dominoes, varying insertion totals does
not change local time even after the physical initial word is restored. -/
theorem prefixedTilingInsertedPrefix_localTime_of_base_not_mem {i : ℕ}
    (initial : List Direction) (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ)
    (terminal : Option Point) (y : Point)
    (hy : tilingBase t y ∉ tilingExternalDominoBases t x r) :
    listLocalTime
        (prefixedTilingPrefixPointPath initial x
          (tilingInsertGapVector t x r q) terminal) y =
      prefixedTilingFixedBoundaryLocalTime initial x r terminal y := by
  have hlocal := tilingInsertedPrefix_localTime_of_base_not_mem
    t x r q terminal y hy
  let inserted := tilingPrefixPointPath x
    (tilingInsertGapVector t x r q) terminal
  let fixed := tilingPrefixPointPath x (List.ofFn r.1) terminal
  have hinsertedHead : inserted.head? = some x := by
    cases terminal <;> simp [inserted, tilingPrefixPointPath, blockPath]
  have hfixedHead : fixed.head? = some x := by
    cases terminal <;> simp [fixed, tilingPrefixPointPath, blockPath]
  unfold prefixedTilingFixedBoundaryLocalTime
  unfold prefixedTilingPrefixPointPath
  change listLocalTime
      (finitePathList
          (pathPrefix
            (trajectory (extendPrefix (directionVectorOfList initial)))
              initial.length) ++ inserted.tail) y =
    listLocalTime
      (finitePathList
          (pathPrefix
            (trajectory (extendPrefix (directionVectorOfList initial)))
              initial.length) ++ fixed.tail) y
  unfold listLocalTime
  simp only [List.count_append]
  have hcount : inserted.count y = fixed.count y := by
    simpa only [inserted, fixed, listLocalTime, tilingFixedBoundaryLocalTime]
      using hlocal
  cases hinsertedEq : inserted with
  | nil => simp [hinsertedEq] at hinsertedHead
  | cons a as =>
      cases hfixedEq : fixed with
      | nil => simp [hfixedEq] at hfixedHead
      | cons b bs =>
          simp only [hinsertedEq, List.head?_cons, Option.some.injEq] at hinsertedHead
          simp only [hfixedEq, List.head?_cons, Option.some.injEq] at hfixedHead
          subst a
          subst b
          simp only [hinsertedEq, hfixedEq, List.tail_cons, List.count_cons] at hcount ⊢
          omega

/-! ## Physical endpoint invariance -/

private theorem finitePathList_getLast?_eq
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

private theorem blockPath_getLast?_eq (x : Point) (bs : List Block) :
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

private theorem prefixedTilingInsertionEndpoint_eq_no_tail
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
    rw [finitePathList_getLast?_eq, hstart]
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
    rw [finitePathList_getLast?_eq, hjoin, blockPath_getLast?_eq,
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
    rw [finitePathList_getLast?_eq, hjoin', blockPath_getLast?_eq,
      followBlocks_tilingInsertGapVector] at hlastClean
    exact hlastClean
  exact Option.some.inj (hq.trans hq'.symm)

/-- The endpoint of a physical prefixed insertion word is independent of all
insertion multiplicities. -/
theorem prefixedTilingInsertionEndpoint_eq_of_coordinates
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
  | nil =>
      exact prefixedTilingInsertionEndpoint_eq_no_tail
        initial t x r q q' hstart
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
          have hbase := prefixedTilingInsertionEndpoint_eq_no_tail
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

/-- The optional physical terminal singleton is likewise independent of all
insertion multiplicities. -/
theorem prefixedTilingInsertionTerminal_eq_of_coordinates
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
            (prefixedTilingInsertionEndpoint_eq_of_coordinates
              initial t x r q q' ⟨[d], htail⟩ hstart)
      | cons e es => simp at htail

/-! ## Distinguished projection invariance -/

/-- A strict bound on the prefix-correct fixed maximum plus the insertion
total bounds both physical endpoints of an away domino. -/
theorem prefixedTilingActualEndpointsBelow_of_max_add_total_lt {i : ℕ}
    (initial : List Direction) (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ)
    (terminal : Option Point) (level : ℕ)
    (b : TilingExternalDomino t x r)
    (hbelow :
      prefixedTilingFixedBoundaryDominoMax initial x r terminal b +
          tilingDominoTotal t x r q b < level) :
    listLocalTime
          (prefixedTilingPrefixPointPath initial x
            (tilingInsertGapVector t x r q) terminal) b.1 < level ∧
      listLocalTime
          (prefixedTilingPrefixPointPath initial x
            (tilingInsertGapVector t x r q) terminal)
          (tilingPartner t b.1) < level := by
  have hbase := prefixedTilingInsertedPrefix_localTime_at_dominoPoint
    initial t x r q terminal b b.1
      (TilingSpatialInsertionFiber.tilingExternalDomino_is_base t x r b)
  have hpartner := prefixedTilingInsertedPrefix_localTime_at_dominoPoint
    initial t x r q terminal b (tilingPartner t b.1)
      (TilingSpatialInsertionFiber.tilingPartner_ofExternalDomino_has_base
        t x r b)
  unfold prefixedTilingFixedBoundaryDominoMax at hbelow
  constructor <;> omega

/-- Once all away endpoints are strictly below `level`, fixing the
distinguished coordinate projection fixes level-threshold membership at every
lattice point on the complete physical prefixed path. -/
theorem prefixedTilingPrefixLocalTime_ge_level_iff_of_distinguished_eq
    {i cap : ℕ} (initial : List Direction) (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (terminal : Option Point)
    (level : ℕ) (D : Finset Point)
    (q q' : TilingCappedCoordinates i cap)
    (hdist : (splitTilingCoordinatesEquiv t x r D q).1 =
      (splitTilingCoordinatesEquiv t x r D q').1)
    (hbelow : ∀ b : TilingExternalDomino t x r, b.1 ∉ D →
      prefixedTilingFixedBoundaryDominoMax initial x r terminal b +
        tilingDominoTotal t x r (fun j ↦ (q j : ℕ)) b < level)
    (hbelow' : ∀ b : TilingExternalDomino t x r, b.1 ∉ D →
      prefixedTilingFixedBoundaryDominoMax initial x r terminal b +
        tilingDominoTotal t x r (fun j ↦ (q' j : ℕ)) b < level)
    (y : Point) :
    level ≤ listLocalTime
        (prefixedTilingPrefixPointPath initial x
          (tilingInsertGapVector t x r (fun j ↦ (q j : ℕ))) terminal) y ↔
      level ≤ listLocalTime
        (prefixedTilingPrefixPointPath initial x
          (tilingInsertGapVector t x r (fun j ↦ (q' j : ℕ))) terminal) y := by
  by_cases hy : tilingBase t y ∈ tilingExternalDominoBases t x r
  · let b : TilingExternalDomino t x r := ⟨tilingBase t y, hy⟩
    by_cases hb : b.1 ∈ D
    · have htotal := tilingDominoTotal_eq_of_distinguished_eq
        t x r D q q' hdist b hb
      rw [prefixedTilingInsertedPrefix_localTime_at_dominoPoint
          initial t x r (fun j ↦ (q j : ℕ)) terminal b y rfl,
        prefixedTilingInsertedPrefix_localTime_at_dominoPoint
          initial t x r (fun j ↦ (q' j : ℕ)) terminal b y rfl,
        htotal]
    · have hends := prefixedTilingActualEndpointsBelow_of_max_add_total_lt
        initial t x r (fun j ↦ (q j : ℕ)) terminal level b (hbelow b hb)
      have hends' := prefixedTilingActualEndpointsBelow_of_max_add_total_lt
        initial t x r (fun j ↦ (q' j : ℕ)) terminal level b (hbelow' b hb)
      rcases point_eq_tilingBase_or_partner_base t y with hybase | hypartner
      · rw [hybase]
        exact iff_of_false (not_le_of_gt hends.1) (not_le_of_gt hends'.1)
      · rw [hypartner]
        exact iff_of_false (not_le_of_gt hends.2) (not_le_of_gt hends'.2)
  · rw [prefixedTilingInsertedPrefix_localTime_of_base_not_mem
        initial t x r (fun j ↦ (q j : ℕ)) terminal y hy,
      prefixedTilingInsertedPrefix_localTime_of_base_not_mem
        initial t x r (fun j ↦ (q' j : ℕ)) terminal y hy]

/-- At any point whose tiling base is distinguished, the complete physical
prefix local time is fixed exactly by the distinguished projection. -/
theorem prefixedTilingPrefixLocalTime_eq_of_distinguished_eq
    {i cap : ℕ} (initial : List Direction) (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (terminal : Option Point)
    (D : Finset Point) (q q' : TilingCappedCoordinates i cap)
    (hdist : (splitTilingCoordinatesEquiv t x r D q).1 =
      (splitTilingCoordinatesEquiv t x r D q').1)
    (y : Point) (hy : tilingBase t y ∈ D) :
    listLocalTime
        (prefixedTilingPrefixPointPath initial x
          (tilingInsertGapVector t x r (fun j ↦ (q j : ℕ))) terminal) y =
      listLocalTime
        (prefixedTilingPrefixPointPath initial x
          (tilingInsertGapVector t x r (fun j ↦ (q' j : ℕ))) terminal) y := by
  by_cases hrepresented :
      tilingBase t y ∈ tilingExternalDominoBases t x r
  · let b : TilingExternalDomino t x r :=
      ⟨tilingBase t y, hrepresented⟩
    have htotal := tilingDominoTotal_eq_of_distinguished_eq
      t x r D q q' hdist b hy
    rw [prefixedTilingInsertedPrefix_localTime_at_dominoPoint
        initial t x r (fun j ↦ (q j : ℕ)) terminal b y rfl,
      prefixedTilingInsertedPrefix_localTime_at_dominoPoint
        initial t x r (fun j ↦ (q' j : ℕ)) terminal b y rfl,
      htotal]
  · rw [prefixedTilingInsertedPrefix_localTime_of_base_not_mem
        initial t x r (fun j ↦ (q j : ℕ)) terminal y hrepresented,
      prefixedTilingInsertedPrefix_localTime_of_base_not_mem
        initial t x r (fun j ↦ (q' j : ℕ)) terminal y hrepresented]

/-- Set-valued threshold invariance for the actual physically prefixed
insertion words.  Unlike the origin-started theorem, the initial word is part
of both stopped cylinders. -/
theorem thresholdSites_prefixedTilingInsertionPrefix_eq_of_distinguished_eq
    (initial : BoundaryTail) {i cap : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (tail : BoundaryTail)
    (level : ℕ) (hlevel : 0 < level) (D : Finset Point)
    (q q' : TilingCappedCoordinates i cap)
    (hstart : trajectory
      (extendPrefix (directionVectorOfList initial.1)) initial.1.length = x)
    (hdist : (splitTilingCoordinatesEquiv t x r D q).1 =
      (splitTilingCoordinatesEquiv t x r D q').1)
    (hbelow : ∀ b : TilingExternalDomino t x r, b.1 ∉ D →
      prefixedTilingFixedBoundaryDominoMax initial.1 x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (q j : ℕ)) tail) b +
        tilingDominoTotal t x r (fun j ↦ (q j : ℕ)) b < level)
    (hbelow' : ∀ b : TilingExternalDomino t x r, b.1 ∉ D →
      prefixedTilingFixedBoundaryDominoMax initial.1 x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (q' j : ℕ)) tail) b +
        tilingDominoTotal t x r (fun j ↦ (q' j : ℕ)) b < level) :
    let v := prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (q j : ℕ)) tail.1
    let v' := prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (q' j : ℕ)) tail.1
    thresholdSites
        (trajectory (extendPrefix (directionVectorOfList v))) v.length level =
      thresholdSites
        (trajectory (extendPrefix (directionVectorOfList v'))) v'.length level := by
  let qNat : Fin (i + 1) → ℕ := fun j ↦ (q j : ℕ)
  let qNat' : Fin (i + 1) → ℕ := fun j ↦ (q' j : ℕ)
  let terminal := prefixedTilingInsertionTerminal initial t x r qNat tail
  let v := prefixedTilingInsertionPrefixList initial.1 t x r qNat tail.1
  let v' := prefixedTilingInsertionPrefixList initial.1 t x r qNat' tail.1
  let omega := extendPrefix (directionVectorOfList v)
  let omega' := extendPrefix (directionVectorOfList v')
  let s := trajectory omega
  let s' := trajectory omega'
  have hterminal' :
      prefixedTilingInsertionTerminal initial t x r qNat' tail = terminal := by
    exact (prefixedTilingInsertionTerminal_eq_of_coordinates
      initial t x r qNat qNat' tail hstart).symm
  have hpath : finitePathList (pathPrefix s v.length) =
      prefixedTilingPrefixPointPath initial.1 x
        (tilingInsertGapVector t x r qNat) terminal := by
    exact finitePathList_prefixedTilingInsertionPrefix
      initial t x r qNat tail hstart
  have hpath' : finitePathList (pathPrefix s' v'.length) =
      prefixedTilingPrefixPointPath initial.1 x
        (tilingInsertGapVector t x r qNat') terminal := by
    rw [← hterminal']
    exact finitePathList_prefixedTilingInsertionPrefix
      initial t x r qNat' tail hstart
  ext y
  rw [mem_thresholdSites_iff s v.length level y hlevel,
    mem_thresholdSites_iff s' v'.length level y hlevel,
    localTime_eq_listLocalTime, localTime_eq_listLocalTime,
    hpath, hpath']
  exact prefixedTilingPrefixLocalTime_ge_level_iff_of_distinguished_eq
    initial.1 t x r terminal level D q q' hdist
      (by simpa only [terminal, qNat] using hbelow)
      (by simpa only [terminal, qNat', hterminal'] using hbelow') y

/-- Prefix-correct stopped-clock invariance.  The final creation site is
distinguished, and all away endpoints remain strictly below the creation
level.  These are exactly the deterministic hypotheses supplied by the
honest accepted-base window in the low candidate product. -/
theorem prefixedTilingStoppingAccepted_iff_of_distinguished_eq_of_strictAway
    (initial : BoundaryTail) {i cap : ℕ} (t : DominoTiling) (x : Point)
    (m k cutoff : ℕ) (hm : 0 < m) (hk : 0 < k)
    (r : TilingRetainedWord t x i) (tail : BoundaryTail)
    (D : Finset Point) (q q' : TilingCappedCoordinates i cap)
    (hstart : trajectory
      (extendPrefix (directionVectorOfList initial.1)) initial.1.length = x)
    (hbase :
      let v := prefixedTilingInsertionPrefixList initial.1 t x r
        (fun j ↦ (q j : ℕ)) tail.1
      tilingBase t
        (trajectory (extendPrefix (directionVectorOfList v)) v.length) ∈ D)
    (hdist : (splitTilingCoordinatesEquiv t x r D q).1 =
      (splitTilingCoordinatesEquiv t x r D q').1)
    (hbelow : ∀ b : TilingExternalDomino t x r, b.1 ∉ D →
      prefixedTilingFixedBoundaryDominoMax initial.1 x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (q j : ℕ)) tail) b +
        tilingDominoTotal t x r (fun j ↦ (q j : ℕ)) b < m)
    (hbelow' : ∀ b : TilingExternalDomino t x r, b.1 ∉ D →
      prefixedTilingFixedBoundaryDominoMax initial.1 x r
          (prefixedTilingInsertionTerminal initial t x r
            (fun j ↦ (q' j : ℕ)) tail) b +
        tilingDominoTotal t x r (fun j ↦ (q' j : ℕ)) b < m)
    (hpos : 0 < (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (q j : ℕ)) tail.1).length)
    (hpos' : 0 < (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (q' j : ℕ)) tail.1).length)
    (hlt : (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (q j : ℕ)) tail.1).length < cutoff)
    (hlt' : (prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (q' j : ℕ)) tail.1).length < cutoff) :
    PrefixedTilingStoppingAccepted (truncatedLevelTime m k cutoff)
        initial.1 t x r (fun j ↦ (q j : ℕ)) tail.1 ↔
      PrefixedTilingStoppingAccepted (truncatedLevelTime m k cutoff)
        initial.1 t x r (fun j ↦ (q' j : ℕ)) tail.1 := by
  let qNat : Fin (i + 1) → ℕ := fun j ↦ (q j : ℕ)
  let qNat' : Fin (i + 1) → ℕ := fun j ↦ (q' j : ℕ)
  let terminal := prefixedTilingInsertionTerminal initial t x r qNat tail
  let v := prefixedTilingInsertionPrefixList initial.1 t x r qNat tail.1
  let v' := prefixedTilingInsertionPrefixList initial.1 t x r qNat' tail.1
  let omega := extendPrefix (directionVectorOfList v)
  let omega' := extendPrefix (directionVectorOfList v')
  let s := trajectory omega
  let s' := trajectory omega'
  have hterminal' :
      prefixedTilingInsertionTerminal initial t x r qNat' tail = terminal :=
    (prefixedTilingInsertionTerminal_eq_of_coordinates
      initial t x r qNat qNat' tail hstart).symm
  have hpath : finitePathList (pathPrefix s v.length) =
      prefixedTilingPrefixPointPath initial.1 x
        (tilingInsertGapVector t x r qNat) terminal := by
    exact finitePathList_prefixedTilingInsertionPrefix
      initial t x r qNat tail hstart
  have hpath' : finitePathList (pathPrefix s' v'.length) =
      prefixedTilingPrefixPointPath initial.1 x
        (tilingInsertGapVector t x r qNat') terminal := by
    rw [← hterminal']
    exact finitePathList_prefixedTilingInsertionPrefix
      initial t x r qNat' tail hstart
  have hend : s v.length = s' v'.length :=
    prefixedTilingInsertionEndpoint_eq_of_coordinates
      initial t x r qNat qNat' tail hstart
  have hsites : thresholdSites s v.length m =
      thresholdSites s' v'.length m := by
    exact thresholdSites_prefixedTilingInsertionPrefix_eq_of_distinguished_eq
      initial t x r tail m hm D q q' hstart hdist hbelow hbelow'
  have hcount : thresholdCount s v.length m =
      thresholdCount s' v'.length m := by
    unfold thresholdCount
    rw [hsites]
  have hlocalList := prefixedTilingPrefixLocalTime_eq_of_distinguished_eq
    initial.1 t x r terminal D q q' hdist (s v.length) hbase
  have hlocal : localTime s v.length (s v.length) =
      localTime s' v'.length (s' v'.length) := by
    rw [← hend, localTime_eq_listLocalTime, localTime_eq_listLocalTime,
      hpath, hpath']
    exact hlocalList
  unfold PrefixedTilingStoppingAccepted
  change truncatedLevelTime m k cutoff omega = v.length ↔
    truncatedLevelTime m k cutoff omega' = v'.length
  rw [truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m k cutoff v.length omega hlt,
    truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m k cutoff v'.length omega' hlt',
    thresholdCreation_iff_terminal_count_and_new_localTime
      s m k v.length hm hk hpos,
    thresholdCreation_iff_terminal_count_and_new_localTime
      s' m k v'.length hm hk hpos']
  constructor
  · rintro ⟨hc, hl⟩
    exact ⟨hcount ▸ hc, hlocal ▸ hl⟩
  · rintro ⟨hc, hl⟩
    exact ⟨hcount.symm ▸ hc, hlocal.symm ▸ hl⟩

end

end Erdos1165.TilingPrefixedFavoriteTraceSupport
