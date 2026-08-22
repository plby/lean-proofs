/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingOrientedShellZeroSourcePartition

/-!
# Endpoint-oriented retained-coordinate support

The insertion coordinates of a stateful retained word are exactly its block
endpoints (including the initial endpoint).  In the checkerboard class of a
source orientation, an endpoint whose tiling base is `b` is literally `b`,
not its partner.  These facts identify the retained external local time used
by the shell source with `card (TilingCoordinatesAt ...)`.
-/

open Set
open scoped BigOperators

namespace Erdos1165.TilingOrientedRetainedCoordinateSupport

open LazyDecomposition PathInsertion SpatialInsertionFiber
open PreStoppingFiber StoppedInsertion VariableStoppedFiber
open TilingLazyDecomposition TilingSpatialInsertionFiber
open TilingOrientedShellZeroSourcePartition
open ExternalCountTransport
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The endpoint list of a function-valued block word is the list of its
raw external bases. -/
theorem blockEndpointPath_eq_rawExternalBaseList (x : Point) :
    ∀ {i : ℕ} (r : Fin i → Block),
      blockEndpointPath x (List.ofFn r) =
        List.ofFn (fun k : Fin (i + 1) ↦ rawExternalBase x r k) := by
  intro i
  induction i generalizing x with
  | zero =>
      intro r
      simp [rawExternalBase, followBlocks]
  | succ i ih =>
      intro r
      rw [List.ofFn_succ, blockEndpointPath_cons, List.ofFn_succ]
      congr 1
      simpa only [rawExternalBase_succ] using
        ih (x := blockEnd x (r 0)) (fun k ↦ r k.succ)

private theorem card_subtype_eq_count_ofFn
    {alpha : Type*} [DecidableEq alpha] [BEq alpha] [LawfulBEq alpha] {n : ℕ}
    (f : Fin n → alpha) (a : alpha) :
    Fintype.card {k : Fin n // f k = a} = (List.ofFn f).count a := by
  classical
  rw [Fintype.card_subtype, Finset.card_filter]
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.count_cons, Fin.sum_univ_succ]
      simp only [beq_iff_eq]
      rw [ih (fun k ↦ f k.succ)]
      by_cases h : f 0 = a <;> simp [h, add_comm]

/-- Coordinate multiplicity at a represented domino is the number of
retained block endpoints whose tiling base is that domino base. -/
theorem card_tilingCoordinatesAt_eq_endpointBaseLocalTime
    {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (b : TilingExternalDomino t x r) :
    Fintype.card (TilingCoordinatesAt t x r b) =
      listLocalTime
        ((blockEndpointPath x (List.ofFn r.1)).map (tilingBase t)) b.1 := by
  unfold TilingCoordinatesAt listLocalTime
  rw [card_subtype_eq_count_ofFn]
  rw [blockEndpointPath_eq_rawExternalBaseList]
  simp only [List.map_ofFn]
  rfl

theorem orientationCompatible_rawExternalBase
    {o : Orientation} {i : ℕ} {x : Point}
    (hx : OrientationCompatible o x) (r : Fin i → Block)
    (k : Fin (i + 1)) :
    OrientationCompatible o (rawExternalBase x r k) := by
  unfold rawExternalBase
  have hpar := pointParity_followBlocks x ((List.ofFn r).take ↑k)
  cases o with
  | even =>
      change pointParity (followBlocks x ((List.ofFn r).take ↑k)) = 0
      exact hpar.trans hx
  | shifted =>
      change pointParity (followBlocks x ((List.ofFn r).take ↑k)) = 1
      exact hpar.trans hx

/-- The physical start stored by a positive-time oriented trace is in its
declared endpoint checkerboard class. -/
theorem orientationCompatible_fixedOrientedTypedExternalWordCode_start
    (t : DominoTiling) (o : Orientation) (n : ℕ) (s : WalkPath)
    (hn : 0 < n) :
    OrientationCompatible o
      (fixedOrientedTypedExternalWordCode t o n s).start := by
  cases o with
  | even =>
      change EvenPoint (trajectory
        (extendPrefix (directionVectorOfList [])) 0)
      rw [EvenPoint, pointParity_trajectory]
      norm_num
  | shifted =>
      change OddPoint (trajectory
        (extendPrefix (directionVectorOfList
          ((incrementPrefixList n (stepsOfWalk s)).take 1)))
        ((incrementPrefixList n (stepsOfWalk s)).take 1).length)
      rw [OddPoint, pointParity_trajectory]
      have hlen :
          ((incrementPrefixList n (stepsOfWalk s)).take 1).length = 1 := by
        rw [List.length_take]
        simp only [incrementPrefixList, List.length_ofFn]
        omega
      rw [hlen]
      norm_num
/-- In one checkerboard endpoint class, equality of tiling bases is equality
of the endpoint points themselves. -/
theorem eq_of_tilingBase_eq_of_orientationCompatible
    (t : DominoTiling) {o : Orientation} {x b : Point}
    (hx : OrientationCompatible o x) (hb : OrientationCompatible o b)
    (hbase : tilingBase t x = b) : x = b := by
  rcases point_eq_tilingBase_or_partner_base t x with h | h
  · exact h.trans hbase
  · have hxpartner : x = tilingPartner t b := by simpa [hbase] using h
    have hpar : pointParity (tilingPartner t b) = pointParity b + 1 := by
      rw [tilingPartner_eq_add_directionVector, pointParity_add,
        pointParity_directionVector]
    cases o with
    | even =>
        change pointParity x = 0 at hx
        change pointParity b = 0 at hb
        rw [hxpartner, hpar, hb] at hx
        norm_num at hx
    | shifted =>
        change pointParity x = 1 at hx
        change pointParity b = 1 at hb
        rw [hxpartner, hpar, hb] at hx
        have hzero : (0 : ZMod 2) = 1 := by
          simpa only [show (1 : ZMod 2) + 1 = 0 by decide] using hx
        exact (zero_ne_one hzero).elim

/-- For an orientation-compatible retained start and domino base, coordinate
multiplicity is the literal endpoint local time at that base. -/
theorem card_tilingCoordinatesAt_eq_endpointLocalTime_of_compatible
    {o : Orientation} {i : ℕ} (t : DominoTiling) (x : Point)
    (hx : OrientationCompatible o x) (r : TilingRetainedWord t x i)
    (b : TilingExternalDomino t x r)
    (hb : OrientationCompatible o b.1) :
    Fintype.card (TilingCoordinatesAt t x r b) =
      listLocalTime (blockEndpointPath x (List.ofFn r.1)) b.1 := by
  rw [card_tilingCoordinatesAt_eq_endpointBaseLocalTime]
  unfold listLocalTime
  rw [List.count_eq_countP, List.countP_map, List.count_eq_countP]
  apply List.countP_congr
  intro y hy
  simp only [Function.comp_apply, beq_iff_eq]
  constructor
  · intro hbase
    have hyc : OrientationCompatible o y := by
      rw [blockEndpointPath_eq_rawExternalBaseList] at hy
      rw [List.mem_ofFn] at hy
      obtain ⟨k, rfl⟩ := hy
      exact orientationCompatible_rawExternalBase hx r.1 k
    exact eq_of_tilingBase_eq_of_orientationCompatible t hyc hb hbase
  · rintro rfl
    exact tilingExternalDomino_is_base t x r b

end

end Erdos1165.TilingOrientedRetainedCoordinateSupport
