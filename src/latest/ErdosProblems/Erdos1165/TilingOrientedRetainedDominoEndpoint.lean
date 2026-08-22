/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingOrientedRetainedSourceLocalTime

/-!
# The oriented endpoint carried by one retained tiling domino

An endpoint-phase external chain stays in one checkerboard class.  A
canonical tiling base need not lie in that class (notably for column
tilings), so the physical endpoint represented by a domino coordinate is
the unique endpoint of that domino in the chosen orientation.  This file
identifies its external local time with the coordinate multiplicity.
-/

open Set

namespace Erdos1165.TilingOrientedRetainedDominoEndpoint

open ExternalCountTransport HLOZSourceOrientedExternalLocalTime
open LazyDecomposition PathInsertion SpatialInsertionFiber
open TilingLazyDecomposition TilingOrientedRetainedCoordinateSupport
open TilingOrientedRetainedSourceLocalTime TilingSpatialInsertionFiber
open VariableStoppedFiber VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

attribute [local instance] Classical.propDecidable

/-- The unique endpoint of the domino with canonical base `b` in the
checkerboard class selected by `o`. -/
def orientedDominoEndpoint (t : DominoTiling) (o : Orientation)
    (b : Point) : Point :=
  if OrientationCompatible o b then b else tilingPartner t b

theorem orientedDominoEndpoint_compatible
    (t : DominoTiling) (o : Orientation) (b : Point) :
    OrientationCompatible o (orientedDominoEndpoint t o b) := by
  unfold orientedDominoEndpoint
  split_ifs with hb
  · exact hb
  · cases o with
    | even =>
        change pointParity (tilingPartner t b) = 0
        change ¬pointParity b = 0 at hb
        have hodd : pointParity b = 1 := by
          have hlt := ZMod.val_lt (pointParity b)
          have hval : (pointParity b).val = 1 := by
            by_contra hne
            have : (pointParity b).val = 0 := by omega
            exact hb ((ZMod.val_eq_zero _).mp this)
          exact (ZMod.val_eq_one (by norm_num) _).mp hval
        rw [tilingPartner_eq_add_directionVector, pointParity_add,
          pointParity_directionVector, hodd]
        change (2 : ZMod 2) = 0
        decide
    | shifted =>
        change pointParity (tilingPartner t b) = 1
        change ¬pointParity b = 1 at hb
        have heven : pointParity b = 0 := by
          have hlt := ZMod.val_lt (pointParity b)
          have hval : (pointParity b).val = 0 := by
            by_contra hne
            have : (pointParity b).val = 1 := by omega
            exact hb ((ZMod.val_eq_one (by norm_num) _).mp this)
          exact (ZMod.val_eq_zero _).mp hval
        rw [tilingPartner_eq_add_directionVector, pointParity_add,
          pointParity_directionVector, heven]
        norm_num

theorem tilingBase_orientedDominoEndpoint
    (t : DominoTiling) (o : Orientation) (b : Point)
    (hb : IsTilingBase t b) :
    tilingBase t (orientedDominoEndpoint t o b) = b := by
  unfold orientedDominoEndpoint
  split_ifs
  · simp [tilingBase, hb]
  · exact (tilingBase_partner t b).trans (by simp [tilingBase, hb])

theorem isTilingBase_of_tilingBase_eq_self
    (t : DominoTiling) (b : Point) (hbase : tilingBase t b = b) :
    IsTilingBase t b := by
  by_contra hb
  apply tilingPartner_ne t b
  simpa [tilingBase, tilingPartner, hb] using hbase

theorem eq_orientedDominoEndpoint_of_compatible_of_tilingBase_eq
    (t : DominoTiling) (o : Orientation) {b y : Point}
    (hy : OrientationCompatible o y)
    (hbase : tilingBase t y = b) :
    y = orientedDominoEndpoint t o b := by
  unfold orientedDominoEndpoint
  split_ifs with hbcompat
  · exact eq_of_tilingBase_eq_of_orientationCompatible t hy hbcompat hbase
  · rcases point_eq_tilingBase_or_partner_base t y with h | h
    · exfalso
      apply hbcompat
      rw [← hbase, ← h]
      exact hy
    · simpa only [hbase] using h

/-- Coordinate multiplicity at a retained domino is the endpoint-chain
local time of its oriented physical endpoint, whether or not the canonical
base itself belongs to the orientation class. -/
theorem card_tilingCoordinatesAt_eq_orientedEndpointLocalTime
    {o : Orientation} {i : ℕ} (t : DominoTiling) (x : Point)
    (hx : OrientationCompatible o x) (r : TilingRetainedWord t x i)
    (b : TilingExternalDomino t x r) :
    Fintype.card (TilingCoordinatesAt t x r b) =
      listLocalTime (blockEndpointPath x (List.ofFn r.1))
        (orientedDominoEndpoint t o b.1) := by
  rw [card_tilingCoordinatesAt_eq_endpointBaseLocalTime]
  unfold listLocalTime
  rw [List.count_eq_countP, List.countP_map, List.count_eq_countP]
  apply List.countP_congr
  intro y hy
  simp only [Function.comp_apply, beq_iff_eq]
  have hyc : OrientationCompatible o y := by
    rw [blockEndpointPath_eq_rawExternalBaseList] at hy
    rw [List.mem_ofFn] at hy
    obtain ⟨k, rfl⟩ := hy
    exact orientationCompatible_rawExternalBase hx r.1 k
  have hbBase : IsTilingBase t b.1 :=
    isTilingBase_of_tilingBase_eq_self t b.1
      (tilingExternalDomino_is_base t x r b)
  constructor
  · intro hbase
    exact eq_orientedDominoEndpoint_of_compatible_of_tilingBase_eq
      t o hyc hbase
  · rintro rfl
    exact tilingBase_orientedDominoEndpoint t o b.1 hbBase

end

end Erdos1165.TilingOrientedRetainedDominoEndpoint
