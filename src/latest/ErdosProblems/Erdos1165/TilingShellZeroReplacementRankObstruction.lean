/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingPrefixedInsertedLocalTime
import ErdosProblems.Erdos1165.TilingShellZeroSourcePartition

/-!
# A rank obstruction for domino-total shell replacement

One tiling insertion total is added to the local time of both endpoints of
its domino.  Consequently, moving one domino total from `I₁` to `I₀`
does not by itself imply that exactly one new level-`m` site is created.
This is the deterministic obstruction to constructing the currently stated
rank `k + total - central` replacement clock from the pure total screen.
-/

open Set

namespace Erdos1165.TilingShellZeroReplacementRankObstruction

open LazyDecomposition SpatialInsertionFiber
open TilingInsertedLocalTime TilingLazyDecomposition
open TilingPrefixedInsertedLocalTime TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The empty retained word, whose only insertion coordinate is based at the
initial point. -/
def emptyRetainedWord (t : DominoTiling) (x : Point) :
    TilingRetainedWord t x 0 :=
  ⟨fun k ↦ Fin.elim0 k, fun k ↦ Fin.elim0 k⟩

def obstructionCoordinates (n : ℕ) : Fin 1 → ℕ := fun _ ↦ n

def obstructionPath (n : ℕ) : List Point :=
  prefixedTilingPrefixPointPath [] (0, 0)
    (tilingInsertGapVector .evenColumns (0, 0)
      (emptyRetainedWord .evenColumns (0, 0))
      (obstructionCoordinates n)) none

private def obstructionDomino : TilingExternalDomino .evenColumns (0, 0)
    (emptyRetainedWord .evenColumns (0, 0)) := by
  refine ⟨(0, 0), ?_⟩
  simp [tilingExternalDominoBases, emptyRetainedWord, rawExternalBase,
    followBlocks, tilingBase, IsTilingBase, Tilings.columnEven]

private def obstructionCoordinate :
    TilingCoordinatesAt .evenColumns (0, 0)
      (emptyRetainedWord .evenColumns (0, 0)) obstructionDomino := by
  refine ⟨0, ?_⟩
  simp [emptyRetainedWord, obstructionDomino, rawExternalBase, followBlocks,
    tilingBase, IsTilingBase, Tilings.columnEven]

private theorem obstructionCoordinatesAt_card :
    Fintype.card
      (TilingCoordinatesAt .evenColumns (0, 0)
        (emptyRetainedWord .evenColumns (0, 0)) obstructionDomino) = 1 := by
  letI : Subsingleton
      (TilingCoordinatesAt .evenColumns (0, 0)
        (emptyRetainedWord .evenColumns (0, 0)) obstructionDomino) :=
    ⟨fun a b ↦ by
      apply Subtype.ext
      exact (Fin.eq_zero a.1).trans (Fin.eq_zero b.1).symm⟩
  exact Fintype.card_ofSubsingleton obstructionCoordinate

private theorem obstructionDominoTotal (n : ℕ) :
    tilingDominoTotal .evenColumns (0, 0)
      (emptyRetainedWord .evenColumns (0, 0))
      (obstructionCoordinates n) obstructionDomino = n := by
  simp [tilingDominoTotal, obstructionCoordinates,
    obstructionCoordinatesAt_card]

theorem obstruction_base_localTime (n : ℕ) :
    listLocalTime (obstructionPath n) (0, 0) = n + 1 := by
  have h := prefixedTilingInsertedPrefix_localTime_at_dominoPoint
    ([] : List Direction) Tilings.Tiling.evenColumns (0, 0)
    (emptyRetainedWord .evenColumns (0, 0)) (obstructionCoordinates n)
    none obstructionDomino (0, 0) (by rfl)
  unfold obstructionPath
  rw [h, obstructionDominoTotal]
  simp [prefixedTilingFixedBoundaryLocalTime,
    prefixedTilingPrefixPointPath, emptyRetainedWord,
    obstructionDomino, tilingPrefixPointPath, PathInsertion.blockPath,
    PathInsertion.blockPathTail, Finset.card_univ,
    obstructionCoordinatesAt_card, rawExternalBase,
    followBlocks, tilingBase, IsTilingBase, Tilings.columnEven,
    listLocalTime, pathPrefix, finitePathList]
  omega

theorem obstruction_partner_localTime (n : ℕ) :
    listLocalTime (obstructionPath n) (1, 0) = n := by
  have h := prefixedTilingInsertedPrefix_localTime_at_dominoPoint
    ([] : List Direction) Tilings.Tiling.evenColumns (0, 0)
    (emptyRetainedWord .evenColumns (0, 0)) (obstructionCoordinates n)
    none obstructionDomino (1, 0) (by rfl)
  unfold obstructionPath
  rw [h, obstructionDominoTotal]
  simp [prefixedTilingFixedBoundaryLocalTime,
    prefixedTilingPrefixPointPath, emptyRetainedWord,
    obstructionDomino, tilingPrefixPointPath, PathInsertion.blockPath,
    PathInsertion.blockPathTail, Finset.card_univ,
    obstructionCoordinatesAt_card, rawExternalBase,
    followBlocks, tilingBase, IsTilingBase, Tilings.columnEven,
    listLocalTime, pathPrefix, finitePathList]

/-- At level `m`, the source total `m-2` leaves both endpoints below the
threshold, whereas the comparison total `m` puts both endpoints at or above
the threshold.  Thus a single `I₁→I₀` domino move can create two sites. -/
theorem one_domino_move_can_create_two_threshold_sites
    {m : ℕ} (hm : 2 ≤ m) :
    listLocalTime (obstructionPath (m - 2)) (0, 0) < m ∧
      listLocalTime (obstructionPath (m - 2)) (1, 0) < m ∧
      m ≤ listLocalTime (obstructionPath m) (0, 0) ∧
      m ≤ listLocalTime (obstructionPath m) (1, 0) := by
  rw [obstruction_base_localTime, obstruction_partner_localTime,
    obstruction_base_localTime, obstruction_partner_localTime]
  omega

end

end Erdos1165.TilingShellZeroReplacementRankObstruction
