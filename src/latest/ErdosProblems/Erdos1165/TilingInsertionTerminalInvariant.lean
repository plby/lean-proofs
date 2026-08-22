/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingStoppedAcceptanceFactorization

/-!
# Coordinate independence of the all-six insertion terminal

Every inserted tiling block is a two-step return to its current base.
Consequently the endpoint before the possible one-step boundary tail is
determined by the retained word alone, and the optional terminal point is
independent of every insertion multiplicity.
-/

namespace Erdos1165.TilingInsertionTerminalInvariant

open TilingLazyDecomposition TilingSpatialInsertionFiber
open TilingStoppedAcceptanceFactorization
open SpatialInsertionFiber PreStoppingFiber VariableStoppedFiber
open ShiftedPrefixBridge

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Inserting any number of tiling returns does not change the endpoint of
the retained block word. -/
theorem followBlocks_tilingInsertGapVector {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (q : Fin (i + 1) → ℕ) :
    followBlocks x (tilingInsertGapVector t x r q) =
      followBlocks x (List.ofFn r.1) := by
  induction i generalizing x with
  | zero =>
      rw [tilingInsertGapVector_zero,
        TilingSpatialInsertionFiber.followBlocks_replicate_tilingRemovable]
      rfl
  | succ i ih =>
      rw [tilingInsertGapVector_succ, followBlocks_append,
        followBlocks_append x
          (List.replicate (q 0) (tilingRemovableBlock t x)) [r.1 0],
        TilingSpatialInsertionFiber.followBlocks_replicate_tilingRemovable]
      change followBlocks (PathInsertion.blockEnd x (r.1 0))
          (tilingInsertGapVector t (PathInsertion.blockEnd x (r.1 0))
            (tilingRetainedTail t x r) (fun k ↦ q k.succ)) = _
      rw [ih]
      simp only [List.ofFn_succ, followBlocks, List.foldl_cons,
        tilingRetainedTail]

/-- The endpoint of a word consisting of complete two-step blocks is its
iterated block endpoint. -/
theorem trajectory_blockWord (bs : List PathInsertion.Block) :
    let v := bs.flatMap (fun b ↦ [b.1, b.2])
    trajectory (StoppedInsertion.extendPrefix
      (PreStoppingFiber.directionVectorOfList v)) v.length =
      followBlocks (0, 0) bs := by
  let v := bs.flatMap (fun b ↦ [b.1, b.2])
  let omega := StoppedInsertion.extendPrefix
    (PreStoppingFiber.directionVectorOfList v)
  have hlen : v.length = 2 * bs.length := by
    simp [v, List.length_flatMap]
    omega
  have hincrement : incrementPrefixList v.length omega = v := by
    unfold incrementPrefixList
    rw [stepPrefix_extendPrefix, ofFn_directionVectorOfList]
  have hblocks : completePrefixBlocks omega v.length = bs := by
    rw [completePrefixBlocks_eq_prefixBlockWord]
    unfold prefixBlockWord
    rw [hincrement]
    simpa using pairDirectionList_flatMap_blocks bs
  change trajectory omega v.length = _
  rw [hlen, ← followBlocks_completePrefixBlocks omega bs.length]
  simpa only [hlen] using congrArg (followBlocks (0, 0)) hblocks

/-- The endpoint of paired block increments followed by one direction is the
block endpoint followed by that final direction. -/
theorem trajectory_blockWord_append_singleton (bs : List PathInsertion.Block)
    (d : Direction) :
    let v := bs.flatMap (fun b ↦ [b.1, b.2]) ++ [d]
    trajectory (StoppedInsertion.extendPrefix
      (PreStoppingFiber.directionVectorOfList v)) v.length =
      followBlocks (0, 0) bs + directionVector d := by
  let v := bs.flatMap (fun b ↦ [b.1, b.2]) ++ [d]
  let omega := StoppedInsertion.extendPrefix
    (PreStoppingFiber.directionVectorOfList v)
  have hlen : v.length = 2 * bs.length + 1 := by
    simp [v, List.length_flatMap]
    omega
  have hflatlen :
      (bs.flatMap (fun b ↦ [b.1, b.2])).length = 2 * bs.length := by
    simp [List.length_flatMap]
    omega
  have hincrement : incrementPrefixList v.length omega = v := by
    unfold incrementPrefixList
    rw [stepPrefix_extendPrefix, ofFn_directionVectorOfList]
  have hblocksFull : completePrefixBlocks omega v.length = bs := by
    rw [completePrefixBlocks_eq_prefixBlockWord]
    unfold prefixBlockWord
    rw [hincrement]
    exact pairDirectionList_flatten_append_shortTail bs [d] (by simp)
  have hblocks : completePrefixBlocks omega (2 * bs.length) = bs := by
    unfold completePrefixBlocks at hblocksFull ⊢
    have heven : 2 * bs.length / 2 = bs.length := by omega
    have hdiv : (2 * bs.length + 1) / 2 = bs.length := by omega
    rw [heven]
    rw [hlen, hdiv] at hblocksFull
    exact hblocksFull
  change trajectory omega v.length = _
  rw [hlen, trajectory_succ]
  rw [← followBlocks_completePrefixBlocks omega bs.length, hblocks]
  congr 1
  unfold omega StoppedInsertion.extendPrefix
  simp [v, hlen, hflatlen, PreStoppingFiber.directionVectorOfList]

/-- Explicit terminal formula: no-tail means no terminal singleton, while a
one-step tail starts from the endpoint of the retained block word. -/
theorem tilingInsertionTerminal_eq_retained_endpoint {i : ℕ}
    (t : DominoTiling) (r : TilingRetainedWord t (0, 0) i)
    (q : Fin (i + 1) → ℕ) (tail : BoundaryTail) :
    tilingInsertionTerminal t r q tail =
      match tail.1 with
      | [] => none
      | d :: _ => some (followBlocks (0, 0) (List.ofFn r.1) + directionVector d) := by
  cases htail : tail.1 with
  | nil => simp [tilingInsertionTerminal, htail]
  | cons d ds =>
      cases ds with
      | nil =>
          unfold tilingInsertionTerminal
          rw [htail]
          simp only
          unfold tilingInsertionPrefixList
          rw [trajectory_blockWord_append_singleton]
          rw [followBlocks_tilingInsertGapVector]
      | cons e es =>
          have hshort := tail.2
          simp [htail] at hshort

/-- The optional terminal point is independent of all insertion
multiplicities. -/
theorem tilingInsertionTerminal_eq_of_coordinates {i : ℕ}
    (t : DominoTiling) (r : TilingRetainedWord t (0, 0) i)
    (q q' : Fin (i + 1) → ℕ) (tail : BoundaryTail) :
    tilingInsertionTerminal t r q tail =
      tilingInsertionTerminal t r q' tail := by
  rw [tilingInsertionTerminal_eq_retained_endpoint,
    tilingInsertionTerminal_eq_retained_endpoint]

/-- Even when there is no optional terminal singleton, the actual canonical
stopped endpoint is independent of all insertion multiplicities. -/
theorem canonical_tilingInsertion_endpoint_eq_of_coordinates {i : ℕ}
    (t : DominoTiling) (r : TilingRetainedWord t (0, 0) i)
    (q q' : Fin (i + 1) → ℕ) (tail : BoundaryTail) :
    let v := tilingInsertionPrefixList t (0, 0) r q tail.1
    let v' := tilingInsertionPrefixList t (0, 0) r q' tail.1
    trajectory (StoppedInsertion.extendPrefix
        (PreStoppingFiber.directionVectorOfList v)) v.length =
      trajectory (StoppedInsertion.extendPrefix
        (PreStoppingFiber.directionVectorOfList v')) v'.length := by
  cases htail : tail.1 with
  | nil =>
      have hv : tilingInsertionPrefixList t (0, 0) r q [] =
          (tilingInsertGapVector t (0, 0) r q).flatMap
            (fun b ↦ [b.1, b.2]) := by
        simp [tilingInsertionPrefixList]
      have hv' : tilingInsertionPrefixList t (0, 0) r q' [] =
          (tilingInsertGapVector t (0, 0) r q').flatMap
            (fun b ↦ [b.1, b.2]) := by
        simp [tilingInsertionPrefixList]
      rw [hv, hv']
      dsimp only
      rw [trajectory_blockWord, trajectory_blockWord,
        followBlocks_tilingInsertGapVector,
        followBlocks_tilingInsertGapVector]
  | cons d ds =>
      cases ds with
      | nil =>
          have hv : tilingInsertionPrefixList t (0, 0) r q [d] =
              (tilingInsertGapVector t (0, 0) r q).flatMap
                (fun b ↦ [b.1, b.2]) ++ [d] := by
            simp [tilingInsertionPrefixList]
          have hv' : tilingInsertionPrefixList t (0, 0) r q' [d] =
              (tilingInsertGapVector t (0, 0) r q').flatMap
                (fun b ↦ [b.1, b.2]) ++ [d] := by
            simp [tilingInsertionPrefixList]
          rw [hv, hv']
          dsimp only
          rw [trajectory_blockWord_append_singleton,
            trajectory_blockWord_append_singleton,
            followBlocks_tilingInsertGapVector,
            followBlocks_tilingInsertGapVector]
      | cons e es =>
          have hshort := tail.2
          simp [htail] at hshort

end

end Erdos1165.TilingInsertionTerminalInvariant
