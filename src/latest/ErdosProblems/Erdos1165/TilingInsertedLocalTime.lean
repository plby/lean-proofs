import ErdosProblems.Erdos1165.TilingStoppedProductDisintegration

/-!
# Pathwise local-time identities for state-dependent tiling insertion

This module connects the block-level insertion decoder with the point-path
deletion used by the six HLOZ tilings.  It proves that the retained external
path is independent of insertion coordinates and describes the erased path
exactly as the concatenation of the inserted domino excursions.
-/

open MeasureTheory Set
open scoped BigOperators

namespace Erdos1165.TilingInsertedLocalTime

open LazyDecomposition PathInsertion SpatialInsertionFiber StoppedInsertion
open TilingLazyDecomposition TilingSpatialInsertionFiber
open PreStoppingSpatialLaw

noncomputable section

/-- Stateful point-path compression agrees with stateful block deletion. -/
theorem tilingCompressTail_blockPathTail (t : DominoTiling) (x : Point) :
    ∀ bs : List Block,
      tilingCompressTail t x (blockPathTail x bs) =
        (blockPath x (deleteTilingBlocks t x bs)).tail := by
  intro bs
  induction bs generalizing x with
  | nil => simp [blockPathTail, blockPath, deleteTilingBlocks,
      tilingCompressTail]
  | cons b bs ih =>
      by_cases hb : b = tilingRemovableBlock t x
      · have hrem : TilingRemovable t x (blockMiddle x b) (blockEnd x b) :=
          (tilingRemovable_block_iff t x b).2 hb
        simp only [blockPathTail, tilingCompressTail, if_pos hrem]
        rw [ih]
        subst b
        simp [deleteTilingBlocks, blockPath]
      · have hrem : ¬TilingRemovable t x (blockMiddle x b) (blockEnd x b) :=
          (tilingRemovable_block_iff t x b).not.mpr hb
        simp only [blockPathTail, tilingCompressTail, if_neg hrem]
        rw [ih]
        simp [deleteTilingBlocks, hb, blockPath, blockPathTail]

/-- Exact external point path of an arbitrary stateful block word. -/
theorem tilingExternalPath_blockPath (t : DominoTiling) (x : Point)
    (bs : List Block) :
    tilingExternalPath t (blockPath x bs) =
      blockPath x (deleteTilingBlocks t x bs) := by
  simp only [blockPath, tilingExternalPath]
  rw [tilingCompressTail_blockPathTail]
  rfl

/-- The erased point list, computed directly block by block. -/
def tilingLazyBlockTrace (t : DominoTiling) (x : Point) :
    List Block → List Point
  | [] => []
  | b :: bs =>
      (if b = tilingRemovableBlock t x then
          [blockMiddle x b, blockEnd x b]
        else []) ++
        tilingLazyBlockTrace t (blockEnd x b) bs

private theorem tilingRemovedTail_blockPathTail_eq_lazyBlockTrace
    (t : DominoTiling) (x : Point) : ∀ bs : List Block,
    tilingRemovedTail t x (blockPathTail x bs) =
      tilingLazyBlockTrace t x bs := by
  intro bs
  induction bs generalizing x with
  | nil => rfl
  | cons b bs ih =>
      by_cases hb : b = tilingRemovableBlock t x
      · have hrem : TilingRemovable t x (blockMiddle x b) (blockEnd x b) :=
          (tilingRemovable_block_iff t x b).2 hb
        simp only [blockPathTail, tilingRemovedTail, if_pos hrem,
          tilingLazyBlockTrace, if_pos hb]
        rw [ih]
        rfl
      · have hrem : ¬TilingRemovable t x (blockMiddle x b) (blockEnd x b) :=
          (tilingRemovable_block_iff t x b).not.mpr hb
        simp only [blockPathTail, tilingRemovedTail, if_neg hrem,
          tilingLazyBlockTrace, if_neg hb, List.nil_append]
        exact ih (blockEnd x b)

/-- Exact erased point path of an arbitrary stateful block word. -/
theorem tilingLazyPoints_blockPath (t : DominoTiling) (x : Point)
    (bs : List Block) :
    tilingLazyPoints t (blockPath x bs) = tilingLazyBlockTrace t x bs := by
  simp only [blockPath, tilingLazyPoints]
  exact tilingRemovedTail_blockPathTail_eq_lazyBlockTrace t x bs

theorem tilingLazyBlockTrace_append (t : DominoTiling) (x : Point)
    (as bs : List Block) :
    tilingLazyBlockTrace t x (as ++ bs) =
      tilingLazyBlockTrace t x as ++
        tilingLazyBlockTrace t (followBlocks x as) bs := by
  induction as generalizing x with
  | nil => rfl
  | cons a as ih =>
      simp only [List.cons_append, tilingLazyBlockTrace, List.append_assoc]
      rw [ih]
      rfl

@[simp] theorem followBlocks_replicate_tilingRemovable
    (t : DominoTiling) (x : Point) (n : ℕ) :
    followBlocks x (List.replicate n (tilingRemovableBlock t x)) = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [List.replicate_succ, followBlocks, List.foldl_cons,
        blockEnd_tilingRemovableBlock]
      exact ih

theorem tilingLazyBlockTrace_replicate_removable
    (t : DominoTiling) (x : Point) (n : ℕ) :
    tilingLazyBlockTrace t x
        (List.replicate n (tilingRemovableBlock t x)) =
      (List.replicate n [tilingPartner t x, x]).flatten := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [List.replicate_succ, tilingLazyBlockTrace,
        blockMiddle_tilingRemovableBlock, blockEnd_tilingRemovableBlock,
        List.flatten_cons]
      simp [ih]

/-- The erased point list prescribed directly by an insertion vector. -/
def tilingInsertionLazyTrace {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ) :
    List Point :=
  (List.ofFn fun k : Fin (i + 1) ↦
    (List.replicate (q k)
      [tilingPartner t (rawExternalBase x r.1 k),
        rawExternalBase x r.1 k]).flatten).flatten

/-- Exact erased trace of the reconstructed stateful insertion word. -/
theorem tilingLazyBlockTrace_tilingInsertGapVector {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (q : Fin (i + 1) → ℕ) :
    tilingLazyBlockTrace t x (tilingInsertGapVector t x r q) =
      tilingInsertionLazyTrace t x r q := by
  induction i generalizing x with
  | zero =>
      rw [tilingInsertGapVector_zero,
        tilingLazyBlockTrace_replicate_removable]
      simp [tilingInsertionLazyTrace, rawExternalBase_zero]
  | succ i ih =>
      have h0 : r.1 0 ≠ tilingRemovableBlock t x := by
        simpa [rawExternalBase_zero] using r.2 0
      rw [tilingInsertGapVector_succ, tilingLazyBlockTrace_append,
        tilingLazyBlockTrace_append,
        tilingLazyBlockTrace_replicate_removable]
      simp only [followBlocks_replicate_tilingRemovable,
        tilingLazyBlockTrace, if_neg h0, List.nil_append]
      rw [followBlocks_append, followBlocks_replicate_tilingRemovable]
      change (List.replicate (q 0) [tilingPartner t x, x]).flatten ++ [] ++
        tilingLazyBlockTrace t (blockEnd x (r.1 0))
          (tilingInsertGapVector t (blockEnd x (r.1 0))
            (tilingRetainedTail t x r) (fun k ↦ q k.succ)) = _
      rw [ih]
      simp only [List.append_nil]
      unfold tilingInsertionLazyTrace
      simp only [List.ofFn_succ, List.flatten_cons, rawExternalBase_zero,
        tilingRetainedTail, rawExternalBase_succ]

/-- The external path of a reconstructed insertion word is exactly the
retained path and is independent of all insertion coordinates. -/
theorem tilingExternalPath_blockPath_tilingInsertGapVector {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (q : Fin (i + 1) → ℕ) :
    tilingExternalPath t (blockPath x (tilingInsertGapVector t x r q)) =
      blockPath x (List.ofFn r.1) := by
  rw [tilingExternalPath_blockPath,
    deleteTilingBlocks_tilingInsertGapVector]

/-- The lazy path of a reconstructed insertion word is exactly the explicit
concatenation of its inserted excursions. -/
theorem tilingLazyPoints_blockPath_tilingInsertGapVector {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (q : Fin (i + 1) → ℕ) :
    tilingLazyPoints t (blockPath x (tilingInsertGapVector t x r q)) =
      tilingInsertionLazyTrace t x r q := by
  rw [tilingLazyPoints_blockPath,
    tilingLazyBlockTrace_tilingInsertGapVector]

/-! ## Optional terminal singleton and the exact away cutoff -/

theorem tilingCompressTail_blockPathTail_append_singleton
    (t : DominoTiling) (x z : Point) : ∀ bs : List Block,
    tilingCompressTail t x (blockPathTail x bs ++ [z]) =
      (blockPath x (deleteTilingBlocks t x bs)).tail ++ [z] := by
  intro bs
  induction bs generalizing x with
  | nil => rfl
  | cons b bs ih =>
      by_cases hb : b = tilingRemovableBlock t x
      · have hrem : TilingRemovable t x (blockMiddle x b) (blockEnd x b) :=
          (tilingRemovable_block_iff t x b).2 hb
        simp only [blockPathTail, List.cons_append, tilingCompressTail,
          if_pos hrem]
        rw [ih]
        subst b
        simp [deleteTilingBlocks, blockPath]
      · have hrem : ¬TilingRemovable t x (blockMiddle x b) (blockEnd x b) :=
          (tilingRemovable_block_iff t x b).not.mpr hb
        simp only [blockPathTail, List.cons_append, tilingCompressTail,
          if_neg hrem]
        rw [ih]
        simp [deleteTilingBlocks, hb, blockPath, blockPathTail]

theorem tilingExternalPath_blockPath_append_singleton
    (t : DominoTiling) (x z : Point) (bs : List Block) :
    tilingExternalPath t (blockPath x bs ++ [z]) =
      blockPath x (deleteTilingBlocks t x bs) ++ [z] := by
  simp only [blockPath, List.cons_append, tilingExternalPath]
  rw [tilingCompressTail_blockPathTail_append_singleton]
  simp [blockPath]

theorem tilingRemovedTail_blockPathTail_append_singleton
    (t : DominoTiling) (x z : Point) : ∀ bs : List Block,
    tilingRemovedTail t x (blockPathTail x bs ++ [z]) =
      tilingRemovedTail t x (blockPathTail x bs) := by
  intro bs
  induction bs generalizing x with
  | nil => rfl
  | cons b bs ih =>
      by_cases hb : b = tilingRemovableBlock t x
      · have hrem : TilingRemovable t x (blockMiddle x b) (blockEnd x b) :=
          (tilingRemovable_block_iff t x b).2 hb
        simp only [blockPathTail, List.cons_append, tilingRemovedTail,
          if_pos hrem, List.cons.injEq, true_and]
        exact ih (blockEnd x b)
      · have hrem : ¬TilingRemovable t x (blockMiddle x b) (blockEnd x b) :=
          (tilingRemovable_block_iff t x b).not.mpr hb
        simp only [blockPathTail, List.cons_append, tilingRemovedTail,
          if_neg hrem]
        exact ih (blockEnd x b)

theorem tilingLazyPoints_blockPath_append_singleton
    (t : DominoTiling) (x z : Point) (bs : List Block) :
    tilingLazyPoints t (blockPath x bs ++ [z]) =
      tilingLazyPoints t (blockPath x bs) := by
  simp only [blockPath, List.cons_append, tilingLazyPoints]
  exact tilingRemovedTail_blockPathTail_append_singleton t x z bs

/-- A block path with the possible unpaired terminal point. -/
def tilingPrefixPointPath (x : Point) (bs : List Block) :
    Option Point → List Point
  | none => blockPath x bs
  | some z => blockPath x bs ++ [z]

/-- Frozen external local time for an arbitrary tiling retained word. -/
def tilingFixedBoundaryLocalTime {i : ℕ} {t : DominoTiling} (x : Point)
    (r : TilingRetainedWord t x i) (terminal : Option Point)
    (y : Point) : ℕ :=
  listLocalTime (tilingPrefixPointPath x (List.ofFn r.1) terminal) y

theorem tilingExternalPath_insertedPrefix {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (q : Fin (i + 1) → ℕ) (terminal : Option Point) :
    tilingExternalPath t
        (tilingPrefixPointPath x (tilingInsertGapVector t x r q) terminal) =
      tilingPrefixPointPath x (List.ofFn r.1) terminal := by
  cases terminal with
  | none =>
      change tilingExternalPath t
          (blockPath x (tilingInsertGapVector t x r q)) =
        blockPath x (List.ofFn r.1)
      exact TilingSpatialInsertionFiber.tilingExternalPath_insertedPath t x r q
  | some z =>
      rw [tilingPrefixPointPath, tilingExternalPath_blockPath_append_singleton,
        deleteTilingBlocks_tilingInsertGapVector]
      rfl

theorem tilingLazyPoints_insertedPrefix {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (q : Fin (i + 1) → ℕ) (terminal : Option Point) :
    tilingLazyPoints t
        (tilingPrefixPointPath x (tilingInsertGapVector t x r q) terminal) =
      tilingLazyPoints t
        (blockPath x (tilingInsertGapVector t x r q)) := by
  cases terminal with
  | none => rfl
  | some z =>
      exact tilingLazyPoints_blockPath_append_singleton t x z _

/-- Exact external-plus-lazy local time at any endpoint of a represented
tiling domino, including the possible terminal singleton. -/
theorem tilingInsertedPrefix_localTime_at_dominoPoint {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (q : Fin (i + 1) → ℕ) (terminal : Option Point)
    (b : TilingExternalDomino t x r) (y : Point)
    (hy : tilingBase t y = b.1) :
    listLocalTime
        (tilingPrefixPointPath x (tilingInsertGapVector t x r q) terminal) y =
      tilingFixedBoundaryLocalTime x r terminal y +
        tilingDominoTotal t x r q b := by
  rw [tilingListLocalTime_split,
    tilingExternalPath_insertedPrefix,
    tilingLazyPoints_insertedPrefix]
  unfold tilingFixedBoundaryLocalTime
  rw [TilingSpatialInsertionFiber.tilingLazyLocalTime_insertedPath,
    tilingInsertionLazyLocalTime_at_dominoPoint t x r q b y hy]

/-- Larger frozen endpoint local time on one tiling domino. -/
def tilingFixedBoundaryDominoMax {i : ℕ} {t : DominoTiling} (x : Point)
    (r : TilingRetainedWord t x i) (terminal : Option Point)
    (b : TilingExternalDomino t x r) : ℕ :=
  max (tilingFixedBoundaryLocalTime x r terminal b.1)
    (tilingFixedBoundaryLocalTime x r terminal (tilingPartner t b.1))

theorem tilingBase_idem (t : DominoTiling) (y : Point) :
    tilingBase t (tilingBase t y) = tilingBase t y := by
  rcases point_eq_tilingBase_or_partner_base t y with h | h
  · nth_rewrite 1 [← h]
    rfl
  · calc
      tilingBase t (tilingBase t y) =
          tilingBase t (tilingPartner t (tilingBase t y)) :=
        (tilingBase_partner t (tilingBase t y)).symm
      _ = tilingBase t y := by rw [← h]

theorem tilingExternalDomino_isBase {i : ℕ} (t : DominoTiling)
    (x : Point) (r : TilingRetainedWord t x i)
    (b : TilingExternalDomino t x r) : tilingBase t b.1 = b.1 := by
  obtain ⟨k, _hk, hkb⟩ := Finset.mem_image.mp b.2
  rw [← hkb]
  exact tilingBase_idem t _

/-- Actual endpoint condition away from distinguished tiling dominoes. -/
def TilingActualEndpointsBelow {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (terminal : Option Point)
    (m : ℕ) (D : Finset Point) (q : Fin (i + 1) → ℕ) : Prop :=
  ∀ b : TilingExternalDomino t x r, b.1 ∉ D →
    listLocalTime
        (tilingPrefixPointPath x (tilingInsertGapVector t x r q) terminal)
        b.1 < m ∧
      listLocalTime
        (tilingPrefixPointPath x (tilingInsertGapVector t x r q) terminal)
        (tilingPartner t b.1) < m

/-- The coordinatewise strict away cutoff fixed by the favorite data. -/
def TilingDominoTruncation {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (terminal : Option Point)
    (m : ℕ) (D : Finset Point) (q : Fin (i + 1) → ℕ) : Prop :=
  ∀ b : TilingExternalDomino t x r, b.1 ∉ D →
    tilingDominoTotal t x r q b <
      m - tilingFixedBoundaryDominoMax x r terminal b

/-- Literal all-six form of the HLOZ observation: after the external trace
and favorite dominoes are frozen, the level condition imposes exactly one
strict upper truncation on each away-domino total. -/
theorem tilingActualEndpointsBelow_iff_dominoTruncation {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (m : ℕ) (D : Finset Point)
    (q : Fin (i + 1) → ℕ) :
    TilingActualEndpointsBelow t x r terminal m D q ↔
      TilingDominoTruncation t x r terminal m D q := by
  constructor
  · intro h b hb
    have hend := h b hb
    rw [tilingInsertedPrefix_localTime_at_dominoPoint t x r q terminal b b.1
        (tilingExternalDomino_isBase t x r b),
      tilingInsertedPrefix_localTime_at_dominoPoint t x r q terminal b
        (tilingPartner t b.1)
        ((tilingBase_partner t b.1).trans
          (tilingExternalDomino_isBase t x r b))] at hend
    apply Nat.lt_sub_iff_add_lt.mpr
    unfold tilingFixedBoundaryDominoMax
    rw [add_comm, max_add]
    exact max_lt hend.1 hend.2
  · intro h b hb
    have hsum := Nat.lt_sub_iff_add_lt.mp (h b hb)
    unfold tilingFixedBoundaryDominoMax at hsum
    rw [add_comm, max_add, max_lt_iff] at hsum
    rw [tilingInsertedPrefix_localTime_at_dominoPoint t x r q terminal b b.1
        (tilingExternalDomino_isBase t x r b),
      tilingInsertedPrefix_localTime_at_dominoPoint t x r q terminal b
        (tilingPartner t b.1)
        ((tilingBase_partner t b.1).trans
          (tilingExternalDomino_isBase t x r b))]
    exact hsum

/-! ## Exact favorite-set identification -/

/-- A point outside the frozen favorite tiling bases has strict local time
below the favorite level. -/
theorem localTime_lt_level_of_tilingBase_not_favorite
    (t : DominoTiling) (s : WalkPath) (n m : ℕ) (hm : 0 < m)
    (hsites : thresholdSites s n m = favoriteSites s n)
    (y : Point) (hy : tilingBase t y ∉ favoriteTilingBases t s n) :
    localTime s n y < m := by
  by_contra hnot
  have hge : m ≤ localTime s n y := Nat.le_of_not_gt hnot
  have hthreshold : y ∈ thresholdSites s n m :=
    (mem_thresholdSites_iff s n m y hm).mpr hge
  have hfavorite : y ∈ favoriteSites s n := by
    rw [← hsites]
    exact hthreshold
  exact hy (mem_favoriteTilingBases hfavorite)

/-- If a reconstructed all-six tiling fibre is the literal stopped prefix
and its distinguished bases are exactly the favorite bases, then its away
coordinates satisfy the corrected strict cutoff. -/
theorem tilingDominoTruncation_of_exact_favorite_prefix {i : ℕ}
    (t : DominoTiling) (s : WalkPath) (n m : ℕ) (hm : 0 < m)
    (hsites : thresholdSites s n m = favoriteSites s n)
    (x : Point) (r : TilingRetainedWord t x i)
    (q : Fin (i + 1) → ℕ) (terminal : Option Point)
    (hpath : finitePathList (pathPrefix s n) =
      tilingPrefixPointPath x (tilingInsertGapVector t x r q) terminal) :
    TilingDominoTruncation t x r terminal m
      (favoriteTilingBases t s n) q := by
  rw [← tilingActualEndpointsBelow_iff_dominoTruncation]
  intro b hb
  have hbase : tilingBase t b.1 = b.1 :=
    tilingExternalDomino_isBase t x r b
  have hpartner : tilingBase t (tilingPartner t b.1) = b.1 :=
    (tilingBase_partner t b.1).trans hbase
  constructor
  · rw [← hpath, ← localTime_eq_listLocalTime]
    exact localTime_lt_level_of_tilingBase_not_favorite
      t s n m hm hsites b.1 (by simpa [hbase] using hb)
  · rw [← hpath, ← localTime_eq_listLocalTime]
    exact localTime_lt_level_of_tilingBase_not_favorite
      t s n m hm hsites (tilingPartner t b.1)
        (by simpa [hpartner] using hb)

/-- Creation-clock specialization of the preceding literal favorite-set
identification, strictly before the artificial cutoff. -/
theorem tilingDominoTruncation_at_truncatedLevelTime {i : ℕ}
    (t : DominoTiling) (m k cutoff n : ℕ) (omega : StepPath)
    (hm : 0 < m) (hk : 0 < k) (hn : n < cutoff)
    (htime : truncatedLevelTime m k cutoff omega = n)
    (hfavorite : levelFavorite (trajectory omega) m k)
    (x : Point) (r : TilingRetainedWord t x i)
    (q : Fin (i + 1) → ℕ) (terminal : Option Point)
    (hpath : finitePathList (pathPrefix (trajectory omega) n) =
      tilingPrefixPointPath x (tilingInsertGapVector t x r q) terminal) :
    TilingDominoTruncation t x r terminal m
      (favoriteTilingBases t (trajectory omega) n) q := by
  apply tilingDominoTruncation_of_exact_favorite_prefix
    t (trajectory omega) n m hm _ x r q terminal hpath
  exact thresholdSites_eq_favoriteSites_at_truncatedLevelTime
    m k cutoff n omega hk hn htime hfavorite

end

end Erdos1165.TilingInsertedLocalTime
