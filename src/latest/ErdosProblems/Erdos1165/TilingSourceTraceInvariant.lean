/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingThresholdHitRecordInvariant
import ErdosProblems.Erdos1165.TilingPrefixedInsertedLocalTime

/-!
# Trace invariance after deleting a prescribed set of tiling dominoes

The distinguished-coordinate projection used elsewhere retains represented
dominoes outside a source support.  For creation-prefix data we must also
retain fixed, unrepresented boundary sites.  The Boolean filter below does
exactly that: it deletes a point precisely when its tiling base lies in the
source support.
-/

namespace Erdos1165.TilingSourceTraceInvariant

open LazyDecomposition PathInsertion SpatialInsertionFiber
open TilingCappedMarginalization TilingLazyDecomposition
open TilingInsertedLocalTime
open TilingPrefixedInsertedLocalTime TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

def pointOutsideTilingBases (t : DominoTiling) (S : Finset Point)
    (y : Point) : Bool := decide (tilingBase t y ∉ S)

/-- Delete removable tiling returns exactly at bases in `S`. -/
def eraseInsideTilingReturns (t : DominoTiling) (S : Finset Point) :
    Point → List Block → List Block
  | _, [] => []
  | x, b :: bs =>
      if b = tilingRemovableBlock t x ∧ tilingBase t x ∈ S then
        eraseInsideTilingReturns t S x bs
      else b :: eraseInsideTilingReturns t S (blockEnd x b) bs

theorem filter_blockPathTail_eraseInsideTilingReturns
    (t : DominoTiling) (S : Finset Point) (x : Point) :
    ∀ bs : List Block,
      (blockPathTail x bs).filter (pointOutsideTilingBases t S) =
        (blockPathTail x (eraseInsideTilingReturns t S x bs)).filter
          (pointOutsideTilingBases t S) := by
  intro bs
  induction bs generalizing x with
  | nil => rfl
  | cons b bs ih =>
      by_cases hskip : b = tilingRemovableBlock t x ∧ tilingBase t x ∈ S
      · rcases hskip with ⟨rfl, hx⟩
        simp only [eraseInsideTilingReturns, true_and, hx, if_pos,
          blockPathTail, blockMiddle_tilingRemovableBlock,
          blockEnd_tilingRemovableBlock]
        have hpartner : tilingBase t (tilingPartner t x) ∈ S := by
          rw [tilingBase_partner]
          exact hx
        simp only [List.filter_cons, pointOutsideTilingBases,
          decide_eq_false_iff_not, not_not, hpartner, Bool.false_eq_true,
          if_false, hx]
        exact ih x
      · simp only [eraseInsideTilingReturns, if_neg hskip, blockPathTail,
          List.filter_cons]
        rw [ih]

theorem filter_blockPath_eraseInsideTilingReturns
    (t : DominoTiling) (S : Finset Point) (x : Point) (bs : List Block) :
    (blockPath x bs).filter (pointOutsideTilingBases t S) =
      (blockPath x (eraseInsideTilingReturns t S x bs)).filter
        (pointOutsideTilingBases t S) := by
  simp only [blockPath, List.filter_cons]
  rw [filter_blockPathTail_eraseInsideTilingReturns]

@[simp] theorem eraseInsideTilingReturns_replicate_removable
    (t : DominoTiling) (S : Finset Point) (x : Point) (n : ℕ) :
    eraseInsideTilingReturns t S x
        (List.replicate n (tilingRemovableBlock t x)) =
      if tilingBase t x ∈ S then []
      else List.replicate n (tilingRemovableBlock t x) := by
  induction n with
  | zero => simp [eraseInsideTilingReturns]
  | succ n ih =>
      rw [List.replicate_succ]
      by_cases hx : tilingBase t x ∈ S
      · simp [eraseInsideTilingReturns, hx, ih]
      · simp [eraseInsideTilingReturns, hx, ih]

theorem eraseInsideTilingReturns_append (t : DominoTiling)
    (S : Finset Point) (x : Point) (as bs : List Block) :
    eraseInsideTilingReturns t S x (as ++ bs) =
      eraseInsideTilingReturns t S x as ++
        eraseInsideTilingReturns t S (followBlocks x as) bs := by
  induction as generalizing x with
  | nil => rfl
  | cons a as ih =>
      by_cases hskip : a = tilingRemovableBlock t x ∧ tilingBase t x ∈ S
      · rcases hskip with ⟨rfl, hx⟩
        simp only [List.cons_append, eraseInsideTilingReturns, true_and, hx,
          if_pos, blockEnd_tilingRemovableBlock]
        rw [ih]
        simp [eraseInsideTilingReturns, hx, followBlocks]
      · simp only [List.cons_append, eraseInsideTilingReturns, if_neg hskip]
        rw [ih]
        rfl

theorem eraseInsideTilingReturns_tilingInsertGapVector_eq_of_coordinates
    {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (S : Finset Point)
    (q q' : Fin (i + 1) → ℕ)
    (hq : ∀ k, tilingBase t (rawExternalBase x r.1 k) ∉ S →
      q k = q' k) :
    eraseInsideTilingReturns t S x (tilingInsertGapVector t x r q) =
      eraseInsideTilingReturns t S x (tilingInsertGapVector t x r q') := by
  induction i generalizing x with
  | zero =>
      rw [tilingInsertGapVector_zero, tilingInsertGapVector_zero,
        eraseInsideTilingReturns_replicate_removable,
        eraseInsideTilingReturns_replicate_removable]
      split
      · rfl
      · rename_i hx
        rw [hq 0 (by rw [rawExternalBase_zero]; exact hx)]
  | succ i ih =>
      rw [tilingInsertGapVector_succ, tilingInsertGapVector_succ,
        eraseInsideTilingReturns_append, eraseInsideTilingReturns_append]
      rw [eraseInsideTilingReturns_append, eraseInsideTilingReturns_append]
      rw [eraseInsideTilingReturns_replicate_removable,
        eraseInsideTilingReturns_replicate_removable]
      by_cases hx : tilingBase t x ∈ S
      · rw [if_pos hx, if_pos hx]
        simp only [List.nil_append]
        rw [followBlocks_append x
            (List.replicate (q 0) (tilingRemovableBlock t x)) [r.1 0],
          followBlocks_append x
            (List.replicate (q' 0) (tilingRemovableBlock t x)) [r.1 0]]
        simp_rw [TilingSpatialInsertionFiber.followBlocks_replicate_tilingRemovable]
        simp only [followBlocks, List.foldl_cons, List.foldl_nil]
        congr 1
        apply ih
        intro k hk
        exact hq k.succ (by
          simpa only [rawExternalBase_succ, tilingRetainedTail] using hk)
      · rw [if_neg hx, if_neg hx]
        rw [hq 0 (by rw [rawExternalBase_zero]; exact hx)]
        rw [followBlocks_append x
          (List.replicate (q' 0) (tilingRemovableBlock t x)) [r.1 0]]
        simp_rw [TilingSpatialInsertionFiber.followBlocks_replicate_tilingRemovable]
        simp only [followBlocks, List.foldl_cons, List.foldl_nil]
        congr 1
        apply ih
        intro k hk
        exact hq k.succ (by
          simpa only [rawExternalBase_succ, tilingRetainedTail] using hk)

theorem eraseInsideTilingReturns_tilingInsertGapVector_eq {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (S : Finset Point) (q q' : TilingCappedCoordinates i cap)
    (hdist : (splitTilingCoordinatesEquiv t x r
        (tilingExternalDominoBases t x r \ S) q).1 =
      (splitTilingCoordinatesEquiv t x r
        (tilingExternalDominoBases t x r \ S) q').1) :
    eraseInsideTilingReturns t S x
        (tilingInsertGapVector t x r (fun k ↦ (q k : ℕ))) =
      eraseInsideTilingReturns t S x
        (tilingInsertGapVector t x r (fun k ↦ (q' k : ℕ))) := by
  apply eraseInsideTilingReturns_tilingInsertGapVector_eq_of_coordinates
  intro k hk
  apply congrArg (fun z : Fin (cap + 1) ↦ (z : ℕ))
  apply TilingDistinguishedTraceInvariant.cappedCoordinate_eq_of_distinguished_projection
    t x r (tilingExternalDominoBases t x r \ S) q q' hdist k
  exact Finset.mem_sdiff.mpr ⟨
    Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩, hk⟩

theorem filter_tilingPrefixPointPath_tilingInsertGapVector_outside_eq
    {i cap : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (terminal : Option Point)
    (S : Finset Point) (q q' : TilingCappedCoordinates i cap)
    (hdist : (splitTilingCoordinatesEquiv t x r
        (tilingExternalDominoBases t x r \ S) q).1 =
      (splitTilingCoordinatesEquiv t x r
        (tilingExternalDominoBases t x r \ S) q').1) :
    (tilingPrefixPointPath x
        (tilingInsertGapVector t x r (fun k ↦ (q k : ℕ))) terminal).filter
          (pointOutsideTilingBases t S) =
      (tilingPrefixPointPath x
        (tilingInsertGapVector t x r (fun k ↦ (q' k : ℕ))) terminal).filter
          (pointOutsideTilingBases t S) := by
  calc
    _ = (tilingPrefixPointPath x
          (eraseInsideTilingReturns t S x
            (tilingInsertGapVector t x r (fun k ↦ (q k : ℕ)))) terminal).filter
          (pointOutsideTilingBases t S) := by
      cases terminal with
      | none => exact filter_blockPath_eraseInsideTilingReturns t S x _
      | some z =>
          simp only [tilingPrefixPointPath, List.filter_append]
          rw [filter_blockPath_eraseInsideTilingReturns]
    _ = (tilingPrefixPointPath x
          (eraseInsideTilingReturns t S x
            (tilingInsertGapVector t x r (fun k ↦ (q' k : ℕ)))) terminal).filter
          (pointOutsideTilingBases t S) := by
      rw [eraseInsideTilingReturns_tilingInsertGapVector_eq
        t x r S q q' hdist]
    _ = _ := by
      cases terminal with
      | none => exact (filter_blockPath_eraseInsideTilingReturns t S x _).symm
      | some z =>
          simp only [tilingPrefixPointPath, List.filter_append]
          congr 1
          exact (filter_blockPath_eraseInsideTilingReturns t S x _).symm

theorem filter_prefixedTilingPrefixPointPath_tilingInsertGapVector_outside_eq
    (initial : List Direction) {i cap : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (terminal : Option Point)
    (S : Finset Point) (q q' : TilingCappedCoordinates i cap)
    (hdist : (splitTilingCoordinatesEquiv t x r
        (tilingExternalDominoBases t x r \ S) q).1 =
      (splitTilingCoordinatesEquiv t x r
        (tilingExternalDominoBases t x r \ S) q').1) :
    (prefixedTilingPrefixPointPath initial x
        (tilingInsertGapVector t x r (fun k ↦ (q k : ℕ))) terminal).filter
          (pointOutsideTilingBases t S) =
      (prefixedTilingPrefixPointPath initial x
        (tilingInsertGapVector t x r (fun k ↦ (q' k : ℕ))) terminal).filter
          (pointOutsideTilingBases t S) := by
  have filter_tail_eq_of_filter_eq_of_head_eq
      (P : Point → Bool) (a b : List Point) (z : Point)
      (ha : a.head? = some z) (hb : b.head? = some z)
      (hfilter : a.filter P = b.filter P) :
      a.tail.filter P = b.tail.filter P := by
    cases a with
    | nil => simp at ha
    | cons a as =>
        cases b with
        | nil => simp at hb
        | cons b bs =>
            simp only [List.head?_cons, Option.some.injEq] at ha hb
            subst a
            subst b
            simp only [List.tail_cons]
            by_cases hz : P z = true
            · simpa [hz] using hfilter
            · have hz' : P z = false := Bool.eq_false_of_not_eq_true hz
              simpa [hz'] using hfilter
  have hfull := filter_tilingPrefixPointPath_tilingInsertGapVector_outside_eq
    t x r terminal S q q' hdist
  have hhead : (tilingPrefixPointPath x
      (tilingInsertGapVector t x r (fun k ↦ (q k : ℕ))) terminal).head? =
      some x := by
    cases terminal <;> simp [tilingPrefixPointPath, blockPath]
  have hhead' : (tilingPrefixPointPath x
      (tilingInsertGapVector t x r (fun k ↦ (q' k : ℕ))) terminal).head? =
      some x := by
    cases terminal <;> simp [tilingPrefixPointPath, blockPath]
  have htail := filter_tail_eq_of_filter_eq_of_head_eq
    (pointOutsideTilingBases t S) _ _ x hhead hhead' hfull
  unfold prefixedTilingPrefixPointPath
  simp only [List.filter_append]
  rw [htail]

end

end Erdos1165.TilingSourceTraceInvariant
