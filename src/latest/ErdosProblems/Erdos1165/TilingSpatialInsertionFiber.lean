/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingLazyDecomposition
import ErdosProblems.Erdos1165.VariableStoppedFiber

/-!
# Stateful insertion fibres for the six HLOZ tilings

For a column tiling the removable two-step block depends on the current
lattice site.  Consequently a retained word cannot be typed merely by
excluding one fixed letter of the sixteen-letter block alphabet.  This file
uses the external spatial base before each retained block to select the one
removable letter at that coordinate.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.TilingSpatialInsertionFiber

open LazyDecomposition PathInsertion SpatialInsertionFiber StoppedInsertion
open TilingLazyDecomposition VariableStoppedFiber PreStoppingFiber

abbrev DominoTiling := Tilings.Tiling

/-- The unique two-increment return through the mate of `x`. -/
def tilingRemovableBlock (t : DominoTiling) (x : Point) : Block :=
  (tilingPartnerDirection t x,
    tilingPartnerDirection t (tilingPartner t x))

@[simp] theorem blockMiddle_tilingRemovableBlock (t : DominoTiling) (x : Point) :
    blockMiddle x (tilingRemovableBlock t x) = tilingPartner t x := by
  rw [blockMiddle, tilingRemovableBlock, tilingPartner_eq_add_directionVector]

@[simp] theorem blockEnd_tilingRemovableBlock (t : DominoTiling) (x : Point) :
    blockEnd x (tilingRemovableBlock t x) = x := by
  rw [blockEnd, tilingRemovableBlock]
  rw [← tilingPartner_eq_add_directionVector t x]
  rw [← tilingPartner_eq_add_directionVector t (tilingPartner t x)]
  exact tilingPartner_partner t x

theorem tilingRemovable_block_iff (t : DominoTiling) (x : Point) (b : Block) :
    TilingRemovable t x (blockMiddle x b) (blockEnd x b) ↔
      b = tilingRemovableBlock t x := by
  constructor
  · rintro ⟨hmiddle, hend⟩
    apply Prod.ext
    · apply directionVector_injective
      apply add_left_cancel (a := x)
      simpa [blockMiddle, tilingRemovableBlock,
        tilingPartner_eq_add_directionVector] using hmiddle
    · have hfirst : b.1 = tilingPartnerDirection t x := by
        apply directionVector_injective
        apply add_left_cancel (a := x)
        simpa [blockMiddle, tilingRemovableBlock,
          tilingPartner_eq_add_directionVector] using hmiddle
      unfold blockEnd at hend
      rw [hfirst] at hend
      change b.2 = tilingPartnerDirection t (tilingPartner t x)
      apply directionVector_injective
      apply add_left_cancel (a := tilingPartner t x)
      rw [← tilingPartner_eq_add_directionVector t (tilingPartner t x),
        tilingPartner_partner]
      simpa [blockEnd, tilingPartner_eq_add_directionVector] using hend
  · rintro rfl
    exact ⟨blockMiddle_tilingRemovableBlock t x,
      blockEnd_tilingRemovableBlock t x⟩

/-- Stateful deletion of removable block letters. -/
def deleteTilingBlocks (t : DominoTiling) : Point → List Block → List Block
  | _, [] => []
  | x, b :: bs =>
      if b = tilingRemovableBlock t x then deleteTilingBlocks t x bs
      else b :: deleteTilingBlocks t (blockEnd x b) bs

/-- The spatial base before the `k`-th block of a raw external word. -/
def rawExternalBase {i : ℕ} (x : Point) (r : Fin i → Block)
    (k : Fin (i + 1)) : Point :=
  followBlocks x ((List.ofFn r).take k)

@[simp] theorem rawExternalBase_zero {i : ℕ} (x : Point) (r : Fin i → Block) :
    rawExternalBase x r 0 = x := by
  simp [rawExternalBase, followBlocks]

theorem rawExternalBase_succ {i : ℕ} (x : Point)
    (r : Fin (i + 1) → Block) (k : Fin (i + 1)) :
    rawExternalBase x r k.succ =
      rawExternalBase (blockEnd x (r 0)) (fun j ↦ r j.succ) k := by
  simp [rawExternalBase, List.ofFn_succ, followBlocks,
    List.take_succ_cons]

theorem rawExternalBase_succ_castSucc {i : ℕ} (x : Point)
    (r : Fin (i + 1) → Block) (k : Fin i) :
    rawExternalBase x r k.succ.castSucc =
      rawExternalBase (blockEnd x (r 0)) (fun j ↦ r j.succ) k.castSucc := by
  rw [show k.succ.castSucc = k.castSucc.succ by apply Fin.ext; rfl]
  exact rawExternalBase_succ x r k.castSucc

private theorem fin_succ_castSucc {i : ℕ} (k : Fin i) :
    k.succ.castSucc = k.castSucc.succ := by
  apply Fin.ext
  rfl

/-- A retained word is statefully valid when no letter is the removable
letter at the spatial base where that letter is read. -/
def ValidTilingRetainedWord (t : DominoTiling) {i : ℕ} (x : Point)
    (r : Fin i → Block) : Prop :=
  ∀ k, r k ≠ tilingRemovableBlock t (rawExternalBase x r k.castSucc)

/-- A statefully retained word of fixed length. -/
abbrev TilingRetainedWord (t : DominoTiling) (x : Point) (i : ℕ) :=
  {r : Fin i → Block // ValidTilingRetainedWord t x r}

/-- Dropping the first external letter preserves stateful validity, with the
spatial start advanced to the endpoint of that letter. -/
def tilingRetainedTail {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x (i + 1)) :
    TilingRetainedWord t (blockEnd x (r.1 0)) i :=
  ⟨fun k ↦ r.1 k.succ, fun k h ↦ by
    exact r.2 k.succ (by simpa [rawExternalBase_succ] using h)⟩

/-- Insert a run at every external base, including the terminal base. -/
def tilingInsertGapVector {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ) : List Block :=
  ((List.ofFn fun k : Fin i ↦
      List.replicate (q k.castSucc)
          (tilingRemovableBlock t (rawExternalBase x r.1 k.castSucc)) ++
        [r.1 k]).flatten) ++
    List.replicate (q (Fin.last i))
      (tilingRemovableBlock t (rawExternalBase x r.1 (Fin.last i)))

@[simp] theorem tilingInsertGapVector_length {i : ℕ} (t : DominoTiling)
    (x : Point) (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ) :
    (tilingInsertGapVector t x r q).length = i + ∑ k, q k := by
  classical
  simp [tilingInsertGapVector, List.length_flatten, List.sum_ofFn,
    Fin.sum_univ_castSucc, Finset.sum_add_distrib]
  ac_rfl

@[simp] theorem tilingInsertGapVector_zero (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x 0) (q : Fin 1 → ℕ) :
    tilingInsertGapVector t x r q =
      List.replicate (q 0) (tilingRemovableBlock t x) := by
  simp [tilingInsertGapVector]

theorem tilingInsertGapVector_succ {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x (i + 1)) (q : Fin (i + 2) → ℕ) :
    tilingInsertGapVector t x r q =
      List.replicate (q 0) (tilingRemovableBlock t x) ++ [r.1 0] ++
        tilingInsertGapVector t (blockEnd x (r.1 0))
          (tilingRetainedTail t x r) (fun k ↦ q k.succ) := by
  have hlast : (Fin.last (i + 1) : Fin (i + 2)) = (Fin.last i).succ := by
    apply Fin.ext
    rfl
  unfold tilingInsertGapVector
  simp only [List.ofFn_succ, List.flatten_cons]
  rw [List.append_assoc]
  simp only [Fin.castSucc_zero, rawExternalBase_zero, tilingRetainedTail,
    rawExternalBase_succ_castSucc, fin_succ_castSucc, hlast,
    rawExternalBase_succ]

/-! ## Stateful uniqueness of insertion coordinates -/

/-- Decode the completed removable run before every retained block, together
with the terminal removable run.  The current spatial point is part of the
decoder state. -/
def decodeTilingRunsAux (t : DominoTiling) :
    Point → ℕ → List Block → List (ℕ × Block) × ℕ
  | _, a, [] => ([], a)
  | x, a, b :: bs =>
      if b = tilingRemovableBlock t x then
        decodeTilingRunsAux t x (a + 1) bs
      else
        let z := decodeTilingRunsAux t (blockEnd x b) 0 bs
        ((a, b) :: z.1, z.2)

@[simp] theorem decodeTilingRunsAux_replicate (t : DominoTiling) (x : Point)
    (a n : ℕ) :
    decodeTilingRunsAux t x a
        (List.replicate n (tilingRemovableBlock t x)) = ([], a + n) := by
  induction n generalizing a with
  | zero => simp [decodeTilingRunsAux]
  | succ n ih =>
      simp [List.replicate_succ, decodeTilingRunsAux, ih, Nat.add_assoc]
      omega

theorem decodeTilingRunsAux_replicate_cons (t : DominoTiling) (x : Point)
    (a n : ℕ) (b : Block) (bs : List Block)
    (hb : b ≠ tilingRemovableBlock t x) :
    decodeTilingRunsAux t x a
        (List.replicate n (tilingRemovableBlock t x) ++ b :: bs) =
      let z := decodeTilingRunsAux t (blockEnd x b) 0 bs
      ((a + n, b) :: z.1, z.2) := by
  induction n generalizing a with
  | zero => simp [decodeTilingRunsAux, hb]
  | succ n ih =>
      simp only [List.replicate_succ, List.cons_append, decodeTilingRunsAux,
        if_pos rfl]
      rw [ih (a + 1)]
      simp only [ite_true]
      congr 3
      omega

private theorem decodeTilingRunsAux_tilingInsertGapVector {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (q : Fin (i + 1) → ℕ) :
    decodeTilingRunsAux t x 0 (tilingInsertGapVector t x r q) =
      (List.ofFn fun k : Fin i ↦ (q k.castSucc, r.1 k), q (Fin.last i)) := by
  induction i generalizing x with
  | zero =>
      rw [tilingInsertGapVector_zero, decodeTilingRunsAux_replicate]
      simp
  | succ i ih =>
      rw [tilingInsertGapVector_succ]
      rw [List.append_assoc]
      simp only [List.singleton_append]
      rw [decodeTilingRunsAux_replicate_cons t x 0 (q 0) (r.1 0) _ (r.2 0)]
      rw [ih]
      have hlast : (Fin.last (i + 1) : Fin (i + 2)) = (Fin.last i).succ := by
        apply Fin.ext
        rfl
      simp only [zero_add, List.ofFn_succ, tilingRetainedTail, Fin.castSucc_zero,
        fin_succ_castSucc, hlast]

/-- A fixed valid stateful retained word has unique insertion coordinates. -/
theorem tilingInsertGapVector_injective {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) :
    Function.Injective (tilingInsertGapVector t x r) := by
  intro q q' hqq'
  have hdecode := congrArg (decodeTilingRunsAux t x 0) hqq'
  rw [decodeTilingRunsAux_tilingInsertGapVector,
    decodeTilingRunsAux_tilingInsertGapVector] at hdecode
  have hpairs :
      (List.ofFn fun k : Fin i ↦ (q k.castSucc, r.1 k)) =
        List.ofFn fun k : Fin i ↦ (q' k.castSucc, r.1 k) :=
    congrArg Prod.fst hdecode
  have hlead : ∀ k : Fin i, q k.castSucc = q' k.castSucc := fun k ↦
    congrArg Prod.fst (congrFun (List.ofFn_injective hpairs) k)
  have hlast : q (Fin.last i) = q' (Fin.last i) :=
    congrArg Prod.snd hdecode
  funext k
  exact Fin.lastCases hlast hlead k

/-! ## Canonical stateful factorization of a raw block word -/

/-- Add one valid retained letter at the front of a statefully valid word. -/
def tilingRetainedCons {i : ℕ} (t : DominoTiling) (x : Point) (b : Block)
    (hb : b ≠ tilingRemovableBlock t x)
    (r : TilingRetainedWord t (blockEnd x b) i) :
    TilingRetainedWord t x (i + 1) :=
  ⟨Fin.cases b r.1, fun k ↦ by
    refine Fin.cases ?_ (fun j ↦ ?_) k
    · simpa [rawExternalBase_zero] using hb
    · change r.1 j ≠
        tilingRemovableBlock t
          (rawExternalBase x (Fin.cases b r.1) j.succ.castSucc)
      rw [rawExternalBase_succ_castSucc]
      simpa using r.2 j⟩

/-- Increase only the initial removable run. -/
def tilingBumpFirstGap {i : ℕ} (q : Fin (i + 1) → ℕ) :
    Fin (i + 1) → ℕ :=
  Fin.cases (q 0 + 1) (fun k ↦ q k.succ)

theorem tilingInsertGapVector_bumpFirst {i : ℕ} (t : DominoTiling)
    (x : Point) (r : TilingRetainedWord t x i)
    (q : Fin (i + 1) → ℕ) :
    tilingInsertGapVector t x r (tilingBumpFirstGap q) =
      tilingRemovableBlock t x :: tilingInsertGapVector t x r q := by
  cases i with
  | zero =>
      rw [tilingInsertGapVector_zero, tilingInsertGapVector_zero]
      simp [tilingBumpFirstGap, List.replicate_succ]
  | succ i =>
      rw [tilingInsertGapVector_succ, tilingInsertGapVector_succ]
      simp [tilingBumpFirstGap, List.replicate_succ]

theorem deleteTilingBlocks_replicate_append (t : DominoTiling) (x : Point)
    (n : ℕ) (w : List Block) :
    deleteTilingBlocks t x
        (List.replicate n (tilingRemovableBlock t x) ++ w) =
      deleteTilingBlocks t x w := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [List.replicate_succ, List.cons_append, deleteTilingBlocks,
        if_pos rfl, blockEnd_tilingRemovableBlock]
      exact ih

/-- Deleting the reconstructed word recovers its retained word exactly. -/
theorem deleteTilingBlocks_tilingInsertGapVector {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (q : Fin (i + 1) → ℕ) :
    deleteTilingBlocks t x (tilingInsertGapVector t x r q) =
      List.ofFn r.1 := by
  induction i generalizing x with
  | zero =>
      rw [tilingInsertGapVector_zero]
      simpa [deleteTilingBlocks] using
        deleteTilingBlocks_replicate_append t x (q 0) []
  | succ i ih =>
      have h0 : r.1 0 ≠ tilingRemovableBlock t x := by
        simpa [rawExternalBase_zero] using r.2 0
      rw [tilingInsertGapVector_succ, List.append_assoc,
        deleteTilingBlocks_replicate_append]
      simp only [List.singleton_append, deleteTilingBlocks,
        if_neg h0]
      rw [ih]
      simp [List.ofFn_succ, tilingRetainedTail]

/-- Stateful point-path compression is exactly block-word deletion. -/
theorem tilingCompressTail_blockPathTail (t : DominoTiling) (x : Point) :
    ∀ bs : List Block,
      tilingCompressTail t x (blockPathTail x bs) =
        (blockPath x (deleteTilingBlocks t x bs)).tail := by
  intro bs
  induction bs generalizing x with
  | nil =>
      simp [blockPathTail, blockPath, deleteTilingBlocks, tilingCompressTail]
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

theorem tilingExternalPath_blockPath (t : DominoTiling) (x : Point)
    (bs : List Block) :
    tilingExternalPath t (blockPath x bs) =
      blockPath x (deleteTilingBlocks t x bs) := by
  simp only [blockPath, tilingExternalPath]
  rw [tilingCompressTail_blockPathTail]
  rfl

/-- The reconstructed path compresses to the exact fixed retained trace. -/
theorem tilingExternalPath_insertedPath {i : ℕ} (t : DominoTiling)
    (x : Point) (r : TilingRetainedWord t x i)
    (q : Fin (i + 1) → ℕ) :
    tilingExternalPath t (blockPath x (tilingInsertGapVector t x r q)) =
      blockPath x (List.ofFn r.1) := by
  rw [tilingExternalPath_blockPath,
    deleteTilingBlocks_tilingInsertGapVector]

/-- Removed point trace computed directly from a stateful block word. -/
def tilingLazyBlockTrace (t : DominoTiling) (x : Point) :
    List Block → List Point
  | [] => []
  | b :: bs =>
      (if b = tilingRemovableBlock t x then
        [blockMiddle x b, blockEnd x b] else []) ++
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

theorem tilingLazyPoints_blockPath (t : DominoTiling) (x : Point)
    (bs : List Block) :
    tilingLazyPoints t (blockPath x bs) = tilingLazyBlockTrace t x bs := by
  simp only [blockPath, tilingLazyPoints]
  exact tilingRemovedTail_blockPathTail_eq_lazyBlockTrace t x bs

@[simp] theorem followBlocks_replicate_tilingRemovable (t : DominoTiling)
    (x : Point) (n : ℕ) :
    followBlocks x (List.replicate n (tilingRemovableBlock t x)) = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [List.replicate_succ, followBlocks, List.foldl_cons,
        blockEnd_tilingRemovableBlock]
      exact ih

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

theorem tilingLazyBlockTrace_replicate (t : DominoTiling) (x : Point)
    (n : ℕ) :
    tilingLazyBlockTrace t x
        (List.replicate n (tilingRemovableBlock t x)) =
      (List.replicate n [tilingPartner t x, x]).flatten := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [List.replicate_succ, tilingLazyBlockTrace, if_pos rfl,
        blockMiddle_tilingRemovableBlock, blockEnd_tilingRemovableBlock,
        List.flatten_cons]
      rw [ih]
      rfl

/-- Every raw block word has a statefully valid retained word and a unique
vector of removable-run lengths reconstructing it. -/
theorem exists_tilingInsertGapVector (t : DominoTiling) (x : Point)
    (w : List Block) :
    ∃ (i : ℕ) (r : TilingRetainedWord t x i)
      (q : Fin (i + 1) → ℕ), tilingInsertGapVector t x r q = w := by
  induction w generalizing x with
  | nil =>
      refine ⟨0, ⟨fun k ↦ Fin.elim0 k, fun k ↦ Fin.elim0 k⟩,
        fun _ ↦ 0, ?_⟩
      simp
  | cons b w ih =>
      by_cases hb : b = tilingRemovableBlock t x
      · obtain ⟨i, r, q, hq⟩ := ih x
        refine ⟨i, r, tilingBumpFirstGap q, ?_⟩
        rw [tilingInsertGapVector_bumpFirst, hq, hb]
      · obtain ⟨i, r, q, hq⟩ := ih (blockEnd x b)
        let rb := tilingRetainedCons t x b hb r
        refine ⟨i + 1, rb, Fin.cases 0 q, ?_⟩
        rw [tilingInsertGapVector_succ]
        have htail : tilingRetainedTail t x rb = r := by
          apply Subtype.ext
          funext k
          rfl
        change List.replicate 0 (tilingRemovableBlock t x) ++ [b] ++
          tilingInsertGapVector t (blockEnd x b)
            (tilingRetainedTail t x rb) q = b :: w
        rw [htail]
        simp [hq]

/-! ## Exact regrouping by a domino of an arbitrary HLOZ tiling -/

/-- The finite set of tiling bases carrying insertion coordinates in a fixed
stateful external word. -/
def tilingExternalDominoBases {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) : Finset Point :=
  Finset.univ.image (fun k ↦ tilingBase t (rawExternalBase x r.1 k))

/-- A domino base occurring in the fixed stateful external trace. -/
abbrev TilingExternalDomino {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) :=
  {b : Point // b ∈ tilingExternalDominoBases t x r}

/-- Coordinates whose spatial locations lie in one fixed tiling domino. -/
abbrev TilingCoordinatesAt {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (b : TilingExternalDomino t x r) :=
  {k : Fin (i + 1) // tilingBase t (rawExternalBase x r.1 k) = b.1}

/-- The domino base that carries one insertion coordinate. -/
def tilingCoordinateDomino {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (k : Fin (i + 1)) :
    TilingExternalDomino t x r :=
  ⟨tilingBase t (rawExternalBase x r.1 k),
    Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩⟩

/-- Each insertion coordinate belongs to exactly one tiling-domino fibre. -/
def tilingCoordinateSigmaEquiv {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) :
    Fin (i + 1) ≃
      Σ b : TilingExternalDomino t x r, TilingCoordinatesAt t x r b where
  toFun k := ⟨tilingCoordinateDomino t x r k, ⟨k, rfl⟩⟩
  invFun z := z.2.1
  left_inv _ := rfl
  right_inv z := by
    rcases z with ⟨⟨b, hb⟩, ⟨k, hk⟩⟩
    dsimp only
    change tilingBase t (rawExternalBase x r.1 k) = b at hk
    subst b
    rfl

/-- Currying a coordinate vector over the state-dependent tiling fibres. -/
def regroupTilingCoordinatesEquiv {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (α : Type*) :
    (Fin (i + 1) → α) ≃
      ((b : TilingExternalDomino t x r) → TilingCoordinatesAt t x r b → α) :=
  ((tilingCoordinateSigmaEquiv t x r).arrowCongr (Equiv.refl α)).trans
    (Equiv.piCurry fun _ ↦ fun _ ↦ α)

/-- Total inserted multiplicity in one tiling domino. -/
def tilingDominoTotal {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ)
    (b : TilingExternalDomino t x r) : ℕ :=
  ∑ k : TilingCoordinatesAt t x r b, q k.1

theorem sum_tilingDominoTotal {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ) :
    ∑ b : TilingExternalDomino t x r, tilingDominoTotal t x r q b =
      ∑ k, q k := by
  classical
  unfold tilingDominoTotal
  rw [← Fintype.sum_sigma
    (fun z : Σ b : TilingExternalDomino t x r,
      TilingCoordinatesAt t x r b ↦ q z.2.1)]
  exact (Fintype.sum_equiv (tilingCoordinateSigmaEquiv t x r)
    (fun k ↦ q k) (fun z ↦ q z.2.1) (fun _ ↦ rfl)).symm

/-! ## Exact local time of a reconstructed stateful fibre -/

/-- Lazy local time reconstructed from the insertion coordinates.  Each
mate-and-return excursion visits both endpoints of its tiling domino once. -/
def tilingInsertionLazyLocalTime {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ)
    (y : Point) : ℕ :=
  ∑ k, q k *
    ((if rawExternalBase x r.1 k = y then 1 else 0) +
      if tilingPartner t (rawExternalBase x r.1 k) = y then 1 else 0)

/-- The coordinate formula computes the local time of the actually removed
points in the reconstructed position path. -/
theorem tilingLazyLocalTime_insertedPath {t : DominoTiling} :
    ∀ {i : ℕ} (x : Point) (r : TilingRetainedWord t x i)
      (q : Fin (i + 1) → ℕ) (y : Point),
      listLocalTime
          (tilingLazyPoints t
            (blockPath x (tilingInsertGapVector t x r q))) y =
        tilingInsertionLazyLocalTime t x r q y := by
  intro i
  induction i with
  | zero =>
      intro x r q y
      rw [tilingLazyPoints_blockPath, tilingInsertGapVector_zero,
        tilingLazyBlockTrace_replicate]
      have hpair : List.count y [tilingPartner t x, x] =
          (if x = y then 1 else 0) +
            (if tilingPartner t x = y then 1 else 0) := by
        simp only [List.count_cons, List.count_nil, beq_iff_eq]
        omega
      simp [listLocalTime, tilingInsertionLazyLocalTime, rawExternalBase,
        followBlocks, List.count_flatten, List.sum_replicate, hpair,
        add_comm]
  | succ i ih =>
      intro x r q y
      rw [tilingLazyPoints_blockPath, tilingInsertGapVector_succ]
      rw [List.append_assoc]
      rw [tilingLazyBlockTrace_append,
        tilingLazyBlockTrace_replicate,
        followBlocks_replicate_tilingRemovable]
      have hretained : r.1 0 ≠ tilingRemovableBlock t x := by
        simpa [rawExternalBase_zero] using r.2 0
      rw [List.singleton_append]
      simp only [tilingLazyBlockTrace, if_neg hretained, List.nil_append]
      rw [← tilingLazyPoints_blockPath t (blockEnd x (r.1 0))
        (tilingInsertGapVector t (blockEnd x (r.1 0))
          (tilingRetainedTail t x r) (fun k ↦ q k.succ))]
      change listLocalTime
          ((List.replicate (q 0) [tilingPartner t x, x]).flatten ++
            tilingLazyPoints t
              (blockPath (blockEnd x (r.1 0))
                (tilingInsertGapVector t (blockEnd x (r.1 0))
                  (tilingRetainedTail t x r) (fun k ↦ q k.succ)))) y = _
      unfold listLocalTime
      rw [List.count_append]
      have hi := ih (blockEnd x (r.1 0))
        (tilingRetainedTail t x r) (fun k ↦ q k.succ) y
      unfold listLocalTime at hi
      rw [hi]
      unfold tilingInsertionLazyLocalTime
      conv_rhs => rw [Fin.sum_univ_succ]
      simp only [rawExternalBase_zero, rawExternalBase_succ]
      have hpair : List.count y [tilingPartner t x, x] =
          (if x = y then 1 else 0) +
            (if tilingPartner t x = y then 1 else 0) := by
        simp only [List.count_cons, List.count_nil, beq_iff_eq]
        omega
      simp [List.count_flatten, List.sum_replicate, hpair,
        tilingRetainedTail, add_comm]
      apply Finset.sum_congr rfl
      intro k _
      rfl

theorem tilingEndpointIndicators (t : DominoTiling) (z y : Point) :
    (if z = y then 1 else 0) +
        (if tilingPartner t z = y then 1 else 0) =
      if tilingBase t z = tilingBase t y then 1 else 0 := by
  by_cases hbase : tilingBase t z = tilingBase t y
  · have hor := (tilingBase_eq_iff t z y).mp hbase
    rcases hor with hzy | hdom
    · subst y
      simp [tilingPartner_ne t z]
    · have hp : tilingPartner t z = y :=
        (sameDomino_iff_partner_eq t z y).mp hdom
      have hzy : z ≠ y := by
        intro h
        exact tilingPartner_ne t z (hp.trans h.symm)
      simp [hzy, hp, hbase]
  · have hzy : z ≠ y := fun h ↦ hbase (congrArg (tilingBase t) h)
    have hpy : tilingPartner t z ≠ y := by
      intro h
      apply hbase
      rw [← h, tilingBase_partner]
    simp [hzy, hpy, hbase]

theorem tilingSumByDomino {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (f : Fin (i + 1) → ℕ) :
    ∑ k, f k =
      ∑ b : TilingExternalDomino t x r,
        ∑ k : TilingCoordinatesAt t x r b, f k.1 := by
  classical
  rw [← Fintype.sum_sigma
    (fun z : Σ b : TilingExternalDomino t x r,
      TilingCoordinatesAt t x r b ↦ f z.2.1)]
  exact Fintype.sum_equiv (tilingCoordinateSigmaEquiv t x r)
    (fun k ↦ f k) (fun z ↦ f z.2.1) (fun _ ↦ rfl)

/-- Every point of a represented domino receives precisely that domino's
total inserted local time. -/
theorem tilingInsertionLazyLocalTime_at_dominoPoint {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (q : Fin (i + 1) → ℕ) (b : TilingExternalDomino t x r)
    (y : Point) (hy : tilingBase t y = b.1) :
    tilingInsertionLazyLocalTime t x r q y =
      tilingDominoTotal t x r q b := by
  classical
  unfold tilingInsertionLazyLocalTime
  simp_rw [tilingEndpointIndicators]
  rw [tilingSumByDomino t x r]
  rw [Finset.sum_eq_single b]
  · unfold tilingDominoTotal
    apply Finset.sum_congr rfl
    intro k _
    have hk : tilingBase t (rawExternalBase x r.1 k.1) = b.1 := k.2
    simp [hk, hy]
  · intro c _ hcb
    apply Finset.sum_eq_zero
    intro k _
    have hk : tilingBase t (rawExternalBase x r.1 k.1) = c.1 := k.2
    have hne : c.1 ≠ b.1 := fun h ↦ hcb (Subtype.ext h)
    simp [hk, hy, hne]
  · simp

/-- Fixed external local time of the retained stateful block word. -/
def tilingFixedExternalLocalTime {i : ℕ} (x : Point)
    (r : Fin i → Block) (y : Point) : ℕ :=
  listLocalTime (blockPath x (List.ofFn r)) y

/-- Exact external-plus-lazy local time at either endpoint of a represented
tiling domino. -/
theorem tilingInsertedPath_localTime_at_dominoPoint {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (q : Fin (i + 1) → ℕ) (b : TilingExternalDomino t x r)
    (y : Point) (hy : tilingBase t y = b.1) :
    listLocalTime (blockPath x (tilingInsertGapVector t x r q)) y =
      tilingFixedExternalLocalTime x r.1 y +
        tilingDominoTotal t x r q b := by
  rw [tilingListLocalTime_split, tilingExternalPath_insertedPath]
  unfold tilingFixedExternalLocalTime
  rw [tilingLazyLocalTime_insertedPath,
    tilingInsertionLazyLocalTime_at_dominoPoint t x r q b y hy]

theorem tilingBase_idem (t : DominoTiling) (y : Point) :
    tilingBase t (tilingBase t y) = tilingBase t y := by
  rcases point_eq_tilingBase_or_partner_base t y with hy | hy
  · exact (congrArg (tilingBase t) hy).symm
  · have h := congrArg (tilingBase t) hy
    rw [tilingBase_partner] at h
    exact h.symm

theorem tilingExternalDomino_is_base {i : ℕ} (t : DominoTiling)
    (x : Point) (r : TilingRetainedWord t x i)
    (b : TilingExternalDomino t x r) : tilingBase t b.1 = b.1 := by
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp b.2
  rw [← hk, tilingBase_idem]

theorem tilingPartner_ofExternalDomino_has_base {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (b : TilingExternalDomino t x r) :
    tilingBase t (tilingPartner t b.1) = b.1 := by
  rw [tilingBase_partner, tilingExternalDomino_is_base]

/-- The larger fixed-external local time at the two endpoints of one tiling
domino. -/
def tilingFixedExternalDominoMax {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (b : TilingExternalDomino t x r) : ℕ :=
  max (tilingFixedExternalLocalTime x r.1 b.1)
    (tilingFixedExternalLocalTime x r.1 (tilingPartner t b.1))

/-- Endpoint inequalities on all represented, non-distinguished dominoes. -/
def TilingEndpointsBelowLevelAway {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (m : ℕ) (D : Finset Point)
    (q : Fin (i + 1) → ℕ) : Prop :=
  ∀ b : TilingExternalDomino t x r, b.1 ∉ D →
    tilingFixedExternalLocalTime x r.1 b.1 +
          tilingDominoTotal t x r q b < m ∧
      tilingFixedExternalLocalTime x r.1 (tilingPartner t b.1) +
          tilingDominoTotal t x r q b < m

/-- One independent coordinatewise cutoff on every represented domino away
from the distinguished bases. -/
def TilingDominoTruncation {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (m : ℕ) (D : Finset Point)
    (q : Fin (i + 1) → ℕ) : Prop :=
  ∀ b : TilingExternalDomino t x r, b.1 ∉ D →
    tilingDominoTotal t x r q b <
      m - tilingFixedExternalDominoMax t x r b

theorem tilingEndpointsBelowLevelAway_iff_dominoTruncation {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (m : ℕ) (D : Finset Point) (q : Fin (i + 1) → ℕ) :
    TilingEndpointsBelowLevelAway t x r m D q ↔
      TilingDominoTruncation t x r m D q := by
  constructor
  · intro h b hb
    have hend := h b hb
    apply Nat.lt_sub_iff_add_lt.mpr
    unfold tilingFixedExternalDominoMax
    rw [add_comm, max_add]
    exact max_lt hend.1 hend.2
  · intro h b hb
    have hsum := Nat.lt_sub_iff_add_lt.mp (h b hb)
    unfold tilingFixedExternalDominoMax at hsum
    rw [add_comm, max_add, max_lt_iff] at hsum
    exact hsum

/-- The actual inserted-path endpoint inequalities away from distinguished
domino bases. -/
def TilingActualEndpointsBelowLevelAway {i : ℕ} (t : DominoTiling)
    (x : Point) (r : TilingRetainedWord t x i) (m : ℕ)
    (D : Finset Point) (q : Fin (i + 1) → ℕ) : Prop :=
  ∀ b : TilingExternalDomino t x r, b.1 ∉ D →
    listLocalTime (blockPath x (tilingInsertGapVector t x r q)) b.1 < m ∧
      listLocalTime (blockPath x (tilingInsertGapVector t x r q))
        (tilingPartner t b.1) < m

theorem tilingActualEndpointsBelowLevelAway_iff_dominoTruncation {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (m : ℕ) (D : Finset Point) (q : Fin (i + 1) → ℕ) :
    TilingActualEndpointsBelowLevelAway t x r m D q ↔
      TilingDominoTruncation t x r m D q := by
  rw [← tilingEndpointsBelowLevelAway_iff_dominoTruncation t x r m D q]
  constructor
  · intro h b hb
    simpa [tilingInsertedPath_localTime_at_dominoPoint t x r q b b.1
        (tilingExternalDomino_is_base t x r b),
      tilingInsertedPath_localTime_at_dominoPoint t x r q b
        (tilingPartner t b.1)
        (tilingPartner_ofExternalDomino_has_base t x r b)] using h b hb
  · intro h b hb
    simpa [tilingInsertedPath_localTime_at_dominoPoint t x r q b b.1
        (tilingExternalDomino_is_base t x r b),
      tilingInsertedPath_localTime_at_dominoPoint t x r q b
        (tilingPartner t b.1)
        (tilingPartner_ofExternalDomino_has_base t x r b)] using h b hb

/-- The complete direction prefix generated by stateful insertion. -/
def tilingInsertionPrefixList {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ)
    (tail : List Direction) : List Direction :=
  (tilingInsertGapVector t x r q).flatMap (fun b ↦ [b.1, b.2]) ++ tail

@[simp] theorem tilingInsertionPrefixList_length {i : ℕ} (t : DominoTiling)
    (x : Point) (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ)
    (tail : List Direction) :
    (tilingInsertionPrefixList t x r q tail).length =
      2 * (i + ∑ k, q k) + tail.length := by
  simp [tilingInsertionPrefixList, tilingInsertGapVector_length]
  omega

/-! ## Exact stopped atoms and their product-geometric mass -/

def tilingStoppedInsertionAtom (τ : StepPath → ℕ) {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (q : Fin (i + 1) → ℕ) (tail : List Direction) : Set StepPath :=
  let v := tilingInsertionPrefixList t x r q tail
  {ω | τ ω = v.length ∧ incrementPrefixList v.length ω = v}

def TilingStoppingAccepted (τ : StepPath → ℕ) {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (q : Fin (i + 1) → ℕ) (tail : List Direction) : Prop :=
  let v := tilingInsertionPrefixList t x r q tail
  τ (extendPrefix (directionVectorOfList v)) = v.length

theorem tilingStoppedInsertionAtom_eq_cylinder {τ : StepPath → ℕ}
    (hτ : IsFiniteStoppingTime τ) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ)
    (tail : List Direction) (hacc : TilingStoppingAccepted τ t x r q tail) :
    tilingStoppedInsertionAtom τ t x r q tail =
      {ω | stepPrefix (tilingInsertionPrefixList t x r q tail).length ω =
        directionVectorOfList (tilingInsertionPrefixList t x r q tail)} := by
  ext ω
  unfold tilingStoppedInsertionAtom
  simp only [Set.mem_setOf_eq]
  rw [incrementPrefixList_eq_iff_stepPrefix_eq_directionVector]
  constructor
  · exact fun h ↦ h.2
  · intro hp
    refine ⟨?_, hp⟩
    apply stoppingTime_eq_of_stepPrefix_eq hτ hacc
    rw [stepPrefix_extendPrefix]
    exact hp

theorem fairSteps_tilingStoppedInsertionAtom {τ : StepPath → ℕ}
    (hτ : IsFiniteStoppingTime τ) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ)
    (tail : List Direction) (hacc : TilingStoppingAccepted τ t x r q tail) :
    fairSteps (tilingStoppedInsertionAtom τ t x r q tail) =
      (1 / 4 : ℝ≥0∞) ^ (tilingInsertionPrefixList t x r q tail).length := by
  rw [tilingStoppedInsertionAtom_eq_cylinder hτ t x r q tail hacc]
  exact fairSteps_stepPrefix_singleton_mass _ _

noncomputable def tilingInsertionPrefixMass {i : ℕ} (t : DominoTiling)
    (x : Point) (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ)
    (tail : List Direction) : ℝ :=
  (1 / 4 : ℝ) ^ (tilingInsertionPrefixList t x r q tail).length

/-- The same fibre-wide constant as in the fixed-letter implementation.  Its
value depends only on the number of retained blocks and the boundary tail. -/
theorem tilingInsertionPrefixMass_eq_const_mul_gapVectorMass {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (q : Fin (i + 1) → ℕ) (tail : List Direction) :
    tilingInsertionPrefixMass t x r q tail =
      prefixFiberConstant i tail * gapVectorMass q := by
  unfold tilingInsertionPrefixMass prefixFiberConstant
  rw [tilingInsertionPrefixList_length, pow_add, pow_mul]
  have hfour : (1 / 4 : ℝ) ^ 2 = 1 / 16 := by norm_num
  rw [hfour]
  unfold gapVectorMass geometricGapMass
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [Finset.prod_pow_eq_pow_sum, pow_add]
  have hbase :
      (1 / 16 : ℝ) ^ i =
        16 * (1 / 15 : ℝ) ^ (i + 1) * (15 / 16 : ℝ) ^ (i + 1) := by
    symm
    calc
      16 * (1 / 15 : ℝ) ^ (i + 1) * (15 / 16 : ℝ) ^ (i + 1) =
          16 * ((1 / 15 : ℝ) ^ (i + 1) * (15 / 16 : ℝ) ^ (i + 1)) := by ring
      _ = 16 * (((1 / 15 : ℝ) * (15 / 16 : ℝ)) ^ (i + 1)) := by rw [mul_pow]
      _ = (1 / 16 : ℝ) ^ i := by
        norm_num
        rw [pow_succ]
        ring
  rw [hbase]
  ring

theorem fairSteps_tilingStoppedInsertionAtom_eq_ofReal
    {τ : StepPath → ℕ} (hτ : IsFiniteStoppingTime τ) {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (q : Fin (i + 1) → ℕ) (tail : List Direction)
    (hacc : TilingStoppingAccepted τ t x r q tail) :
    fairSteps (tilingStoppedInsertionAtom τ t x r q tail) =
      ENNReal.ofReal (tilingInsertionPrefixMass t x r q tail) := by
  rw [fairSteps_tilingStoppedInsertionAtom hτ t x r q tail hacc]
  unfold tilingInsertionPrefixMass
  rw [ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 1 / 4)]
  congr 1
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
  norm_num

theorem tilingInsertionPrefixList_injective {i : ℕ} (t : DominoTiling)
    (x : Point) (r : TilingRetainedWord t x i) (tail : List Direction) :
    Function.Injective
      (fun q : Fin (i + 1) → ℕ ↦ tilingInsertionPrefixList t x r q tail) := by
  intro q q' h
  unfold tilingInsertionPrefixList at h
  have hflat := List.append_cancel_right h
  have hword := congrArg pairDirectionList hflat
  rw [pairDirectionList_flatMap_blocks,
    pairDirectionList_flatMap_blocks] at hword
  exact tilingInsertGapVector_injective t x r hword

/-- Stopped stateful atoms with different insertion coordinates are
prefix-free. -/
theorem tilingStoppedInsertionAtom_pairwise_disjoint
    (τ : StepPath → ℕ) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (tail : List Direction) :
    Pairwise fun q q' : Fin (i + 1) → ℕ ↦
      Disjoint (tilingStoppedInsertionAtom τ t x r q tail)
        (tilingStoppedInsertionAtom τ t x r q' tail) := by
  intro q q' hqq'
  rw [Set.disjoint_left]
  intro omega hq hq'
  apply hqq'
  apply tilingInsertionPrefixList_injective t x r tail
  have hlen :
      (tilingInsertionPrefixList t x r q tail).length =
        (tilingInsertionPrefixList t x r q' tail).length :=
    hq.1.symm.trans hq'.1
  unfold tilingStoppedInsertionAtom at hq hq'
  simp only [Set.mem_ofPred_eq] at hq hq'
  rw [hlen] at hq
  exact hq.2.symm.trans hq'.2

/-! ## Finite capped stopped fibres -/

/-- Coordinatewise finite insertion cap for an all-six tiling fibre. -/
abbrev TilingCappedCoordinates (i cap : ℕ) :=
  Fin (i + 1) → Fin (cap + 1)

/-- Capped coordinates satisfying fixed spatial data and accepted by the
supplied finite stopping time. -/
abbrev TilingAcceptedCappedCoordinates (τ : StepPath → ℕ) {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (cap : ℕ) (tail : List Direction)
    (P : TilingCappedCoordinates i cap → Prop) :=
  {q : TilingCappedCoordinates i cap //
    P q ∧ TilingStoppingAccepted τ t x r (fun k ↦ (q k : ℕ)) tail}

noncomputable instance tilingAcceptedCappedCoordinatesFintype
    (τ : StepPath → ℕ) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (cap : ℕ) (tail : List Direction)
    (P : TilingCappedCoordinates i cap → Prop) :
    Fintype (TilingAcceptedCappedCoordinates τ t x r cap tail P) :=
  Fintype.ofFinite _

/-- Finite union of all accepted stopped atoms in one stateful capped fibre. -/
def tilingPreStoppingFiberEvent (τ : StepPath → ℕ) {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (cap : ℕ) (tail : List Direction)
    (P : TilingCappedCoordinates i cap → Prop) : Set StepPath :=
  ⋃ q : TilingAcceptedCappedCoordinates τ t x r cap tail P,
    tilingStoppedInsertionAtom τ t x r (fun k ↦ (q.1 k : ℕ)) tail

theorem tilingAcceptedCappedAtoms_pairwise_disjoint
    (τ : StepPath → ℕ) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (cap : ℕ) (tail : List Direction)
    (P : TilingCappedCoordinates i cap → Prop) :
    Pairwise fun q q' : TilingAcceptedCappedCoordinates τ t x r cap tail P ↦
      Disjoint
        (tilingStoppedInsertionAtom τ t x r (fun k ↦ (q.1 k : ℕ)) tail)
        (tilingStoppedInsertionAtom τ t x r (fun k ↦ (q'.1 k : ℕ)) tail) := by
  intro q q' hqq'
  apply tilingStoppedInsertionAtom_pairwise_disjoint τ t x r tail
  intro h
  apply hqq'
  apply Subtype.ext
  funext k
  apply Fin.ext
  exact congrFun h k

theorem measurableSet_tilingPreStoppingFiberEvent
    {τ : StepPath → ℕ} (hτ : IsFiniteStoppingTime τ) {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (cap : ℕ) (tail : List Direction)
    (P : TilingCappedCoordinates i cap → Prop) :
    MeasurableSet (tilingPreStoppingFiberEvent τ t x r cap tail P) := by
  classical
  exact MeasurableSet.iUnion fun q ↦ by
    rw [tilingStoppedInsertionAtom_eq_cylinder hτ t x r _ tail q.2.2]
    exact measurableSet_eq_fun (measurable_stepPrefix _) measurable_const

theorem tilingPreStoppingFiberEvent_mono
    (τ : StepPath → ℕ) {i cap : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (tail : List Direction)
    {P Q : TilingCappedCoordinates i cap → Prop}
    (hQP : ∀ q, Q q → P q) :
    tilingPreStoppingFiberEvent τ t x r cap tail Q ⊆
      tilingPreStoppingFiberEvent τ t x r cap tail P := by
  classical
  intro omega homega
  rcases Set.mem_iUnion.mp homega with ⟨q, hq⟩
  apply Set.mem_iUnion.mpr
  exact ⟨⟨q.1, hQP q.1 q.2.1, q.2.2⟩, hq⟩

theorem fairSteps_tilingPreStoppingFiberEvent
    {τ : StepPath → ℕ} (hτ : IsFiniteStoppingTime τ) {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (cap : ℕ) (tail : List Direction)
    (P : TilingCappedCoordinates i cap → Prop) :
    fairSteps (tilingPreStoppingFiberEvent τ t x r cap tail P) =
      ENNReal.ofReal
        (∑ q : TilingAcceptedCappedCoordinates τ t x r cap tail P,
          tilingInsertionPrefixMass t x r (fun k ↦ (q.1 k : ℕ)) tail) := by
  classical
  have hmeas :
      ∀ q : TilingAcceptedCappedCoordinates τ t x r cap tail P,
        MeasurableSet
          (tilingStoppedInsertionAtom τ t x r (fun k ↦ (q.1 k : ℕ)) tail) := by
    intro q
    rw [tilingStoppedInsertionAtom_eq_cylinder hτ t x r _ tail q.2.2]
    exact measurableSet_eq_fun (measurable_stepPrefix _) measurable_const
  have hdis :
      Pairwise fun q q' : TilingAcceptedCappedCoordinates τ t x r cap tail P ↦
        Disjoint
          (tilingStoppedInsertionAtom τ t x r (fun k ↦ (q.1 k : ℕ)) tail)
          (tilingStoppedInsertionAtom τ t x r (fun k ↦ (q'.1 k : ℕ)) tail) :=
    tilingAcceptedCappedAtoms_pairwise_disjoint τ t x r cap tail P
  unfold tilingPreStoppingFiberEvent
  rw [measure_iUnion hdis hmeas]
  simp_rw [show
      ∀ q : TilingAcceptedCappedCoordinates τ t x r cap tail P,
        fairSteps
            (tilingStoppedInsertionAtom τ t x r (fun k ↦ (q.1 k : ℕ)) tail) =
          ENNReal.ofReal
            (tilingInsertionPrefixMass t x r (fun k ↦ (q.1 k : ℕ)) tail) from
    fun q ↦ fairSteps_tilingStoppedInsertionAtom_eq_ofReal
      hτ t x r _ tail q.2.2]
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg]
  intro q _
  unfold tilingInsertionPrefixMass
  positivity

/-- Exact transport from the stopped-prefix partition to the independent
geometric coordinate weights. -/
theorem fairSteps_tilingPreStoppingFiberEvent_eq_geometricSum
    {τ : StepPath → ℕ} (hτ : IsFiniteStoppingTime τ) {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (cap : ℕ) (tail : List Direction)
    (P : TilingCappedCoordinates i cap → Prop) :
    fairSteps (tilingPreStoppingFiberEvent τ t x r cap tail P) =
      ENNReal.ofReal
        (prefixFiberConstant i tail *
          ∑ q : TilingAcceptedCappedCoordinates τ t x r cap tail P,
            gapVectorMass (fun k ↦ (q.1 k : ℕ))) := by
  rw [fairSteps_tilingPreStoppingFiberEvent hτ t x r cap tail P]
  congr 1
  simp_rw [tilingInsertionPrefixMass_eq_const_mul_gapVectorMass]
  rw [Finset.mul_sum]

end Erdos1165.TilingSpatialInsertionFiber
