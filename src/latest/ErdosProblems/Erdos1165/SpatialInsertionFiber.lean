/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.Clock
import ErdosProblems.Erdos1165.LazyDecomposition
import ErdosProblems.Erdos1165.PathInsertion
import ErdosProblems.Erdos1165.StoppedInsertion

/-!
# Finite spatial insertion fibres

This file supplies the finite, pre-stopping path bijection needed before the
conditional law in HLOZ (6.7) can be passed to the unbounded level clock.
For a fixed finite external block word, a word in its deletion fibre is
specified by one removable-excursion multiplicity at every external
block-base, including the terminal base.  The coordinates are then regrouped
by the spatial domino to which their base belongs.

The final section records the exact finite truncation statement.  Outside a
set of distinguished dominoes, keeping both endpoint local times below `m` is
equivalent to imposing, separately at every remaining domino, the upper bound

`lazy total < m - max (external endpoint local times)`.

Everything here is deterministic and finite.  In particular, no conditional
law at the unbounded random time `T_m^k` is asserted.
-/

open scoped BigOperators

namespace Erdos1165.SpatialInsertionFiber

open LazyDecomposition PathInsertion StoppedInsertion

/-! ## A fixed external word and its full deletion fibre -/

/-- The retained block word underlying a fixed external trace. -/
def retainedWord {o : Orientation} {i : ℕ} (r : Fin i → RetainedBlock o) : List Block :=
  List.ofFn fun k ↦ (r k : Block)

/-- Insert a prescribed number of removable blocks at every external base.
There are `i + 1` bases for `i` retained blocks: the last coordinate is the
run after the final retained block. -/
def insertGapVector {o : Orientation} {i : ℕ}
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ) : List Block :=
  ((List.ofFn fun k : Fin i ↦
      List.replicate (q k.castSucc) (removableBlock o) ++ [(r k : Block)]).flatten) ++
    List.replicate (q (Fin.last i)) (removableBlock o)

@[simp] theorem insertGapVector_zero {o : Orientation}
    (r : Fin 0 → RetainedBlock o) (q : Fin 1 → ℕ) :
    insertGapVector r q = List.replicate (q 0) (removableBlock o) := by
  simp [insertGapVector]

theorem insertGapVector_length {o : Orientation} {i : ℕ}
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ) :
    (insertGapVector r q).length = i + ∑ k, q k := by
  classical
  simp [insertGapVector, List.length_flatten, List.sum_ofFn,
    Fin.sum_univ_castSucc, Finset.sum_add_distrib]
  ac_rfl

theorem deleteRemovableBlocks_insertGapVector {o : Orientation} {i : ℕ}
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ) :
    deleteRemovableBlocks o (insertGapVector r q) = retainedWord r := by
  classical
  unfold insertGapVector deleteRemovableBlocks retainedWord
  simp only [List.filter_append, List.filter_replicate, decide_not,
    decide_true, Bool.not_true, List.filter_flatten, List.map_ofFn]
  have hfun :
      ((List.filter fun b : Block ↦ !decide (b = removableBlock o)) ∘
          fun k : Fin i ↦
            List.replicate (q k.castSucc) (removableBlock o) ++ [(r k : Block)]) =
        (fun k : Fin i ↦ [(r k : Block)]) := by
    funext k
    simp [(r k).property]
  simp only [Bool.false_eq_true, if_false, List.append_nil]
  rw [hfun]
  rw [List.ofFn_eq_map, List.ofFn_eq_map]
  induction List.finRange i with
  | nil => rfl
  | cons k ks ih => simp [ih]

/-- The full lattice trace obtained from a fixed external word and its lazy
insertion coordinates. -/
def insertedPath {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ) : List Point :=
  blockPath x (insertGapVector r q)

/-- Endpoint after following a finite block word from a prescribed base. -/
def followBlocks (x : Point) (bs : List Block) : Point :=
  bs.foldl blockEnd x

theorem externalPath_insertedPath {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ) :
    externalPath o (insertedPath x r q) = blockPath x (retainedWord r) := by
  rw [insertedPath, externalPath_blockPath, deleteRemovableBlocks_insertGapVector]

/-! ## The erased trace of an inserted word -/

@[simp] theorem blockMiddle_removableBlock (o : Orientation) (x : Point) :
    blockMiddle x (removableBlock o) = excursionMiddle o x := by
  rcases x with ⟨x₁, x₂⟩
  cases o with
  | even => simp [blockMiddle, removableBlock, excursionMiddle, directionVector, e₁]
  | shifted =>
      simp [blockMiddle, removableBlock, excursionMiddle, directionVector, e₁]
      omega

/-- The erased point list, computed directly block by block. -/
def lazyBlockTrace (o : Orientation) (x : Point) : List Block → List Point
  | [] => []
  | b :: bs =>
      (if b = removableBlock o then [blockMiddle x b, blockEnd x b] else []) ++
        lazyBlockTrace o (blockEnd x b) bs

private theorem removedTail_blockPathTail_eq_lazyBlockTrace (o : Orientation) (x : Point) :
    ∀ bs : List Block,
      removedTail o x (blockPathTail x bs) = lazyBlockTrace o x bs := by
  intro bs
  induction bs generalizing x with
  | nil => rfl
  | cons b bs ih =>
      by_cases hb : b = removableBlock o
      · have hrem : Removable o x (blockMiddle x b) (blockEnd x b) :=
          (removable_block_iff o x b).2 hb
        simp only [blockPathTail, removedTail, if_pos hrem, lazyBlockTrace, if_pos hb]
        rw [ih]
        rfl
      · have hrem : ¬Removable o x (blockMiddle x b) (blockEnd x b) :=
          (removable_block_iff o x b).not.mpr hb
        simp only [blockPathTail, removedTail, if_neg hrem, lazyBlockTrace, if_neg hb,
          List.nil_append]
        exact ih (blockEnd x b)

theorem lazyPoints_blockPath (o : Orientation) (x : Point) (bs : List Block) :
    lazyPoints o (blockPath x bs) = lazyBlockTrace o x bs := by
  simp only [blockPath, lazyPoints]
  exact removedTail_blockPathTail_eq_lazyBlockTrace o x bs

@[simp] theorem followBlocks_append (x : Point) (as bs : List Block) :
    followBlocks x (as ++ bs) = followBlocks (followBlocks x as) bs := by
  simp [followBlocks, List.foldl_append]

theorem lazyBlockTrace_append (o : Orientation) (x : Point) (as bs : List Block) :
    lazyBlockTrace o x (as ++ bs) =
      lazyBlockTrace o x as ++ lazyBlockTrace o (followBlocks x as) bs := by
  induction as generalizing x with
  | nil => rfl
  | cons a as ih =>
      simp only [List.cons_append, lazyBlockTrace, List.append_assoc]
      rw [ih]
      rfl

@[simp] theorem followBlocks_replicate_removable (o : Orientation) (x : Point) (n : ℕ) :
    followBlocks x (List.replicate n (removableBlock o)) = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [List.replicate_succ, followBlocks, List.foldl_cons,
        blockEnd_removableBlock]
      exact ih

theorem lazyBlockTrace_replicate_removable (o : Orientation) (x : Point) (n : ℕ) :
    lazyBlockTrace o x (List.replicate n (removableBlock o)) =
      (List.replicate n [excursionMiddle o x, x]).flatten := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [List.replicate_succ, lazyBlockTrace,
        blockMiddle_removableBlock, blockEnd_removableBlock, List.flatten_cons]
      rw [ih]
      simp

theorem insertGapVector_succ {o : Orientation} {i : ℕ}
    (r : Fin (i + 1) → RetainedBlock o) (q : Fin (i + 2) → ℕ) :
    insertGapVector r q =
      List.replicate (q 0) (removableBlock o) ++ [(r 0 : Block)] ++
        insertGapVector (fun k ↦ r k.succ) (fun k ↦ q k.succ) := by
  simp [insertGapVector, List.ofFn_succ, List.append_assoc]

/-- Increase the initial removable run of an insertion vector by one. -/
def bumpFirstGap {i : ℕ} (q : Fin (i + 1) → ℕ) : Fin (i + 1) → ℕ :=
  Fin.cases (q 0 + 1) (fun k ↦ q k.succ)

theorem insertGapVector_bumpFirst {o : Orientation} {i : ℕ}
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ) :
    insertGapVector r (bumpFirstGap q) = removableBlock o :: insertGapVector r q := by
  cases i with
  | zero =>
      rw [insertGapVector_zero, insertGapVector_zero]
      simp [bumpFirstGap, List.replicate_succ]
  | succ i =>
      rw [insertGapVector_succ, insertGapVector_succ]
      simp [bumpFirstGap, List.replicate_succ]

/-- Every finite two-step block word has a unique external word together with
some full insertion vector.  This existence theorem is the decoding half
needed when a random prefix is placed in a fixed external fibre. -/
theorem exists_insertGapVector (o : Orientation) (w : List Block) :
    ∃ (i : ℕ) (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ),
      insertGapVector r q = w := by
  induction w with
  | nil =>
      refine ⟨0, fun k ↦ Fin.elim0 k, fun _ ↦ 0, ?_⟩
      simp [insertGapVector]
  | cons b w ih =>
      obtain ⟨i, r, q, hq⟩ := ih
      by_cases hb : b = removableBlock o
      · refine ⟨i, r, bumpFirstGap q, ?_⟩
        rw [insertGapVector_bumpFirst, hq, hb]
      · let rb : RetainedBlock o := ⟨b, hb⟩
        refine ⟨i + 1, Fin.cases rb r, Fin.cases 0 q, ?_⟩
        rw [insertGapVector_succ]
        simp [rb, hq]

/-- Every finite block word lies in a deletion fibre with the deterministic
coordinate cap `w.length`. -/
theorem exists_capped_insertGapVector (o : Orientation) (w : List Block) :
    ∃ (i : ℕ) (r : Fin i → RetainedBlock o)
      (q : Fin (i + 1) → Fin (w.length + 1)),
      insertGapVector r (fun k ↦ (q k : ℕ)) = w := by
  obtain ⟨i, r, q, hq⟩ := exists_insertGapVector o w
  have hlen : i + ∑ k, q k = w.length := by
    rw [← hq]
    exact (insertGapVector_length r q).symm
  have hbound : ∀ k, q k < w.length + 1 := by
    intro k
    have hk : q k ≤ ∑ j, q j :=
      Finset.single_le_sum (s := Finset.univ) (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ k)
    omega
  let qc : Fin (i + 1) → Fin (w.length + 1) := fun k ↦ ⟨q k, hbound k⟩
  exact ⟨i, r, qc, hq⟩

/-! ## Exact pairing of a capped random prefix -/

/-- Pair consecutive directions, leaving at most one terminal direction. -/
def pairDirectionList : List Direction → List Block
  | a :: b :: rest => (a, b) :: pairDirectionList rest
  | _ => []

/-- The optional incomplete final direction after pairing. -/
def unpairedDirectionTail : List Direction → List Direction
  | [] => []
  | [a] => [a]
  | _ :: _ :: rest => unpairedDirectionTail rest

theorem pairDirectionList_flatten_append_tail : ∀ ds : List Direction,
    (pairDirectionList ds).flatMap (fun b ↦ [b.1, b.2]) ++
      unpairedDirectionTail ds = ds := by
  intro ds
  induction ds using List.twoStepInduction with
  | nil => rfl
  | singleton a => rfl
  | cons_cons a b rest ih _ =>
      simp [pairDirectionList, unpairedDirectionTail, ih]

theorem unpairedDirectionTail_length_le_one (ds : List Direction) :
    (unpairedDirectionTail ds).length ≤ 1 := by
  induction ds using List.twoStepInduction with
  | nil => simp [unpairedDirectionTail]
  | singleton a => simp [unpairedDirectionTail]
  | cons_cons a b rest ih _ => simpa [unpairedDirectionTail] using ih

/-- Increment list through a deterministic time. -/
def incrementPrefixList (n : ℕ) (omega : StepPath) : List Direction :=
  List.ofFn (stepPrefix n omega)

def prefixBlockWord (n : ℕ) (omega : StepPath) : List Block :=
  pairDirectionList (incrementPrefixList n omega)

def prefixDirectionTail (n : ℕ) (omega : StepPath) : List Direction :=
  unpairedDirectionTail (incrementPrefixList n omega)

theorem incrementPrefixList_decompose (n : ℕ) (omega : StepPath) :
    (prefixBlockWord n omega).flatMap (fun b ↦ [b.1, b.2]) ++
      prefixDirectionTail n omega = incrementPrefixList n omega := by
  exact pairDirectionList_flatten_append_tail _

/-- Block word before the capped HLOZ level time. -/
noncomputable def truncatedLevelPrefixWord (m k cutoff : ℕ) (omega : StepPath) : List Block :=
  prefixBlockWord (truncatedLevelTime m k cutoff omega) omega

noncomputable def truncatedLevelPrefixTail (m k cutoff : ℕ) (omega : StepPath) : List Direction :=
  prefixDirectionTail (truncatedLevelTime m k cutoff omega) omega

/-- Exact capped random-prefix identification.  The complete two-step part is
in a capped insertion fibre; the displayed final list is the sole possible
incomplete block and has length at most one. -/
theorem truncatedLevelPrefix_capped_fiber (o : Orientation) (m k cutoff : ℕ)
    (omega : StepPath) :
    ∃ (i : ℕ) (r : Fin i → RetainedBlock o)
      (q : Fin (i + 1) → Fin ((truncatedLevelPrefixWord m k cutoff omega).length + 1)),
      insertGapVector r (fun j ↦ (q j : ℕ)) = truncatedLevelPrefixWord m k cutoff omega ∧
        (insertGapVector r (fun j ↦ (q j : ℕ))).flatMap (fun b ↦ [b.1, b.2]) ++
            truncatedLevelPrefixTail m k cutoff omega =
          incrementPrefixList (truncatedLevelTime m k cutoff omega) omega ∧
        (truncatedLevelPrefixTail m k cutoff omega).length ≤ 1 := by
  obtain ⟨i, r, q, hq⟩ :=
    exists_capped_insertGapVector o (truncatedLevelPrefixWord m k cutoff omega)
  refine ⟨i, r, q, hq, ?_, ?_⟩
  · rw [hq]
    exact incrementPrefixList_decompose _ _
  · exact unpairedDirectionTail_length_le_one _

/-! ## Uniqueness and a finite capped equivalence -/

private theorem decodeRuns_insertGapVector {o : Orientation} {i : ℕ}
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ) :
    decodeRuns o (insertGapVector r q) =
      List.ofFn fun k : Fin i ↦ (q k.castSucc, (r k : Block)) := by
  classical
  have htail : ∀ (a n : ℕ),
      decodeRunsAux o a (List.replicate n (removableBlock o)) = [] := by
    intro a n
    induction n generalizing a with
    | zero => rfl
    | succ n ih =>
        simp only [List.replicate_succ, decodeRunsAux]
        exact ih (a + 1)
  unfold decodeRuns insertGapVector
  rw [List.ofFn_eq_map, List.ofFn_eq_map]
  induction List.finRange i with
  | nil => exact htail 0 _
  | cons k ks ih =>
      simp only [List.map_cons, List.flatten_cons]
      rw [List.append_assoc]
      rw [List.append_assoc]
      rw [List.singleton_append]
      rw [decodeRunsAux_replicate o 0 (q k.castSucc) (r k).property]
      rw [ih]
      simp

private theorem count_removable_insertGapVector {o : Orientation} {i : ℕ}
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ) :
    (insertGapVector r q).count (removableBlock o) = ∑ k, q k := by
  classical
  simp [insertGapVector, (r _).property, List.count_flatten, List.sum_ofFn,
    Fin.sum_univ_castSucc]

theorem insertGapVector_injective {o : Orientation} {i : ℕ}
    (r : Fin i → RetainedBlock o) : Function.Injective (insertGapVector r) := by
  intro q q' hqq'
  have hdecode := congrArg (decodeRuns o) hqq'
  rw [decodeRuns_insertGapVector, decodeRuns_insertGapVector] at hdecode
  have hpairs := List.ofFn_injective hdecode
  have hlead : ∀ k : Fin i, q k.castSucc = q' k.castSucc := fun k ↦
    congrArg Prod.fst (congrFun hpairs k)
  have hcount := congrArg (fun w : List Block ↦ w.count (removableBlock o)) hqq'
  rw [count_removable_insertGapVector, count_removable_insertGapVector,
    Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at hcount
  funext k
  refine Fin.lastCases ?_ (fun j ↦ hlead j) k
  have hsum : (∑ j : Fin i, q j.castSucc) = ∑ j : Fin i, q' j.castSucc := by
    apply Finset.sum_congr rfl
    intro j _
    exact hlead j
  omega

/-- Insertion coordinates capped coordinatewise by `cap`. -/
abbrev CappedCoordinates (i cap : ℕ) := Fin (i + 1) → Fin (cap + 1)

/-- The genuine set of block words in the capped deletion fibre of `r`. -/
def CappedSpatialWord {o : Orientation} {i : ℕ}
    (r : Fin i → RetainedBlock o) (cap : ℕ) :=
  {w : List Block // ∃ q : CappedCoordinates i cap,
    insertGapVector r (fun k ↦ (q k : ℕ)) = w}

/-- Finite capped insertion is a bijection onto the corresponding genuine
external-trace fibre. -/
noncomputable def cappedSpatialEquiv {o : Orientation} {i : ℕ}
    (r : Fin i → RetainedBlock o) (cap : ℕ) :
    CappedCoordinates i cap ≃ CappedSpatialWord r cap where
  toFun q := ⟨insertGapVector r (fun k ↦ (q k : ℕ)), ⟨q, rfl⟩⟩
  invFun w := Classical.choose w.property
  left_inv q := by
    have hnat := insertGapVector_injective r
      (Classical.choose_spec (show ∃ d : CappedCoordinates i cap,
      insertGapVector r (fun k ↦ (d k : ℕ)) =
        insertGapVector r (fun k ↦ (q k : ℕ)) from ⟨q, rfl⟩))
    funext k
    apply Fin.ext
    exact congrFun hnat k
  right_inv w := by
    apply Subtype.ext
    exact Classical.choose_spec w.property

noncomputable instance {o : Orientation} {i : ℕ}
    (r : Fin i → RetainedBlock o) (cap : ℕ) : Fintype (CappedSpatialWord r cap) :=
  Fintype.ofEquiv (CappedCoordinates i cap) (cappedSpatialEquiv r cap)

@[simp] theorem card_cappedSpatialWord {o : Orientation} {i : ℕ}
    (r : Fin i → RetainedBlock o) (cap : ℕ) :
    Fintype.card (CappedSpatialWord r cap) = (cap + 1) ^ (i + 1) := by
  rw [← Fintype.card_congr (cappedSpatialEquiv r cap)]
  simp [CappedCoordinates]

/-! ## Regrouping insertion coordinates by spatial domino -/

/-- Base of the `k`-th insertion coordinate in the fixed external trace. -/
def externalBase {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (k : Fin (i + 1)) : Point :=
  followBlocks x ((retainedWord r).take k)

@[simp] theorem externalBase_zero {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) : externalBase x r 0 = x := by
  simp [externalBase, followBlocks]

theorem externalBase_succ {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin (i + 1) → RetainedBlock o) (k : Fin (i + 1)) :
    externalBase x r k.succ =
      externalBase (blockEnd x (r 0 : Block)) (fun j ↦ r j.succ) k := by
  simp [externalBase, retainedWord, followBlocks, List.ofFn_succ, List.take_succ_cons]

/-- Lazy local time reconstructed from insertion coordinates.  Each inserted
excursion contributes once at its base and once at the other endpoint of the
domino. -/
def insertionLazyLocalTime {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ) (y : Point) : ℕ :=
  ∑ k, q k *
    ((if externalBase x r k = y then 1 else 0) +
      if excursionMiddle o (externalBase x r k) = y then 1 else 0)

/-- The algebraic insertion coordinates compute the actual erased local time
of the reconstructed position path. -/
theorem lazyLocalTime_insertedPath {o : Orientation} :
    ∀ {i : ℕ} (x : Point) (r : Fin i → RetainedBlock o)
      (q : Fin (i + 1) → ℕ) (y : Point),
      listLocalTime (lazyPoints o (insertedPath x r q)) y =
        insertionLazyLocalTime x r q y := by
  intro i
  induction i with
  | zero =>
      intro x r q y
      rw [insertedPath, lazyPoints_blockPath]
      rw [insertGapVector_zero, lazyBlockTrace_replicate_removable]
      have hpair : List.count y [excursionMiddle o x, x] =
          (if x = y then 1 else 0) +
            (if excursionMiddle o x = y then 1 else 0) := by
        simp only [List.count_cons, List.count_nil, beq_iff_eq]
        omega
      simp [listLocalTime, insertionLazyLocalTime, externalBase, followBlocks,
        List.count_flatten, List.sum_replicate, hpair]
  | succ i ih =>
      intro x r q y
      rw [insertedPath, lazyPoints_blockPath, insertGapVector_succ]
      rw [List.append_assoc]
      rw [lazyBlockTrace_append, lazyBlockTrace_replicate_removable,
        followBlocks_replicate_removable]
      have hretained : (r 0 : Block) ≠ removableBlock o := (r 0).property
      rw [List.singleton_append]
      simp only [lazyBlockTrace, if_neg hretained, List.nil_append]
      rw [← lazyPoints_blockPath o (blockEnd x (r 0 : Block))
        (insertGapVector (fun k ↦ r k.succ) (fun k ↦ q k.succ))]
      change listLocalTime
          ((List.replicate (q 0) [excursionMiddle o x, x]).flatten ++
            lazyPoints o
              (insertedPath (blockEnd x (r 0 : Block))
                (fun k ↦ r k.succ) (fun k ↦ q k.succ))) y = _
      unfold listLocalTime
      rw [List.count_append]
      have hi := ih (blockEnd x (r 0 : Block))
        (fun k ↦ r k.succ) (fun k ↦ q k.succ) y
      unfold listLocalTime at hi
      rw [hi]
      unfold insertionLazyLocalTime
      conv_rhs => rw [Fin.sum_univ_succ]
      simp only [externalBase_zero, externalBase_succ]
      have hpair : List.count y [excursionMiddle o x, x] =
          (if x = y then 1 else 0) +
            (if excursionMiddle o x = y then 1 else 0) := by
        simp only [List.count_cons, List.count_nil, beq_iff_eq]
        omega
      simp [List.count_flatten, List.sum_replicate, hpair]

/-- The finite set of domino bases visited by the external even skeleton. -/
def externalDominoBases {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) : Finset Point :=
  Finset.univ.image (externalBase x r)

/-- A spatial domino occurring in this external trace. -/
abbrev ExternalDomino {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) := {y : Point // y ∈ externalDominoBases x r}

/-- External insertion coordinates carried by one fixed spatial domino. -/
abbrev CoordinatesAt {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (b : ExternalDomino x r) :=
  {k : Fin (i + 1) // externalBase x r k = b.1}

private def coordinateDomino {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (k : Fin (i + 1)) : ExternalDomino x r :=
  ⟨externalBase x r k, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩⟩

/-- Every external coordinate belongs to exactly one of the spatial fibres. -/
def coordinateSigmaEquiv {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) :
    Fin (i + 1) ≃ Σ b : ExternalDomino x r, CoordinatesAt x r b where
  toFun k := ⟨coordinateDomino x r k, ⟨k, rfl⟩⟩
  invFun z := z.2.1
  left_inv _ := rfl
  right_inv z := by
    rcases z with ⟨⟨b, hbmem⟩, ⟨k, hk⟩⟩
    dsimp only
    change externalBase x r k = b at hk
    subst b
    rfl

/-- Currying a coordinate vector over the fibres of the spatial-base map.
This is the exact finite regrouping by domino. -/
def groupByDominoEquiv {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (α : Type*) :
    (Fin (i + 1) → α) ≃ ((b : ExternalDomino x r) → CoordinatesAt x r b → α) :=
  ((coordinateSigmaEquiv x r).arrowCongr (Equiv.refl α)).trans
    (Equiv.piCurry fun _ ↦ fun _ ↦ α)

/-- Total lazy multiplicity attached to a spatial domino. -/
def dominoLazyTotal {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ)
    (b : ExternalDomino x r) : ℕ :=
  ∑ k : CoordinatesAt x r b, q k.1

theorem sum_dominoLazyTotal {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ) :
    ∑ b : ExternalDomino x r, dominoLazyTotal x r q b = ∑ k, q k := by
  classical
  unfold dominoLazyTotal
  rw [← Fintype.sum_sigma
    (fun z : Σ b : ExternalDomino x r, CoordinatesAt x r b ↦ q z.2.1)]
  exact (Fintype.sum_equiv (coordinateSigmaEquiv x r) (fun k ↦ q k)
    (fun z ↦ q z.2.1) (fun _ ↦ rfl)).symm

/-- External local time read from the retained position trace. -/
def fixedExternalLocalTime {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (y : Point) : ℕ :=
  listLocalTime (blockPath x (retainedWord r)) y

theorem sum_by_domino {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (f : Fin (i + 1) → ℕ) :
    ∑ k, f k = ∑ b : ExternalDomino x r, ∑ k : CoordinatesAt x r b, f k.1 := by
  classical
  rw [← Fintype.sum_sigma
    (fun z : Σ b : ExternalDomino x r, CoordinatesAt x r b ↦ f z.2.1)]
  exact Fintype.sum_equiv (coordinateSigmaEquiv x r) (fun k ↦ f k)
    (fun z ↦ f z.2.1) (fun _ ↦ rfl)

/-- No base in the external trace is the opposite endpoint of another base's
domino.  Checkerboard parity gives this property for the two HLOZ deletion
orientations. -/
def BaseMiddleDisjoint {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) : Prop :=
  ∀ b c : ExternalDomino x r, excursionMiddle o b.1 ≠ c.1

/-- The initial parity appropriate to the chosen deletion orientation. -/
def OrientationCompatible : Orientation → Point → Prop
  | .even, x => EvenPoint x
  | .shifted, x => OddPoint x

theorem pointParity_blockEnd (x : Point) (b : Block) :
    pointParity (blockEnd x b) = pointParity x := by
  rw [blockEnd, pointParity_add, pointParity_add, pointParity_directionVector,
    pointParity_directionVector]
  rw [add_assoc, show (1 : ZMod 2) + 1 = 0 by decide]
  simp

theorem pointParity_followBlocks (x : Point) (bs : List Block) :
    pointParity (followBlocks x bs) = pointParity x := by
  induction bs generalizing x with
  | nil => rfl
  | cons b bs ih =>
    simp only [followBlocks, List.foldl_cons]
    change pointParity (followBlocks (blockEnd x b) bs) = pointParity x
    rw [ih, pointParity_blockEnd]

theorem pointParity_externalBase {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (k : Fin (i + 1)) :
    pointParity (externalBase x r k) = pointParity x := by
  exact pointParity_followBlocks x _

/-- Checkerboard parity proves that the external bases really index disjoint
dominoes in either deletion orientation. -/
theorem baseMiddleDisjoint_of_compatible {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (hx : OrientationCompatible o x) :
    BaseMiddleDisjoint x r := by
  intro b c hbc
  obtain ⟨kb, _, hbbase⟩ := Finset.mem_image.mp b.2
  obtain ⟨kc, _, hcbase⟩ := Finset.mem_image.mp c.2
  have hbpar := pointParity_externalBase x r kb
  have hcpar := pointParity_externalBase x r kc
  rw [hbbase] at hbpar
  rw [hcbase] at hcpar
  cases o with
  | even =>
      change EvenPoint x at hx
      have hbEven : EvenPoint b.1 := hbpar.trans hx
      have hmOdd : OddPoint (excursionMiddle .even b.1) := even_middle_is_odd hbEven
      have hcEven : EvenPoint c.1 := hcpar.trans hx
      rw [hbc] at hmOdd
      rw [OddPoint, hcEven] at hmOdd
      exact zero_ne_one hmOdd
  | shifted =>
      change OddPoint x at hx
      have hbOdd : OddPoint b.1 := hbpar.trans hx
      have hmEven : EvenPoint (excursionMiddle .shifted b.1) := shifted_middle_is_even hbOdd
      have hcOdd : OddPoint c.1 := hcpar.trans hx
      rw [hbc] at hmEven
      rw [EvenPoint, hcOdd] at hmEven
      exact one_ne_zero hmEven

theorem excursionMiddle_injective (o : Orientation) :
    Function.Injective (excursionMiddle o) := by
  intro x y h
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  cases o <;> simp [excursionMiddle, e₁] at h ⊢ <;> omega

theorem insertionLazyLocalTime_at_base {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ)
    (hdis : BaseMiddleDisjoint x r) (b : ExternalDomino x r) :
    insertionLazyLocalTime x r q b.1 = dominoLazyTotal x r q b := by
  classical
  unfold insertionLazyLocalTime
  rw [sum_by_domino x r]
  rw [Finset.sum_eq_single b]
  · unfold dominoLazyTotal
    apply Finset.sum_congr rfl
    intro k _
    have hk : externalBase x r k.1 = b.1 := k.2
    simp only [hk]
    have hmiddle : excursionMiddle o b.1 ≠ b.1 := hdis b b
    simp [hmiddle]
  · intro c _ hcb
    have hbase : c.1 ≠ b.1 := by
      intro h
      exact hcb (Subtype.ext h)
    have hmiddle : excursionMiddle o c.1 ≠ b.1 := hdis c b
    apply Finset.sum_eq_zero
    intro k _
    have hk : externalBase x r k.1 = c.1 := k.2
    simp [hk, hbase, hmiddle]
  · simp

theorem insertionLazyLocalTime_at_middle {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ)
    (hdis : BaseMiddleDisjoint x r) (b : ExternalDomino x r) :
    insertionLazyLocalTime x r q (excursionMiddle o b.1) =
      dominoLazyTotal x r q b := by
  classical
  unfold insertionLazyLocalTime
  rw [sum_by_domino x r]
  rw [Finset.sum_eq_single b]
  · unfold dominoLazyTotal
    apply Finset.sum_congr rfl
    intro k _
    have hk : externalBase x r k.1 = b.1 := k.2
    have hbase : b.1 ≠ excursionMiddle o b.1 := (hdis b b).symm
    simp [hk, hbase]
  · intro c _ hcb
    have hbase : c.1 ≠ excursionMiddle o b.1 := (hdis b c).symm
    have hmiddle : excursionMiddle o c.1 ≠ excursionMiddle o b.1 := by
      intro h
      exact hcb (Subtype.ext (excursionMiddle_injective o h))
    apply Finset.sum_eq_zero
    intro k _
    have hk : externalBase x r k.1 = c.1 := k.2
    simp [hk, hbase, hmiddle]
  · simp

theorem insertedPath_localTime_at_base {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ)
    (hdis : BaseMiddleDisjoint x r) (b : ExternalDomino x r) :
    listLocalTime (insertedPath x r q) b.1 =
      fixedExternalLocalTime x r b.1 + dominoLazyTotal x r q b := by
  rw [listLocalTime_split, externalPath_insertedPath]
  unfold fixedExternalLocalTime
  rw [lazyLocalTime_insertedPath, insertionLazyLocalTime_at_base x r q hdis b]

theorem insertedPath_localTime_at_middle {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ)
    (hdis : BaseMiddleDisjoint x r) (b : ExternalDomino x r) :
    listLocalTime (insertedPath x r q) (excursionMiddle o b.1) =
      fixedExternalLocalTime x r (excursionMiddle o b.1) +
        dominoLazyTotal x r q b := by
  rw [listLocalTime_split, externalPath_insertedPath]
  unfold fixedExternalLocalTime
  rw [lazyLocalTime_insertedPath, insertionLazyLocalTime_at_middle x r q hdis b]

/-! ## Pointwise probability weight and spatial factorization -/

/-- Product geometric weight of one full insertion vector. -/
noncomputable def gapVectorMass {i : ℕ} (q : Fin (i + 1) → ℕ) : ℝ :=
  ∏ k, geometricGapMass (q k)

/-- Product geometric weight of the coordinates carried by one domino. -/
noncomputable def dominoCoordinateMass {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ)
    (b : ExternalDomino x r) : ℝ :=
  ∏ k : CoordinatesAt x r b, geometricGapMass (q k.1)

/-- Once the external trace is fixed, the insertion weight factors exactly
over the spatial dominoes.  This is the finite point-mass disintegration
underlying (6.8). -/
theorem gapVectorMass_factorization {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ) :
    gapVectorMass q = ∏ b : ExternalDomino x r, dominoCoordinateMass x r q b := by
  classical
  unfold gapVectorMass dominoCoordinateMass
  rw [← Fintype.prod_sigma
    (fun z : Σ b : ExternalDomino x r, CoordinatesAt x r b ↦
      geometricGapMass (q z.2.1))]
  exact Fintype.prod_equiv (coordinateSigmaEquiv x r)
    (fun k ↦ geometricGapMass (q k))
    (fun z ↦ geometricGapMass (q z.2.1)) (fun _ ↦ rfl)

/-- Number of external insertion opportunities attached to one domino. -/
def dominoExternalMultiplicity {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (b : ExternalDomino x r) : ℕ :=
  Fintype.card (CoordinatesAt x r b)

theorem dominoExternalMultiplicity_pos {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (b : ExternalDomino x r) :
    0 < dominoExternalMultiplicity x r b := by
  unfold dominoExternalMultiplicity
  rw [Fintype.card_pos_iff]
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp b.2
  exact ⟨⟨k, hk⟩⟩

/-- The fixed-external-word insertion count gives the HLOZ mass `p(a,ℓ)`
for the lazy total on an individual spatial domino. -/
theorem dominoTotal_conditionalMass {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (b : ExternalDomino x r) (ℓ : ℕ) :
    fixedExternalJointMass (dominoExternalMultiplicity x r b) ℓ /
        fixedExternalMarginalMass (dominoExternalMultiplicity x r b) =
      NegativeBinomial.mass (15 / 16 : ℝ) (dominoExternalMultiplicity x r b) ℓ := by
  exact fixedExternal_conditionalMass (dominoExternalMultiplicity_pos x r b) ℓ

/-! ## The exact level truncation on a fixed external fibre -/

/-- The larger of the two external local times on a spatial domino. -/
def fixedExternalDominoMax {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (b : ExternalDomino x r) : ℕ :=
  max (fixedExternalLocalTime x r b.1)
    (fixedExternalLocalTime x r (excursionMiddle o b.1))

/-- The finite fibre version of the level condition away from distinguished
dominoes.  The pathwise split says that the same lazy total is added to both
endpoints of a domino. -/
def EndpointsBelowLevelAway {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m : ℕ) (D : Finset Point)
    (q : Fin (i + 1) → ℕ) : Prop :=
  ∀ b : ExternalDomino x r, b.1 ∉ D →
    fixedExternalLocalTime x r b.1 + dominoLazyTotal x r q b < m ∧
      fixedExternalLocalTime x r (excursionMiddle o b.1) +
        dominoLazyTotal x r q b < m

/-- Coordinatewise upper truncation after grouping by domino. -/
def DominoTruncation {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m : ℕ) (D : Finset Point)
    (q : Fin (i + 1) → ℕ) : Prop :=
  ∀ b : ExternalDomino x r, b.1 ∉ D →
    dominoLazyTotal x r q b < m - fixedExternalDominoMax x r b

/-- Local admissibility factor: distinguished dominoes are unrestricted and
every other domino obeys its own HLOZ cutoff. -/
def DominoAdmissible {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m : ℕ) (D : Finset Point)
    (q : Fin (i + 1) → ℕ) (b : ExternalDomino x r) : Prop :=
  b.1 ∈ D ∨ dominoLazyTotal x r q b < m - fixedExternalDominoMax x r b

theorem dominoTruncation_iff_forall_admissible {o : Orientation} {i : ℕ}
    (x : Point) (r : Fin i → RetainedBlock o) (m : ℕ) (D : Finset Point)
    (q : Fin (i + 1) → ℕ) :
    DominoTruncation x r m D q ↔ ∀ b, DominoAdmissible x r m D q b := by
  constructor
  · intro h b
    by_cases hb : b.1 ∈ D
    · exact Or.inl hb
    · exact Or.inr (h b hb)
  · intro h b hb
    exact (h b).resolve_left hb

/-- Unnormalized weight after imposing the finite level event. -/
noncomputable def conditionedGapVectorMass {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m : ℕ) (D : Finset Point)
    (q : Fin (i + 1) → ℕ) : ℝ := by
  classical
  exact if DominoTruncation x r m D q then gapVectorMass q else 0

/-- One local factor in the finite conditioned density. -/
noncomputable def conditionedDominoCoordinateMass {o : Orientation} {i : ℕ}
    (x : Point) (r : Fin i → RetainedBlock o) (m : ℕ) (D : Finset Point)
    (q : Fin (i + 1) → ℕ) (b : ExternalDomino x r) : ℝ := by
  classical
  exact if DominoAdmissible x r m D q b then dominoCoordinateMass x r q b else 0

/-- Full finite-fibre disintegration: after fixing external and level/favorite
data, the unnormalized conditional density is a product of independent local
domino factors, each with precisely its own cutoff. -/
theorem conditionedGapVectorMass_factorization {o : Orientation} {i : ℕ}
    (x : Point) (r : Fin i → RetainedBlock o) (m : ℕ) (D : Finset Point)
    (q : Fin (i + 1) → ℕ) :
    conditionedGapVectorMass x r m D q =
      ∏ b : ExternalDomino x r, conditionedDominoCoordinateMass x r m D q b := by
  classical
  by_cases htr : DominoTruncation x r m D q
  · have hall := (dominoTruncation_iff_forall_admissible x r m D q).mp htr
    rw [conditionedGapVectorMass, if_pos htr, gapVectorMass_factorization x r]
    apply Finset.prod_congr rfl
    intro b _
    unfold conditionedDominoCoordinateMass
    rw [if_pos (hall b)]
  · have hnall : ¬∀ b, DominoAdmissible x r m D q b :=
      mt (dominoTruncation_iff_forall_admissible x r m D q).mpr htr
    push Not at hnall
    obtain ⟨b, hb⟩ := hnall
    rw [conditionedGapVectorMass, if_neg htr]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ b)
    unfold conditionedDominoCoordinateMass
    rw [if_neg hb]

/-- The normalized one-domino law appearing in HLOZ (6.7), now with its
finite-fibre cutoff made explicit. -/
noncomputable def truncatedDominoMass {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m : ℕ) (b : ExternalDomino x r)
    (ℓ : ℕ) : ℝ :=
  if ℓ < m - fixedExternalDominoMax x r b then
    NegativeBinomial.mass (15 / 16 : ℝ) (dominoExternalMultiplicity x r b) ℓ /
      ∑ j ∈ Finset.range (m - fixedExternalDominoMax x r b),
        NegativeBinomial.mass (15 / 16 : ℝ) (dominoExternalMultiplicity x r b) j
  else 0

/-! ## Normalization of the capped product law -/

@[simp] theorem groupByDominoEquiv_apply {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (α : Type*) (q : Fin (i + 1) → α)
    (b : ExternalDomino x r) (k : CoordinatesAt x r b) :
    (groupByDominoEquiv x r α q) b k = q k.1 := rfl

noncomputable def conditionedCappedDominoMass {o : Orientation} {i : ℕ}
    (x : Point) (r : Fin i → RetainedBlock o) (m cap : ℕ) (D : Finset Point)
    (b : ExternalDomino x r) (v : CoordinatesAt x r b → Fin (cap + 1)) : ℝ := by
  classical
  exact if b.1 ∈ D ∨
      (∑ k, (v k : ℕ)) < m - fixedExternalDominoMax x r b then
    ∏ k, geometricGapMass (v k : ℕ)
  else 0

theorem conditionedDominoCoordinateMass_eq_capped {o : Orientation} {i : ℕ}
    (x : Point) (r : Fin i → RetainedBlock o) (m cap : ℕ) (D : Finset Point)
    (q : CappedCoordinates i cap) (b : ExternalDomino x r) :
    conditionedDominoCoordinateMass x r m D (fun k ↦ (q k : ℕ)) b =
      conditionedCappedDominoMass x r m cap D b ((groupByDominoEquiv x r _ q) b) := by
  classical
  unfold conditionedDominoCoordinateMass conditionedCappedDominoMass
  unfold DominoAdmissible dominoCoordinateMass dominoLazyTotal
  simp only [groupByDominoEquiv_apply]
  rfl

/-- Finite normalizing constant on the capped external-trace fibre. -/
noncomputable def cappedConditionedPartition {o : Orientation} {i : ℕ}
    (x : Point) (r : Fin i → RetainedBlock o) (m cap : ℕ) (D : Finset Point) : ℝ :=
  ∑ q : CappedCoordinates i cap,
    conditionedGapVectorMass x r m D (fun k ↦ (q k : ℕ))

/-- Local finite normalizing constant for one spatial domino. -/
noncomputable def cappedDominoPartition {o : Orientation} {i : ℕ}
    (x : Point) (r : Fin i → RetainedBlock o) (m cap : ℕ) (D : Finset Point)
    (b : ExternalDomino x r) : ℝ :=
  ∑ v : CoordinatesAt x r b → Fin (cap + 1),
    conditionedCappedDominoMass x r m cap D b v

theorem conditionedGapVectorMass_eq_capped_product {o : Orientation} {i : ℕ}
    (x : Point) (r : Fin i → RetainedBlock o) (m cap : ℕ) (D : Finset Point)
    (q : CappedCoordinates i cap) :
    conditionedGapVectorMass x r m D (fun k ↦ (q k : ℕ)) =
      ∏ b : ExternalDomino x r,
        conditionedCappedDominoMass x r m cap D b ((groupByDominoEquiv x r _ q) b) := by
  rw [conditionedGapVectorMass_factorization]
  apply Finset.prod_congr rfl
  intro b _
  exact conditionedDominoCoordinateMass_eq_capped x r m cap D q b

/-- The capped conditioned partition function factors over spatial dominoes. -/
theorem cappedConditionedPartition_factorization {o : Orientation} {i : ℕ}
    (x : Point) (r : Fin i → RetainedBlock o) (m cap : ℕ) (D : Finset Point) :
    cappedConditionedPartition x r m cap D =
      ∏ b : ExternalDomino x r, cappedDominoPartition x r m cap D b := by
  classical
  unfold cappedConditionedPartition cappedDominoPartition
  calc
    (∑ q : CappedCoordinates i cap,
        conditionedGapVectorMass x r m D (fun k ↦ (q k : ℕ))) =
        ∑ Q : (b : ExternalDomino x r) → CoordinatesAt x r b → Fin (cap + 1),
          ∏ b, conditionedCappedDominoMass x r m cap D b (Q b) :=
      Fintype.sum_equiv (groupByDominoEquiv x r (Fin (cap + 1))) _ _
        (fun q ↦ conditionedGapVectorMass_eq_capped_product x r m cap D q)
    _ = ∏ b : ExternalDomino x r,
        ∑ v : CoordinatesAt x r b → Fin (cap + 1),
          conditionedCappedDominoMass x r m cap D b v :=
      (Fintype.prod_sum fun b v ↦ conditionedCappedDominoMass x r m cap D b v).symm

/-- Normalized mass on a capped insertion vector after fixing the external
trace and the level/favorite data. -/
noncomputable def cappedConditionedDensity {o : Orientation} {i : ℕ}
    (x : Point) (r : Fin i → RetainedBlock o) (m cap : ℕ) (D : Finset Point)
    (q : CappedCoordinates i cap) : ℝ :=
  conditionedGapVectorMass x r m D (fun k ↦ (q k : ℕ)) /
    cappedConditionedPartition x r m cap D

/-- Normalized local mass on the capped coordinates of one domino. -/
noncomputable def cappedDominoDensity {o : Orientation} {i : ℕ}
    (x : Point) (r : Fin i → RetainedBlock o) (m cap : ℕ) (D : Finset Point)
    (b : ExternalDomino x r) (v : CoordinatesAt x r b → Fin (cap + 1)) : ℝ :=
  conditionedCappedDominoMass x r m cap D b v /
    cappedDominoPartition x r m cap D b

/-- Exact finite conditional independence: the normalized capped density is
the product of its normalized spatial-domino marginals. -/
theorem cappedConditionedDensity_factorization {o : Orientation} {i : ℕ}
    (x : Point) (r : Fin i → RetainedBlock o) (m cap : ℕ) (D : Finset Point)
    (q : CappedCoordinates i cap) :
    cappedConditionedDensity x r m cap D q =
      ∏ b : ExternalDomino x r,
        cappedDominoDensity x r m cap D b ((groupByDominoEquiv x r _ q) b) := by
  unfold cappedConditionedDensity cappedDominoDensity
  rw [conditionedGapVectorMass_eq_capped_product,
    cappedConditionedPartition_factorization]
  exact (Finset.prod_div_distrib _ _).symm

/-- On every non-distinguished domino, the two endpoint inequalities imposed
by `M_m^k` are exactly one upper truncation on that domino's lazy coordinate.
No probabilistic or stopping-time input occurs in this equivalence. -/
theorem endpointsBelowLevelAway_iff_dominoTruncation
    {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m : ℕ) (D : Finset Point)
    (q : Fin (i + 1) → ℕ) :
    EndpointsBelowLevelAway x r m D q ↔ DominoTruncation x r m D q := by
  constructor
  · intro h b hb
    have hend := h b hb
    apply Nat.lt_sub_iff_add_lt.mpr
    unfold fixedExternalDominoMax
    rw [add_comm, max_add]
    exact max_lt hend.1 hend.2
  · intro h b hb
    have hsum := Nat.lt_sub_iff_add_lt.mp (h b hb)
    unfold fixedExternalDominoMax at hsum
    rw [add_comm, max_add, max_lt_iff] at hsum
    exact hsum

/-- The same level condition stated using the actual local times of the
inserted position path. -/
def ActualEndpointsBelowLevelAway {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m : ℕ) (D : Finset Point)
    (q : Fin (i + 1) → ℕ) : Prop :=
  ∀ b : ExternalDomino x r, b.1 ∉ D →
    listLocalTime (insertedPath x r q) b.1 < m ∧
      listLocalTime (insertedPath x r q) (excursionMiddle o b.1) < m

/-- Genuine finite-path form of the HLOZ observation that, after the external
trace and distinguished dominoes are fixed, the level event imposes exactly
independent upper truncations on the remaining domino coordinates. -/
theorem actualEndpointsBelowLevelAway_iff_dominoTruncation
    {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m : ℕ) (D : Finset Point)
    (q : Fin (i + 1) → ℕ) (hdis : BaseMiddleDisjoint x r) :
    ActualEndpointsBelowLevelAway x r m D q ↔ DominoTruncation x r m D q := by
  rw [← endpointsBelowLevelAway_iff_dominoTruncation x r m D q]
  constructor
  · intro h b hb
    simpa [insertedPath_localTime_at_base x r q hdis b,
      insertedPath_localTime_at_middle x r q hdis b] using h b hb
  · intro h b hb
    simpa [insertedPath_localTime_at_base x r q hdis b,
      insertedPath_localTime_at_middle x r q hdis b] using h b hb

/-- Capped insertion vectors satisfying the finite level/favorite datum. -/
abbrev CappedLevelCoordinates {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m cap : ℕ) (D : Finset Point) :=
  {q : CappedCoordinates i cap //
    DominoTruncation x r m D (fun k ↦ (q k : ℕ))}

/-- Genuine words in the capped external-trace fibre satisfying the same
finite level/favorite datum. -/
def CappedLevelSpatialWord {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m cap : ℕ) (D : Finset Point) :=
  {w : List Block // ∃ q : CappedLevelCoordinates x r m cap D,
    insertGapVector r (fun k ↦ (q.1 k : ℕ)) = w}

/-- Disintegration of the capped deletion fibre after fixing both the
external trace and the level/favorite data. -/
noncomputable def cappedLevelSpatialEquiv {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m cap : ℕ) (D : Finset Point) :
    CappedLevelCoordinates x r m cap D ≃ CappedLevelSpatialWord x r m cap D where
  toFun q := ⟨insertGapVector r (fun k ↦ (q.1 k : ℕ)), ⟨q, rfl⟩⟩
  invFun w := Classical.choose w.property
  left_inv q := by
    apply Subtype.ext
    funext k
    apply Fin.ext
    have hnat := insertGapVector_injective r
      (Classical.choose_spec (show ∃ d : CappedLevelCoordinates x r m cap D,
        insertGapVector r (fun k ↦ (d.1 k : ℕ)) =
          insertGapVector r (fun k ↦ (q.1 k : ℕ)) from ⟨q, rfl⟩))
    exact congrFun hnat k
  right_inv w := by
    apply Subtype.ext
    exact Classical.choose_spec w.property

noncomputable instance {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m cap : ℕ) (D : Finset Point) :
    Fintype (CappedLevelSpatialWord x r m cap D) := by
  classical
  exact Fintype.ofEquiv (CappedLevelCoordinates x r m cap D)
    (cappedLevelSpatialEquiv x r m cap D)

end Erdos1165.SpatialInsertionFiber
