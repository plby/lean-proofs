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

import ErdosProblems.Erdos1165.LazyDecomposition
import ErdosProblems.Erdos1165.NegativeBinomial

/-!
# Finite path insertion for the HLOZ lazy decomposition

The deletion in `LazyDecomposition` reads the increments in disjoint pairs.
There are sixteen possible two-increment blocks and, for either orientation,
exactly one of them is deleted.  This file proves the finite combinatorial and
probabilistic statement behind the geometric variables in HLOZ.

Fix `i > 0` retained blocks and stop when the `i`-th retained block is read.
A deleted-block pattern with `j` deletions is a multiset of cardinality `j`
on `Fin i`: its multiplicity at `k` is the number of deleted blocks inserted
immediately before retained block `k`.  Thus it is a weak composition of `j`
into `i` parts.  Together with the `i` retained block values, this data inserts
to a unique finite block word.  We package the graph of this insertion as the
type `InsertedWord`; `insertionEquiv` is the path-insertion bijection.

The exact counts are

`choose (i + j - 1) j * 15^i`

and hence, under the uniform sixteen-letter IID block law, the failure count
has mass

`choose (i + j - 1) j * (15/16)^i * (1/16)^j`.

We also prove the product factorization into `i` geometric gap masses and the
conditional factorization given any fixed retained word.  These are
deterministic-external-time statements.  Passing to a random external stopping
time additionally needs stopping-time measurability and a strong Markov theorem;
that extension is intentionally not asserted here.
-/

open scoped BigOperators ENNReal

namespace Erdos1165.PathInsertion

open LazyDecomposition

/-! ## The sixteen two-increment blocks -/

/-- A block consists of two consecutive random-walk directions. -/
abbrev Block := Direction × Direction

/-- The unique block erased in the selected orientation. -/
def removableBlock : Orientation → Block
  | .even => (0, 1)
  | .shifted => (1, 0)

/-- Position after the first increment of a block based at `x`. -/
def blockMiddle (x : Point) (b : Block) : Point := x + directionVector b.1

/-- Position after both increments of a block based at `x`. -/
def blockEnd (x : Point) (b : Block) : Point :=
  x + directionVector b.1 + directionVector b.2

/-- The block formulation agrees exactly with `LazyDecomposition.Removable`. -/
theorem removable_block_iff (o : Orientation) (x : Point) (b : Block) :
    Removable o x (blockMiddle x b) (blockEnd x b) ↔ b = removableBlock o := by
  rcases x with ⟨x₁, x₂⟩
  rcases b with ⟨d₁, d₂⟩
  cases o <;> fin_cases d₁ <;> fin_cases d₂ <;>
    simp [Removable, excursionMiddle, removableBlock, blockMiddle, blockEnd,
      directionVector, e₁] <;> omega

@[simp] theorem card_block : Fintype.card Block = 16 := by
  simp [Block, Fintype.card_prod]

/-- The fifteen blocks retained by deletion. -/
abbrev RetainedBlock (o : Orientation) := {b : Block // b ≠ removableBlock o}

@[simp] theorem card_retainedBlock (o : Orientation) :
    Fintype.card (RetainedBlock o) = 15 := by
  rw [← Nat.add_left_cancel_iff (n := 1)]
  simpa [Fintype.card_unique] using
    (Fintype.card_subtype_compl (fun b : Block ↦ b = removableBlock o)).symm

/-! ## Insertion data and its block word -/

/-- A multiset on `Fin i` is the weak-composition encoding of the gaps. -/
abbrev GapPattern (i j : ℕ) := Sym (Fin i) j

/-- Number of removable blocks inserted before retained block `k`. -/
def gapMultiplicity {i j : ℕ} (g : GapPattern i j) (k : Fin i) : ℕ :=
  g.toMultiset.count k

theorem sum_gapMultiplicity {i j : ℕ} (g : GapPattern i j) :
    ∑ k : Fin i, gapMultiplicity g k = j := by
  simpa [gapMultiplicity] using
    (Multiset.sum_count_eq_card (s := (Finset.univ : Finset (Fin i)))
      (m := g.toMultiset) (fun _ _ ↦ Finset.mem_univ _))

/-- Insertion data: a gap pattern and the retained block at every external time. -/
abbrev InsertionCode (o : Orientation) (i j : ℕ) :=
  GapPattern i j × (Fin i → RetainedBlock o)

/-- The run inserted immediately before retained block `k`. -/
def insertedRun {o : Orientation} {i j : ℕ} (c : InsertionCode o i j) (k : Fin i) :
    List Block :=
  List.replicate (gapMultiplicity c.1 k) (removableBlock o) ++ [(c.2 k : Block)]

/-- Insert all removable excursions into a retained block word. -/
def insertBlocks {o : Orientation} {i j : ℕ} (c : InsertionCode o i j) : List Block :=
  (List.ofFn fun k : Fin i ↦ insertedRun c k).flatten

/-- Delete the distinguished block letter. -/
def deleteRemovableBlocks (o : Orientation) (w : List Block) : List Block :=
  w.filter fun b ↦ b ≠ removableBlock o

@[simp] theorem insertedRun_count_removable {o : Orientation} {i j : ℕ}
    (c : InsertionCode o i j) (k : Fin i) :
    (insertedRun c k).count (removableBlock o) = gapMultiplicity c.1 k := by
  classical
  simp [insertedRun, (c.2 k).property]

@[simp] theorem insertedRun_filter_removable {o : Orientation} {i j : ℕ}
    (c : InsertionCode o i j) (k : Fin i) :
    (insertedRun c k).filter (fun b ↦ b ≠ removableBlock o) = [(c.2 k : Block)] := by
  classical
  simp [insertedRun, (c.2 k).property]

theorem insertBlocks_length {o : Orientation} {i j : ℕ} (c : InsertionCode o i j) :
    (insertBlocks c).length = i + j := by
  classical
  simp only [insertBlocks, List.length_flatten, List.map_ofFn, Function.comp_def,
    insertedRun, List.length_append, List.length_replicate, List.length_singleton,
    List.sum_ofFn]
  rw [Finset.sum_add_distrib, sum_gapMultiplicity]
  simp [Nat.add_comm]

theorem insertBlocks_count_removable {o : Orientation} {i j : ℕ}
    (c : InsertionCode o i j) :
    (insertBlocks c).count (removableBlock o) = j := by
  classical
  simp [insertBlocks, List.count_flatten, List.map_ofFn, List.sum_ofFn,
    sum_gapMultiplicity]

theorem deleteRemovableBlocks_insertBlocks {o : Orientation} {i j : ℕ}
    (c : InsertionCode o i j) :
    deleteRemovableBlocks o (insertBlocks c) = List.ofFn fun k ↦ (c.2 k : Block) := by
  classical
  simp only [deleteRemovableBlocks, insertBlocks, List.filter_flatten, List.map_ofFn]
  have hfun :
      ((List.filter (fun b : Block ↦ b ≠ removableBlock o)) ∘
          fun k : Fin i ↦ insertedRun c k) =
        (fun k : Fin i ↦ [(c.2 k : Block)]) := by
    funext k
    exact insertedRun_filter_removable c k
  rw [hfun]
  rw [List.ofFn_eq_map, List.ofFn_eq_map]
  induction List.finRange i with
  | nil => rfl
  | cons k ks ih => simp [ih]

theorem insertBlocks_retained_length {o : Orientation} {i j : ℕ}
    (c : InsertionCode o i j) :
    (deleteRemovableBlocks o (insertBlocks c)).length = i := by
  rw [deleteRemovableBlocks_insertBlocks]
  simp

/-! ## Connection to the lattice-position deletion -/

/-- Positions after the current base point while following a list of blocks. -/
def blockPathTail (x : Point) : List Block → List Point
  | [] => []
  | b :: bs => blockMiddle x b :: blockEnd x b :: blockPathTail (blockEnd x b) bs

/-- The lattice path obtained by following a block word from `x`. -/
def blockPath (x : Point) (bs : List Block) : List Point := x :: blockPathTail x bs

@[simp] theorem blockEnd_removableBlock (o : Orientation) (x : Point) :
    blockEnd x (removableBlock o) = x := by
  rcases x with ⟨x₁, x₂⟩
  cases o <;> simp [blockEnd, removableBlock, directionVector]

@[simp] theorem blockPathTail_length (x : Point) (bs : List Block) :
    (blockPathTail x bs).length = 2 * bs.length := by
  induction bs generalizing x with
  | nil => simp [blockPathTail]
  | cons b bs ih =>
      simp [blockPathTail, ih]
      omega

@[simp] theorem blockPath_length (x : Point) (bs : List Block) :
    (blockPath x bs).length = 2 * bs.length + 1 := by
  simp [blockPath]

theorem compressTail_blockPathTail (o : Orientation) (x : Point) :
    ∀ bs : List Block,
      compressTail o x (blockPathTail x bs) =
        (blockPath x (deleteRemovableBlocks o bs)).tail := by
  intro bs
  induction bs generalizing x with
  | nil => simp [blockPathTail, blockPath, deleteRemovableBlocks, compressTail]
  | cons b bs ih =>
      by_cases hb : b = removableBlock o
      · have hrem : Removable o x (blockMiddle x b) (blockEnd x b) :=
          (removable_block_iff o x b).2 hb
        simp only [blockPathTail, compressTail, if_pos hrem]
        rw [ih]
        subst b
        simp [deleteRemovableBlocks, blockPath]
      · have hrem : ¬Removable o x (blockMiddle x b) (blockEnd x b) :=
          (removable_block_iff o x b).not.mpr hb
        simp only [blockPathTail, compressTail, if_neg hrem]
        rw [ih]
        simp [deleteRemovableBlocks, hb, blockPath, blockPathTail]

/-- Pairwise deletion on positions is exactly filtering out the removable
letters in the underlying block word. -/
theorem externalPath_blockPath (o : Orientation) (x : Point) (bs : List Block) :
    externalPath o (blockPath x bs) = blockPath x (deleteRemovableBlocks o bs) := by
  simp only [blockPath, externalPath]
  rw [compressTail_blockPathTail]
  rfl

/-- The position path produced by insertion compresses back to the prescribed
retained block word. -/
theorem externalPath_blockPath_insertBlocks {o : Orientation} {i j : ℕ}
    (c : InsertionCode o i j) (x : Point) :
    externalPath o (blockPath x (insertBlocks c)) =
      blockPath x (List.ofFn fun k ↦ (c.2 k : Block)) := by
  rw [externalPath_blockPath, deleteRemovableBlocks_insertBlocks]

theorem removedExcursionsTail_blockPathTail (o : Orientation) (x : Point) :
    ∀ bs : List Block,
      removedExcursionsTail o x (blockPathTail x bs) =
        bs.count (removableBlock o) := by
  intro bs
  induction bs generalizing x with
  | nil => simp [blockPathTail, removedExcursionsTail]
  | cons b bs ih =>
      by_cases hb : b = removableBlock o
      · have hrem : Removable o x (blockMiddle x b) (blockEnd x b) :=
          (removable_block_iff o x b).2 hb
        simp only [blockPathTail, removedExcursionsTail, if_pos hrem]
        rw [ih]
        simp [hb, Nat.add_comm]
      · have hrem : ¬Removable o x (blockMiddle x b) (blockEnd x b) :=
          (removable_block_iff o x b).not.mpr hb
        simp only [blockPathTail, removedExcursionsTail, if_neg hrem]
        rw [ih]
        simp [hb]

theorem removedExcursions_blockPath (o : Orientation) (x : Point) (bs : List Block) :
    removedExcursions o (blockPath x bs) = bs.count (removableBlock o) := by
  simp only [blockPath, removedExcursions]
  exact removedExcursionsTail_blockPathTail o x bs

theorem removedExcursions_blockPath_insertBlocks {o : Orientation} {i j : ℕ}
    (c : InsertionCode o i j) (x : Point) :
    removedExcursions o (blockPath x (insertBlocks c)) = j := by
  rw [removedExcursions_blockPath, insertBlocks_count_removable]

theorem externalClock_blockPath_insertBlocks {o : Orientation} {i j : ℕ}
    (c : InsertionCode o i j) (x : Point) :
    externalClock o (blockPath x (insertBlocks c)) = 2 * i := by
  rw [externalClock, externalPath_blockPath_insertBlocks, blockPath_length]
  simp

/-! ## Unique decoding and the genuine word-level bijection -/

/-- Parse a block word into runs, carrying the number of removable letters
seen since the preceding retained block. -/
def decodeRunsAux (o : Orientation) : ℕ → List Block → List (ℕ × Block)
  | _, [] => []
  | q, b :: bs =>
      if b = removableBlock o then decodeRunsAux o (q + 1) bs
      else (q, b) :: decodeRunsAux o 0 bs

def decodeRuns (o : Orientation) (bs : List Block) : List (ℕ × Block) :=
  decodeRunsAux o 0 bs

theorem decodeRunsAux_replicate (o : Orientation) (q n : ℕ) {b : Block}
    (hb : b ≠ removableBlock o) (bs : List Block) :
    decodeRunsAux o q (List.replicate n (removableBlock o) ++ b :: bs) =
      (q + n, b) :: decodeRunsAux o 0 bs := by
  induction n generalizing q with
  | zero => simp [decodeRunsAux, hb]
  | succ n ih =>
      simp only [List.replicate_succ, List.cons_append, decodeRunsAux]
      rw [ih]
      ac_rfl

/-- Decoding an inserted word recovers every gap multiplicity and retained
block, in order. -/
theorem decodeRuns_insertBlocks {o : Orientation} {i j : ℕ}
    (c : InsertionCode o i j) :
    decodeRuns o (insertBlocks c) =
      List.ofFn fun k ↦ (gapMultiplicity c.1 k, (c.2 k : Block)) := by
  classical
  unfold decodeRuns insertBlocks
  rw [List.ofFn_eq_map, List.ofFn_eq_map]
  induction List.finRange i with
  | nil => rfl
  | cons k ks ih =>
      simp only [List.map_cons, List.flatten_cons, insertedRun]
      rw [List.append_assoc]
      simp only [List.singleton_append]
      rw [decodeRunsAux_replicate o 0 (gapMultiplicity c.1 k) (c.2 k).property]
      unfold insertedRun at ih
      rw [ih]
      simp

/-- The inserted block word uniquely determines both its weak-composition
gaps and its retained block values. -/
theorem insertBlocks_injective (o : Orientation) (i j : ℕ) :
    Function.Injective (@insertBlocks o i j) := by
  intro c d hcd
  have hdecode := congrArg (decodeRuns o) hcd
  rw [decodeRuns_insertBlocks, decodeRuns_insertBlocks] at hdecode
  have hpairs := List.ofFn_injective hdecode
  apply Prod.ext
  · apply Sym.coe_injective
    apply Multiset.count_injective
    funext k
    exact congrArg Prod.fst (congrFun hpairs k)
  · funext k
    apply Subtype.ext
    exact congrArg Prod.snd (congrFun hpairs k)

/-- Actual block words obtained by inserting `j` removable excursions before
the `i`-th retained block. -/
def StoppedBlockWord (o : Orientation) (i j : ℕ) :=
  {w : List Block // ∃ c : InsertionCode o i j, insertBlocks c = w}

/-- The path-insertion bijection with the genuine range of inserted words. -/
noncomputable def stoppedWordEquiv (o : Orientation) (i j : ℕ) :
    InsertionCode o i j ≃ StoppedBlockWord o i j where
  toFun c := ⟨insertBlocks c, ⟨c, rfl⟩⟩
  invFun w := Classical.choose w.property
  left_inv c := by
    apply insertBlocks_injective o i j
    exact Classical.choose_spec (show ∃ d : InsertionCode o i j,
      insertBlocks d = insertBlocks c from ⟨c, rfl⟩)
  right_inv w := by
    apply Subtype.ext
    exact Classical.choose_spec w.property

/-- A finite inserted word is the graph of the insertion map.  Retaining the
code makes the inverse map constructive while the equation records the actual
block word on which `LazyDecomposition` operates. -/
structure InsertedWord (o : Orientation) (i j : ℕ) where
  code : InsertionCode o i j
  blocks : List Block
  blocks_eq : blocks = insertBlocks code

/-- The finite path-insertion bijection. -/
def insertionEquiv (o : Orientation) (i j : ℕ) :
    InsertionCode o i j ≃ InsertedWord o i j where
  toFun c := ⟨c, insertBlocks c, rfl⟩
  invFun w := w.code
  left_inv _ := rfl
  right_inv w := by
    rcases w with ⟨c, blocks, hblocks⟩
    subst blocks
    rfl

@[simp] theorem insertionEquiv_apply_blocks {o : Orientation} {i j : ℕ}
    (c : InsertionCode o i j) : (insertionEquiv o i j c).blocks = insertBlocks c := rfl

/-! ## Exact finite counts -/

@[simp] theorem card_gapPattern (i j : ℕ) :
    Fintype.card (GapPattern i j) = (i + j - 1).choose j := by
  simpa using (Sym.card_sym_eq_choose (α := Fin i) j)

@[simp] theorem card_insertionCode (o : Orientation) (i j : ℕ) :
    Fintype.card (InsertionCode o i j) = (i + j - 1).choose j * 15 ^ i := by
  simp [InsertionCode, GapPattern, Fintype.card_prod]

noncomputable instance (o : Orientation) (i j : ℕ) : Fintype (InsertedWord o i j) :=
  Fintype.ofEquiv (InsertionCode o i j) (insertionEquiv o i j)

@[simp] theorem card_insertedWord (o : Orientation) (i j : ℕ) :
    Fintype.card (InsertedWord o i j) = (i + j - 1).choose j * 15 ^ i := by
  rw [← Fintype.card_congr (insertionEquiv o i j)]
  exact card_insertionCode o i j

noncomputable instance (o : Orientation) (i j : ℕ) : Fintype (StoppedBlockWord o i j) :=
  Fintype.ofEquiv (InsertionCode o i j) (stoppedWordEquiv o i j)

@[simp] theorem card_stoppedBlockWord (o : Orientation) (i j : ℕ) :
    Fintype.card (StoppedBlockWord o i j) = (i + j - 1).choose j * 15 ^ i := by
  rw [← Fintype.card_congr (stoppedWordEquiv o i j)]
  exact card_insertionCode o i j

/-! ## Geometric gap factorization -/

/-- Mass of `q` failures before one success for success probability `15/16`. -/
noncomputable def geometricGapMass (q : ℕ) : ℝ :=
  (15 / 16 : ℝ) * (1 / 16 : ℝ) ^ q

theorem geometricGapMass_nonneg (q : ℕ) : 0 ≤ geometricGapMass q := by
  unfold geometricGapMass
  positivity

theorem hasSum_geometricGapMass : HasSum geometricGapMass 1 := by
  unfold geometricGapMass
  have h := hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 16 : ℝ)‖ < 1)
  have h' := h.mul_left (15 / 16 : ℝ)
  norm_num at h' ⊢
  exact h'

/-- The geometric gap mass as a genuine probability mass function. -/
noncomputable def geometricGapLaw : PMF ℕ :=
  ⟨fun q ↦ ENNReal.ofReal (geometricGapMass q), by
    apply ENNReal.hasSum_coe.mpr
    rw [← Real.toNNReal_one]
    exact hasSum_geometricGapMass.toNNReal geometricGapMass_nonneg⟩

@[simp] theorem geometricGapLaw_apply (q : ℕ) :
    geometricGapLaw q = ENNReal.ofReal (geometricGapMass q) := rfl

/-- For a fixed insertion pattern, the product of the individual gap masses
depends only on its total number `j` of inserted excursions. -/
theorem prod_geometricGapMass {i j : ℕ} (g : GapPattern i j) :
    ∏ k : Fin i, geometricGapMass (gapMultiplicity g k) =
      (15 / 16 : ℝ) ^ i * (1 / 16 : ℝ) ^ j := by
  simp only [geometricGapMass, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [Finset.prod_pow_eq_pow_sum, sum_gapMultiplicity]

/-! ## Uniform finite-word law and conditional factorization -/

/-- Uniform law of one two-increment block. -/
noncomputable def uniformBlock : PMF Block := PMF.uniformOfFintype Block

@[simp] theorem uniformBlock_apply (b : Block) :
    uniformBlock b = (16 : ℝ≥0∞)⁻¹ := by
  simp [uniformBlock]

/-- Uniform law on `n` independent block coordinates.  Since every word has
the same mass, this is the finite-dimensional IID block law. -/
noncomputable def uniformBlockWords (n : ℕ) : PMF (Fin n → Block) :=
  PMF.uniformOfFintype (Fin n → Block)

@[simp] theorem uniformBlockWords_apply (n : ℕ) (w : Fin n → Block) :
    uniformBlockWords n w = ((16 : ℝ≥0∞)⁻¹) ^ n := by
  simp [uniformBlockWords]
  exact ENNReal.inv_pow

/-- Every length-`n` block word has this mass under the IID uniform block law. -/
noncomputable def uniformBlockWordMass (n : ℕ) : ℝ := (1 / 16 : ℝ) ^ n

/-- Joint mass of observing a specified retained word of length `i` and exactly
`j` inserted removable blocks before its last block. -/
noncomputable def fixedExternalJointMass (i j : ℕ) : ℝ :=
  (Fintype.card (GapPattern i j) : ℝ) * uniformBlockWordMass (i + j)

/-- Marginal mass of a specified retained word. -/
noncomputable def fixedExternalMarginalMass (i : ℕ) : ℝ := (1 / 15 : ℝ) ^ i

/-- The unconditional mass of having `j` failures before the `i`-th success,
with all retained block values allowed. -/
noncomputable def stoppedFailureMass (o : Orientation) (i j : ℕ) : ℝ :=
  (Fintype.card (StoppedBlockWord o i j) : ℝ) * uniformBlockWordMass (i + j)

theorem fixedExternalJointMass_eq (i j : ℕ) :
    fixedExternalJointMass i j =
      ((i + j - 1).choose j : ℝ) * (1 / 16 : ℝ) ^ (i + j) := by
  simp [fixedExternalJointMass, uniformBlockWordMass]

/-- Joint mass factors as the retained-word marginal times the HLOZ
negative-binomial mass.  This is the exact finite conditional-law identity. -/
theorem fixedExternalJointMass_factorization {i : ℕ} (hi : 0 < i) (j : ℕ) :
    fixedExternalJointMass i j = fixedExternalMarginalMass i *
      NegativeBinomial.mass (15 / 16 : ℝ) i j := by
  rw [fixedExternalJointMass_eq, fixedExternalMarginalMass,
    NegativeBinomial.mass_eq_hloz_formula (15 / 16 : ℝ) hi]
  have hp : (1 / 16 : ℝ) ^ i = (1 / 15 : ℝ) ^ i * (15 / 16 : ℝ) ^ i := by
    rw [← mul_pow]
    norm_num
  rw [pow_add, hp]
  ring

/-- Conditioning on any fixed retained word gives precisely the
negative-binomial mass. -/
theorem fixedExternal_conditionalMass {i : ℕ} (hi : 0 < i) (j : ℕ) :
    fixedExternalJointMass i j / fixedExternalMarginalMass i =
      NegativeBinomial.mass (15 / 16 : ℝ) i j := by
  rw [fixedExternalJointMass_factorization hi]
  field_simp [fixedExternalMarginalMass]

theorem stoppedFailureMass_eq_negativeBinomial (o : Orientation) {i : ℕ}
    (hi : 0 < i) (j : ℕ) :
    stoppedFailureMass o i j = NegativeBinomial.mass (15 / 16 : ℝ) i j := by
  rw [stoppedFailureMass, uniformBlockWordMass, card_stoppedBlockWord,
    NegativeBinomial.mass_eq_hloz_formula (15 / 16 : ℝ) hi]
  push_cast
  rw [pow_add]
  have hp : (15 : ℝ) ^ i * (1 / 16 : ℝ) ^ i = (15 / 16 : ℝ) ^ i := by
    rw [← mul_pow]
    norm_num
  rw [← hp]
  ring

theorem hasSum_stoppedFailureMass (o : Orientation) {i : ℕ} (hi : 0 < i) :
    HasSum (stoppedFailureMass o i) 1 := by
  have h := NegativeBinomial.hasSum_mass (p := (15 / 16 : ℝ))
    (by norm_num) (by norm_num) hi
  exact HasSum.congr_fun h fun j ↦ stoppedFailureMass_eq_negativeBinomial o hi j

theorem stoppedFailureMass_nonneg (o : Orientation) {i : ℕ} (hi : 0 < i) (j : ℕ) :
    0 ≤ stoppedFailureMass o i j := by
  rw [stoppedFailureMass_eq_negativeBinomial o hi]
  exact NegativeBinomial.mass_nonneg (by norm_num) (by norm_num) i j

/-- The finite counting law, packaged as a PMF. -/
noncomputable def stoppedFailureLaw (o : Orientation) (i : ℕ) (hi : 0 < i) : PMF ℕ :=
  ⟨fun j ↦ ENNReal.ofReal (stoppedFailureMass o i j), by
    apply ENNReal.hasSum_coe.mpr
    rw [← Real.toNNReal_one]
    exact (hasSum_stoppedFailureMass o hi).toNNReal (stoppedFailureMass_nonneg o hi)⟩

@[simp] theorem stoppedFailureLaw_apply (o : Orientation) (i : ℕ) (hi : 0 < i) (j : ℕ) :
    stoppedFailureLaw o i hi j = ENNReal.ofReal (stoppedFailureMass o i j) := rfl

/-- The PMF obtained from the path-insertion count is Mathlib-level equal to
the negative-binomial law developed in `NegativeBinomial.lean`. -/
theorem stoppedFailureLaw_eq_negativeBinomialLaw (o : Orientation) (i : ℕ)
    (hi : 0 < i) :
    stoppedFailureLaw o i hi =
      NegativeBinomial.law (15 / 16 : ℝ) (by norm_num) (by norm_num) i hi := by
  ext j
  simp [stoppedFailureMass_eq_negativeBinomial o hi]

/-- A fixed retained word has marginal mass `15⁻ⁱ`; summing the joint masses
over every possible insertion count proves that the conditional denominator is
the claimed one. -/
theorem hasSum_fixedExternalJointMass {i : ℕ} (hi : 0 < i) :
    HasSum (fixedExternalJointMass i) (fixedExternalMarginalMass i) := by
  have h := (NegativeBinomial.hasSum_mass (p := (15 / 16 : ℝ))
    (by norm_num) (by norm_num) hi).mul_left (fixedExternalMarginalMass i)
  have h' := HasSum.congr_fun h fun j ↦ fixedExternalJointMass_factorization hi j
  simpa using h'

end Erdos1165.PathInsertion
