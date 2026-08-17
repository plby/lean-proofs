/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib
import ErdosProblems.Erdos440.SharpUpper
import ErdosProblems.Erdos440.Constant

namespace Erdos440SharpConstruction

open scoped BigOperators
open Filter

set_option autoImplicit false

/-!
This file isolates the finite blocks in the sharpness construction for
Erdős Problem 440.  For a height `X` and a gap parameter `d`, the block
consists of the multiples `d*m` with

`sqrt ((d-1)X) / d < m < sqrt (X/d)`.

The slightly shortened upper endpoint makes the lcm estimate integral and
free of rounding qualifications.  It loses at most a bounded number of terms
from each block, which is harmless in the diagonal construction.
-/

/-- First multiplier in the `d`-th finite block. -/
def blockStart (X d : ℕ) : ℕ := Nat.sqrt ((d - 1) * X) / d + 1

/-- Exclusive upper endpoint for multipliers in the `d`-th finite block. -/
def blockStop (X d : ℕ) : ℕ := Nat.sqrt (X / d)

/-- The ordered `d`-th block. -/
def block (X d : ℕ) : List ℕ :=
  (List.Ico (blockStart X d) (blockStop X d)).map (d * ·)

@[simp] theorem length_block (X d : ℕ) :
    (block X d).length = blockStop X d - blockStart X d := by
  simp [block]

@[simp] theorem mem_block {X d a : ℕ} :
    a ∈ block X d ↔ ∃ m, blockStart X d ≤ m ∧ m < blockStop X d ∧ a = d * m := by
  simp [block]
  aesop

/-- Every block is strictly increasing when its gap parameter is positive. -/
theorem block_pairwise_lt {X d : ℕ} (hd : 0 < d) :
    (block X d).Pairwise (· < ·) := by
  rw [block, List.pairwise_map]
  exact (List.Ico.pairwise_lt _ _).imp (Nat.mul_lt_mul_left hd).2

/-- Scaling two consecutive coprime integers by `d` scales their lcm by `d`. -/
theorem lcm_consecutive_multiples (d m : ℕ) :
    Nat.lcm (d * m) (d * (m + 1)) = d * (m * (m + 1)) := by
  rw [Nat.lcm_mul_left]
  rw [Nat.Coprime.lcm_eq_mul]
  simp [Nat.Coprime]

/-- The conservative upper endpoint of a block gives the required lcm bound. -/
theorem lcm_consecutive_multiples_le {X d m : ℕ}
    (hm : m + 1 ≤ blockStop X d) :
    Nat.lcm (d * m) (d * (m + 1)) ≤ X := by
  rw [lcm_consecutive_multiples]
  have hsquare : (blockStop X d) * (blockStop X d) ≤ X / d := by
    exact Nat.sqrt_le (X / d)
  have hmm : m * (m + 1) ≤ (blockStop X d) * (blockStop X d) := by
    exact Nat.mul_le_mul (Nat.le_trans (Nat.le_succ m) hm) hm
  have hmul : d * (m * (m + 1)) ≤ d * (X / d) :=
    Nat.mul_le_mul_left d (hmm.trans hsquare)
  exact hmul.trans (Nat.mul_div_le X d)

/-- Every adjacent pair inside a block has lcm at most `X`. -/
theorem block_isChain_lcm_le {X d : ℕ} :
    (block X d).IsChain fun a b ↦ Nat.lcm a b ≤ X := by
  rw [block, List.isChain_map]
  exact (List.Ico.isChain_succ _ _).imp_of_mem_imp fun m n _ hn hnstep ↦ by
    subst n
    apply lcm_consecutive_multiples_le
    exact Nat.le_of_lt (List.Ico.mem.mp hn).2

/-- Every term of the `d`-th block lies at or below the upper quadratic
boundary `d*X`. -/
theorem sq_le_mul_of_mem_block {X d a : ℕ} (ha : a ∈ block X d) :
    a * a ≤ d * X := by
  obtain ⟨m, _, hmstop, rfl⟩ := mem_block.mp ha
  have hmle : m * m ≤ X / d :=
    Nat.le_sqrt.mp (Nat.le_of_lt hmstop)
  calc
    (d * m) * (d * m) = (d * d) * (m * m) := by ring
    _ ≤ (d * d) * (X / d) := Nat.mul_le_mul_left (d * d) hmle
    _ = d * (d * (X / d)) := by ring
    _ ≤ d * X := Nat.mul_le_mul_left d (Nat.mul_div_le X d)

/-- Every term of a positive-parameter block is strictly above its lower
quadratic boundary. -/
theorem mul_lt_sq_of_mem_block {X d a : ℕ} (hd : 0 < d)
    (ha : a ∈ block X d) :
    (d - 1) * X < a * a := by
  obtain ⟨m, hmstart, _, rfl⟩ := mem_block.mp ha
  have hquot : Nat.sqrt ((d - 1) * X) / d < m := by
    simpa [blockStart] using hmstart
  have hsqrt : Nat.sqrt ((d - 1) * X) < d * m := by
    simpa [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hd).mp hquot
  have hsq :
      (Nat.sqrt ((d - 1) * X) + 1) *
          (Nat.sqrt ((d - 1) * X) + 1) ≤ (d * m) * (d * m) :=
    Nat.mul_le_mul (Nat.succ_le_of_lt hsqrt) (Nat.succ_le_of_lt hsqrt)
  exact (Nat.lt_succ_sqrt ((d - 1) * X)).trans_le hsq

/-- Blocks with increasing gap parameters occupy disjoint ordered quadratic
annuli, so every entry of the earlier block precedes every entry of the later
block. -/
theorem lt_of_mem_blocks {X d e a b : ℕ} (hd : 0 < d) (hde : d < e)
    (ha : a ∈ block X d) (hb : b ∈ block X e) : a < b := by
  have ha2 : a * a ≤ d * X := sq_le_mul_of_mem_block ha
  have hde' : d ≤ e - 1 := by omega
  have hmid : d * X ≤ (e - 1) * X := Nat.mul_le_mul_right X hde'
  have hb2 : (e - 1) * X < b * b :=
    mul_lt_sq_of_mem_block (lt_trans hd hde) hb
  exact Nat.mul_self_lt_mul_self_iff.mp (ha2.trans_lt (hmid.trans_lt hb2))

/-- Concatenation of the first `J` positive blocks. -/
def initialBlocks (X J : ℕ) : List ℕ :=
  (List.Ico 1 (J + 1)).flatMap (block X)

/-- The finite block construction, including all blocks with parameters
`1,...,J`, is a strictly increasing list. -/
theorem initialBlocks_pairwise_lt (X J : ℕ) :
    (initialBlocks X J).Pairwise (· < ·) := by
  rw [initialBlocks, List.pairwise_flatMap]
  constructor
  · intro d hd
    exact block_pairwise_lt (List.Ico.mem.mp hd).1
  · exact (List.Ico.pairwise_lt 1 (J + 1)).imp_of_mem
      (fun hd _ hde ↦ fun a ha b hb ↦
        lt_of_mem_blocks (List.Ico.mem.mp hd).1 hde ha hb)

/-- The exact length of a block yields a convenient rounding-error estimate:
the expected difference of the two integer square-root cutoffs exceeds the
actual length by at most one. -/
theorem blockStop_le_length_add_start (X d : ℕ) :
    blockStop X d ≤ (block X d).length + blockStart X d := by
  simp only [length_block]
  omega

/-- Expanded exact cardinal formula for the `d`-th block. -/
theorem length_block_eq_sqrt_cutoffs (X d : ℕ) :
    (block X d).length =
      Nat.sqrt (X / d) - Nat.sqrt ((d - 1) * X) / d - 1 := by
  simp only [length_block, blockStop, blockStart]
  omega

/-- The length of the concatenated finite construction is the sum of its
block lengths; this is the finite sum whose normalized limit gives the
partial sums of the Erdős--Szemerédi constant. -/
theorem length_initialBlocks (X J : ℕ) :
    (initialBlocks X J).length =
      ((List.Ico 1 (J + 1)).map fun d ↦ (block X d).length).sum := by
  simp [initialBlocks]

/-- Indices of adjacent pairs in a finite list whose lcm is at most `X`.
The `getD` defaults are never used on the range in question. -/
def goodInternalEdgeIndices (X : ℕ) (l : List ℕ) : Finset ℕ :=
  (Finset.range (l.length - 1)).filter fun i ↦
    Nat.lcm (l.getD i 0) (l.getD (i + 1) 0) ≤ X

/-- A chain all of whose adjacent lcms are at most `X` contributes exactly
`length-1` good internal edges. -/
theorem card_goodInternalEdgeIndices_eq {X : ℕ} {l : List ℕ}
    (hl : l.IsChain fun a b ↦ Nat.lcm a b ≤ X) :
    (goodInternalEdgeIndices X l).card = l.length - 1 := by
  unfold goodInternalEdgeIndices
  rw [Finset.filter_eq_self.2]
  · simp
  · intro i hi
    have hi' : i + 1 < l.length := by
      have hirange := Finset.mem_range.mp hi
      omega
    rw [List.getD_eq_getElem l 0 (by omega), List.getD_eq_getElem l 0 hi']
    exact List.isChain_iff_getElem.mp hl i hi'

/-- Consequently the exact good-edge count supplied by one finite block is
its length minus one. -/
theorem card_goodInternalEdgeIndices_block (X d : ℕ) :
    (goodInternalEdgeIndices X (block X d)).card = (block X d).length - 1 :=
  card_goodInternalEdgeIndices_eq block_isChain_lcm_le

/-! ## Cutoff-truncated stages for the diagonal construction -/

/-- First multiplier after also imposing the absolute cutoff `C`. -/
def truncatedBlockStart (C X d : ℕ) : ℕ :=
  max (blockStart X d) (C / d + 1)

/-- The `d`-th block with all terms at most `C` removed. -/
def truncatedBlock (C X d : ℕ) : List ℕ :=
  (List.Ico (truncatedBlockStart C X d) (blockStop X d)).map (d * ·)

@[simp] theorem length_truncatedBlock (C X d : ℕ) :
    (truncatedBlock C X d).length =
      blockStop X d - truncatedBlockStart C X d := by
  simp [truncatedBlock]

@[simp] theorem mem_truncatedBlock {C X d a : ℕ} :
    a ∈ truncatedBlock C X d ↔
      ∃ m, truncatedBlockStart C X d ≤ m ∧ m < blockStop X d ∧ a = d * m := by
  simp [truncatedBlock]
  aesop

/-- Truncation preserves strict increase inside a block. -/
theorem truncatedBlock_pairwise_lt {C X d : ℕ} (hd : 0 < d) :
    (truncatedBlock C X d).Pairwise (· < ·) := by
  rw [truncatedBlock, List.pairwise_map]
  exact (List.Ico.pairwise_lt _ _).imp (Nat.mul_lt_mul_left hd).2

/-- Truncation preserves the internal lcm bound. -/
theorem truncatedBlock_isChain_lcm_le {C X d : ℕ} :
    (truncatedBlock C X d).IsChain fun a b ↦ Nat.lcm a b ≤ X := by
  rw [truncatedBlock, List.isChain_map]
  exact (List.Ico.isChain_succ _ _).imp_of_mem_imp fun m n _ hn hnstep ↦ by
    subst n
    apply lcm_consecutive_multiples_le
    exact Nat.le_of_lt (List.Ico.mem.mp hn).2

/-- Every entry surviving the cutoff is strictly larger than the cutoff. -/
theorem cutoff_lt_of_mem_truncatedBlock {C X d a : ℕ} (hd : 0 < d)
    (ha : a ∈ truncatedBlock C X d) : C < a := by
  obtain ⟨m, hmstart, _, rfl⟩ := mem_truncatedBlock.mp ha
  have hquot : C / d < m := by
    have : C / d + 1 ≤ truncatedBlockStart C X d :=
      Nat.le_max_right _ _
    omega
  simpa [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hd).mp hquot

/-- A truncated block remains a sub-block of the original quadratic annulus. -/
theorem mem_block_of_mem_truncatedBlock {C X d a : ℕ}
    (ha : a ∈ truncatedBlock C X d) : a ∈ block X d := by
  obtain ⟨m, hmstart, hmstop, rfl⟩ := mem_truncatedBlock.mp ha
  exact mem_block.mpr
    ⟨m, (Nat.le_max_left _ _).trans hmstart, hmstop, rfl⟩

/-- Concatenation of cutoff-truncated blocks `1,...,J`. -/
def truncatedStage (C X J : ℕ) : List ℕ :=
  (List.Ico 1 (J + 1)).flatMap (truncatedBlock C X)

/-- A truncated stage is strictly increasing. -/
theorem truncatedStage_pairwise_lt (C X J : ℕ) :
    (truncatedStage C X J).Pairwise (· < ·) := by
  rw [truncatedStage, List.pairwise_flatMap]
  constructor
  · intro d hd
    exact truncatedBlock_pairwise_lt (List.Ico.mem.mp hd).1
  · exact (List.Ico.pairwise_lt 1 (J + 1)).imp_of_mem
      (fun hd _ hde ↦ fun a ha b hb ↦
        lt_of_mem_blocks (List.Ico.mem.mp hd).1 hde
          (mem_block_of_mem_truncatedBlock ha)
          (mem_block_of_mem_truncatedBlock hb))

/-- Every term in a truncated stage lies above the old maximum `C`. -/
theorem cutoff_lt_of_mem_truncatedStage {C X J a : ℕ}
    (ha : a ∈ truncatedStage C X J) : C < a := by
  obtain ⟨d, hd, had⟩ := List.mem_flatMap.mp ha
  exact cutoff_lt_of_mem_truncatedBlock (List.Ico.mem.mp hd).1 had

/-- The exact good internal-edge count for a truncated block. -/
theorem card_goodInternalEdgeIndices_truncatedBlock (C X d : ℕ) :
    (goodInternalEdgeIndices X (truncatedBlock C X d)).card =
      (truncatedBlock C X d).length - 1 :=
  card_goodInternalEdgeIndices_eq truncatedBlock_isChain_lcm_le

/-! ## A concrete infinite diagonal scaffold -/

/-- Cutoff before stage `r`.  The next cutoff is an elementary upper bound
for all entries of stage `r`. -/
def stageCutoff : ℕ → ℕ
  | 0 => 0
  | r + 1 => (r + 1) * ((stageCutoff r + 1) * (r + 2)) ^ 2

/-- Basic scale at stage `r`. -/
def stageScale (r : ℕ) : ℕ := (stageCutoff r + 1) * (r + 2)

/-- Height used at stage `r`; the fourth power makes the old cutoff negligible
compared with its square root. -/
def stageHeight (r : ℕ) : ℕ := stageScale r ^ 4

/-- Number of annular blocks used at stage `r`. -/
def stageWidth (r : ℕ) : ℕ := r + 1

/-- The concrete `r`-th finite stage. -/
def sharpStage (r : ℕ) : List ℕ :=
  truncatedStage (stageCutoff r) (stageHeight r) (stageWidth r)

@[simp] theorem stageCutoff_succ (r : ℕ) :
    stageCutoff (r + 1) = stageWidth r * stageScale r ^ 2 := by
  simp [stageCutoff, stageWidth, stageScale]

/-- Exact integer square root of the chosen fourth-power stage height. -/
theorem sqrt_stageHeight (r : ℕ) :
    Nat.sqrt (stageHeight r) = stageScale r ^ 2 := by
  rw [stageHeight]
  rw [show stageScale r ^ 4 = (stageScale r ^ 2) * (stageScale r ^ 2) by ring]
  exact Nat.sqrt_eq _

/-- The cutoffs dominate the stage number. -/
theorem le_stageCutoff (r : ℕ) : r ≤ stageCutoff r := by
  induction r with
  | zero => simp [stageCutoff]
  | succ r _ =>
      rw [stageCutoff_succ]
      simp only [stageWidth]
      have hscale : 1 ≤ stageScale r ^ 2 := by
        have : 1 ≤ stageScale r := by
          simp only [stageScale]
          have hpos : 0 < (stageCutoff r + 1) * (r + 2) :=
            Nat.mul_pos (by omega) (by omega)
          omega
        nlinarith
      nlinarith

/-- The stage cutoffs are strictly increasing. -/
theorem stageCutoff_strictMono : StrictMono stageCutoff := by
  apply strictMono_nat_of_lt_succ
  intro r
  rw [stageCutoff_succ]
  have hscale : stageCutoff r < stageScale r := by
    simp only [stageScale]
    nlinarith
  have hscalePos : 0 < stageScale r := by simp [stageScale]
  have hsq : stageScale r ≤ stageScale r ^ 2 := by
    rw [pow_two]
    exact Nat.le_mul_of_pos_right _ hscalePos
  have hwidth : 0 < stageWidth r := by simp [stageWidth]
  exact hscale.trans_le (hsq.trans (Nat.le_mul_of_pos_left _ hwidth))

/-- Every stage is nonempty: its first block contains `cutoff+1`. -/
theorem stage_seed_mem (r : ℕ) : stageCutoff r + 1 ∈ sharpStage r := by
  rw [sharpStage, truncatedStage]
  apply List.mem_flatMap.mpr
  refine ⟨1, ?_, ?_⟩
  · simp [stageWidth]
  · apply mem_truncatedBlock.mpr
    refine ⟨stageCutoff r + 1, ?_, ?_, by simp⟩
    · simp [truncatedBlockStart, blockStart]
    · rw [blockStop, Nat.div_one, sqrt_stageHeight]
      have hlt : stageCutoff r + 1 < stageScale r := by
        simp only [stageScale]
        nlinarith
      have hpos : 0 < stageScale r := by simp [stageScale]
      exact hlt.trans_le (by
        rw [pow_two]
        exact Nat.le_mul_of_pos_right _ hpos)

/-- Every term of a stage is below the next cutoff. -/
theorem mem_sharpStage_lt_nextCutoff {r a : ℕ} (ha : a ∈ sharpStage r) :
    a < stageCutoff (r + 1) := by
  rw [sharpStage, truncatedStage] at ha
  obtain ⟨d, hd, had⟩ := List.mem_flatMap.mp ha
  obtain ⟨m, _, hmstop, rfl⟩ := mem_truncatedBlock.mp had
  have hdpos : 0 < d := (List.Ico.mem.mp hd).1
  have hdle : d ≤ stageWidth r := by
    have := (List.Ico.mem.mp hd).2
    simp only [stageWidth] at this ⊢
    omega
  have hdiv : stageHeight r / d ≤ stageHeight r := Nat.div_le_self _ _
  have hsqrt : Nat.sqrt (stageHeight r / d) ≤ stageScale r ^ 2 := by
    rw [← sqrt_stageHeight r]
    exact Nat.sqrt_le_sqrt hdiv
  have hm : m < stageScale r ^ 2 := hmstop.trans_le hsqrt
  calc
    d * m < d * stageScale r ^ 2 := (Nat.mul_lt_mul_left hdpos).2 hm
    _ ≤ stageWidth r * stageScale r ^ 2 := Nat.mul_le_mul_right _ hdle
    _ = stageCutoff (r + 1) := (stageCutoff_succ r).symm

/-- Every term of an earlier stage precedes every term of a later stage. -/
theorem lt_of_mem_sharpStages {r s a b : ℕ} (hrs : r < s)
    (ha : a ∈ sharpStage r) (hb : b ∈ sharpStage s) : a < b := by
  have haCut : a < stageCutoff (r + 1) := mem_sharpStage_lt_nextCutoff ha
  have hCut : stageCutoff (r + 1) ≤ stageCutoff s :=
    stageCutoff_strictMono.monotone (Nat.succ_le_iff.mpr hrs)
  have hbCut : stageCutoff s < b := by
    simpa [sharpStage] using (cutoff_lt_of_mem_truncatedStage hb)
  exact haCut.trans_le hCut |>.trans hbCut

/-- The set obtained by taking the union of all concrete stages. -/
def sharpSet : Set ℕ := {a | ∃ r, a ∈ sharpStage r}

/-- The stage union is unbounded, hence infinite. -/
theorem sharpSet_infinite : sharpSet.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  refine ⟨stageCutoff (N + 1) + 1, ?_, ?_⟩
  · exact ⟨N + 1, stage_seed_mem (N + 1)⟩
  · have := le_stageCutoff (N + 1)
    omega

/-- Increasing enumeration of the concrete stage union. -/
noncomputable def sharpSequence (i : ℕ) : ℕ :=
  Nat.nth (· ∈ sharpSet) i

/-- The concrete diagonal scaffold is an exact strictly increasing sequence. -/
theorem sharpSequence_strictMono : StrictMono sharpSequence :=
  Nat.nth_strictMono sharpSet_infinite

/-- All entries of the concrete diagonal scaffold are positive. -/
theorem sharpSequence_pos (i : ℕ) : 0 < sharpSequence i := by
  have hi : sharpSequence i ∈ sharpSet := Nat.nth_mem_of_infinite sharpSet_infinite i
  obtain ⟨r, hir⟩ := hi
  exact (Nat.zero_le (stageCutoff r)).trans_lt (cutoff_lt_of_mem_truncatedStage hir)

/-! ## Internal block edges are genuine consecutive edges of the union -/

/-- Two consecutive multipliers surviving in a stage block give two elements
of that stage. -/
theorem internal_pair_mem_sharpStage {r d m : ℕ}
    (hd : d ∈ List.Ico 1 (stageWidth r + 1))
    (hm0 : truncatedBlockStart (stageCutoff r) (stageHeight r) d ≤ m)
    (hm1 : m + 1 < blockStop (stageHeight r) d) :
    d * m ∈ sharpStage r ∧ d * (m + 1) ∈ sharpStage r := by
  rw [sharpStage, truncatedStage]
  constructor <;> apply List.mem_flatMap.mpr <;> refine ⟨d, hd, ?_⟩
  · exact mem_truncatedBlock.mpr ⟨m, hm0, by omega, rfl⟩
  · exact mem_truncatedBlock.mpr ⟨m + 1, hm0.trans (Nat.le_succ _), hm1, rfl⟩

/-- No element of the complete stage union lies strictly between two
consecutive surviving multiples in one block. -/
theorem no_sharpSet_between_internal {r d m z : ℕ}
    (hd : d ∈ List.Ico 1 (stageWidth r + 1))
    (hm0 : truncatedBlockStart (stageCutoff r) (stageHeight r) d ≤ m)
    (hm1 : m + 1 < blockStop (stageHeight r) d)
    (hz : z ∈ sharpSet) :
    ¬(d * m < z ∧ z < d * (m + 1)) := by
  intro hazb
  obtain ⟨t, hzt⟩ := hz
  have habStage := internal_pair_mem_sharpStage hd hm0 hm1
  rcases lt_trichotomy t r with htr | htreq | hrt
  · have hza : z < d * m := lt_of_mem_sharpStages htr hzt habStage.1
    omega
  · subst t
    rw [sharpStage, truncatedStage] at hzt
    obtain ⟨e, he, hze⟩ := List.mem_flatMap.mp hzt
    rcases lt_trichotomy e d with hed | heq | hde
    · have hza : z < d * m :=
        lt_of_mem_blocks (List.Ico.mem.mp he).1 hed
          (mem_block_of_mem_truncatedBlock hze)
          (mem_block_of_mem_truncatedBlock
            (mem_truncatedBlock.mpr ⟨m, hm0, by omega, rfl⟩))
      omega
    · subst e
      obtain ⟨n, _, _, hzn⟩ := mem_truncatedBlock.mp hze
      rw [hzn] at hazb
      have hdpos : 0 < d := (List.Ico.mem.mp hd).1
      have hmn : m < n := (Nat.mul_lt_mul_left hdpos).mp hazb.1
      have hnm : n < m + 1 := (Nat.mul_lt_mul_left hdpos).mp hazb.2
      omega
    · have hbz : d * (m + 1) < z :=
        lt_of_mem_blocks (List.Ico.mem.mp hd).1 hde
          (mem_block_of_mem_truncatedBlock
            (mem_truncatedBlock.mpr ⟨m + 1, hm0.trans (Nat.le_succ _), hm1, rfl⟩))
          (mem_block_of_mem_truncatedBlock hze)
      omega
  · have hbz : d * (m + 1) < z :=
      lt_of_mem_sharpStages hrt habStage.2 hzt
    omega

/-- Every internal block edge appears at two consecutive indices of the
increasing enumeration `sharpSequence`. -/
theorem exists_sharpSequence_consecutive_internal {r d m : ℕ}
    (hd : d ∈ List.Ico 1 (stageWidth r + 1))
    (hm0 : truncatedBlockStart (stageCutoff r) (stageHeight r) d ≤ m)
    (hm1 : m + 1 < blockStop (stageHeight r) d) :
    ∃ i, sharpSequence i = d * m ∧ sharpSequence (i + 1) = d * (m + 1) := by
  have habStage := internal_pair_mem_sharpStage hd hm0 hm1
  have haSet : d * m ∈ sharpSet := ⟨r, habStage.1⟩
  have hbSet : d * (m + 1) ∈ sharpSet := ⟨r, habStage.2⟩
  obtain ⟨i, hi⟩ : ∃ i, sharpSequence i = d * m := by
    have hinf : {x : ℕ | x ∈ sharpSet}.Infinite := by
      simpa only [Set.ofPred_mem_eq] using sharpSet_infinite
    have harange : d * m ∈ Set.range (Nat.nth (· ∈ sharpSet)) := by
      rw [Nat.range_nth_of_infinite hinf]
      exact haSet
    obtain ⟨i, hi⟩ := harange
    exact ⟨i, by simpa [sharpSequence] using hi⟩
  obtain ⟨j, hj⟩ : ∃ j, sharpSequence j = d * (m + 1) := by
    have hinf : {x : ℕ | x ∈ sharpSet}.Infinite := by
      simpa only [Set.ofPred_mem_eq] using sharpSet_infinite
    have hbrange : d * (m + 1) ∈ Set.range (Nat.nth (· ∈ sharpSet)) := by
      rw [Nat.range_nth_of_infinite hinf]
      exact hbSet
    obtain ⟨j, hj⟩ := hbrange
    exact ⟨j, by simpa [sharpSequence] using hj⟩
  have hdpos : 0 < d := (List.Ico.mem.mp hd).1
  have hab : d * m < d * (m + 1) :=
    (Nat.mul_lt_mul_left hdpos).2 (Nat.lt_succ_self m)
  have hij : i < j := by
    rw [← sharpSequence_strictMono.lt_iff_lt, hi, hj]
    exact hab
  have hnextMem : sharpSequence (i + 1) ∈ sharpSet :=
    Nat.nth_mem_of_infinite sharpSet_infinite (i + 1)
  have haNext : d * m < sharpSequence (i + 1) := by
    rw [← hi]
    exact sharpSequence_strictMono (Nat.lt_succ_self i)
  have hbNext : d * (m + 1) ≤ sharpSequence (i + 1) := by
    by_contra h
    have hnextb : sharpSequence (i + 1) < d * (m + 1) := Nat.lt_of_not_ge h
    exact no_sharpSet_between_internal hd hm0 hm1 hnextMem ⟨haNext, hnextb⟩
  have hNextb : sharpSequence (i + 1) ≤ d * (m + 1) := by
    rw [← hj]
    exact sharpSequence_strictMono.monotone (Nat.succ_le_iff.mpr hij)
  exact ⟨i, hi, le_antisymm hNextb hbNext⟩

/-! ## A finite injective family of good indices at every stage height -/

/-- All internal multiplier pairs in stage `r`, represented by their block
parameter and their first multiplier. -/
def stageEdgePairs (r : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Ico 1 (stageWidth r + 1)).product
      (Finset.range (stageScale r ^ 2))).filter fun p ↦
    truncatedBlockStart (stageCutoff r) (stageHeight r) p.1 ≤ p.2 ∧
      p.2 + 1 < blockStop (stageHeight r) p.1

/-- The multiplier cutoff of every stage block is below the common square
scale. -/
theorem blockStop_stage_le_scale_sq (r d : ℕ) :
    blockStop (stageHeight r) d ≤ stageScale r ^ 2 := by
  rw [blockStop, ← sqrt_stageHeight r]
  exact Nat.sqrt_le_sqrt (Nat.div_le_self _ _)

@[simp] theorem mem_stageEdgePairs {r d m : ℕ} :
    (d, m) ∈ stageEdgePairs r ↔
      d ∈ Finset.Ico 1 (stageWidth r + 1) ∧
      m < stageScale r ^ 2 ∧
      truncatedBlockStart (stageCutoff r) (stageHeight r) d ≤ m ∧
      m + 1 < blockStop (stageHeight r) d := by
  simp [stageEdgePairs, and_assoc, and_left_comm, and_comm]

/-- Each encoded internal multiplier pair produces consecutive terms of the
infinite sequence. -/
theorem exists_consecutive_of_mem_stageEdgePairs {r d m : ℕ}
    (h : (d, m) ∈ stageEdgePairs r) :
    ∃ i, sharpSequence i = d * m ∧ sharpSequence (i + 1) = d * (m + 1) := by
  rw [mem_stageEdgePairs] at h
  exact exists_sharpSequence_consecutive_internal
    (by simpa using h.1) h.2.2.1 h.2.2.2

/-- Chosen index of an internal edge. -/
noncomputable def stageEdgeIndex (r : ℕ) (p : {p // p ∈ stageEdgePairs r}) : ℕ :=
  (exists_consecutive_of_mem_stageEdgePairs p.2).choose

theorem stageEdgeIndex_spec (r : ℕ) (p : {p // p ∈ stageEdgePairs r}) :
    sharpSequence (stageEdgeIndex r p) = p.1.1 * p.1.2 ∧
      sharpSequence (stageEdgeIndex r p + 1) = p.1.1 * (p.1.2 + 1) :=
  (exists_consecutive_of_mem_stageEdgePairs p.2).choose_spec

/-- Different internal multiplier pairs have different first terms. -/
theorem stageEdgePair_start_injective (r : ℕ) :
    Function.Injective (fun p : {p // p ∈ stageEdgePairs r} ↦ p.1.1 * p.1.2) := by
  intro p q hpq
  rcases p with ⟨⟨d, m⟩, hp⟩
  rcases q with ⟨⟨e, n⟩, hq⟩
  simp only at hpq ⊢
  rw [mem_stageEdgePairs] at hp hq
  have hdpos : 0 < d := (Finset.mem_Ico.mp hp.1).1
  have hepos : 0 < e := (Finset.mem_Ico.mp hq.1).1
  rcases lt_trichotomy d e with hde | hde | hed
  · have hlt : d * m < e * n :=
      lt_of_mem_blocks hdpos hde
        (mem_block_of_mem_truncatedBlock
          (mem_truncatedBlock.mpr ⟨m, hp.2.2.1, by omega, rfl⟩))
        (mem_block_of_mem_truncatedBlock
          (mem_truncatedBlock.mpr ⟨n, hq.2.2.1, by omega, rfl⟩))
    omega
  · subst e
    have hm : m = n := Nat.eq_of_mul_eq_mul_left hdpos hpq
    subst n
    rfl
  · have hlt : e * n < d * m :=
      lt_of_mem_blocks hepos hed
        (mem_block_of_mem_truncatedBlock
          (mem_truncatedBlock.mpr ⟨n, hq.2.2.1, by omega, rfl⟩))
        (mem_block_of_mem_truncatedBlock
          (mem_truncatedBlock.mpr ⟨m, hp.2.2.1, by omega, rfl⟩))
    omega

/-- Chosen internal edges have distinct indices. -/
theorem stageEdgeIndex_injective (r : ℕ) : Function.Injective (stageEdgeIndex r) := by
  intro p q hpq
  apply stageEdgePair_start_injective r
  exact (stageEdgeIndex_spec r p).1.symm.trans <|
    (congrArg sharpSequence hpq).trans (stageEdgeIndex_spec r q).1

/-- The exact finite version of the original counting function for the
concrete sharpness sequence. -/
noncomputable def sharpGoodIndices (X : ℕ) : Finset ℕ :=
  (Finset.range X).filter fun i ↦
    Nat.lcm (sharpSequence i) (sharpSequence (i + 1)) ≤ X

/-- The `i`-th entry of any positive strictly increasing natural sequence is
at least `i+1`. -/
theorem index_add_one_le_sharpSequence (i : ℕ) : i + 1 ≤ sharpSequence i := by
  induction i with
  | zero => exact Nat.succ_le_iff.mpr (sharpSequence_pos 0)
  | succ i ih =>
      have hs := sharpSequence_strictMono (Nat.lt_succ_self i)
      have h := ih.trans_lt hs
      simpa [Nat.succ_eq_add_one] using Nat.succ_le_of_lt h

/-- A good edge index is automatically below its height cutoff. -/
theorem index_lt_of_sharp_lcm_le {i X : ℕ}
    (hi : Nat.lcm (sharpSequence i) (sharpSequence (i + 1)) ≤ X) : i < X := by
  have hright : sharpSequence (i + 1) ≤
      Nat.lcm (sharpSequence i) (sharpSequence (i + 1)) := by
    apply Nat.le_of_dvd
    · exact Nat.lcm_pos (sharpSequence_pos i) (sharpSequence_pos (i + 1))
    · exact Nat.dvd_lcm_right _ _
  have hindex : i + 2 ≤ sharpSequence (i + 1) := by
    simpa [Nat.add_assoc] using index_add_one_le_sharpSequence (i + 1)
  omega

@[simp] theorem mem_sharpGoodIndices {i X : ℕ} :
    i ∈ sharpGoodIndices X ↔
      Nat.lcm (sharpSequence i) (sharpSequence (i + 1)) ≤ X := by
  rw [sharpGoodIndices, Finset.mem_filter]
  constructor
  · exact fun h ↦ h.2
  · exact fun h ↦ ⟨Finset.mem_range.mpr (index_lt_of_sharp_lcm_le h), h⟩

/-- Every encoded internal edge at stage `r` is counted at height
`stageHeight r`. -/
theorem stageEdgeIndex_mem_good (r : ℕ) (p : {p // p ∈ stageEdgePairs r}) :
    stageEdgeIndex r p ∈ sharpGoodIndices (stageHeight r) := by
  rw [mem_sharpGoodIndices, (stageEdgeIndex_spec r p).1, (stageEdgeIndex_spec r p).2]
  exact lcm_consecutive_multiples_le (by
    rw [blockStop]
    have hp := p.2
    rw [mem_stageEdgePairs] at hp
    exact Nat.le_of_lt hp.2.2.2)

/-- The actual counting function at a stage height dominates the number of
all internal edges in that stage. -/
theorem card_stageEdgePairs_le_countingFunction (r : ℕ) :
    (stageEdgePairs r).card ≤ (sharpGoodIndices (stageHeight r)).card := by
  rw [← Finset.card_attach]
  exact Finset.card_le_card_of_injOn (f := stageEdgeIndex r)
    (fun p _ ↦ stageEdgeIndex_mem_good r p)
    (fun _ _ _ _ h ↦ stageEdgeIndex_injective r h)

/-- Sigma-type presentation of the same internal edges, convenient for
computing their cardinality as a sum of block contributions. -/
def stageEdgeData (r : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.Ico 1 (stageWidth r + 1)).sigma fun d ↦
    Finset.Ico (truncatedBlockStart (stageCutoff r) (stageHeight r) d)
      (blockStop (stageHeight r) d - 1)

/-- Mapping sigma data to ordinary pairs identifies `stageEdgeData` with
`stageEdgePairs`. -/
theorem image_stageEdgeData (r : ℕ) :
    (stageEdgeData r).image (fun p ↦ (p.1, p.2)) = stageEdgePairs r := by
  ext p
  rcases p with ⟨d, m⟩
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨p, hp, hpval⟩
    rcases p with ⟨e, n⟩
    simp only [Prod.mk.injEq] at hpval
    rcases hpval with ⟨rfl, rfl⟩
    simp only [stageEdgeData, Finset.mem_sigma, Finset.mem_Ico] at hp
    rw [mem_stageEdgePairs]
    refine ⟨Finset.mem_Ico.mpr hp.1, ?_, hp.2.1, ?_⟩
    · exact (hp.2.2.trans_le (Nat.sub_le _ _)).trans_le
        (blockStop_stage_le_scale_sq r e)
    · omega
  · intro hp
    rw [mem_stageEdgePairs] at hp
    refine ⟨⟨d, m⟩, ?_, rfl⟩
    simp only [stageEdgeData, Finset.mem_sigma, Finset.mem_Ico]
    refine ⟨Finset.mem_Ico.mp hp.1, hp.2.2.1, ?_⟩
    omega

/-- Exact sum formula for the number of encoded internal edges. -/
theorem card_stageEdgePairs (r : ℕ) :
    (stageEdgePairs r).card =
      ∑ d ∈ Finset.Ico 1 (stageWidth r + 1),
        ((truncatedBlock (stageCutoff r) (stageHeight r) d).length - 1) := by
  rw [← image_stageEdgeData r]
  rw [Finset.card_image_of_injective]
  · rw [stageEdgeData, Finset.card_sigma]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Nat.card_Ico, length_truncatedBlock]
    omega
  · intro p q hpq
    rcases p with ⟨d, m⟩
    rcases q with ⟨e, n⟩
    simp only [Prod.mk.injEq] at hpq
    rcases hpq with ⟨rfl, rfl⟩
    rfl

/-! ## Quantitative lower estimate for a stage -/

/-- Taking a natural quotient and then a natural square root loses less than
two compared with taking the corresponding real square root. -/
theorem real_sqrt_div_lt_nat_sqrt_div_add_two {X d : ℕ} (hd : 0 < d) :
    Real.sqrt ((X : ℝ) / d) < (Nat.sqrt (X / d) : ℝ) + 2 := by
  have hfloor : ((X / d : ℕ) : ℝ) ≤ (X : ℝ) / d := by
    exact Nat.cast_div_le
  have hceil : (X : ℝ) / d < ((X / d : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ (by exact_mod_cast hd)]
    norm_cast
    exact (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self (X / d))
  have hsqrt : Real.sqrt ((X : ℝ) / d) <
      Real.sqrt ((X / d : ℕ) : ℝ) + 1 := by
    rw [Real.sqrt_lt (by positivity) (by positivity)]
    have hs := Real.sq_sqrt (show 0 ≤ ((X / d : ℕ) : ℝ) by positivity)
    nlinarith [Real.sqrt_nonneg ((X / d : ℕ) : ℝ)]
  have hnat := Real.real_sqrt_lt_nat_sqrt_succ (a := X / d)
  linarith

/-- Lower real estimate for the common upper multiplier cutoff at a stage. -/
theorem blockStop_stage_lower {r d : ℕ} (hd : 0 < d) :
    (stageScale r ^ 2 : ℝ) / Real.sqrt d - 2 <
      (blockStop (stageHeight r) d : ℝ) := by
  have h := real_sqrt_div_lt_nat_sqrt_div_add_two
    (X := stageHeight r) hd
  have hsqrt : Real.sqrt ((stageHeight r : ℝ) / d) =
      (stageScale r ^ 2 : ℝ) / Real.sqrt d := by
    rw [Real.sqrt_div (by positivity)]
    congr 1
    rw [stageHeight]
    push_cast
    rw [show (stageScale r : ℝ) ^ 4 = ((stageScale r : ℝ) ^ 2) ^ 2 by ring]
    rw [Real.sqrt_sq (by positivity)]
  change Real.sqrt ((stageHeight r : ℝ) / d) <
      (blockStop (stageHeight r) d : ℝ) + 2 at h
  rw [hsqrt] at h
  linarith

/-- The untruncated lower endpoint has the expected real upper estimate. -/
theorem blockStart_stage_upper {r d : ℕ} (hd : 0 < d) :
    (blockStart (stageHeight r) d : ℝ) ≤
      (stageScale r ^ 2 : ℝ) * Real.sqrt (d - 1) / d + 1 := by
  have hsqrtNat : (Nat.sqrt ((d - 1) * stageHeight r) : ℝ) ≤
      Real.sqrt (((d - 1) * stageHeight r : ℕ) : ℝ) :=
    Real.nat_sqrt_le_real_sqrt
  have hdiv : ((Nat.sqrt ((d - 1) * stageHeight r) / d : ℕ) : ℝ) ≤
      (Nat.sqrt ((d - 1) * stageHeight r) : ℝ) / d := Nat.cast_div_le
  have hsqrt : Real.sqrt (((d - 1) * stageHeight r : ℕ) : ℝ) =
      (stageScale r ^ 2 : ℝ) * Real.sqrt (d - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (Nat.succ_le_iff.mpr hd)]
    simp only [Nat.cast_one]
    have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast (Nat.succ_le_iff.mpr hd)
    rw [Real.sqrt_mul (sub_nonneg.mpr hdreal)]
    rw [stageHeight]
    push_cast
    rw [show (stageScale r : ℝ) ^ 4 = ((stageScale r : ℝ) ^ 2) ^ 2 by ring]
    rw [Real.sqrt_sq (by positivity)]
    ring
  rw [blockStart, Nat.cast_add, Nat.cast_one]
  calc
    ((Nat.sqrt ((d - 1) * stageHeight r) / d : ℕ) : ℝ) + 1 ≤
        (Nat.sqrt ((d - 1) * stageHeight r) : ℝ) / d + 1 := by gcongr
    _ ≤ Real.sqrt (((d - 1) * stageHeight r : ℕ) : ℝ) / d + 1 := by gcongr
    _ = (stageScale r ^ 2 : ℝ) * Real.sqrt (d - 1) / d + 1 := by rw [hsqrt]

/-- Truncation raises a block start by at most `cutoff+1`. -/
theorem truncatedBlockStart_stage_upper {r d : ℕ} (hd : 0 < d) :
    (truncatedBlockStart (stageCutoff r) (stageHeight r) d : ℝ) ≤
      (stageScale r ^ 2 : ℝ) * Real.sqrt (d - 1) / d +
        (stageCutoff r : ℝ) + 2 := by
  rw [truncatedBlockStart, Nat.cast_max]
  apply max_le
  · have hc : (0 : ℝ) ≤ stageCutoff r := by positivity
    exact (blockStart_stage_upper hd).trans (by
      have hs : 0 ≤ (stageScale r ^ 2 : ℝ) * Real.sqrt (d - 1) / d := by positivity
      linarith)
  · have hdiv : ((stageCutoff r / d : ℕ) : ℝ) ≤
        (stageCutoff r : ℝ) / d := Nat.cast_div_le
    have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have : (stageCutoff r : ℝ) / d ≤ stageCutoff r := by
      exact div_le_self (by positivity) hdreal
    rw [Nat.cast_add, Nat.cast_one]
    have hs : 0 ≤ (stageScale r ^ 2 : ℝ) * Real.sqrt (d - 1) / d := by positivity
    linarith

/-- Casting natural truncated subtraction to the reals is at least real
subtraction. -/
theorem sub_le_natCast_tsub (a b : ℕ) :
    (a : ℝ) - b ≤ (a - b : ℕ) := by
  by_cases hba : b ≤ a
  · rw [Nat.cast_sub hba]
  · have hab : a ≤ b := Nat.le_of_not_ge hba
    rw [Nat.sub_eq_zero_of_le hab, Nat.cast_zero]
    exact sub_nonpos.mpr (by exact_mod_cast hab)

/-- Limiting normalized contribution of the block with gap `d`. -/
noncomputable def blockCoefficient (d : ℕ) : ℝ :=
  1 / Real.sqrt d - Real.sqrt (d - 1) / d

/-- Quantitative lower bound for the number of internal edges in one
truncated stage block. -/
theorem stageBlockEdges_lower {r d : ℕ} (hd : 0 < d) :
    (stageScale r ^ 2 : ℝ) * blockCoefficient d - stageCutoff r - 5 ≤
      ((truncatedBlock (stageCutoff r) (stageHeight r) d).length - 1 : ℕ) := by
  have hstop := (blockStop_stage_lower (r := r) hd).le
  have hstart := truncatedBlockStart_stage_upper (r := r) hd
  have hlenCast := sub_le_natCast_tsub
    (blockStop (stageHeight r) d)
    (truncatedBlockStart (stageCutoff r) (stageHeight r) d)
  have hedgeCast := sub_le_natCast_tsub
    (truncatedBlock (stageCutoff r) (stageHeight r) d).length 1
  rw [← length_truncatedBlock] at hlenCast
  rw [blockCoefficient]
  have hsqrtPos : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hrewrite : (stageScale r ^ 2 : ℝ) / Real.sqrt d =
      (stageScale r ^ 2 : ℝ) * (1 / Real.sqrt d) := by field_simp
  rw [hrewrite] at hstop
  ring_nf at hstop hstart hlenCast hedgeCast ⊢
  linarith

/-- Partial sum of block coefficients used at stage `r`. -/
noncomputable def stageCoefficientSum (r : ℕ) : ℝ :=
  ∑ d ∈ Finset.Ico 1 (stageWidth r + 1), blockCoefficient d

/-- The annular coefficient is the difference-of-square-roots summand used
in the analytic evaluation of the sharp constant. -/
theorem blockCoefficient_succ (n : ℕ) :
    blockCoefficient (n + 1) =
      (Real.sqrt (n + 1 : ℝ) - Real.sqrt n) / (n + 1 : ℝ) := by
  unfold blockCoefficient
  norm_num only [Nat.cast_add, Nat.cast_one]
  ring_nf
  have hspos : 0 < Real.sqrt (1 + (n : ℝ)) := by positivity
  have hsquare : Real.sqrt (1 + (n : ℝ)) ^ 2 = 1 + (n : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hrecip : 1 / Real.sqrt (1 + (n : ℝ)) =
      Real.sqrt (1 + (n : ℝ)) / (1 + (n : ℝ)) := by
    field_simp
    nlinarith
  have hrecip' : (Real.sqrt (1 + (n : ℝ)))⁻¹ =
      Real.sqrt (1 + (n : ℝ)) * (1 + (n : ℝ))⁻¹ := by
    simpa only [div_eq_mul_inv, one_mul] using hrecip
  rw [hrecip']

/-- Reindexing identifies the sum of the first `N` annular coefficients with
the partial sum whose convergence is proved in `Erdos440.Constant`. -/
theorem sum_blockCoefficient_Ico (N : ℕ) :
    (∑ d ∈ Finset.Ico 1 (N + 1), blockCoefficient d) =
      Erdos440Constant.incrementPartialSum N := by
  induction N with
  | zero => simp [Erdos440Constant.incrementPartialSum]
  | succ N ih =>
      rw [Finset.sum_Ico_succ_top (by omega), ih]
      calc
        Erdos440Constant.incrementPartialSum N + blockCoefficient (N + 1) =
            Erdos440Constant.incrementPartialSum N +
              (Real.sqrt (N + 1 : ℝ) - Real.sqrt N) / (N + 1 : ℝ) := by
                rw [blockCoefficient_succ]
        _ = Erdos440Constant.incrementPartialSum (N + 1) := by
          simp only [Erdos440Constant.incrementPartialSum, Finset.sum_range_succ]

/-- The stage coefficient is exactly the first `stageWidth r` terms of the
sharp coefficient series. -/
theorem stageCoefficientSum_eq_incrementPartialSum (r : ℕ) :
    stageCoefficientSum r =
      Erdos440Constant.incrementPartialSum (stageWidth r) := by
  exact sum_blockCoefficient_Ico (stageWidth r)

/-- The analytic constant module and the universal upper-bound module use the
same sharp constant (with shifted and unshifted indexing, respectively). -/
theorem analyticSharpConstant_eq_universalSharpConstant :
    Erdos440Constant.sharpConstant =
      Erdos440SharpUpper.IncreasingSequence.sharpConstant := by
  rw [Erdos440Constant.sharpConstant_eq_unshifted_tsum]
  unfold Erdos440SharpUpper.IncreasingSequence.sharpConstant
  apply tsum_congr
  intro d
  rfl

/-- Quantitative lower bound for all encoded good edges at a stage. -/
theorem stageEdgePairs_lower (r : ℕ) :
    (stageScale r ^ 2 : ℝ) * stageCoefficientSum r -
        stageWidth r * ((stageCutoff r : ℝ) + 5) ≤
      (stageEdgePairs r).card := by
  let D := Finset.Ico 1 (stageWidth r + 1)
  have hsum :
      ∑ d ∈ D,
          ((stageScale r ^ 2 : ℝ) * blockCoefficient d - stageCutoff r - 5) ≤
        ∑ d ∈ D,
          (((truncatedBlock (stageCutoff r) (stageHeight r) d).length - 1 : ℕ) : ℝ) := by
    apply Finset.sum_le_sum
    intro d hdD
    exact stageBlockEdges_lower (Finset.mem_Ico.mp hdD).1
  calc
    (stageScale r ^ 2 : ℝ) * stageCoefficientSum r -
          stageWidth r * ((stageCutoff r : ℝ) + 5) =
        ∑ d ∈ D,
          ((stageScale r ^ 2 : ℝ) * blockCoefficient d - stageCutoff r - 5) := by
            rw [stageCoefficientSum]
            change _ = ∑ d ∈ Finset.Ico 1 (stageWidth r + 1), _
            rw [Finset.mul_sum]
            simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
              Nat.card_Ico]
            push_cast
            ring
    _ ≤ ∑ d ∈ D,
          (((truncatedBlock (stageCutoff r) (stageHeight r) d).length - 1 : ℕ) : ℝ) := hsum
    _ = (stageEdgePairs r).card := by
      rw [card_stageEdgePairs]
      push_cast
      rfl

/-- Relative rounding and truncation error in the stage lower bound. -/
noncomputable def stageError (r : ℕ) : ℝ :=
  stageWidth r * ((stageCutoff r : ℝ) + 5) / (stageScale r ^ 2 : ℝ)

theorem stageError_nonneg (r : ℕ) : 0 ≤ stageError r := by
  unfold stageError
  positivity

/-- The deliberately enlarged scale makes the whole-stage error at most
`5/(r+2)`. -/
theorem stageError_le (r : ℕ) : stageError r ≤ 5 / (r + 2 : ℝ) := by
  have hq : 0 < (stageScale r ^ 2 : ℝ) := by
    have : 0 < stageScale r := by simp [stageScale]
    positivity
  have hr : 0 < (r + 2 : ℝ) := by positivity
  rw [stageError, div_le_div_iff₀ hq hr]
  have hw : (stageWidth r : ℝ) ≤ r + 2 := by
    rw [stageWidth]
    push_cast
    linarith
  have hc : (stageCutoff r : ℝ) + 5 ≤ 5 * (stageCutoff r + 1) := by
    have hc0 : (0 : ℝ) ≤ stageCutoff r := by positivity
    linarith
  have hone : (1 : ℝ) ≤ stageCutoff r + 1 := by
    have hc0 : (0 : ℝ) ≤ stageCutoff r := by positivity
    linarith
  rw [stageScale]
  push_cast
  calc
    (stageWidth r : ℝ) * ((stageCutoff r : ℝ) + 5) * ((r : ℝ) + 2) ≤
        ((r : ℝ) + 2) * ((5 : ℝ) * ((stageCutoff r : ℝ) + 1)) *
          ((r : ℝ) + 2) := by
          gcongr
    _ ≤ (5 : ℝ) * ((((stageCutoff r : ℝ) + 1) * ((r : ℝ) + 2)) ^ 2) := by
      have hrr : 0 ≤ ((r : ℝ) + 2) ^ 2 := sq_nonneg _
      nlinarith

/-! ## Passage from the quantitative stage bound to sharpness -/

/-- The coefficient sums along the concrete stages converge to the analytic
sharp constant. -/
theorem stageCoefficientSum_tendsto :
    Tendsto stageCoefficientSum atTop
      (nhds Erdos440Constant.sharpConstant) := by
  have h := Erdos440Constant.incrementPartialSum_tendsto.comp
    (tendsto_add_atTop_nat 1)
  refine h.congr' (Eventually.of_forall fun r ↦ ?_)
  exact (stageCoefficientSum_eq_incrementPartialSum r).symm

/-- The relative error in the concrete stages tends to zero. -/
theorem stageError_tendsto : Tendsto stageError atTop (nhds 0) := by
  apply squeeze_zero' (g := fun r : ℕ ↦ 5 / (r + 2 : ℝ))
  · exact Eventually.of_forall stageError_nonneg
  · exact Eventually.of_forall stageError_le
  · have h := (tendsto_const_div_atTop_nhds_zero_nat (5 : ℝ)).comp
        (tendsto_add_atTop_nat 2)
    refine h.congr' (Eventually.of_forall fun r ↦ ?_)
    norm_num only [Function.comp_apply, Nat.cast_add, Nat.cast_ofNat]

/-- The normalized quantitative lower bounds converge to the sharp constant. -/
theorem stageLowerBound_tendsto :
    Tendsto (fun r ↦ stageCoefficientSum r - stageError r) atTop
      (nhds Erdos440Constant.sharpConstant) := by
  simpa only [sub_zero] using stageCoefficientSum_tendsto.sub stageError_tendsto

/-- Real square root of the chosen perfect fourth-power height. -/
theorem real_sqrt_stageHeight (r : ℕ) :
    Real.sqrt (stageHeight r : ℝ) = (stageScale r ^ 2 : ℕ) := by
  rw [stageHeight]
  push_cast
  rw [show (stageScale r : ℝ) ^ 4 = ((stageScale r : ℝ) ^ 2) ^ 2 by ring]
  exact Real.sqrt_sq (sq_nonneg _)

/-- Every stage height dominates its stage index. -/
theorem le_stageHeight (r : ℕ) : r ≤ stageHeight r := by
  have hscale : r + 2 ≤ stageScale r := by
    rw [stageScale]
    nlinarith [Nat.zero_le (stageCutoff r)]
  have hscalePos : 0 < stageScale r := by omega
  have hsqPos : 0 < stageScale r ^ 2 := pow_pos hscalePos 2
  have hs_le_sq : stageScale r ≤ stageScale r ^ 2 := by
    rw [pow_two]
    exact Nat.le_mul_of_pos_right _ hscalePos
  have hsq_le_fourth : stageScale r ^ 2 ≤ stageScale r ^ 4 := by
    calc
      stageScale r ^ 2 ≤ (stageScale r ^ 2) * (stageScale r ^ 2) :=
        Nat.le_mul_of_pos_right _ hsqPos
      _ = stageScale r ^ 4 := by ring
  exact (by omega : r ≤ stageScale r) |>.trans (hs_le_sq.trans hsq_le_fourth)

/-- The selected heights form a cofinal sequence. -/
theorem stageHeight_tendsto : Tendsto stageHeight atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro N
  exact ⟨N, fun r hr ↦ hr.trans (le_stageHeight r)⟩

/-- The concrete increasing sequence, packaged in the format used by the
universal upper-bound development. -/
noncomputable def sharpIncreasingSequence :
    Erdos440SharpUpper.IncreasingSequence where
  val := sharpSequence
  positive := sharpSequence_pos
  strictMono := sharpSequence_strictMono

@[simp] theorem sharpIncreasingSequence_val (i : ℕ) :
    sharpIncreasingSequence.val i = sharpSequence i := rfl

/-- Our directly defined finite good-index set agrees definitionally with
the counting-function API used in the upper-bound file. -/
theorem sharpGoodIndices_eq_goodIndices (X : ℕ) :
    sharpGoodIndices X = sharpIncreasingSequence.goodIndices X := rfl

/-- Normalized counting function of the concrete sharp sequence. -/
noncomputable def sharpNormalizedCount (X : ℕ) : ℝ :=
  (sharpIncreasingSequence.countingFunction X : ℝ) / Real.sqrt X

theorem sharpNormalizedCount_nonneg (X : ℕ) : 0 ≤ sharpNormalizedCount X := by
  unfold sharpNormalizedCount
  positivity

/-- At every selected height, the normalized counting function dominates
the convergent stage lower bound. -/
theorem stageLowerBound_le_normalizedCount (r : ℕ) :
    stageCoefficientSum r - stageError r ≤
      sharpNormalizedCount (stageHeight r) := by
  have hscale : 0 < (stageScale r ^ 2 : ℝ) := by
    have : 0 < stageScale r := by simp [stageScale]
    positivity
  have hpairs := stageEdgePairs_lower r
  have hcardNat := card_stageEdgePairs_le_countingFunction r
  have hcard : ((stageEdgePairs r).card : ℝ) ≤
      ((sharpGoodIndices (stageHeight r)).card : ℝ) := by
    exact_mod_cast hcardNat
  have hraw :
      (stageScale r ^ 2 : ℝ) * stageCoefficientSum r -
          stageWidth r * ((stageCutoff r : ℝ) + 5) ≤
        ((sharpGoodIndices (stageHeight r)).card : ℝ) :=
    hpairs.trans hcard
  unfold sharpNormalizedCount Erdos440SharpUpper.IncreasingSequence.countingFunction
  rw [← sharpGoodIndices_eq_goodIndices, real_sqrt_stageHeight]
  norm_num only [Nat.cast_pow]
  rw [le_div_iff₀ hscale]
  calc
    (stageCoefficientSum r - stageError r) * (stageScale r ^ 2 : ℝ) =
        (stageScale r ^ 2 : ℝ) * stageCoefficientSum r -
          stageWidth r * ((stageCutoff r : ℝ) + 5) := by
            rw [stageError]
            have hbase : (stageScale r : ℝ) ≠ 0 := by
              intro hzero
              rw [hzero] at hscale
              norm_num at hscale
            field_simp [hbase]
    _ ≤ ((sharpGoodIndices (stageHeight r)).card : ℝ) := hraw

/-- Epsilon form of sharpness along the selected cofinal stages.  This is
often the most convenient interface for downstream limsup proofs. -/
theorem eventually_stage_normalizedCount_gt
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop,
      Erdos440SharpUpper.IncreasingSequence.sharpConstant - ε <
        sharpNormalizedCount (stageHeight r) := by
  have hevent : ∀ᶠ r : ℕ in atTop,
      Erdos440Constant.sharpConstant - ε <
        stageCoefficientSum r - stageError r :=
    (tendsto_order.1 stageLowerBound_tendsto).1 _ (sub_lt_self _ hε)
  filter_upwards [hevent] with r hr
  rw [← analyticSharpConstant_eq_universalSharpConstant]
  exact hr.trans_le (stageLowerBound_le_normalizedCount r)

/-- The sharp lower values occur frequently in the original height variable,
not merely after reindexing by the stages. -/
theorem frequently_sharpNormalizedCount_gt
    {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ X : ℕ in atTop,
      Erdos440SharpUpper.IncreasingSequence.sharpConstant - ε <
        sharpNormalizedCount X := by
  rw [frequently_atTop]
  intro N
  have hN : ∀ᶠ r : ℕ in atTop, N ≤ stageHeight r :=
    stageHeight_tendsto.eventually (eventually_ge_atTop N)
  obtain ⟨r, hrsharp, hrN⟩ :=
    ((eventually_stage_normalizedCount_gt hε).and hN).exists
  exact ⟨stageHeight r, hrN, hrsharp⟩

/-- The limsup of the normalized counting function for the concrete sequence
is at least the sharp constant. -/
theorem universalSharpConstant_le_limsup_sharpNormalizedCount :
    Erdos440SharpUpper.IncreasingSequence.sharpConstant ≤
      limsup sharpNormalizedCount atTop := by
  have hbdd : IsBoundedUnder (· ≤ ·) atTop sharpNormalizedCount := by
    apply isBoundedUnder_of_eventually_le
    simpa only [sharpNormalizedCount] using
      sharpIncreasingSequence.eventually_countingFunction_div_sqrt_le 1 zero_lt_one
  have hcob : IsCoboundedUnder (· ≤ ·) atTop sharpNormalizedCount :=
    isCoboundedUnder_le_of_le atTop sharpNormalizedCount_nonneg
  rw [le_limsup_iff hcob hbdd]
  intro y hy
  have hε : 0 < Erdos440SharpUpper.IncreasingSequence.sharpConstant - y := sub_pos.mpr hy
  simpa only [sub_sub_cancel] using frequently_sharpNormalizedCount_gt hε

end Erdos440SharpConstruction
