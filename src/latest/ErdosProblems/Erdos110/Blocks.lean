/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos110.Specker

/-!
# Finite blocks used in the Lambie--Hanson graph

This file packages the finite concatenation bookkeeping.  For a requested
scale `q k`, block `k` uses the Specker parameter `q k + 1` and the generous
width from `Specker.width`.  `realizeBlocks` is the exact simultaneous
finite-type consequence of `Height.realizeRanks` used to create an edge.
-/

noncomputable section

open Cardinal Set

namespace Erdos110
namespace Blocks

open Height

/-- Specker parameter at scale `k`. -/
def scale (q : ℕ → ℕ) (k : ℕ) : ℕ := q k + 1

/-- Width of block `k`. -/
def blockWidth (q : ℕ → ℕ) (k : ℕ) : ℕ :=
  Specker.width (scale q k)

/-- First ladder coordinate belonging to block `k`. -/
def blockStart (q : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => blockStart q k + blockWidth q k

@[simp] theorem blockStart_zero (q : ℕ → ℕ) : blockStart q 0 = 0 := rfl

@[simp] theorem blockStart_succ (q : ℕ → ℕ) (k : ℕ) :
    blockStart q (k + 1) = blockStart q k + blockWidth q k := rfl

theorem blockWidth_pos (q : ℕ → ℕ) (k : ℕ) : 0 < blockWidth q k := by
  simp [blockWidth, Specker.width]

theorem blockStart_strictMono (q : ℕ → ℕ) : StrictMono (blockStart q) := by
  apply strictMono_nat_of_lt_succ
  intro k
  simp only [blockStart_succ]
  exact Nat.lt_add_of_pos_right (blockWidth_pos q k)

/-- Ranks for one block, shifted past all preceding blocks. -/
def rankBlock (q : ℕ → ℕ) (k : ℕ) : List ℕ :=
  List.ofFn fun i : Fin (blockWidth q k) ↦
    blockStart q k + (i.1 - scale q k)

@[simp] theorem length_rankBlock (q : ℕ → ℕ) (k : ℕ) :
    (rankBlock q k).length = blockWidth q k := by
  simp [rankBlock]

theorem rankBlock_pairwise (q : ℕ → ℕ) (k : ℕ) :
    (rankBlock q k).Pairwise (· ≤ ·) := by
  rw [rankBlock, List.pairwise_ofFn]
  intro i j hij
  exact Nat.add_le_add_left (Nat.sub_le_sub_right hij.le (scale q k)) _

theorem mem_rankBlock_lower {q : ℕ → ℕ} {k x : ℕ}
    (hx : x ∈ rankBlock q k) : blockStart q k ≤ x := by
  rw [rankBlock, List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  exact Nat.le_add_right _ _

theorem mem_rankBlock_upper {q : ℕ → ℕ} {k x : ℕ}
    (hx : x ∈ rankBlock q k) : x < blockStart q (k + 1) := by
  rw [rankBlock, List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  rw [blockStart_succ]
  exact Nat.add_lt_add_left ((Nat.sub_le i.1 _).trans_lt i.2) _

/-- Concatenation of ranks for blocks `0,...,k`. -/
def ranksThrough (q : ℕ → ℕ) : ℕ → List ℕ
  | 0 => rankBlock q 0
  | k + 1 => ranksThrough q k ++ rankBlock q (k + 1)

@[simp] theorem ranksThrough_zero (q : ℕ → ℕ) :
    ranksThrough q 0 = rankBlock q 0 := rfl

@[simp] theorem ranksThrough_succ (q : ℕ → ℕ) (k : ℕ) :
    ranksThrough q (k + 1) = ranksThrough q k ++ rankBlock q (k + 1) := rfl

@[simp] theorem length_ranksThrough (q : ℕ → ℕ) (k : ℕ) :
    (ranksThrough q k).length = blockStart q (k + 1) := by
  induction k with
  | zero => simp [ranksThrough]
  | succ k ih => simp [ranksThrough, ih, Nat.add_assoc]

theorem mem_ranksThrough_upper {q : ℕ → ℕ} {k x : ℕ}
    (hx : x ∈ ranksThrough q k) : x < blockStart q (k + 1) := by
  induction k with
  | zero =>
      simpa only [ranksThrough_zero] using mem_rankBlock_upper hx
  | succ k ih =>
      rw [ranksThrough_succ, List.mem_append] at hx
      rcases hx with hx | hx
      · exact (ih hx).trans (blockStart_strictMono q (Nat.lt_succ_self _))
      · simpa only [Nat.add_eq, blockStart_succ] using mem_rankBlock_upper hx

theorem ranksThrough_pairwise (q : ℕ → ℕ) (k : ℕ) :
    (ranksThrough q k).Pairwise (· ≤ ·) := by
  induction k with
  | zero => exact rankBlock_pairwise q 0
  | succ k ih =>
      rw [ranksThrough_succ, List.pairwise_append]
      refine ⟨ih, rankBlock_pairwise q (k + 1), ?_⟩
      intro a ha b hb
      exact (mem_ranksThrough_upper ha).le.trans (mem_rankBlock_lower hb)

private theorem block_position_lt (q : ℕ → ℕ) {j k : ℕ} (hjk : j ≤ k)
    (i : Fin (blockWidth q j)) :
    blockStart q j + i.1 < blockStart q (k + 1) := by
  have hlocal : blockStart q j + i.1 < blockStart q (j + 1) := by
    rw [blockStart_succ]
    exact Nat.add_lt_add_left i.2 _
  exact hlocal.trans_le ((blockStart_strictMono q).monotone (Nat.succ_le_succ hjk))

theorem getElem_ranksThrough_block (q : ℕ → ℕ) {j k : ℕ} (hjk : j ≤ k)
    (i : Fin (blockWidth q j)) :
    (ranksThrough q k)[blockStart q j + i.1]'(by
      simpa only [length_ranksThrough] using block_position_lt q hjk i) =
      blockStart q j + (i.1 - scale q j) := by
  induction k with
  | zero =>
      have hj : j = 0 := by omega
      subst j
      simp [ranksThrough, rankBlock]
  | succ k ih =>
      by_cases hj : j ≤ k
      · simp only [ranksThrough_succ]
        rw [List.getElem_append_left]
        exact ih hj
      · have hj' : j = k + 1 := by omega
        subst j
        simp only [ranksThrough_succ]
        rw [List.getElem_append_right (by
          rw [length_ranksThrough]
          exact Nat.le_add_right _ _)]
        simp [rankBlock]

/-- The increasing tuple cut out by block `k` of the ladder at `a`. -/
def tuple (C : (a : Height.S) → Ordinal.Club a.1)
    (q : ℕ → ℕ) (a : Height.S) (k : ℕ) :
    Specker.IncSeq (blockWidth q k) (Set.Iio Height.lambda.ord) where
  val i :=
    ⟨Height.point C a (blockStart q k + i.1),
      (Height.point_lt_height C a _).trans a.2.1⟩
  strictMono i j hij := by
    apply Height.point_strictMono C a
    exact Nat.add_lt_add_left hij _

/-- All Specker block inequalities through `k` hold between two heights. -/
def CompatibleThrough
    (C : (a : Height.S) → Ordinal.Club a.1)
    (q : ℕ → ℕ) (a b : Height.S) (k : ℕ) : Prop :=
  ∀ j ≤ k, Specker.Up (scale q j) (tuple C q a j) (tuple C q b j)

/-- A club-guessing cell contains two increasing heights which realize every
Specker block through a prescribed finite stage. -/
theorem realizeBlocks
    (C : (a : Height.S) → Ordinal.Club a.1)
    (q : ℕ → ℕ) (P : Height.S → Prop)
    (hguess : ∀ D : Ordinal.Club Height.lambda.ord,
      ∃ a : Height.S, P a ∧ (C a).carrier ⊆ D.carrier)
    (k : ℕ) :
    ∃ a b : Height.S, P a ∧ P b ∧ a.1 < b.1 ∧
      CompatibleThrough C q a b k := by
  obtain ⟨a, b, hPa, hPb, hab, hrel⟩ :=
    Height.realizeRanks C P hguess (ranksThrough q k)
      (ranksThrough_pairwise q k)
  refine ⟨a, b, hPa, hPb, hab, ?_⟩
  intro j hj i hsi hin
  let p := blockStart q j + i
  have hp : p < (ranksThrough q k).length := by
    simpa only [length_ranksThrough] using
      block_position_lt q hj ⟨i, hin⟩
  have hp' : p < (Height.initial C a (ranksThrough q k).length).length := by
    simpa only [Height.length_initial] using hp
  have hr := hrel.get hp hp'
  have hrank : (ranksThrough q k).get ⟨p, hp⟩ =
      blockStart q j + (i - scale q j) := by
    simpa [p] using getElem_ranksThrough_block q hj ⟨i, hin⟩
  have hpoint : (Height.initial C a (ranksThrough q k).length).get ⟨p, hp'⟩ =
      ⟨Height.point C a p, (Height.point_lt_height C a p).trans a.2.1⟩ := by
    simp [Height.initial]
  rw [hrank, hpoint] at hr
  have hrpos : blockStart q j + (i - scale q j) ≠ 0 := by
    have : 0 < i - scale q j := Nat.sub_pos_of_lt hsi
    omega
  rw [Height.lowerPoint, if_neg hrpos] at hr
  have hidx : blockStart q j + (i - scale q j) - 1 =
      blockStart q j + (i - scale q j - 1) := by
    have : 0 < i - scale q j := Nat.sub_pos_of_lt hsi
    omega
  change
    Height.point C b (blockStart q j + (i - scale q j - 1)) <
        Height.point C a (blockStart q j + i) ∧
      Height.point C a (blockStart q j + i) <
        Height.point C b (blockStart q j + (i - scale q j))
  simpa [Height.upperPoint, p, hidx] using hr

end Blocks
end Erdos110
