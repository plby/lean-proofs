/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteRelationTrace
import ErdosProblems.Erdos599.RunCompressor

/-!
# Chronological loop erasure for a finite vertex sequence

Starting at the last occurrence of the first vertex, retain the outgoing
edge, and then jump its other endpoint to its last occurrence.  The retained
indices strictly increase until the final raw index, and their projected
vertices are injective.  This is the finite counterpart of the construction
in `RawAlternatingDichotomy`.
-/

namespace Erdos599
namespace Alternating

universe u

variable {V : Type u}

/-- The last bounded index at which the value at `i` occurs. -/
noncomputable def boundedLastOccurrence {N : ℕ}
    (f : Fin (N + 1) → V) (i : Fin (N + 1)) : Fin (N + 1) := by
  classical
  let s := Finset.univ.filter (fun j ↦ f j = f i)
  exact s.max' ⟨i, by simp [s]⟩

theorem boundedLastOccurrence_mem {N : ℕ}
    (f : Fin (N + 1) → V) (i : Fin (N + 1)) :
    f (boundedLastOccurrence f i) = f i := by
  classical
  have hmem := Finset.max'_mem
    (Finset.univ.filter (fun j ↦ f j = f i))
    ⟨i, by simp⟩
  simpa [boundedLastOccurrence] using hmem

theorem le_boundedLastOccurrence {N : ℕ}
    (f : Fin (N + 1) → V) (i : Fin (N + 1)) :
    i ≤ boundedLastOccurrence f i := by
  classical
  apply Finset.le_max'
  simp

theorem le_boundedLastOccurrence_of_eq {N : ℕ}
    (f : Fin (N + 1) → V) {i j : Fin (N + 1)} (h : f j = f i) :
    j ≤ boundedLastOccurrence f i := by
  classical
  apply Finset.le_max'
  simp [h]

theorem boundedLastOccurrence_is_last {N : ℕ}
    (f : Fin (N + 1) → V) {i j : Fin (N + 1)}
    (h : f j = f (boundedLastOccurrence f i)) :
    j ≤ boundedLastOccurrence f i := by
  apply le_boundedLastOccurrence_of_eq f
  exact h.trans (boundedLastOccurrence_mem f i)

/-- The bounded chronological-erasure index stream.  It stays at the final
raw index after reaching it. -/
noncomputable def finiteLoopIndex {N : ℕ} (f : Fin (N + 1) → V) :
    ℕ → Fin (N + 1)
  | 0 => boundedLastOccurrence f ⟨0, Nat.zero_lt_succ _⟩
  | n + 1 =>
      let i := finiteLoopIndex f n
      if h : i.1 < N then
        boundedLastOccurrence f ⟨i.1 + 1, by omega⟩
      else i

theorem finiteLoopIndex_le_succ {N : ℕ} (f : Fin (N + 1) → V) (n : ℕ) :
    finiteLoopIndex f n ≤ finiteLoopIndex f (n + 1) := by
  rw [finiteLoopIndex]
  split_ifs with h
  · exact (Fin.mk_le_mk.mpr (Nat.le_succ _)).trans
      (le_boundedLastOccurrence f _)
  · exact le_rfl

theorem finiteLoopIndex_lt_succ_of_lt {N : ℕ}
    (f : Fin (N + 1) → V) {n : ℕ}
    (h : (finiteLoopIndex f n).1 < N) :
    finiteLoopIndex f n < finiteLoopIndex f (n + 1) := by
  rw [finiteLoopIndex, dif_pos h]
  exact (Fin.mk_lt_mk.mpr (Nat.lt_succ_self _)).trans_le
    (le_boundedLastOccurrence f _)

theorem finiteLoopIndex_join_of_lt {N : ℕ}
    (f : Fin (N + 1) → V) {n : ℕ}
    (h : (finiteLoopIndex f n).1 < N) :
    f ⟨(finiteLoopIndex f n).1 + 1, by omega⟩ =
      f (finiteLoopIndex f (n + 1)) := by
  rw [finiteLoopIndex, dif_pos h]
  exact (boundedLastOccurrence_mem f _).symm

theorem finiteLoopIndex_stable_of_eq_top {N : ℕ}
    (f : Fin (N + 1) → V) {n : ℕ}
    (h : (finiteLoopIndex f n).1 = N) :
    finiteLoopIndex f (n + 1) = finiteLoopIndex f n := by
  rw [finiteLoopIndex, dif_neg (by omega)]

theorem finiteLoopIndex_lower_bound {N : ℕ}
    (f : Fin (N + 1) → V) {n : ℕ} (hn : n ≤ N) :
    n ≤ (finiteLoopIndex f n).1 := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
      have hn' : n ≤ N := Nat.le_trans (Nat.le_succ n) hn
      have ih' := ih hn'
      by_cases htop : (finiteLoopIndex f n).1 = N
      · rw [finiteLoopIndex_stable_of_eq_top f htop, htop]
        exact hn
      · have hlt : (finiteLoopIndex f n).1 < N := by omega
        have hstep := finiteLoopIndex_lt_succ_of_lt f hlt
        exact Nat.succ_le_of_lt (lt_of_le_of_lt ih' (Fin.mk_lt_mk.mp hstep))

theorem finiteLoopIndex_at_top {N : ℕ} (f : Fin (N + 1) → V) :
    (finiteLoopIndex f N).1 = N := by
  have hlower := finiteLoopIndex_lower_bound f (n := N) le_rfl
  exact Nat.le_antisymm (Nat.le_of_lt_succ (finiteLoopIndex f N).2) hlower

/-- The first step at which bounded loop erasure reaches the final raw
index. -/
noncomputable def finiteLoopLength {N : ℕ} (f : Fin (N + 1) → V) : ℕ :=
  Nat.find (show ∃ n, (finiteLoopIndex f n).1 = N from
    ⟨N, finiteLoopIndex_at_top f⟩)

@[simp]
theorem finiteLoopIndex_at_length {N : ℕ} (f : Fin (N + 1) → V) :
    (finiteLoopIndex f (finiteLoopLength f)).1 = N :=
  Nat.find_spec (show ∃ n, (finiteLoopIndex f n).1 = N from
    ⟨N, finiteLoopIndex_at_top f⟩)

theorem finiteLoopLength_le {N : ℕ} (f : Fin (N + 1) → V) :
    finiteLoopLength f ≤ N :=
  Nat.find_min' (show ∃ n, (finiteLoopIndex f n).1 = N from
    ⟨N, finiteLoopIndex_at_top f⟩) (finiteLoopIndex_at_top f)

theorem finiteLoopIndex_lt_top_of_lt_length {N : ℕ}
    (f : Fin (N + 1) → V) {n : ℕ} (hn : n < finiteLoopLength f) :
    (finiteLoopIndex f n).1 < N := by
  by_contra hnot
  have heq : (finiteLoopIndex f n).1 = N := by
    have hle := Nat.le_of_lt_succ (finiteLoopIndex f n).2
    omega
  exact (Nat.find_min (show ∃ n, (finiteLoopIndex f n).1 = N from
    ⟨N, finiteLoopIndex_at_top f⟩) hn) heq

theorem finiteLoopIndex_strict_of_lt_length {N : ℕ}
    (f : Fin (N + 1) → V) {i j : ℕ}
    (hij : i < j) (hj : j ≤ finiteLoopLength f) :
    finiteLoopIndex f i < finiteLoopIndex f j := by
  have hmono : Monotone (finiteLoopIndex f) :=
    monotone_nat_of_le_succ (finiteLoopIndex_le_succ f)
  have hi : i < finiteLoopLength f := hij.trans_le hj
  exact (finiteLoopIndex_lt_succ_of_lt f
    (finiteLoopIndex_lt_top_of_lt_length f hi)).trans_le
      (hmono (Nat.succ_le_iff.mpr hij))

/-- Every retained index is the last raw occurrence of its projected
vertex. -/
theorem finiteLoopIndex_is_last {N : ℕ}
    (f : Fin (N + 1) → V) (n : ℕ) {j : Fin (N + 1)}
    (h : f j = f (finiteLoopIndex f n)) :
    j ≤ finiteLoopIndex f n := by
  induction n with
  | zero =>
      rw [finiteLoopIndex]
      exact boundedLastOccurrence_is_last f h
  | succ n ih =>
      by_cases hlt : (finiteLoopIndex f n).1 < N
      · rw [finiteLoopIndex, dif_pos hlt] at h ⊢
        exact boundedLastOccurrence_is_last f h
      · have heq : finiteLoopIndex f (n + 1) = finiteLoopIndex f n := by
          rw [finiteLoopIndex, dif_neg hlt]
        rw [heq] at h ⊢
        exact ih h

theorem finiteLoopVertex_injective_to_length {N : ℕ}
    (f : Fin (N + 1) → V) {i j : ℕ}
    (hi : i ≤ finiteLoopLength f) (hj : j ≤ finiteLoopLength f)
    (h : f (finiteLoopIndex f i) = f (finiteLoopIndex f j)) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hindex := finiteLoopIndex_strict_of_lt_length f hij hj
    have hlast := finiteLoopIndex_is_last f i (j := finiteLoopIndex f j) h.symm
    exact (not_lt_of_ge hlast) hindex
  · have hindex := finiteLoopIndex_strict_of_lt_length f hji hi
    have hlast := finiteLoopIndex_is_last f j (j := finiteLoopIndex f i) h
    exact (not_lt_of_ge hlast) hindex

theorem finiteLoopIndex_zero_of_root_unique {N : ℕ}
    (f : Fin (N + 1) → V)
    (hroot : ∀ i, f i = f ⟨0, Nat.zero_lt_succ _⟩ → i.1 = 0) :
    finiteLoopIndex f 0 = ⟨0, Nat.zero_lt_succ _⟩ := by
  rw [finiteLoopIndex]
  apply Fin.ext
  exact hroot _ (boundedLastOccurrence_mem f _)

theorem finiteLoopLength_pos {N : ℕ} (hN : 0 < N)
    (f : Fin (N + 1) → V)
    (hroot : ∀ i, f i = f ⟨0, Nat.zero_lt_succ _⟩ → i.1 = 0) :
    0 < finiteLoopLength f := by
  by_contra hnot
  have hzero : finiteLoopLength f = 0 := Nat.eq_zero_of_not_pos hnot
  have htop := finiteLoopIndex_at_length f
  rw [hzero, finiteLoopIndex_zero_of_root_unique f hroot] at htop
  exact (Nat.ne_of_gt hN) htop.symm

/-- Extend the retained finite vertex sequence constantly after its last
index.  Only the initial segment through `finiteLoopLength f` is used by a
finite run compressor. -/
noncomputable def finiteLoopVertex {N : ℕ} (f : Fin (N + 1) → V)
    (k : ℕ) : V :=
  if _h : k ≤ finiteLoopLength f then f (finiteLoopIndex f k)
  else f (finiteLoopIndex f (finiteLoopLength f))

theorem finiteLoopVertex_eq {N : ℕ} (f : Fin (N + 1) → V)
    {k : ℕ} (hk : k ≤ finiteLoopLength f) :
    finiteLoopVertex f k = f (finiteLoopIndex f k) := by
  simp [finiteLoopVertex, hk]

theorem finiteLoopVertex_injective_on {N : ℕ}
    (f : Fin (N + 1) → V) {i j : ℕ}
    (hi : i ≤ finiteLoopLength f) (hj : j ≤ finiteLoopLength f)
    (h : finiteLoopVertex f i = finiteLoopVertex f j) : i = j := by
  rw [finiteLoopVertex_eq f hi, finiteLoopVertex_eq f hj] at h
  exact finiteLoopVertex_injective_to_length f hi hj h

theorem finiteLoopVertex_zero_of_root_unique {N : ℕ}
    (f : Fin (N + 1) → V)
    (hroot : ∀ i, f i = f ⟨0, Nat.zero_lt_succ _⟩ → i.1 = 0) :
    finiteLoopVertex f 0 = f ⟨0, Nat.zero_lt_succ _⟩ := by
  rw [finiteLoopVertex_eq f (Nat.zero_le _),
    finiteLoopIndex_zero_of_root_unique f hroot]

theorem finiteLoopVertex_last {N : ℕ} (f : Fin (N + 1) → V) :
    finiteLoopVertex f (finiteLoopLength f) =
      f ⟨N, Nat.lt_succ_self _⟩ := by
  rw [finiteLoopVertex_eq f le_rfl]
  apply congrArg f
  apply Fin.ext
  exact finiteLoopIndex_at_length f

/-- Each retained successor pair is the raw edge leaving its retained raw
index. -/
theorem finiteLoopVertex_succ {N : ℕ} (f : Fin (N + 1) → V)
    {k : ℕ} (hk : k < finiteLoopLength f) :
    finiteLoopVertex f k = f (finiteLoopIndex f k) ∧
      finiteLoopVertex f (k + 1) =
        f ⟨(finiteLoopIndex f k).1 + 1, by
          have := finiteLoopIndex_lt_top_of_lt_length f hk
          omega⟩ := by
  have hk' : k ≤ finiteLoopLength f := Nat.le_of_lt hk
  have hks' : k + 1 ≤ finiteLoopLength f := Nat.succ_le_iff.mpr hk
  constructor
  · exact finiteLoopVertex_eq f hk'
  · rw [finiteLoopVertex_eq f hks']
    exact (finiteLoopIndex_join_of_lt f
      (finiteLoopIndex_lt_top_of_lt_length f hk)).symm

/-- Feed bounded chronological loop erasure directly to the finite maximal
run compressor.  Edge colours and oriented adjacency are read at the retained
raw edge indices. -/
noncomputable def RunCompressor.FiniteInput.ofLoopErasure
    {D : Digraph V} {N : ℕ} (hN : 0 < N)
    (f : Fin (N + 1) → V)
    (hroot : ∀ i, f i = f ⟨0, Nat.zero_lt_succ _⟩ → i.1 = 0)
    (rawColour : Fin N → Direction)
    (forward_adj : ∀ i : Fin N, rawColour i = .forward →
      D.Adj (f ⟨i.1, by omega⟩) (f ⟨i.1 + 1, by omega⟩))
    (backward_adj : ∀ i : Fin N, rawColour i = .backward →
      D.Adj (f ⟨i.1 + 1, by omega⟩) (f ⟨i.1, by omega⟩)) :
    RunCompressor.FiniteInput D where
  lastEdge := finiteLoopLength f
  lastEdge_pos := finiteLoopLength_pos hN f hroot
  vertex := finiteLoopVertex f
  vertex_injective_on := fun hi hj h ↦
    finiteLoopVertex_injective_on f hi hj h
  colour i := rawColour ⟨(finiteLoopIndex f i.1).1,
    finiteLoopIndex_lt_top_of_lt_length f i.2⟩
  forward_adj i hdir := by
    rcases finiteLoopVertex_succ f i.2 with ⟨hcur, hnext⟩
    rw [hcur, hnext]
    exact forward_adj _ hdir
  backward_adj i hdir := by
    rcases finiteLoopVertex_succ f i.2 with ⟨hcur, hnext⟩
    rw [hcur, hnext]
    exact backward_adj _ hdir

namespace RunCompressor.FiniteInput

@[simp]
theorem ofLoopErasure_vertex_zero
    {D : Digraph V} {N : ℕ} (hN : 0 < N)
    (f : Fin (N + 1) → V) (hroot) (rawColour) (forward_adj) (backward_adj) :
    (ofLoopErasure (D := D) hN f hroot rawColour forward_adj backward_adj).vertex 0 =
      f ⟨0, Nat.zero_lt_succ _⟩ :=
  finiteLoopVertex_zero_of_root_unique f hroot

@[simp]
theorem ofLoopErasure_vertex_last
    {D : Digraph V} {N : ℕ} (hN : 0 < N)
    (f : Fin (N + 1) → V) (hroot) (rawColour) (forward_adj) (backward_adj) :
    let S := ofLoopErasure (D := D) hN f hroot rawColour forward_adj backward_adj
    S.vertex S.lastEdge = f ⟨N, Nat.lt_succ_self _⟩ := by
  dsimp only
  exact finiteLoopVertex_last f

@[simp]
theorem ofLoopErasure_colour
    {D : Digraph V} {N : ℕ} (hN : 0 < N)
    (f : Fin (N + 1) → V) (hroot) (rawColour) (forward_adj) (backward_adj)
    (i : Fin (finiteLoopLength f)) :
    (ofLoopErasure (D := D) hN f hroot rawColour forward_adj backward_adj).colour i =
      rawColour ⟨(finiteLoopIndex f i.1).1,
        finiteLoopIndex_lt_top_of_lt_length f i.2⟩ :=
  rfl

theorem ofLoopErasure_runWalk_initial
    {D : Digraph V} {N : ℕ} (hN : 0 < N)
    (f : Fin (N + 1) → V) (hroot) (rawColour) (forward_adj) (backward_adj) :
    let S := ofLoopErasure (D := D) hN f hroot rawColour forward_adj backward_adj
    S.toFiniteRunWalk.vertex 0 = f ⟨0, Nat.zero_lt_succ _⟩ := by
  dsimp only [RunCompressor.FiniteInput.toFiniteRunWalk]
  exact finiteLoopVertex_zero_of_root_unique f hroot

theorem ofLoopErasure_runWalk_terminal
    {D : Digraph V} {N : ℕ} (hN : 0 < N)
    (f : Fin (N + 1) → V) (hroot) (rawColour) (forward_adj) (backward_adj) :
    let S := ofLoopErasure (D := D) hN f hroot rawColour forward_adj backward_adj
    S.toFiniteRunWalk.vertex
        (S.toFiniteRunWalk.run S.toFiniteRunWalk.lastRunIndex).last =
      f ⟨N, Nat.lt_succ_self _⟩ := by
  dsimp only
  rw [RunCompressor.FiniteInput.toFiniteRunWalk_final_last]
  exact finiteLoopVertex_last f

end RunCompressor.FiniteInput

end Alternating
end Erdos599
