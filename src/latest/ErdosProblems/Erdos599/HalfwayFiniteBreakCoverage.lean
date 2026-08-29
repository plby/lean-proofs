/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayFiniteInputBreakInterval

/-!
# Coverage by consecutive finite break intervals

The largest displayed break coordinate below a nonfinal traversal position
determines the unique consecutive interval containing that position.
-/

noncomputable section

open Set

namespace Erdos599.Alternating.FiniteRunWalk

universe u

variable {V : Type u} {D : Digraph V}

def breakIndicesBelow (W : FiniteRunWalk D) (X : Set V) (n : Nat) :
    Finset (Fin (W.breakCount X + 1)) := by
  classical
  exact Finset.univ.filter fun i => W.breakPosition X i ≤ n

theorem breakIndicesBelow_nonempty (W : FiniteRunWalk D) (X : Set V)
    (n : Nat) : (W.breakIndicesBelow X n).Nonempty := by
  refine ⟨⟨0, Nat.zero_lt_succ _⟩, ?_⟩
  classical
  simp only [breakIndicesBelow, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [W.breakPosition_zero X]
  exact Nat.zero_le n

noncomputable def lowerBreakIndex (W : FiniteRunWalk D) (X : Set V)
    (n : Nat) : Fin (W.breakCount X + 1) :=
  (W.breakIndicesBelow X n).max' (W.breakIndicesBelow_nonempty X n)

theorem lowerBreakIndex_mem (W : FiniteRunWalk D) (X : Set V) (n : Nat) :
    W.lowerBreakIndex X n ∈ W.breakIndicesBelow X n :=
  Finset.max'_mem _ _

theorem breakPosition_lowerBreakIndex_le (W : FiniteRunWalk D)
    (X : Set V) (n : Nat) :
    W.breakPosition X (W.lowerBreakIndex X n) ≤ n := by
  have h := W.lowerBreakIndex_mem X n
  classical
  simpa only [breakIndicesBelow, Finset.mem_filter, Finset.mem_univ,
    true_and] using h

theorem le_lowerBreakIndex_of_breakPosition_le (W : FiniteRunWalk D)
    (X : Set V) (n : Nat) (i : Fin (W.breakCount X + 1))
    (hi : W.breakPosition X i ≤ n) : i ≤ W.lowerBreakIndex X n := by
  apply Finset.le_max'
  classical
  simp [breakIndicesBelow, hi]

theorem lowerBreakIndex_lt_last_of_lt_final (W : FiniteRunWalk D)
    (X : Set V) {n : Nat} (hn : n < W.finalPosition) :
    (W.lowerBreakIndex X n).1 < W.breakCount X := by
  have hne : W.lowerBreakIndex X n ≠
      (⟨W.breakCount X, Nat.lt_succ_self _⟩ :
        Fin (W.breakCount X + 1)) := by
    intro heq
    have hle := W.breakPosition_lowerBreakIndex_le X n
    rw [heq, W.breakPosition_last X] at hle
    omega
  have hneval : (W.lowerBreakIndex X n).1 ≠ W.breakCount X := by
    intro hval
    apply hne
    exact Fin.ext hval
  exact lt_of_le_of_ne (Nat.le_of_lt_succ (W.lowerBreakIndex X n).2) hneval

/-- Every nonfinal coordinate lies between two consecutive displayed break
coordinates. -/
theorem exists_consecutiveBreak_interval (W : FiniteRunWalk D)
    (X : Set V) {n : Nat} (hn : n < W.finalPosition) :
    ∃ i : Fin (W.breakCount X),
      W.breakPosition X i.castSucc ≤ n ∧
      n < W.breakPosition X i.succ := by
  let i : Fin (W.breakCount X) :=
    ⟨(W.lowerBreakIndex X n).1,
      W.lowerBreakIndex_lt_last_of_lt_final X hn⟩
  refine ⟨i, ?_, ?_⟩
  · have heq : i.castSucc = W.lowerBreakIndex X n := Fin.ext rfl
    rw [heq]
    exact W.breakPosition_lowerBreakIndex_le X n
  · by_contra hnot
    have hle : W.breakPosition X i.succ ≤ n := Nat.le_of_not_gt hnot
    have hisucc : i.succ ≤ W.lowerBreakIndex X n :=
      W.le_lowerBreakIndex_of_breakPosition_le X n i.succ hle
    have heq : i.castSucc = W.lowerBreakIndex X n := Fin.ext rfl
    rw [← heq] at hisucc
    exact (not_le_of_gt Fin.castSucc_lt_succ) hisucc

end Erdos599.Alternating.FiniteRunWalk

#print axioms Erdos599.Alternating.FiniteRunWalk.exists_consecutiveBreak_interval
