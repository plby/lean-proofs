/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayInfiniteCoordinateRunEmbedding

/-!
# A shifted infinite compressor inside its parent

Cutting an infinite raw stream at coordinate `a` and recompressing can split
the original maximal run which contains `a`; all later shifted runs are still
literal directed subpaths of distinct original runs.  This is the terminal
tail counterpart of the bounded coordinate-interval construction.
-/

noncomputable section

open Set

namespace Erdos599.Alternating.RunCompressor.InfiniteInput

open DirectedPath

universe u

variable {V : Type u} {D : Digraph V}

def shiftGlobalLower (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (a i : Nat) : Nat :=
  a + runBoundary (S.shift a).colour (S.shift_changes hchange a) i

def shiftGlobalUpper (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (a i : Nat) : Nat :=
  a + runBoundary (S.shift a).colour (S.shift_changes hchange a) (i + 1)

noncomputable def shiftParentRun (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (a i : Nat) : Nat :=
  S.runIndexAt hchange (S.shiftGlobalLower hchange a i)

theorem shiftGlobalLower_lt_upper (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (a i : Nat) :
    S.shiftGlobalLower hchange a i < S.shiftGlobalUpper hchange a i := by
  exact Nat.add_lt_add_left
    (runBoundary_lt_succ (S.shift a).colour (S.shift_changes hchange a) i) a

theorem shiftParentRun_lower_le (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (a i : Nat) :
    runBoundary S.colour hchange (S.shiftParentRun hchange a i) ≤
      S.shiftGlobalLower hchange a i :=
  S.runBoundary_runIndexAt_le hchange _

theorem shiftParentRun_start_lt_upper (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (a i : Nat) :
    S.shiftGlobalLower hchange a i <
      runBoundary S.colour hchange (S.shiftParentRun hchange a i + 1) :=
  S.runIndexAt_lt_nextBoundary hchange _

theorem shiftParentRun_direction (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (a i : Nat) :
    S.colour (runBoundary S.colour hchange (S.shiftParentRun hchange a i)) =
      (S.shift a).colour
        (runBoundary (S.shift a).colour (S.shift_changes hchange a) i) := by
  let n := S.shiftGlobalLower hchange a i
  have hp : S.colour n =
      S.colour (runBoundary S.colour hchange
        (S.shiftParentRun hchange a i)) :=
    colour_eq_on_run S.colour hchange
      (S.shiftParentRun_lower_le hchange a i)
      (S.shiftParentRun_start_lt_upper hchange a i)
  change S.colour (runBoundary S.colour hchange
      (S.shiftParentRun hchange a i)) =
    S.colour (a + runBoundary (S.shift a).colour
      (S.shift_changes hchange a) i)
  exact hp.symm

theorem shiftGlobalUpper_le_parentUpper (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (a i : Nat) :
    S.shiftGlobalUpper hchange a i ≤
      runBoundary S.colour hchange (S.shiftParentRun hchange a i + 1) := by
  let U := S.shift a
  let hu := S.shift_changes hchange a
  let p := S.shiftParentRun hchange a i
  by_contra hnot
  have hpLtChild : runBoundary S.colour hchange (p + 1) <
      S.shiftGlobalUpper hchange a i := Nat.lt_of_not_ge hnot
  have hchildLower : S.shiftGlobalLower hchange a i <
      runBoundary S.colour hchange (p + 1) :=
    S.shiftParentRun_start_lt_upper hchange a i
  have ha : a ≤ runBoundary S.colour hchange (p + 1) := by
    exact (Nat.le_add_right a _).trans hchildLower.le
  let k := runBoundary S.colour hchange (p + 1) - a
  have hkLower : runBoundary U.colour hu i ≤ k := by
    change runBoundary U.colour hu i ≤
      runBoundary S.colour hchange (p + 1) - a
    change a + runBoundary U.colour hu i <
      runBoundary S.colour hchange (p + 1) at hchildLower
    omega
  have hkUpper : k < runBoundary U.colour hu (i + 1) := by
    change runBoundary S.colour hchange (p + 1) - a <
      runBoundary U.colour hu (i + 1)
    change runBoundary S.colour hchange (p + 1) <
      a + runBoundary U.colour hu (i + 1) at hpLtChild
    omega
  have hkColour : U.colour k =
      U.colour (runBoundary U.colour hu i) :=
    colour_eq_on_run U.colour hu hkLower hkUpper
  have hsame : U.colour k =
      S.colour (runBoundary S.colour hchange (p + 1)) := by
    change S.colour (a + k) =
      S.colour (runBoundary S.colour hchange (p + 1))
    rw [show a + k = runBoundary S.colour hchange (p + 1) from
      Nat.add_sub_of_le ha]
  have hpDir := S.shiftParentRun_direction hchange a i
  have heq : S.colour (runBoundary S.colour hchange (p + 1)) =
      S.colour (runBoundary S.colour hchange p) :=
    hsame.symm.trans (hkColour.trans hpDir.symm)
  exact (colour_runBoundary_succ_ne S.colour hchange p) heq

theorem shift_projectedRun_isSubpathOf_parent
    (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (a i : Nat) :
    ((S.shift a).projectedRun (S.shift_changes hchange a) i).link.path.IsSubpathOf
      (.inl (S.projectedRun hchange
        (S.shiftParentRun hchange a i)).link.path) := by
  let U := S.shift a
  let hu := S.shift_changes hchange a
  let p := S.shiftParentRun hchange a i
  have hdir : S.colour (runBoundary S.colour hchange p) =
      U.colour (runBoundary U.colour hu i) :=
    S.shiftParentRun_direction hchange a i
  constructor
  · change (U.projectedRun hu i).link.path.support ⊆
      (S.projectedRun hchange p).link.path.support
    rw [U.projectedRun_support hu i, S.projectedRun_support hchange p]
    rintro x ⟨n, hn, rfl⟩
    refine ⟨a + n, ⟨?_, ?_⟩, rfl⟩
    · exact (S.shiftParentRun_lower_le hchange a i).trans
        (Nat.add_le_add_left hn.1 a)
    · exact (Nat.add_le_add_left hn.2 a).trans
        (S.shiftGlobalUpper_le_parentUpper hchange a i)
  · cases hchild : U.colour (runBoundary U.colour hu i) with
    | forward =>
        have hparent : S.colour (runBoundary S.colour hchange p) = .forward :=
          hdir.trans hchild
        change (U.projectedRun hu i).link.path.edgeSet ⊆
          (S.projectedRun hchange p).link.path.edgeSet
        rw [U.projectedRun_edgeSet_eq_forward hu i hchild,
          S.projectedRun_edgeSet_eq_forward hchange p hparent]
        rintro e ⟨k, hlo, hhi, rfl⟩
        refine ⟨a + k, ?_, ?_, ?_⟩
        · exact (S.shiftParentRun_lower_le hchange a i).trans
            (Nat.add_le_add_left hlo a)
        · apply Nat.lt_of_succ_le
          have hstep : a + (k + 1) ≤ S.shiftGlobalUpper hchange a i := by
            change a + (k + 1) ≤
              a + runBoundary U.colour hu (i + 1)
            omega
          exact hstep.trans
            (S.shiftGlobalUpper_le_parentUpper hchange a i)
        · simp only [U, shift_vertex, Nat.add_assoc]
    | backward =>
        have hparent : S.colour (runBoundary S.colour hchange p) = .backward :=
          hdir.trans hchild
        change (U.projectedRun hu i).link.path.edgeSet ⊆
          (S.projectedRun hchange p).link.path.edgeSet
        rw [U.projectedRun_edgeSet_eq_backward hu i hchild,
          S.projectedRun_edgeSet_eq_backward hchange p hparent]
        rintro e ⟨k, hlo, hhi, rfl⟩
        refine ⟨a + k, ?_, ?_, ?_⟩
        · exact (S.shiftParentRun_lower_le hchange a i).trans
            (Nat.add_le_add_left hlo a)
        · apply Nat.lt_of_succ_le
          have hstep : a + (k + 1) ≤ S.shiftGlobalUpper hchange a i := by
            change a + (k + 1) ≤
              a + runBoundary U.colour hu (i + 1)
            omega
          exact hstep.trans
            (S.shiftGlobalUpper_le_parentUpper hchange a i)
        · simp only [U, shift_vertex, Nat.add_assoc]

theorem shiftParentRun_injective (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (a : Nat) : Function.Injective (S.shiftParentRun hchange a) := by
  let U := S.shift a
  let hu := S.shift_changes hchange a
  have forwardCase : ∀ {i j : Nat}, i < j →
      S.shiftParentRun hchange a i = S.shiftParentRun hchange a j → i = j := by
    intro i j hij hparent
    exfalso
    let p := S.shiftParentRun hchange a i
    have hlo : runBoundary S.colour hchange p ≤
        S.shiftGlobalLower hchange a (i + 1) := by
      exact (S.shiftParentRun_lower_le hchange a i).trans
        (Nat.add_le_add_left
          ((runBoundary_strictMono U.colour hu).monotone
            (Nat.le_succ i)) a)
    have hhi : S.shiftGlobalLower hchange a (i + 1) <
        runBoundary S.colour hchange (p + 1) := by
      have hj := S.shiftParentRun_start_lt_upper hchange a j
      rw [← hparent] at hj
      exact (Nat.add_le_add_left
        ((runBoundary_strictMono U.colour hu).monotone (by omega)) a).trans_lt hj
    have hm : S.shiftParentRun hchange a (i + 1) = p := by
      apply S.runIndexAt_eq_of_mem_interval hchange
        (S.shiftGlobalLower hchange a (i + 1)) p hlo hhi
    have hiDir := S.shiftParentRun_direction hchange a i
    have hmDir := S.shiftParentRun_direction hchange a (i + 1)
    rw [hm] at hmDir
    exact (colour_runBoundary_succ_ne U.colour hu i)
      (hmDir.symm.trans hiDir)
  intro i j hparent
  by_cases h : i = j
  · exact h
  rcases lt_or_gt_of_ne h with hij | hji
  · exact forwardCase hij hparent
  · exact (forwardCase hji hparent.symm).symm

#print axioms shiftGlobalUpper_le_parentUpper
#print axioms shift_projectedRun_isSubpathOf_parent
#print axioms shiftParentRun_injective

end Erdos599.Alternating.RunCompressor.InfiniteInput
