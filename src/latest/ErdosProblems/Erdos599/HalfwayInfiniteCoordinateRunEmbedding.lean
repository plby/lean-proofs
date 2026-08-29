/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayInfiniteInputCoordinateInterval

/-!
# Finite coordinate runs inside an infinite compressor

Every maximal run created by recompressing a bounded coordinate interval of
an `InfiniteInput` lies in the unique maximal run of the original stream
which contains its first raw edge.  The construction below retains the
literal coordinate interval, direction, vertices, and directed edges.
-/

noncomputable section

open Set

namespace Erdos599.Alternating.RunCompressor.InfiniteInput

open DirectedPath

universe u

variable {V : Type u} {D : Digraph V}

def coordinateIntervalGlobalLower (S : InfiniteInput D)
    (a b : Nat) (hab : a < b)
    (j : Fin (S.coordinateInterval a b hab).runs.length) : Nat :=
  a + runLower (S.coordinateInterval a b hab).runs j

def coordinateIntervalGlobalUpper (S : InfiniteInput D)
    (a b : Nat) (hab : a < b)
    (j : Fin (S.coordinateInterval a b hab).runs.length) : Nat :=
  a + runLower (S.coordinateInterval a b hab).runs (j.1 + 1)

theorem coordinateIntervalGlobalLower_lt_upper (S : InfiniteInput D)
    (a b : Nat) (hab : a < b)
    (j : Fin (S.coordinateInterval a b hab).runs.length) :
    S.coordinateIntervalGlobalLower a b hab j <
      S.coordinateIntervalGlobalUpper a b hab j := by
  let T := S.coordinateInterval a b hab
  have hstrict : runLower T.runs j.1 < runLower T.runs (j.1 + 1) :=
    runLower_strictMonoOn T.runs (fun r hr ↦ T.run_ne_nil hr)
      (Nat.lt_succ_self _) (Nat.succ_le_of_lt j.2)
  exact Nat.add_lt_add_left hstrict a

theorem coordinateIntervalGlobalUpper_le (S : InfiniteInput D)
    (a b : Nat) (hab : a < b)
    (j : Fin (S.coordinateInterval a b hab).runs.length) :
    S.coordinateIntervalGlobalUpper a b hab j ≤ b := by
  let T := S.coordinateInterval a b hab
  have h := T.runUpper_le_lastEdge j
  rw [← runLower_succ T.runs j.2] at h
  change runLower T.runs (j.1 + 1) ≤ b - a at h
  have hadd := Nat.add_le_add_left h a
  simpa only [coordinateIntervalGlobalUpper, Nat.add_sub_of_le hab.le] using hadd

/-- The original infinite maximal run containing the first edge of a
recompressed bounded run. -/
noncomputable def coordinateIntervalParentRun (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (a b : Nat) (hab : a < b)
    (j : Fin (S.coordinateInterval a b hab).runs.length) : Nat :=
  S.runIndexAt hchange (S.coordinateIntervalGlobalLower a b hab j)

theorem coordinateIntervalParentRun_lower_le (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (a b : Nat) (hab : a < b)
    (j : Fin (S.coordinateInterval a b hab).runs.length) :
    runBoundary S.colour hchange
        (S.coordinateIntervalParentRun hchange a b hab j) ≤
      S.coordinateIntervalGlobalLower a b hab j :=
  S.runBoundary_runIndexAt_le hchange _

theorem coordinateIntervalParentRun_start_lt_upper (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (a b : Nat) (hab : a < b)
    (j : Fin (S.coordinateInterval a b hab).runs.length) :
    S.coordinateIntervalGlobalLower a b hab j <
      runBoundary S.colour hchange
        (S.coordinateIntervalParentRun hchange a b hab j + 1) :=
  S.runIndexAt_lt_nextBoundary hchange _

theorem coordinateIntervalParentRun_direction (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (a b : Nat) (hab : a < b)
    (j : Fin (S.coordinateInterval a b hab).runs.length) :
    S.colour (runBoundary S.colour hchange
        (S.coordinateIntervalParentRun hchange a b hab j)) =
      (S.coordinateInterval a b hab).runDirection j := by
  let T := S.coordinateInterval a b hab
  let n := S.coordinateIntervalGlobalLower a b hab j
  let p := S.coordinateIntervalParentRun hchange a b hab j
  have hparent : S.colour n =
      S.colour (runBoundary S.colour hchange p) :=
    colour_eq_on_run S.colour hchange
      (S.coordinateIntervalParentRun_lower_le hchange a b hab j)
      (S.coordinateIntervalParentRun_start_lt_upper hchange a b hab j)
  have hpos : 0 < (T.runs.get j).length :=
    List.length_pos_iff_ne_nil.2 (T.run_ne_nil (List.get_mem _ j))
  have hchild := T.colour_run_offset j (k := 0) hpos
  have hsame : T.colour
      ⟨runLower T.runs j + 0, by
        exact lt_of_lt_of_le (Nat.add_lt_add_left hpos _)
          (T.runUpper_le_lastEdge j)⟩ = S.colour n := by
    rfl
  exact hparent.symm.trans (hsame.symm.trans hchild)

/-- The restricted maximal run cannot cross the next original colour-change
boundary. -/
theorem coordinateIntervalGlobalUpper_le_parentUpper (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (a b : Nat) (hab : a < b)
    (j : Fin (S.coordinateInterval a b hab).runs.length) :
    S.coordinateIntervalGlobalUpper a b hab j ≤
      runBoundary S.colour hchange
        (S.coordinateIntervalParentRun hchange a b hab j + 1) := by
  let T := S.coordinateInterval a b hab
  let p := S.coordinateIntervalParentRun hchange a b hab j
  by_contra hnot
  have hpLtChild : runBoundary S.colour hchange (p + 1) <
      S.coordinateIntervalGlobalUpper a b hab j := Nat.lt_of_not_ge hnot
  have hchildLower : S.coordinateIntervalGlobalLower a b hab j <
      runBoundary S.colour hchange (p + 1) :=
    S.coordinateIntervalParentRun_start_lt_upper hchange a b hab j
  have ha : a ≤ runBoundary S.colour hchange (p + 1) := by
    exact (Nat.le_add_right a _).trans hchildLower.le
  have hpLtB : runBoundary S.colour hchange (p + 1) < b :=
    hpLtChild.trans_le (S.coordinateIntervalGlobalUpper_le a b hab j)
  let k : Fin T.lastEdge :=
    ⟨runBoundary S.colour hchange (p + 1) - a, by
      change runBoundary S.colour hchange (p + 1) - a < b - a
      omega⟩
  have hkLower : runLower T.runs j ≤ k.1 := by
    change runLower T.runs j ≤
      runBoundary S.colour hchange (p + 1) - a
    change a + runLower T.runs j <
      runBoundary S.colour hchange (p + 1) at hchildLower
    omega
  have hkUpper : k.1 < runLower T.runs (j.1 + 1) := by
    change runBoundary S.colour hchange (p + 1) - a <
      runLower T.runs (j.1 + 1)
    change runBoundary S.colour hchange (p + 1) <
      a + runLower T.runs (j.1 + 1) at hpLtChild
    omega
  have hkColour : T.colour k = T.runDirection j :=
    T.colour_eq_runDirection j hkLower hkUpper
  have hsame : T.colour k =
      S.colour (runBoundary S.colour hchange (p + 1)) := by
    change S.colour (a + k.1) =
      S.colour (runBoundary S.colour hchange (p + 1))
    rw [show a + k.1 = runBoundary S.colour hchange (p + 1) from
      Nat.add_sub_of_le ha]
  have hpDir :=
    S.coordinateIntervalParentRun_direction hchange a b hab j
  have heq : S.colour (runBoundary S.colour hchange (p + 1)) =
      S.colour (runBoundary S.colour hchange p) :=
    hsame.symm.trans (hkColour.trans hpDir.symm)
  exact (colour_runBoundary_succ_ne S.colour hchange p) heq

/-- Every recompressed finite run is a literal directed subpath of its
original infinite parent run. -/
theorem coordinateInterval_projectedRun_isSubpathOf_parent
    (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (a b : Nat) (hab : a < b)
    (j : Fin (S.coordinateInterval a b hab).runs.length) :
    ((S.coordinateInterval a b hab).projectedRun j).link.path.IsSubpathOf
      (.inl (S.projectedRun
        hchange (S.coordinateIntervalParentRun hchange a b hab j)).link.path) := by
  let T := S.coordinateInterval a b hab
  let p := S.coordinateIntervalParentRun hchange a b hab j
  have hdir : S.colour (runBoundary S.colour hchange p) =
      T.runDirection j :=
    S.coordinateIntervalParentRun_direction hchange a b hab j
  constructor
  · change (T.projectedRun j).link.path.support ⊆
      (S.projectedRun hchange p).link.path.support
    rw [T.projectedRun_support j, S.projectedRun_support hchange p]
    rintro x ⟨n, hn, rfl⟩
    refine ⟨a + n, ⟨?_, ?_⟩, rfl⟩
    · exact (S.coordinateIntervalParentRun_lower_le hchange a b hab j).trans
        (Nat.add_le_add_left hn.1 a)
    · exact (Nat.add_le_add_left hn.2 a).trans
        (S.coordinateIntervalGlobalUpper_le_parentUpper hchange a b hab j)
  · cases hchild : T.runDirection j with
    | forward =>
        have hparent : S.colour (runBoundary S.colour hchange p) = .forward :=
          hdir.trans hchild
        change (T.projectedRun j).link.path.edgeSet ⊆
          (S.projectedRun hchange p).link.path.edgeSet
        rw [T.projectedRun_edgeSet_eq_forward j hchild,
          S.projectedRun_edgeSet_eq_forward hchange p hparent]
        rintro e ⟨k, hk, rfl⟩
        let n := a + runLower T.runs j.1 + k
        refine ⟨n, ?_, ?_, ?_⟩
        · have hstep : S.coordinateIntervalGlobalLower a b hab j ≤ n := by
            change a + runLower T.runs j.1 ≤ n
            dsimp [n]
            omega
          exact (S.coordinateIntervalParentRun_lower_le hchange a b hab j).trans
            hstep
        · have hchildUpper : runLower T.runs j.1 + k + 1 ≤
              runLower T.runs (j.1 + 1) := by
            calc
              runLower T.runs j.1 + k + 1 =
                  runLower T.runs j.1 + (k + 1) := by omega
              _ ≤ runLower T.runs j.1 + (T.runs.get j).length :=
                Nat.add_le_add_left (Nat.succ_le_iff.mpr hk) _
              _ = runLower T.runs (j.1 + 1) :=
                (runLower_succ T.runs j.2).symm
          have hparentUpper :=
            S.coordinateIntervalGlobalUpper_le_parentUpper hchange a b hab j
          change a + runLower T.runs (j.1 + 1) ≤
            runBoundary S.colour hchange (p + 1) at hparentUpper
          have hnNext := (Nat.add_le_add_left hchildUpper a).trans hparentUpper
          apply Nat.lt_of_succ_le
          dsimp only [n]
          rw [show (a + runLower T.runs j.1 + k).succ =
            a + (runLower T.runs j.1 + k + 1) by omega]
          exact hnNext
        · simpa only [T, coordinateInterval_vertex, n, Nat.add_assoc]
    | backward =>
        have hparent : S.colour (runBoundary S.colour hchange p) = .backward :=
          hdir.trans hchild
        change (T.projectedRun j).link.path.edgeSet ⊆
          (S.projectedRun hchange p).link.path.edgeSet
        rw [T.projectedRun_edgeSet_eq_backward j hchild,
          S.projectedRun_edgeSet_eq_backward hchange p hparent]
        rintro e ⟨k, hk, rfl⟩
        let n := a + runLower T.runs j.1 + k
        refine ⟨n, ?_, ?_, ?_⟩
        · have hstep : S.coordinateIntervalGlobalLower a b hab j ≤ n := by
            change a + runLower T.runs j.1 ≤ n
            dsimp [n]
            omega
          exact (S.coordinateIntervalParentRun_lower_le hchange a b hab j).trans
            hstep
        · have hchildUpper : runLower T.runs j.1 + k + 1 ≤
              runLower T.runs (j.1 + 1) := by
            calc
              runLower T.runs j.1 + k + 1 =
                  runLower T.runs j.1 + (k + 1) := by omega
              _ ≤ runLower T.runs j.1 + (T.runs.get j).length :=
                Nat.add_le_add_left (Nat.succ_le_iff.mpr hk) _
              _ = runLower T.runs (j.1 + 1) :=
                (runLower_succ T.runs j.2).symm
          have hparentUpper :=
            S.coordinateIntervalGlobalUpper_le_parentUpper hchange a b hab j
          change a + runLower T.runs (j.1 + 1) ≤
            runBoundary S.colour hchange (p + 1) at hparentUpper
          have hnNext := (Nat.add_le_add_left hchildUpper a).trans hparentUpper
          apply Nat.lt_of_succ_le
          dsimp only [n]
          rw [show (a + runLower T.runs j.1 + k).succ =
            a + (runLower T.runs j.1 + k + 1) by omega]
          exact hnNext
        · simpa only [T, coordinateInterval_vertex, n, Nat.add_assoc]

/-- Distinct maximal runs of a bounded restriction lie in distinct maximal
runs of the original infinite stream.  Otherwise the intervening restricted
colour change would occur strictly inside one original maximal run. -/
theorem coordinateIntervalParentRun_injective
    (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (a b : Nat) (hab : a < b) :
    Function.Injective (S.coordinateIntervalParentRun hchange a b hab) := by
  let T := S.coordinateInterval a b hab
  have forwardCase : ∀ {j k : Fin T.runs.length}, j.1 < k.1 →
      S.coordinateIntervalParentRun hchange a b hab j =
        S.coordinateIntervalParentRun hchange a b hab k → j = k := by
    intro j k hjk hparent
    exfalso
    let m : Fin T.runs.length := ⟨j.1 + 1, by omega⟩
    let p := S.coordinateIntervalParentRun hchange a b hab j
    have hjm : runLower T.runs j.1 ≤ runLower T.runs m.1 :=
      runLower_mono T.runs (by simp [m])
    have hmk : runLower T.runs m.1 ≤ runLower T.runs k.1 :=
      runLower_mono T.runs (by simp [m]; omega)
    have hlo : runBoundary S.colour hchange p ≤
        S.coordinateIntervalGlobalLower a b hab m := by
      exact (S.coordinateIntervalParentRun_lower_le hchange a b hab j).trans
        (Nat.add_le_add_left hjm a)
    have hhi : S.coordinateIntervalGlobalLower a b hab m <
        runBoundary S.colour hchange (p + 1) := by
      have hk :=
        S.coordinateIntervalParentRun_start_lt_upper hchange a b hab k
      rw [← hparent] at hk
      exact (Nat.add_le_add_left hmk a).trans_lt hk
    have hmParent : S.coordinateIntervalParentRun hchange a b hab m = p := by
      apply S.runIndexAt_eq_of_mem_interval hchange
        (S.coordinateIntervalGlobalLower a b hab m) p hlo hhi
    have hjdir := S.coordinateIntervalParentRun_direction hchange a b hab j
    have hmdir := S.coordinateIntervalParentRun_direction hchange a b hab m
    rw [hmParent] at hmdir
    have heqDir : T.runDirection j = T.runDirection m :=
      hjdir.symm.trans hmdir
    have hneDir := finiteColourRuns_head_ne_head T.colours
      ⟨j.1, by
        apply Nat.lt_sub_of_add_lt
        exact m.2⟩
    apply hneDir
    change T.runDirection ⟨j.1, by omega⟩ =
      T.runDirection ⟨j.1 + 1, by omega⟩
    convert heqDir using 1 <;> apply Fin.ext <;> rfl
  intro j k hparent
  by_cases heq : j = k
  · exact heq
  have hval : j.1 ≠ k.1 := fun h ↦ heq (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hjk | hkj
  · exact forwardCase hjk hparent
  · exact (forwardCase hkj hparent.symm).symm

/-- Distinct original infinite run indices produce distinct links. -/
theorem projectedRun_link_injective (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n) :
    Function.Injective (fun i ↦ (S.projectedRun hchange i).link) := by
  intro i j hij
  have hentry := congrArg Link.entry hij
  rw [(S.projectedRun hchange i).entry_eq,
    (S.projectedRun hchange j).entry_eq,
    S.projectedRun_first hchange i,
    S.projectedRun_first hchange j] at hentry
  exact (runBoundary_strictMono S.colour hchange).injective
    (S.vertex_injective hentry)

#print axioms coordinateIntervalGlobalUpper_le_parentUpper
#print axioms coordinateInterval_projectedRun_isSubpathOf_parent
#print axioms coordinateIntervalParentRun_injective
#print axioms projectedRun_link_injective

end Erdos599.Alternating.RunCompressor.InfiniteInput
