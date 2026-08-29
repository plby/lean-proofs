/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayFiniteInputRunLocator

/-!
# Maximal-run embedding for coordinate restrictions

A maximal run of a coordinate-restricted finite compressor lies inside one
maximal run of its parent.  This is the exact combinatorial fact needed to
transport backward-owner data to contact intervals.
-/

noncomputable section

open Set

namespace Erdos599.Alternating.RunCompressor.FiniteInput

open DirectedPath

universe u

variable {V : Type u} {D : Digraph V}

def coordinateIntervalGlobalLower (S : FiniteInput D)
    (a b : Nat) (hab : a < b) (hb : b ≤ S.lastEdge)
    (j : Fin (S.coordinateInterval a b hab hb).runs.length) : Nat :=
  a + runLower (S.coordinateInterval a b hab hb).runs j

def coordinateIntervalGlobalUpper (S : FiniteInput D)
    (a b : Nat) (hab : a < b) (hb : b ≤ S.lastEdge)
    (j : Fin (S.coordinateInterval a b hab hb).runs.length) : Nat :=
  a + runLower (S.coordinateInterval a b hab hb).runs (j.1 + 1)

theorem coordinateIntervalGlobalLower_lt_upper (S : FiniteInput D)
    (a b : Nat) (hab : a < b) (hb : b ≤ S.lastEdge)
    (j : Fin (S.coordinateInterval a b hab hb).runs.length) :
    S.coordinateIntervalGlobalLower a b hab hb j <
      S.coordinateIntervalGlobalUpper a b hab hb j := by
  let T := S.coordinateInterval a b hab hb
  have hstrict : runLower T.runs j.1 < runLower T.runs (j.1 + 1) :=
    runLower_strictMonoOn T.runs (fun r hr ↦ T.run_ne_nil hr)
      (Nat.lt_succ_self _) (Nat.succ_le_of_lt j.2)
  exact Nat.add_lt_add_left hstrict a

theorem coordinateIntervalGlobalUpper_le (S : FiniteInput D)
    (a b : Nat) (hab : a < b) (hb : b ≤ S.lastEdge)
    (j : Fin (S.coordinateInterval a b hab hb).runs.length) :
    S.coordinateIntervalGlobalUpper a b hab hb j ≤ b := by
  let T := S.coordinateInterval a b hab hb
  have h := T.runUpper_le_lastEdge j
  rw [← runLower_succ T.runs j.2] at h
  change runLower T.runs (j.1 + 1) ≤ b - a at h
  have hadd := Nat.add_le_add_left h a
  simpa only [coordinateIntervalGlobalUpper, Nat.add_sub_of_le hab.le] using hadd

theorem coordinateIntervalGlobalLower_lt_lastEdge (S : FiniteInput D)
    (a b : Nat) (hab : a < b) (hb : b ≤ S.lastEdge)
    (j : Fin (S.coordinateInterval a b hab hb).runs.length) :
    S.coordinateIntervalGlobalLower a b hab hb j < S.lastEdge := by
  have hlt := S.coordinateIntervalGlobalLower_lt_upper a b hab hb j
  have hle := S.coordinateIntervalGlobalUpper_le a b hab hb j
  omega

/-- Parent maximal run containing the first raw edge of a restricted run. -/
def coordinateIntervalParentRun (S : FiniteInput D)
    (a b : Nat) (hab : a < b) (hb : b ≤ S.lastEdge)
    (j : Fin (S.coordinateInterval a b hab hb).runs.length) :
    Fin S.runs.length :=
  S.rawRun ⟨S.coordinateIntervalGlobalLower a b hab hb j,
    S.coordinateIntervalGlobalLower_lt_lastEdge a b hab hb j⟩

theorem coordinateIntervalParentRun_lower_le (S : FiniteInput D)
    (a b : Nat) (hab : a < b) (hb : b ≤ S.lastEdge)
    (j : Fin (S.coordinateInterval a b hab hb).runs.length) :
    runLower S.runs (S.coordinateIntervalParentRun a b hab hb j) ≤
      S.coordinateIntervalGlobalLower a b hab hb j := by
  exact S.rawRun_lower_le _

theorem coordinateIntervalParentRun_start_lt_upper (S : FiniteInput D)
    (a b : Nat) (hab : a < b) (hb : b ≤ S.lastEdge)
    (j : Fin (S.coordinateInterval a b hab hb).runs.length) :
    S.coordinateIntervalGlobalLower a b hab hb j <
      runLower S.runs
        ((S.coordinateIntervalParentRun a b hab hb j).1 + 1) := by
  simpa only [coordinateIntervalParentRun] using
    S.rawRun_lt_upper
      (⟨S.coordinateIntervalGlobalLower a b hab hb j,
        S.coordinateIntervalGlobalLower_lt_lastEdge a b hab hb j⟩ :
        Fin S.lastEdge)

theorem coordinateIntervalParentRun_direction (S : FiniteInput D)
    (a b : Nat) (hab : a < b) (hb : b ≤ S.lastEdge)
    (j : Fin (S.coordinateInterval a b hab hb).runs.length) :
    S.runDirection (S.coordinateIntervalParentRun a b hab hb j) =
      (S.coordinateInterval a b hab hb).runDirection j := by
  let T := S.coordinateInterval a b hab hb
  let n : Fin S.lastEdge :=
    ⟨S.coordinateIntervalGlobalLower a b hab hb j,
      S.coordinateIntervalGlobalLower_lt_lastEdge a b hab hb j⟩
  have hparent : S.colour n =
      S.runDirection (S.coordinateIntervalParentRun a b hab hb j) := by
    exact S.rawRun_colour n
  have hpos : 0 < (T.runs.get j).length :=
    List.length_pos_iff_ne_nil.2 (T.run_ne_nil (List.get_mem _ j))
  have hchild := T.colour_run_offset j (k := 0) hpos
  have hsame : T.colour
      ⟨runLower T.runs j + 0, by
        exact lt_of_lt_of_le (Nat.add_lt_add_left hpos _)
          (T.runUpper_le_lastEdge j)⟩ = S.colour n := by
    rfl
  exact hparent.symm.trans (hsame.symm.trans hchild)

/-- A restricted maximal run cannot cross the upper boundary of its parent
maximal run: at that boundary the parent colour changes, while the
restricted run remains constant. -/
theorem coordinateIntervalGlobalUpper_le_parentUpper (S : FiniteInput D)
    (a b : Nat) (hab : a < b) (hb : b ≤ S.lastEdge)
    (j : Fin (S.coordinateInterval a b hab hb).runs.length) :
    S.coordinateIntervalGlobalUpper a b hab hb j ≤
      runLower S.runs
        ((S.coordinateIntervalParentRun a b hab hb j).1 + 1) := by
  let T := S.coordinateInterval a b hab hb
  let p := S.coordinateIntervalParentRun a b hab hb j
  by_contra hnot
  have hpLtChild : runLower S.runs (p.1 + 1) <
      S.coordinateIntervalGlobalUpper a b hab hb j :=
    Nat.lt_of_not_ge hnot
  have hpLtLast : runLower S.runs (p.1 + 1) < S.lastEdge := by
    exact hpLtChild.trans_le
      ((S.coordinateIntervalGlobalUpper_le a b hab hb j).trans hb)
  have hpNext : p.1 + 1 < S.runs.length := by
    by_contra hpnot
    have heq : p.1 + 1 = S.runs.length := by omega
    rw [heq, S.runLower_total] at hpLtLast
    exact (Nat.lt_irrefl _ hpLtLast).elim
  let q : Fin S.runs.length := ⟨p.1 + 1, hpNext⟩
  let n : Fin S.lastEdge :=
    ⟨runLower S.runs (p.1 + 1), hpLtLast⟩
  have hnRaw : S.rawRun n = q := by
    apply S.rawRun_eq_of_mem_interval n q
    · exact le_rfl
    · have hpos : 0 < (S.runs.get q).length :=
        List.length_pos_iff_ne_nil.2 (S.run_ne_nil (List.get_mem _ q))
      rw [runLower_succ S.runs q.2]
      exact Nat.lt_add_of_pos_right hpos
  have hnParentColour : S.colour n = S.runDirection q := by
    rw [← hnRaw]
    exact S.rawRun_colour n
  have hglobalLower :
      S.coordinateIntervalGlobalLower a b hab hb j ≤ n.1 := by
    simpa only [p, n] using
      (S.coordinateIntervalParentRun_start_lt_upper a b hab hb j).le
  have haN : a ≤ n.1 := by
    exact (Nat.le_add_right a _).trans hglobalLower
  let k : Fin T.lastEdge := ⟨n.1 - a, by
    change n.1 - a < b - a
    have hupper := S.coordinateIntervalGlobalUpper_le a b hab hb j
    have hnUpper : n.1 <
        S.coordinateIntervalGlobalUpper a b hab hb j := by
      simpa only [n, p] using hpLtChild
    omega⟩
  have hkLower : runLower T.runs j ≤ k.1 := by
    change runLower T.runs j ≤ n.1 - a
    change a + runLower T.runs j ≤ n.1 at hglobalLower
    omega
  have hkUpper : k.1 < runLower T.runs (j.1 + 1) := by
    change n.1 - a < runLower T.runs (j.1 + 1)
    have hnUpper : n.1 <
        S.coordinateIntervalGlobalUpper a b hab hb j := by
      simpa only [n, p] using hpLtChild
    change n.1 < a + runLower T.runs (j.1 + 1) at hnUpper
    omega
  have hnChildColour : T.colour k = T.runDirection j :=
    T.colour_eq_runDirection j hkLower hkUpper
  have hsameColour : T.colour k = S.colour n := by
    have heq : a + k.1 = n.1 := Nat.add_sub_of_le haN
    let m : Fin S.lastEdge := ⟨a + k.1, by simpa only [heq] using n.2⟩
    change S.colour m = S.colour n
    rw [show m = n from Fin.ext heq]
  have hpDir : S.runDirection p = T.runDirection j := by
    exact S.coordinateIntervalParentRun_direction a b hab hb j
  have hqDir : S.runDirection q = T.runDirection j := by
    exact hnParentColour.symm.trans (hsameColour ▸ hnChildColour)
  have hpBeforeLast : p.1 < S.runs.length - 1 := by
    exact Nat.lt_sub_of_add_lt hpNext
  have hne := finiteColourRuns_head_ne_head S.colours
    ⟨p.1, hpBeforeLast⟩
  apply hne
  change S.runDirection ⟨p.1, by omega⟩ =
    S.runDirection ⟨p.1 + 1, by omega⟩
  exact hpDir.trans hqDir.symm

end Erdos599.Alternating.RunCompressor.FiniteInput

#print axioms Erdos599.Alternating.RunCompressor.FiniteInput.coordinateIntervalGlobalUpper_le_parentUpper
