/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayFiniteCoordinateRunEmbedding

/-!
# Restricted maximal runs as literal parent subpaths

The numerical run embedding upgrades to directed-path containment.  The
same construction also shows that two restricted runs of the same direction
cannot map to one parent run.
-/

noncomputable section

open Set

namespace Erdos599.Alternating.RunCompressor.FiniteInput

open DirectedPath

universe u

variable {V : Type u} {D : Digraph V}

theorem coordinateInterval_projectedRun_isSubpathOf_parent
    (S : FiniteInput D)
    (a b : Nat) (hab : a < b) (hb : b ≤ S.lastEdge)
    (j : Fin (S.coordinateInterval a b hab hb).runs.length) :
    ((S.coordinateInterval a b hab hb).projectedRun j).link.path.IsSubpathOf
      (.inl (S.projectedRun
        (S.coordinateIntervalParentRun a b hab hb j)).link.path) := by
  let T := S.coordinateInterval a b hab hb
  let p := S.coordinateIntervalParentRun a b hab hb j
  have hdir : S.runDirection p = T.runDirection j :=
    S.coordinateIntervalParentRun_direction a b hab hb j
  constructor
  · change (T.projectedRun j).link.path.support ⊆
      (S.projectedRun p).link.path.support
    rw [T.projectedRun_support j, S.projectedRun_support p]
    rintro x ⟨n, hn, rfl⟩
    refine ⟨a + n, ⟨?_, ?_⟩, rfl⟩
    · have hlo := S.coordinateIntervalParentRun_lower_le a b hab hb j
      have hstep : S.coordinateIntervalGlobalLower a b hab hb j ≤
          a + n := by
        change a + runLower T.runs j ≤ a + n
        exact Nat.add_le_add_left hn.1 a
      exact hlo.trans hstep
    · have hhi :=
        S.coordinateIntervalGlobalUpper_le_parentUpper a b hab hb j
      have hstep : a + n ≤
          S.coordinateIntervalGlobalUpper a b hab hb j := by
        change a + n ≤ a + runLower T.runs (j.1 + 1)
        exact Nat.add_le_add_left hn.2 a
      exact hstep.trans hhi
  · cases hchild : T.runDirection j with
    | forward =>
        have hparent : S.runDirection p = .forward := hdir.trans hchild
        change (T.projectedRun j).link.path.edgeSet ⊆
          (S.projectedRun p).link.path.edgeSet
        rw [T.projectedRun_edgeSet_eq_forward j hchild,
          S.projectedRun_edgeSet_eq_forward p hparent]
        rintro e ⟨k, hk, rfl⟩
        let n := a + runLower T.runs j.1 + k
        refine ⟨n - runLower S.runs p.1, ?_, ?_⟩
        · have hlo := S.coordinateIntervalParentRun_lower_le a b hab hb j
          have hhi :=
            S.coordinateIntervalGlobalUpper_le_parentUpper a b hab hb j
          have hchildUpper : runLower T.runs j.1 + k + 1 ≤
              runLower T.runs (j.1 + 1) := by
            calc
              runLower T.runs j.1 + k + 1 =
                  runLower T.runs j.1 + (k + 1) := by omega
              _ ≤ runLower T.runs j.1 + (T.runs.get j).length :=
                Nat.add_le_add_left (Nat.succ_le_iff.mpr hk) _
              _ = runLower T.runs (j.1 + 1) :=
                (runLower_succ T.runs j.2).symm
          have hnNextLe : n + 1 ≤ runLower S.runs (p.1 + 1) := by
            apply le_trans _ hhi
            simpa only [n, coordinateIntervalGlobalUpper, T, Nat.add_assoc]
              using Nat.add_le_add_left hchildUpper a
          have hnNextLe' : n + 1 ≤
              runLower S.runs p.1 + (S.runs.get p).length := by
            simpa only [runLower_succ S.runs p.2] using hnNextLe
          have hglobalN :
              S.coordinateIntervalGlobalLower a b hab hb j ≤ n := by
            change a + runLower T.runs j.1 ≤ n
            dsimp [n]
            omega
          have hle : runLower S.runs p.1 ≤ n := hlo.trans hglobalN
          omega
        · have hlo := S.coordinateIntervalParentRun_lower_le a b hab hb j
          have hle : runLower S.runs p.1 ≤ n := by
            apply hlo.trans
            change a + runLower T.runs j.1 ≤ n
            dsimp [n]
            omega
          have heq : runLower S.runs p.1 +
              (n - runLower S.runs p.1) = n := Nat.add_sub_of_le hle
          apply Prod.ext
          · apply congrArg S.vertex
            change a + (runLower T.runs j.1 + k) =
              runLower S.runs p.1 + (n - runLower S.runs p.1)
            dsimp [n]
            omega
          · apply congrArg S.vertex
            change a + (runLower T.runs j.1 + (k + 1)) =
              runLower S.runs p.1 + (n - runLower S.runs p.1) + 1
            dsimp [n]
            omega
    | backward =>
        have hparent : S.runDirection p = .backward := hdir.trans hchild
        change (T.projectedRun j).link.path.edgeSet ⊆
          (S.projectedRun p).link.path.edgeSet
        rw [T.projectedRun_edgeSet_eq_backward j hchild,
          S.projectedRun_edgeSet_eq_backward p hparent]
        rintro e ⟨k, hk, rfl⟩
        let n := a + runLower T.runs j.1 + k
        refine ⟨n - runLower S.runs p.1, ?_, ?_⟩
        · have hlo := S.coordinateIntervalParentRun_lower_le a b hab hb j
          have hhi :=
            S.coordinateIntervalGlobalUpper_le_parentUpper a b hab hb j
          have hchildUpper : runLower T.runs j.1 + k + 1 ≤
              runLower T.runs (j.1 + 1) := by
            calc
              runLower T.runs j.1 + k + 1 =
                  runLower T.runs j.1 + (k + 1) := by omega
              _ ≤ runLower T.runs j.1 + (T.runs.get j).length :=
                Nat.add_le_add_left (Nat.succ_le_iff.mpr hk) _
              _ = runLower T.runs (j.1 + 1) :=
                (runLower_succ T.runs j.2).symm
          have hnNextLe : n + 1 ≤ runLower S.runs (p.1 + 1) := by
            apply le_trans _ hhi
            simpa only [n, coordinateIntervalGlobalUpper, T, Nat.add_assoc]
              using Nat.add_le_add_left hchildUpper a
          have hnNextLe' : n + 1 ≤
              runLower S.runs p.1 + (S.runs.get p).length := by
            simpa only [runLower_succ S.runs p.2] using hnNextLe
          have hglobalN :
              S.coordinateIntervalGlobalLower a b hab hb j ≤ n := by
            change a + runLower T.runs j.1 ≤ n
            dsimp [n]
            omega
          have hle : runLower S.runs p.1 ≤ n := hlo.trans hglobalN
          omega
        · have hlo := S.coordinateIntervalParentRun_lower_le a b hab hb j
          have hle : runLower S.runs p.1 ≤ n := by
            apply hlo.trans
            change a + runLower T.runs j.1 ≤ n
            dsimp [n]
            omega
          have heq : runLower S.runs p.1 +
              (n - runLower S.runs p.1) = n := Nat.add_sub_of_le hle
          apply Prod.ext
          · apply congrArg S.vertex
            change a + (runLower T.runs j.1 + (k + 1)) =
              runLower S.runs p.1 + (n - runLower S.runs p.1) + 1
            dsimp [n]
            omega
          · apply congrArg S.vertex
            change a + (runLower T.runs j.1 + k) =
              runLower S.runs p.1 + (n - runLower S.runs p.1)
            dsimp [n]
            omega

/-- On runs of one fixed direction, the parent-run map is injective. -/
theorem coordinateIntervalParentRun_eq_imp_eq_of_direction
    (S : FiniteInput D)
    (a b : Nat) (hab : a < b) (hb : b ≤ S.lastEdge)
    {j k : Fin (S.coordinateInterval a b hab hb).runs.length}
    (hparent : S.coordinateIntervalParentRun a b hab hb j =
      S.coordinateIntervalParentRun a b hab hb k)
    (hdir : (S.coordinateInterval a b hab hb).runDirection j =
      (S.coordinateInterval a b hab hb).runDirection k) :
    j = k := by
  let T := S.coordinateInterval a b hab hb
  have forwardCase : ∀ {r s : Fin T.runs.length}, r.1 < s.1 →
      S.coordinateIntervalParentRun a b hab hb r =
        S.coordinateIntervalParentRun a b hab hb s →
      T.runDirection r = T.runDirection s → r = s := by
    intro r s hrs hrsParent hrsDir
    exfalso
    have hrNext : r.1 + 1 < s.1 := by
      by_contra hnot
      have heq : s.1 = r.1 + 1 := by omega
      have hrSuccLt : r.1 + 1 < T.runs.length := by
        rw [← heq]
        exact s.2
      have hneDir := finiteColourRuns_head_ne_head T.colours
        ⟨r.1, by
          exact Nat.lt_sub_of_add_lt hrSuccLt⟩
      apply hneDir
      change T.runDirection ⟨r.1, by omega⟩ =
        T.runDirection ⟨r.1 + 1, by omega⟩
      have hsFin : s = ⟨r.1 + 1, hrSuccLt⟩ := Fin.ext heq
      rw [hsFin] at hrsDir
      exact hrsDir
    let m : Fin T.runs.length := ⟨r.1 + 1, by omega⟩
    have hLower : runLower S.runs
          (S.coordinateIntervalParentRun a b hab hb r) ≤
        S.coordinateIntervalGlobalLower a b hab hb m := by
      have hrlo := S.coordinateIntervalParentRun_lower_le a b hab hb r
      have hmono := runLower_mono T.runs
        (show r.1 ≤ m.1 by
          change r.1 ≤ r.1 + 1
          omega)
      exact hrlo.trans (Nat.add_le_add_left hmono a)
    have hUpper : S.coordinateIntervalGlobalLower a b hab hb m <
        runLower S.runs
          ((S.coordinateIntervalParentRun a b hab hb r).1 + 1) := by
      have hstrict := runLower_strictMonoOn T.runs
        (fun q hq ↦ T.run_ne_nil hq) hrNext
        (Nat.le_of_lt s.2)
      have hsUpper :=
        S.coordinateIntervalParentRun_start_lt_upper a b hab hb s
      rw [← hrsParent] at hsUpper
      exact (Nat.add_lt_add_left hstrict a).trans hsUpper
    let n : Fin S.lastEdge :=
      ⟨S.coordinateIntervalGlobalLower a b hab hb m,
        S.coordinateIntervalGlobalLower_lt_lastEdge a b hab hb m⟩
    have hnRaw : S.rawRun n =
        S.coordinateIntervalParentRun a b hab hb r := by
      exact S.rawRun_eq_of_mem_interval n _ hLower hUpper
    have hmParent : S.coordinateIntervalParentRun a b hab hb m =
        S.coordinateIntervalParentRun a b hab hb r := by
      exact hnRaw
    have hrDirection :=
      S.coordinateIntervalParentRun_direction a b hab hb r
    have hmDirection :=
      S.coordinateIntervalParentRun_direction a b hab hb m
    rw [hmParent] at hmDirection
    have heqDirection : T.runDirection r = T.runDirection m :=
      hrDirection.symm.trans hmDirection
    have hneDir := finiteColourRuns_head_ne_head T.colours
      ⟨r.1, by
        apply Nat.lt_sub_of_add_lt
        exact m.2⟩
    apply hneDir
    change T.runDirection ⟨r.1, by omega⟩ =
      T.runDirection ⟨r.1 + 1, by omega⟩
    exact heqDirection
  by_cases heq : j = k
  · exact heq
  have hval : j.1 ≠ k.1 := fun h ↦ heq (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hjk | hkj
  · exact forwardCase hjk hparent hdir
  · exact (forwardCase hkj hparent.symm hdir.symm).symm

end Erdos599.Alternating.RunCompressor.FiniteInput

#print axioms Erdos599.Alternating.RunCompressor.FiniteInput.coordinateInterval_projectedRun_isSubpathOf_parent
#print axioms Erdos599.Alternating.RunCompressor.FiniteInput.coordinateIntervalParentRun_eq_imp_eq_of_direction
