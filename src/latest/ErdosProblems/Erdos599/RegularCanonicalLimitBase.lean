/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularCanonicalHistoryLimit

/-!
# Packaging a canonical completed/pending limit base

The source-9.15 successor is installed on a finite-character base row.  At
a genuine recursion limit that row is the threadwise limit of the earlier
completed/pending rows.  The difficult history argument classifies each
thread as either already completed or the exact ladder prefix at the new
club frontier.  This file proves that this classification is sufficient to
package the direct limit as `HistoryBase`; no extra tightness or roof
invariant for the whole completed row is assumed.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularCanonicalLimitBase

open SingularExtension SliceSpliceSource

universe u v

variable {V : Type u}

/-- A completed thread remains completed in its thread limit. -/
theorem threadLimit_reachesTarget_of_completed
    {I : Type v} [LinearOrder I]
    {G : DWeb V} (hNorm : G.IsNormalized)
    (C : G.GrowingWarpChain I) (a : C.initialUnion)
    (hcompleted : ∃ i p, p ∈ C.stage i ∧ p.initial = a.1 ∧
      SliceSpliceConstructor.ReachesTarget G p) :
    SliceSpliceConstructor.ReachesTarget G (C.threadLimit G a) := by
  obtain ⟨i, p, hp, hpinitial, b, hbTarget, hpterminal⟩ := hcompleted
  have hcofinal : DirectedPath.Path.TerminalCofinal
      (C.thread G a.1) b :=
    SliceSpliceConstructor.terminalCofinal_of_thread_member_target
      hNorm C a hp hpinitial hbTarget hpterminal
  exact ⟨b, hbTarget,
    DirectedPath.Path.terminal_chainLimit_of_cofinal
      (C.thread G a.1) (C.thread_nonempty G a)
      (C.thread_isChain G a.1) hcofinal⟩

/-- Under the completed-or-prefix classification, a member of the direct
limit which is still pending is necessarily the exact prefix at `beta`. -/
theorem pending_limitPath_isStagePrefix
    {I : Type v} [LinearOrder I]
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa}
    (hNorm : G.IsNormalized) (C : G.GrowingWarpChain I)
    (beta : Ladder.Stage kappa)
    (hclass : ∀ a : C.initialUnion,
      (∃ i p, p ∈ C.stage i ∧ p.initial = a.1 ∧
        SliceSpliceConstructor.ReachesTarget G p) ∨
      SliceSpliceConstructor.IsStagePrefix G L beta
        (C.threadLimit G a)) :
    ∀ p ∈ pendingPart G (C.limitPaths G),
      SliceSpliceConstructor.IsStagePrefix G L beta p := by
  intro p hpPending
  obtain ⟨a, rfl⟩ := hpPending.1
  rcases hclass a with hcompleted | hprefix
  · exact (hpPending.2 ⟨hpPending.1,
      threadLimit_reachesTarget_of_completed hNorm C a hcompleted⟩).elim
  · exact hprefix

/-- A completed-or-prefix direct limit is the exact history base consumed
by the next canonical source-9.15 successor.  The pending roof bound is
derived path by path from normalization, the legal ladder's source-roof
law, and the exact stage-prefix boundary certificate. -/
def historyBaseOfLimit
    {I : Type v} [LinearOrder I]
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (hNorm : G.IsNormalized) (hL : L.SliceGeometry) (hA : A ⊆ G.source)
    (C : G.GrowingWarpChain I) (beta : Ladder.Stage kappa)
    (hbeta : beta ∈ Sigma)
    (hindex : ∀ j (hji : j < i),
      (previous j hji).stageIndex ≤ beta)
    (hinitial : C.initialUnion = A)
    (hclosed : ∀ t, G.vertexSet (C.stage t) ⊆ Z)
    (hbaseTight : TightLinkageBetween G A (L.frontier beta)
      (C.limitPaths G))
    (hbaseRoof : G.vertexSet (C.limitPaths G) ⊆
      G.roof (L.frontier beta))
    (hextends : ∀ j (hji : j < i),
      G.ForwardExtension (previous j hji).row (C.limitPaths G))
    (hfreezes : ∀ j (hji : j < i),
      completedPart G (previous j hji).row ⊆
        completedPart G (C.limitPaths G))
    (hclass : ∀ a : C.initialUnion,
      (∃ t p, p ∈ C.stage t ∧ p.initial = a.1 ∧
        SliceSpliceConstructor.ReachesTarget G p) ∨
      SliceSpliceConstructor.IsStagePrefix G L beta
        (C.threadLimit G a)) :
    RegularCanonicalHistoryLimit.HistoryBase
      G L Sigma Z A request i previous := by
  have hfinite : G.HasFiniteCharacter (C.limitPaths G) :=
    RegularCanonicalHistoryLimit.limitPaths_finiteCharacter_of_completed_or_stagePrefix
      hNorm C beta hclass
  have hpendingPrefix : ∀ p ∈ pendingPart G (C.limitPaths G),
      SliceSpliceConstructor.IsStagePrefix G L beta p :=
    pending_limitPath_isStagePrefix hNorm C beta hclass
  have hpendingWarp : G.IsWarp (pendingPart G (C.limitPaths G)) :=
    (C.isWarp_limitPaths G).subset Set.sdiff_subset
  have hpendingFinite : G.HasFiniteCharacter
      (pendingPart G (C.limitPaths G)) := by
    intro p hp
    exact hfinite hp.1
  have hpendingInitialSource :
      G.initialSet (pendingPart G (C.limitPaths G)) ⊆ G.source := by
    rintro x ⟨p, hp, rfl⟩
    apply hA
    rw [← hinitial, ← C.initialSet_limitPaths G]
    exact ⟨p, hp.1, rfl⟩
  have hpendingTerminal : G.terminalFrontier
      (pendingPart G (C.limitPaths G)) ⊆ L.frontier beta := by
    rintro x ⟨p, hp, hpx⟩
    obtain ⟨f, rfl, _hf, hfFrontier⟩ := hpendingPrefix p hp
    exact Option.some.inj hpx |>.symm ▸ hfFrontier
  have hpendingBoundary : MeetsOnlyAtTerminal G
      (pendingPart G (C.limitPaths G)) (L.frontier beta) := by
    intro p hp
    exact RegularCanonicalHistoryLimit.stagePrefix_meetsOnlyAtTerminal
      hL (hpendingPrefix p hp)
  have hpendingTight : TightLinkageBetween G
      (G.initialSet (pendingPart G (C.limitPaths G)))
      (L.frontier beta) (pendingPart G (C.limitPaths G)) :=
    tightLinkageBetween_of_structural hNorm hpendingInitialSource
      hpendingWarp hpendingFinite rfl hpendingTerminal hpendingBoundary
  have hsourceRoof : G.source ⊆ G.roof (L.frontier beta) := by
    rw [L.frontier_eq_essential_terminalFrontier
      hL.roofsSourceAtStages beta, G.roof_essential]
    exact hL.roofsSourceAtStages (Ladder.Stage.toExtended beta)
  have hpendingRoof : G.vertexSet (pendingPart G (C.limitPaths G)) ⊆
      G.roof (L.frontier beta) := by
    rintro x ⟨p, hp, hxp⟩
    apply G.pathSupportRoof p (L.frontier beta)
    · exact hsourceRoof (hpendingInitialSource ⟨p, hp, rfl⟩)
    · intro t ht
      exact hpendingTerminal ⟨p, hp, ht⟩
    · intro y hy
      rw [hpendingBoundary p hp y hy.1 hy.2]
      exact Set.mem_singleton y
    · exact hxp
  exact
    { baseStage := beta
      baseStage_admissible := Or.inr hbeta
      index_le_base := hindex
      base := C.limitPaths G
      base_warp := C.isWarp_limitPaths G
      base_finite := hfinite
      base_initial := (C.initialSet_limitPaths G).trans hinitial
      base_vertices_closed :=
        RegularCanonicalHistoryLimit.limitPaths_vertices_closed hclosed
      base_tight := hbaseTight
      base_below_roof := hbaseRoof
      base_extends := hextends
      base_freezes := hfreezes
      pending_tight := hpendingTight
      pending_below_roof := hpendingRoof
      old_pending_status := fun p hp ↦ Or.inl (hpendingPrefix p hp) }

/-- If every stage of a growing chain has the same initial set, each stage
is a genuine two-sided forward predecessor of the threadwise limit. -/
theorem forwardExtension_limitPaths_of_initialSet_eq
    {I : Type v} [LinearOrder I]
    {G : DWeb V} (C : G.GrowingWarpChain I) (i : I)
    (hinitial : G.initialSet (C.stage i) = C.initialUnion) :
    G.ForwardExtension (C.stage i) (C.limitPaths G) := by
  constructor
  · exact C.grows_limitPaths G i
  · intro q hq
    have hqInitialUnion : q.initial ∈ C.initialUnion := by
      rw [← C.initialSet_limitPaths G]
      exact ⟨q, hq, rfl⟩
    have hqInitialStage : q.initial ∈ G.initialSet (C.stage i) :=
      hinitial.symm ▸ hqInitialUnion
    obtain ⟨p, hp, hpinitial⟩ := hqInitialStage
    obtain ⟨r, hr, hpr⟩ := C.grows_limitPaths G i p hp
    have hrq : r = q :=
      DWeb.IsWarp.eq_of_initial_eq G (C.isWarp_limitPaths G) hr hq
        ((G.extends_initial hpr).symm.trans hpinitial)
    exact ⟨p, hp, hrq ▸ hpr⟩

/-- Every certified strict history has the canonical row on which the next
source-9.15 comparison is installed.  Zero uses the trivial source row,
successors use the immediate predecessor, and genuine limits use the
threadwise completed-or-prefix limit at the supremum of the earlier club
indices. -/
theorem nonempty_historyBase
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z : Set V}
    (request : Ladder.Stage kappa → Option ↑(G.source ∩ Z))
    (hNorm : G.IsNormalized) (hUnhindered : G.IsUnhindered)
    (hL : L.SliceGeometry)
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (havoid : Disjoint Sigma L.phi)
    (i : Ladder.Stage kappa)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload
        G L Sigma Z (G.source ∩ Z))
    (hprevious : ∀ j (hji : j < i),
      RegularCompletedPendingSplice.IsValidRecursiveStage request j
        (fun l hlj ↦ previous l (lt_trans hlj hji))
        (previous j hji))
    (hstrong : ∀ j (hji : j < i),
      TightLinkageBetween G (G.source ∩ Z)
          (L.frontier (previous j hji).stageIndex) (previous j hji).row ∧
        G.vertexSet (previous j hji).row ⊆
          G.roof (L.frontier (previous j hji).stageIndex)) :
    Nonempty (RegularCanonicalHistoryLimit.HistoryBase
      G L Sigma Z (G.source ∩ Z) request i previous) := by
  rcases Ordinal.zero_or_succ_or_isSuccLimit i.1 with hi0 | hisucc | hilimit
  · have hi : i = ⟨0, hL.regular.ord_pos⟩ := by
      apply Subtype.ext
      exact hi0
    subst i
    exact ⟨RegularCanonicalHistoryLimit.HistoryBase.zero rfl
      hNorm hUnhindered hL previous⟩
  · obtain ⟨jOrd, hjOrd⟩ := hisucc
    exact ⟨RegularCanonicalHistoryLimit.HistoryBase.successor
      previous hprevious hstrong hjOrd.symm⟩
  · let I := Set.Iio i
    let stageIndex : I → Ladder.Stage kappa := fun j ↦
      (previous j.1 j.2).stageIndex
    let C : G.GrowingWarpChain I :=
      { stage := fun j ↦ (previous j.1 j.2).row
        isWarp := fun j ↦ (previous j.1 j.2).isWarp
        grows := by
          intro j l hjl p hp
          rcases hjl.lt_or_eq with hjl | rfl
          · exact ((hprevious l.1 l.2).extends_previous j.1 hjl).1 p hp
          · exact ⟨p, hp, G.extends_refl p⟩ }
    let betaOrd : Ordinal.{u} := iSup (fun j : I ↦ (stageIndex j).1)
    have hIcard : Cardinal.lift.{u} #I < Cardinal.lift.{u + 1} kappa := by
      rw [Cardinal.lift_id'.{u, u + 1}]
      exact SliceSpliceConstructor.mk_Iio_stage_lt_lift i
    have hbetaKappa : betaOrd < kappa.ord := by
      exact Stationary.lift_iSup_lt_ord_of_lt hL.regular hIcard
        (fun j ↦ (stageIndex j).2)
    let beta : Ladder.Stage kappa := ⟨betaOrd, hbetaKappa⟩
    let : Nonempty I :=
      ⟨⟨⟨0, hL.regular.ord_pos⟩, hilimit.pos⟩⟩
    have hBdd : BddAbove (Set.range fun j : I ↦ (stageIndex j).1) := by
      refine ⟨kappa.ord, ?_⟩
      rintro _ ⟨j, rfl⟩
      exact (stageIndex j).2.le
    have hLUB : IsLUB (Set.range stageIndex) beta := by
      constructor
      · rintro _ ⟨j, rfl⟩
        exact le_ciSup hBdd j
      · intro b hb
        apply Subtype.coe_le_coe.1
        exact ciSup_le' (fun j ↦ Subtype.coe_le_coe.2 (hb ⟨j, rfl⟩))
    have hmono : Monotone stageIndex := by
      intro j l hjl
      rcases hjl.lt_or_eq with hjl | rfl
      · exact ((hprevious l.1 l.2).index_strict j.1 hjl).le
      · exact le_rfl
    have hbetaNotRange : beta ∉ Set.range stageIndex := by
      rintro ⟨j, hj⟩
      let jnext : Ladder.Stage kappa :=
        ⟨j.1.1 + 1,
          (Cardinal.isSuccLimit_ord hL.regular.aleph0_le).succ_lt j.1.2⟩
      have hjnexti : jnext < i := hilimit.succ_lt j.2
      have hjjnext : j.1 < jnext := Order.lt_succ j.1.1
      have hstrict := (hprevious jnext hjnexti).index_strict j.1 hjjnext
      have hupper := hLUB.1 ⟨⟨jnext, hjnexti⟩, rfl⟩
      rw [← hj] at hupper
      exact (not_lt_of_ge hupper) hstrict
    have hbetaLimit : Order.IsSuccLimit beta.1 := by
      have hLUBOrd : IsLUB
          (Set.range fun j : I ↦ (stageIndex j).1) betaOrd := by
        constructor
        · rintro _ ⟨j, rfl⟩
          exact le_ciSup hBdd j
        · exact fun b hb ↦ ciSup_le' (fun j ↦ hb ⟨j, rfl⟩)
      apply hLUBOrd.isSuccLimit_of_notMem (Set.range_nonempty _)
      rintro ⟨j, hj⟩
      apply hbetaNotRange
      exact ⟨j, Subtype.ext hj⟩
    have hindex : ∀ j, stageIndex j < beta := by
      intro j
      have hjle := hLUB.1 ⟨j, rfl⟩
      exact lt_of_le_of_ne hjle (fun h ↦ hbetaNotRange ⟨j, h⟩)
    have hindexSigma : ∀ j, stageIndex j ∈ Sigma := fun j ↦
      (previous j.1 j.2).stageIndex_mem
    have hrangeSigma : Set.range stageIndex ⊆ Sigma := by
      rintro _ ⟨j, rfl⟩
      exact hindexSigma j
    have hbetaSigma : beta ∈ Sigma :=
      Stationary.mem_club_of_isLUB hSigma hrangeSigma
        (Set.range_nonempty stageIndex) hLUB
    have hcofinal : ∀ b : Set.Iio beta.1,
        ∃ j, b.1 ≤ (stageIndex j).1 := by
      intro b
      obtain ⟨j, hj⟩ := (lt_ciSup_iff hBdd).1 b.2
      exact ⟨j, hj.le⟩
    have hinitialRow : ∀ j, G.initialSet (C.stage j) = G.source ∩ Z :=
      fun j ↦ (previous j.1 j.2).initialSet_eq
    have hinitialUnion : C.initialUnion = G.source ∩ Z := by
      apply Set.Subset.antisymm
      · rintro x hx
        obtain ⟨j, hxj⟩ := Set.mem_iUnion.1 hx
        rw [hinitialRow j] at hxj
        exact hxj
      · intro x hx
        let j : I := Classical.choice inferInstance
        exact Set.mem_iUnion.2 ⟨j, (hinitialRow j).symm ▸ hx⟩
    have hclass : ∀ a : C.initialUnion,
        (∃ j p, p ∈ C.stage j ∧ p.initial = a.1 ∧
          SliceSpliceConstructor.ReachesTarget G p) ∨
        SliceSpliceConstructor.IsStagePrefix G L beta
          (C.threadLimit G a) := by
      intro a
      by_cases hc : ∃ j p, p ∈ C.stage j ∧ p.initial = a.1 ∧
          SliceSpliceConstructor.ReachesTarget G p
      · exact Or.inl hc
      · right
        apply RegularCanonicalHistoryLimit.threadLimit_isStagePrefix_of_pendingStagePrefixes
          hL C stageIndex beta hbetaLimit hindex hindexSigma hSigma
          havoid hmono hLUB hcofinal hinitialRow
          (fun j ↦ (previous j.1 j.2).pending_tight)
          (fun j ↦ (previous j.1 j.2).pending_below_roof)
          a (hinitialUnion ▸ a.2) hc
        intro j p hp hpinitial
        rcases (previous j.1 j.2).pending_status p hp with
          hprefix | hpending
        · exact hprefix
        · let jnext : Ladder.Stage kappa :=
            ⟨j.1.1 + 1,
              (Cardinal.isSuccLimit_ord hL.regular.aleph0_le).succ_lt j.1.2⟩
          have hjnexti : jnext < i := hilimit.succ_lt j.2
          have hjjnext : j.1 < jnext := Order.lt_succ j.1.1
          obtain ⟨q, hqCompleted, hqinitial⟩ :=
            (hprevious jnext hjnexti).resolves_pending
              j.1 hjjnext p hp hpending
          exact (hc ⟨⟨jnext, hjnexti⟩, q, hqCompleted.1,
            hqinitial.trans hpinitial, hqCompleted.2⟩).elim
    have hboundary : ∀ j,
        MeetsOnlyAtTerminal G (C.stage j) (L.frontier beta) := by
      intro j
      exact meetsOnlyAtTerminal_of_roof_of_disjoint_strictRoof
        (hL.frontiersEssential (stageIndex j))
        (hstrong j.1 j.2).2 (hstrong j.1 j.2).1.2
        (hL.strictFrontierChronology (hindex j))
    have hterminal : ∀ a : C.initialUnion,
        ∃ b ∈ L.frontier beta,
          DirectedPath.Path.TerminalCofinal (C.thread G a.1) b := by
      intro a
      have hhit : (L.frontier beta ∩
          (C.threadLimit G a).support).Nonempty := by
        rcases hclass a with hcompleted | hprefix
        · obtain ⟨j, p, hp, hpinitial, b, hbTarget, hpterminal⟩ :=
            hcompleted
          have hbOld : b ∈ L.frontier (stageIndex j) :=
            (hstrong j.1 j.2).1.1.terminalFrontier_subset
              ⟨p, hp, hpterminal⟩
          have hbBeta : b ∈ L.frontier beta :=
            SliceSpliceConstructor.target_mem_of_mem_roof hbTarget
              (hL.frontierChronology (hindex j) hbOld)
          have hcofinal : DirectedPath.Path.TerminalCofinal
              (C.thread G a.1) b :=
            SliceSpliceConstructor.terminalCofinal_of_thread_member_target
              hNorm C a hp hpinitial hbTarget hpterminal
          have hlimitTerminal : G.terminal? (C.threadLimit G a) = some b :=
            DirectedPath.Path.terminal_chainLimit_of_cofinal
              (C.thread G a.1) (C.thread_nonempty G a)
              (C.thread_isChain G a.1) hcofinal
          exact ⟨b, hbBeta, G.terminal_mem_support hlimitTerminal⟩
        · obtain ⟨f, hlimit, _hf, hfinish⟩ := hprefix
          refine ⟨f.finish, hfinish, ?_⟩
          rw [hlimit]
          exact f.finish_mem_support
      obtain ⟨b, hbBeta, hbLimit⟩ := hhit
      exact ⟨b, hbBeta,
        SliceSpliceConstructor.terminalCofinal_of_threadLimit_meets_boundary
          C hboundary a hbBeta hbLimit⟩
    have hbaseTight : TightLinkageBetween G (G.source ∩ Z)
        (L.frontier beta) (C.limitPaths G) :=
      tightLinkageBetween_limitPaths_of_terminalCofinal C hNorm
        Set.inter_subset_left hinitialUnion hterminal hboundary
    have hbaseRoof : G.vertexSet (C.limitPaths G) ⊆
        G.roof (L.frontier beta) := by
      rw [C.vertexSet_limitPaths G]
      rintro x hx
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.1 hx
      exact G.roof_cut (hL.frontierChronology (hindex j))
        ((hstrong j.1 j.2).2 hxj)
    have hextends : ∀ j (hji : j < i),
        G.ForwardExtension (previous j hji).row (C.limitPaths G) := by
      intro j hji
      apply forwardExtension_limitPaths_of_initialSet_eq C ⟨j, hji⟩
      exact (hinitialRow ⟨j, hji⟩).trans hinitialUnion.symm
    have hfreezes : ∀ j (hji : j < i),
        completedPart G (previous j hji).row ⊆
          completedPart G (C.limitPaths G) := by
      intro j hji
      apply RegularCanonicalHistoryLimit.completedPart_subset_limitPaths
        C ⟨j, hji⟩
      intro l hjl
      rcases hjl.lt_or_eq with hjl | hjl
      · exact (hprevious l.1 l.2).freezes_completed j hjl
      · subst l
        exact Set.Subset.rfl
    exact ⟨historyBaseOfLimit hNorm hL Set.inter_subset_left C beta
      hbetaSigma (fun j hji ↦ (hindex ⟨j, hji⟩).le)
      hinitialUnion (fun j ↦ (previous j.1 j.2).vertices_closed)
      hbaseTight hbaseRoof hextends hfreezes hclass⟩

/-- Canonical choice of the history base. -/
noncomputable def historyBase
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z : Set V}
    (request : Ladder.Stage kappa → Option ↑(G.source ∩ Z))
    (hNorm : G.IsNormalized) (hUnhindered : G.IsUnhindered)
    (hL : L.SliceGeometry)
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (havoid : Disjoint Sigma L.phi)
    (i : Ladder.Stage kappa)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload
        G L Sigma Z (G.source ∩ Z))
    (hprevious : ∀ j (hji : j < i),
      RegularCompletedPendingSplice.IsValidRecursiveStage request j
        (fun l hlj ↦ previous l (lt_trans hlj hji))
        (previous j hji))
    (hstrong : ∀ j (hji : j < i),
      TightLinkageBetween G (G.source ∩ Z)
          (L.frontier (previous j hji).stageIndex) (previous j hji).row ∧
        G.vertexSet (previous j hji).row ⊆
          G.roof (L.frontier (previous j hji).stageIndex)) :
    RegularCanonicalHistoryLimit.HistoryBase
      G L Sigma Z (G.source ∩ Z) request i previous :=
  Classical.choice (nonempty_historyBase request hNorm hUnhindered hL
    hSigma havoid i previous hprevious hstrong)

end RegularCanonicalLimitBase
end CardinalInduction
end Erdos599
