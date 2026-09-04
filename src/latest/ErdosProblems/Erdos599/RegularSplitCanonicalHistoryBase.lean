/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularCanonicalLimitBase
import ErdosProblems.Erdos599.RegularSplitCanonicalRecursion

/-!
# Pending-tight history bases for the persistent/clean recursion

Completed target components need not be tight at later frontiers.  This
history base therefore records tightness and roof containment only for the
pending part.  At a genuine limit, never-completed threads are exact ladder
prefixes; completed threads are retained as finite target paths.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularSplitCanonicalHistoryBase

open SingularExtension SliceSpliceSource

universe u v

variable {V : Type u}

structure HistoryBase
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z A : Set V) (request : Ladder.Stage kappa → Option A)
    (i : Ladder.Stage kappa)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A) where
  baseStage : Ladder.Stage kappa
  baseStage_admissible : baseStage.1 = 0 ∨ baseStage ∈ Sigma
  index_le_base : ∀ j (hji : j < i),
    (previous j hji).stageIndex ≤ baseStage
  base : Set G.DPath
  base_warp : G.IsWarp base
  base_finite : G.HasFiniteCharacter base
  base_initial : G.initialSet base = A
  base_vertices_closed : G.vertexSet base ⊆ Z
  base_below_roof : G.vertexSet base ⊆ G.roof (L.frontier baseStage)
  base_extends : ∀ j (hji : j < i),
    G.ForwardExtension (previous j hji).row base
  base_freezes : ∀ j (hji : j < i),
    completedPart G (previous j hji).row ⊆ completedPart G base
  pending_tight : TightLinkageBetween G
    (G.initialSet (pendingPart G base)) (L.frontier baseStage)
      (pendingPart G base)
  pending_below_roof : G.vertexSet (pendingPart G base) ⊆
    G.roof (L.frontier baseStage)
  old_pending_status : ∀ p ∈ pendingPart G base,
    SliceSpliceConstructor.IsStagePrefix G L baseStage p ∨
      ∃ x ∈ RegularGlobalAdmissibleProvider.requiredPendingTerminals
        G L Sigma Z A request i previous base,
        G.terminal? p = some x

/-- Forget the whole-row fields of the initial strong base; those fields are
valid at zero but are deliberately not propagated by this recursion. -/
noncomputable def HistoryBase.zero
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    (hAeq : A = G.source ∩ Z)
    (hNorm : G.IsNormalized) (hUnhindered : G.IsUnhindered)
    (hL : L.SliceGeometry)
    (previous : ∀ j : Ladder.Stage kappa,
      j < ⟨0, hL.regular.ord_pos⟩ →
        RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A) :
    HistoryBase G L Sigma Z A request
      ⟨0, hL.regular.ord_pos⟩ previous := by
  let B := RegularCanonicalHistoryLimit.HistoryBase.zero
    (request := request) hAeq hNorm hUnhindered hL previous
  exact
    { baseStage := B.baseStage
      baseStage_admissible := B.baseStage_admissible
      index_le_base := B.index_le_base
      base := B.base
      base_warp := B.base_warp
      base_finite := B.base_finite
      base_initial := B.base_initial
      base_vertices_closed := B.base_vertices_closed
      base_below_roof := B.base_below_roof
      base_extends := B.base_extends
      base_freezes := B.base_freezes
      pending_tight := B.pending_tight
      pending_below_roof := B.pending_below_roof
      old_pending_status := B.old_pending_status }

def HistoryBase.ofPrevious
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    {j : Ladder.Stage kappa} (hji : j < i)
    (hindex : ∀ l (hli : l < i),
      (previous l hli).stageIndex ≤ (previous j hji).stageIndex)
    (hextends : ∀ l (hli : l < i),
      G.ForwardExtension (previous l hli).row (previous j hji).row)
    (hfreezes : ∀ l (hli : l < i),
      completedPart G (previous l hli).row ⊆
        completedPart G (previous j hji).row)
    (hroof : G.vertexSet (previous j hji).row ⊆
      G.roof (L.frontier (previous j hji).stageIndex)) :
    HistoryBase G L Sigma Z A request i previous where
  baseStage := (previous j hji).stageIndex
  baseStage_admissible := Or.inr (previous j hji).stageIndex_mem
  index_le_base := hindex
  base := (previous j hji).row
  base_warp := (previous j hji).isWarp
  base_finite := (previous j hji).finiteCharacter
  base_initial := (previous j hji).initialSet_eq
  base_vertices_closed := (previous j hji).vertices_closed
  base_below_roof := hroof
  base_extends := hextends
  base_freezes := hfreezes
  pending_tight := (previous j hji).pending_tight
  pending_below_roof := (previous j hji).pending_below_roof
  old_pending_status := by
    intro p hp
    rcases (previous j hji).pending_status p hp with hprefix | hpending
    · exact Or.inl hprefix
    · obtain ⟨x, hxRequest, hpx⟩ := hpending
      exact Or.inr ⟨x,
        ⟨p, hp, Or.inr ⟨j, hji, p, hp,
          ⟨x, hxRequest, hpx⟩, rfl⟩, hpx⟩,
        hpx⟩

def HistoryBase.successor
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A)
    (hprevious : ∀ j (hji : j < i),
      RegularCompletedPendingSplice.IsValidRecursiveStage request j
        (fun l hlj ↦ previous l (lt_trans hlj hji))
        (previous j hji))
    (hrowRoof : ∀ j (hji : j < i),
      G.vertexSet (previous j hji).row ⊆
        G.roof (L.frontier (previous j hji).stageIndex))
    {jOrd : Ordinal.{u}} (hi : i.1 = Order.succ jOrd) :
    HistoryBase G L Sigma Z A request i previous := by
  have hjkappa : jOrd < kappa.ord :=
    lt_trans (Order.lt_succ jOrd) (hi ▸ i.2)
  let j : Ladder.Stage kappa := ⟨jOrd, hjkappa⟩
  have hji : j < i := by
    change jOrd < i.1
    rw [hi]
    exact Order.lt_succ jOrd
  apply HistoryBase.ofPrevious hji
  · intro l hli
    have hljle : l ≤ j := by
      change l.1 ≤ jOrd
      exact Order.lt_succ_iff.mp (hi ▸ hli)
    rcases hljle.lt_or_eq with hlj | rfl
    · exact ((hprevious j hji).index_strict l hlj).le
    · exact le_rfl
  · intro l hli
    have hljle : l ≤ j := by
      change l.1 ≤ jOrd
      exact Order.lt_succ_iff.mp (hi ▸ hli)
    rcases hljle.lt_or_eq with hlj | rfl
    · exact (hprevious j hji).extends_previous l hlj
    · exact G.forwardExtension_refl _
  · intro l hli
    have hljle : l ≤ j := by
      change l.1 ≤ jOrd
      exact Order.lt_succ_iff.mp (hi ▸ hli)
    rcases hljle.lt_or_eq with hlj | rfl
    · exact (hprevious j hji).freezes_completed l hlj
    · exact Set.Subset.rfl
  · exact hrowRoof j hji

/-- A completed-or-prefix direct limit is the weak history base needed by
the next persistent/clean successor. -/
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
    (hrowRoof : ∀ t, G.vertexSet (C.stage t) ⊆
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
    HistoryBase G L Sigma Z A request i previous := by
  have hfinite : G.HasFiniteCharacter (C.limitPaths G) :=
    RegularCanonicalHistoryLimit.limitPaths_finiteCharacter_of_completed_or_stagePrefix
      hNorm C beta hclass
  have hpendingPrefix : ∀ p ∈ pendingPart G (C.limitPaths G),
      SliceSpliceConstructor.IsStagePrefix G L beta p :=
    RegularCanonicalLimitBase.pending_limitPath_isStagePrefix
      hNorm C beta hclass
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
      base_below_roof :=
        RegularCanonicalHistoryLimit.limitPaths_vertices_closed hrowRoof
      base_extends := hextends
      base_freezes := hfreezes
      pending_tight := hpendingTight
      pending_below_roof := hpendingRoof
      old_pending_status := fun p hp ↦ Or.inl (hpendingPrefix p hp) }

/-- Every certified split-canonical history has a pending-tight base for
the next successor. -/
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
    (hrowRoof : ∀ j (hji : j < i),
      G.vertexSet (previous j hji).row ⊆
        G.roof (L.frontier (previous j hji).stageIndex)) :
    Nonempty (HistoryBase G L Sigma Z (G.source ∩ Z)
      request i previous) := by
  rcases Ordinal.zero_or_succ_or_isSuccLimit i.1 with hi0 | hisucc | hilimit
  · have hi : i = ⟨0, hL.regular.ord_pos⟩ := by
      apply Subtype.ext
      exact hi0
    subst i
    exact ⟨HistoryBase.zero rfl hNorm hUnhindered hL previous⟩
  · obtain ⟨jOrd, hjOrd⟩ := hisucc
    exact ⟨HistoryBase.successor previous hprevious hrowRoof hjOrd.symm⟩
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
    have hbetaKappa : betaOrd < kappa.ord :=
      Stationary.lift_iSup_lt_ord_of_lt hL.regular hIcard
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
    have hextends : ∀ j (hji : j < i),
        G.ForwardExtension (previous j hji).row (C.limitPaths G) := by
      intro j hji
      apply RegularCanonicalLimitBase.forwardExtension_limitPaths_of_initialSet_eq
        C ⟨j, hji⟩
      exact (hinitialRow ⟨j, hji⟩).trans hinitialUnion.symm
    have hfreezes : ∀ j (hji : j < i),
        completedPart G (previous j hji).row ⊆
          completedPart G (C.limitPaths G) := by
      intro j hji
      apply RegularCanonicalHistoryLimit.completedPart_subset_limitPaths
        C ⟨j, hji⟩
      intro l hjl
      rcases hjl.lt_or_eq with hjl | rfl
      · exact (hprevious l.1 l.2).freezes_completed j hjl
      · exact Set.Subset.rfl
    have hlimitRowRoof : ∀ j : I,
        G.vertexSet (C.stage j) ⊆ G.roof (L.frontier beta) := by
      intro j
      exact (hrowRoof j.1 j.2).trans
        (G.roof_cut (hL.frontierChronology (hindex j)))
    exact ⟨historyBaseOfLimit hNorm hL Set.inter_subset_left C beta
      hbetaSigma (fun j hji ↦ (hindex ⟨j, hji⟩).le)
      hinitialUnion (fun j ↦ (previous j.1 j.2).vertices_closed)
      hlimitRowRoof hextends hfreezes hclass⟩

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
    (hrowRoof : ∀ j (hji : j < i),
      G.vertexSet (previous j hji).row ⊆
        G.roof (L.frontier (previous j hji).stageIndex)) :
    HistoryBase G L Sigma Z (G.source ∩ Z) request i previous :=
  Classical.choice (nonempty_historyBase request hNorm hUnhindered hL
    hSigma havoid i previous hprevious hrowRoof)

end RegularSplitCanonicalHistoryBase
end CardinalInduction
end Erdos599
