/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularCanonicalAdmissibleProvider
import ErdosProblems.Erdos599.RegularCanonicalHistoryDependencies

/-!
# Limit rows for the canonical regular recursion

The completed/pending recursion is analyzed thread by thread.  A thread
which was completed has a target terminal cofinally.  Every other thread
consists of exact ladder prefixes; source Lemma 7.28 identifies its direct
limit with the prefix at the limiting club frontier.  Target vertices on an
earlier ladder frontier persist to every later frontier, so the resulting
whole row retains the stronger tight/roofed invariant used by the source's
global comparison argument.

This file packages the representation-independent parts of that argument.
It is deliberately separate from the successor slice construction.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularCanonicalHistoryLimit

open SingularExtension SliceSpliceSource

universe u v

variable {V : Type u}

/-- An exact accumulated-ladder prefix meets its declared frontier only at
its terminal.  The proof uses the warp property of the essential part, not
any right-tightness assumption on a larger family containing the prefix. -/
theorem stagePrefix_meetsOnlyAtTerminal
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} (hL : L.SliceGeometry)
    {alpha : Ladder.Stage kappa} {p : G.DPath}
    (hp : SliceSpliceConstructor.IsStagePrefix G L alpha p) :
    ∀ x ∈ p.support, x ∈ L.frontier alpha → G.terminal? p = some x := by
  obtain ⟨f, rfl, hf, hfinish⟩ := hp
  intro x hxf hxfrontier
  have hxterminal : x ∈
      G.terminalFrontier (G.essentialWarpPart (L.warpAt alpha)) := by
    rw [L.frontier_eq_essential_terminalFrontier
      hL.roofsSourceAtStages alpha,
      ← G.terminalFrontier_essentialWarpPart] at hxfrontier
    exact hxfrontier
  obtain ⟨q, hq, hqterm⟩ := hxterminal
  have hqf : q = (Sum.inl f : G.DPath) := by
    by_contra hne
    exact Set.disjoint_left.1
      (DWeb.IsWarp.essentialWarpPart
        G (hL.warpStages (Ladder.Stage.toExtended alpha)) hq hf hne)
      (G.terminal_mem_support hqterm) hxf
  rw [hqf] at hqterm
  exact hqterm

/-- If every thread of a growing warp has either reached the ambient target
or is an exact finite ladder prefix at the limiting stage, then the raw
threadwise limit has finite character.  This is the finiteness half of the
completed/pending limit construction. -/
theorem limitPaths_finiteCharacter_of_completed_or_stagePrefix
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
    G.HasFiniteCharacter (C.limitPaths G) := by
  intro p hp
  obtain ⟨a, rfl⟩ := hp
  rcases hclass a with hcompleted | hprefix
  · obtain ⟨i, q, hqi, hqinitial, b, hbTarget, hqterminal⟩ :=
      hcompleted
    have hcofinal : DirectedPath.Path.TerminalCofinal
        (C.thread G a.1) b :=
      SliceSpliceConstructor.terminalCofinal_of_thread_member_target
        hNorm C a hqi hqinitial hbTarget hqterminal
    have hterminal : G.terminal? (C.threadLimit G a) = some b :=
      DirectedPath.Path.terminal_chainLimit_of_cofinal
        (C.thread G a.1) (C.thread_nonempty G a)
        (C.thread_isChain G a.1) hcofinal
    generalize heq : C.threadLimit G a = r at hterminal ⊢
    rcases r with f | ray
    · exact ⟨f, rfl⟩
    · simp at hterminal
  · obtain ⟨f, hlimit, _hf, _hfinish⟩ := hprefix
    exact ⟨f, hlimit⟩

/-- The direct-limit carrier stays in every stagewise closed set. -/
theorem limitPaths_vertices_closed
    {I : Type v} [LinearOrder I]
    {G : DWeb V} {C : G.GrowingWarpChain I} {Z : Set V}
    (hclosed : ∀ i, G.vertexSet (C.stage i) ⊆ Z) :
    G.vertexSet (C.limitPaths G) ⊆ Z :=
  SliceSpliceSource.vertexSet_limitPaths_subset_of_stages hclosed

/-- A completed member of an earlier row remains a completed member of the
threadwise limit. -/
theorem completedPart_subset_limitPaths
    {I : Type v} [LinearOrder I] [Nonempty I] [IsDirectedOrder I]
    {G : DWeb V}
    (C : G.GrowingWarpChain I) (i : I)
    (hpersist : ∀ j, i ≤ j →
      completedPart G (C.stage i) ⊆ completedPart G (C.stage j)) :
    completedPart G (C.stage i) ⊆ completedPart G (C.limitPaths G) := by
  intro p hp
  refine ⟨C.mem_limitPaths_of_tail i hp.1 ?_, hp.2⟩
  intro j hij
  exact (hpersist j hij hp).1

/-- `chainLimit` is independent of the proof objects witnessing nonemptiness
and linearity, and hence respects equality of its underlying path set. -/
theorem chainLimit_eq_of_set_eq
    {G : DWeb V} {C D : Set G.DPath}
    (hCD : C = D) (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hCchain : IsChain DirectedPath.Path.Extends C)
    (hDchain : IsChain DirectedPath.Path.Extends D) :
    DirectedPath.Path.chainLimit C hCne hCchain =
      DirectedPath.Path.chainLimit D hDne hDchain := by
  subst D
  rfl

/-- Removing the already completed components of a tight row preserves a
tight linkage on the remaining initial coordinates.  This elementary
restriction is used at the zero and limit bases of the canonical recursion. -/
theorem pendingPart_tightLinkageBetween
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A C : Set V} {W : Set G.DPath}
    (hA : A ⊆ G.source) (hW : TightLinkageBetween G A C W) :
    TightLinkageBetween G (G.initialSet (pendingPart G W)) C
      (pendingPart G W) := by
  apply tightLinkageBetween_of_structural hNorm
  · intro x hx
    apply hA
    rw [← hW.1.initialSet_eq]
    obtain ⟨p, hp, rfl⟩ := hx
    exact ⟨p, hp.1, rfl⟩
  · exact hW.1.isWarp.subset Set.sdiff_subset
  · intro p hp
    exact hW.1.finiteCharacter hp.1
  · rfl
  · intro x hx
    obtain ⟨p, hp, hpx⟩ := hx
    exact hW.1.terminalFrontier_subset ⟨p, hp.1, hpx⟩
  · intro p hp x hxp hxC
    exact hW.2 p hp.1 x hxp hxC

/-! ## The row on which a source-9.15 successor is installed -/

/-- The history-dependent base row needed by the global comparison-stage
constructor.  At zero it is the canonical trivial row.  At a successor it
is the preceding installed row.  At a genuine limit it is the threadwise
limit of the certified history.  The disjunction on `baseStage` is exactly
what distinguishes the special first-slice theorem from the club-indexed
9.15 successor theorem. -/
structure HistoryBase
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z A : Set V) (request : Ladder.Stage kappa → Option A)
    (i : Ladder.Stage kappa)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A) where
  baseStage : Ladder.Stage kappa
  baseStage_admissible :
    baseStage.1 = 0 ∨ baseStage ∈ Sigma
  index_le_base : ∀ j (hji : j < i),
    (previous j hji).stageIndex ≤ baseStage
  base : Set G.DPath
  base_warp : G.IsWarp base
  base_finite : G.HasFiniteCharacter base
  base_initial : G.initialSet base = A
  base_vertices_closed : G.vertexSet base ⊆ Z
  /-- The source proof keeps the whole displayed row tight at its installed
  frontier.  Completed target components remain on every later frontier;
  retaining this stronger invariant makes the next full tracked slice an
  honest comparison warp. -/
  base_tight : TightLinkageBetween G A (L.frontier baseStage) base
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

/-- The genuine zero history has the canonical trivial source row as its
9.15 base.  There are no earlier rows to extend or freeze. -/
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
  subst A
  let z : Ladder.Stage kappa := ⟨0, hL.regular.ord_pos⟩
  let S0 := SliceSpliceConstructor.initialTrackedPartialState_zero
    hNorm hUnhindered hL (Z := Z)
  refine
    { baseStage := z
      baseStage_admissible := Or.inl rfl
      index_le_base := ?_
      base := S0.family
      base_warp := S0.tight.1.isWarp
      base_finite := S0.tight.1.finiteCharacter
      base_initial := S0.tight.1.initialSet_eq
      base_vertices_closed := S0.vertices_closed
      base_tight := S0.tight
      base_below_roof := S0.below_roof
      base_extends := ?_
      base_freezes := ?_
      pending_tight := pendingPart_tightLinkageBetween hNorm
        Set.inter_subset_left S0.tight
      pending_below_roof := ?_
      old_pending_status := ?_ }
  · intro j hj
    exact (not_lt_of_ge (bot_le : (0 : Ordinal) ≤ j.1) hj).elim
  · intro j hj
    exact (not_lt_of_ge (bot_le : (0 : Ordinal) ≤ j.1) hj).elim
  · intro j hj
    exact (not_lt_of_ge (bot_le : (0 : Ordinal) ≤ j.1) hj).elim
  · rintro x ⟨p, hp, hxp⟩
    exact S0.below_roof ⟨p, hp.1, hxp⟩
  · intro p hp
    rcases S0.status p hp.1 with hcomplete | hprefix | hpending
    · exact (hp.2 ⟨hp.1, hcomplete⟩).elim
    · exact Or.inl hprefix
    · obtain ⟨x, hx, _⟩ := hpending
      exact hx.elim

/-- Any certified row which dominates the whole strict history is already a
valid successor base.  In particular the immediate predecessor supplies
this datum at a successor recursion index. -/
def HistoryBase.ofPrevious
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    {j : Ladder.Stage kappa} (hji : j < i)
    (hbaseTight : TightLinkageBetween G A
      (L.frontier (previous j hji).stageIndex) (previous j hji).row)
    (hbaseRoof : G.vertexSet (previous j hji).row ⊆
      G.roof (L.frontier (previous j hji).stageIndex))
    (hindex : ∀ l (hli : l < i),
      (previous l hli).stageIndex ≤ (previous j hji).stageIndex)
    (hextends : ∀ l (hli : l < i),
      G.ForwardExtension (previous l hli).row (previous j hji).row)
    (hfreezes : ∀ l (hli : l < i),
      completedPart G (previous l hli).row ⊆
        completedPart G (previous j hji).row) :
    HistoryBase G L Sigma Z A request i previous where
  baseStage := (previous j hji).stageIndex
  baseStage_admissible := Or.inr (previous j hji).stageIndex_mem
  index_le_base := hindex
  base := (previous j hji).row
  base_warp := (previous j hji).isWarp
  base_finite := (previous j hji).finiteCharacter
  base_initial := (previous j hji).initialSet_eq
  base_vertices_closed := (previous j hji).vertices_closed
  base_tight := hbaseTight
  base_below_roof := hbaseRoof
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

/-- At a successor recursion index the immediate predecessor dominates the
entire strict history, both for forward extension and for literal completed
components. -/
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
    (hstrong : ∀ j (hji : j < i),
      TightLinkageBetween G A (L.frontier (previous j hji).stageIndex)
          (previous j hji).row ∧
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
  apply HistoryBase.ofPrevious hji (hstrong j hji).1 (hstrong j hji).2
  · intro l hli
    have hljle : l ≤ j := by
      change l.1 ≤ jOrd
      exact Order.lt_succ_iff.mp (hi ▸ hli)
    rcases hljle.lt_or_eq with hlj | hlj
    · exact ((hprevious j hji).index_strict l hlj).le
    · subst l
      exact le_rfl
  · intro l hli
    have hljle : l ≤ j := by
      change l.1 ≤ jOrd
      exact Order.lt_succ_iff.mp (hi ▸ hli)
    rcases hljle.lt_or_eq with hlj | hlj
    · exact (hprevious j hji).extends_previous l hlj
    · subst l
      exact G.forwardExtension_refl _
  · intro l hli
    have hljle : l ≤ j := by
      change l.1 ≤ jOrd
      exact Order.lt_succ_iff.mp (hi ▸ hli)
    rcases hljle.lt_or_eq with hlj | hlj
    · exact (hprevious j hji).freezes_completed l hlj
    · subst l
      exact Set.Subset.rfl

/-- The ordinary thread lemma specialized to completed/pending rows.  The
whole rows are not frontier-tight because completed target paths are frozen.
For a thread which never completes, restricting every row to its one initial
coordinate gives an honest chain of tight pending linkages, so the existing
closed-hit-stage theorem applies without any false tightness assertion about
the completed part. -/
theorem threadLimit_isStagePrefix_of_pendingStagePrefixes
    {I : Type v} [LinearOrder I] [Nonempty I]
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {A : Set V}
    (hL : L.SliceGeometry)
    (C : G.GrowingWarpChain I)
    (stageIndex : I → Ladder.Stage kappa)
    (beta : Ladder.Stage kappa)
    (hbeta : Order.IsSuccLimit beta.1)
    (hindex : ∀ i, stageIndex i < beta)
    (hindexSigma : ∀ i, stageIndex i ∈ Sigma)
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (havoid : Disjoint Sigma L.phi)
    (hmono : Monotone stageIndex)
    (hLUB : IsLUB (Set.range stageIndex) beta)
    (hcofinal : ∀ j : Set.Iio beta.1,
      ∃ i, j.1 ≤ (stageIndex i).1)
    (hinitial : ∀ i, G.initialSet (C.stage i) = A)
    (hpending : ∀ i, TightLinkageBetween G
      (G.initialSet (pendingPart G (C.stage i)))
      (L.frontier (stageIndex i)) (pendingPart G (C.stage i)))
    (hroof : ∀ i, G.vertexSet (pendingPart G (C.stage i)) ⊆
      G.roof (L.frontier (stageIndex i)))
    (a : C.initialUnion) (haA : a.1 ∈ A)
    (hnotCompleted : ¬ ∃ i p, p ∈ C.stage i ∧ p.initial = a.1 ∧
      SliceSpliceConstructor.ReachesTarget G p)
    (hprefix : ∀ i p, p ∈ pendingPart G (C.stage i) →
      p.initial = a.1 →
      SliceSpliceConstructor.IsStagePrefix G L (stageIndex i) p) :
    SliceSpliceConstructor.IsStagePrefix G L beta
      (C.threadLimit G a) := by
  have hnotCompletedAt : ∀ i p, p ∈ C.stage i → p.initial = a.1 →
      p ∉ completedPart G (C.stage i) := by
    intro i p hp hpinitial hpcompleted
    exact hnotCompleted ⟨i, p, hp, hpinitial, hpcompleted.2⟩
  have haPendingInitial : ∀ i,
      a.1 ∈ G.initialSet (pendingPart G (C.stage i)) := by
    intro i
    have haRow : a.1 ∈ G.initialSet (C.stage i) := by
      rw [hinitial i]
      exact haA
    obtain ⟨p, hp, hpinitial⟩ := haRow
    exact ⟨p, ⟨hp, hnotCompletedAt i p hp hpinitial⟩, hpinitial⟩
  let Ca : G.GrowingWarpChain I :=
    { stage := fun i ↦ initialRestriction G
        (pendingPart G (C.stage i)) {a.1}
      isWarp := fun i ↦ (hpending i).1.isWarp.subset
        (fun _ hp ↦ hp.1)
      grows := by
        intro i j hij p hp
        obtain ⟨q, hq, hpq⟩ := C.grows hij p hp.1.1
        have hqinitial : q.initial = a.1 :=
          (G.extends_initial hpq).symm.trans
            (Set.mem_singleton_iff.1 hp.2)
        have hqpending : q ∈ pendingPart G (C.stage j) :=
          ⟨hq, hnotCompletedAt j q hq hqinitial⟩
        exact ⟨q, ⟨hqpending, Set.mem_singleton_iff.2 hqinitial⟩, hpq⟩ }
  have hsingleSubset : ∀ i,
      {a.1} ⊆ G.initialSet (pendingPart G (C.stage i)) := by
    intro i x hx
    exact Set.mem_singleton_iff.1 hx ▸ haPendingInitial i
  have htightCa : ∀ i, TightLinkageBetween G {a.1}
      (L.frontier (stageIndex i)) (Ca.stage i) := by
    intro i
    let hlink := isLinkageBetween_initialRestriction
      (hpending i).1 (hsingleSubset i)
    refine ⟨hlink, ?_⟩
    intro p hp x hxp hxfrontier
    exact (hpending i).2 p hp.1 x hxp hxfrontier
  have hroofCa : ∀ i, G.vertexSet (Ca.stage i) ⊆
      G.roof (L.frontier (stageIndex i)) := by
    intro i x hx
    exact hroof i (vertexSet_initialRestriction_subset
      G (pendingPart G (C.stage i)) {a.1} hx)
  let i0 : I := Classical.choice inferInstance
  have haCa : a.1 ∈ Ca.initialUnion := by
    apply Set.mem_iUnion.2
    refine ⟨i0, ?_⟩
    rw [(htightCa i0).1.initialSet_eq]
    exact Set.mem_singleton a.1
  let aCa : Ca.initialUnion := ⟨a.1, haCa⟩
  have hthread : Ca.thread G a.1 = C.thread G a.1 := by
    ext p
    constructor
    · rintro ⟨i, hp, hpinitial⟩
      exact ⟨i, hp.1.1, hpinitial⟩
    · rintro ⟨i, hp, hpinitial⟩
      exact ⟨i,
        ⟨⟨hp, hnotCompletedAt i p hp hpinitial⟩,
          Set.mem_singleton_iff.2 hpinitial⟩,
        hpinitial⟩
  have hlimit : Ca.threadLimit G aCa = C.threadLimit G a := by
    unfold DWeb.GrowingWarpChain.threadLimit
    exact chainLimit_eq_of_set_eq hthread
      (Ca.thread_nonempty G aCa) (C.thread_nonempty G a)
      (Ca.thread_isChain G a.1) (C.thread_isChain G a.1)
  have hprefixCa : ∀ i p, p ∈ Ca.stage i → p.initial = aCa.1 →
      SliceSpliceConstructor.IsStagePrefix G L (stageIndex i) p := by
    intro i p hp hpinitial
    exact hprefix i p hp.1 hpinitial
  have hresult :=
    SliceSpliceConstructor.threadLimit_isStagePrefix_of_stagePrefixes
      hL Ca stageIndex beta hbeta hindex hindexSigma hSigma havoid
      hmono hLUB hcofinal htightCa hroofCa aCa
      (Set.mem_singleton a.1) hprefixCa
  rwa [hlimit] at hresult

end RegularCanonicalHistoryLimit
end CardinalInduction
end Erdos599
