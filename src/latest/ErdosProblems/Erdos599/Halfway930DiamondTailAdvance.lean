/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Halfway930OldSliceMacroBridge
import ErdosProblems.Erdos599.HalfwayOldSliceDiamondAdvance

/-!
# The honest old-slice front-and-tail diamond advance

The first diamond advance retains the incoming blueprint and appends the
old-to-new first-hit front.  Its result meets the stored ambient target
suffix only at the splice vertex: the old carrier is roofed at the old
frontier, while the selected safe path leaves that roof immediately, and
the front itself has exact one-point incidence with its suffix.

Consequently a second literal diamond can append the external suffix.  The
result is an actual linkage blueprint which retains every incoming real edge
and the complete scheduled path to the ambient target.  No claim is made
that this second result is contained in the fixed later-stage roof.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- Appending an original finite path by a diamond can destroy only the
real terminal at the splice vertex. -/
theorem diamond_preserves_realTerminals_except_finish
    (cut : LinkageBlueprint Gamma Y kappa)
    (p : FinitePath (imaginaryGraph Gamma Y kappa))
    (hp : (.inl p : Path _) ∈ cut.paths)
    (P : FinitePath Gamma.graph) (hstart : P.start = p.finish)
    (hfresh : cut.vertexSet ∩ P.support ⊆ {p.finish}) :
    cut.realPart.terminals \ {p.finish} ⊆
      (cut.diamond p hp P hstart hfresh).realPart.terminals := by
  intro x hx
  refine ⟨?_, ?_⟩
  · rw [realPart_vertices, diamond_vertexSet]
    exact Or.inl hx.1.1
  · rintro ⟨y, hy⟩
    rcases hy with ⟨hyEdge, hyOriginal⟩
    rw [diamond_edgeSet] at hyEdge
    rcases hyEdge with hyCut | hyP
    · exact hx.1.2 ⟨y, ⟨hyCut, hyOriginal⟩⟩
    · have hxP : x ∈ P.support :=
        (P.edgeSet_subset_support_prod hyP).1
      have hxeq : x = p.finish :=
        Set.mem_singleton_iff.1 (hfresh ⟨hx.1.1, hxP⟩)
      exact hx.2 hxeq

/-- The same one-point loss statement for terminals of the whole imaginary
blueprint relation. -/
theorem diamond_preserves_terminals_except_finish
    (cut : LinkageBlueprint Gamma Y kappa)
    (p : FinitePath (imaginaryGraph Gamma Y kappa))
    (hp : (.inl p : Path _) ∈ cut.paths)
    (P : FinitePath Gamma.graph) (hstart : P.start = p.finish)
    (hfresh : cut.vertexSet ∩ P.support ⊆ {p.finish}) :
    cut.terminalSet \ {p.finish} ⊆
      (cut.diamond p hp P hstart hfresh).terminalSet := by
  intro x hx
  rw [cut.terminalSet_eq_no_outgoing] at hx
  rw [(cut.diamond p hp P hstart hfresh).terminalSet_eq_no_outgoing]
  refine ⟨?_, ?_⟩
  · rw [diamond_vertexSet]
    exact Or.inl hx.1.1
  · rintro ⟨y, hy⟩
    rw [diamond_edgeSet] at hy
    rcases hy with hyCut | hyP
    · exact hx.1.2 ⟨y, hyCut⟩
    · have hxP : x ∈ P.support :=
        (P.edgeSet_subset_support_prod hyP).1
      have hxeq : x = p.finish :=
        Set.mem_singleton_iff.1 (hfresh ⟨hx.1.1, hxP⟩)
      exact hx.2 hxeq

/-- A real terminal created by a literal diamond is either an old real
terminal or the terminal of the appended original path.  This is the upper
bound complementary to `diamond_preserves_realTerminals_except_finish` and
is the local exhaustion fact needed at a final scheduler step. -/
theorem diamond_realTerminals_subset_terminal_union_finish
    (cut : LinkageBlueprint Gamma Y kappa)
    (p : FinitePath (imaginaryGraph Gamma Y kappa))
    (hp : (.inl p : Path _) ∈ cut.paths)
    (P : FinitePath Gamma.graph) (hstart : P.start = p.finish)
    (hfresh : cut.vertexSet ∩ P.support ⊆ {p.finish}) :
    (cut.diamond p hp P hstart hfresh).realPart.terminals ⊆
      cut.realPart.terminals ∪ {P.finish} := by
  intro x hx
  have hxVertex := hx.1
  rw [realPart_vertices, diamond_vertexSet] at hxVertex
  rcases hxVertex with hxCut | hxP
  · left
    refine ⟨hxCut, ?_⟩
    rintro ⟨y, hy⟩
    apply hx.2
    refine ⟨y, ?_⟩
    exact ⟨by
      rw [diamond_edgeSet]
      exact Or.inl hy.1, hy.2⟩
  · by_cases hxFinish : x = P.finish
    · exact Or.inr (Set.mem_singleton_iff.2 hxFinish)
    · obtain ⟨y, hxy⟩ :=
        Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
          P hxP hxFinish
      exact False.elim (hx.2 ⟨y, ⟨by
        rw [diamond_edgeSet]
        exact Or.inr hxy, P.edgeSet_subset_adj hxy⟩⟩)

/-- A closed local interval transaction together with its actual
edge-retaining first diamond. -/
structure ClosedOldSlice930DiamondTailTransaction
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : LinkageBlueprint Gamma C.selectedReference kappa)
    (u : V) where
  localMacro : ClosedOldSlice930MacroTransaction C W u
  oldBlueprint : W.IsLinkageBlueprint
    C.oldSlice C.oldClosedSet C.persistent
  scheduled_terminal : u ∈ W.realPart.terminals
  frontAdvance : OldSliceDiamondAdvance localMacro.intervalTransaction oldBlueprint

/-- The honest two-diamond transaction is unconditional in the old-slice
branch. -/
theorem exists_closedOldSlice930DiamondTailTransaction
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : LinkageBlueprint Gamma C.selectedReference kappa)
    {u : V}
    (hlower : CardinalInduction.UniversalCardinalInductionBelow V kappa)
    (hext : CardinalInduction.UniversalExtensionClauseAt V kappa)
    (hW : W.IsLinkageBlueprint C.oldSlice C.oldClosedSet C.persistent)
    (hu : u ∈ W.realPart.terminals) (huOld : u ∈ C.oldSlice)
    (hbefore : C.before ⊆ C.outerRoof)
    (href : ∀ p ∈ C.selectedReference, p.support ⊆ C.outerRoof)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof) :
    Nonempty (ClosedOldSlice930DiamondTailTransaction C W u) := by
  obtain ⟨Q⟩ := exists_closedOldSlice930MacroTransaction C W hlower hext hW
    hu huOld hbefore href hSafeRoof
  obtain ⟨D⟩ := OldSliceDiamondAdvance.exists_diamondAdvance
    Q.intervalTransaction hW
  exact ⟨{
    localMacro := Q
    oldBlueprint := hW
    scheduled_terminal := hu
    frontAdvance := D }⟩

namespace ClosedOldSlice930DiamondTailTransaction

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {W : LinkageBlueprint Gamma C.selectedReference kappa}
variable {u : V}

/-- The explicit finite prefix produced by the first diamond. -/
def frontPrefix (Q : ClosedOldSlice930DiamondTailTransaction C W u) :
    FinitePath (imaginaryGraph Gamma C.selectedReference kappa) :=
  diamondPath Q.frontAdvance.selectedPrefix
    Q.localMacro.intervalTransaction.interval.front
    (Q.localMacro.intervalTransaction.interval.front_start.trans
      Q.frontAdvance.selectedPrefix_finish.symm)
    (fun x hx ↦ by
      simpa only [Q.frontAdvance.selectedPrefix_finish] using
        Q.frontAdvance.fresh
          ⟨⟨.inl Q.frontAdvance.selectedPrefix,
            Q.frontAdvance.selectedPrefix_mem, hx.1⟩, hx.2⟩)

/-- The explicit first-diamond prefix is literally a member of the first
result. -/
theorem frontPrefix_mem_result
    (Q : ClosedOldSlice930DiamondTailTransaction C W u) :
    (.inl Q.frontPrefix : Path _) ∈ Q.frontAdvance.result.paths := by
  simp [frontPrefix, OldSliceDiamondAdvance.result, diamond, diamondPaths]

@[simp] theorem frontPrefix_finish
    (Q : ClosedOldSlice930DiamondTailTransaction C W u) :
    Q.frontPrefix.finish =
      Q.localMacro.intervalTransaction.interval.front.finish := by
  exact diamondPath_finish Q.frontAdvance.selectedPrefix
    Q.localMacro.intervalTransaction.interval.front
    (Q.localMacro.intervalTransaction.interval.front_start.trans
      Q.frontAdvance.selectedPrefix_finish.symm)
    (fun x hx ↦ by
      simpa only [Q.frontAdvance.selectedPrefix_finish] using
        Q.frontAdvance.fresh
          ⟨⟨.inl Q.frontAdvance.selectedPrefix,
            Q.frontAdvance.selectedPrefix_mem, hx.1⟩, hx.2⟩)

/-- The carrier after the first diamond meets the external suffix exactly
at the splice vertex. -/
theorem frontResult_tail_inter
    (Q : ClosedOldSlice930DiamondTailTransaction C W u) :
    Q.frontAdvance.result.vertexSet ∩
        Q.localMacro.intervalTransaction.interval.tail.support =
      {Q.localMacro.intervalTransaction.interval.tail.start} := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [Q.frontAdvance.result_vertexSet_eq] at hx
    rcases hx.1 with hxCut | hxFront
    · apply Q.localMacro.oldRoof_tail_inter_subset
      refine ⟨?_, hx.2⟩
      apply Q.oldBlueprint.vertices_roofed
      rw [← Q.localMacro.intervalTransaction.continuation.conclusion.isCutAt.vertexSet_eq]
      exact hxCut
    · have hxContact : x ∈
          Q.localMacro.intervalTransaction.interval.front.support ∩
            Q.localMacro.intervalTransaction.interval.tail.support :=
        ⟨hxFront, hx.2⟩
      rw [Q.localMacro.intervalTransaction.interval.front_tail_inter] at hxContact
      simpa only [← Q.localMacro.intervalTransaction.interval.tail_start] using
        hxContact
  · intro x hx
    have hxeq : x = Q.localMacro.intervalTransaction.interval.tail.start :=
      Set.mem_singleton_iff.1 hx
    subst x
    refine ⟨?_,
      Q.localMacro.intervalTransaction.interval.tail.start_mem_support⟩
    apply Q.frontAdvance.front_support_subset_result
    rw [Q.localMacro.intervalTransaction.interval.tail_start]
    exact Q.localMacro.intervalTransaction.interval.front.finish_mem_support

/-- The complete honest successor, obtained by appending the stored target
suffix to the first diamond prefix. -/
def result (Q : ClosedOldSlice930DiamondTailTransaction C W u) :
    LinkageBlueprint Gamma C.selectedReference kappa :=
  Q.frontAdvance.result.diamond Q.frontPrefix Q.frontPrefix_mem_result
    Q.localMacro.intervalTransaction.interval.tail
    (Q.localMacro.intervalTransaction.interval.tail_start.trans
      Q.frontPrefix_finish.symm)
    (by simpa only [Q.frontPrefix_finish,
      Q.localMacro.intervalTransaction.interval.tail_start] using
        Q.frontResult_tail_inter.subset)

/-- Exact carrier accounting for the complete two-diamond successor. -/
theorem result_vertexSet_eq
    (Q : ClosedOldSlice930DiamondTailTransaction C W u) :
    Q.result.vertexSet = Q.frontAdvance.result.vertexSet ∪
      Q.localMacro.intervalTransaction.interval.tail.support := by
  exact diamond_vertexSet Q.frontAdvance.result Q.frontPrefix
    Q.frontPrefix_mem_result Q.localMacro.intervalTransaction.interval.tail
    (Q.localMacro.intervalTransaction.interval.tail_start.trans
      Q.frontPrefix_finish.symm)
    (by simpa only [Q.frontPrefix_finish,
      Q.localMacro.intervalTransaction.interval.tail_start] using
        Q.frontResult_tail_inter.subset)

/-- Exact edge accounting for the complete two-diamond successor. -/
theorem result_edgeSet_eq
    (Q : ClosedOldSlice930DiamondTailTransaction C W u) :
    Q.result.edgeSet = Q.frontAdvance.result.edgeSet ∪
      Q.localMacro.intervalTransaction.interval.tail.edgeSet := by
  exact diamond_edgeSet Q.frontAdvance.result Q.frontPrefix
    Q.frontPrefix_mem_result Q.localMacro.intervalTransaction.interval.tail
    (Q.localMacro.intervalTransaction.interval.tail_start.trans
      Q.frontPrefix_finish.symm)
    (by simpa only [Q.frontPrefix_finish,
      Q.localMacro.intervalTransaction.interval.tail_start] using
        Q.frontResult_tail_inter.subset)

theorem frontResult_vertexSet_subset_result
    (Q : ClosedOldSlice930DiamondTailTransaction C W u) :
    Q.frontAdvance.result.vertexSet ⊆ Q.result.vertexSet := by
  rw [Q.result_vertexSet_eq]
  exact Set.subset_union_left

theorem tail_support_subset_result
    (Q : ClosedOldSlice930DiamondTailTransaction C W u) :
    Q.localMacro.intervalTransaction.interval.tail.support ⊆
      Q.result.vertexSet := by
  rw [Q.result_vertexSet_eq]
  exact Set.subset_union_right

theorem frontResult_edgeSet_subset_result
    (Q : ClosedOldSlice930DiamondTailTransaction C W u) :
    Q.frontAdvance.result.edgeSet ⊆ Q.result.edgeSet := by
  rw [Q.result_edgeSet_eq]
  exact Set.subset_union_left

theorem tail_edgeSet_subset_result
    (Q : ClosedOldSlice930DiamondTailTransaction C W u) :
    Q.localMacro.intervalTransaction.interval.tail.edgeSet ⊆
      Q.result.edgeSet := by
  rw [Q.result_edgeSet_eq]
  exact Set.subset_union_right

/-- Every old real edge survives as a real edge of the complete successor. -/
theorem old_realEdges_subset_result_realEdges
    (Q : ClosedOldSlice930DiamondTailTransaction C W u) :
    W.realPart.edges ⊆ Q.result.realPart.edges := by
  intro e he
  exact Q.result.mem_realPart_of_mem_edgeSet_of_original
    (Q.frontResult_edgeSet_subset_result
      ((Q.frontAdvance.old_realEdges_subset_result_realEdges he).1)) he.2

/-- Every edge of the selected deletion-safe target path survives literally
as a real edge of the complete successor. -/
theorem targetPath_edgeSet_subset_result_realEdges
    (Q : ClosedOldSlice930DiamondTailTransaction C W u) :
    Q.localMacro.intervalTransaction.interval.path.edgeSet ⊆
      Q.result.realPart.edges := by
  rw [← Q.localMacro.front_append_tail, FinitePath.edgeSet_appendFinite]
  rintro e (heFront | heTail)
  · exact Q.result.mem_realPart_of_mem_edgeSet_of_original
      (Q.frontResult_edgeSet_subset_result
        (Q.frontAdvance.front_edgeSet_subset_result heFront))
      (Q.localMacro.intervalTransaction.interval.front.edgeSet_subset_adj heFront)
  · exact Q.result.mem_realPart_of_mem_edgeSet_of_original
      (Q.tail_edgeSet_subset_result heTail)
      (Q.localMacro.intervalTransaction.interval.tail.edgeSet_subset_adj heTail)

/-- The whole selected target path lies in the complete successor carrier. -/
theorem targetPath_support_subset_result
    (Q : ClosedOldSlice930DiamondTailTransaction C W u) :
    Q.localMacro.intervalTransaction.interval.path.support ⊆
      Q.result.vertexSet := by
  rw [← Q.localMacro.front_append_tail,
    FinitePath.support_appendFinite_eq_union]
  rintro x (hxFront | hxTail)
  · exact Q.frontResult_vertexSet_subset_result
      (Q.frontAdvance.front_support_subset_result hxFront)
  · exact Q.tail_support_subset_result hxTail

theorem targetPath_boundary
    (Q : ClosedOldSlice930DiamondTailTransaction C W u) :
    Q.localMacro.intervalTransaction.interval.path.start = u ∧
      Q.localMacro.intervalTransaction.interval.path.finish ∈ Gamma.target :=
  Q.localMacro.targetPath_boundary

/-- The complete successor genuinely links the scheduled old terminal to
the ambient target through real edges. -/
theorem result_realLinksTo
    (Q : ClosedOldSlice930DiamondTailTransaction C W u) :
    Q.result.RealLinksTo u Gamma.target := by
  refine ⟨Q.localMacro.intervalTransaction.interval.path,
    Q.targetPath_boundary.1, Q.targetPath_boundary.2, ?_, ?_⟩
  · simpa only [realPart_vertices] using Q.targetPath_support_subset_result
  · exact Q.targetPath_edgeSet_subset_result_realEdges

/-- The complete successor creates no new non-target real terminal.  The
first diamond can expose only the front endpoint; the second diamond either
makes that point internal to the stored suffix or, if the suffix is trivial,
identifies it with its target endpoint. -/
theorem result_realTerminals_subset_old_union_target
    (Q : ClosedOldSlice930DiamondTailTransaction C W u) :
    Q.result.realPart.terminals ⊆
      W.realPart.terminals ∪ Gamma.target := by
  intro x hx
  have hxOuter : x ∈ Q.frontAdvance.result.realPart.terminals ∪
      {Q.localMacro.intervalTransaction.interval.tail.finish} := by
    exact diamond_realTerminals_subset_terminal_union_finish
      Q.frontAdvance.result Q.frontPrefix Q.frontPrefix_mem_result
      Q.localMacro.intervalTransaction.interval.tail
      (Q.localMacro.intervalTransaction.interval.tail_start.trans
        Q.frontPrefix_finish.symm)
      (by simpa only [Q.frontPrefix_finish,
        Q.localMacro.intervalTransaction.interval.tail_start] using
          Q.frontResult_tail_inter.subset)
      hx
  rcases hxOuter with hxFrontResult | hxTailFinish
  · have hxInner :
        x ∈ Q.localMacro.intervalTransaction.cut.realPart.terminals ∪
          {Q.localMacro.intervalTransaction.interval.front.finish} := by
      exact diamond_realTerminals_subset_terminal_union_finish
        Q.localMacro.intervalTransaction.cut
        Q.frontAdvance.selectedPrefix Q.frontAdvance.selectedPrefix_mem
        Q.localMacro.intervalTransaction.interval.front
        (Q.localMacro.intervalTransaction.interval.front_start.trans
          Q.frontAdvance.selectedPrefix_finish.symm)
        (by simpa only [Q.frontAdvance.selectedPrefix_finish] using
          Q.frontAdvance.fresh)
        hxFrontResult
    rcases hxInner with hxCut | hxFrontFinish
    · exact Or.inl
        (Q.localMacro.intervalTransaction.continuation.conclusion.isCutAt
          |>.realTerminal_iff Q.scheduled_terminal |>.1 hxCut)
    · have hxeq : x =
          Q.localMacro.intervalTransaction.interval.tail.start := by
        calc
          x = Q.localMacro.intervalTransaction.interval.front.finish :=
            Set.mem_singleton_iff.1 hxFrontFinish
          _ = Q.localMacro.intervalTransaction.interval.tail.start :=
            Q.localMacro.intervalTransaction.interval.tail_start.symm
      by_cases htrivial :
          Q.localMacro.intervalTransaction.interval.tail.start =
            Q.localMacro.intervalTransaction.interval.tail.finish
      · exact Or.inr (hxeq.trans htrivial ▸ Q.localMacro.tail_boundary.2)
      · obtain ⟨y, hxy⟩ :=
          Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
            Q.localMacro.intervalTransaction.interval.tail
            Q.localMacro.intervalTransaction.interval.tail.start_mem_support
            htrivial
        exfalso
        apply hx.2
        refine ⟨y, ?_⟩
        rw [hxeq]
        exact Q.result.mem_realPart_of_mem_edgeSet_of_original
          (Q.tail_edgeSet_subset_result hxy)
          (Q.localMacro.intervalTransaction.interval.tail.edgeSet_subset_adj hxy)
  · exact Or.inr
      (Set.mem_singleton_iff.1 hxTailFinish ▸ Q.localMacro.tail_boundary.2)

/-- The cut blueprint's whole family graph is retained by the two literal
diamonds. -/
theorem cut_familyGraph_extends_result
    (Q : ClosedOldSlice930DiamondTailTransaction C W u) :
    Q.localMacro.intervalTransaction.cut.familyGraph.Extends
      Q.result.familyGraph := by
  constructor
  · exact Q.frontAdvance.cut_vertexSet_subset_result.trans
      Q.frontResult_vertexSet_subset_result
  · exact Q.frontAdvance.cut_edgeSet_subset_result.trans
      Q.frontResult_edgeSet_subset_result

/-- The cut blueprint's spanning real graph is retained as well. -/
theorem cut_realPart_extends_result
    (Q : ClosedOldSlice930DiamondTailTransaction C W u) :
    Q.localMacro.intervalTransaction.cut.realPart.Extends
      Q.result.realPart := by
  constructor
  · exact Q.cut_familyGraph_extends_result.1
  · intro e he
    exact ⟨Q.cut_familyGraph_extends_result.2 he.1, he.2⟩

/-- No real terminal of the cut other than the scheduled splice vertex is
lost by the two-diamond advance. -/
theorem cut_realTerminals_except_subset_result
    (Q : ClosedOldSlice930DiamondTailTransaction C W u) :
    Q.localMacro.intervalTransaction.cut.realPart.terminals \ {u} ⊆
      Q.result.realPart.terminals := by
  intro x hx
  have hxFront : x ∈ Q.frontAdvance.result.realPart.terminals := by
    apply diamond_preserves_realTerminals_except_finish
      Q.localMacro.intervalTransaction.cut Q.frontAdvance.selectedPrefix
      Q.frontAdvance.selectedPrefix_mem
      Q.localMacro.intervalTransaction.interval.front
      (Q.localMacro.intervalTransaction.interval.front_start.trans
        Q.frontAdvance.selectedPrefix_finish.symm)
      (by simpa only [Q.frontAdvance.selectedPrefix_finish] using
        Q.frontAdvance.fresh)
    exact ⟨hx.1, by simpa only [Q.frontAdvance.selectedPrefix_finish] using hx.2⟩
  have hxNeTail :
      x ≠ Q.localMacro.intervalTransaction.interval.tail.start := by
    intro hxeq
    have hxCut : x ∈ Q.localMacro.intervalTransaction.cut.vertexSet :=
      hx.1.1
    have hxFrontSupport : x ∈
        Q.localMacro.intervalTransaction.interval.front.support := by
      rw [hxeq, Q.localMacro.intervalTransaction.interval.tail_start]
      exact Q.localMacro.intervalTransaction.interval.front.finish_mem_support
    have hxu : x = u := Set.mem_singleton_iff.1
      (Q.frontAdvance.fresh ⟨hxCut, hxFrontSupport⟩)
    exact hx.2 hxu
  apply diamond_preserves_realTerminals_except_finish
    Q.frontAdvance.result Q.frontPrefix Q.frontPrefix_mem_result
    Q.localMacro.intervalTransaction.interval.tail
    (Q.localMacro.intervalTransaction.interval.tail_start.trans
      Q.frontPrefix_finish.symm)
    (by simpa only [Q.frontPrefix_finish,
      Q.localMacro.intervalTransaction.interval.tail_start] using
        Q.frontResult_tail_inter.subset)
  refine ⟨hxFront, ?_⟩
  intro hxeq
  apply hxNeTail
  calc
    x = Q.frontPrefix.finish := Set.mem_singleton_iff.1 hxeq
    _ = Q.localMacro.intervalTransaction.interval.front.finish :=
      Q.frontPrefix_finish
    _ = Q.localMacro.intervalTransaction.interval.tail.start :=
      Q.localMacro.intervalTransaction.interval.tail_start.symm

/-- Every incoming real terminal other than the scheduled one survives in
the complete honest successor. -/
theorem old_realTerminals_except_subset_result
    (Q : ClosedOldSlice930DiamondTailTransaction C W u) :
    W.realPart.terminals \ {u} ⊆ Q.result.realPart.terminals := by
  intro x hx
  apply Q.cut_realTerminals_except_subset_result
  exact ⟨Q.localMacro.intervalTransaction.continuation.preserves_other_terminals hx,
    hx.2⟩

/-- The two-diamond result satisfies the exact real-extension persistence
law (9.32), without asserting any false fixed-frontier roof condition. -/
theorem old_realExtends_result
    (Q : ClosedOldSlice930DiamondTailTransaction C W u) :
    W.RealExtends Q.result Gamma.target := by
  refine ⟨?_, ?_⟩
  · exact ⟨Q.frontAdvance.old_vertexSet_subset_result.trans
      Q.frontResult_vertexSet_subset_result,
      Q.old_realEdges_subset_result_realEdges⟩
  · intro x hxW
    by_cases hxu : x = u
    · subst x
      exact Or.inr Q.result_realLinksTo.start_mem_completedRealVertices
    by_cases hxTerminal : x ∈ W.terminalSet
    · have hxTerminalNo : x ∈ W.vertexSet ∧
          ¬ ∃ y, (x, y) ∈ W.edgeSet := by
        rw [W.terminalSet_eq_no_outgoing] at hxTerminal
        exact hxTerminal
      have hxCutTerminal :
          x ∈ Q.localMacro.intervalTransaction.cut.terminalSet := by
        rcases Q.localMacro.intervalTransaction.continuation.conclusion.isCutAt with
          ⟨_, hcut⟩ | ⟨v, hv⟩
        · simpa only [hcut] using hxTerminal
        · rw [Q.localMacro.intervalTransaction.cut.terminalSet_eq_no_outgoing]
          refine ⟨hv.vertices_eq.symm ▸ hxTerminalNo.1, ?_⟩
          rintro ⟨y, hy⟩
          rw [hv.edges_eq] at hy
          exact hxTerminalNo.2 ⟨y, hy.1⟩
      have hxFrontTerminal : x ∈ Q.frontAdvance.result.terminalSet := by
        apply diamond_preserves_terminals_except_finish
          Q.localMacro.intervalTransaction.cut Q.frontAdvance.selectedPrefix
          Q.frontAdvance.selectedPrefix_mem
          Q.localMacro.intervalTransaction.interval.front
          (Q.localMacro.intervalTransaction.interval.front_start.trans
            Q.frontAdvance.selectedPrefix_finish.symm)
          (by simpa only [Q.frontAdvance.selectedPrefix_finish] using
            Q.frontAdvance.fresh)
        exact ⟨hxCutTerminal, by
          simpa only [Set.mem_singleton_iff,
            Q.frontAdvance.selectedPrefix_finish] using hxu⟩
      have hxNeTail :
          x ≠ Q.localMacro.intervalTransaction.interval.tail.start := by
        intro hxeq
        have hxCutTerminalNo :
            x ∈ Q.localMacro.intervalTransaction.cut.vertexSet ∧
              ¬ ∃ y, (x, y) ∈
                Q.localMacro.intervalTransaction.cut.edgeSet := by
          rw [Q.localMacro.intervalTransaction.cut.terminalSet_eq_no_outgoing]
            at hxCutTerminal
          exact hxCutTerminal
        have hxCut : x ∈ Q.localMacro.intervalTransaction.cut.vertexSet :=
          hxCutTerminalNo.1
        have hxFrontSupport : x ∈
            Q.localMacro.intervalTransaction.interval.front.support := by
          rw [hxeq, Q.localMacro.intervalTransaction.interval.tail_start]
          exact Q.localMacro.intervalTransaction.interval.front.finish_mem_support
        have hxu' : x = u := Set.mem_singleton_iff.1
          (Q.frontAdvance.fresh ⟨hxCut, hxFrontSupport⟩)
        exact hxu hxu'
      have hxResultTerminal : x ∈ Q.result.terminalSet := by
        apply diamond_preserves_terminals_except_finish
          Q.frontAdvance.result Q.frontPrefix Q.frontPrefix_mem_result
          Q.localMacro.intervalTransaction.interval.tail
          (Q.localMacro.intervalTransaction.interval.tail_start.trans
            Q.frontPrefix_finish.symm)
          (by simpa only [Q.frontPrefix_finish,
            Q.localMacro.intervalTransaction.interval.tail_start] using
              Q.frontResult_tail_inter.subset)
        refine ⟨hxFrontTerminal, ?_⟩
        intro hxeq
        apply hxNeTail
        calc
          x = Q.frontPrefix.finish := Set.mem_singleton_iff.1 hxeq
          _ = Q.localMacro.intervalTransaction.interval.front.finish :=
            Q.frontPrefix_finish
          _ = Q.localMacro.intervalTransaction.interval.tail.start :=
            Q.localMacro.intervalTransaction.interval.tail_start.symm
      exact Or.inl (Or.inl ⟨hxResultTerminal, hxTerminal⟩)
    · obtain ⟨y, hyW⟩ :=
        W.exists_outgoing_of_mem_vertexSet_of_not_mem_terminalSet hxW hxTerminal
      rcases Q.localMacro.intervalTransaction.continuation.conclusion.isCutAt with
        ⟨_, hcut⟩ | ⟨v, hv⟩
      · have hyCut : (x, y) ∈
            Q.localMacro.intervalTransaction.cut.edgeSet := by
          simpa only [hcut] using hyW
        exact Or.inl (Or.inr ⟨y, hyW,
          Q.cut_familyGraph_extends_result.2 hyCut⟩)
      · by_cases hyDeleted : (x, y) = (u, v)
        · exact False.elim (hxu (congrArg Prod.fst hyDeleted))
        · have hyCut : (x, y) ∈ Q.localMacro.intervalTransaction.cut.edgeSet :=
            hv.edges_eq.symm ▸ ⟨hyW, hyDeleted⟩
          exact Or.inl (Or.inr ⟨y, hyW,
            Q.cut_familyGraph_extends_result.2 hyCut⟩)

#print axioms exists_closedOldSlice930DiamondTailTransaction
#print axioms ClosedOldSlice930DiamondTailTransaction.frontResult_tail_inter
#print axioms ClosedOldSlice930DiamondTailTransaction.old_realEdges_subset_result_realEdges
#print axioms ClosedOldSlice930DiamondTailTransaction.targetPath_edgeSet_subset_result_realEdges
#print axioms ClosedOldSlice930DiamondTailTransaction.old_realExtends_result

end ClosedOldSlice930DiamondTailTransaction

end LinkageBlueprint
end Blueprint
end Erdos599
