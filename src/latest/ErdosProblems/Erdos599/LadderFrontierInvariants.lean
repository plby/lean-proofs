/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Ladder
import ErdosProblems.Erdos599.QuotientRoofTransport

/-!
# Frontier invariants for the canonical ladder

This file isolates the roof calculations behind source Lemmas 7.10--7.11.
In particular, it identifies the source of an essential quotient stage with
the essential terminal frontier of the accumulated warp.  This calculation
does not require accumulated paths to start in the original source; the exact
hypothesis is the separation invariant used by the ladder construction.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb

universe u v

variable {V : Type u} {G : DWeb V}

/-- Enlarging a frontier cannot make an old strictly roofed point
essential.  This elementary fact is useful for the optional singleton
marker: after the arrow calculation, adjoining the marker terminal cannot
destroy strict-roof monotonicity. -/
theorem disjoint_essential_union_strictRoof_left (S T : Set V) :
    Disjoint (G.essential (S ∪ T)) (G.strictRoof S) := by
  apply Set.disjoint_left.2
  intro x hxEssential hxStrict
  apply hxEssential.2
  apply G.roof_mono ?_
  · rw [G.roof_essential]
    exact hxStrict.1
  · intro y hy
    refine ⟨Or.inl (G.essential_subset S hy), ?_⟩
    intro hyx
    apply hxStrict.2
    exact hyx ▸ hy

/-- The strict roof is monotone under adjoining arbitrary frontier
vertices. -/
theorem strictRoof_subset_strictRoof_union_left (S T : Set V) :
    G.strictRoof S ⊆ G.strictRoof (S ∪ T) := by
  intro x hx
  refine ⟨G.roof_mono Set.subset_union_left hx.1, ?_⟩
  intro hxEssential
  exact Set.disjoint_left.1
    (G.disjoint_essential_union_strictRoof_left S T)
    hxEssential hx

/-- The arrow frontier calculation only needs the two input warps to roof
the union of their initial sets.  The standard library theorem states the
special case where both inputs are waves of one web; replacing the source
by the union of initial sets gives this source-free form. -/
theorem essential_terminalFrontier_arrow_eq_union_of_crossRoof
    {U W : Set G.DPath} (hUwarp : G.IsWarp U) (hWwarp : G.IsWarp W)
    (hUroof : G.initialSet (U ∪ W) ⊆
      G.roof (G.terminalFrontier U))
    (hWroof : G.initialSet (U ∪ W) ⊆
      G.roof (G.terminalFrontier W)) :
    G.essential (G.terminalFrontier (G.arrow U W)) =
      G.essential
        (G.terminalFrontier U ∪ G.terminalFrontier W) := by
  let H : DWeb V :=
    { graph := G.graph
      source := G.initialSet (U ∪ W)
      target := G.target }
  have hU : H.IsWave U := by
    refine ⟨hUwarp, ?_, hUroof⟩
    change G.initialSet U ⊆ G.initialSet (U ∪ W)
    rw [G.initialSet_union]
    exact Set.subset_union_left
  have hW : H.IsWave W := by
    refine ⟨hWwarp, ?_, hWroof⟩
    change G.initialSet W ⊆ G.initialSet (U ∪ W)
    rw [G.initialSet_union]
    exact Set.subset_union_right
  have h := H.essential_terminalFrontier_arrow_eq_union hU hW
  have hterminalFrontier (X : Set G.DPath) :
      H.terminalFrontier X = G.terminalFrontier X := by
    rfl
  let candidateToG {p : DirectedPath.FinitePath G.graph}
      (c : H.ArrowCandidate U W p) : G.ArrowCandidate U W p :=
    { path := c.path
      mem_path := c.mem_path
      finish_mem := c.finish_mem
      clean := c.clean }
  let candidateToH {p : DirectedPath.FinitePath G.graph}
      (c : G.ArrowCandidate U W p) : H.ArrowCandidate U W p :=
    { path := c.path
      mem_path := c.mem_path
      finish_mem := c.finish_mem
      clean := c.clean }
  have harrow : H.arrow U W = G.arrow U W := by
    unfold DWeb.arrow
    congr 1
    funext p
    rcases p with ⟨p, hp⟩
    rcases p with p | p
    · simp only [DWeb.arrowPath]
      change H.arrowFinite U W p hp = G.arrowFinite U W p hp
      rw [DWeb.arrowFinite, DWeb.arrowFinite]
      by_cases hH : Nonempty (H.ArrowCandidate U W p)
      · have hG : Nonempty (G.ArrowCandidate U W p) :=
          ⟨candidateToG (Classical.choice hH)⟩
        rw [dif_pos hH, dif_pos hG]
        have hpath : (Classical.choice hH).path =
            (Classical.choice hG).path := by
          exact ArrowCandidate.path_eq (G := H) hWwarp
            (Classical.choice hH)
            (candidateToH (Classical.choice hG))
        dsimp only
        have happend : ∀ (q r : G.DPath), q = r →
            ∀ (hq : p.finish ∈ q.support)
              (hr : p.finish ∈ r.support)
              (ha : DirectedPath.Path.Appendable p q hq)
              (hb : DirectedPath.Path.Appendable p r hr),
              DirectedPath.Path.appendAt p q hq ha =
                DirectedPath.Path.appendAt p r hr hb := by
          intro q r hqr
          subst r
          intros
          rfl
        exact happend _ _ hpath _ _ _ _
      · have hG : ¬ Nonempty (G.ArrowCandidate U W p) := by
          intro hc
          exact hH ⟨candidateToH (Classical.choice hc)⟩
        rw [dif_neg hH, dif_neg hG]
    · rfl
  have hessential (S : Set V) : H.essential S = G.essential S := by
    rfl
  rw [hessential, hterminalFrontier, harrow, hessential,
    hterminalFrontier, hterminalFrontier] at h
  exact h

/-- Cross-roofed arrows roof exactly the union of the two input
frontiers. -/
theorem roof_terminalFrontier_arrow_eq_union_of_crossRoof
    {U W : Set G.DPath} (hUwarp : G.IsWarp U) (hWwarp : G.IsWarp W)
    (hUroof : G.initialSet (U ∪ W) ⊆
      G.roof (G.terminalFrontier U))
    (hWroof : G.initialSet (U ∪ W) ⊆
      G.roof (G.terminalFrontier W)) :
    G.roof (G.terminalFrontier (G.arrow U W)) =
      G.roof (G.terminalFrontier U ∪ G.terminalFrontier W) := by
  calc
    G.roof (G.terminalFrontier (G.arrow U W)) =
        G.roof (G.essential (G.terminalFrontier (G.arrow U W))) :=
      (G.roof_essential _).symm
    _ = G.roof (G.essential
        (G.terminalFrontier U ∪ G.terminalFrontier W)) :=
      congrArg G.roof
        (G.essential_terminalFrontier_arrow_eq_union_of_crossRoof
          hUwarp hWwarp hUroof hWroof)
    _ = G.roof (G.terminalFrontier U ∪ G.terminalFrontier W) :=
      G.roof_essential _

/-- Cross-roofed arrows preserve the strict roof of their left input. -/
theorem strictRoof_terminalFrontier_subset_arrow_left_of_crossRoof
    {U W : Set G.DPath} (hUwarp : G.IsWarp U) (hWwarp : G.IsWarp W)
    (hUroof : G.initialSet (U ∪ W) ⊆
      G.roof (G.terminalFrontier U))
    (hWroof : G.initialSet (U ∪ W) ⊆
      G.roof (G.terminalFrontier W)) :
    G.strictRoof (G.terminalFrontier U) ⊆
      G.strictRoof (G.terminalFrontier (G.arrow U W)) := by
  intro x hx
  refine ⟨?_, ?_⟩
  · rw [G.roof_terminalFrontier_arrow_eq_union_of_crossRoof
      hUwarp hWwarp hUroof hWroof]
    exact G.roof_mono Set.subset_union_left hx.1
  · intro hxEssential
    rw [G.essential_terminalFrontier_arrow_eq_union_of_crossRoof
      hUwarp hWwarp hUroof hWroof] at hxEssential
    exact Set.disjoint_left.1
      (G.disjoint_essential_union_strictRoof_left
        (G.terminalFrontier U) (G.terminalFrontier W))
      hxEssential hx

/-- A family in an essential quotient stage remains a warp after the two
canonical lifts back to the original web. -/
theorem isWarp_liftLadderStageFamily
    (W : Set G.DPath)
    {U : Set (G.stageWebOf W).DPath}
    (hU : (G.stageWebOf W).IsWarp U) :
    G.IsWarp (G.liftLadderStagePathOf W '' U) := by
  let Q := G.quotient (G.terminalFrontier W)
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hpq
  have hpq' : p ≠ q := fun h ↦
    hpq (congrArg (G.liftLadderStagePathOf W) h)
  have hdisj := hU hp hq hpq'
  have hsupport (r : (G.stageWebOf W).DPath) :
      (G.liftLadderStagePathOf W r).support = r.support := by
    rcases r with r | r <;>
      simp only [stageWebOf, liftLadderStagePathOf,
        G.support_liftQuotientPath,
        (G.quotient (G.terminalFrontier W)).support_liftEssentialPartPath]
  change Disjoint (G.liftLadderStagePathOf W p).support
    (G.liftLadderStagePathOf W q).support
  rw [hsupport p, hsupport q]
  exact hdisj

/-- Lifted rung paths start in the old essential terminal frontier. -/
theorem initialSet_liftLadderStageFamily_subset_essential
    (W : Set G.DPath)
    (hroof : G.source ⊆ G.roof (G.terminalFrontier W))
    {U : Set (G.stageWebOf W).DPath}
    (hU : (G.stageWebOf W).initialSet U ⊆
      (G.stageWebOf W).source) :
    G.initialSet (G.liftLadderStagePathOf W '' U) ⊆
      G.essential (G.terminalFrontier W) := by
  let Q := G.quotient (G.terminalFrontier W)
  rintro x ⟨_, ⟨p, hp, rfl⟩, rfl⟩
  have hpSource : p.initial ∈ Q.source :=
    (hU ⟨p, hp, rfl⟩).1
  rw [G.quotient_source_eq_essential_terminalFrontier_of_roofsSource
    hroof] at hpSource
  have hinitial : (G.liftLadderStagePathOf W p).initial = p.initial := by
    rcases p with p | p <;> rfl
  rw [hinitial]
  exact hpSource

/-- A wave in an essential quotient stage roofs the old essential
commitment frontier after both canonical lifts. -/
theorem essential_subset_roof_terminalFrontier_liftLadderStageFamily
    (hNoEnter : G.NoEdgeEnters G.source) (W : Set G.DPath)
    {U : Set (G.stageWebOf W).DPath}
    (hU : (G.stageWebOf W).IsWave U) :
    G.essential (G.terminalFrontier W) ⊆
      G.roof (G.terminalFrontier
        (G.liftLadderStagePathOf W '' U)) := by
  let Q := G.quotient (G.terminalFrontier W)
  let UQ : Set Q.DPath := Q.liftEssentialPartFamily U
  have hUQ : Q.IsWave UQ := Q.isWave_liftEssentialPartFamily hU
  have hroof := G.essential_subset_original_roof_of_quotient_wave_general
    hNoEnter hUQ
  have hterminalLift (p : (G.stageWebOf W).DPath) :
      G.terminal? (G.liftLadderStagePathOf W p) =
        (G.stageWebOf W).terminal? p := by
    rcases p with p | p <;> rfl
  have hterminalEssentialLift (p : (G.stageWebOf W).DPath) :
      Q.terminal? (Q.liftEssentialPartPath p) =
        (G.stageWebOf W).terminal? p := by
    rcases p with p | p <;> rfl
  have hterminalQuotientLift (p : Q.essentialPart.DPath) :
      G.terminal?
          (G.liftQuotientPath (G.terminalFrontier W)
            (Q.liftEssentialPartPath p)) =
        Q.essentialPart.terminal? p := by
    rcases p with p | p <;> rfl
  have hfrontier :
      G.terminalFrontier (G.liftLadderStagePathOf W '' U) =
        Q.terminalFrontier UQ := by
    ext x
    constructor
    · rintro ⟨_, ⟨p, hp, rfl⟩, hterm⟩
      refine ⟨Q.liftEssentialPartPath p, ⟨p, hp, rfl⟩, ?_⟩
      exact (hterminalEssentialLift p).trans
        ((hterminalLift p).symm.trans hterm)
    · rintro ⟨_, ⟨p, hp, rfl⟩, hterm⟩
      refine ⟨G.liftLadderStagePathOf W p, ⟨p, hp, rfl⟩, ?_⟩
      change G.terminal?
        (G.liftQuotientPath (G.terminalFrontier W)
          (Q.liftEssentialPartPath p)) = some x
      exact (hterminalQuotientLift p).trans
        ((Q.terminal?_liftEssentialPartPath p).symm.trans hterm)
  rwa [hfrontier]

namespace GrowingWarpChain

variable {I : Type v} [LinearOrder I] [Nonempty I] [IsDirectedOrder I]

/-- Every vertex which is eventually a stage terminal is a terminal of the
corresponding thread in the genuine direct limit.  Unlike the analogous
wave-chain lemma, this permits fresh initial threads to be introduced. -/
theorem setLiminf_terminalFrontier_subset_limitPaths
    (C : G.GrowingWarpChain I) :
    WarpLimits.setLiminf (fun i ↦ G.terminalFrontier (C.stage i)) ⊆
      G.terminalFrontier (C.limitPaths G) := by
  intro x hx
  obtain ⟨i₀, hxlate⟩ := (WarpLimits.mem_setLiminf _ _).mp hx
  obtain ⟨p₀, hp₀, hp₀term⟩ := hxlate i₀ le_rfl
  have hp₀initial : p₀.initial ∈ C.initialUnion :=
    Set.mem_iUnion.2 ⟨i₀, p₀, hp₀, rfl⟩
  let a : C.initialUnion := ⟨p₀.initial, hp₀initial⟩
  have hcofinal : DirectedPath.Path.TerminalCofinal
      (C.thread G a.1) x := by
    intro p hpThread
    obtain ⟨i, hpi, hpinitial⟩ := hpThread
    obtain ⟨j, hij, hi₀j⟩ := exists_ge_ge i i₀
    obtain ⟨q, hqj, hpq⟩ := C.grows hij p hpi
    obtain ⟨s, hsj, hp₀s⟩ := C.grows hi₀j p₀ hp₀
    obtain ⟨r, hrj, hrterm⟩ := hxlate j hi₀j
    have hxs : x ∈ s.support :=
      G.support_mono_of_extends hp₀s (G.terminal_mem_support hp₀term)
    have hxr : x ∈ r.support := G.terminal_mem_support hrterm
    have hsr : s = r := by
      by_contra hne
      exact Set.disjoint_left.1 (C.isWarp j hsj hrj hne) hxs hxr
    have hqinitial : q.initial = a.1 :=
      (G.extends_initial hpq).symm.trans hpinitial
    have hsinitial : s.initial = a.1 :=
      (G.extends_initial hp₀s).symm
    have hqs : q = s :=
      DWeb.IsWarp.eq_of_initial_eq G (C.isWarp j) hqj hsj
        (hqinitial.trans hsinitial.symm)
    refine ⟨q, ⟨j, hqj, hqinitial⟩, hpq, ?_⟩
    simpa only [hqs, hsr] using hrterm
  have hterminal : (C.threadLimit G a).terminal? = some x :=
    DirectedPath.Path.terminal_chainLimit_of_cofinal
      (C.thread G a.1) (C.thread_nonempty G a)
      (C.thread_isChain G a.1) hcofinal
  exact ⟨C.threadLimit G a, ⟨a, rfl⟩, hterminal⟩

/-- Source separation is preserved by the genuine direct limit of a
growing chain, provided every stage is self-roofing.  This is the limit
clause needed by the ladder recursion in the presence of fresh marker
threads. -/
theorem source_subset_roof_terminalFrontier_limitPaths
    (C : G.GrowingWarpChain I)
    (hsource : ∀ i, G.source ⊆
      G.roof (G.terminalFrontier (C.stage i)))
    (hself : ∀ i, G.vertexSet (C.stage i) ⊆
      G.roof (G.terminalFrontier (C.stage i))) :
    G.source ⊆ G.roof (G.terminalFrontier (C.limitPaths G)) := by
  have hfrontier : ∀ (i j : I), i ≤ j →
      G.terminalFrontier (C.stage i) ⊆
        G.roof (G.terminalFrontier (C.stage j)) := by
    intro i j hij x hx
    obtain ⟨p, hpi, hpterm⟩ := hx
    obtain ⟨q, hqj, hpq⟩ := C.grows hij p hpi
    exact hself j ⟨q, hqj,
      G.support_mono_of_extends hpq (G.terminal_mem_support hpterm)⟩
  intro x hx
  let i₀ := Classical.choice (inferInstance : Nonempty I)
  have hxUnion : x ∈ ⋃ i, G.roof (G.terminalFrontier (C.stage i)) :=
    Set.mem_iUnion.2 ⟨i₀, hsource i₀ hx⟩
  have hxLiminf : x ∈ G.roof
      (WarpLimits.setLiminf
        (fun i ↦ G.terminalFrontier (C.stage i))) :=
    G.roof_setLiminf_of_roof_chain
      (fun i ↦ G.terminalFrontier (C.stage i)) hfrontier hxUnion
  exact G.roof_mono (C.setLiminf_terminalFrontier_subset_limitPaths (G := G))
    hxLiminf

/-- Self-roofing is preserved by the genuine threadwise direct limit of a
growing chain. -/
theorem vertexSet_limitPaths_subset_roof_terminalFrontier
    (C : G.GrowingWarpChain I)
    (hself : ∀ i, G.vertexSet (C.stage i) ⊆
      G.roof (G.terminalFrontier (C.stage i))) :
    G.vertexSet (C.limitPaths G) ⊆
      G.roof (G.terminalFrontier (C.limitPaths G)) := by
  have hfrontier : ∀ (i j : I), i ≤ j →
      G.terminalFrontier (C.stage i) ⊆
        G.roof (G.terminalFrontier (C.stage j)) := by
    intro i j hij x hx
    obtain ⟨p, hpi, hpterm⟩ := hx
    obtain ⟨q, hqj, hpq⟩ := C.grows hij p hpi
    exact hself j ⟨q, hqj,
      G.support_mono_of_extends hpq (G.terminal_mem_support hpterm)⟩
  have hroofUnion : (⋃ i, G.roof (G.terminalFrontier (C.stage i))) ⊆
      G.roof (G.terminalFrontier (C.limitPaths G)) := by
    exact (G.roof_setLiminf_of_roof_chain
      (fun i ↦ G.terminalFrontier (C.stage i)) hfrontier).trans
        (G.roof_mono (C.setLiminf_terminalFrontier_subset_limitPaths (G := G)))
  rw [C.vertexSet_limitPaths G]
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx
  exact hroofUnion (Set.mem_iUnion.2 ⟨i, hself i hxi⟩)

end GrowingWarpChain

/-- If `T` roofs the original source, passing to the essential part of the
quotient by `T` does not discard any point of the essential frontier of `T`.
Each such point starts a genuine target path in the quotient. -/
theorem quotientEssentialPart_source_eq_essential_of_roofsSource
    {T : Set V} (hroof : G.source ⊆ G.roof T) :
    (G.quotient T).essentialPart.source = G.essential T := by
  have hqsource : (G.quotient T).source = G.essential T := by
    simpa only [G.terminalFrontier_trivialPaths] using
      (G.quotient_source_eq_essential_terminalFrontier_of_roofsSource
        (W := G.trivialPath '' T) (by
          simpa only [G.terminalFrontier_trivialPaths] using hroof))
  rw [essentialPart_source, hqsource]
  apply Set.Subset.antisymm
  · exact Set.inter_subset_left
  · intro x hx
    refine ⟨hx, ?_⟩
    obtain ⟨p, hpstart, hptarget⟩ :=
      G.exists_quotientTargetPath_from_essential T hx
    exact ⟨p, hpstart, hptarget⟩

namespace KappaLadder

open Ladder

variable {kappa : Cardinal.{u}} (L : G.KappaLadder kappa)

/-- Under the accumulated-stage separation invariant, a ladder frontier is
exactly the essential terminal frontier of the accumulated warp. -/
theorem frontier_eq_essential_terminalFrontier
    (hroof : L.RoofsSourceAtStages) (a : Stage kappa) :
    L.frontier a = G.essential (G.terminalFrontier (L.warpAt a)) := by
  exact G.quotientEssentialPart_source_eq_essential_of_roofsSource
    (hroof (Stage.toExtended a))

/-- The stage-separation invariant implies that every ladder frontier is
already essential in the original web. -/
theorem frontiersAreEssential_of_roofsSourceAtStages
    (hroof : L.RoofsSourceAtStages) : L.FrontiersAreEssential := by
  intro a
  rw [L.frontier_eq_essential_terminalFrontier hroof a,
    G.essential_idem]

/-- One-sided growth of accumulated paths, together with self-roofing of
the later accumulated warp, advances the terminal-frontier roof.  This is
the exact pathwise calculation used at both successor and direct-limit
stages; no wave assumption on the accumulated family is made. -/
theorem terminalFrontier_subset_roof_of_grows_of_selfRoofing
    {a b : Stage kappa}
    (hgrows : ∀ p ∈ L.warpAt a,
      ∃ q ∈ L.warpAt b, G.Extends p q)
    (hself : G.vertexSet (L.warpAt b) ⊆
      G.roof (G.terminalFrontier (L.warpAt b))) :
    G.terminalFrontier (L.warpAt a) ⊆
      G.roof (G.terminalFrontier (L.warpAt b)) := by
  rintro x ⟨p, hp, hpx⟩
  obtain ⟨q, hq, hpq⟩ := hgrows p hp
  apply hself
  exact ⟨q, hq,
    G.support_mono_of_extends hpq (G.terminal_mem_support hpx)⟩

/-- Structural construction invariants imply source Lemma 7.10.  The
growth premise is the one-sided notion appropriate for ladders, since a
successor is allowed to add one fresh marker component. -/
theorem hasFrontierChronology_of_grows_of_selfRoofing
    (hroof : L.RoofsSourceAtStages)
    (hgrows : ∀ (a b : Stage kappa), a < b →
      ∀ p ∈ L.warpAt a, ∃ q ∈ L.warpAt b, G.Extends p q)
    (hself : ∀ b : Stage kappa,
      G.vertexSet (L.warpAt b) ⊆
        G.roof (G.terminalFrontier (L.warpAt b))) :
    L.HasFrontierChronology := by
  intro a b hab x hx
  have hxTerminal : x ∈ G.terminalFrontier (L.warpAt a) := by
    rw [L.frontier_eq_essential_terminalFrontier hroof a] at hx
    exact G.essential_subset _ hx
  have hxRoof := L.terminalFrontier_subset_roof_of_grows_of_selfRoofing
    (hgrows a b hab) (hself b) hxTerminal
  rw [L.frontier_eq_essential_terminalFrontier hroof b,
    G.roof_essential]
  exact hxRoof

/-- Monotonicity of the strict roofs of the raw accumulated terminal
frontiers implies source Lemma 7.11.  In the canonical recursion the raw
monotonicity statement is the convenient induction invariant: at a
successor it follows from quotient avoidance, and at a limit from the
threadwise direct-limit construction. -/
theorem hasStrictFrontierChronology_of_strictRoof_mono
    (hroof : L.RoofsSourceAtStages)
    (hstrict : ∀ (a b : Stage kappa), a < b →
      G.strictRoof (G.terminalFrontier (L.warpAt a)) ⊆
        G.strictRoof (G.terminalFrontier (L.warpAt b))) :
    L.HasStrictFrontierChronology := by
  intro a b hab
  rw [L.frontier_eq_essential_terminalFrontier hroof a,
    L.frontier_eq_essential_terminalFrontier hroof b,
    G.strictRoof_essential]
  apply Set.disjoint_left.2
  intro x hxa hxb
  exact Set.disjoint_left.1
    (G.disjoint_strictRoof_essential
      (G.terminalFrontier (L.warpAt b)))
    (hstrict a b hab hxa) hxb

end KappaLadder
end DWeb
end Erdos599
