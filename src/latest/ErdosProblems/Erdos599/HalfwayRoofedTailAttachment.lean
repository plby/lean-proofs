/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.BlueprintSplice
import ErdosProblems.Erdos599.HalfwayBoundedTargetLinkage
import ErdosProblems.Erdos599.SliceSpliceSource

/-!
# Attaching simultaneous target tails to a roofed half-way blueprint

The local half-way transaction stops at the later club frontier.  Its target
continuations do not lie below that frontier, so they must not be inserted in
the local stage datum.  This file implements the separate, source-faithful
operation: reinterpret one simultaneous ambient target linkage in the
imaginary graph and source-star it onto a roofed blueprint.  The exact
one-point incidence theorem for the lifted stage linkage proves compatibility.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- Reinterpret an arbitrary original-web path in the imaginary graph.  This
version, unlike `liftOriginal`, also accepts rays. -/
def liftOriginalDPath (p : Gamma.DPath) :
    Path (imaginaryGraph Gamma Y kappa) :=
  p.restrictGraphOnEdges fun e he ↦
    original_adj_imaginaryGraph (p.edgeSet_subset_adj he)

@[simp] theorem liftOriginalDPath_support (p : Gamma.DPath) :
    (liftOriginalDPath (Y := Y) (kappa := kappa) p).support = p.support :=
  p.support_restrictGraphOnEdges _

@[simp] theorem liftOriginalDPath_initial (p : Gamma.DPath) :
    (liftOriginalDPath (Y := Y) (kappa := kappa) p).initial = p.initial :=
  p.initial_restrictGraphOnEdges _

@[simp] theorem liftOriginalDPath_terminal (p : Gamma.DPath) :
    (liftOriginalDPath (Y := Y) (kappa := kappa) p).terminal? = p.terminal? :=
  p.terminal_restrictGraphOnEdges _

private theorem walk_edgeSet_restrictGraphOnEdges
    {D E : Digraph V} : ∀ {a b : V} (p : Walk D a b)
      (h : ∀ e, e ∈ p.edgeSet → E.Adj e.1 e.2),
      (Walk.restrictGraphOnEdges p h).edgeSet = p.edgeSet
  | _, _, .nil, _ => rfl
  | _, _, .cons e p, h => by
      simp only [Walk.restrictGraphOnEdges, Walk.edgeSet_cons]
      congr 1
      exact walk_edgeSet_restrictGraphOnEdges p _

private theorem walk_edgeSet_append_local
    {D : Digraph V} {a b c : V} (p : Walk D a b) (q : Walk D b c) :
    (p.append q).edgeSet = p.edgeSet ∪ q.edgeSet := by
  induction p with
  | nil => simp [Walk.edgeSet]
  | cons e p ih =>
      ext z
      simp only [Walk.append, Walk.edgeSet_cons, ih, Set.mem_union,
        Set.mem_singleton_iff]
      tauto

private theorem finitePath_edgeSet_appendFinite_local
    {D : Digraph V} (p q : FinitePath D)
    (hstart : q.start = p.finish)
    (hinter : p.support ∩ q.support ⊆ {p.finish}) :
    (p.appendFinite q hstart hinter).edgeSet =
      p.edgeSet ∪ q.edgeSet := by
  rcases p with ⟨ps, pf, pw, hp⟩
  rcases q with ⟨qs, qf, qw, hq⟩
  dsimp only at hstart
  subst qs
  change (pw.append qw).edgeSet = pw.edgeSet ∪ qw.edgeSet
  exact walk_edgeSet_append_local pw qw

@[simp] theorem liftOriginalDPath_edgeSet (p : Gamma.DPath) :
    (liftOriginalDPath (Y := Y) (kappa := kappa) p).edgeSet = p.edgeSet := by
  rcases p with p | r
  · exact walk_edgeSet_restrictGraphOnEdges p.walk _
  · rfl

/-- Pointwise change of graph for a whole original-web family. -/
def liftOriginalFamily (P : Set Gamma.DPath) :
    Set (Path (imaginaryGraph Gamma Y kappa)) :=
  liftOriginalDPath (Y := Y) (kappa := kappa) '' P

@[simp] theorem mem_liftOriginalFamily {P : Set Gamma.DPath}
    {q : Path (imaginaryGraph Gamma Y kappa)} :
    q ∈ liftOriginalFamily (Y := Y) (kappa := kappa) P ↔
      ∃ p ∈ P, liftOriginalDPath (Y := Y) (kappa := kappa) p = q := by
  rfl

theorem isWarp_liftOriginalFamily {P : Set Gamma.DPath}
    (hP : Gamma.IsWarp P) :
    (imaginaryWeb Gamma Y kappa).IsWarp
      (liftOriginalFamily (Y := Y) (kappa := kappa) P) := by
  rintro q ⟨p, hpP, rfl⟩ s ⟨r, hrP, rfl⟩ hne
  change Disjoint
    (liftOriginalDPath (Y := Y) (kappa := kappa) p).support
    (liftOriginalDPath (Y := Y) (kappa := kappa) r).support
  rw [liftOriginalDPath_support, liftOriginalDPath_support]
  apply hP hpP hrP
  intro hpr
  apply hne
  subst r
  rfl

theorem hasFiniteCharacter_liftOriginalFamily {P : Set Gamma.DPath}
    (hP : Gamma.HasFiniteCharacter P) :
    (imaginaryWeb Gamma Y kappa).HasFiniteCharacter
      (liftOriginalFamily (Y := Y) (kappa := kappa) P) := by
  rintro q ⟨p, hpP, rfl⟩
  obtain ⟨f, rfl⟩ := hP hpP
  refine ⟨f.restrictGraphOnEdges (fun e he ↦
    original_adj_imaginaryGraph (f.edgeSet_subset_adj he)), rfl⟩

@[simp] theorem vertexSet_liftOriginalFamily (P : Set Gamma.DPath) :
    (imaginaryWeb Gamma Y kappa).vertexSet
      (liftOriginalFamily (Y := Y) (kappa := kappa) P) =
        Gamma.vertexSet P := by
  ext x
  constructor
  · rintro ⟨q, ⟨p, hpP, rfl⟩, hxq⟩
    change x ∈ (liftOriginalDPath (Y := Y) (kappa := kappa) p).support at hxq
    rw [liftOriginalDPath_support] at hxq
    exact ⟨p, hpP, hxq⟩
  · rintro ⟨p, hpP, hxp⟩
    exact ⟨liftOriginalDPath (Y := Y) (kappa := kappa) p,
      ⟨p, hpP, rfl⟩, by
        change x ∈ (liftOriginalDPath (Y := Y) (kappa := kappa) p).support
        rw [liftOriginalDPath_support]
        exact hxp⟩

@[simp] theorem initialSet_liftOriginalFamily (P : Set Gamma.DPath) :
    (imaginaryWeb Gamma Y kappa).initialSet
      (liftOriginalFamily (Y := Y) (kappa := kappa) P) =
        Gamma.initialSet P := by
  ext x
  constructor
  · rintro ⟨q, ⟨p, hpP, rfl⟩, hqx⟩
    change (liftOriginalDPath (Y := Y) (kappa := kappa) p).initial = x at hqx
    rw [liftOriginalDPath_initial] at hqx
    exact ⟨p, hpP, hqx⟩
  · rintro ⟨p, hpP, hpx⟩
    exact ⟨liftOriginalDPath (Y := Y) (kappa := kappa) p,
      ⟨p, hpP, rfl⟩, by
        change (liftOriginalDPath (Y := Y) (kappa := kappa) p).initial = x
        rw [liftOriginalDPath_initial]
        exact hpx⟩

@[simp] theorem terminalFrontier_liftOriginalFamily (P : Set Gamma.DPath) :
    (imaginaryWeb Gamma Y kappa).terminalFrontier
      (liftOriginalFamily (Y := Y) (kappa := kappa) P) =
        Gamma.terminalFrontier P := by
  ext x
  constructor
  · rintro ⟨q, ⟨p, hpP, rfl⟩, hqx⟩
    change (liftOriginalDPath (Y := Y) (kappa := kappa) p).terminal? = some x at hqx
    rw [liftOriginalDPath_terminal] at hqx
    exact ⟨p, hpP, hqx⟩
  · rintro ⟨p, hpP, hpx⟩
    exact ⟨liftOriginalDPath (Y := Y) (kappa := kappa) p,
      ⟨p, hpP, rfl⟩, by
        change (liftOriginalDPath (Y := Y) (kappa := kappa) p).terminal? = some x
        rw [liftOriginalDPath_terminal]
        exact hpx⟩

theorem edgeSet_liftOriginalFamily (P : Set Gamma.DPath) :
    ⋃ q ∈ liftOriginalFamily (Y := Y) (kappa := kappa) P, q.edgeSet =
      familyEdges P := by
  ext e
  constructor
  · simp only [Set.mem_iUnion]
    rintro ⟨q, hq, he⟩
    obtain ⟨p, hpP, rfl⟩ := hq
    rw [liftOriginalDPath_edgeSet] at he
    simp only [familyEdges, Set.mem_iUnion]
    exact ⟨p, hpP, he⟩
  · simp only [familyEdges, Set.mem_iUnion]
    rintro ⟨p, hpP, he⟩
    refine ⟨liftOriginalDPath (Y := Y) (kappa := kappa) p,
      ⟨p, hpP, rfl⟩, ?_⟩
    rw [liftOriginalDPath_edgeSet]
    exact he

/-- The usual upper terminal-frontier bound for source star does not require
finite character of the entire old family: a member witnessing a terminal is
itself necessarily finite. -/
theorem terminalFrontier_star_subset_general
    {G : DWeb V} {W U : Set G.DPath}
    (hcompat : G.StarCompatible W U)
    (hcover : G.terminalFrontier W ⊆ G.initialSet U) :
    G.terminalFrontier (G.star hcompat) ⊆ G.terminalFrontier U := by
  rintro z ⟨r, ⟨p, rfl⟩, hrz⟩
  rcases p with ⟨p, hpW⟩
  rcases p with f | ray
  · have hmatch : ∃ q ∈ U, q.initial = f.finish := by
      obtain ⟨q, hqU, hqstart⟩ := hcover ⟨.inl f, hpW, rfl⟩
      exact ⟨q, hqU, hqstart⟩
    simp only [DWeb.starPath] at hrz
    rw [dif_pos hmatch] at hrz
    let q := Classical.choose hmatch
    have hqU : q ∈ U := (Classical.choose_spec hmatch).1
    have hqstart : q.initial = f.finish :=
      (Classical.choose_spec hmatch).2
    have hinter : f.support ∩ q.support ⊆ {f.finish} := by
      intro x hx
      have hx' := hcompat (.inl f) hpW q hqU x hx.1 hx.2
      exact Set.mem_singleton_iff.2 (Option.some.inj hx'.1).symm
    refine ⟨q, hqU, ?_⟩
    have hterm := Path.terminal?_appendFinite f q hqstart hinter
    change q.terminal? = some z
    rw [← hterm]
    dsimp only [q]
    exact hrz
  · simp only [DWeb.starPath] at hrz
    simp [DWeb.terminal?, Path.terminal?] at hrz

private theorem edgeSet_appendFinite_subset_union_of_finite
    {G : DWeb V} (f : FinitePath G.graph) (q : G.DPath)
    (hstart : q.initial = f.finish)
    (hinter : f.support ∩ q.support ⊆ {f.finish})
    (hqfinite : ∃ g : FinitePath G.graph, q = .inl g) :
    (Path.appendFinite f q hstart hinter).edgeSet ⊆
      f.edgeSet ∪ q.edgeSet := by
  rcases q with g | ray
  · intro e he
    have hstart' : g.start = f.finish := hstart
    have hinter' : f.support ∩ g.support ⊆ {f.finish} := hinter
    change e ∈ (f.appendFinite g hstart' hinter').edgeSet at he
    change e ∈ f.edgeSet ∪ g.edgeSet
    rw [finitePath_edgeSet_appendFinite_local f g hstart' hinter'] at he
    exact he
  · obtain ⟨g, hg⟩ := hqfinite
    cases hg

/-- Every edge in a source star comes from one of its two input families.
Finite character is needed only for the new family, in order to expose the
finite append selected by `starPath`. -/
theorem edgeSet_star_subset_union
    {G : DWeb V} {W U : Set G.DPath}
    (hUfinite : G.HasFiniteCharacter U)
    (hcompat : G.StarCompatible W U) :
    (⋃ r ∈ G.star hcompat, r.edgeSet) ⊆
      (⋃ p ∈ W, p.edgeSet) ∪ (⋃ q ∈ U, q.edgeSet) := by
  intro e he
  simp only [Set.mem_iUnion] at he
  obtain ⟨r, ⟨p, rfl⟩, he⟩ := he
  rcases p with ⟨p, hpW⟩
  rcases p with f | ray
  · simp only [DWeb.starPath] at he
    split at he
    next hmatch =>
      let q := Classical.choose hmatch
      have hqU : q ∈ U := (Classical.choose_spec hmatch).1
      have hqstart : q.initial = f.finish :=
        (Classical.choose_spec hmatch).2
      have hinter : f.support ∩ q.support ⊆ {f.finish} := by
        intro x hx
        have hx' := hcompat (.inl f) hpW q hqU x hx.1 hx.2
        exact Set.mem_singleton_iff.2 (Option.some.inj hx'.1).symm
      have he' := edgeSet_appendFinite_subset_union_of_finite
        f q hqstart hinter (hUfinite hqU) he
      rcases he' with he | he
      · apply Set.mem_union_left
        exact Set.mem_iUnion.2 ⟨(Sum.inl f : G.DPath),
          Set.mem_iUnion.2 ⟨hpW, he⟩⟩
      · apply Set.mem_union_right
        exact Set.mem_iUnion.2 ⟨q,
          Set.mem_iUnion.2 ⟨hqU, he⟩⟩
    next _ =>
      apply Set.mem_union_left
      exact Set.mem_iUnion.2 ⟨(Sum.inl f : G.DPath),
        Set.mem_iUnion.2 ⟨hpW, he⟩⟩
  · apply Set.mem_union_left
    exact Set.mem_iUnion.2 ⟨(Sum.inr ray : G.DPath),
      Set.mem_iUnion.2 ⟨hpW, he⟩⟩

/-- A roofed blueprint and a simultaneous later-stage target linkage meet in
exactly the endpoint configuration required by source star. -/
theorem starCompatible_liftOriginalFamily_of_roof
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : LinkageBlueprint Gamma Y kappa) {A : Set V}
    (hWroof : W.vertexSet ⊆ C.outerRoof)
    (hWterminal : W.terminalSet = A)
    {P : Set (C.ladder.stageWeb C.newStage).DPath}
    (hA : A ⊆ C.newSlice)
    (hP : CardinalInduction.IsLinkageBetween
      (C.ladder.stageWeb C.newStage) A
        (C.ladder.stageWeb C.newStage).target P) :
    (imaginaryWeb Gamma Y kappa).StarCompatible W.paths
      (liftOriginalFamily (Y := Y) (kappa := kappa)
        (CardinalInduction.SliceSegmentCore.liftStageFamily
          C.ladder C.newStage P)) := by
  intro p hpW q hqU x hxp hxq
  have hxRoof : x ∈ C.outerRoof := hWroof ⟨p, hpW, hxp⟩
  have hxLift : x ∈ Gamma.vertexSet
      (CardinalInduction.SliceSegmentCore.liftStageFamily
        C.ladder C.newStage P) := by
    rw [← vertexSet_liftOriginalFamily (Y := Y) (kappa := kappa)]
    exact ⟨q, hqU, hxq⟩
  have hxA : x ∈ A := by
    rw [← ClubStageGeometry.vertexSet_liftNewStageFamily_inter_outerRoof
      C hA hP]
    exact ⟨hxLift, hxRoof⟩
  have hxTerminal : x ∈ W.terminalSet := hWterminal.symm ▸ hxA
  have hpTerminal : (imaginaryWeb Gamma Y kappa).terminal? p = some x :=
    DWeb.IsWarp.terminal_eq_of_mem_support_mem_terminalFrontier
      (imaginaryWeb Gamma Y kappa) W.isWarp hpW hxp hxTerminal
  obtain ⟨r, hrLift, rfl⟩ := hqU
  rw [CardinalInduction.SliceSegmentCore.mem_liftStageFamily] at hrLift
  obtain ⟨s, hsP, rfl⟩ := hrLift
  have hxInitial : x ∈
      (C.ladder.stageWeb C.newStage).initialSet P :=
    hP.initialSet_eq.symm ▸ hxA
  obtain ⟨t, htP, htInitial⟩ := hxInitial
  have hst : s = t := by
    apply Alternating.DWeb.IsWarp.eq_of_mem_support hP.isWarp hsP htP
    · have hxsLift : x ∈
          (C.ladder.liftStagePath C.newStage s).support := by
        have hsupp := liftOriginalDPath_support
          (Y := Y) (kappa := kappa)
          (C.ladder.liftStagePath C.newStage s)
        exact Eq.mp (congrArg (fun S : Set V ↦ x ∈ S) hsupp) hxq
      rw [C.ladder.support_liftStagePath] at hxsLift
      exact hxsLift
    · have : t.initial ∈ t.support := t.initial_mem_support
      rwa [htInitial] at this
  subst t
  refine ⟨hpTerminal, ?_⟩
  change
    (liftOriginalDPath (Y := Y) (kappa := kappa)
      (C.ladder.liftStagePath C.newStage s)).initial = x
  rw [liftOriginalDPath_initial, C.ladder.initial_liftStagePath]
  exact htInitial

/-- Reference-indexed generalization of
`starCompatible_liftOriginalFamily_of_roof`.  The club geometry selects the
ambient later-stage linkage, while the roofed blueprint may live in the
imaginary graph of a different reference warp.  Only the common ambient roof
and the original-web target tails enter the incidence proof. -/
theorem starCompatible_liftOriginalFamily_of_roof_acrossReference
    {Z : Set Gamma.DPath}
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : LinkageBlueprint Gamma Z kappa) {A : Set V}
    (hWroof : W.vertexSet ⊆ C.outerRoof)
    (hWterminal : W.terminalSet = A)
    {P : Set (C.ladder.stageWeb C.newStage).DPath}
    (hA : A ⊆ C.newSlice)
    (hP : CardinalInduction.IsLinkageBetween
      (C.ladder.stageWeb C.newStage) A
        (C.ladder.stageWeb C.newStage).target P) :
    (imaginaryWeb Gamma Z kappa).StarCompatible W.paths
      (liftOriginalFamily (Y := Z) (kappa := kappa)
        (CardinalInduction.SliceSegmentCore.liftStageFamily
          C.ladder C.newStage P)) := by
  intro p hpW q hqU x hxp hxq
  have hxRoof : x ∈ C.outerRoof := hWroof ⟨p, hpW, hxp⟩
  have hxLift : x ∈ Gamma.vertexSet
      (CardinalInduction.SliceSegmentCore.liftStageFamily
        C.ladder C.newStage P) := by
    rw [← vertexSet_liftOriginalFamily (Y := Z) (kappa := kappa)]
    exact ⟨q, hqU, hxq⟩
  have hxA : x ∈ A := by
    rw [← ClubStageGeometry.vertexSet_liftNewStageFamily_inter_outerRoof
      C hA hP]
    exact ⟨hxLift, hxRoof⟩
  have hxTerminal : x ∈ W.terminalSet := hWterminal.symm ▸ hxA
  have hpTerminal : (imaginaryWeb Gamma Z kappa).terminal? p = some x :=
    DWeb.IsWarp.terminal_eq_of_mem_support_mem_terminalFrontier
      (imaginaryWeb Gamma Z kappa) W.isWarp hpW hxp hxTerminal
  obtain ⟨r, hrLift, rfl⟩ := hqU
  rw [CardinalInduction.SliceSegmentCore.mem_liftStageFamily] at hrLift
  obtain ⟨s, hsP, rfl⟩ := hrLift
  have hxInitial : x ∈
      (C.ladder.stageWeb C.newStage).initialSet P :=
    hP.initialSet_eq.symm ▸ hxA
  obtain ⟨t, htP, htInitial⟩ := hxInitial
  have hst : s = t := by
    apply Alternating.DWeb.IsWarp.eq_of_mem_support hP.isWarp hsP htP
    · have hxsLift : x ∈
          (C.ladder.liftStagePath C.newStage s).support := by
        have hsupp := liftOriginalDPath_support
          (Y := Z) (kappa := kappa)
          (C.ladder.liftStagePath C.newStage s)
        exact Eq.mp (congrArg (fun S : Set V ↦ x ∈ S) hsupp) hxq
      rw [C.ladder.support_liftStagePath] at hxsLift
      exact hxsLift
    · have : t.initial ∈ t.support := t.initial_mem_support
      rwa [htInitial] at this
  subst t
  refine ⟨hpTerminal, ?_⟩
  change
    (liftOriginalDPath (Y := Z) (kappa := kappa)
      (C.ladder.liftStagePath C.newStage s)).initial = x
  rw [liftOriginalDPath_initial, C.ladder.initial_liftStagePath]
  exact htInitial

/-- Attach later-stage target tails to a roofed blueprint whose reference
warp need not be the reference parameter used to choose the club geometry. -/
def attachTargetTailsAcrossReference
    {Z : Set Gamma.DPath}
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : LinkageBlueprint Gamma Z kappa) {A : Set V}
    (hWroof : W.vertexSet ⊆ C.outerRoof)
    (hWterminal : W.terminalSet = A)
    {P : Set (C.ladder.stageWeb C.newStage).DPath}
    (hA : A ⊆ C.newSlice)
    (hP : CardinalInduction.IsLinkageBetween
      (C.ladder.stageWeb C.newStage) A
        (C.ladder.stageWeb C.newStage).target P) :
    LinkageBlueprint Gamma Z kappa where
  paths := (imaginaryWeb Gamma Z kappa).star
    (starCompatible_liftOriginalFamily_of_roof_acrossReference
      C W hWroof hWterminal hA hP)

/-- Source star retains every vertex of the roofed front.  The target-tail
attachment may add vertices outside the club roof, but it never deletes a
front vertex. -/
theorem vertexSet_subset_attachTargetTailsAcrossReference
    {Z : Set Gamma.DPath}
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : LinkageBlueprint Gamma Z kappa) {A : Set V}
    (hWroof : W.vertexSet ⊆ C.outerRoof)
    (hWterminal : W.terminalSet = A)
    {P : Set (C.ladder.stageWeb C.newStage).DPath}
    (hA : A ⊆ C.newSlice)
    (hP : CardinalInduction.IsLinkageBetween
      (C.ladder.stageWeb C.newStage) A
        (C.ladder.stageWeb C.newStage).target P) :
    W.vertexSet ⊆
      (attachTargetTailsAcrossReference
        C W hWroof hWterminal hA hP).vertexSet := by
  let hc := starCompatible_liftOriginalFamily_of_roof_acrossReference
    C W hWroof hWterminal hA hP
  rintro x ⟨p, hpW, hxp⟩
  let ps : W.paths := ⟨p, hpW⟩
  refine ⟨(imaginaryWeb Gamma Z kappa).starPath hc ps, ⟨ps, rfl⟩, ?_⟩
  exact Path.support_mono_of_extends
    ((imaginaryWeb Gamma Z kappa).extends_starPath hc ps) hxp
  isWarp := (imaginaryWeb Gamma Z kappa).isWarp_star W.isWarp
    (isWarp_liftOriginalFamily
      (CardinalInduction.SliceDeltaLift.IsLinkageBetween.liftStageFamily hP).isWarp)
    (starCompatible_liftOriginalFamily_of_roof_acrossReference
      C W hWroof hWterminal hA hP)

@[simp] theorem attachTargetTailsAcrossReference_initialSet
    {Z : Set Gamma.DPath}
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : LinkageBlueprint Gamma Z kappa) {A : Set V}
    (hWroof : W.vertexSet ⊆ C.outerRoof)
    (hWterminal : W.terminalSet = A)
    {P : Set (C.ladder.stageWeb C.newStage).DPath}
    (hA : A ⊆ C.newSlice)
    (hP : CardinalInduction.IsLinkageBetween
      (C.ladder.stageWeb C.newStage) A
        (C.ladder.stageWeb C.newStage).target P) :
    (attachTargetTailsAcrossReference
      C W hWroof hWterminal hA hP).initialSet = W.initialSet := by
  exact CardinalInduction.SliceSpliceSource.initialSet_star_eq
    (starCompatible_liftOriginalFamily_of_roof_acrossReference
      C W hWroof hWterminal hA hP)

theorem attachTargetTailsAcrossReference_terminalSet_subset_target
    {Z : Set Gamma.DPath}
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : LinkageBlueprint Gamma Z kappa) {A : Set V}
    (hWroof : W.vertexSet ⊆ C.outerRoof)
    (hWterminal : W.terminalSet = A)
    {P : Set (C.ladder.stageWeb C.newStage).DPath}
    (hA : A ⊆ C.newSlice)
    (hP : CardinalInduction.IsLinkageBetween
      (C.ladder.stageWeb C.newStage) A
        (C.ladder.stageWeb C.newStage).target P) :
    (attachTargetTailsAcrossReference
      C W hWroof hWterminal hA hP).terminalSet ⊆ Gamma.target := by
  let L := CardinalInduction.SliceSegmentCore.liftStageFamily
    C.ladder C.newStage P
  let U : Set (imaginaryWeb Gamma Z kappa).DPath :=
    liftOriginalFamily (Y := Z) (kappa := kappa) L
  let hc := starCompatible_liftOriginalFamily_of_roof_acrossReference
    C W hWroof hWterminal hA hP
  have hUinitial : (imaginaryWeb Gamma Z kappa).initialSet U = A := by
    dsimp only [U]
    rw [initialSet_liftOriginalFamily]
    dsimp only [L]
    rw [CardinalInduction.SliceSegmentCore.initialSet_liftStageFamily,
      hP.initialSet_eq]
  have hcover : (imaginaryWeb Gamma Z kappa).terminalFrontier W.paths ⊆
      (imaginaryWeb Gamma Z kappa).initialSet U := by
    intro x hx
    have hxA : x ∈ A := by
      change x ∈ W.terminalSet at hx
      exact hWterminal ▸ hx
    exact hUinitial.symm ▸ hxA
  have hupper := terminalFrontier_star_subset_general hc hcover
  intro x hx
  have hxU : x ∈ (imaginaryWeb Gamma Z kappa).terminalFrontier U :=
    hupper (by
      change x ∈ (imaginaryWeb Gamma Z kappa).terminalFrontier
        ((imaginaryWeb Gamma Z kappa).star hc)
      exact hx)
  dsimp only [U] at hxU
  rw [terminalFrontier_liftOriginalFamily] at hxU
  dsimp only [L] at hxU
  rw [CardinalInduction.SliceSegmentCore.terminalFrontier_liftStageFamily]
    at hxU
  exact hP.2.2.2.1 hxU

theorem attachTargetTailsAcrossReference_edge_real
    {Z : Set Gamma.DPath}
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : LinkageBlueprint Gamma Z kappa) {A : Set V}
    (hWroof : W.vertexSet ⊆ C.outerRoof)
    (hWterminal : W.terminalSet = A)
    {P : Set (C.ladder.stageWeb C.newStage).DPath}
    (hA : A ⊆ C.newSlice)
    (hP : CardinalInduction.IsLinkageBetween
      (C.ladder.stageWeb C.newStage) A
        (C.ladder.stageWeb C.newStage).target P)
    (hWreal : W.IsEdgeReal) :
    (attachTargetTailsAcrossReference
      C W hWroof hWterminal hA hP).IsEdgeReal := by
  let L := CardinalInduction.SliceSegmentCore.liftStageFamily
    C.ladder C.newStage P
  let U : Set (imaginaryWeb Gamma Z kappa).DPath :=
    liftOriginalFamily (Y := Z) (kappa := kappa) L
  let hc := starCompatible_liftOriginalFamily_of_roof_acrossReference
    C W hWroof hWterminal hA hP
  have hLfinite : Gamma.HasFiniteCharacter L :=
    CardinalInduction.SliceSegmentCore.liftStageFamily_finiteCharacter
      C.ladder C.newStage hP.finiteCharacter
  have hUfinite : (imaginaryWeb Gamma Z kappa).HasFiniteCharacter U :=
    hasFiniteCharacter_liftOriginalFamily hLfinite
  intro e he
  have he' := edgeSet_star_subset_union hUfinite hc he
  rcases he' with heOld | heNew
  · exact hWreal heOld
  · have heFamily : e ∈ familyEdges L := by
      rw [← edgeSet_liftOriginalFamily (Y := Z) (kappa := kappa) L]
      exact heNew
    simp only [familyEdges, Set.mem_iUnion] at heFamily
    obtain ⟨p, hpL, hep⟩ := heFamily
    exact p.edgeSet_subset_adj hep

/-- Select and attach the simultaneous target linkage across distinct
reference indices. -/
theorem ClubStageGeometry.exists_edgeRealTargetAttachmentAcrossReference
    {Z : Set Gamma.DPath}
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hlower : CardinalInduction.UniversalCardinalInductionBelow V kappa)
    (hext : CardinalInduction.UniversalExtensionClauseAt V kappa)
    (W : LinkageBlueprint Gamma Z kappa) {A : Set V}
    (hWroof : W.vertexSet ⊆ C.outerRoof)
    (hWterminal : W.terminalSet = A)
    (hA : A ⊆ C.newSlice) (hcard : #A ≤ kappa)
    (hWreal : W.IsEdgeReal) :
    ∃ U : LinkageBlueprint Gamma Z kappa,
      U.initialSet = W.initialSet ∧
        U.terminalSet ⊆ Gamma.target ∧ U.IsEdgeReal := by
  obtain ⟨P, hP⟩ := C.exists_newStageTargetLinkage_of_mk_le
    hlower hext hA hcard
  let U := attachTargetTailsAcrossReference
    C W hWroof hWterminal hA hP
  exact ⟨U,
    attachTargetTailsAcrossReference_initialSet
      C W hWroof hWterminal hA hP,
    attachTargetTailsAcrossReference_terminalSet_subset_target
      C W hWroof hWterminal hA hP,
    attachTargetTailsAcrossReference_edge_real
      C W hWroof hWterminal hA hP hWreal⟩

/-- Source-star the simultaneous target tails onto a roofed blueprint.  The
result is again a genuine linkage blueprint; no target tail is claimed to lie
inside the local club roof. -/
def attachTargetTails
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : LinkageBlueprint Gamma Y kappa) {A : Set V}
    (hWroof : W.vertexSet ⊆ C.outerRoof)
    (hWterminal : W.terminalSet = A)
    {P : Set (C.ladder.stageWeb C.newStage).DPath}
    (hA : A ⊆ C.newSlice)
    (hP : CardinalInduction.IsLinkageBetween
      (C.ladder.stageWeb C.newStage) A
        (C.ladder.stageWeb C.newStage).target P) :
    LinkageBlueprint Gamma Y kappa where
  paths := (imaginaryWeb Gamma Y kappa).star
    (starCompatible_liftOriginalFamily_of_roof
      C W hWroof hWterminal hA hP)
  isWarp := (imaginaryWeb Gamma Y kappa).isWarp_star W.isWarp
    (isWarp_liftOriginalFamily
      (CardinalInduction.SliceDeltaLift.IsLinkageBetween.liftStageFamily hP).isWarp)
    (starCompatible_liftOriginalFamily_of_roof
      C W hWroof hWterminal hA hP)

@[simp] theorem attachTargetTails_initialSet
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : LinkageBlueprint Gamma Y kappa) {A : Set V}
    (hWroof : W.vertexSet ⊆ C.outerRoof)
    (hWterminal : W.terminalSet = A)
    {P : Set (C.ladder.stageWeb C.newStage).DPath}
    (hA : A ⊆ C.newSlice)
    (hP : CardinalInduction.IsLinkageBetween
      (C.ladder.stageWeb C.newStage) A
        (C.ladder.stageWeb C.newStage).target P) :
    (attachTargetTails C W hWroof hWterminal hA hP).initialSet =
      W.initialSet := by
  exact CardinalInduction.SliceSpliceSource.initialSet_star_eq
    (starCompatible_liftOriginalFamily_of_roof
      C W hWroof hWterminal hA hP)

theorem attachTargetTails_terminalSet_subset_target
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : LinkageBlueprint Gamma Y kappa) {A : Set V}
    (hWroof : W.vertexSet ⊆ C.outerRoof)
    (hWterminal : W.terminalSet = A)
    {P : Set (C.ladder.stageWeb C.newStage).DPath}
    (hA : A ⊆ C.newSlice)
    (hP : CardinalInduction.IsLinkageBetween
      (C.ladder.stageWeb C.newStage) A
        (C.ladder.stageWeb C.newStage).target P) :
    (attachTargetTails C W hWroof hWterminal hA hP).terminalSet ⊆
      Gamma.target := by
  let L := CardinalInduction.SliceSegmentCore.liftStageFamily
    C.ladder C.newStage P
  let U : Set (imaginaryWeb Gamma Y kappa).DPath :=
    liftOriginalFamily (Y := Y) (kappa := kappa) L
  let hc := starCompatible_liftOriginalFamily_of_roof
    C W hWroof hWterminal hA hP
  have hUinitial : (imaginaryWeb Gamma Y kappa).initialSet U = A := by
    dsimp only [U]
    rw [initialSet_liftOriginalFamily]
    dsimp only [L]
    rw [
      CardinalInduction.SliceSegmentCore.initialSet_liftStageFamily,
      hP.initialSet_eq]
  have hcover : (imaginaryWeb Gamma Y kappa).terminalFrontier W.paths ⊆
      (imaginaryWeb Gamma Y kappa).initialSet U := by
    intro x hx
    have hxA : x ∈ A := by
      change x ∈ W.terminalSet at hx
      exact hWterminal ▸ hx
    exact hUinitial.symm ▸ hxA
  have hupper := terminalFrontier_star_subset_general hc hcover
  intro x hx
  have hxU : x ∈ (imaginaryWeb Gamma Y kappa).terminalFrontier U :=
    hupper (by
      change x ∈ (imaginaryWeb Gamma Y kappa).terminalFrontier
        ((imaginaryWeb Gamma Y kappa).star hc)
      exact hx)
  dsimp only [U] at hxU
  rw [terminalFrontier_liftOriginalFamily] at hxU
  dsimp only [L] at hxU
  rw [CardinalInduction.SliceSegmentCore.terminalFrontier_liftStageFamily]
    at hxU
  exact hP.2.2.2.1 hxU

theorem attachTargetTails_finiteCharacter
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : LinkageBlueprint Gamma Y kappa) {A : Set V}
    (hWroof : W.vertexSet ⊆ C.outerRoof)
    (hWterminal : W.terminalSet = A)
    {P : Set (C.ladder.stageWeb C.newStage).DPath}
    (hA : A ⊆ C.newSlice)
    (hP : CardinalInduction.IsLinkageBetween
      (C.ladder.stageWeb C.newStage) A
        (C.ladder.stageWeb C.newStage).target P)
    (hWfinite : (imaginaryWeb Gamma Y kappa).HasFiniteCharacter W.paths) :
    (imaginaryWeb Gamma Y kappa).HasFiniteCharacter
      (attachTargetTails C W hWroof hWterminal hA hP).paths := by
  apply CardinalInduction.SliceSpliceSource.hasFiniteCharacter_star hWfinite
  exact hasFiniteCharacter_liftOriginalFamily
    (CardinalInduction.SliceSegmentCore.liftStageFamily_finiteCharacter
      C.ladder C.newStage hP.finiteCharacter)

theorem attachTargetTails_edge_real
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : LinkageBlueprint Gamma Y kappa) {A : Set V}
    (hWroof : W.vertexSet ⊆ C.outerRoof)
    (hWterminal : W.terminalSet = A)
    {P : Set (C.ladder.stageWeb C.newStage).DPath}
    (hA : A ⊆ C.newSlice)
    (hP : CardinalInduction.IsLinkageBetween
      (C.ladder.stageWeb C.newStage) A
        (C.ladder.stageWeb C.newStage).target P)
    (hWreal : W.IsEdgeReal) :
    (attachTargetTails C W hWroof hWterminal hA hP).IsEdgeReal := by
  let L := CardinalInduction.SliceSegmentCore.liftStageFamily
    C.ladder C.newStage P
  let U : Set (imaginaryWeb Gamma Y kappa).DPath :=
    liftOriginalFamily (Y := Y) (kappa := kappa) L
  let hc := starCompatible_liftOriginalFamily_of_roof
    C W hWroof hWterminal hA hP
  have hLfinite : Gamma.HasFiniteCharacter L := by
    exact CardinalInduction.SliceSegmentCore.liftStageFamily_finiteCharacter
      C.ladder C.newStage hP.finiteCharacter
  have hUfinite : (imaginaryWeb Gamma Y kappa).HasFiniteCharacter U := by
    exact hasFiniteCharacter_liftOriginalFamily hLfinite
  intro e he
  have he' := edgeSet_star_subset_union hUfinite hc he
  rcases he' with heOld | heNew
  · exact hWreal heOld
  · have heFamily : e ∈ familyEdges L := by
      rw [← edgeSet_liftOriginalFamily (Y := Y) (kappa := kappa) L]
      exact heNew
    simp only [familyEdges, Set.mem_iUnion] at heFamily
    obtain ⟨p, hpL, hep⟩ := heFamily
    exact p.edgeSet_subset_adj hep

/-- In a normalized ambient web, an edge-real finite blueprint with full
source initials and target terminals has the endpoint purity required by the
final certificate. -/
theorem endpointPure_of_edgeReal_full
    (U : LinkageBlueprint Gamma Y kappa)
    (hNorm : Gamma.IsNormalized) (hreal : U.IsEdgeReal)
    (hfinite : (imaginaryWeb Gamma Y kappa).HasFiniteCharacter U.paths)
    (hinitial : U.initialSet = Gamma.source)
    (hterminal : U.terminalSet ⊆ Gamma.target) :
    ∀ p ∈ U.paths, U.IsPathBetween Gamma.source Gamma.target p := by
  intro p hpU
  obtain ⟨q, rfl⟩ := hfinite hpU
  have hqstart : q.start ∈ Gamma.source := by
    rw [← hinitial]
    exact ⟨.inl q, hpU, rfl⟩
  have hqfinish : q.finish ∈ Gamma.target :=
    hterminal ⟨.inl q, hpU, rfl⟩
  let qr := U.realFinitePath hreal q hpU
  have eq_start {x : V} (hxq : x ∈ q.support)
      (hxsource : x ∈ Gamma.source) : x = q.start := by
    have hxqr : x ∈ qr.walk.support := by
      change x ∈ qr.support
      dsimp only [qr]
      apply Eq.mpr
        (congrArg (fun S : Set V ↦ x ∈ S)
          (FinitePath.support_restrictGraphOnEdges q _))
      exact hxq
    have hx := hNorm.eq_start_of_mem_walk qr.walk hxqr hxsource
    dsimp only [qr] at hx
    exact hx
  have eq_finish {x : V} (hxq : x ∈ q.support)
      (hxtarget : x ∈ Gamma.target) : x = q.finish := by
    have hxqr : x ∈ qr.walk.support := by
      change x ∈ qr.support
      dsimp only [qr]
      apply Eq.mpr
        (congrArg (fun S : Set V ↦ x ∈ S)
          (FinitePath.support_restrictGraphOnEdges q _))
      exact hxq
    have hx := hNorm.eq_finish_of_mem_walk qr.walk hxqr hxtarget
    dsimp only [qr] at hx
    exact hx
  refine ⟨q, rfl, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · rintro x ⟨hxq, hxsource | hxtarget⟩
      · exact Set.mem_insert_iff.2 (Or.inl (eq_start hxq hxsource))
      · exact Set.mem_insert_iff.2
          (Or.inr (Set.mem_singleton_iff.2 (eq_finish hxq hxtarget)))
    · intro x hx
      rcases Set.mem_insert_iff.1 hx with rfl | hx
      · exact ⟨q.start_mem_support, Or.inl hqstart⟩
      · have hxeq := Set.mem_singleton_iff.1 hx
        subst x
        exact ⟨q.finish_mem_support, Or.inr hqfinish⟩
  · apply Set.Subset.antisymm
    · rintro x ⟨hxq, hxsource⟩
      exact Set.mem_singleton_iff.2 (eq_start hxq hxsource)
    · intro x hx
      have hxeq := Set.mem_singleton_iff.1 hx
      subst x
      exact ⟨q.start_mem_support, hqstart⟩

theorem attachTargetTails_endpointPure
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : LinkageBlueprint Gamma Y kappa) {A : Set V}
    (hWroof : W.vertexSet ⊆ C.outerRoof)
    (hWterminal : W.terminalSet = A)
    {P : Set (C.ladder.stageWeb C.newStage).DPath}
    (hA : A ⊆ C.newSlice)
    (hP : CardinalInduction.IsLinkageBetween
      (C.ladder.stageWeb C.newStage) A
        (C.ladder.stageWeb C.newStage).target P)
    (hWfinite : (imaginaryWeb Gamma Y kappa).HasFiniteCharacter W.paths)
    (hWinitial : W.initialSet = Gamma.source)
    (hWreal : W.IsEdgeReal) :
    ∀ p ∈ (attachTargetTails C W hWroof hWterminal hA hP).paths,
      (attachTargetTails C W hWroof hWterminal hA hP).IsPathBetween
        Gamma.source Gamma.target p := by
  apply endpointPure_of_edgeReal_full
  · exact C.normalized
  · exact attachTargetTails_edge_real
      C W hWroof hWterminal hA hP hWreal
  · exact attachTargetTails_finiteCharacter
      C W hWroof hWterminal hA hP hWfinite
  · rw [attachTargetTails_initialSet, hWinitial]
  · exact attachTargetTails_terminalSet_subset_target
      C W hWroof hWterminal hA hP

/-- Select the simultaneous later-stage target linkage and attach all of its
tails in one operation.  This is the direct consumer expected from the
roofed track of a two-track half-way scheduler. -/
theorem ClubStageGeometry.exists_edgeRealTargetAttachment
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hlower : CardinalInduction.UniversalCardinalInductionBelow V kappa)
    (hext : CardinalInduction.UniversalExtensionClauseAt V kappa)
    (W : LinkageBlueprint Gamma Y kappa) {A : Set V}
    (hWroof : W.vertexSet ⊆ C.outerRoof)
    (hWterminal : W.terminalSet = A)
    (hA : A ⊆ C.newSlice) (hcard : #A ≤ kappa)
    (hWreal : W.IsEdgeReal) :
    ∃ U : LinkageBlueprint Gamma Y kappa,
      U.initialSet = W.initialSet ∧
        U.terminalSet ⊆ Gamma.target ∧ U.IsEdgeReal := by
  obtain ⟨P, hP⟩ := C.exists_newStageTargetLinkage_of_mk_le
    hlower hext hA hcard
  let U := attachTargetTails C W hWroof hWterminal hA hP
  exact ⟨U,
    attachTargetTails_initialSet C W hWroof hWterminal hA hP,
    attachTargetTails_terminalSet_subset_target
      C W hWroof hWterminal hA hP,
    attachTargetTails_edge_real C W hWroof hWterminal hA hP hWreal⟩

/-- Fully resolved form used by the final exact-frontier certificate: in
addition to edge reality and target terminals, the attached blueprint has
finite character and literal endpoint purity. -/
theorem ClubStageGeometry.exists_resolvedTargetAttachment
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hlower : CardinalInduction.UniversalCardinalInductionBelow V kappa)
    (hext : CardinalInduction.UniversalExtensionClauseAt V kappa)
    (W : LinkageBlueprint Gamma Y kappa) {A : Set V}
    (hWroof : W.vertexSet ⊆ C.outerRoof)
    (hWterminal : W.terminalSet = A)
    (hA : A ⊆ C.newSlice) (hcard : #A ≤ kappa)
    (hWreal : W.IsEdgeReal)
    (hWfinite : (imaginaryWeb Gamma Y kappa).HasFiniteCharacter W.paths)
    (hWinitial : W.initialSet = Gamma.source) :
    ∃ U : LinkageBlueprint Gamma Y kappa,
      U.initialSet = Gamma.source ∧ U.terminalSet ⊆ Gamma.target ∧
        U.IsEdgeReal ∧
        (imaginaryWeb Gamma Y kappa).HasFiniteCharacter U.paths ∧
        ∀ p ∈ U.paths, U.IsPathBetween Gamma.source Gamma.target p := by
  obtain ⟨P, hP⟩ := C.exists_newStageTargetLinkage_of_mk_le
    hlower hext hA hcard
  let U := attachTargetTails C W hWroof hWterminal hA hP
  refine ⟨U, ?_, ?_, ?_, ?_, ?_⟩
  · rw [attachTargetTails_initialSet, hWinitial]
  · exact attachTargetTails_terminalSet_subset_target
      C W hWroof hWterminal hA hP
  · exact attachTargetTails_edge_real C W hWroof hWterminal hA hP hWreal
  · exact attachTargetTails_finiteCharacter
      C W hWroof hWterminal hA hP hWfinite
  · exact attachTargetTails_endpointPure
      C W hWroof hWterminal hA hP hWfinite hWinitial hWreal

#print axioms attachTargetTails
#print axioms starCompatible_liftOriginalFamily_of_roof_acrossReference
#print axioms attachTargetTailsAcrossReference
#print axioms attachTargetTailsAcrossReference_initialSet
#print axioms attachTargetTailsAcrossReference_terminalSet_subset_target
#print axioms attachTargetTailsAcrossReference_edge_real
#print axioms
  ClubStageGeometry.exists_edgeRealTargetAttachmentAcrossReference
#print axioms attachTargetTails_initialSet
#print axioms attachTargetTails_terminalSet_subset_target
#print axioms attachTargetTails_edge_real
#print axioms attachTargetTails_endpointPure
#print axioms ClubStageGeometry.exists_edgeRealTargetAttachment
#print axioms ClubStageGeometry.exists_resolvedTargetAttachment

end LinkageBlueprint
end Blueprint
end Erdos599
