/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CardinalInduction
import ErdosProblems.Erdos599.SingularCardinal
import ErdosProblems.Erdos599.WaveLimits

/-!
# Continuing a half-way linkage through its quotient

Assertion 9.17 repeatedly applies the half-way clause in the quotient by
the current stop-over set.  The current warp is a linkage, not a wave, so
the wave-specific quotient-star theorem is not the right interface.  This
file proves the geometric fact actually used there.

Let `W` be a linkage from the source to a trimmed source--target separator
`C`, and let `U` be a full-source warp in `G / C`.  The source explicitly
uses terminal-clean pruning in the nearby proof of Assertion 9.10, but the
one-sentence proof of Assertion 9.17 omits the corresponding compatibility
argument.  Under that exact terminal-clean certificate, every lifted member
of `U` meets a member of `W` only when it starts at that member's terminal.
Consequently source star is defined without any wave hypothesis, remains a
warp, and is an honest forward extension of `W`.

The proof separates the two roles which are conflated in the informal
sentence “use the half-way clause in `G / C`”.  Separation and endpoint
purity put every old linkage path inside `RF(C)`.  Quotient paths, after
their initial vertex, avoid both `C` and `RF^o(C)`.  Trimmedness
`E(C) = C` therefore rules out every unintended intersection.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularContinuation

open DirectedPath

universe u

variable {V : Type u}

/-- The pruning convention used explicitly in the source proof: every
member of the current linkage meets the stop-over only at its terminal. -/
def TerminalCleanAt (G : DWeb V) (W : Set G.DPath) (C : Set V) : Prop :=
  ∀ p ∈ W, ∀ x ∈ p.support, x ∈ C → G.terminal? p = some x

/-- A trimmed source--target separator is exactly the source of the
quotient.  This is the source identity used in Assertion 9.17. -/
theorem quotient_source_eq_stopover
    (G : DWeb V) {C : Set V}
    (hsep : IsSeparatorFrom G G.source C)
    (htrim : IsTrimmedSeparator G C) :
    (G.quotient C).source = C := by
  rw [DWeb.quotient_source, Set.union_comm]
  calc
    G.essential (C ∪ G.source) = G.essential C :=
      RelationalRoof.essential_union_eq_of_subset_roof
        G.graph.Adj G.target hsep
    _ = C := htrim

/-- Coverage of all old terminals is not a competitor-closure fact.  It is
forced by taking a full-source linkage in the quotient, once separation and
trimming identify the quotient source with the old stop-over. -/
theorem terminalFrontier_subset_quotientInitialSet_of_linkage
    (G : DWeb V) {C D : Set V} {W : Set G.DPath}
    (hsep : IsSeparatorFrom G G.source C)
    (htrim : IsTrimmedSeparator G C)
    (hterminal : G.terminalFrontier W ⊆ C)
    {U : Set (G.quotient C).DPath}
    (hU : IsLinkageBetween (G.quotient C)
      (G.quotient C).source D U) :
    G.terminalFrontier W ⊆ (G.quotient C).initialSet U := by
  intro x hx
  rw [hU.initialSet_eq, quotient_source_eq_stopover G hsep htrim]
  exact hterminal hx

/-- Every member of a source--stop-over linkage lies in the roof of the
stop-over.  The disjointness of source and stop-over is exactly what turns
endpoint purity into “the path meets `C` only at its terminal”. -/
theorem linkage_vertexSet_subset_roof
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    (hW : IsLinkageBetween G G.source C W)
    (hsep : IsSeparatorFrom G G.source C)
    (hclean : TerminalCleanAt G W C) :
    G.vertexSet W ⊆ G.roof C := by
  rintro x ⟨p, hpW, hxp⟩
  apply G.pathSupportRoof p C
  · apply hsep
    have hinit : p.initial ∈ G.initialSet W := ⟨p, hpW, rfl⟩
    rw [hW.initialSet_eq] at hinit
    exact hinit
  · intro t ht
    apply hW.terminalFrontier_subset
    exact ⟨p, hpW, ht⟩
  · intro y hy
    rw [hclean p hpW y hy.1 hy.2]
    exact Set.mem_singleton y
  · exact hxp

/-- When source and stop-over are disjoint, endpoint purity supplies the
source's terminal-clean pruning property automatically. -/
theorem terminalCleanAt_of_linkage_of_disjoint
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    (hW : IsLinkageBetween G G.source C W)
    (hdis : Disjoint G.source C) :
    TerminalCleanAt G W C := by
  intro p hpW x hxp hxC
  obtain ⟨f, rfl, hends, _hsource⟩ := hW.endpointPure p hpW
  have hxEnds : x ∈ ({f.start, f.finish} : Set V) := by
    rw [← hends]
    exact ⟨hxp, Or.inr hxC⟩
  have hxFinish : x = f.finish := by
    rcases Set.mem_insert_iff.1 hxEnds with hxStart | hxFinish
    · exfalso
      have hfSource : f.start ∈ G.source := by
        have : f.start ∈ G.initialSet W := ⟨.inl f, hpW, rfl⟩
        rw [hW.initialSet_eq] at this
        exact this
      exact Set.disjoint_left.1 hdis hfSource (hxStart ▸ hxC)
    · exact Set.mem_singleton_iff.1 hxFinish
  change some f.finish = some x
  exact congrArg some hxFinish.symm

/-- Lift a quotient warp to the ambient graph. -/
abbrev liftedQuotientFamily (G : DWeb V) (C : Set V)
    (U : Set (G.quotient C).DPath) : Set G.DPath :=
  G.liftQuotientFamily C U

/-- Appending a finite path to a path known to be finite again produces a
finite path.  This small eliminator keeps the proof independent of the
proof arguments used by `Path.appendFinite`. -/
private theorem appendFinite_finite_of_finite
    {D : Digraph V} (p : DirectedPath.FinitePath D)
    (q : DirectedPath.Path D) (hstart : q.initial = p.finish)
    (hinter : p.support ∩ q.support ⊆ {p.finish})
    (hq : ∃ g : DirectedPath.FinitePath D, q = .inl g) :
    ∃ g : DirectedPath.FinitePath D,
      DirectedPath.Path.appendFinite p q hstart hinter = .inl g := by
  rcases q with q | r
  · exact ⟨p.appendFinite q hstart hinter, rfl⟩
  · obtain ⟨g, hg⟩ := hq
    cases hg

/-- The exact geometric continuation certificate needed in the singular
matrix.  It deliberately speaks about only the pending subwarp: completed
paths may be frozen outside it.  No separation of the whole source, and no
disjointness of the whole source from `C`, is required. -/
theorem starCompatible_liftQuotientFamily_of_roof
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    (hclean : TerminalCleanAt G W C)
    {U : Set (G.quotient C).DPath}
    (hUstart : (G.quotient C).initialSet U ⊆ C) :
    G.StarCompatible W (liftedQuotientFamily G C U) := by
  intro p hpW q hqU x hxp hxq
  obtain ⟨q₀, hq₀U, rfl⟩ := hqU
  have hq₀C : q₀.initial ∈ C :=
    hUstart ⟨q₀, hq₀U, rfl⟩
  have hxRoof : x ∈ G.roof C :=
    hroof ⟨p, hpW, hxp⟩
  have hxClass := G.quotientPath_support_initial_or_avoids C q₀ (by
    simpa only [G.support_liftQuotientPath] using hxq)
  have hxInitial : x = q₀.initial := by
    rcases hxClass with hx | hxAvoid
    · exact hx
    · exfalso
      by_cases hxEssential : x ∈ G.essential C
      · exact hxAvoid.2 (htrim ▸ hxEssential)
      · exact hxAvoid.1 ⟨hxRoof, hxEssential⟩
  have hxC : x ∈ C := hxInitial ▸ hq₀C
  have hxTerminal : G.terminal? p = some x :=
    hclean p hpW x hxp hxC
  exact ⟨hxTerminal, by
    simpa only [G.initial_liftQuotientPath] using hxInitial.symm⟩

/-- Continue only the terminal-clean, roofed pending subwarp.  This is the
source-star operation used after target-completed paths have been frozen. -/
noncomputable def pendingContinuation
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    (hclean : TerminalCleanAt G W C)
    (U : Set (G.quotient C).DPath)
    (hUstart : (G.quotient C).initialSet U ⊆ C) :
    Set G.DPath :=
  G.star (starCompatible_liftQuotientFamily_of_roof
    G hroof htrim hclean hUstart)

/-- The pending continuation is a warp whenever the two input families are
warps. -/
theorem pendingContinuation_isWarp
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    (hW : G.IsWarp W)
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    (hclean : TerminalCleanAt G W C)
    {U : Set (G.quotient C).DPath}
    (hU : (G.quotient C).IsWarp U)
    (hUstart : (G.quotient C).initialSet U ⊆ C) :
    G.IsWarp (pendingContinuation G hroof htrim hclean U hUstart) := by
  apply G.isWarp_star hW
    (DWeb.IsWarp.liftQuotientFamily G hU)

/-- The pending source-star is a genuine forward extension.  This is the
precise order clause used for one row of Assertion 9.17. -/
theorem forwardExtension_pendingContinuation
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    (hclean : TerminalCleanAt G W C)
    (U : Set (G.quotient C).DPath)
    (hUstart : (G.quotient C).initialSet U ⊆ C) :
    G.ForwardExtension W
      (pendingContinuation G hroof htrim hclean U hUstart) := by
  exact G.forwardExtension_star
    (starCompatible_liftQuotientFamily_of_roof
      G hroof htrim hclean hUstart)

/-- Pending continuation preserves precisely the pending initial set. -/
theorem initialSet_pendingContinuation
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    (hclean : TerminalCleanAt G W C)
    (U : Set (G.quotient C).DPath)
    (hUstart : (G.quotient C).initialSet U ⊆ C) :
    G.initialSet (pendingContinuation G hroof htrim hclean U hUstart) =
      G.initialSet W := by
  exact (G.initialSet_eq_of_forwardExtension
    (forwardExtension_pendingContinuation
      G hroof htrim hclean U hUstart)).symm

/-- Source-star introduces no vertices outside the old pending family and
the lifted quotient family. -/
theorem vertexSet_pendingContinuation_subset
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    (hclean : TerminalCleanAt G W C)
    (U : Set (G.quotient C).DPath)
    (hUstart : (G.quotient C).initialSet U ⊆ C) :
    G.vertexSet (pendingContinuation G hroof htrim hclean U hUstart) ⊆
      G.vertexSet W ∪ G.vertexSet (liftedQuotientFamily G C U) := by
  rintro x ⟨r, ⟨p, rfl⟩, hxr⟩
  rcases G.mem_support_starPath_cases
      (starCompatible_liftQuotientFamily_of_roof
        G hroof htrim hclean hUstart) p hxr with hxOld | hxNew
  · exact Or.inl ⟨p.1, p.2, hxOld⟩
  · obtain ⟨_t, q, _hpterm, hq, _hqinit, hxq⟩ := hxNew
    exact Or.inr ⟨q, hq, hxq⟩

/-- Componentwise avoidance is sufficient for the output-dependent cross
disjointness premise of the frozen union. -/
theorem disjoint_vertexSet_pendingContinuation
    (G : DWeb V) {F : Set G.DPath} {C : Set V} {W : Set G.DPath}
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    (hclean : TerminalCleanAt G W C)
    (U : Set (G.quotient C).DPath)
    (hUstart : (G.quotient C).initialSet U ⊆ C)
    (hFW : Disjoint (G.vertexSet F) (G.vertexSet W))
    (hFU : Disjoint (G.vertexSet F)
      (G.vertexSet (liftedQuotientFamily G C U))) :
    Disjoint (G.vertexSet F)
      (G.vertexSet (pendingContinuation G hroof htrim hclean U hUstart)) := by
  apply Set.disjoint_left.2
  intro x hxF hxNew
  rcases vertexSet_pendingContinuation_subset
      G hroof htrim hclean U hUstart hxNew with hxW | hxU
  · exact Set.disjoint_left.1 hFW hxF hxW
  · exact Set.disjoint_left.1 hFU hxF hxU

/-- Finite character is preserved by pending continuation. -/
theorem pendingContinuation_finiteCharacter
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    (hWfinite : G.HasFiniteCharacter W)
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    (hclean : TerminalCleanAt G W C)
    {U : Set (G.quotient C).DPath}
    (hUfinite : (G.quotient C).HasFiniteCharacter U)
    (hUstart : (G.quotient C).initialSet U ⊆ C) :
    G.HasFiniteCharacter
      (pendingContinuation G hroof htrim hclean U hUstart) := by
  let L := liftedQuotientFamily G C U
  let hc : G.StarCompatible W L :=
    starCompatible_liftQuotientFamily_of_roof
      G hroof htrim hclean hUstart
  have hLfinite : G.HasFiniteCharacter L := by
    rintro q ⟨q₀, hq₀U, rfl⟩
    obtain ⟨g, rfl⟩ := hUfinite hq₀U
    let g' : DirectedPath.FinitePath G.graph :=
      g.lift (fun {_ _} h => G.quotient_adj_imp h)
    exact ⟨g', rfl⟩
  rintro r ⟨p, rfl⟩
  rcases p with ⟨p, hpW⟩
  obtain ⟨f, rfl⟩ := hWfinite hpW
  simp only [DWeb.starPath]
  split
  next hmatch =>
    exact appendFinite_finite_of_finite f (Classical.choose hmatch) _ _
      (hLfinite (Classical.choose_spec hmatch).1)
  next _ => exact ⟨f, rfl⟩

/-- Coverage of the old pending frontier gives a lifted quotient path
starting at every old pending terminal. -/
theorem exists_liftedQuotientPath_from_pending_terminal
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    {U : Set (G.quotient C).DPath}
    (hcover : G.terminalFrontier W ⊆
      (G.quotient C).initialSet U)
    {f : DirectedPath.FinitePath G.graph}
    (hfW : (Sum.inl f : G.DPath) ∈ W) :
    ∃ q ∈ liftedQuotientFamily G C U, q.initial = f.finish := by
  have hfInitial : f.finish ∈ (G.quotient C).initialSet U :=
    hcover ⟨.inl f, hfW, rfl⟩
  obtain ⟨q₀, hq₀U, hq₀init⟩ := hfInitial
  refine ⟨G.liftQuotientPath C q₀, ⟨q₀, hq₀U, rfl⟩, ?_⟩
  simpa only [G.initial_liftQuotientPath] using hq₀init

/-- If the chosen quotient family covers all pending terminals, every
terminal left by the source-star comes from that quotient family. -/
theorem terminalFrontier_pendingContinuation_subset
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    (hWfinite : G.HasFiniteCharacter W)
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    (hclean : TerminalCleanAt G W C)
    {U : Set (G.quotient C).DPath}
    (hUstart : (G.quotient C).initialSet U ⊆ C)
    (hcover : G.terminalFrontier W ⊆
      (G.quotient C).initialSet U) :
    G.terminalFrontier
        (pendingContinuation G hroof htrim hclean U hUstart) ⊆
      (G.quotient C).terminalFrontier U := by
  let L := liftedQuotientFamily G C U
  let hc : G.StarCompatible W L :=
    starCompatible_liftQuotientFamily_of_roof
      G hroof htrim hclean hUstart
  rintro z ⟨r, ⟨p, rfl⟩, hrz⟩
  rcases p with ⟨p, hpW⟩
  obtain ⟨f, rfl⟩ := hWfinite hpW
  have hmatch : ∃ q ∈ L, q.initial = f.finish :=
    exists_liftedQuotientPath_from_pending_terminal G hcover hpW
  simp only [DWeb.starPath] at hrz
  rw [dif_pos hmatch] at hrz
  let q := Classical.choose hmatch
  have hqL : q ∈ L := (Classical.choose_spec hmatch).1
  have hqstart : q.initial = f.finish := (Classical.choose_spec hmatch).2
  have hinter : f.support ∩ q.support ⊆ {f.finish} := by
    intro x hx
    have hx' := hc (.inl f) hpW q hqL x hx.1 hx.2
    exact Set.mem_singleton_iff.2 (Option.some.inj hx'.1).symm
  have hqTerminal : G.terminal? q = some z := by
    have hterm := DirectedPath.Path.terminal?_appendFinite
      f q hqstart hinter
    change DirectedPath.Path.terminal? q = some z
    rw [← hterm]
    dsimp only [q]
    exact hrz
  rw [← G.terminalFrontier_liftQuotientFamily C U]
  exact ⟨q, hqL, hqTerminal⟩

/-- Forward extension is stable under adjoining a family which is frozen
verbatim on both sides. -/
theorem forwardExtension_union_frozen
    (G : DWeb V) {F W W' : Set G.DPath}
    (hforward : G.ForwardExtension W W') :
    G.ForwardExtension (F ∪ W) (F ∪ W') := by
  constructor
  · intro p hp
    rcases hp with hpF | hpW
    · exact ⟨p, Or.inl hpF, G.extends_refl p⟩
    · obtain ⟨q, hqW', hpq⟩ := hforward.1 p hpW
      exact ⟨q, Or.inr hqW', hpq⟩
  · intro q hq
    rcases hq with hqF | hqW'
    · exact ⟨q, Or.inl hqF, G.extends_refl q⟩
    · obtain ⟨p, hpW, hpq⟩ := hforward.2 q hqW'
      exact ⟨p, Or.inr hpW, hpq⟩

/-- Two warps with disjoint total vertex sets form a warp. -/
theorem isWarp_union_of_disjoint_vertexSet
    (G : DWeb V) {F W : Set G.DPath}
    (hF : G.IsWarp F) (hW : G.IsWarp W)
    (hcross : Disjoint (G.vertexSet F) (G.vertexSet W)) :
    G.IsWarp (F ∪ W) := by
  intro p hp q hq hpq
  rcases hp with hpF | hpW <;> rcases hq with hqF | hqW
  · exact hF hpF hqF hpq
  · apply Set.disjoint_left.2
    intro x hxp hxq
    exact Set.disjoint_left.1 hcross
      ⟨p, hpF, hxp⟩ ⟨q, hqW, hxq⟩
  · apply Set.disjoint_left.2
    intro x hxp hxq
    exact Set.disjoint_left.1 hcross
      ⟨q, hqF, hxq⟩ ⟨p, hpW, hxp⟩
  · exact hW hpW hqW hpq

/-- A union of finite-character families has finite character. -/
theorem finiteCharacter_union
    (G : DWeb V) {F W : Set G.DPath}
    (hF : G.HasFiniteCharacter F) (hW : G.HasFiniteCharacter W) :
    G.HasFiniteCharacter (F ∪ W) := by
  intro p hp
  exact hp.elim (fun hpF => hF hpF) (fun hpW => hW hpW)

/-! ### What competitor closure actually proves

Competitor closure controls two subfamilies of the *same ambient stage
family*.  It cannot by itself control a newly chosen quotient family, which
is why quotient-selection safety remains a separate construction-specific
obligation below. -/

/-- Every ambient path meeting a path whose initial lies in `S` has its own
initial in any set containing the competitor closure of `S`. -/
theorem pathsMeetingFamily_subset_startPaths_of_competitorClosure
    (G : DWeb V) {X : Set G.DPath} {S T : Set V}
    (hclose : G.competitorClosure X S ⊆ T) :
    G.pathsMeetingFamily X (G.startPaths X S) ⊆ G.startPaths X T := by
  rintro q ⟨hqX, p, ⟨hpX, hpS⟩, hqp⟩
  refine ⟨hqX, hclose ?_⟩
  exact ⟨p.initial, hpS, p, hpX, rfl, q, hqX, rfl,
    by simpa [disjoint_comm] using hqp⟩

/-- The exact disjointness consequence of competitor closure.  The first
family starts in `S`; the second is an ambient-stage subfamily whose starts
remain outside the closed set `T`. -/
theorem disjoint_vertexSet_of_competitorClosure
    (G : DWeb V) {X F R : Set G.DPath} {S T : Set V}
    (hclose : G.competitorClosure X S ⊆ T)
    (hFX : F ⊆ X) (hFstart : ∀ p ∈ F, p.initial ∈ S)
    (hRX : R ⊆ X) (hRoutside : ∀ q ∈ R, q.initial ∉ T) :
    Disjoint (G.vertexSet F) (G.vertexSet R) := by
  apply Set.disjoint_left.2
  intro x hxF hxR
  obtain ⟨p, hpF, hxp⟩ := hxF
  obtain ⟨q, hqR, hxq⟩ := hxR
  apply hRoutside q hqR
  apply hclose
  refine ⟨p.initial, hFstart p hpF, p, hFX hpF, rfl,
    q, hRX hqR, rfl, ?_⟩
  intro hpq
  exact Set.disjoint_left.1 hpq hxp hxq

/-- Canonical complement form used after one matrix-source closing step. -/
theorem disjoint_startPaths_compl_of_competitorClosure
    (G : DWeb V) {X : Set G.DPath} {S T : Set V}
    (hclose : G.competitorClosure X S ⊆ T) :
    Disjoint (G.vertexSet (G.startPaths X S))
      (G.vertexSet (G.startPaths X Tᶜ)) := by
  apply disjoint_vertexSet_of_competitorClosure G hclose
  · exact fun _ hp => hp.1
  · exact fun _ hp => hp.2
  · exact fun _ hp => hp.1
  · intro _ hp
    exact hp.2

/-! Competitor closure contains no information about a family chosen only
after the closing step.  The following one-vertex example makes the logical
boundary executable: closure into `univ` holds, while an unconstrained new
family can reuse the frozen vertex. -/

private def competitorClosureUnitWeb : DWeb Unit where
  graph := ⟨fun _ _ => False⟩
  source := Set.univ
  target := ∅

private def competitorClosureUnitPath : competitorClosureUnitWeb.DPath :=
  DirectedPath.Path.trivial competitorClosureUnitWeb.graph ()

private def competitorClosureUnitFamily :
    Set competitorClosureUnitWeb.DPath :=
  {competitorClosureUnitPath}

/-- Closing the old stage cannot imply disjointness from a newly chosen
family unless the latter is tied to that closing operation by extra data. -/
theorem competitorClosure_does_not_control_new_family :
    competitorClosureUnitWeb.competitorClosure
        competitorClosureUnitFamily Set.univ ⊆ Set.univ ∧
      ¬ Disjoint
        (competitorClosureUnitWeb.vertexSet competitorClosureUnitFamily)
        (competitorClosureUnitWeb.vertexSet competitorClosureUnitFamily) := by
  refine ⟨Set.subset_univ _, ?_⟩
  intro hdis
  have hx : () ∈ competitorClosureUnitWeb.vertexSet
      competitorClosureUnitFamily := by
    refine ⟨competitorClosureUnitPath, Set.mem_singleton _, ?_⟩
    simp [competitorClosureUnitPath, competitorClosureUnitWeb]
  exact Set.disjoint_left.1 hdis hx hx

/-!
## What the general arrow can and cannot attach

The source operation `U ↦ U → W` always produces a forward extension, even
when `U` is not a wave.  Its finite old path is actually continued along a
proposed path `q ∈ W` precisely when the suffix of `q` from the old terminal
has no second contact with `U`.  The following dichotomy makes the failed
case executable.  Notice that the old path witnessing the second contact is
allowed to be the path being continued: self re-entry is a genuine
obstruction and is not repaired merely by closing the source set under
competitors.
-/

/-- A proposed continuation at a covered old terminal is either an arrow
candidate, or its suffix has an explicit extra contact with the old warp. -/
theorem arrowCandidate_or_extra_old_contact
    (G : DWeb V) {U W : Set G.DPath}
    {f : DirectedPath.FinitePath G.graph}
    (hfU : (Sum.inl f : G.DPath) ∈ U)
    {q : G.DPath} (hqW : q ∈ W)
    (hfinish : f.finish ∈ q.support) :
    Nonempty (G.ArrowCandidate U W f) ∨
      ∃ x, x ∈ (q.suffixFrom f.finish hfinish).support ∧
        x ∈ G.vertexSet U ∧ x ≠ f.finish := by
  classical
  let S : Set V :=
    (q.suffixFrom f.finish hfinish).support ∩ G.vertexSet U
  have hfinishInitial :
      (q.suffixFrom f.finish hfinish).initial = f.finish := by
    rcases q with q | r
    · exact q.suffixFromAux_start f.finish hfinish
    · exact r.initial_suffixFrom f.finish hfinish
  have hfinishSuffix : f.finish ∈
      (q.suffixFrom f.finish hfinish).support := by
    exact Set.mem_of_eq_of_mem hfinishInitial.symm
      (q.suffixFrom f.finish hfinish).initial_mem_support
  have hfinishOld : f.finish ∈ G.vertexSet U :=
    ⟨.inl f, hfU, f.finish_mem_support⟩
  have hsingleton : ({f.finish} : Set V) ⊆ S := by
    rw [Set.singleton_subset_iff]
    exact ⟨hfinishSuffix, hfinishOld⟩
  by_cases hclean : S = {f.finish}
  · exact Or.inl ⟨{
      path := q
      mem_path := hqW
      finish_mem := hfinish
      clean := hclean
    }⟩
  · right
    have hnsub : ¬ S ⊆ ({f.finish} : Set V) := by
      intro hsub
      exact hclean (Set.Subset.antisymm hsub hsingleton)
    obtain ⟨x, hxS, hxne⟩ := Set.not_subset.mp hnsub
    exact ⟨x, hxS.1, hxS.2, by simpa using hxne⟩

/-- Path-valued form of `arrowCandidate_or_extra_old_contact`: in the
failed case an actual member of the old warp witnesses the extra contact.
That member may equal the old path `f` (the self-re-entry case). -/
theorem arrowCandidate_or_blocking_old_path
    (G : DWeb V) {U W : Set G.DPath}
    {f : DirectedPath.FinitePath G.graph}
    (hfU : (Sum.inl f : G.DPath) ∈ U)
    {q : G.DPath} (hqW : q ∈ W)
    (hfinish : f.finish ∈ q.support) :
    Nonempty (G.ArrowCandidate U W f) ∨
      ∃ x p, p ∈ U ∧ x ∈ p.support ∧
        x ∈ (q.suffixFrom f.finish hfinish).support ∧ x ≠ f.finish := by
  rcases arrowCandidate_or_extra_old_contact G hfU hqW hfinish with hc | hc
  · exact Or.inl hc
  · right
    obtain ⟨x, hxq, ⟨p, hpU, hxp⟩, hxne⟩ := hc
    exact ⟨x, p, hpU, hxp, hxq, hxne⟩

/-- If the proposed family is a warp and its path terminates at `z`, the
chosen arrow image either also terminates at `z`, or the proposed suffix has
an explicit extra old contact.  Thus this is the precise local obstruction
to preserving the proposed terminal through `arrow`. -/
theorem terminal_arrowPath_or_extra_old_contact
    (G : DWeb V) {U W : Set G.DPath}
    (hW : G.IsWarp W)
    {f : DirectedPath.FinitePath G.graph}
    (hfU : (Sum.inl f : G.DPath) ∈ U)
    {q : G.DPath} (hqW : q ∈ W)
    (hfinish : f.finish ∈ q.support)
    {z : V} (hqterminal : q.terminal? = some z) :
    (G.arrowPath U W ⟨.inl f, hfU⟩).terminal? = some z ∨
      ∃ x, x ∈ (q.suffixFrom f.finish hfinish).support ∧
        x ∈ G.vertexSet U ∧ x ≠ f.finish := by
  rcases arrowCandidate_or_extra_old_contact G hfU hqW hfinish with hc | hc
  · left
    let c := Classical.choice hc
    have hcq : c.path = q := by
      by_contra hne
      exact Set.disjoint_left.1 (hW c.mem_path hqW hne)
        c.finish_mem hfinish
    apply G.terminal_arrowPath_of_candidate hW hfU c
    simpa only [hcq] using hqterminal
  · exact Or.inr hc

/-- Freeze the already target-completed paths and continue only the pending
paths through the quotient. -/
noncomputable def frozenPendingContinuation
    (G : DWeb V) (F : Set G.DPath) {C : Set V} {W : Set G.DPath}
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    (hclean : TerminalCleanAt G W C)
    (U : Set (G.quotient C).DPath)
    (hUstart : (G.quotient C).initialSet U ⊆ C) :
    Set G.DPath :=
  F ∪ pendingContinuation G hroof htrim hclean U hUstart

/-- The frozen/pending construction is a genuine forward extension of the
whole old row. -/
theorem forwardExtension_frozenPendingContinuation
    (G : DWeb V) (F : Set G.DPath) {C : Set V} {W : Set G.DPath}
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    (hclean : TerminalCleanAt G W C)
    (U : Set (G.quotient C).DPath)
    (hUstart : (G.quotient C).initialSet U ⊆ C) :
    G.ForwardExtension (F ∪ W)
      (frozenPendingContinuation G F hroof htrim hclean U hUstart) := by
  exact forwardExtension_union_frozen G
    (forwardExtension_pendingContinuation
      G hroof htrim hclean U hUstart)

/-- The competitor-closure obligation appears here in its exact geometric
form: frozen vertices must avoid the newly continued pending warp. -/
theorem frozenPendingContinuation_isWarp
    (G : DWeb V) {F : Set G.DPath} {C : Set V} {W : Set G.DPath}
    (hF : G.IsWarp F) (hW : G.IsWarp W)
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    (hclean : TerminalCleanAt G W C)
    {U : Set (G.quotient C).DPath}
    (hU : (G.quotient C).IsWarp U)
    (hUstart : (G.quotient C).initialSet U ⊆ C)
    (hcross : Disjoint (G.vertexSet F)
      (G.vertexSet (pendingContinuation G hroof htrim hclean U hUstart))) :
    G.IsWarp
      (frozenPendingContinuation G F hroof htrim hclean U hUstart) := by
  exact isWarp_union_of_disjoint_vertexSet G hF
    (pendingContinuation_isWarp
      G hW hroof htrim hclean hU hUstart) hcross

/-- The frozen/pending construction also preserves finite character. -/
theorem frozenPendingContinuation_finiteCharacter
    (G : DWeb V) {F : Set G.DPath} {C : Set V} {W : Set G.DPath}
    (hFfinite : G.HasFiniteCharacter F)
    (hWfinite : G.HasFiniteCharacter W)
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    (hclean : TerminalCleanAt G W C)
    {U : Set (G.quotient C).DPath}
    (hUfinite : (G.quotient C).HasFiniteCharacter U)
    (hUstart : (G.quotient C).initialSet U ⊆ C) :
    G.HasFiniteCharacter
      (frozenPendingContinuation G F hroof htrim hclean U hUstart) := by
  exact finiteCharacter_union G hFfinite
    (pendingContinuation_finiteCharacter G hWfinite hroof htrim hclean
      hUfinite hUstart)

/-- The new frontier consists only of frozen terminals and quotient
terminals; all old pending terminals have been consumed. -/
theorem terminalFrontier_frozenPendingContinuation_subset
    (G : DWeb V) {F : Set G.DPath} {C : Set V} {W : Set G.DPath}
    (hWfinite : G.HasFiniteCharacter W)
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    (hclean : TerminalCleanAt G W C)
    {U : Set (G.quotient C).DPath}
    (hUstart : (G.quotient C).initialSet U ⊆ C)
    (hcover : G.terminalFrontier W ⊆
      (G.quotient C).initialSet U) :
    G.terminalFrontier
        (frozenPendingContinuation G F hroof htrim hclean U hUstart) ⊆
      G.terminalFrontier F ∪ (G.quotient C).terminalFrontier U := by
  rintro z ⟨p, hp, hpz⟩
  rcases hp with hpF | hpPending
  · exact Or.inl ⟨p, hpF, hpz⟩
  · exact Or.inr (terminalFrontier_pendingContinuation_subset G hWfinite
      hroof htrim hclean hUstart hcover ⟨p, hpPending, hpz⟩)

/-- A single future-proof row-step package: the displayed witness is the
actual family, not merely an abstract compatibility interface. -/
theorem exists_frozenPendingContinuation
    (G : DWeb V) {F : Set G.DPath} {C : Set V} {W : Set G.DPath}
    (hF : G.IsWarp F) (hW : G.IsWarp W)
    (hFfinite : G.HasFiniteCharacter F)
    (hWfinite : G.HasFiniteCharacter W)
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    (hclean : TerminalCleanAt G W C)
    {U : Set (G.quotient C).DPath}
    (hU : (G.quotient C).IsWarp U)
    (hUfinite : (G.quotient C).HasFiniteCharacter U)
    (hUstart : (G.quotient C).initialSet U ⊆ C)
    (hcross : Disjoint (G.vertexSet F)
      (G.vertexSet (pendingContinuation G hroof htrim hclean U hUstart))) :
    ∃ W' : Set G.DPath,
      G.IsWarp W' ∧ G.HasFiniteCharacter W' ∧
      G.ForwardExtension (F ∪ W) W' ∧
      G.initialSet W' = G.initialSet (F ∪ W) := by
  let W' := frozenPendingContinuation G F hroof htrim hclean U hUstart
  refine ⟨W', ?_, ?_, ?_, ?_⟩
  · exact frozenPendingContinuation_isWarp G hF hW hroof htrim hclean
      hU hUstart hcross
  · exact frozenPendingContinuation_finiteCharacter G hFfinite hWfinite
      hroof htrim hclean hUfinite hUstart
  · exact forwardExtension_frozenPendingContinuation G F
      hroof htrim hclean U hUstart
  · exact (G.initialSet_eq_of_forwardExtension
      (forwardExtension_frozenPendingContinuation G F
        hroof htrim hclean U hUstart)).symm

/-- The complete constructive row-step witness, including the frontier
transfer obtained from quotient coverage of every pending terminal. -/
theorem exists_frozenPendingContinuation_with_frontier
    (G : DWeb V) {F : Set G.DPath} {C : Set V} {W : Set G.DPath}
    (hF : G.IsWarp F) (hW : G.IsWarp W)
    (hFfinite : G.HasFiniteCharacter F)
    (hWfinite : G.HasFiniteCharacter W)
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    (hclean : TerminalCleanAt G W C)
    {U : Set (G.quotient C).DPath}
    (hU : (G.quotient C).IsWarp U)
    (hUfinite : (G.quotient C).HasFiniteCharacter U)
    (hUstart : (G.quotient C).initialSet U ⊆ C)
    (hcover : G.terminalFrontier W ⊆
      (G.quotient C).initialSet U)
    (hcross : Disjoint (G.vertexSet F)
      (G.vertexSet (pendingContinuation G hroof htrim hclean U hUstart))) :
    ∃ W' : Set G.DPath,
      G.IsWarp W' ∧ G.HasFiniteCharacter W' ∧
      G.ForwardExtension (F ∪ W) W' ∧
      G.initialSet W' = G.initialSet (F ∪ W) ∧
      G.terminalFrontier W' ⊆
        G.terminalFrontier F ∪ (G.quotient C).terminalFrontier U := by
  let W' := frozenPendingContinuation G F hroof htrim hclean U hUstart
  refine ⟨W', ?_, ?_, ?_, ?_, ?_⟩
  · exact frozenPendingContinuation_isWarp G hF hW hroof htrim hclean
      hU hUstart hcross
  · exact frozenPendingContinuation_finiteCharacter G hFfinite hWfinite
      hroof htrim hclean hUfinite hUstart
  · exact forwardExtension_frozenPendingContinuation G F
      hroof htrim hclean U hUstart
  · exact (G.initialSet_eq_of_forwardExtension
      (forwardExtension_frozenPendingContinuation G F
        hroof htrim hclean U hUstart)).symm
  · exact terminalFrontier_frozenPendingContinuation_subset G hWfinite
      hroof htrim hclean hUstart hcover

/-- Matrix-facing form of the complete construction.  Instead of asking
for disjointness from the as-yet unbuilt result, it asks separately that
the frozen part avoid the old pending family and the lifted quotient
family. -/
theorem exists_frozenPendingContinuation_of_componentwise_disjoint
    (G : DWeb V) {F : Set G.DPath} {C : Set V} {W : Set G.DPath}
    (hF : G.IsWarp F) (hW : G.IsWarp W)
    (hFfinite : G.HasFiniteCharacter F)
    (hWfinite : G.HasFiniteCharacter W)
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    (hclean : TerminalCleanAt G W C)
    {U : Set (G.quotient C).DPath}
    (hU : (G.quotient C).IsWarp U)
    (hUfinite : (G.quotient C).HasFiniteCharacter U)
    (hUstart : (G.quotient C).initialSet U ⊆ C)
    (hcover : G.terminalFrontier W ⊆
      (G.quotient C).initialSet U)
    (hFW : Disjoint (G.vertexSet F) (G.vertexSet W))
    (hFU : Disjoint (G.vertexSet F)
      (G.vertexSet (liftedQuotientFamily G C U))) :
    ∃ W' : Set G.DPath,
      G.IsWarp W' ∧ G.HasFiniteCharacter W' ∧
      G.ForwardExtension (F ∪ W) W' ∧
      G.initialSet W' = G.initialSet (F ∪ W) ∧
      G.terminalFrontier W' ⊆
        G.terminalFrontier F ∪ (G.quotient C).terminalFrontier U := by
  have hcross : Disjoint (G.vertexSet F)
      (G.vertexSet
        (pendingContinuation G hroof htrim hclean U hUstart)) :=
    disjoint_vertexSet_pendingContinuation G hroof htrim hclean U
      hUstart hFW hFU
  exact exists_frozenPendingContinuation_with_frontier G
    hF hW hFfinite hWfinite hroof htrim hclean hU hUfinite
    hUstart hcover hcross

/-- The old half-way linkage and the lifted full-source quotient warp
satisfy the exact sole-intersection condition for source star.  No wave
hypothesis on `W` is used. -/
theorem starCompatible_liftQuotientFamily_of_linkage
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    (hW : IsLinkageBetween G G.source C W)
    (hsep : IsSeparatorFrom G G.source C)
    (htrim : IsTrimmedSeparator G C)
    (hclean : TerminalCleanAt G W C)
    {U : Set (G.quotient C).DPath}
    (hUinit : (G.quotient C).initialSet U = (G.quotient C).source) :
    G.StarCompatible W (liftedQuotientFamily G C U) := by
  apply starCompatible_liftQuotientFamily_of_roof G
    (linkage_vertexSet_subset_roof G hW hsep hclean) htrim hclean
  intro x hx
  rw [hUinit, quotient_source_eq_stopover G hsep htrim] at hx
  exact hx

/-- The concrete warp obtained by continuing `W` through a full-source
warp in the quotient by its stop-over. -/
noncomputable def continuation
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    (hW : IsLinkageBetween G G.source C W)
    (hsep : IsSeparatorFrom G G.source C)
    (htrim : IsTrimmedSeparator G C)
    (hclean : TerminalCleanAt G W C)
    (U : Set (G.quotient C).DPath)
    (hUinit : (G.quotient C).initialSet U = (G.quotient C).source) :
    Set G.DPath :=
  G.star (starCompatible_liftQuotientFamily_of_linkage
    G hW hsep htrim hclean hUinit)

/-- Quotient continuation is a warp. -/
theorem continuation_isWarp
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    (hW : IsLinkageBetween G G.source C W)
    (hsep : IsSeparatorFrom G G.source C)
    (htrim : IsTrimmedSeparator G C)
    (hclean : TerminalCleanAt G W C)
    {U : Set (G.quotient C).DPath}
    (hU : (G.quotient C).IsWarp U)
    (hUinit : (G.quotient C).initialSet U = (G.quotient C).source) :
    G.IsWarp (continuation G hW hsep htrim hclean U hUinit) := by
  apply G.isWarp_star hW.isWarp
    (DWeb.IsWarp.liftQuotientFamily G hU)

/-- If the quotient continuation has finite character, then so does the
continued ambient warp. -/
theorem continuation_finiteCharacter
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    (hW : IsLinkageBetween G G.source C W)
    (hsep : IsSeparatorFrom G G.source C)
    (htrim : IsTrimmedSeparator G C)
    (hclean : TerminalCleanAt G W C)
    {U : Set (G.quotient C).DPath}
    (hUfinite : (G.quotient C).HasFiniteCharacter U)
    (hUinit : (G.quotient C).initialSet U = (G.quotient C).source) :
    G.HasFiniteCharacter
      (continuation G hW hsep htrim hclean U hUinit) := by
  let L := liftedQuotientFamily G C U
  let hc : G.StarCompatible W L :=
    starCompatible_liftQuotientFamily_of_linkage
      G hW hsep htrim hclean hUinit
  have hLfinite : G.HasFiniteCharacter L := by
    rintro q ⟨q₀, hq₀U, rfl⟩
    obtain ⟨g, rfl⟩ := hUfinite hq₀U
    let g' : DirectedPath.FinitePath G.graph :=
      g.lift (fun {_ _} h => G.quotient_adj_imp h)
    exact ⟨g', rfl⟩
  rintro r ⟨p, rfl⟩
  rcases p with ⟨p, hpW⟩
  obtain ⟨f, rfl⟩ := hW.finiteCharacter hpW
  simp only [DWeb.starPath]
  split
  next hmatch =>
    exact appendFinite_finite_of_finite f (Classical.choose hmatch) _ _
      (hLfinite (Classical.choose_spec hmatch).1)
  next _ => exact ⟨f, rfl⟩

/-- Every old path has a quotient continuation beginning at its terminal.
This is where full coverage of the quotient source is used. -/
theorem exists_liftedQuotientPath_from_old_terminal
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    (hW : IsLinkageBetween G G.source C W)
    (hsep : IsSeparatorFrom G G.source C)
    (htrim : IsTrimmedSeparator G C)
    {U : Set (G.quotient C).DPath}
    (hUinit : (G.quotient C).initialSet U = (G.quotient C).source)
    {f : DirectedPath.FinitePath G.graph}
    (hfW : (Sum.inl f : G.DPath) ∈ W) :
    ∃ q ∈ liftedQuotientFamily G C U, q.initial = f.finish := by
  have hfC : f.finish ∈ C := by
    apply hW.terminalFrontier_subset
    exact ⟨.inl f, hfW, rfl⟩
  have hfSource : f.finish ∈ (G.quotient C).source := by
    rw [quotient_source_eq_stopover G hsep htrim]
    exact hfC
  have hfInitial : f.finish ∈ (G.quotient C).initialSet U := by
    rw [hUinit]
    exact hfSource
  obtain ⟨q₀, hq₀U, hq₀init⟩ := hfInitial
  refine ⟨G.liftQuotientPath C q₀, ⟨q₀, hq₀U, rfl⟩, ?_⟩
  simpa only [G.initial_liftQuotientPath] using hq₀init

/-- Since every old terminal is covered, no old terminal remains exposed:
every terminal of the continued warp is a terminal of the lifted quotient
warp. -/
theorem terminalFrontier_continuation_subset
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    (hW : IsLinkageBetween G G.source C W)
    (hsep : IsSeparatorFrom G G.source C)
    (htrim : IsTrimmedSeparator G C)
    (hclean : TerminalCleanAt G W C)
    {U : Set (G.quotient C).DPath}
    (hUinit : (G.quotient C).initialSet U = (G.quotient C).source) :
    G.terminalFrontier
        (continuation G hW hsep htrim hclean U hUinit) ⊆
      G.terminalFrontier (liftedQuotientFamily G C U) := by
  let L := liftedQuotientFamily G C U
  let hc : G.StarCompatible W L :=
    starCompatible_liftQuotientFamily_of_linkage
      G hW hsep htrim hclean hUinit
  rintro z ⟨r, ⟨p, rfl⟩, hrz⟩
  rcases p with ⟨p, hpW⟩
  obtain ⟨f, rfl⟩ := hW.finiteCharacter hpW
  have hmatch : ∃ q ∈ L, q.initial = f.finish :=
    exists_liftedQuotientPath_from_old_terminal
      G hW hsep htrim hUinit hpW
  simp only [DWeb.starPath] at hrz
  rw [dif_pos hmatch] at hrz
  let q := Classical.choose hmatch
  have hqL : q ∈ L := (Classical.choose_spec hmatch).1
  have hqstart : q.initial = f.finish := (Classical.choose_spec hmatch).2
  have hinter : f.support ∩ q.support ⊆ {f.finish} := by
    intro x hx
    have hx' := hc (.inl f) hpW q hqL x hx.1 hx.2
    exact Set.mem_singleton_iff.2 (Option.some.inj hx'.1).symm
  refine ⟨q, hqL, ?_⟩
  have hterm := DirectedPath.Path.terminal?_appendFinite
    f q hqstart hinter
  change DirectedPath.Path.terminal? q = some z
  rw [← hterm]
  dsimp only [q]
  exact hrz

/-- Assertion 9.17's order clause: the quotient continuation is an honest
forward extension of the old half-way warp.  This theorem deliberately
assumes no wave property. -/
theorem forwardExtension_continuation
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    (hW : IsLinkageBetween G G.source C W)
    (hsep : IsSeparatorFrom G G.source C)
    (htrim : IsTrimmedSeparator G C)
    (hclean : TerminalCleanAt G W C)
    (U : Set (G.quotient C).DPath)
    (hUinit : (G.quotient C).initialSet U = (G.quotient C).source) :
    G.ForwardExtension W
      (continuation G hW hsep htrim hclean U hUinit) := by
  exact G.forwardExtension_star
    (starCompatible_liftQuotientFamily_of_linkage
      G hW hsep htrim hclean hUinit)

/-- The continuation retains exactly the old initial set, hence all old
sources. -/
theorem initialSet_continuation
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    (hW : IsLinkageBetween G G.source C W)
    (hsep : IsSeparatorFrom G G.source C)
    (htrim : IsTrimmedSeparator G C)
    (hclean : TerminalCleanAt G W C)
    (U : Set (G.quotient C).DPath)
    (hUinit : (G.quotient C).initialSet U = (G.quotient C).source) :
    G.initialSet (continuation G hW hsep htrim hclean U hUinit) =
      G.source := by
  rw [← hW.initialSet_eq]
  exact (G.initialSet_eq_of_forwardExtension
    (forwardExtension_continuation G hW hsep htrim hclean U hUinit)).symm

end SingularContinuation
end CardinalInduction
end Erdos599
