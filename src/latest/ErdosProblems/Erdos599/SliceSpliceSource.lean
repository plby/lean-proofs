/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Normalization
import ErdosProblems.Erdos599.SliceSplice

/-!
# Source-faithful base and successor facts for Assertion 9.11

The printed proof of Aharoni--Berger Assertion 9.11 recursively stars
frontier-to-frontier linkages.  Its first slice is based at `T_0 = A`; at
later stages the request is the terminal of the current partial path which
starts at the next enumerated source.  Thus the recursion is a recursion of
partial `A`--frontier linkages, not a recursion which retains only paths that
have already reached the original target.

This file records the elementary facts needed by that recursion.  In
particular, `TightLinkageBetween` makes explicit the boundary condition used
by the source star operation: a member meets its right-hand frontier only at
its terminal.  The weaker predicate `IsLinkageBetween` permits the initial
endpoint also to lie in the right-hand set, so it is not by itself sufficient
for iterated star when consecutive frontiers overlap.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SliceSpliceSource

open DirectedPath

universe u v

variable {V : Type u}

/-- Restrict a path family to the members whose initial vertex lies in `A`. -/
def initialRestriction (Gamma : DWeb V) (W : Set Gamma.DPath)
    (A : Set V) : Set Gamma.DPath :=
  {p | p ∈ W ∧ p.initial ∈ A}

@[simp]
theorem mem_initialRestriction {Gamma : DWeb V} {W : Set Gamma.DPath}
    {A : Set V} {p : Gamma.DPath} :
    p ∈ initialRestriction Gamma W A ↔ p ∈ W ∧ p.initial ∈ A :=
  Iff.rfl

theorem vertexSet_initialRestriction_subset
    (Gamma : DWeb V) (W : Set Gamma.DPath) (A : Set V) :
    Gamma.vertexSet (initialRestriction Gamma W A) ⊆ Gamma.vertexSet W := by
  rintro x ⟨p, hp, hxp⟩
  exact ⟨p, hp.1, hxp⟩

/-- Restricting the initial vertices of a linkage gives a linkage on the
smaller left-hand set. -/
theorem isLinkageBetween_initialRestriction
    {Gamma : DWeb V} {W : Set Gamma.DPath} {A C A' : Set V}
    (hW : IsLinkageBetween Gamma A C W) (hA' : A' ⊆ A) :
    IsLinkageBetween Gamma A' C (initialRestriction Gamma W A') := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun p hp q hq hpq ↦ hW.1 hp.1 hq.1 hpq
  · intro p hp
    exact hW.2.1 hp.1
  · apply Set.Subset.antisymm
    · rintro x ⟨p, hp, rfl⟩
      exact hp.2
    · intro x hx
      have hxA : x ∈ A := hA' hx
      have hxInitial : x ∈ Gamma.initialSet W :=
        hW.2.2.1.symm ▸ hxA
      obtain ⟨p, hpW, hpstart⟩ : ∃ p ∈ W, p.initial = x := by
        exact hxInitial
      exact ⟨p, ⟨hpW, hpstart ▸ hx⟩, hpstart⟩
  · rintro x ⟨p, hp, hpx⟩
    exact hW.2.2.2.1 ⟨p, hp.1, hpx⟩
  · intro p hp
    obtain ⟨q, hpq, hends, hsource⟩ := hW.2.2.2.2 p hp.1
    subst p
    refine ⟨q, rfl, ?_, ?_⟩
    · apply Set.Subset.antisymm
      · rintro x ⟨hxq, hx⟩
        have hxAC : x ∈ q.support ∩ (A ∪ C) :=
          ⟨hxq, hx.elim (fun hxA' ↦ Or.inl (hA' hxA')) Or.inr⟩
        rw [hends] at hxAC
        exact hxAC
      · intro x hx
        rcases Set.mem_insert_iff.mp hx with hxstart | hxfinish
        · subst x
          exact ⟨q.start_mem_support, Or.inl hp.2⟩
        · have hqterminal : q.finish ∈ Gamma.terminalFrontier W :=
            ⟨Sum.inl q, hp.1, rfl⟩
          subst x
          exact ⟨q.finish_mem_support,
            Or.inr (hW.2.2.2.1 hqterminal)⟩
    · apply Set.Subset.antisymm
      · rintro x ⟨hxq, hxA'⟩
        have hxA : x ∈ q.support ∩ A := ⟨hxq, hA' hxA'⟩
        rw [hsource] at hxA
        exact hxA
      · rintro x hx
        have hxstart : x = q.start := Set.mem_singleton_iff.mp hx
        subst x
        exact ⟨q.start_mem_support, hp.2⟩

/-- A linkage is tight on its right-hand frontier when no member visits
that frontier before its terminal. -/
def MeetsOnlyAtTerminal (Gamma : DWeb V) (W : Set Gamma.DPath)
    (C : Set V) : Prop :=
  ∀ p ∈ W, ∀ x ∈ p.support, x ∈ C → Gamma.terminal? p = some x

/-- The source-faithful linkage invariant used in the star recursion. -/
def TightLinkageBetween (Gamma : DWeb V) (A C : Set V)
    (W : Set Gamma.DPath) : Prop :=
  IsLinkageBetween Gamma A C W ∧ MeetsOnlyAtTerminal Gamma W C

theorem TightLinkageBetween.isLinkageBetween
    {Gamma : DWeb V} {A C : Set V} {W : Set Gamma.DPath}
    (hW : TightLinkageBetween Gamma A C W) :
    IsLinkageBetween Gamma A C W :=
  hW.1

theorem TightLinkageBetween.meetsOnlyAtTerminal
    {Gamma : DWeb V} {A C : Set V} {W : Set Gamma.DPath}
    (hW : TightLinkageBetween Gamma A C W) :
    MeetsOnlyAtTerminal Gamma W C :=
  hW.2

theorem TightLinkageBetween.initialRestriction
    {Gamma : DWeb V} {W : Set Gamma.DPath} {A C A' : Set V}
    (hW : TightLinkageBetween Gamma A C W) (hA' : A' ⊆ A) :
    TightLinkageBetween Gamma A' C (initialRestriction Gamma W A') := by
  refine ⟨isLinkageBetween_initialRestriction hW.1 hA', ?_⟩
  intro p hp
  exact hW.2 p hp.1

/-- Unhinderedness rules out an unreachable source vertex: deleting its
trivial path from the trivial wave would otherwise be a hindrance. -/
theorem source_subset_reachableToTarget_of_isUnhindered
    {Gamma : DWeb V} (hGamma : Gamma.IsUnhindered) :
    Gamma.source ⊆ Gamma.reachableToTarget := by
  intro a ha
  by_contra hreach
  let W : Set Gamma.DPath :=
    Gamma.trivialPath '' (Gamma.source \ {a})
  have hWwave : Gamma.IsWave W := by
    refine ⟨Gamma.isWarp_trivialPaths _, ?_, ?_⟩
    · rw [Gamma.initialSet_trivialPaths]
      exact Set.sdiff_subset
    · rw [Gamma.terminalFrontier_trivialPaths]
      intro x hx
      by_cases hxa : x = a
      · subst x
        intro p hp
        exact False.elim (hreach ⟨p, hp⟩)
      · exact Gamma.subset_roof (Gamma.source \ {a}) ⟨hx, hxa⟩
  have hWmissing : Gamma.initialSet W ≠ Gamma.source := by
    rw [Gamma.initialSet_trivialPaths]
    intro heq
    have : a ∈ Gamma.source \ {a} := heq.symm ▸ ha
    exact this.2 rfl
  exact hGamma ⟨W, hWwave, hWmissing⟩

/-- In a normalized web in which every source reaches the target, every
source vertex is essential in the source set. -/
theorem essential_source_eq_of_isNormalized_of_reachable
    {Gamma : DWeb V} (hNorm : Gamma.IsNormalized)
    (hReach : Gamma.source ⊆ Gamma.reachableToTarget) :
    Gamma.essential Gamma.source = Gamma.source := by
  apply Set.Subset.antisymm
  · exact Gamma.essential_subset _
  · intro a ha
    refine ⟨ha, (Gamma.not_mem_roof_iff (Gamma.source \ {a}) a).2 ?_⟩
    obtain ⟨p, hpstart, hpfinish⟩ := hReach ha
    refine ⟨p, ⟨hpstart, hpfinish⟩, ?_⟩
    apply Set.disjoint_left.2
    intro x hxp hxsource
    have hxa : x = a :=
      (hNorm.eq_initial_of_mem_path (Sum.inl p) hxp hxsource.1).trans hpstart
    exact hxsource.2 hxa

/-- Passing to the essential part of a quotient by a set which roofs the
source leaves exactly the essential boundary as the new source. -/
theorem quotientEssentialPart_source_eq_essential_of_roofsSource
    (Gamma : DWeb V) {T : Set V} (hroof : Gamma.source ⊆ Gamma.roof T) :
    (Gamma.quotient T).essentialPart.source = Gamma.essential T := by
  have hsource : (Gamma.quotient T).source = Gamma.essential T := by
    simpa only [Gamma.terminalFrontier_trivialPaths] using
      (Gamma.quotient_source_eq_essential_terminalFrontier_of_roofsSource
        (W := Gamma.trivialPath '' T) (by
          simpa only [Gamma.terminalFrontier_trivialPaths] using hroof))
  rw [DWeb.essentialPart_source, hsource]
  apply Set.Subset.antisymm
  · exact Set.inter_subset_left
  · intro x hx
    refine ⟨hx, ?_⟩
    obtain ⟨p, hpstart, hptarget⟩ :=
      Gamma.exists_quotientTargetPath_from_essential T hx
    exact ⟨p, hpstart, hptarget⟩

/-- The initial-stage law and regularity are the only ladder fields needed
for the `T_0=A` identity.  Keeping this provenance-free lets both legacy and
successor-normalized split legality feed the regular splice. -/
theorem frontier_zero_eq_source_of_initialStage
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa} (hNorm : Gamma.IsNormalized)
    (hUnhindered : Gamma.IsUnhindered) (hregular : kappa.IsRegular)
    (hinitial : L.HasInitialStage) :
    L.frontier ⟨0, hregular.ord_pos⟩ = Gamma.source := by
  have hzero : L.warpAt ⟨0, hregular.ord_pos⟩ = Gamma.trivialWave := by
    exact hinitial
  change (Gamma.quotient
    (Gamma.terminalFrontier (L.warpAt ⟨0, hregular.ord_pos⟩))).essentialPart.source =
      Gamma.source
  rw [hzero, Gamma.terminalFrontier_trivialWave,
    quotientEssentialPart_source_eq_essential_of_roofsSource Gamma
      (Gamma.subset_roof Gamma.source)]
  exact essential_source_eq_of_isNormalized_of_reachable hNorm
    (source_subset_reachableToTarget_of_isUnhindered hUnhindered)

/-- Legacy legal-ladder wrapper for the initial-frontier identity. -/
theorem frontier_zero_eq_source
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa} (hNorm : Gamma.IsNormalized)
    (hUnhindered : Gamma.IsUnhindered) (hL : L.IsLegal) :
    L.frontier ⟨0, hL.regular.ord_pos⟩ = Gamma.source :=
  frontier_zero_eq_source_of_initialStage hNorm hUnhindered
    hL.regular hL.initialStage

/-- A controlled slice member whose initial vertex has been registered in
`Z` is wholly contained in `Z`. -/
theorem controlledSlice_support_subset_of_initial_mem
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa} {Z U : Set V}
    {alpha beta : Ladder.Stage kappa} {T : Set Gamma.DPath}
    (hclosed : SliceSplice.IsLimitWarpClosed Gamma L Z)
    (hT : RegularCardinal.IsControlledSlice
      (ControlledSlices.SliceGood Gamma L)
      (ControlledSlices.sliceMavericks Gamma L.limitWarp)
      (fun p : Gamma.DPath ↦ p.support) Z alpha beta U T)
    {p : Gamma.DPath} (hpT : p ∈ T) (hpinitial : p.initial ∈ Z) :
    p.support ⊆ Z := by
  apply SliceSplice.controlledSlice_path_support_subset hclosed hT hpT
  exact ⟨p.initial, p.initial_mem_support, hpinitial⟩

/-- Restricting a controlled slice to registered initial vertices gives a
closed linkage. -/
theorem vertexSet_initialRestriction_subset_of_controlledSlice
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa} {Z U A : Set V}
    {alpha beta : Ladder.Stage kappa} {T : Set Gamma.DPath}
    (hclosed : SliceSplice.IsLimitWarpClosed Gamma L Z)
    (hA : A ⊆ Z)
    (hT : RegularCardinal.IsControlledSlice
      (ControlledSlices.SliceGood Gamma L)
      (ControlledSlices.sliceMavericks Gamma L.limitWarp)
      (fun p : Gamma.DPath ↦ p.support) Z alpha beta U T) :
    Gamma.vertexSet (initialRestriction Gamma T A) ⊆ Z := by
  rintro x ⟨p, hp, hxp⟩
  exact controlledSlice_support_subset_of_initial_mem hclosed hT hp.1
    (hA hp.2) hxp

/-- A member starting at a prescribed vertex of the left side has a
well-defined terminal in the right side. -/
theorem exists_member_terminal_of_linkage
    {Gamma : DWeb V} {A C : Set V} {W : Set Gamma.DPath}
    (hW : IsLinkageBetween Gamma A C W) {a : V} (ha : a ∈ A) :
    ∃ p ∈ W, p.initial = a ∧
      ∃ c ∈ C, Gamma.terminal? p = some c := by
  have haInitial : a ∈ Gamma.initialSet W := hW.2.2.1.symm ▸ ha
  obtain ⟨p, hpW, hpinitial⟩ := haInitial
  obtain ⟨q, hpq⟩ := hW.2.1 hpW
  subst p
  have hqterminal : q.finish ∈ Gamma.terminalFrontier W :=
    ⟨Sum.inl q, hpW, rfl⟩
  exact ⟨Sum.inl q, hpW, hpinitial,
    q.finish, hW.2.2.2.1 hqterminal, rfl⟩

/-- Every member of a linkage is finite and has a terminal on its right
side. -/
theorem exists_terminal_of_mem_linkage
    {Gamma : DWeb V} {A C : Set V} {W : Set Gamma.DPath}
    (hW : IsLinkageBetween Gamma A C W) {p : Gamma.DPath} (hp : p ∈ W) :
    ∃ c ∈ C, Gamma.terminal? p = some c := by
  obtain ⟨q, rfl⟩ := hW.2.1 hp
  exact ⟨q.finish, hW.2.2.2.1 ⟨Sum.inl q, hp, rfl⟩, rfl⟩

/-- The first controlled slice, restricted to the registered sources, is
the initial partial linkage in Assertion 9.11.  Its carrier is closed in
`Z` and lies below the later frontier roof.

The theorem deliberately concludes `IsLinkageBetween`, rather than the
stronger `TightLinkageBetween`: the current `SliceGood` record does not say
that a path whose initial vertex also belongs to the later frontier is
stationary there. -/
theorem exists_initialPartialLinkage_of_firstControlledSlice
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa} {Z U : Set V}
    {beta : Ladder.Stage kappa} {T : Set Gamma.DPath}
    (hNorm : Gamma.IsNormalized) (hUnhindered : Gamma.IsUnhindered)
    (hL : L.IsLegal)
    (hclosed : SliceSplice.IsLimitWarpClosed Gamma L Z)
    (hT : RegularCardinal.IsControlledSlice
      (SliceSplice.IsAnnularSlice Gamma L)
      (ControlledSlices.sliceMavericks Gamma L.limitWarp)
      (fun p : Gamma.DPath ↦ p.support) Z
      ⟨0, hL.regular.ord_pos⟩ beta U T) :
    ∃ W : Set Gamma.DPath,
      IsLinkageBetween Gamma (Gamma.source ∩ Z) (L.frontier beta) W ∧
        Gamma.vertexSet W ⊆ Z ∧
        Gamma.vertexSet W ⊆ Gamma.roof (L.frontier beta) := by
  let A : Set V := Gamma.source ∩ Z
  let W : Set Gamma.DPath := initialRestriction Gamma T A
  have hfirst : L.frontier ⟨0, hL.regular.ord_pos⟩ = Gamma.source :=
    frontier_zero_eq_source hNorm hUnhindered hL
  have hlinkT : IsLinkageBetween Gamma Gamma.source (L.frontier beta) T := by
    simpa only [hfirst] using hT.1.1.1
  have hlinkW : IsLinkageBetween Gamma A (L.frontier beta) W :=
    isLinkageBetween_initialRestriction hlinkT Set.inter_subset_left
  refine ⟨W, hlinkW, ?_, ?_⟩
  · apply vertexSet_initialRestriction_subset_of_controlledSlice
      hclosed Set.inter_subset_right
    exact SliceSplice.controlledSlice_of_annularControlledSlice hT
  · exact (vertexSet_initialRestriction_subset Gamma T A).trans
      (fun _ hx ↦ hT.1.2 hx |>.2)

/-- Star preserves the exact set of initial vertices. -/
theorem initialSet_star_eq
    {Gamma : DWeb V} {W T : Set Gamma.DPath}
    (hcompat : Gamma.StarCompatible W T) :
    Gamma.initialSet (Gamma.star hcompat) = Gamma.initialSet W := by
  apply Set.Subset.antisymm
  · exact Gamma.initialSet_star_subset hcompat
  · rintro x ⟨p, hpW, hpinitial⟩
    let ps : W := ⟨p, hpW⟩
    refine ⟨Gamma.starPath hcompat ps, ⟨ps, rfl⟩, ?_⟩
    exact (Gamma.initial_starPath hcompat ps).trans hpinitial

/-- Star introduces only vertices from the two input families. -/
theorem vertexSet_star_subset_union
    {Gamma : DWeb V} {W T : Set Gamma.DPath}
    (hcompat : Gamma.StarCompatible W T) :
    Gamma.vertexSet (Gamma.star hcompat) ⊆
      Gamma.vertexSet W ∪ Gamma.vertexSet T := by
  rintro x ⟨r, ⟨p, rfl⟩, hxr⟩
  rcases Gamma.mem_support_starPath_cases hcompat p hxr with hx | hx
  · exact Or.inl ⟨p.1, p.2, hx⟩
  · obtain ⟨_t, q, _hpt, hqT, _hqstart, hxq⟩ := hx
    exact Or.inr ⟨q, hqT, hxq⟩

/-- If the old carrier is below the old frontier and the new carrier is
below the new frontier, frontier chronology puts the whole star below the
new frontier. -/
theorem vertexSet_star_subset_roof
    {Gamma : DWeb V} {W T : Set Gamma.DPath} {S R : Set V}
    (hcompat : Gamma.StarCompatible W T)
    (hchron : S ⊆ Gamma.roof R)
    (hWroof : Gamma.vertexSet W ⊆ Gamma.roof S)
    (hTroof : Gamma.vertexSet T ⊆ Gamma.roof R) :
    Gamma.vertexSet (Gamma.star hcompat) ⊆ Gamma.roof R := by
  intro x hx
  rcases vertexSet_star_subset_union hcompat hx with hxW | hxT
  · exact Gamma.roof_cut hchron (hWroof hxW)
  · exact hTroof hxT

/-- A family below an essential frontier meets a later frontier only at
its current terminals, provided the later frontier avoids the old strict
roof. -/
theorem meetsOnlyAtTerminal_of_roof_of_disjoint_strictRoof
    {Gamma : DWeb V} {W : Set Gamma.DPath} {S R : Set V}
    (hessential : Gamma.essential S = S)
    (hWroof : Gamma.vertexSet W ⊆ Gamma.roof S)
    (hboundary : MeetsOnlyAtTerminal Gamma W S)
    (hdisjoint : Disjoint (Gamma.strictRoof S) R) :
    MeetsOnlyAtTerminal Gamma W R := by
  intro p hp x hxp hxR
  have hxRoof : x ∈ Gamma.roof S := hWroof ⟨p, hp, hxp⟩
  have hxNotStrict : x ∉ Gamma.strictRoof S := by
    intro hx
    exact Set.disjoint_left.1 hdisjoint hx hxR
  have hxEssential : x ∈ Gamma.essential S := by
    by_contra hx
    exact hxNotStrict ⟨hxRoof, hx⟩
  exact hboundary p hp x hxp (hessential ▸ hxEssential)

/-- The exact strengthening of an annular slice used by source star.
`SliceGood` supplies the linkage and source-frontier purity; the second
conjunct supplies purity at the later frontier even when the two
frontiers overlap. -/
def IsTightAnnularSlice {kappa : Cardinal.{u}}
    (Gamma : DWeb V) (L : Gamma.KappaLadder kappa)
    (T : Set Gamma.DPath) (alpha beta : Ladder.Stage kappa)
    (U : Set V) : Prop :=
  SliceSplice.IsAnnularSlice Gamma L T alpha beta U ∧
    MeetsOnlyAtTerminal Gamma T (L.frontier beta)

theorem tightLinkageBetween_of_tightAnnularSlice
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa} {T : Set Gamma.DPath}
    {alpha beta : Ladder.Stage kappa} {U : Set V}
    (hT : IsTightAnnularSlice Gamma L T alpha beta U) :
    TightLinkageBetween Gamma (L.frontier alpha) (L.frontier beta) T :=
  ⟨hT.1.1.1, hT.2⟩

/-- Appending a finite path to a path which has finite character is again
finite.  Stating this as an eliminator avoids depending on the proof
arguments manufactured inside `DWeb.starPath`. -/
theorem appendFinite_finite_of_finite
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

/-- Star of two finite-character families again has finite character. -/
theorem hasFiniteCharacter_star
    {Gamma : DWeb V} {W T : Set Gamma.DPath}
    (hW : Gamma.HasFiniteCharacter W)
    (hT : Gamma.HasFiniteCharacter T)
    (hcompat : Gamma.StarCompatible W T) :
    Gamma.HasFiniteCharacter (Gamma.star hcompat) := by
  rintro r ⟨p, rfl⟩
  rcases p with ⟨p, hpW⟩
  obtain ⟨f, rfl⟩ := hW hpW
  simp only [DWeb.starPath]
  split
  next hmatch =>
    exact appendFinite_finite_of_finite f (Classical.choose hmatch) _ _
      (hT (Classical.choose_spec hmatch).1)
  next _ => exact ⟨f, rfl⟩

/-- If every old terminal starts a new path, every terminal exposed by
star is a terminal of the new family. -/
theorem terminalFrontier_star_subset
    {Gamma : DWeb V} {W T : Set Gamma.DPath}
    (hWfinite : Gamma.HasFiniteCharacter W)
    (hcompat : Gamma.StarCompatible W T)
    (hcover : Gamma.terminalFrontier W ⊆ Gamma.initialSet T) :
    Gamma.terminalFrontier (Gamma.star hcompat) ⊆
      Gamma.terminalFrontier T := by
  rintro z ⟨r, ⟨p, rfl⟩, hrz⟩
  rcases p with ⟨p, hpW⟩
  obtain ⟨f, rfl⟩ := hWfinite hpW
  have hmatch : ∃ q ∈ T, q.initial = f.finish := by
    exact hcover ⟨Sum.inl f, hpW, rfl⟩
  simp only [DWeb.starPath] at hrz
  rw [dif_pos hmatch] at hrz
  let q := Classical.choose hmatch
  have hqT : q ∈ T := (Classical.choose_spec hmatch).1
  have hqstart : q.initial = f.finish :=
    (Classical.choose_spec hmatch).2
  have hinter : f.support ∩ q.support ⊆ {f.finish} := by
    intro x hx
    have hx' := hcompat (.inl f) hpW q hqT x hx.1 hx.2
    exact Set.mem_singleton_iff.2 (Option.some.inj hx'.1).symm
  refine ⟨q, hqT, ?_⟩
  have hterm := DirectedPath.Path.terminal?_appendFinite
    f q hqstart hinter
  change DirectedPath.Path.terminal? q = some z
  rw [← hterm]
  dsimp only [q]
  exact hrz

/-- Boundary purity is stable under a covered star.  If an old member
already meets the new right-hand set, it does so at its terminal; the new
member then starts at that vertex, and its own tightness forces it to end
there as well. -/
theorem meetsOnlyAtTerminal_star
    {Gamma : DWeb V} {W T : Set Gamma.DPath} {R : Set V}
    (hWfinite : Gamma.HasFiniteCharacter W)
    (hWboundary : MeetsOnlyAtTerminal Gamma W R)
    (hTboundary : MeetsOnlyAtTerminal Gamma T R)
    (hcompat : Gamma.StarCompatible W T)
    (hcover : Gamma.terminalFrontier W ⊆ Gamma.initialSet T) :
    MeetsOnlyAtTerminal Gamma (Gamma.star hcompat) R := by
  rintro r ⟨p, rfl⟩ x hxr hxR
  rcases p with ⟨p, hpW⟩
  obtain ⟨f, rfl⟩ := hWfinite hpW
  have hmatch : ∃ q ∈ T, q.initial = f.finish :=
    hcover ⟨Sum.inl f, hpW, rfl⟩
  simp only [DWeb.starPath] at hxr ⊢
  rw [dif_pos hmatch] at hxr ⊢
  let q := Classical.choose hmatch
  have hqT : q ∈ T := (Classical.choose_spec hmatch).1
  have hqstart : q.initial = f.finish :=
    (Classical.choose_spec hmatch).2
  have hinter : f.support ∩ q.support ⊆ {f.finish} := by
    intro y hy
    have hy' := hcompat (.inl f) hpW q hqT y hy.1 hy.2
    exact Set.mem_singleton_iff.2 (Option.some.inj hy'.1).symm
  rw [DirectedPath.Path.support_appendFinite f q hqstart hinter] at hxr
  rcases hxr with hxf | hxq
  · have hfx : (some f.finish : Option V) = some x :=
      hWboundary (Sum.inl f) hpW x hxf hxR
    have hxinitial : q.initial = x :=
      hqstart.trans (Option.some.inj hfx)
    have hqterm := hTboundary q hqT x
      (hxinitial ▸ q.initial_mem_support) hxR
    change DirectedPath.Path.terminal? q = some x at hqterm
    rw [← DirectedPath.Path.terminal?_appendFinite
      f q hqstart hinter] at hqterm
    dsimp only [q] at hqterm
    exact hqterm
  · have hqterm := hTboundary q hqT x hxq hxR
    change DirectedPath.Path.terminal? q = some x at hqterm
    rw [← DirectedPath.Path.terminal?_appendFinite
      f q hqstart hinter] at hqterm
    dsimp only [q] at hqterm
    exact hqterm

/-- In a normalized web, warp, finiteness, endpoint-set equations, and
right-boundary tightness imply the full canonical linkage predicate. -/
theorem tightLinkageBetween_of_structural
    {Gamma : DWeb V} {A R : Set V} {W : Set Gamma.DPath}
    (hNorm : Gamma.IsNormalized) (hA : A ⊆ Gamma.source)
    (hWarp : Gamma.IsWarp W) (hfinite : Gamma.HasFiniteCharacter W)
    (hinitial : Gamma.initialSet W = A)
    (hterminal : Gamma.terminalFrontier W ⊆ R)
    (hboundary : MeetsOnlyAtTerminal Gamma W R) :
    TightLinkageBetween Gamma A R W := by
  refine ⟨⟨hWarp, hfinite, hinitial, hterminal, ?_⟩, hboundary⟩
  intro p hpW
  obtain ⟨q, rfl⟩ := hfinite hpW
  have hqA : q.start ∈ A := by
    rw [← hinitial]
    exact ⟨Sum.inl q, hpW, rfl⟩
  have hqR : q.finish ∈ R :=
    hterminal ⟨Sum.inl q, hpW, rfl⟩
  have hsource : q.support ∩ A = {q.start} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxq, hxA⟩
      exact Set.mem_singleton_iff.2
        (hNorm.eq_initial_of_mem_path (Sum.inl q) hxq (hA hxA))
    · rintro x hx
      have hxstart : x = q.start := Set.mem_singleton_iff.1 hx
      subst x
      exact ⟨q.start_mem_support, hqA⟩
  have htarget : q.support ∩ R = {q.finish} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxq, hxR⟩
      have h := hboundary (Sum.inl q) hpW x hxq hxR
      exact Set.mem_singleton_iff.2 (Option.some.inj h).symm
    · rintro x hx
      have hxfinish : x = q.finish := Set.mem_singleton_iff.1 hx
      subst x
      exact ⟨q.finish_mem_support, hqR⟩
  refine ⟨q, rfl, ?_, hsource⟩
  rw [Set.inter_union_distrib_left, hsource, htarget]
  simp only [Set.singleton_union]

/-- Exact limit-stage interface for the source splice.  The genuinely
graph-theoretic stabilization obligation is `hterminal`: every initial
thread has one right-frontier terminal cofinally.  Once that is known, the
generic threadwise direct limit is finite, is still boundary-tight, and is
the required partial linkage. -/
theorem tightLinkageBetween_limitPaths_of_terminalCofinal
    {I : Type v} [LinearOrder I]
    {Gamma : DWeb V} {A R : Set V}
    (C : Gamma.GrowingWarpChain I)
    (hNorm : Gamma.IsNormalized) (hA : A ⊆ Gamma.source)
    (hinitial : C.initialUnion = A)
    (hterminal : ∀ a : C.initialUnion,
      ∃ b ∈ R, DirectedPath.Path.TerminalCofinal
        (C.thread Gamma a.1) b)
    (hboundary : ∀ i, MeetsOnlyAtTerminal Gamma (C.stage i) R) :
    TightLinkageBetween Gamma A R (C.limitPaths Gamma) := by
  apply tightLinkageBetween_of_structural hNorm hA
  · exact C.isWarp_limitPaths Gamma
  · rintro p ⟨a, rfl⟩
    obtain ⟨b, _hbR, hb⟩ := hterminal a
    have hterm : (C.threadLimit Gamma a).terminal? = some b :=
      DirectedPath.Path.terminal_chainLimit_of_cofinal
        (C.thread Gamma a.1) (C.thread_nonempty Gamma a)
        (C.thread_isChain Gamma a.1) hb
    generalize hp : C.threadLimit Gamma a = p at hterm ⊢
    rcases p with q | r
    · exact ⟨q, rfl⟩
    · simp at hterm
  · exact (C.initialSet_limitPaths Gamma).trans hinitial
  · rintro x ⟨p, ⟨a, rfl⟩, hpx⟩
    obtain ⟨b, hbR, hb⟩ := hterminal a
    have hpb : (C.threadLimit Gamma a).terminal? = some b :=
      DirectedPath.Path.terminal_chainLimit_of_cofinal
        (C.thread Gamma a.1) (C.thread_nonempty Gamma a)
        (C.thread_isChain Gamma a.1) hb
    exact (Option.some.inj (hpx.symm.trans hpb)) ▸ hbR
  · rintro p ⟨a, rfl⟩ x hxp hxR
    obtain ⟨i, q, hqi, hqinitial, hxq⟩ :=
      (C.mem_support_threadLimit_iff Gamma a x).1 hxp
    have hqterminal : Gamma.terminal? q = some x :=
      hboundary i q hqi x hxq hxR
    obtain ⟨b, _hbR, hb⟩ := hterminal a
    obtain ⟨r, ⟨j, hrj, hrinitial⟩, hqr, hrterminal⟩ :=
      hb q ⟨i, hqi, hqinitial⟩
    have hxr : x ∈ r.support :=
      Gamma.support_mono_of_extends hqr hxq
    have hrterminal' : Gamma.terminal? r = some x :=
      hboundary j r hrj x hxr hxR
    have hbx : b = x :=
      Option.some.inj (hrterminal.symm.trans hrterminal')
    have hlimit : (C.threadLimit Gamma a).terminal? = some b :=
      DirectedPath.Path.terminal_chainLimit_of_cofinal
        (C.thread Gamma a.1) (C.thread_nonempty Gamma a)
        (C.thread_isChain Gamma a.1) hb
    exact hlimit.trans (congrArg some hbx)

/-- A stagewise carrier bound passes to the threadwise direct limit. -/
theorem vertexSet_limitPaths_subset_of_stages
    {I : Type v} [LinearOrder I]
    {Gamma : DWeb V} {C : Gamma.GrowingWarpChain I} {Z : Set V}
    (hZ : ∀ i, Gamma.vertexSet (C.stage i) ⊆ Z) :
    Gamma.vertexSet (C.limitPaths Gamma) ⊆ Z := by
  rw [C.vertexSet_limitPaths Gamma]
  rintro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx
  exact hZ i hxi

/-- Eventual stabilization of one thread's terminal is the concrete form
of the cofinal-terminal hypothesis consumed by the limit theorem. -/
theorem terminalCofinal_of_eventually_terminal
    {I : Type v} [LinearOrder I]
    {Gamma : DWeb V} (C : Gamma.GrowingWarpChain I)
    (a : C.initialUnion) {b : V}
    (hstable : ∃ i₀, ∀ i, i₀ ≤ i →
      ∀ p ∈ C.stage i, p.initial = a.1 →
        Gamma.terminal? p = some b) :
    DirectedPath.Path.TerminalCofinal (C.thread Gamma a.1) b := by
  obtain ⟨i₀, hi₀⟩ := hstable
  rintro p ⟨j, hpj, hpinitial⟩
  obtain ⟨q, hq, hpq⟩ := C.grows (show j ≤ max i₀ j from le_max_right _ _) p hpj
  have hqinitial : q.initial = a.1 :=
    (Gamma.extends_initial hpq).symm.trans hpinitial
  exact ⟨q, ⟨max i₀ j, hq, hqinitial⟩, hpq,
    hi₀ (max i₀ j) (le_max_left _ _) q hq hqinitial⟩

/-- The maverick branch of the limit argument.  Once a member of a source
thread has been completed to the original target, any set roofing that
source meets the completed member, hence also the thread limit. -/
theorem threadLimit_meets_of_target_member
    {I : Type v} [LinearOrder I]
    {Gamma : DWeb V} (C : Gamma.GrowingWarpChain I)
    (a : C.initialUnion) {R : Set V}
    (haRoof : a.1 ∈ Gamma.roof R)
    (hcomplete : ∃ p ∈ C.thread Gamma a.1,
      ∃ b ∈ Gamma.target, Gamma.terminal? p = some b) :
    (R ∩ (C.threadLimit Gamma a).support).Nonempty := by
  obtain ⟨p, ⟨i, hpi, hpinitial⟩, b, hbTarget, hpterminal⟩ := hcomplete
  rcases p with q | r
  · have hqfinish : q.finish = b := Option.some.inj hpterminal
    obtain ⟨x, hxq, hxR⟩ := haRoof q
      ⟨hpinitial, hqfinish ▸ hbTarget⟩
    refine ⟨x, hxR, ?_⟩
    exact (C.mem_support_threadLimit_iff Gamma a x).2
      ⟨i, Sum.inl q, hpi, hpinitial, hxq⟩
  · simp at hpterminal

/-! ### The general last-hit arrow under full annular coverage -/

/-- Compatibility turns a continuation beginning at an old terminal into
an admissible last-hit arrow candidate. -/
theorem arrowCandidate_of_initial_match
    {Gamma : DWeb V} {W T : Set Gamma.DPath}
    (hcompat : Gamma.StarCompatible W T)
    {f : DirectedPath.FinitePath Gamma.graph}
    (hfW : (Sum.inl f : Gamma.DPath) ∈ W)
    {q : Gamma.DPath} (hqT : q ∈ T) (hqinitial : q.initial = f.finish) :
    Nonempty (Gamma.ArrowCandidate W T f) := by
  let hfinish : f.finish ∈ q.support :=
    hqinitial ▸ q.initial_mem_support
  refine ⟨{
    path := q
    mem_path := hqT
    finish_mem := hfinish
    clean := ?_ }⟩
  apply Set.Subset.antisymm
  · rintro x ⟨hxq, ⟨p, hpW, hxp⟩⟩
    have hxq' : x ∈ q.support :=
      q.support_suffixFrom_subset f.finish hfinish hxq
    have hxmeet := hcompat p hpW q hqT x hxp hxq'
    exact Set.mem_singleton_iff.2 (hxmeet.2.symm.trans hqinitial)
  · rintro x hx
    have hxfinish : x = f.finish := Set.mem_singleton_iff.1 hx
    subst x
    have hinitial :
        (q.suffixFrom f.finish hfinish).initial = f.finish := by
      rcases q with q | r
      · exact q.suffixFromAux_start f.finish hfinish
      · exact r.initial_suffixFrom f.finish hfinish
    exact ⟨Set.mem_of_eq_of_mem hinitial.symm
        (q.suffixFrom f.finish hfinish).initial_mem_support,
      ⟨Sum.inl f, hfW, f.finish_mem_support⟩⟩

/-- Appending at a support point of a finite path preserves finite
character when the selected continuation is finite. -/
theorem appendAt_finite_of_finite
    {D : Digraph V} (p : DirectedPath.FinitePath D)
    (q : DirectedPath.Path D) (hx : p.finish ∈ q.support)
    (happend : DirectedPath.Path.Appendable p q hx)
    (hq : ∃ g : DirectedPath.FinitePath D, q = .inl g) :
    ∃ g : DirectedPath.FinitePath D,
      DirectedPath.Path.appendAt p q hx happend = .inl g := by
  rcases q with q | r
  · exact ⟨p.appendSuffix q hx
      (p.disjoint_tail_of_appendableFinite q hx happend), rfl⟩
  · obtain ⟨g, hg⟩ := hq
    cases hg

/-- Arrow preserves finite character when both input families have finite
character. -/
theorem hasFiniteCharacter_arrow
    {Gamma : DWeb V} {W T : Set Gamma.DPath}
    (hW : Gamma.HasFiniteCharacter W)
    (hT : Gamma.HasFiniteCharacter T) :
    Gamma.HasFiniteCharacter (Gamma.arrow W T) := by
  rintro r ⟨p, rfl⟩
  rcases p with ⟨p, hpW⟩
  obtain ⟨f, rfl⟩ := hW hpW
  rcases Gamma.arrowPath_finite_cases W T f hpW with heq | ⟨c, heq⟩
  · exact ⟨f, heq⟩
  · rw [heq]
    exact appendAt_finite_of_finite f c.path c.finish_mem
      (c.appendable hpW) (hT c.mem_path)

/-- Arrow retains exactly the initial vertices of the old family. -/
theorem initialSet_arrow_eq
    {Gamma : DWeb V} (W T : Set Gamma.DPath) :
    Gamma.initialSet (Gamma.arrow W T) = Gamma.initialSet W := by
  apply Set.Subset.antisymm
  · rintro x ⟨r, ⟨p, rfl⟩, hrx⟩
    exact ⟨p.1, p.2, (Gamma.arrowPath_initial W T p).symm.trans hrx⟩
  · rintro x ⟨p, hpW, hpx⟩
    let pW : W := ⟨p, hpW⟩
    exact ⟨Gamma.arrowPath W T pW, ⟨pW, rfl⟩,
      (Gamma.arrowPath_initial W T pW).trans hpx⟩

/-- Under full coverage and source-star compatibility, the general
last-hit arrow has the same tight-linkage invariants needed by the annular
recursion. -/
theorem tightLinkageBetween_arrow
    {Gamma : DWeb V} {A S R : Set V} {W T : Set Gamma.DPath}
    (hNorm : Gamma.IsNormalized) (hA : A ⊆ Gamma.source)
    (hW : TightLinkageBetween Gamma A S W)
    (hT : TightLinkageBetween Gamma S R T)
    (hWR : MeetsOnlyAtTerminal Gamma W R)
    (hcompat : Gamma.StarCompatible W T) :
    TightLinkageBetween Gamma A R (Gamma.arrow W T) := by
  have hcover : Gamma.terminalFrontier W ⊆ Gamma.initialSet T := by
    intro x hx
    rw [hT.1.2.2.1]
    exact hW.1.2.2.2.1 hx
  apply tightLinkageBetween_of_structural hNorm hA
  · exact Gamma.isWarp_arrow hW.1.1 hT.1.1
  · exact hasFiniteCharacter_arrow hW.1.2.1 hT.1.2.1
  · rw [initialSet_arrow_eq W T, hW.1.2.2.1]
  · rintro x ⟨r, ⟨p, rfl⟩, hrx⟩
    rcases p with ⟨p, hpW⟩
    obtain ⟨f, rfl⟩ := hW.1.2.1 hpW
    have hmatch : ∃ q ∈ T, q.initial = f.finish :=
      hcover ⟨Sum.inl f, hpW, rfl⟩
    let q := Classical.choose hmatch
    have hqT : q ∈ T := (Classical.choose_spec hmatch).1
    have hqinitial : q.initial = f.finish :=
      (Classical.choose_spec hmatch).2
    let hcand : Nonempty (Gamma.ArrowCandidate W T f) :=
      arrowCandidate_of_initial_match hcompat hpW hqT hqinitial
    let c := Classical.choice hcand
    have harrow : Gamma.arrowPath W T ⟨Sum.inl f, hpW⟩ =
        DirectedPath.Path.appendAt f c.path c.finish_mem
          (c.appendable hpW) := by
      simp only [DWeb.arrowPath, DWeb.arrowFinite]
      rw [dif_pos hcand]
    obtain ⟨b, hbR, hcb⟩ := exists_terminal_of_mem_linkage hT.1 c.mem_path
    have harrowTerminal :
        Gamma.terminal? (Gamma.arrowPath W T ⟨Sum.inl f, hpW⟩) = some b := by
      rw [harrow]
      change DirectedPath.Path.terminal?
        (DirectedPath.Path.appendAt f c.path c.finish_mem
          (c.appendable hpW)) = some b
      rw [DirectedPath.Path.terminal?_appendAt]
      change Gamma.terminal? c.path = some b
      exact hcb
    exact (Option.some.inj (hrx.symm.trans harrowTerminal)) ▸ hbR
  · rintro r ⟨p, rfl⟩ x hxr hxR
    rcases p with ⟨p, hpW⟩
    obtain ⟨f, rfl⟩ := hW.1.2.1 hpW
    have hmatch : ∃ q ∈ T, q.initial = f.finish :=
      hcover ⟨Sum.inl f, hpW, rfl⟩
    let q := Classical.choose hmatch
    have hqT : q ∈ T := (Classical.choose_spec hmatch).1
    have hqinitial : q.initial = f.finish :=
      (Classical.choose_spec hmatch).2
    let hcand : Nonempty (Gamma.ArrowCandidate W T f) :=
      arrowCandidate_of_initial_match hcompat hpW hqT hqinitial
    let c := Classical.choice hcand
    have harrow : Gamma.arrowPath W T ⟨Sum.inl f, hpW⟩ =
        DirectedPath.Path.appendAt f c.path c.finish_mem
          (c.appendable hpW) := by
      simp only [DWeb.arrowPath, DWeb.arrowFinite]
      rw [dif_pos hcand]
    rw [harrow, DirectedPath.Path.support_appendAt] at hxr
    have hcTerminal : Gamma.terminal? c.path = some x := by
      rcases hxr with hxf | hxc
      · have hfx : (some f.finish : Option V) = some x :=
          hWR (Sum.inl f) hpW x hxf hxR
        have hxmem : x ∈ c.path.support := by
          exact (Option.some.inj hfx).symm ▸ c.finish_mem
        exact hT.2 c.path c.mem_path x hxmem hxR
      · exact hT.2 c.path c.mem_path x
          (c.path.support_suffixFrom_subset f.finish c.finish_mem hxc) hxR
    rw [harrow]
    change DirectedPath.Path.terminal?
      (DirectedPath.Path.appendAt f c.path c.finish_mem
        (c.appendable hpW)) = some x
    rw [DirectedPath.Path.terminal?_appendAt]
    change Gamma.terminal? c.path = some x
    exact hcTerminal

/-- Successor splicing for tight partial linkages. -/
theorem tightLinkageBetween_star
    {Gamma : DWeb V} {A S R : Set V} {W T : Set Gamma.DPath}
    (hNorm : Gamma.IsNormalized) (hA : A ⊆ Gamma.source)
    (hW : TightLinkageBetween Gamma A S W)
    (hT : TightLinkageBetween Gamma S R T)
    (hWR : MeetsOnlyAtTerminal Gamma W R)
    (hcompat : Gamma.StarCompatible W T) :
    TightLinkageBetween Gamma A R (Gamma.star hcompat) := by
  have hcover : Gamma.terminalFrontier W ⊆ Gamma.initialSet T := by
    intro x hx
    rw [hT.1.2.2.1]
    exact hW.1.2.2.2.1 hx
  apply tightLinkageBetween_of_structural hNorm hA
  · exact Gamma.isWarp_star hW.1.1 hT.1.1 hcompat
  · exact hasFiniteCharacter_star hW.1.2.1 hT.1.2.1 hcompat
  · rw [initialSet_star_eq hcompat, hW.1.2.2.1]
  · exact (terminalFrontier_star_subset hW.1.2.1 hcompat hcover).trans
      hT.1.2.2.2.1
  · exact meetsOnlyAtTerminal_star hW.1.2.1 hWR hT.2 hcompat hcover

end SliceSpliceSource
end CardinalInduction
end Erdos599
