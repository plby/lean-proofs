/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ControlledSlices
import ErdosProblems.Erdos599.RegularSplitLegality
import ErdosProblems.Erdos599.StageIntervalBuilder

/-!
# Surviving components between two regular-cardinal ladder stages

This file isolates the component-survival argument used in the annular
slice construction.  A source on the earlier frontier survives to a later
stage when its essential finite component has an essential finite extension
there.  Every failed source injects into the inessential part of the later
warp, so outside a bookkeeping obstruction stage there are fewer than
`kappa` failed sources.

The survivor witnesses also give, without any further choice principle at
the call site, the `EssentialStageExtensions` consumed by the stage-interval
constructor.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularSliceSurvivors

open DirectedPath

universe u

variable {V : Type u}

/-- A point of the earlier frontier whose essential finite component has an
essential finite extension at the later stage. -/
def IsSurvivorSource
    (Gamma : DWeb V) {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa)
    (delta beta : Ladder.Stage kappa) (x : V) : Prop :=
  x ∈ L.frontier delta ∧
    ∃ (p q : FinitePath Gamma.graph),
      (Sum.inl p : Gamma.DPath) ∈
          Gamma.essentialWarpPart (L.warpAt delta) ∧
        (Sum.inl q : Gamma.DPath) ∈
          Gamma.essentialWarpPart (L.warpAt beta) ∧
        p.finish = x ∧ Gamma.Extends (.inl p) (.inl q)

/-- The sources surviving from `delta` to `beta`. -/
def survivorSources
    (Gamma : DWeb V) {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa)
    (delta beta : Ladder.Stage kappa) : Set V :=
  {x | IsSurvivorSource Gamma L delta beta x}

/-- The earlier-frontier sources which fail to survive to `beta`. -/
def nonsurvivorSources
    (Gamma : DWeb V) {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa)
    (delta beta : Ladder.Stage kappa) : Set V :=
  L.frontier delta \ survivorSources Gamma L delta beta

@[simp]
theorem mem_survivorSources_iff
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa}
    {delta beta : Ladder.Stage kappa} {x : V} :
    x ∈ survivorSources Gamma L delta beta ↔
      IsSurvivorSource Gamma L delta beta x :=
  Iff.rfl

@[simp]
theorem mem_nonsurvivorSources_iff
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa}
    {delta beta : Ladder.Stage kappa} {x : V} :
    x ∈ nonsurvivorSources Gamma L delta beta ↔
      x ∈ L.frontier delta ∧
        x ∉ survivorSources Gamma L delta beta :=
  Iff.rfl

private theorem exists_essentialFinitePath_finish
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa}
    (hroof : L.RoofsSourceAtStages) {a : Ladder.Stage kappa}
    {x : V} (hx : x ∈ L.frontier a) :
    ∃ p : FinitePath Gamma.graph,
      (Sum.inl p : Gamma.DPath) ∈
        Gamma.essentialWarpPart (L.warpAt a) ∧ p.finish = x := by
  obtain ⟨p, hp, hterm⟩ :=
    Gamma.exists_essentialWarpPart_terminal_of_mem_quotientEssentialPart_source
      (hroof (Ladder.Stage.toExtended a)) hx
  rcases p with p | r
  · exact ⟨p, hp, Option.some.inj hterm⟩
  · simp at hterm

/-- Failure to survive injects into the inessential part of the later warp.
This is the pathwise core of the survivor estimate. -/
theorem mk_nonsurvivorSources_le_inessential
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa}
    (hroof : L.RoofsSourceAtStages)
    (hwarp : L.HasWarpStages)
    {delta beta : Ladder.Stage kappa}
    (hgrows : Gamma.LadderGrows (L.warpAt delta) (L.warpAt beta)) :
    #(nonsurvivorSources Gamma L delta beta) ≤
      #(Gamma.inessentialPaths (L.warpAt beta)) := by
  classical
  have hwitness : ∀ x : nonsurvivorSources Gamma L delta beta,
      ∃ (p : FinitePath Gamma.graph) (q : Gamma.DPath),
        (Sum.inl p : Gamma.DPath) ∈
            Gamma.essentialWarpPart (L.warpAt delta) ∧
          q ∈ Gamma.inessentialPaths (L.warpAt beta) ∧
          p.finish = x.1 ∧ Gamma.Extends (.inl p) q := by
    intro x
    obtain ⟨p, hp, hpfinish⟩ :=
      exists_essentialFinitePath_finish hroof x.2.1
    obtain ⟨q, hq, hpq⟩ := hgrows (.inl p) hp.1
    have hqInessential : q ∈ Gamma.inessentialPaths (L.warpAt beta) := by
      refine ⟨hq, ?_⟩
      intro hqEssential
      rcases q with q | r
      · apply x.2.2
        exact ⟨x.2.1, p, q, hp, hqEssential, hpfinish, hpq⟩
      · obtain ⟨_, hterminal, _⟩ := hqEssential.2
        simp at hterminal
    exact ⟨p, q, hp, hqInessential, hpfinish, hpq⟩
  choose left right hleft hright hfinish hext using hwitness
  let assign : nonsurvivorSources Gamma L delta beta →
      Gamma.inessentialPaths (L.warpAt beta) :=
    fun x ↦ ⟨right x, hright x⟩
  have hassign : Function.Injective assign := by
    intro x y hxy
    have hrightEq : right x = right y := by
      simpa only [assign] using congrArg Subtype.val hxy
    have hleftEq : left x = left y := by
      by_contra hne
      have hdis := hwarp (Ladder.Stage.toExtended delta)
        (hleft x).1 (hleft y).1 (fun h ↦ hne (Sum.inl.inj h))
      apply Set.disjoint_left.1 hdis (left x).start_mem_support
      have hxinitial := Gamma.extends_initial (hext x)
      have hyinitial := Gamma.extends_initial (hext y)
      have hstarts : (left x).start = (left y).start := by
        calc
          (left x).start = (right x).initial := hxinitial
          _ = (right y).initial := congrArg Path.initial hrightEq
          _ = (left y).start := hyinitial.symm
      exact hstarts ▸ (left y).start_mem_support
    apply Subtype.ext
    calc
      x.1 = (left x).finish := (hfinish x).symm
      _ = (left y).finish := congrArg FinitePath.finish hleftEq
      _ = y.1 := hfinish y
  exact Cardinal.mk_le_of_injective hassign

/-- Fewer than `kappa` earlier-frontier sources fail to survive at a later
non-obstruction stage of a legal ladder. -/
theorem mk_nonsurvivorSources_lt_of_legal
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa}
    (hL : L.IsSplitLegal)
    {delta beta : Ladder.Stage kappa} (_hdeltaBeta : delta < beta)
    (hbeta : beta ∉ L.phi)
    (hgrows : Gamma.LadderGrows (L.warpAt delta) (L.warpAt beta)) :
    #(nonsurvivorSources Gamma L delta beta) < kappa := by
  exact (mk_nonsurvivorSources_le_inessential
    hL.roofsSourceAtStages hL.warpStages hgrows).trans_lt
      (ControlledSlices.mk_inessentialWarpAt_lt_of_not_mem_phi
        Gamma L hL beta hbeta)

/-- Any chosen subset of survivor sources carries compatible essential
prefixes at the two stages. -/
noncomputable def essentialStageExtensionsOfSubset
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa}
    {delta beta : Ladder.Stage kappa} {S : Set V}
    (hS : S ⊆ survivorSources Gamma L delta beta) :
    SliceCandidate.EssentialStageExtensions L delta beta S := by
  classical
  have hwitness : ∀ x : S,
      ∃ (p q : FinitePath Gamma.graph),
        (Sum.inl p : Gamma.DPath) ∈
            Gamma.essentialWarpPart (L.warpAt delta) ∧
          (Sum.inl q : Gamma.DPath) ∈
            Gamma.essentialWarpPart (L.warpAt beta) ∧
          p.finish = x.1 ∧ Gamma.Extends (.inl p) (.inl q) := by
    intro x
    exact (hS x.2).2
  choose left right hleft hright hfinish hext using hwitness
  exact
    { leftPrefix := left
      rightPrefix := right
      left_mem := hleft
      right_mem := hright
      left_finish := hfinish
      extension := hext }

/-- For a legal ladder, any subset of the survivor set canonically realizes
the corresponding annular stage intervals. -/
noncomputable def stageIntervalRealizationOfSubset
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa}
    {delta beta : Ladder.Stage kappa} {S : Set V}
    (hS : S ⊆ survivorSources Gamma L delta beta)
    (hL : L.IsSplitLegal)
    (hgrows : Gamma.LadderGrows (L.warpAt delta) (L.warpAt beta)) :
    SliceCandidate.StageIntervalRealization L delta beta S :=
  (essentialStageExtensionsOfSubset hS).toStageIntervalRealization hL hgrows

private theorem finish_mem_essential_of_mem_essentialWarpPart
    {Gamma : DWeb V} {W : Set Gamma.DPath}
    {p : FinitePath Gamma.graph}
    (hp : (Sum.inl p : Gamma.DPath) ∈ Gamma.essentialWarpPart W) :
    p.finish ∈ Gamma.essential (Gamma.terminalFrontier W) := by
  obtain ⟨t, hterm, ht⟩ := hp.2
  have hfinish : p.finish = t := Option.some.inj hterm
  exact hfinish ▸ ht

/-- Earlier-frontier endpoint purity only uses the stage-separation and
warp geometry.  In particular it is independent of the ladder's obstruction
bookkeeping. -/
theorem segment_frontier_delta_of_geometry
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa}
    {delta beta : Ladder.Stage kappa} {S : Set V}
    (E : SliceCandidate.EssentialStageExtensions L delta beta S)
    (hroof : L.RoofsSourceAtStages)
    (hwarp : L.HasWarpStages)
    (hgrows : Gamma.LadderGrows (L.warpAt delta) (L.warpAt beta))
    (x : S) :
    (E.segment x).support ∩ L.frontier delta =
      {(E.segment x).start} := by
  apply Set.Subset.antisymm
  · rintro y ⟨hyseg, hyfrontier⟩
    obtain ⟨p, hp, hpfinish⟩ :=
      exists_essentialFinitePath_finish hroof hyfrontier
    obtain ⟨q, hq, hpq⟩ := hgrows (.inl p) hp.1
    have hqright : q = (.inl (E.rightPrefix x) : Gamma.DPath) := by
      by_contra hne
      have hdis := hwarp (Ladder.Stage.toExtended beta)
        hq (E.right_mem x).1 hne
      exact Set.disjoint_left.1 hdis
        (Gamma.support_mono_of_extends hpq
          (hpfinish.symm ▸ p.finish_mem_support))
        ((E.segment_subpath x).1 hyseg)
    have hpleft : p = E.leftPrefix x := by
      by_contra hne
      have hdis := hwarp (Ladder.Stage.toExtended delta)
        hp.1 (E.left_mem x).1 (fun h ↦ hne (Sum.inl.inj h))
      have hpstart := Gamma.extends_initial hpq
      have hlstart := Gamma.extends_initial (E.extension x)
      apply Set.disjoint_left.1 hdis p.start_mem_support
      have hstart : p.start = (E.leftPrefix x).start := by
        calc
          p.start = q.initial := hpstart
          _ = (E.rightPrefix x).start := by
            rw [hqright]
            rfl
          _ = (E.leftPrefix x).start := by
            simpa only [Path.initial] using hlstart.symm
      exact hstart ▸ (E.leftPrefix x).start_mem_support
    apply Set.mem_singleton_iff.mpr
    calc
      y = p.finish := hpfinish.symm
      _ = (E.leftPrefix x).finish := congrArg FinitePath.finish hpleft
      _ = x.1 := E.left_finish x
      _ = (E.segment x).start := (E.segment_start x).symm
  · intro y hy
    have hy' : y = (E.segment x).start := Set.mem_singleton_iff.mp hy
    subst y
    refine ⟨(E.segment x).start_mem_support, ?_⟩
    rw [E.segment_start x,
      L.frontier_eq_essential_terminalFrontier hroof delta]
    rw [← E.left_finish x]
    exact finish_mem_essential_of_mem_essentialWarpPart (E.left_mem x)

/-- Later-frontier endpoint purity only uses stage-separation and warp
geometry. -/
theorem segment_frontier_beta_of_geometry
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa}
    {delta beta : Ladder.Stage kappa} {S : Set V}
    (E : SliceCandidate.EssentialStageExtensions L delta beta S)
    (hroof : L.RoofsSourceAtStages)
    (hwarp : L.HasWarpStages) (x : S) :
    (E.segment x).support ∩ L.frontier beta =
      {(E.segment x).finish} := by
  apply Set.Subset.antisymm
  · rintro y ⟨hyseg, hyfrontier⟩
    obtain ⟨p, hp, hpfinish⟩ :=
      exists_essentialFinitePath_finish hroof hyfrontier
    have hpright : p = E.rightPrefix x := by
      by_contra hne
      have hdis := hwarp (Ladder.Stage.toExtended beta)
        hp.1 (E.right_mem x).1 (fun h ↦ hne (Sum.inl.inj h))
      exact Set.disjoint_left.1 hdis
        (hpfinish.symm ▸ p.finish_mem_support)
        ((E.segment_subpath x).1 hyseg)
    apply Set.mem_singleton_iff.mpr
    calc
      y = p.finish := hpfinish.symm
      _ = (E.rightPrefix x).finish := congrArg FinitePath.finish hpright
      _ = (E.segment x).finish := (E.segment_finish x).symm
  · intro y hy
    have hy' : y = (E.segment x).finish := Set.mem_singleton_iff.mp hy
    subst y
    refine ⟨(E.segment x).finish_mem_support, ?_⟩
    rw [E.segment_finish x]
    rw [L.frontier_eq_essential_terminalFrontier
      hroof beta]
    exact finish_mem_essential_of_mem_essentialWarpPart (E.right_mem x)

/-- Survivor extensions produce a stage-interval realization from only the
stage-separation and warp geometry.  This is the bookkeeping-free constructor
used on `canonicalLadderCore`. -/
noncomputable def stageIntervalRealizationOfSubset_of_geometry
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa}
    {delta beta : Ladder.Stage kappa} {S : Set V}
    (hS : S ⊆ survivorSources Gamma L delta beta)
    (hroof : L.RoofsSourceAtStages)
    (hwarp : L.HasWarpStages)
    (hgrows : Gamma.LadderGrows (L.warpAt delta) (L.warpAt beta)) :
    SliceCandidate.StageIntervalRealization L delta beta S := by
  let E := essentialStageExtensionsOfSubset hS
  exact
    { source_subset := by
        intro x hx
        rw [L.frontier_eq_essential_terminalFrontier hroof delta]
        have hessential := finish_mem_essential_of_mem_essentialWarpPart
          (E.left_mem ⟨x, hx⟩)
        simpa only [E.left_finish] using hessential
      carrier := fun x ↦ .inl (E.rightPrefix x)
      carrier_mem := fun x ↦ (E.right_mem x).1
      carrier_injective := by
        intro x y hxy
        exact E.rightPrefix_injective
          (hwarp (Ladder.Stage.toExtended delta))
          (Sum.inl.inj hxy)
      segment := E.segment
      segment_start := E.segment_start
      segment_finish_mem := by
        intro x
        rw [E.segment_finish x]
        rw [L.frontier_eq_essential_terminalFrontier hroof beta]
        exact finish_mem_essential_of_mem_essentialWarpPart (E.right_mem x)
      segment_subpath := E.segment_subpath
      segment_endpoints := by
        intro x
        rw [Set.inter_union_distrib_left,
          segment_frontier_delta_of_geometry E hroof hwarp hgrows x,
          segment_frontier_beta_of_geometry E hroof hwarp x]
        rfl
      segment_source :=
        segment_frontier_delta_of_geometry E hroof hwarp hgrows
      leftPrefix := E.leftPrefix
      rightPrefix := E.rightPrefix
      left_mem := E.left_mem
      right_mem := E.right_mem
      left_finish := E.left_finish
      right_finish := fun x ↦ (E.segment_finish x).symm
      prefix_inter := E.prefix_inter
      append_eq := E.append_eq }

end RegularSliceSurvivors
end CardinalInduction
end Erdos599
