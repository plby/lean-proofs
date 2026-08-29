/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Normalization
import ErdosProblems.Erdos599.SafeSwitching
import ErdosProblems.Erdos599.SliceSplice

/-!
# One annular successor splice

This file proves the elementary successor step used in the controlled-slice
recursion.  An old partial warp is assumed to lie below one ladder frontier
and to meet that frontier only at its finite terminals.  Annularity then
makes the old warp and the new slice compatible for source star.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SliceAnnularStep

open DirectedPath
open SliceSplice

universe u

variable {V : Type u}

/-- Annularity turns terminal cleanliness at the old frontier into the exact
cross-family compatibility required by source star. -/
theorem starCompatible_of_annular
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {old T : Set Gamma.DPath}
    {alpha beta : Ladder.Stage kappa} {U : Set V}
    (hessential : Gamma.essential (L.frontier alpha) = L.frontier alpha)
    (holdRoof : Gamma.vertexSet old ⊆ Gamma.roof (L.frontier alpha))
    (holdTerminal : ∀ p ∈ old, ∀ x ∈ p.support,
      x ∈ L.frontier alpha → Gamma.terminal? p = some x)
    (hT : IsAnnularSlice Gamma L T alpha beta U) :
    Gamma.StarCompatible old T := by
  intro p hp q hq x hxp hxq
  have hxFrontier : x ∈ L.frontier alpha :=
    vertexSet_inter_subset_frontier_of_annular hessential holdRoof hT
      ⟨⟨p, hp, hxp⟩, ⟨q, hq, hxq⟩⟩
  have hpTerminal : Gamma.terminal? p = some x :=
    holdTerminal p hp x hxp hxFrontier
  obtain ⟨f, hqf, _hends, hsource⟩ := hT.1.1.endpointPure q hq
  have hxf : x ∈ f.support := by
    rw [hqf] at hxq
    change x ∈ f.support at hxq
    exact hxq
  have hxStart : x = f.start := by
    have hx : x ∈ f.support ∩ L.frontier alpha := ⟨hxf, hxFrontier⟩
    rw [hsource] at hx
    exact Set.mem_singleton_iff.mp hx
  refine ⟨hpTerminal, ?_⟩
  rw [hqf]
  change f.start = x
  exact hxStart.symm

/-- A vertex of a finite path in the target side is its terminal vertex in
a normalized web. -/
theorem eq_finish_of_mem_target_of_normalized
    {Gamma : DWeb V} (hGamma : Gamma.IsNormalized)
    (p : FinitePath Gamma.graph) {x : V}
    (hxp : x ∈ p.support) (hxTarget : x ∈ Gamma.target) :
    x = p.finish := by
  by_contra hxFinish
  obtain ⟨y, hxy⟩ :=
    Alternating.FinitePath.exists_edge_from_of_mem_of_ne_finish
      p hxp hxFinish
  have hAdj : Gamma.graph.Adj x y := p.edgeSet_subset_adj hxy
  exact (hGamma hAdj).2 hxTarget

/-- In a normalized web, the suffix-meets-target conclusion already forces
the finite path itself to finish in the target. -/
theorem finish_mem_target_of_suffixMeets_of_normalized
    {Gamma : DWeb V} (hGamma : Gamma.IsNormalized)
    (p : FinitePath Gamma.graph) {a : V}
    (h : FinitePathSuffixMeets p a Gamma.target) :
    p.finish ∈ Gamma.target := by
  obtain ⟨before, after, hsupport, b, hbTarget, hbAfter⟩ := h
  have hbSupport : b ∈ p.support := by
    change b ∈ p.walk.support
    rw [hsupport]
    exact List.mem_append_right before hbAfter
  exact (eq_finish_of_mem_target_of_normalized hGamma p hbSupport hbTarget) ▸
    hbTarget

/-- Star does not introduce a vertex outside a set closed under the ladder
limit warp and containing the old partial warp.  The controlled-slice
certificate registers every exceptional component in that set. -/
theorem vertexSet_star_subset_of_controlledAnnularSlice
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {old T : Set Gamma.DPath}
    {ZV : Set V} {alpha beta : Ladder.Stage kappa} {U : Set V}
    (hclosed : IsLimitWarpClosed Gamma L ZV)
    (hold : Gamma.vertexSet old ⊆ ZV)
    (hT : RegularCardinal.IsControlledSlice
      (IsAnnularSlice Gamma L)
      (ControlledSlices.sliceMavericks Gamma L.limitWarp)
      (fun p : Gamma.DPath => p.support) ZV alpha beta U T)
    (hcompat : Gamma.StarCompatible old T) :
    Gamma.vertexSet (Gamma.star hcompat) ⊆ ZV := by
  rintro x ⟨r, hr, hxr⟩
  obtain ⟨p, rfl⟩ := hr
  rcases Gamma.mem_support_starPath_cases hcompat p hxr with
      hxOld | ⟨t, q, hpTerminal, hqT, hqInitial, hxq⟩
  · exact hold ⟨p.1, p.2, hxOld⟩
  · have htZ : t ∈ ZV :=
      hold ⟨p.1, p.2, Gamma.terminal_mem_support hpTerminal⟩
    have hqMeetsZ : (q.support ∩ ZV).Nonempty := by
      refine ⟨t, ?_, htZ⟩
      simpa only [hqInitial] using q.initial_mem_support
    exact controlledSlice_path_support_subset hclosed
      (controlledSlice_of_annularControlledSlice hT) hqT hqMeetsZ hxq

/-- The starred family lies below the later frontier.  Old vertices use
frontier chronology and the roof cut lemma; new vertices use annularity. -/
theorem vertexSet_star_subset_laterRoof
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {old T : Set Gamma.DPath}
    {alpha beta : Ladder.Stage kappa} {U : Set V}
    (hchronology : L.HasFrontierChronology)
    (hab : alpha < beta)
    (holdRoof : Gamma.vertexSet old ⊆ Gamma.roof (L.frontier alpha))
    (hT : IsAnnularSlice Gamma L T alpha beta U)
    (hcompat : Gamma.StarCompatible old T) :
    Gamma.vertexSet (Gamma.star hcompat) ⊆
      Gamma.roof (L.frontier beta) := by
  have holdLater : Gamma.vertexSet old ⊆
      Gamma.roof (L.frontier beta) :=
    holdRoof.trans (Gamma.roof_cut (hchronology hab))
  rintro x ⟨r, hr, hxr⟩
  obtain ⟨p, rfl⟩ := hr
  rcases Gamma.mem_support_starPath_cases hcompat p hxr with
      hxOld | ⟨_t, q, _hpTerminal, hqT, _hqInitial, hxq⟩
  · exact holdLater ⟨p.1, p.2, hxOld⟩
  · exact (hT.2 ⟨q, hqT, hxq⟩).2

/-- A requested old terminal is completed to the target by the source star.
The selected slice member starts at that terminal by endpoint purity, and
normalization turns `LinksToTarget`'s target hit into its terminal. -/
theorem exists_completed_starPath_of_scheduled_terminal
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {old T : Set Gamma.DPath}
    {alpha beta : Ladder.Stage kappa} {U : Set V}
    (hGamma : Gamma.IsNormalized)
    (hU : U ⊆ L.frontier alpha)
    (hT : IsAnnularSlice Gamma L T alpha beta U)
    (hcompat : Gamma.StarCompatible old T)
    {p : Gamma.DPath} (hpOld : p ∈ old) {a : V}
    (haU : a ∈ U) (hpTerminal : Gamma.terminal? p = some a) :
    ∃ r ∈ Gamma.star hcompat,
      r.initial = p.initial ∧
        ∃ b ∈ Gamma.target, Gamma.terminal? r = some b := by
  obtain ⟨q, hqT, f, hqf, hfU, hfSuffix⟩ := hT.1.2 a haU
  have haSupport : a ∈ f.support := by
    have haInter : a ∈ f.support ∩ U := by
      rw [hfU]
      exact Set.mem_singleton a
    exact haInter.1
  have haFrontier : a ∈ L.frontier alpha := hU haU
  obtain ⟨g, hqg, _hgEnds, hgSource⟩ :=
    hT.1.1.endpointPure q hqT
  have hgf : g = f := by
    rw [hqf] at hqg
    exact Sum.inl.inj hqg.symm
  subst g
  have haStart : a = f.start := by
    have ha : a ∈ f.support ∩ L.frontier alpha :=
      ⟨haSupport, haFrontier⟩
    rw [hgSource] at ha
    exact Set.mem_singleton_iff.mp ha
  have hfTarget : f.finish ∈ Gamma.target :=
    finish_mem_target_of_suffixMeets_of_normalized hGamma f hfSuffix
  rcases p with fp | ray
  · change some fp.finish = some a at hpTerminal
    have hfinish : fp.finish = a := Option.some.inj hpTerminal
    let pOld : old := ⟨Sum.inl fp, hpOld⟩
    refine ⟨Gamma.starPath hcompat pOld, ⟨pOld, rfl⟩,
      Gamma.initial_starPath hcompat pOld, f.finish, hfTarget, ?_⟩
    have hqStart : q.initial = fp.finish := by
      rw [hqf]
      exact haStart.symm.trans hfinish.symm
    have hinter : fp.support ∩ q.support ⊆ {fp.finish} := by
      intro x hx
      have hx' := hcompat (Sum.inl fp) hpOld q hqT x hx.1 hx.2
      exact Set.mem_singleton_iff.mpr (Option.some.inj hx'.1).symm
    have hstarEq : Gamma.starPath hcompat pOld =
        DirectedPath.Path.appendFinite fp q hqStart hinter := by
      dsimp only [pOld, DWeb.starPath]
      split
      next h =>
        let q' := Classical.choose h
        have hq'T : q' ∈ T := (Classical.choose_spec h).1
        have hq'Start : q'.initial = fp.finish :=
          (Classical.choose_spec h).2
        have hq'eq : q' = q :=
          DWeb.IsWarp.eq_of_initial_eq Gamma hT.1.1.isWarp hq'T hqT
            (hq'Start.trans hqStart.symm)
        dsimp only [q'] at hq'eq ⊢
        cases hq'eq
        rfl
      next h =>
        exfalso
        apply h
        exact ⟨q, hqT, hqStart⟩
    rw [hstarEq]
    exact (DirectedPath.Path.terminal?_appendFinite fp q hqStart hinter).trans
      (by rw [hqf]; rfl)
  · simp at hpTerminal

/-- The complete sound one-step package. -/
theorem annularStarStep
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {old T : Set Gamma.DPath}
    {Z : Set V} {alpha beta : Ladder.Stage kappa} {U : Set V}
    (hGamma : Gamma.IsNormalized)
    (hessential : Gamma.essential (L.frontier alpha) = L.frontier alpha)
    (hchronology : L.HasFrontierChronology)
    (hab : alpha < beta)
    (hU : U ⊆ L.frontier alpha)
    (hclosed : IsLimitWarpClosed Gamma L Z)
    (holdWarp : Gamma.IsWarp old)
    (holdRoof : Gamma.vertexSet old ⊆ Gamma.roof (L.frontier alpha))
    (holdZ : Gamma.vertexSet old ⊆ Z)
    (holdTerminal : ∀ p ∈ old, ∀ x ∈ p.support,
      x ∈ L.frontier alpha → Gamma.terminal? p = some x)
    (hT : RegularCardinal.IsControlledSlice
      (IsAnnularSlice Gamma L)
      (ControlledSlices.sliceMavericks Gamma L.limitWarp)
      (fun p : Gamma.DPath => p.support) Z alpha beta U T) :
    let hcompat : Gamma.StarCompatible old T :=
      starCompatible_of_annular hessential holdRoof holdTerminal hT.1
    Gamma.IsWarp (Gamma.star hcompat) ∧
      Gamma.ForwardExtension old (Gamma.star hcompat) ∧
      Gamma.vertexSet (Gamma.star hcompat) ⊆ Z ∧
      Gamma.vertexSet (Gamma.star hcompat) ⊆
        Gamma.roof (L.frontier beta) ∧
      ∀ p ∈ old, ∀ a ∈ U, Gamma.terminal? p = some a →
        ∃ r ∈ Gamma.star hcompat,
          r.initial = p.initial ∧
            ∃ b ∈ Gamma.target, Gamma.terminal? r = some b := by
  let hcompat : Gamma.StarCompatible old T :=
    starCompatible_of_annular hessential holdRoof holdTerminal hT.1
  dsimp only
  refine ⟨Gamma.isWarp_star holdWarp hT.1.1.1.isWarp hcompat,
    Gamma.forwardExtension_star hcompat,
    vertexSet_star_subset_of_controlledAnnularSlice hclosed holdZ hT hcompat,
    vertexSet_star_subset_laterRoof hchronology hab holdRoof hT.1 hcompat,
    ?_⟩
  intro p hp a ha hpterm
  exact exists_completed_starPath_of_scheduled_terminal
    hGamma hU hT.1 hcompat hp ha hpterm

end SliceAnnularStep
end CardinalInduction
end Erdos599
