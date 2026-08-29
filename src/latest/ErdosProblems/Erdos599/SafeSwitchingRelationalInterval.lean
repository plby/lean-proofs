/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeSwitchingArbitraryReference

/-!
# Relational interval-convex switching

This module isolates the no-forward-sandwich argument from alternating-path
syntax.  A locally biunique relation obtained by deleting one interval from
each member of a warp and inserting edges disjoint from the warp cannot have
an inserted--retained--inserted sandwich, provided inserted edges do not enter
warp initials or leave finite warp terminals.
-/

namespace Erdos599

open Set DirectedPath

universe u

namespace Alternating
namespace SwitchingCore
namespace RelationalInterval

variable {V : Type u} {Gamma : DWeb V}

/-- An incoming warp edge at the target of an inserted edge must have been
deleted: otherwise local left-uniqueness identifies it with an inserted edge,
contradicting disjointness from the warp. -/
theorem incoming_mem_removed
    {Y : Set Gamma.DPath} {R F E : Set (V × V)}
    (hE : E = (familyEdges Y \ R) ∪ F)
    (hunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ E))
    (hdisj : Disjoint F (familyEdges Y))
    {a z x : V} (hF : (a, x) ∈ F)
    (hYedge : (z, x) ∈ familyEdges Y) : (z, x) ∈ R := by
  by_contra hnot
  have hzE : (z, x) ∈ E := by
    rw [hE]
    exact Or.inl ⟨hYedge, hnot⟩
  have haE : (a, x) ∈ E := by
    rw [hE]
    exact Or.inr hF
  have hza : z = a := hunique.1 hzE haE
  exact Set.disjoint_left.1 hdisj hF (hza ▸ hYedge)

/-- The outgoing analogue of `incoming_mem_removed`. -/
theorem outgoing_mem_removed
    {Y : Set Gamma.DPath} {R F E : Set (V × V)}
    (hE : E = (familyEdges Y \ R) ∪ F)
    (hunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ E))
    (hdisj : Disjoint F (familyEdges Y))
    {x w b : V} (hF : (x, b) ∈ F)
    (hYedge : (x, w) ∈ familyEdges Y) : (x, w) ∈ R := by
  by_contra hnot
  have hwE : (x, w) ∈ E := by
    rw [hE]
    exact Or.inl ⟨hYedge, hnot⟩
  have hbE : (x, b) ∈ E := by
    rw [hE]
    exact Or.inr hF
  have hwb : w = b := hunique.2 hwE hbE
  exact Set.disjoint_left.1 hdisj hF (hwb ▸ hYedge)

/-- Direct removal of every conflicting reference incidence, together
with interval convexity, excludes a retained middle. A forward edge may
itself be a removed reference edge which is then reinserted. -/
theorem noForwardSandwich_of_incidence_intervalConvex
    {Y : Set Gamma.DPath} {R F : Set (V × V)}
    (hY : Gamma.IsWarp Y)
    (hin : ∀ {a b x : V}, (a, x) ∈ F →
      (b, x) ∈ familyEdges Y → (b, x) ∈ R)
    (hout : ∀ {x a b : V}, (x, a) ∈ F →
      (x, b) ∈ familyEdges Y → (x, b) ∈ R)
    (hinterval : ∀ p ∈ Y, IsEdgeInterval (R ∩ p.edgeSet) p)
    (hpure : ∀ {x y : V}, (x, y) ∈ F →
      y ∉ Gamma.initialSet Y ∧ x ∉ Gamma.terminalFrontier Y) :
    NoForwardSandwich (D := Gamma.graph) (familyEdges Y \ R) F := by
  intro r hrne hrRet a b hIn hOut
  have hfrag := finitePath_isFragmentOf_of_edgeSet_subset_familyEdges
    hY r hrne (hrRet.trans Set.sdiff_subset)
  rcases hfrag with ⟨p, hpY, hrp⟩
  have hstartNotInitial : r.start ∉ Gamma.initialSet Y := (hpure hIn).1
  have hfinishNotTerminal : r.finish ∉ Gamma.terminalFrontier Y :=
    (hpure hOut).2
  obtain ⟨t, hrt⟩ :=
    FinitePath.exists_edge_from_of_mem_of_ne_finish r
      r.start_mem_support hrne
  have hrtRet := hrRet hrt
  rcases p with p | p
  · have hstartNe : r.start ≠ p.start := by
      intro heq
      apply hstartNotInitial
      exact ⟨.inl p, hpY, heq.symm⟩
    have hfinishNe : r.finish ≠ p.finish := by
      intro heq
      apply hfinishNotTerminal
      exact ⟨.inl p, hpY, by simpa [heq]⟩
    obtain ⟨z, hzP⟩ :=
      FinitePath.exists_edge_to_of_mem_of_ne_start p
        (hrp.1 r.start_mem_support) hstartNe
    obtain ⟨w, hwP⟩ :=
      FinitePath.exists_edge_from_of_mem_of_ne_finish p
        (hrp.1 r.finish_mem_support) hfinishNe
    have hzFamily : (z, r.start) ∈ familyEdges Y := by
      simp only [familyEdges, Set.mem_iUnion]
      exact ⟨.inl p, hpY, hzP⟩
    have hwFamily : (r.finish, w) ∈ familyEdges Y := by
      simp only [familyEdges, Set.mem_iUnion]
      exact ⟨.inl p, hpY, hwP⟩
    have hzR : (z, r.start) ∈ R :=
      hin hIn hzFamily
    have hwR : (r.finish, w) ∈ R :=
      hout hOut hwFamily
    classical
    letI := Classical.decEq V
    have hpos := FinitePath.edgeSet_eq_position_interval p r hrp
    have hrtPos : p.walk.support.idxOf r.start ≤
        p.walk.support.idxOf (r.start, t).1 ∧
        p.walk.support.idxOf (r.start, t).1 <
          p.walk.support.idxOf r.finish := by
      rw [hpos] at hrt
      exact hrt.2
    have hzPos := Walk.idxOf_target_eq_source_add_one
      p.walk p.isPath hzP
    have hleft : p.walk.support.idxOf (z, r.start).1 ≤
        p.walk.support.idxOf (r.start, t).1 := by
      change p.walk.support.idxOf z ≤ p.walk.support.idxOf r.start
      omega
    have hright : p.walk.support.idxOf (r.start, t).1 ≤
        p.walk.support.idxOf (r.finish, w).1 := by
      change p.walk.support.idxOf r.start ≤
        p.walk.support.idxOf r.finish
      omega
    have hrtR : (r.start, t) ∈ R ∩ p.edgeSet :=
      IsEdgeInterval.mem_of_between_positions
        (hinterval (.inl p) hpY) ⟨hzR, hzP⟩ ⟨hwR, hwP⟩
        (hrp.2 hrt) hleft hright
    exact hrtRet.2 hrtR.1
  · have hstartNe : r.start ≠ p.initial := by
      intro heq
      apply hstartNotInitial
      exact ⟨.inr p, hpY, heq.symm⟩
    obtain ⟨is, his⟩ := hrp.1 r.start_mem_support
    have hisPos : 0 < is := by
      by_contra hnot
      have hisZero : is = 0 := by omega
      subst is
      exact hstartNe his.symm
    obtain ⟨iz, rfl⟩ : ∃ iz, is = iz + 1 := by
      exact ⟨is - 1, by omega⟩
    have hzP : (p iz, r.start) ∈ p.edgeSet := by
      refine ⟨iz, ?_⟩
      rw [his]
    obtain ⟨iw, hiw⟩ := hrp.1 r.finish_mem_support
    have hwP : (r.finish, p (iw + 1)) ∈ p.edgeSet := by
      refine ⟨iw, ?_⟩
      rw [hiw]
    have hzFamily : (p iz, r.start) ∈ familyEdges Y := by
      simp only [familyEdges, Set.mem_iUnion]
      exact ⟨.inr p, hpY, hzP⟩
    have hwFamily : (r.finish, p (iw + 1)) ∈ familyEdges Y := by
      simp only [familyEdges, Set.mem_iUnion]
      exact ⟨.inr p, hpY, hwP⟩
    have hzR : (p iz, r.start) ∈ R :=
      hin hIn hzFamily
    have hwR : (r.finish, p (iw + 1)) ∈ R :=
      hout hOut hwFamily
    obtain ⟨ir, hir⟩ := hrp.2 hrt
    have hirEq : ir = iz + 1 := by
      apply p.injective
      exact (congrArg Prod.fst hir).symm.trans his.symm
    have hfinishMap : r.finish = p (ir + r.walk.length) := by
      have hmap :=
        ArbitraryReference.Walk.getElem_eq_ray_start_add r.walk p hrp.2 ir
          (congrArg Prod.fst hir)
      simpa [Walk.getElem_length_eq_end] using hmap r.walk.length le_rfl
    have hiwEq : ir + r.walk.length = iw := by
      apply p.injective
      exact hfinishMap.symm.trans hiw.symm
    have hzI : (p iz, p (iz + 1)) ∈ R ∩ p.edgeSet := by
      rw [his]
      exact ⟨hzR, hzP⟩
    have hwI : (p iw, p (iw + 1)) ∈ R ∩ p.edgeSet := by
      rw [hiw]
      exact ⟨hwR, hwP⟩
    have hrtI : (p ir, p (ir + 1)) ∈ R ∩ p.edgeSet :=
      ArbitraryReference.IsEdgeInterval.mem_of_between_ray_positions
        (hinterval (.inr p) hpY) hzI hwI (by omega) (by omega)
    apply hrtRet.2
    rw [hir]
    exact hrtI.1

/-- The earlier disjoint-edge interface is preserved as a specialization
of the direct-incidence theorem. -/
theorem noForwardSandwich_of_intervalConvex
    {Y : Set Gamma.DPath} {R F E : Set (V × V)}
    (hY : Gamma.IsWarp Y)
    (_hR : R ⊆ familyEdges Y)
    (hFdisj : Disjoint F (familyEdges Y))
    (hE : E = (familyEdges Y \ R) ∪ F)
    (hunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ E))
    (hinterval : ∀ p ∈ Y, IsEdgeInterval (R ∩ p.edgeSet) p)
    (hpure : ∀ {x y : V}, (x, y) ∈ F →
      y ∉ Gamma.initialSet Y ∧ x ∉ Gamma.terminalFrontier Y) :
    NoForwardSandwich (D := Gamma.graph) (familyEdges Y \ R) F := by
  exact noForwardSandwich_of_incidence_intervalConvex hY
    (incoming_mem_removed hE hunique hFdisj)
    (outgoing_mem_removed hE hunique hFdisj) hinterval hpure

/-- Direct contact removal makes the retained and inserted relations
disjoint even if some inserted edges were reference edges before removal. -/
theorem retained_disjoint_inserted_of_incidence
    {Y : Set Gamma.DPath} {R F : Set (V × V)}
    (hin : ∀ {a b x : V}, (a, x) ∈ F →
      (b, x) ∈ familyEdges Y → (b, x) ∈ R) :
    Disjoint (familyEdges Y \ R) F := by
  apply Set.disjoint_left.2
  intro e heY heF
  exact heY.2 (hin heF heY.1)

#print axioms noForwardSandwich_of_incidence_intervalConvex
#print axioms noForwardSandwich_of_intervalConvex

end RelationalInterval
end SwitchingCore
end Alternating
end Erdos599
