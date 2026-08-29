/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeSwitchingDegenerateConfinement
import ErdosProblems.Erdos599.SafeSwitchingArbitraryReference

/-!
# The endpoints of a degenerate exposed switching path have one forward owner

This form consumes the actual degeneracy predicate and exposed endpoints.
It derives the first and last forward edges from the switched path witness,
so applications need not choose those edges separately. Switching-ready
safeness remains explicit.
-/

namespace Erdos599.Alternating.SwitchingCore

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

theorem isBracketAlternating_of_forwardEdges_subset
    {U Y : Set Gamma.DPath} {Q : AltPath Gamma.graph}
    (hU : Gamma.IsWarp U) (hQ : IsAlternating Y Q)
    (hforward : Q.directionEdges .forward ⊆ familyEdges U) :
    IsBracketAlternating U Y Q := by
  refine ⟨hQ, ?_⟩
  intro l hl hdir
  apply finitePath_isFragmentOf_of_edgeSet_subset_familyEdges hU l.path l.nontrivial
  intro e he
  exact hforward (Set.mem_iUnion.2 ⟨l,
    Set.mem_iUnion.2 ⟨hl, Set.mem_iUnion.2 ⟨hdir, he⟩⟩⟩)

/-- The two-colour confinement proof applies to ray reference owners as
well; only the forward owner is required to be a warp. -/
theorem finiteSwitchedPath_isFragmentOf_forwardWarp_arbitraryReference
    {U Y : Set Gamma.DPath} {Q : AltPath Gamma.graph}
    (hU : Gamma.IsWarp U) (hSafe : IsSwitchingSafe Y Q)
    (hforward : Q.directionEdges .forward ⊆ familyEdges U)
    (p : FinitePath Gamma.graph) (hpne : p.start ≠ p.finish)
    (hp : p.edgeSet ⊆ switchedEdges Y Q)
    (hstart : ∃ y, (p.start, y) ∈ Q.directionEdges .forward)
    (hfinish : ∃ x, (x, p.finish) ∈ Q.directionEdges .forward) :
    IsFragmentOf p U := by
  let B := familyEdges Y \ Q.directionEdges .backward
  let F := Q.directionEdges .forward
  have hSwitch := hSafe.isSwitchingAlternating
  have hswitched : switchedEdges Y Q = B ∪ F := hSwitch.switchedEdges_eq
  have hdisj : Disjoint B F := by
    rw [Set.disjoint_left]
    intro e heB heF
    exact Set.disjoint_left.1 hSwitch.forwardLinksOff.directionEdges_disjoint heF heB.1
  have hbi : Relator.BiUnique (fun x y ↦ (x, y) ∈ B ∪ F) := by
    simpa only [← hswitched] using hSwitch.switchedEdges_biUnique
  have hpF : p.edgeSet ⊆ F :=
    finitePath_edgeSet_subset_right_of_noForwardSandwich B F hdisj hbi
      (ArbitraryReference.isSwitchingSafe_noForwardSandwich hSafe)
      p (by simpa only [← hswitched] using hp) hstart hfinish
  exact finitePath_isFragmentOf_of_edgeSet_subset_familyEdges hU p hpne
    (hpF.trans hforward)

theorem exists_common_forward_owner_of_isDegenerate
    {U Y : Set Gamma.DPath} {Q : AltPath Gamma.graph} {v : V}
    (hU : Gamma.IsWarp U)
    (hSafe : IsSwitchingSafe Y Q)
    (hforward : Q.directionEdges .forward ⊆ familyEdges U)
    (hne : Q.initial ≠ v)
    (hstartOff : Q.initial ∉ Gamma.vertexSet Y)
    (hfinishOff : v ∉ Gamma.vertexSet Y)
    (hdeg : IsDegenerate Y Q (.vertex v)) :
    ∃ p ∈ U, Q.initial ∈ p.support ∧ v ∈ p.support := by
  obtain ⟨r, hrstart, hrfinish, hr⟩ := hdeg
  have hrne : r.start ≠ r.finish := by
    simpa only [hrstart, hrfinish] using hne
  have hcover : r.edgeSet ⊆
      (familyEdges Y \ Q.directionEdges .backward) ∪
        Q.directionEdges .forward := by
    rw [← hSafe.isSwitchingAlternating.switchedEdges_eq]
    exact hr.1
  have hstart : ∃ y, (r.start, y) ∈ Q.directionEdges .forward := by
    obtain ⟨y, hy⟩ :=
      FinitePath.exists_edge_from_of_mem_of_ne_finish r r.start_mem_support hrne
    rcases hcover hy with hret | hfwd
    · have hmem := (familyEdges_subset_vertexSet_prod Y hret.1).1
      rw [hrstart] at hmem
      exact (hstartOff hmem).elim
    · exact ⟨y, hfwd⟩
  have hfinish : ∃ x, (x, r.finish) ∈ Q.directionEdges .forward := by
    obtain ⟨x, hx⟩ :=
      FinitePath.exists_edge_to_of_mem_of_ne_start r r.finish_mem_support hrne.symm
    rcases hcover hx with hret | hfwd
    · have hmem := (familyEdges_subset_vertexSet_prod Y hret.1).2
      rw [hrfinish] at hmem
      exact (hfinishOff hmem).elim
    · exact ⟨x, hfwd⟩
  obtain ⟨p, hp, hsupp, _hedges⟩ :=
    finiteSwitchedPath_isFragmentOf_forwardWarp_arbitraryReference
      hU hSafe hforward r hrne hr.1 hstart hfinish
  refine ⟨p, hp, ?_, ?_⟩
  · simpa only [hrstart] using hsupp r.start_mem_support
  · simpa only [hrfinish] using hsupp r.finish_mem_support

#print axioms isBracketAlternating_of_forwardEdges_subset
#print axioms finiteSwitchedPath_isFragmentOf_forwardWarp_arbitraryReference
#print axioms exists_common_forward_owner_of_isDegenerate

end Erdos599.Alternating.SwitchingCore
