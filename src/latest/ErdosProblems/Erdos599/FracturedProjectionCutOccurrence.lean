/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FracturedProjectionFiniteOccurrenceLift
import ErdosProblems.Erdos599.HalfwayMacroContactOwnership

/-!
# Endpoint roles of projected cut contacts

An edge of an occurrence-lifted fractured member which leaves the cutting
set starts at the outgoing copy of its projected tail.  Dually, an edge
which enters the cutting set ends at the incoming copy of its projected
head.  These facts retain the side of a cut contact after compressor
projection and are the family-level input for projected bi-uniqueness.
-/

noncomputable section

namespace Erdos599.Blueprint.LinkageBlueprint.FracturedAssignmentPeel

open Set DirectedPath _root_.Erdos599.Alternating
open Alternating.FracturedDuplication PopularAuxiliary.Input

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}

private theorem path_edge_tail_ne_terminal {p : Gamma.DPath} {x y : V}
    (hxy : (x, y) ∈ p.edgeSet) : Gamma.terminal? p ≠ some x := by
  rcases p with p | r
  · intro hterm
    have hx : x = p.finish := by
      simpa [DWeb.terminal?, Path.terminal?] using Option.some.inj hterm.symm
    exact FinitePath.no_outgoing_edge_at_finish p y (hx ▸ hxy)
  · simp [DWeb.terminal?, Path.terminal?]

private theorem path_edge_head_ne_initial {p : Gamma.DPath} {x y : V}
    (hxy : (x, y) ∈ p.edgeSet) : y ≠ p.initial := by
  rcases p with p | r
  · exact FinitePath.target_ne_start_of_mem_edgeSet p hxy
  · rintro rfl
    rcases hxy with ⟨n, hn⟩
    have hzero : n + 1 = 0 := by
      apply r.injective
      exact (congrArg Prod.snd hn).symm
    omega

/-- The tail of a lifted edge at a cut contact is the outgoing occurrence. -/
theorem liftPath_edge_tail_eq_outgoing_of_cutEndpointPure
    (Z : FracturedWarp Gamma) (X : Set V)
    (hcut : CutEndpointPure Z.paths X)
    {p : Gamma.DPath} (hp : p ∈ Z.paths)
    {e : Vertex V × Vertex V} (he : e ∈ (liftPath Z p).edgeSet)
    (heX : project e.1 ∈ X) : e.1 = outgoing (project e.1) := by
  have heOriginal := projected_edge_mem_of_mem_liftPath Z p he
  have heSupport := (liftPath Z p).edgeSet_subset_support_prod he
  obtain ⟨x, hxp, hx⟩ := (mem_support_liftPath Z p e.1).1 heSupport.1
  have hxeq : x = project e.1 := by
    simpa only [project_occurrence] using congrArg project hx
  subst x
  rcases hcut p hp (project e.1) hxp heX with hinitial | hterminal
  · calc
      e.1 = occurrence Z p (project e.1) := hx.symm
      _ = outgoing (project e.1) := by simp [occurrence, hinitial]
  · exact False.elim (path_edge_tail_ne_terminal heOriginal hterminal)

/-- The head of a lifted edge at a cut contact is the incoming occurrence. -/
theorem liftPath_edge_head_eq_incoming_of_cutEndpointPure
    (Z : FracturedWarp Gamma) (X : Set V)
    (hcut : CutEndpointPure Z.paths X)
    {p : Gamma.DPath} (hp : p ∈ Z.paths)
    {e : Vertex V × Vertex V} (he : e ∈ (liftPath Z p).edgeSet)
    (heX : project e.2 ∈ X) : e.2 = incoming (project e.2) := by
  have heOriginal := projected_edge_mem_of_mem_liftPath Z p he
  have heSupport := (liftPath Z p).edgeSet_subset_support_prod he
  obtain ⟨y, hyp, hy⟩ := (mem_support_liftPath Z p e.2).1 heSupport.2
  have hyeq : y = project e.2 := by
    simpa only [project_occurrence] using congrArg project hy
  subst y
  rcases hcut p hp (project e.2) hyp heX with hinitial | hterminal
  · exact False.elim (path_edge_head_ne_initial heOriginal hinitial.symm)
  · calc
      e.2 = occurrence Z p (project e.2) := hy.symm
      _ = incoming (project e.2) := by
        have hne : project e.2 ≠ p.initial :=
          path_edge_head_ne_initial heOriginal
        simp [occurrence, hne, hterminal]

/-- A forward selected link inherits the outgoing role at every cut tail. -/
theorem bracketSafe_forwardEdge_tail_eq_outgoing_of_cutEndpointPure
    (Z : FracturedWarp Gamma) (X : Set V)
    (hcut : CutEndpointPure Z.paths X)
    {Q : AltPath (web Gamma Z).graph}
    (hQ : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) Q)
    {l : Link (web Gamma Z).graph} (hl : l ∈ Q.links)
    (hforward : l.direction = .forward)
    {e : Vertex V × Vertex V} (he : e ∈ l.path.edgeSet)
    (heX : project e.1 ∈ X) : e.1 = outgoing (project e.1) := by
  obtain ⟨P, hP, hsub⟩ := hQ.isBracketAlternating.2 l hl hforward
  rcases hP with ⟨p, hp, rfl⟩
  exact liftPath_edge_tail_eq_outgoing_of_cutEndpointPure Z X hcut hp.1
    (hsub.2 he) heX

/-- A forward selected link inherits the incoming role at every cut head. -/
theorem bracketSafe_forwardEdge_head_eq_incoming_of_cutEndpointPure
    (Z : FracturedWarp Gamma) (X : Set V)
    (hcut : CutEndpointPure Z.paths X)
    {Q : AltPath (web Gamma Z).graph}
    (hQ : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) Q)
    {l : Link (web Gamma Z).graph} (hl : l ∈ Q.links)
    (hforward : l.direction = .forward)
    {e : Vertex V × Vertex V} (he : e ∈ l.path.edgeSet)
    (heX : project e.2 ∈ X) : e.2 = incoming (project e.2) := by
  obtain ⟨P, hP, hsub⟩ := hQ.isBracketAlternating.2 l hl hforward
  rcases hP with ⟨p, hp, rfl⟩
  exact liftPath_edge_head_eq_incoming_of_cutEndpointPure Z X hcut hp.1
    (hsub.2 he) heX

end Erdos599.Blueprint.LinkageBlueprint.FracturedAssignmentPeel

#print axioms Erdos599.Blueprint.LinkageBlueprint.FracturedAssignmentPeel.liftPath_edge_tail_eq_outgoing_of_cutEndpointPure
#print axioms Erdos599.Blueprint.LinkageBlueprint.FracturedAssignmentPeel.liftPath_edge_head_eq_incoming_of_cutEndpointPure
