/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteColouredOccurrenceWord
import ErdosProblems.Erdos599.SafeSwitchingRelationalProgress

/-!
# Exact switching semantics for finite coloured occurrence words

This is an additive internal representation, not a change to the problem
statement or to `AltPath`. The local interval/contact conditions are stated
on literal edges. The output balance is proved from the occurrence word,
and the output warp is constructed by relational decomposition.
-/

namespace Erdos599.Alternating.FiniteColouredOccurrenceWord

open Set DirectedPath SwitchingCore.RelationalInterval

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

/-- Local conditions ensuring that the literal coloured word implements
an interval-convex switch. No output warp or boundary equation is stored. -/
structure IsIntervalSafe (Q : FiniteColouredOccurrenceWord W Y) : Prop where
  incoming_removed : ∀ {a b x : V}, (a, x) ∈ Q.forwardEdges →
    (b, x) ∈ familyEdges Y → (b, x) ∈ Q.backwardEdges
  outgoing_removed : ∀ {x a b : V}, (x, a) ∈ Q.forwardEdges →
    (x, b) ∈ familyEdges Y → (x, b) ∈ Q.backwardEdges
  intervals : ∀ p ∈ Y, IsEdgeInterval (Q.backwardEdges ∩ p.edgeSet) p
  endpoint_pure : ∀ {x y : V}, (x, y) ∈ Q.forwardEdges →
    y ∉ Gamma.initialSet Y ∧ x ∉ Gamma.terminalFrontier Y

/-- The signed balance needed for the augmentation is derived from the
word, not assumed in `IsIntervalSafe`. In particular repeated ambient
vertices do not invalidate the construction. -/
theorem IsIntervalSafe.exists_augmenting_warp
    {Q : FiniteColouredOccurrenceWord W Y} (hQ : Q.IsIntervalSafe)
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    (hne : Q.vertex 0 ≠ Q.vertex (Fin.last Q.length))
    (hstart : Q.vertex 0 ∉ Gamma.vertexSet Y)
    (hfinish : Q.vertex (Fin.last Q.length) ∉ Gamma.vertexSet Y) :
    ∃ U : Set Gamma.DPath, Gamma.IsWarp U ∧ Gamma.HasFiniteCharacter U ∧
      familyEdges U = (familyEdges Y \ Q.backwardEdges) ∪ Q.forwardEdges ∧
      isolatedVertices U = isolatedVertices Y ∧
      Gamma.initialSet U = Gamma.initialSet Y ∪ {Q.vertex 0} ∧
      Gamma.terminalFrontier U = Gamma.terminalFrontier Y ∪
        {Q.vertex (Fin.last Q.length)} := by
  exact exists_finiteWarp_augmenting_of_incidence_balanced_intervalSwitch
    hW hY hWfin hYfin
    Q.backwardEdges_subset_familyEdges Q.forwardEdges_subset_familyEdges
    hQ.incoming_removed hQ.outgoing_removed
    hQ.intervals hQ.endpoint_pure hne hstart hfinish
    (Q.edgeBalance_forward_sub_backward hW hY)

/-- Degeneracy of a finite interval-safe occurrence word forces its
endpoints to belong to one forward owner, exactly as needed by the
finite-owner ray argument. The converse is not asserted. -/
theorem IsIntervalSafe.degenerate_endpoints_same_forward_owner
    {Q : FiniteColouredOccurrenceWord W Y} (hQ : Q.IsIntervalSafe)
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (p : FinitePath Gamma.graph)
    (hpstart : p.start = Q.vertex 0)
    (hpfinish : p.finish = Q.vertex (Fin.last Q.length))
    (hne : Q.vertex 0 ≠ Q.vertex (Fin.last Q.length))
    (hstart : Q.vertex 0 ∉ Gamma.vertexSet Y)
    (hfinish : Q.vertex (Fin.last Q.length) ∉ Gamma.vertexSet Y)
    (hp : p.edgeSet ⊆ (familyEdges Y \ Q.backwardEdges) ∪ Q.forwardEdges) :
    ∃ q ∈ W, Q.vertex 0 ∈ q.support ∧
      Q.vertex (Fin.last Q.length) ∈ q.support := by
  have hbi := biUnique_of_incident_reference_edges_removed hW hY
    Q.forwardEdges_subset_familyEdges hQ.incoming_removed hQ.outgoing_removed
  obtain ⟨q, hqW, hpq⟩ := finitePath_isFragmentOf_forwardWarp_of_incidence hW hY
    Q.forwardEdges_subset_familyEdges hQ.incoming_removed hQ.outgoing_removed
    rfl hbi hQ.intervals hQ.endpoint_pure p
    (fun heq ↦ hne (hpstart.symm.trans (heq.trans hpfinish))) hp
    (hpstart ▸ hstart) (hpfinish ▸ hfinish)
  exact ⟨q, hqW, hpstart ▸ hpq.1 p.start_mem_support,
    hpfinish ▸ hpq.1 p.finish_mem_support⟩

/-- At an actual backward-ending prefix, the next forward incidence is
unused. This follows from proved word balance and local reference contact
conditions; it is not an extra state field. -/
theorem IsIntervalSafe.no_forward_outgoing_at_backward_exit
    {Q : FiniteColouredOccurrenceWord W Y} (hQ : Q.IsIntervalSafe)
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hYfin : Gamma.HasFiniteCharacter Y)
    (hstart : Q.vertex 0 ∉ Gamma.vertexSet Y)
    (hback : HasOutgoing Q.backwardEdges (Q.vertex (Fin.last Q.length))) :
    ¬HasOutgoing Q.forwardEdges (Q.vertex (Fin.last Q.length)) := by
  have hne : Q.vertex 0 ≠ Q.vertex (Fin.last Q.length) := by
    intro heq
    obtain ⟨b, hb⟩ := hback
    exact hstart (heq ▸
      (familyEdges_subset_vertexSet_prod Y (Q.backwardEdges_subset_familyEdges hb)).1)
  exact no_forward_outgoing_at_backward_exit_of_reference hY hYfin
    Q.backwardEdges_subset_familyEdges hQ.incoming_removed
    (fun h ↦ (hQ.endpoint_pure h).1) hne
    (Q.edgeBalance_forward_sub_backward hW hY _) hback

#print axioms IsIntervalSafe.exists_augmenting_warp
#print axioms IsIntervalSafe.degenerate_endpoints_same_forward_owner
#print axioms IsIntervalSafe.no_forward_outgoing_at_backward_exit

end Erdos599.Alternating.FiniteColouredOccurrenceWord
