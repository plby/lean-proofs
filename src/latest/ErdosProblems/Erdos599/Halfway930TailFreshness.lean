/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GlobalAdvance931

/-!
# Freshness of a retained finite attachment

A finite attachment which meets the incoming blueprint's roof only at its
start cannot introduce an edge entering an old blueprint vertex.  This is
the local incidence fact used by the old-to-new club-stage tail and by the
fresh 9.31 splice relation.  It depends only on the literal finite path and
the one-point roof intersection, not on the obsolete aggregate stage API.
-/

noncomputable section

open Cardinal Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace FiniteAttachment

/-- No edge of a finite attachment enters an old blueprint vertex when its
only possible contact with the old roof is its initial vertex. -/
theorem noIncomingOld
    {W : LinkageBlueprint Gamma Y kappa} {T Z persistent : Set V}
    (hW : W.IsLinkageBlueprint T Z persistent)
    (P : FinitePath Gamma.graph)
    (hinter : Gamma.roof T ∩ P.support ⊆ {P.start})
    {x y : V} (hx : x ∈ W.vertexSet) (hyx : (y, x) ∈ P.edgeSet) : False := by
  have hxRoof : x ∈ Gamma.roof T := hW.vertices_roofed hx
  have hxPath : x ∈ P.support :=
    (P.edgeSet_subset_support_prod hyx).2
  have hxStart : x = P.start :=
    Set.mem_singleton_iff.1 (hinter ⟨hxRoof, hxPath⟩)
  exact Alternating.FinitePath.no_incoming_edge_at_start P y (hxStart ▸ hyx)

/-- Consequently the finite attachment is edge-disjoint from the incoming
blueprint. -/
theorem edgeSet_disjoint_old
    {W : LinkageBlueprint Gamma Y kappa} {T Z persistent : Set V}
    (hW : W.IsLinkageBlueprint T Z persistent)
    (P : FinitePath Gamma.graph)
    (hinter : Gamma.roof T ∩ P.support ⊆ {P.start}) :
    Disjoint P.edgeSet W.edgeSet := by
  apply Set.disjoint_left.2
  intro e heP heW
  rcases Set.mem_iUnion.1 heW with ⟨p, heW⟩
  rcases Set.mem_iUnion.1 heW with ⟨hp, hep⟩
  exact noIncomingOld hW P hinter
    ⟨p, hp, (p.edgeSet_subset_support_prod hep).2⟩ heP

/-- Adjoining such a path to a relation which already has no new incoming
edge at old vertices preserves that property. -/
theorem noNewIncomingOld_union
    {W : LinkageBlueprint Gamma Y kappa} {T Z persistent : Set V}
    (hW : W.IsLinkageBlueprint T Z persistent)
    (P : FinitePath Gamma.graph)
    (hinter : Gamma.roof T ∩ P.support ⊆ {P.start})
    (E : Set (V × V))
    (hE : ∀ {x y : V}, x ∈ W.vertexSet → (y, x) ∈ E →
      (y, x) ∈ W.edgeSet) :
    ∀ {x y : V}, x ∈ W.vertexSet →
      (y, x) ∈ E ∪ P.edgeSet → (y, x) ∈ W.edgeSet := by
  intro x y hx hyx
  rcases hyx with hyxE | hyxP
  · exact hE hx hyxE
  · exact False.elim (noIncomingOld hW P hinter hx hyxP)

#print axioms noIncomingOld
#print axioms edgeSet_disjoint_old
#print axioms noNewIncomingOld_union

end FiniteAttachment
end Erdos599.Blueprint.LinkageBlueprint
