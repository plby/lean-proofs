/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Halfway930TailFreshness

/-!
# Incidence compiler for a fresh 9.31 attachment

The source construction makes the new relation enter the old linkage only
at its scheduled initial vertex, and never by an edge directed into the old
carrier.  That single literal incidence statement supplies three fields of
`FreshAdvanceSpliceRelation`: edge disjointness, the forward-sandwich
exclusion, and the stated real-predecessor condition.

These lemmas are deliberately independent of how the occurrence-level
inside/outside relation was constructed.
-/

noncomputable section

open Cardinal Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace FreshIncidence

/-- A relation with no edge entering the old carrier is disjoint from the
old edge union. -/
theorem disjoint_old_of_noIncomingOld
    (W : LinkageBlueprint Gamma Y kappa) (F : Set (V × V))
    (hF : ∀ {x y : V}, x ∈ W.vertexSet → (y, x) ∈ F → False) :
    Disjoint W.edgeSet F := by
  apply Set.disjoint_left.2
  intro e heW heF
  rcases Set.mem_iUnion.1 heW with ⟨p, heW⟩
  rcases Set.mem_iUnion.1 heW with ⟨hp, hep⟩
  exact hF ⟨p, hp, (p.edgeSet_subset_support_prod hep).2⟩ heF

/-- No old finite block can be bracketed by fresh edges when fresh edges do
not enter old vertices. -/
theorem noForwardSandwich_of_noIncomingOld
    (W : LinkageBlueprint Gamma Y kappa) (F : Set (V × V))
    (hF : ∀ {x y : V}, x ∈ W.vertexSet → (y, x) ∈ F → False) :
    SwitchingCore.NoForwardSandwich
      (D := imaginaryGraph Gamma Y kappa) W.edgeSet F := by
  intro p hne hp a b hap _hpb
  obtain ⟨c, hpc⟩ :=
    FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
      p p.start_mem_support hne
  have hpcW : (p.start, c) ∈ W.edgeSet := hp hpc
  rcases Set.mem_iUnion.1 hpcW with ⟨q, hpcW⟩
  rcases Set.mem_iUnion.1 hpcW with ⟨hq, hpcq⟩
  exact hF ⟨q, hq, (q.edgeSet_subset_support_prod hpcq).1⟩ hap

/-- The carrier-level incidence statement implies the exact real-vertex
field requested by `FreshAdvanceSpliceRelation`. -/
theorem noIncomingOldReal_of_noIncomingOld
    (W : LinkageBlueprint Gamma Y kappa) (F : Set (V × V))
    (hF : ∀ {x y : V}, x ∈ W.vertexSet → (y, x) ∈ F → False) :
    ∀ {x y : V}, x ∈ W.realPart.vertices → (y, x) ∈ F → False := by
  intro x y hx hyx
  exact hF (by simpa only [realPart_vertices] using hx) hyx

/-- No-incoming-old incidence is closed under adjoining another fresh
relation with the same property. -/
theorem noIncomingOld_union
    (W : LinkageBlueprint Gamma Y kappa) (E F : Set (V × V))
    (hE : ∀ {x y : V}, x ∈ W.vertexSet → (y, x) ∈ E → False)
    (hF : ∀ {x y : V}, x ∈ W.vertexSet → (y, x) ∈ F → False) :
    ∀ {x y : V}, x ∈ W.vertexSet → (y, x) ∈ E ∪ F → False := by
  intro x y hx hyx
  exact hyx.elim (hE hx) (hF hx)

/-- The canonical one-point roof incidence of a finite tail supplies the
global no-sandwich condition directly. -/
theorem finiteAttachment_noForwardSandwich
    {W : LinkageBlueprint Gamma Y kappa} {T Z persistent : Set V}
    (hW : W.IsLinkageBlueprint T Z persistent)
    (P : FinitePath Gamma.graph)
    (hinter : Gamma.roof T ∩ P.support ⊆ {P.start}) :
    SwitchingCore.NoForwardSandwich
      (D := imaginaryGraph Gamma Y kappa) W.edgeSet P.edgeSet := by
  apply noForwardSandwich_of_noIncomingOld W P.edgeSet
  exact FiniteAttachment.noIncomingOld hW P hinter

#print axioms disjoint_old_of_noIncomingOld
#print axioms noForwardSandwich_of_noIncomingOld
#print axioms noIncomingOldReal_of_noIncomingOld
#print axioms finiteAttachment_noForwardSandwich

end FreshIncidence
end Erdos599.Blueprint.LinkageBlueprint

