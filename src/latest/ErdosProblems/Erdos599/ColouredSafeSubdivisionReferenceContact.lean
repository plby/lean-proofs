/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ArcSubdivisionNoStrong
import ErdosProblems.Erdos599.FiniteColouredOccurrenceSwitch

/-!
# Internal reference contacts in subdivision geometry

A pure forward edge whose endpoints both lie in the reference must itself
be a reference edge. The conclusion uses the actual subdivision incidence;
it is not asserted for arbitrary directed graphs.
-/

namespace Erdos599.Alternating.ColouredSafeSubdivisionReferenceContact

open Set DirectedPath Blueprint

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}

theorem referenceEdge_of_internal_pure_subdivision
    (hY : Gamma.IsWarp Y) (hYfin : Gamma.HasFiniteCharacter Y)
    {a b : V} (hinc : HasSubdivisionIncidenceAt Gamma.graph a b)
    (ha : a ∈ Gamma.vertexSet Y) (hb : b ∈ Gamma.vertexSet Y)
    (hbInitial : b ∉ Gamma.initialSet Y) (haTerminal : a ∉ Gamma.terminalFrontier Y) :
    (a, b) ∈ familyEdges Y := by
  rcases hinc with ⟨_hne, ⟨w, _hwa, _hwb, hin, _hout⟩ | ⟨w, _hwa, _hwb, hout, _hin⟩⟩
  · have hbIn : HasIncoming (familyEdges Y) b := by
      by_contra hno
      apply hbInitial
      rw [initialSet_eq_vertexSet_diff_hasIncoming hY hYfin]
      exact ⟨hb, hno⟩
    obtain ⟨x, hx⟩ := hbIn
    have hxa : x = a := hin (familyEdges_subset_adj Y hx)
    exact hxa ▸ hx
  · have haOut : HasOutgoing (familyEdges Y) a := by
      by_contra hno
      apply haTerminal
      rw [terminalFrontier_eq_vertexSet_diff_hasOutgoing hY hYfin]
      exact ⟨ha, hno⟩
    obtain ⟨x, hx⟩ := haOut
    have hxb : x = b := hout (familyEdges_subset_adj Y hx)
    exact hxb ▸ hx

/-- The internal-edge condition for any endpoint-pure forward subrelation
in a graph with hereditary subdivision incidence. -/
theorem internal_edges_of_pure_relation
    (hsub : HasHereditarySubdivisionIncidence Gamma.graph)
    (hY : Gamma.IsWarp Y) (hYfin : Gamma.HasFiniteCharacter Y)
    {F : Set (V × V)} (hF : F ⊆ {e | Gamma.graph.Adj e.1 e.2})
    (hpure : ∀ {a b}, (a, b) ∈ F →
      b ∉ Gamma.initialSet Y ∧ a ∉ Gamma.terminalFrontier Y)
    {a b : V} (he : (a, b) ∈ F)
    (ha : a ∈ Gamma.vertexSet Y) (hb : b ∈ Gamma.vertexSet Y) :
    (a, b) ∈ familyEdges Y :=
  referenceEdge_of_internal_pure_subdivision hY hYfin (hsub (hF he))
    ha hb (hpure he).1 (hpure he).2

#print axioms referenceEdge_of_internal_pure_subdivision
#print axioms internal_edges_of_pure_relation

end Erdos599.Alternating.ColouredSafeSubdivisionReferenceContact
