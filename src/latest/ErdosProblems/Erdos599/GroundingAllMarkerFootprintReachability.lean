/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerIndependentGeometry
import ErdosProblems.Erdos599.PopularCountableCutRegions

/-!
# Every captured source reaches its footprint's requested endpoint

An actual source on the route uses its suffix. A source added by carrier
expansion reaches the corresponding route vertex within its own record
carrier, then follows the suffix. Loop erasure preserves the endpoints
and footprint containment. This accounts for every captured source, not
merely the original sources chosen by the independent-route recursion.
-/

noncomputable section

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set Cardinal DirectedPath Alternating GroundingAllMarkerPorts Stationary

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I)

theorem routeFootprint_source_reaches_finish (C : Set L.Vertex)
    (p : FinitePath L.web.graph) (i : I) (hiFoot : Vertex.source i ∈ L.routeFootprint C p) :
    ∃ q : FinitePath L.web.graph, q.start = .source i ∧ q.finish = p.finish ∧
      q.support ⊆ L.routeFootprint C p := by
  classical
  have hiFoot' := hiFoot
  rcases hiFoot with hiPath | hiCarrier
  · refine ⟨p.suffixFrom (.source i) hiPath,
      p.suffixFrom_start (.source i) hiPath, p.suffixFrom_finish (.source i) hiPath, ?_⟩
    exact (p.suffixFrom_support_subset (.source i) hiPath).trans
      (L.support_subset_routeFootprint C p)
  · obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hiCarrier
    obtain ⟨haPath, hiA⟩ := Set.mem_iUnion.mp ha
    have haI := L.mem_vertexFragmentCarrier_symm C hiA
    have hiGood : i ∉ L.badRecords C := by
      by_contra hiBad
      simp only [vertexFragmentCarrier, if_neg (not_not_intro hiBad), Set.mem_empty_iff_false] at haI
    have haOwn : a ∈ L.recordCarrier i := by
      simpa only [vertexFragmentCarrier, if_pos hiGood] using haI
    have hOwnFoot : L.recordCarrier i ⊆ L.routeFootprint C p := by
      simpa only [vertexFragmentCarrier, if_pos hiGood] using L.routeFootprint_closed C p hiFoot'
    obtain ⟨q, hqs, hqt, hqSupport⟩ := L.recordCarrier_internally_reachable i a haOwn
    let t := p.suffixFrom a haPath
    let tw : Walk L.web.graph q.finish t.finish :=
      RelationalRoof.castStart L.web.graph.Adj
        ((p.suffixFrom_start a haPath).trans hqt.symm) t.walk
    let w := q.walk.append tw
    obtain ⟨z, hz⟩ := RelationalRoof.exists_pathTo_support_subset (R := L.web.graph.Adj) w
    refine ⟨⟨q.start, t.finish, z.1, z.2⟩, hqs, p.suffixFrom_finish a haPath, ?_⟩
    intro b hb
    have hbw := hz hb
    simp only [w, Walk.support_append, List.mem_append] at hbw
    rcases hbw with hbq | hbt
    · exact hOwnFoot (hqSupport hbq)
    · have hbTail : b ∈ t.walk.support := by
        simpa only [tw, RelationalRoof.support_castStart] using List.mem_of_mem_tail hbt
      exact L.support_subset_routeFootprint C p (p.suffixFrom_support_subset a haPath hbTail)

variable {kappa : Cardinal.{u}} {U : Popular.KappaIndexed L.web kappa}
  (S : Popular.PopularSeparator U) (hInitial : ∀ i, (L.record i).initial ∉ L.markers)

def selectedFootprintRegions : Popular.CountableCutRegions L.web S.cut (L.Request S.cut) where
  region r := L.routeFootprint S.cut (L.independentSelectedPath S hInitial r)
  countable r := L.routeFootprint_countable S.cut _
  disjoint := L.independentSelectedPath_footprints_disjoint S hInitial
  endpoint r := r.1
  endpoint_mem r := r.2.1
  source_reaches := by
    intro r x hx
    obtain ⟨i, hi⟩ := x.2
    have hiFoot : Vertex.source i ∈ L.routeFootprint S.cut
        (L.independentSelectedPath S hInitial r) := hi.symm ▸ hx
    obtain ⟨q, hqs, hqt, hqSupport⟩ := L.routeFootprint_source_reaches_finish S.cut
      (L.independentSelectedPath S hInitial r) i hiFoot
    exact ⟨q, hqs.trans hi, hqt.trans (L.independentSelectedPath_finish S hInitial r), hqSupport⟩

def usedFootprintIndices : Set (Below kappa) := (L.selectedFootprintRegions S hInitial).capturedIndices U

theorem usedFootprintIndices_nonstationary : ¬ IsStationaryBelow kappa (L.usedFootprintIndices S hInitial) :=
  (L.selectedFootprintRegions S hInitial).capturedIndices_nonstationary U S.not_strongly_popular

#print axioms routeFootprint_source_reaches_finish
#print axioms selectedFootprintRegions
#print axioms usedFootprintIndices_nonstationary

end Erdos599.GroundingAllMarkerAuxiliary.Input
