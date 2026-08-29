/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeSwitchingRelationalProgress
import ErdosProblems.Erdos599.AlternatingTraceOps

/-!
# Gap-free backward interval extension

The new backward fragment starts at the latest upper contact of the old
removed interval on its reference owner. Its edges are genuinely fresh,
and their insertion preserves the interval condition on every owner.
The empty old interval is represented by a trivial finite path, so the
same constructor covers a first visit as well as a repeated visit.
-/

namespace Erdos599.Alternating.SwitchingCore.RelationalInterval

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

theorem adjacent_subpaths_edgeSet_disjoint
    (p q : FinitePath Gamma.graph) (owner : Gamma.DPath)
    (hp : p.IsSubpathOf owner) (hq : q.IsSubpathOf owner)
    (hjoin : p.finish = q.start) : Disjoint p.edgeSet q.edgeSet := by
  have hinter := FinitePath.support_inter_subset_singleton_of_isSubpathOf
    p q owner hp hq hjoin
  apply Set.disjoint_left.2
  intro e hep heq
  have heStart : e.1 = p.finish := Set.mem_singleton_iff.mp
    (hinter ⟨(p.edgeSet_subset_support_prod hep).1,
      (q.edgeSet_subset_support_prod heq).1⟩)
  exact FinitePath.no_outgoing_edge_at_finish p e.2 (heStart ▸ hep)

/-- The newly appended interval contains no previously removed edge. -/
theorem backward_interval_extension_fresh
    {R : Set (V × V)}
    (owner : Gamma.DPath) (p q : FinitePath Gamma.graph)
    (hp : p.IsSubpathOf owner) (hq : q.IsSubpathOf owner)
    (hjoin : p.finish = q.start)
    (hRowner : R ∩ owner.edgeSet = p.edgeSet) : Disjoint q.edgeSet R := by
  have hdisj := adjacent_subpaths_edgeSet_disjoint p q owner hp hq hjoin
  apply Set.disjoint_left.2
  intro e heq heR
  have hep : e ∈ p.edgeSet := by
    rw [← hRowner]
    exact ⟨heR, hq.2 heq⟩
  exact Set.disjoint_left.1 hdisj hep heq

/-- An end-to-start extension of the selected owner's deleted interval
preserves interval convexity on the whole warp. -/
theorem backward_interval_extension_intervals
    {Y : Set Gamma.DPath} {R : Set (V × V)} (hY : Gamma.IsWarp Y)
    (hintervals : ∀ r ∈ Y, IsEdgeInterval (R ∩ r.edgeSet) r)
    (owner : Gamma.DPath) (howner : owner ∈ Y)
    (p q : FinitePath Gamma.graph)
    (hp : p.IsSubpathOf owner) (hq : q.IsSubpathOf owner)
    (hjoin : p.finish = q.start)
    (hRowner : R ∩ owner.edgeSet = p.edgeSet) :
    ∀ r ∈ Y, IsEdgeInterval ((R ∪ q.edgeSet) ∩ r.edgeSet) r := by
  intro r hrY
  by_cases hr : r = owner
  · subst r
    obtain ⟨s, _hsStart, _hsFinish, hsOwner, _hsSupport, hsEdges⟩ :=
      FinitePath.exists_append_isSubpathOf p q owner hp hq hjoin
    right
    refine ⟨.inl s, hsOwner, ?_⟩
    change (R ∪ q.edgeSet) ∩ owner.edgeSet = s.edgeSet
    have hqEdges : q.edgeSet ⊆ owner.edgeSet := hq.2
    rw [hsEdges, Set.union_inter_distrib_right, hRowner,
      Set.inter_eq_left.mpr hqEdges]
  · have hdisj : Disjoint q.edgeSet r.edgeSet := by
      apply Set.disjoint_left.2
      intro e heq her
      have hxOwner := hq.1 (q.edgeSet_subset_support_prod heq).1
      have hxr := (r.edgeSet_subset_support_prod her).1
      exact Set.disjoint_left.1 (hY hrY howner hr) hxr hxOwner
    have heq : (R ∪ q.edgeSet) ∩ r.edgeSet = R ∩ r.edgeSet := by
      rw [Set.union_inter_distrib_right, Set.disjoint_iff_inter_eq_empty.mp hdisj,
        Set.union_empty]
    rw [heq]
    exact hintervals r hrY

/-- The local backward step preserves reference-edge containment as well
as freshness and every interval certificate. -/
theorem backward_interval_extension
    {Y : Set Gamma.DPath} {R : Set (V × V)} (hY : Gamma.IsWarp Y)
    (hR : R ⊆ familyEdges Y)
    (hintervals : ∀ r ∈ Y, IsEdgeInterval (R ∩ r.edgeSet) r)
    (owner : Gamma.DPath) (howner : owner ∈ Y)
    (p q : FinitePath Gamma.graph)
    (hp : p.IsSubpathOf owner) (hq : q.IsSubpathOf owner)
    (hjoin : p.finish = q.start)
    (hRowner : R ∩ owner.edgeSet = p.edgeSet) :
    Disjoint q.edgeSet R ∧ R ∪ q.edgeSet ⊆ familyEdges Y ∧
      ∀ r ∈ Y, IsEdgeInterval ((R ∪ q.edgeSet) ∩ r.edgeSet) r := by
  refine ⟨backward_interval_extension_fresh owner p q hp hq hjoin hRowner, ?_,
    backward_interval_extension_intervals hY hintervals owner howner
      p q hp hq hjoin hRowner⟩
  rintro e (he | he)
  · exact hR he
  · simp only [familyEdges, Set.mem_iUnion]
    exact ⟨owner, howner, hq.2 he⟩

#print axioms backward_interval_extension

end Erdos599.Alternating.SwitchingCore.RelationalInterval
