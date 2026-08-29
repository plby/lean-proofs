/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerRouteFootprints

/-!
# Fragment-carrier closure makes route independence symmetric

Nonempty vertex carriers are disjoint classes. Their membership relation
is symmetric, and a route footprint is closed under these classes. Thus
avoiding an earlier footprint with the new finite route already gives
disjointness of the two complete fragmentwise footprints.
-/

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set DirectedPath Alternating GroundingAllMarkerPorts

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I)

theorem vertexFragmentCarrier_eq_fragmentCarrier_of_mem (C : Set L.Vertex)
    {P : L.CutFragment} (hP : P ∈ L.cutFragments C) {a : L.Vertex}
    (ha : a ∈ L.fragmentCarrier C P) :
    L.vertexFragmentCarrier C a = L.fragmentCarrier C P := by
  classical
  cases a with
  | source i =>
      change L.record i = P.parent ∧ i ∉ L.badRecords C at ha
      simpa only [vertexFragmentCarrier, if_pos ha.2] using
        (L.fragmentCarrier_eq_recordCarrier C hP i ha.2 ha.1.symm).symm
  | edge e =>
      have heC : e.1 ∉ L.cutEdges C :=
        fun h ↦ Set.disjoint_left.mp (L.cutFragment_edges_disjoint C hP) ha h
      have heq := L.fragmentCarrier_eq_of_common C (L.edgeFragment_mem C e heC) hP
        ((L.edgeFragment C e heC).path.edgeSet_subset_support_prod (L.edgeFragment_edge C e heC)).1
        (P.path.edgeSet_subset_support_prod ha).1
      simpa only [vertexFragmentCarrier, dif_pos heC] using heq
  | marker y => exact ha.elim
  | off x => exact ha.elim

theorem vertexFragmentCarrier_eq_recordCarrier_of_mem (C : Set L.Vertex)
    (i : I) (hi : i ∉ L.badRecords C) {a : L.Vertex} (ha : a ∈ L.recordCarrier i) :
    L.vertexFragmentCarrier C a = L.recordCarrier i := by
  have hmem := L.recordFragment_mem C i hi
  have heq := L.fragmentCarrier_eq_recordCarrier C hmem i hi rfl
  have haFragment : a ∈ L.fragmentCarrier C (L.recordFragment i) := heq.symm ▸ ha
  exact (L.vertexFragmentCarrier_eq_fragmentCarrier_of_mem C hmem haFragment).trans heq

theorem vertexFragmentCarrier_eq_of_mem (C : Set L.Vertex) {a b : L.Vertex}
    (hab : a ∈ L.vertexFragmentCarrier C b) :
    L.vertexFragmentCarrier C a = L.vertexFragmentCarrier C b := by
  classical
  cases b with
  | source i =>
      by_cases hi : i ∉ L.badRecords C
      · simp only [vertexFragmentCarrier, if_pos hi] at hab ⊢
        exact L.vertexFragmentCarrier_eq_recordCarrier_of_mem C i hi hab
      · simp only [vertexFragmentCarrier, if_neg hi, Set.mem_empty_iff_false] at hab
  | edge e =>
      by_cases he : e.1 ∉ L.cutEdges C
      · simp only [vertexFragmentCarrier, dif_pos he] at hab ⊢
        exact L.vertexFragmentCarrier_eq_fragmentCarrier_of_mem C (L.edgeFragment_mem C e he) hab
      · simp only [vertexFragmentCarrier, dif_neg he, Set.mem_empty_iff_false] at hab
  | marker y => exact hab.elim
  | off x => exact hab.elim

theorem mem_vertexFragmentCarrier_self_of_mem (C : Set L.Vertex) {a b : L.Vertex}
    (hab : a ∈ L.vertexFragmentCarrier C b) : b ∈ L.vertexFragmentCarrier C b := by
  classical
  cases b with
  | source i =>
      by_cases hi : i ∉ L.badRecords C
      · simp only [vertexFragmentCarrier, if_pos hi]
        exact rfl
      · simp only [vertexFragmentCarrier, if_neg hi, Set.mem_empty_iff_false] at hab
  | edge e =>
      by_cases he : e.1 ∉ L.cutEdges C
      · simp only [vertexFragmentCarrier, dif_pos he]
        exact L.edgeFragment_edge C e he
      · simp only [vertexFragmentCarrier, dif_neg he, Set.mem_empty_iff_false] at hab
  | marker y => exact hab.elim
  | off x => exact hab.elim

theorem mem_vertexFragmentCarrier_symm (C : Set L.Vertex) {a b : L.Vertex}
    (hab : a ∈ L.vertexFragmentCarrier C b) : b ∈ L.vertexFragmentCarrier C a := by
  rw [L.vertexFragmentCarrier_eq_of_mem C hab]
  exact L.mem_vertexFragmentCarrier_self_of_mem C hab

theorem routeFootprint_closed (C : Set L.Vertex) (p : FinitePath L.web.graph)
    {a : L.Vertex} (ha : a ∈ L.routeFootprint C p) :
    L.vertexFragmentCarrier C a ⊆ L.routeFootprint C p := by
  rcases ha with ha | ha
  · exact L.vertexFragmentCarrier_subset_routeFootprint C p ha
  · obtain ⟨b, hb⟩ := Set.mem_iUnion.mp ha
    obtain ⟨hbp, hab⟩ := Set.mem_iUnion.mp hb
    rw [L.vertexFragmentCarrier_eq_of_mem C hab]
    exact L.vertexFragmentCarrier_subset_routeFootprint C p hbp

/-- Only the new path, not its whole expanded footprint, must be avoided
at a recursive selection step. Carrier closure supplies the full result. -/
theorem routeFootprint_disjoint_of_support_disjoint (C : Set L.Vertex)
    (p q : FinitePath L.web.graph) (hpq : Disjoint p.support (L.routeFootprint C q)) :
    Disjoint (L.routeFootprint C p) (L.routeFootprint C q) := by
  apply Set.disjoint_left.mpr
  rintro a (hap | hap) haq
  · exact Set.disjoint_left.mp hpq hap haq
  · obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hap
    obtain ⟨hbp, hab⟩ := Set.mem_iUnion.mp hb
    have hba := L.mem_vertexFragmentCarrier_symm C hab
    exact Set.disjoint_left.mp hpq hbp (L.routeFootprint_closed C q haq hba)

#print axioms vertexFragmentCarrier_eq_of_mem
#print axioms mem_vertexFragmentCarrier_symm
#print axioms routeFootprint_closed
#print axioms routeFootprint_disjoint_of_support_disjoint

end Erdos599.GroundingAllMarkerAuxiliary.Input
