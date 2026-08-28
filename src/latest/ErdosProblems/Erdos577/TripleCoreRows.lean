import ErdosProblems.Erdos577.UniversalTripleLabels

/-! Exact rows and replacement cliques in the eight-vertex triple-pattern core. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma Paw.internal_contacts_eq_eight (p : Paw G) (hn : ¬QuadOn G p.support) :
    contacts G p.support p.support = 8 := by
  have hl : degreeIn G p.leaf p.support = 1 := by
    rw [p.support_eq, degreeIn_insert G _ _ p.leaf_not_mem_triangle,
      if_neg G.irrefl, zero_add, p.leaf_triangle_degree_eq_one hn]
  have hr : degreeIn G p.center p.support = 3 := by
    have hpend : G.Adj p.center p.leaf := p.pendant.symm
    rw [p.support_eq, degreeIn_insert G _ _ p.leaf_not_mem_triangle,
      if_pos hpend, degreeIn_clique G p.triangle_clique.isClique
        p.center_mem_triangle, p.triangle_clique.card_eq]
  obtain ⟨h2, h3⟩ := p.noncentral_support_degrees hn
  rw [p.contacts_support, p.contacts_triangle, hl, h2, h3]
  change 1 + (degreeIn G p.center p.support + (2 + 2)) = 8
  rw [hr]

namespace UniversalTriple

variable [Fintype V]
variable {c : TriangleChain G} {p : Paw G} {q : Quadrilateral G}

lemma Configuration.paw_outside (h : Configuration c p q) (i : Fin 4) :
    p.vertices i ∉ q.support := by
  exact fun hh ↦ disjoint_left.mp h.disjoint
    ((mem_tupleSupport _ _).mpr ⟨i, rfl⟩) hh

lemma Configuration.quad_outside (h : Configuration c p q) (i : Fin 4) :
    q i ∉ p.support := fun hh ↦ disjoint_left.mp h.disjoint hh
      ((q.mem_support _).mpr ⟨i, rfl⟩)

lemma Configuration.row_degrees (h : Configuration c p q) :
    degreeIn G p.leaf q.support = 3 ∧ degreeIn G (p.vertices 2) q.support = 3 ∧
      degreeIn G (p.vertices 3) q.support = 0 ∧
      degreeIn G p.center q.support = if G.Adj p.center (q 3) then 1 else 0 := by
  have he (v : V) : degreeIn G v q.support = ∑ i : Fin 4, if G.Adj v (q i) then 1 else 0 := by
    rw [Quadrilateral.support, degreeIn_image G v univ q q.injective]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [he]
    simp_rw [h.leaf_row]
    decide
  · rw [he]
    simp_rw [h.second_row]
    decide
  · exact (degreeIn_eq_zero_iff _ _).mpr (by
      intro v hv
      obtain ⟨i, rfl⟩ := (q.mem_support _).mp hv
      exact h.third_row i)
  · have hno (i : Fin 4) (hi : i ≠ 3) : ¬G.Adj p.center (q i) :=
      fun hh ↦ hi (h.center_row i hh)
    rw [he, Fin.sum_univ_four, if_neg (hno 0 (by decide)),
      if_neg (hno 1 (by decide)), if_neg (hno 2 (by decide))]
    omega

lemma Configuration.exposed_paw_degree (h : Configuration c p q) :
    degreeIn G (q 3) p.support = if G.Adj p.center (q 3) then 1 else 0 := by
  have hX : ¬G.Adj (q 3) p.leaf := fun he ↦ (h.leaf_row 3).mp he.symm rfl
  have hb : ¬G.Adj (q 3) (p.vertices 2) := fun he ↦ (h.second_row 3).mp he.symm rfl
  have hc : ¬G.Adj (q 3) (p.vertices 3) := fun he ↦ h.third_row 3 he.symm
  have he : degreeIn G (q 3) p.support =
      ∑ i : Fin 4, if G.Adj (q 3) (p.vertices i) then 1 else 0 := by
    rw [Paw.support, tupleSupport, degreeIn_image G _ univ p.vertices p.vertices.injective]
  rw [he, Fin.sum_univ_four]
  change (if G.Adj (q 3) p.leaf then 1 else 0) +
    (if G.Adj (q 3) p.center then 1 else 0) +
    (if G.Adj (q 3) (p.vertices 2) then 1 else 0) +
    (if G.Adj (q 3) (p.vertices 3) then 1 else 0) = _
  rw [if_neg hX, if_neg hb, if_neg hc]
  by_cases hr : G.Adj p.center (q 3)
  · simp [hr, hr.symm]
  · have hr' : ¬G.Adj (q 3) p.center := fun he ↦ hr he.symm
    simp [hr, hr']

lemma Configuration.replacement_complete (h : Configuration c p q)
    (v : V) (hv : v ∉ q.support) (hrow : ∀ i : Fin 4, i ≠ 3 → G.Adj v (q i)) :
    G.IsNClique 4 (insert v (q.support.erase (q 3))) := by
  have hout : v ∉ q.support.erase (q 3) := fun hh ↦ hv (mem_erase.mp hh).2
  refine ⟨?_, ?_⟩
  · rw [coe_insert]
    apply SimpleGraph.isClique_insert.mpr
    refine ⟨h.complete.isClique.subset (coe_subset.mpr (erase_subset _ _)), ?_⟩
    intro u hu _
    obtain ⟨hne, hm⟩ := mem_erase.mp hu
    obtain ⟨i, rfl⟩ := (q.mem_support _).mp hm
    exact hrow i (fun he ↦ hne (congrArg q he))
  · rw [card_insert_of_notMem hout,
      card_erase_of_mem ((q.mem_support _).mpr ⟨3, rfl⟩), q.card_support]

lemma Configuration.leaf_replacement_complete (h : Configuration c p q) :
    G.IsNClique 4 (insert p.leaf (q.support.erase (q 3))) :=
  h.replacement_complete p.leaf (h.paw_outside 0) (fun i hi ↦ (h.leaf_row i).mpr hi)

lemma Configuration.second_replacement_complete (h : Configuration c p q) :
    G.IsNClique 4 (insert (p.vertices 2) (q.support.erase (q 3))) :=
  h.replacement_complete (p.vertices 2) (h.paw_outside 2) (fun i hi ↦ (h.second_row i).mpr hi)

end UniversalTriple

end Erdos577
