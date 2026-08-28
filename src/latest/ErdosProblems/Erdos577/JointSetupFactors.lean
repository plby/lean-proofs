import ErdosProblems.Erdos577.JointSetupRows
import ErdosProblems.Erdos577.CommonPathFactor
import ErdosProblems.Erdos577.CoreCliqueFactorSupport

/-! The two explicit factors excluding every contact from the third triangle vertex in TeX9.47. -/

namespace Erdos577.JointClaims

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma case_one_factor (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (hcl : G.IsNClique 4 q.support)
    (hx3 : G.Adj p.leaf (q 3)) (hr1 : G.Adj p.center (q 1))
    (hb2 : G.Adj (p.vertices 2) (q 2)) (hc0 : G.Adj (p.vertices 3) (q 0)) :
    LocalFactor G (p.support ∪ q.support) := by
  have hpm (i : Fin 4) : p.vertices i ∈ p.support := (mem_tupleSupport p.vertices _).mpr ⟨i, rfl⟩
  have hqm (i : Fin 4) : q i ∈ q.support := (q.mem_support _).mpr ⟨i, rfl⟩
  have hpq (i j : Fin 4) : p.vertices i ≠ q j :=
    fun he ↦ disjoint_left.mp hd (hpm i) (he.symm ▸ hqm j)
  have hqp (i j : Fin 4) : q i ≠ p.vertices j := (hpq j i).symm
  have hfirst : QuadOn G {p.leaf, p.center, q 1, q 3} :=
    QuadOn.of_vertices (hpq 0 1) (hpq 1 3) p.pendant hr1
      (hcl.isClique (hqm 1) (hqm 3) (q.injective.ne (by decide : (1 : Fin 4) ≠ 3))) hx3.symm
  have hsecond : QuadOn G {p.vertices 2, p.vertices 3, q 0, q 2} :=
    QuadOn.of_vertices (hpq 2 0) (hpq 3 2) p.edge23 hc0
      (hcl.isClique (hqm 0) (hqm 2) (q.injective.ne (by decide : (0 : Fin 4) ≠ 2))) hb2.symm
  have hdis : Disjoint ({p.leaf, p.center, q 1, q 3} : Finset V)
      {p.vertices 2, p.vertices 3, q 0, q 2} := by
    have hh : (q 0 ≠ q 1 ∧ q 0 ≠ q 3) ∧ q 2 ≠ q 1 ∧ q 2 ≠ q 3 :=
      ⟨⟨q.injective.ne (by decide : (0 : Fin 4) ≠ 1),
      q.injective.ne (by decide : (0 : Fin 4) ≠ 3)⟩,
      q.injective.ne (by decide : (2 : Fin 4) ≠ 1),
      q.injective.ne (by decide : (2 : Fin 4) ≠ 3)⟩
    simpa [Paw.leaf, Paw.center, hpq, hqp, p.vertices.injective.eq_iff] using hh
  have he : ({p.leaf, p.center, q 1, q 3} : Finset V) ∪
      {p.vertices 2, p.vertices 3, q 0, q 2} = p.support ∪ q.support := by
    rw [p.support_eq, q.support_four]
    ext u
    simp only [Paw.triangle, Paw.center, mem_insert, mem_singleton, mem_union]
    tauto
  rw [← he]
  exact ⟨_, subset_union_left, hfirst, (union_sdiff_cancel_left hdis).symm ▸ hsecond⟩

lemma third_common_factor (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support)
    (h : CommonReplacement G p.leaf (p.vertices 3) (p.vertices 2) q.support) :
    LocalFactor G (p.support ∪ q.support) := by
  have hsub : ({p.leaf, p.center, p.vertices 3} : Finset V) ⊆ p.support := by
    intro u hu
    simp only [mem_insert, mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · exact (mem_tupleSupport p.vertices _).mpr ⟨0, rfl⟩
    · exact (mem_tupleSupport p.vertices _).mpr ⟨1, rfl⟩
    · exact (mem_tupleSupport p.vertices _).mpr ⟨3, rfl⟩
  have hbout : p.vertices 2 ∉ ({p.leaf, p.center, p.vertices 3} : Finset V) ∪ q.support := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · simp only [Paw.leaf, Paw.center, mem_insert, mem_singleton, p.vertices.injective.eq_iff] at hh
      rcases hh with hh | hh | hh <;> omega
    · exact disjoint_left.mp hd ((mem_tupleSupport p.vertices _).mpr ⟨2, rfl⟩) hh
  have hf := LocalFactor.of_common_path p.leaf p.center (p.vertices 3) (p.vertices 2)
    (p.vertices.injective.ne (by decide : (0 : Fin 4) ≠ 3)) p.pendant p.edge13
    (hd.mono_left hsub) hbout h
  have he : insert (p.vertices 2) ({p.leaf, p.center, p.vertices 3} ∪ q.support) =
      p.support ∪ q.support := by
    rw [p.support_eq]
    ext u
    simp only [Paw.triangle, Paw.center, mem_insert, mem_singleton, mem_union]
    tauto
  exact he ▸ hf

variable [Fintype V] [DecidableRel G.Adj]

theorem third_row_zero {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (h : CaseOne p q ∨ CaseTwo p q) : degreeIn G (p.vertices 3) q.support = 0 := by
  have hthree : 3 ≤ degreeIn G p.leaf s := hq ▸ leaf_lower p q h
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hnlocal : ¬LocalFactor G (p.support ∪ q.support) := by
    rw [hp, hq]
    exact c.no_local_factor hcard hn hs
  have hcr := triangle_rows_disjoint hc hcard hn p hp hs hthree (p.vertices 3) p.center
    (by simp [Paw.triangle]) p.center_mem_triangle
    (p.vertices.injective.ne (by decide : (3 : Fin 4) ≠ 1))
  have hcb := triangle_rows_disjoint hc hcard hn p hp hs hthree (p.vertices 3) (p.vertices 2)
    (by simp [Paw.triangle]) (by simp [Paw.triangle])
    (p.vertices.injective.ne (by decide : (3 : Fin 4) ≠ 2))
  apply Nat.eq_zero_of_not_pos
  intro hpos
  obtain ⟨u, hu⟩ := card_pos.mp hpos
  obtain ⟨huQ, hcu⟩ := mem_filter.mp hu
  have hcs : u ∈ s.filter (G.Adj (p.vertices 3)) := mem_filter.mpr ⟨hq ▸ huQ, hcu⟩
  have hnotr : ¬G.Adj p.center u := fun hh ↦
    disjoint_left.mp hcr hcs (mem_filter.mpr ⟨hq ▸ huQ, hh⟩)
  have hnotb : ¬G.Adj (p.vertices 2) u := fun hh ↦
    disjoint_left.mp hcb hcs (mem_filter.mpr ⟨hq ▸ huQ, hh⟩)
  rcases h with h | h
  · have hcl : G.IsNClique 4 q.support := hq.symm ▸
      (hc.presentPaw_feasible p hp).clique_of_terminal_degree_four hs (hq ▸ h.1)
    obtain ⟨i, rfl⟩ := (q.mem_support u).mp huQ
    fin_cases i
    · exact hnlocal (case_one_factor p q hd hcl
        ((degreeIn_eq_card_iff p.leaf q.support).mp (h.1.trans q.card_support.symm)
          (q 3) ((q.mem_support _).mpr ⟨3, rfl⟩)) h.2.1 h.2.2.1 hcu)
    · exact hnotr h.2.1
    · exact hnotb h.2.2.1
    · exact hnotb h.2.2.2
  · by_cases hfour : degreeIn G p.leaf q.support = 4
    · have hxu := (degreeIn_eq_card_iff p.leaf q.support).mp
        (hfour.trans q.card_support.symm) u huQ
      exact hnlocal (third_common_factor p q hd
        ⟨u, huQ, hxu, hcu, case_two_universal hc p hp hs q hq h u huQ⟩)
    · have hseven := h.1
      have hxbound := degreeIn_le_card G p.leaf q.support
      have hbbound := degreeIn_le_card G (p.vertices 2) q.support
      rw [q.card_support] at hxbound hbbound
      have hbfull : degreeIn G (p.vertices 2) q.support = 4 := by omega
      exact hnotb ((degreeIn_eq_card_iff (p.vertices 2) q.support).mp
        (hbfull.trans q.card_support.symm) u huQ)

end Erdos577.JointClaims
