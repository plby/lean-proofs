import ErdosProblems.Erdos577.WeightedTwelveCommonTriple

/-! The common triple and one old-triangle contact give two explicit complementary four-cycles. -/

namespace Erdos577.WeightedTwelve

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma DensePair.third_meets_pair {p : Paw G} {d : Quadrilateral G} (h : DensePair p d) :
    G.Adj (p.vertices 3) (d 2) ∨ G.Adj (p.vertices 3) (d 3) := by
  by_contra hn
  have hnot := not_or.mp hn
  have hsub : d.support.filter (G.Adj (p.vertices 3)) ⊆ {d 0, d 1} := by
    intro u hu
    obtain ⟨hu, hadj⟩ := mem_filter.mp hu
    obtain ⟨i, rfl⟩ := (d.mem_support u).mp hu
    fin_cases i
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_singleton_self _)
    · exact False.elim (hnot.1 hadj)
    · exact False.elim (hnot.2 hadj)
  have hle := (card_le_card hsub).trans (show ({d 0, d 1} : Finset V).card ≤ 2 from card_le_two)
  have hge := h.center_third_degrees.2
  change degreeIn G (p.vertices 3) d.support ≤ 2 at hle
  omega

omit [DecidableRel G.Adj] in
lemma final_factor_ordered (v : Quadrilateral G) (y b z1 z2 : V)
    (hcard : ({y, b, z1, z2} : Finset V).card = 4)
    (hdis : Disjoint ({y, b, z1, z2} : Finset V) v.support)
    (hyb : G.Adj y b) (hbz : G.Adj b z2)
    (hrows : ∀ i : Fin 4, i ≠ 0 → G.Adj z1 (v i) ∧ G.Adj z2 (v i))
    (hyv : G.Adj y (v 2)) : LocalFactor G (insert y ({b, z1, z2} ∪ v.support)) := by
  obtain ⟨_, hy1, hy2, hb1, _, h12⟩ := JointCore.four_distinct hcard
  have hout (u : V) (hu : u ∈ ({y, b, z1, z2} : Finset V)) : u ∉ v.support :=
    fun hh ↦ disjoint_left.mp hdis hu hh
  have hbase : Disjoint ({y, b, z2} : Finset V) v.support := hdis.mono_left (by
    intro u hu
    simp only [mem_insert, mem_singleton] at hu ⊢
    rcases hu with hu | hu | hu
    · exact Or.inl hu
    · exact Or.inr (Or.inl hu)
    · exact Or.inr (Or.inr (Or.inr hu)))
  have hzout : z1 ∉ ({y, b, z2} : Finset V) ∪ v.support := by
    simp only [mem_union, mem_insert, mem_singleton, not_or]
    exact ⟨⟨hy1.symm, hb1.symm, h12⟩, hout z1 (by simp)⟩
  have hquad : QuadOn G {v 2, y, b, z2} := QuadOn.of_vertices
    (fun he ↦ hout b (by simp) (he ▸ (v.mem_support _).mpr ⟨2, rfl⟩)) hy2
    hyv.symm hyb hbz (hrows 2 (by decide)).2
  have hrep := JointFinal.low_pair_replace v z1 (hout z1 (by simp))
    (hrows 1 (by decide)).1 (hrows 3 (by decide)).1 2 (Or.inr rfl)
  have hf := LocalFactor.of_replacement hbase hzout ((v.mem_support _).mpr ⟨2, rfl⟩) hquad hrep
  have he : insert z1 (({y, b, z2} : Finset V) ∪ v.support) =
      insert y ({b, z1, z2} ∪ v.support) := by
    simp only [insert_union, singleton_union]
    rw [insert_comm z1 y, insert_comm z1 b]
  exact he ▸ hf

omit [DecidableRel G.Adj] in
lemma final_factor_either (v : Quadrilateral G) (y b z1 z2 : V)
    (hcard : ({y, b, z1, z2} : Finset V).card = 4)
    (hdis : Disjoint ({y, b, z1, z2} : Finset V) v.support)
    (hyb : G.Adj y b) (hbz : G.Adj b z1 ∨ G.Adj b z2)
    (hrows : ∀ i : Fin 4, i ≠ 0 → G.Adj z1 (v i) ∧ G.Adj z2 (v i))
    (hyv : G.Adj y (v 2)) : LocalFactor G (insert y ({b, z1, z2} ∪ v.support)) := by
  rcases hbz with hbz | hbz
  · have hc' : ({y, b, z2, z1} : Finset V).card = 4 := by rwa [pair_comm z2 z1]
    have hd' : Disjoint ({y, b, z2, z1} : Finset V) v.support := by rwa [pair_comm z2 z1]
    have hf := final_factor_ordered v y b z2 z1 hc' hd' hyb hbz
      (fun i hi ↦ (hrows i hi).symm) hyv
    rwa [pair_comm z2 z1] at hf
  · exact final_factor_ordered v y b z1 z2 hcard hdis hyb hbz hrows hyv

end Erdos577.WeightedTwelve
