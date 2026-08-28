import ErdosProblems.Erdos577.TwoCoreFirstExchange

/-! The complete first-block replacement and exact scores of full-row replacements. -/

namespace Erdos577.TwoCore

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
lemma erase_three_support (q : Quadrilateral G) :
    q.support.erase (q 3) = {q 0, q 1, q 2} := by
  have h03 : q 0 ≠ q 3 := q.injective.ne (by decide : (0 : Fin 4) ≠ 3)
  have h13 : q 1 ≠ q 3 := q.injective.ne (by decide : (1 : Fin 4) ≠ 3)
  have h23 : q 2 ≠ q 3 := q.injective.ne (by decide : (2 : Fin 4) ≠ 3)
  rw [q.support_four, erase_insert_of_ne h03, erase_insert_of_ne h13,
    erase_insert_of_ne h23, erase_singleton]
  rfl

lemma first_block_score (q : Quadrilateral G) (hdiag : PawBlock.OnlyFirst q) :
    edgeCount G q.support = 5 := by
  rw [q.edgeCount_eq, if_pos hdiag.1, if_neg hdiag.2]

lemma third_replacement (q : Quadrilateral G) (z : V) (hdiag : PawBlock.OnlyFirst q)
    (hrow : ∀ i : Fin 4, i ≠ 3 → G.Adj z (q i)) :
    G.IsNClique 4 (insert z (q.support.erase (q 3))) ∧
      QuadOn G (insert z (q.support.erase (q 3))) ∧
      edgeCount G (insert z (q.support.erase (q 3))) = edgeCount G q.support + 1 := by
  have htri : G.IsNClique 3 {q 0, q 1, q 2} :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨q.adjacent 0, hdiag.1, q.adjacent 1⟩
  have hcl : G.IsNClique 4 (insert z (q.support.erase (q 3))) := by
    rw [erase_three_support]
    apply htri.insert
    intro u hu
    simp only [mem_insert, mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · exact hrow 0 (by decide)
    · exact hrow 1 (by decide)
    · exact hrow 2 (by decide)
  refine ⟨hcl, QuadOn.of_clique hcl.card_eq hcl.isClique, ?_⟩
  rw [edgeCount_clique hcl.isClique, hcl.card_eq, first_block_score q hdiag]
  decide +kernel

lemma full_replacement_score {b : Finset V} (hb : QuadOn G b) (x : V)
    (hfull : degreeIn G x b = 4) (u : V) (hu : u ∈ b) :
    QuadOn G (insert x (b.erase u)) ∧
      edgeCount G (insert x (b.erase u)) + degreeIn G u b = edgeCount G b + 3 := by
  have hx := FullRow.full_row_outside hb x hfull
  have hxu := (degreeIn_eq_card_iff x b).mp (hfull.trans hb.card.symm) u hu
  have he := degreeIn_erase_add G x u hu
  rw [hfull, if_pos hxu] at he
  refine ⟨hb.replace_of_degree_four hx hfull hu, ?_⟩
  have hs := edgeCount_replace G u x hu hx
  omega

lemma quad_vertex_degree {b : Finset V} (hb : QuadOn G b) (u : V) (hu : u ∈ b) :
    degreeIn G u b = 2 ∨ degreeIn G u b = 3 := by
  obtain ⟨q, hq⟩ := hb
  obtain ⟨i, rfl⟩ := (q.mem_support u).mp (hq.symm ▸ hu)
  rw [← hq, q.degreeIn_eq]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

lemma degree_three_adjacent {b : Finset V} (hb : QuadOn G b) (u : V) (hu : u ∈ b)
    (hdegree : degreeIn G u b = 3) (v : V) (hv : v ∈ b) (hne : u ≠ v) : G.Adj u v := by
  have hfull : degreeIn G u (b.erase u) = (b.erase u).card := by
    rw [degreeIn_erase_self G u hu, hdegree, card_erase_of_mem hu, hb.card]
  exact (degreeIn_eq_card_iff u (b.erase u)).mp hfull v (mem_erase.mpr ⟨hne.symm, hv⟩)

omit [DecidableRel G.Adj] in
lemma crossing_quad (q : Quadrilateral G) (z₁ z₂ : V)
    (hz₁ : z₁ ∉ q.support) (hz₂ : z₂ ∉ q.support)
    (h1 : G.Adj z₁ (q 1)) (h2 : G.Adj z₂ (q 2)) (h12 : G.Adj z₁ z₂) :
    QuadOn G {z₁, q 1, q 2, z₂} :=
  QuadOn.of_vertices
    (fun he ↦ hz₁ (he.symm ▸ (q.mem_support _).mpr ⟨2, rfl⟩))
    (fun he ↦ hz₂ (he ▸ (q.mem_support _).mpr ⟨1, rfl⟩))
    h1 (q.adjacent 1) h2.symm h12.symm

end Erdos577.TwoCore
