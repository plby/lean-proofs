import ErdosProblems.Erdos1105.ThreePetalRainbow
import ErdosProblems.Erdos1105.RootedTwoCounting

namespace Erdos1105

open SimpleGraph Finset

theorem threePetal_copy_of_disjoint_neighbor_edges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) {e₁ e₂ e₃ : Sym2 V}
    (h₁ : e₁ ∈ E767EGApi.edgesInside G (G.neighborFinset u))
    (h₂ : e₂ ∈ E767EGApi.edgesInside G (G.neighborFinset u))
    (h₃ : e₃ ∈ E767EGApi.edgesInside G (G.neighborFinset u))
    (h₁₂ : Disjoint e₁.toFinset e₂.toFinset)
    (h₁₃ : Disjoint e₁.toFinset e₃.toFinset)
    (h₂₃ : Disjoint e₂.toFinset e₃.toFinset) : Nonempty (threePetalGraph.Copy G) := by
  classical
  induction e₁ using Sym2.inductionOn with
  | _ a b =>
    induction e₂ using Sym2.inductionOn with
    | _ c d =>
      induction e₃ using Sym2.inductionOn with
      | _ e f =>
        have hpair (x y : V) (h : s(x, y) ∈ E767EGApi.edgesInside G (G.neighborFinset u)) :
            G.Adj x y ∧ G.Adj u x ∧ G.Adj u y := by
          refine ⟨mem_edgeFinset.mp (mem_filter.mp h).1, ?_, ?_⟩
          · have hm := (mem_filter.mp h).2 (by simp : x ∈ s(x, y).toFinset)
            simpa only [mem_neighborFinset] using hm
          · have hm := (mem_filter.mp h).2 (by simp : y ∈ s(x, y).toFinset)
            simpa only [mem_neighborFinset] using hm
        obtain ⟨hab, hua, hub⟩ := hpair a b h₁
        obtain ⟨hcd, huc, hud⟩ := hpair c d h₂
        obtain ⟨hef, hue, huf⟩ := hpair e f h₃
        simp only [Sym2.toFinset_mk_eq, disjoint_insert_left, disjoint_singleton_left,
          mem_insert, mem_singleton, not_or] at h₁₂ h₁₃ h₂₃
        have hnodup : [u, a, b, c, d, e, f].Nodup := by
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
            not_or, not_false_eq_true, and_true]
          exact ⟨⟨hua.ne, hub.ne, huc.ne, hud.ne, hue.ne, huf.ne⟩,
            ⟨hab.ne, h₁₂.1.1, h₁₂.1.2, h₁₃.1.1, h₁₃.1.2⟩,
            ⟨h₁₂.2.1, h₁₂.2.2, h₁₃.2.1, h₁₃.2.2⟩,
            ⟨hcd.ne, h₂₃.1.1, h₂₃.1.2⟩, ⟨h₂₃.2.1, h₂₃.2.2⟩, hef.ne⟩
        let φ : Fin 7 → V := fun i ↦ [u, a, b, c, d, e, f].get i
        refine ⟨{ toHom := ⟨φ, ?_⟩, injective' := List.nodup_iff_injective_get.mp hnodup }⟩
        intro i j hij
        fin_cases i <;> fin_cases j <;>
          simp only [Fin.mk_one, Fin.isValue, Fin.reduceFinMk, Fin.zero_eta] at hij ⊢
        all_goals first | assumption | exact hua.symm | exact hub.symm | exact huc.symm |
          exact hud.symm | exact hue.symm | exact huf.symm | exact hab.symm |
          exact hcd.symm | exact hef.symm |
          (exfalso; simp [threePetalGraph] at hij)

theorem threePetal_copy_of_rooted_two_high_edges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Preconnected) (u : V)
    (hpath : ∀ w, ∀ p : G.Walk u w, p.IsPath → p.length ≤ 2)
    (hhigh : Fintype.card V + 1 < G.edgeFinset.card) : Nonempty (threePetalGraph.Copy G) := by
  have hb := rooted_two_edge_count G hconn u hpath
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨u⟩
  have hthree : 2 < (E767EGApi.edgesInside G (G.neighborFinset u)).card := by omega
  obtain ⟨e₁, h₁, e₂, h₂, e₃, h₃, h₁₂, h₁₃, h₂₃⟩ := two_lt_card.mp hthree
  exact threePetal_copy_of_disjoint_neighbor_edges G u h₁ h₂ h₃
    (rooted_two_neighbor_edges_disjoint G u hpath h₁ h₂ h₁₂)
    (rooted_two_neighbor_edges_disjoint G u hpath h₁ h₃ h₁₃)
    (rooted_two_neighbor_edges_disjoint G u hpath h₂ h₃ h₂₃)

theorem rooted_two_rainbow_edge_bound {V C : Type*} [Fintype V] [DecidableEq V]
    (c : (⊤ : SimpleGraph V).edgeSet → C) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hR : Set.InjOn (extendColor c) G.edgeSet) (hconn : G.Preconnected) (u : V)
    (hpath : ∀ w, ∀ p : G.Walk u w, p.IsPath → p.length ≤ 2)
    (hfree : ∀ f : (pathGraph 6).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c) :
    G.edgeFinset.card ≤ Fintype.card V + 1 := by
  by_contra! hhigh
  obtain ⟨f⟩ := threePetal_copy_of_rooted_two_high_edges G hconn u hpath hhigh
  obtain ⟨p, hp⟩ := rainbow_path_six_of_threePetal_copy c hR f
  exact hfree p hp

end Erdos1105

#print axioms Erdos1105.rooted_two_rainbow_edge_bound
