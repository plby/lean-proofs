import ErdosProblems.Erdos556.ClosingPaths
import ErdosProblems.Erdos556.PathBounds
import ErdosProblems.Erdos556.DeletionPaths

/-!
# Long cycles from a connecting reservoir and minimum degree
-/

namespace Erdos556

open SimpleGraph Finset

theorem exists_cycle_of_path_and_connection_succ {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (hp : p.IsPath) (hlen : 1 < p.length)
    (K : ℕ) (R : Finset V) (hoff : ∀ x ∈ p.support, x ∉ R)
    (hconn : ShortConnection G K u v R) :
    ∃ c : G.Walk u u, c.IsCycle ∧ p.length + 1 ≤ c.length := by
  obtain ⟨q, hq, _, hqR⟩ := hconn
  have huv : u ≠ v := by
    intro h
    have hz := (hp.nil_iff_eq.mpr h).length_eq_zero
    omega
  have hqpos : 0 < q.length := Walk.not_nil_iff_lt_length.mp (Walk.not_nil_of_ne huv)
  have hc : (p.append q.reverse).IsCycle := by
    apply isCycle_append_reverse_of_support_inter p q hp hq hlen
    intro x hxp hxq
    by_cases hxu : x = u
    · exact Or.inl hxu
    by_cases hxv : x = v
    · exact Or.inr hxv
    exact (hoff x hxp (hqR x hxq hxu hxv)).elim
  refine ⟨p.append q.reverse, hc, ?_⟩
  simp only [Walk.length_append, Walk.length_reverse]
  omega

theorem exists_long_cycle_of_reservoir {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (L b K : ℕ) (hL : 2 ≤ L)
    (R : Finset V) (hR : R.card ≤ b) (hconn : ConnectedAfterDeleting G b)
    (hdegree : ∀ v, L + R.card ≤ G.degree v)
    (hN : 2 * L + R.card ≤ Fintype.card V)
    (hres : ∀ u v, ShortConnection G K u v R) :
    ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ 2 * L ≤ c.length := by
  classical
  let U := (R : Set V)ᶜ
  have hRc : Fintype.card (R : Set V) = R.card := by
    calc
      Fintype.card (R : Set V) = (R : Set V).ncard := Nat.card_eq_fintype_card.symm
      _ = R.card := Set.ncard_coe_finset R
  have hUc : Fintype.card U = Fintype.card V - R.card := by
    simp only [U, Fintype.card_compl_set, hRc]
  have hUlarge : 2 * L ≤ Fintype.card U := by omega
  let : Nonempty U := Fintype.card_pos_iff.mp (by omega)
  have hc : (G.induce U).Connected := ⟨hconn R hR⟩
  have hdeg (v : U) : L ≤ (G.induce U).degree v := by
    have h := degree_le_induce_compl_degree_add_card G R v
    have hg := hdegree v.val
    change G.degree v.val ≤ (G.induce U).degree v + R.card at h
    omega
  obtain ⟨u, v, p, hp, hlen⟩ := exists_long_path_of_min_degree (G.induce U) hc L hL hdeg
  let f : G.induce U ↪g G := SimpleGraph.Embedding.induce U
  have hp' : (p.map f.toHom).IsPath := hp.map f.injective
  have hplen : 1 < (p.map f.toHom).length := by rw [Walk.length_map]; omega
  have hoff (x : V) (hx : x ∈ (p.map f.toHom).support) : x ∉ R := by
    rw [Walk.support_map, List.mem_map] at hx
    obtain ⟨y, _, hyx⟩ := hx
    exact hyx ▸ y.property
  obtain ⟨c, hcyc, hclen⟩ := exists_cycle_of_path_and_connection_succ (p.map f.toHom) hp' hplen
    K R hoff (hres (f u) (f v))
  refine ⟨f u, c, hcyc, ?_⟩
  rw [Walk.length_map] at hclen
  omega

#print axioms exists_long_cycle_of_reservoir

end Erdos556
