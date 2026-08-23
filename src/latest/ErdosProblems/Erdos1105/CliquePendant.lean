import ErdosProblems.Erdos1105.CliquePaths
import ErdosProblems.Erdos1105.PathFree
import ErdosProblems.Erdos1105.SetPath
import ErdosProblems.Erdos1105.PathCycleSplice

namespace Erdos1105

open SimpleGraph Finset

theorem path_to_large_clique_length_le_one {V : Type*} (G : SimpleGraph V)
    {S : Finset V} (hS : G.IsClique (S : Set V)) (hcard : 3 ≤ S.card)
    (hfree : ¬pathGraph (S.card + 2) ⊑ G) {x v : V} (hv : v ∈ S)
    (p : G.Walk x v) (hp : p.IsPath)
    (hmeet : ∀ w ∈ p.support, w ∈ S → w = v) : p.length ≤ 1 := by
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (show 1 < S.card by omega)
  have hu : ∃ u ∈ S, v ≠ u := by
    by_cases hva : v = a
    · exact ⟨b, hb, fun h ↦ hab (hva.symm.trans h)⟩
    · exact ⟨a, ha, hva⟩
  obtain ⟨u, hu, hvu⟩ := hu
  obtain ⟨q, hq, hqlen, hqsupp⟩ := clique_spanning_path G hS hcard hv hu hvu
  have hpq := isPath_append_of_inter_eq_end hp hq
    (fun w hwp hwq ↦ hmeet w hwp ((hqsupp w).mp hwq))
  have hlen := path_length_lt_of_path_free hfree (p.append q) hpq
  rw [Walk.length_append] at hlen
  omega

theorem outside_large_clique_has_neighbor {V : Type*} (G : SimpleGraph V)
    (hconn : G.Preconnected) {S : Finset V} (hS : G.IsClique (S : Set V))
    (hcard : 3 ≤ S.card) (hfree : ¬pathGraph (S.card + 2) ⊑ G)
    {x : V} (hx : x ∉ S) : ∃ v ∈ S, G.Adj x v := by
  classical
  obtain ⟨v, hv⟩ := card_pos.mp (show 0 < S.card by omega)
  obtain ⟨p, hp⟩ := (hconn x v).exists_isPath
  obtain ⟨a, ha, b, hb, q, hq, _, _, hmeet⟩ := exists_set_path_within G {x}
    (S : Set V) Set.univ ⟨x, rfl, v, hv, p, hp, by simp⟩
  have hax : a = x := ha
  subst a
  have hlen := path_to_large_clique_length_le_one G hS hcard hfree hb q hq hmeet
  have hpos : 0 < q.length := by
    by_contra! h
    have heq : x = b := q.eq_of_length_eq_zero (by omega)
    exact hx (heq ▸ hb)
  exact ⟨b, hb, Walk.adj_of_length_eq_one (by omega : q.length = 1)⟩

theorem outside_large_clique_no_edge {V : Type*} (G : SimpleGraph V)
    (hconn : G.Preconnected) {S : Finset V} (hS : G.IsClique (S : Set V))
    (hcard : 3 ≤ S.card) (hfree : ¬pathGraph (S.card + 2) ⊑ G)
    {x y : V} (hx : x ∉ S) (hy : y ∉ S) : ¬G.Adj x y := by
  classical
  intro hxy
  obtain ⟨v, hv, hyv⟩ := outside_large_clique_has_neighbor G hconn hS hcard hfree hy
  let p := Walk.cons hxy (Walk.cons hyv Walk.nil)
  have hp : p.IsPath := by
    have hxv : x ≠ v := fun h ↦ hx (h ▸ hv)
    simp [p, Walk.cons_isPath_iff, hxy.ne, hyv.ne, hxv]
  have hmeet : ∀ w ∈ p.support, w ∈ S → w = v := by
    intro w hw hwS
    simp only [p, Walk.support_cons, Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact (hx hwS).elim
    · exact (hy hwS).elim
    · rfl
  have hlen := path_to_large_clique_length_le_one G hS hcard hfree hv p hp hmeet
  simp [p] at hlen

theorem outside_large_clique_neighbors_eq {V : Type*} (G : SimpleGraph V)
    {S : Finset V} (hS : G.IsClique (S : Set V)) (hcard : 3 ≤ S.card)
    (hfree : ¬pathGraph (S.card + 2) ⊑ G)
    {x y a b : V} (hx : x ∉ S) (hy : y ∉ S) (hxy : x ≠ y)
    (ha : a ∈ S) (hb : b ∈ S) (hxa : G.Adj x a) (hyb : G.Adj y b) : a = b := by
  classical
  by_contra hab
  obtain ⟨p, hp, hlen, hsupp⟩ := clique_spanning_path G hS hcard ha hb hab
  have hxnot : x ∉ p.support := fun h ↦ hx ((hsupp x).mp h)
  let q := Walk.cons hxa p
  have hq : q.IsPath := (Walk.cons_isPath_iff _ _).mpr ⟨hp, hxnot⟩
  have hynot : y ∉ q.support := by
    simp only [q, Walk.support_cons, List.mem_cons, not_or]
    exact ⟨hxy.symm, fun h ↦ hy ((hsupp y).mp h)⟩
  have h := path_length_lt_of_path_free hfree (q.concat hyb.symm) (hq.concat hynot hyb.symm)
  simp only [q, Walk.length_concat, Walk.length_cons] at h
  omega

/-- In a connected `P_(r+2)`-free graph, a clique of order `r` leaves only
pendant vertices, all attached to the same clique vertex. -/
theorem large_clique_pendant_structure {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hconn : G.Preconnected) {S : Finset V} (hS : G.IsClique (S : Set V))
    (hcard : 3 ≤ S.card) (hn : S.card + 2 ≤ Fintype.card V)
    (hfree : ¬pathGraph (S.card + 2) ⊑ G) :
    ∃ u ∈ S, ∀ x ∉ S, ∀ y, G.Adj x y → y = u := by
  classical
  have houtcard : 1 < Sᶜ.card := by rw [card_compl]; omega
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy⟩ := one_lt_card.mp houtcard
  have hx₀ : x₀ ∉ S := mem_compl.mp hx₀
  have hy₀ : y₀ ∉ S := mem_compl.mp hy₀
  obtain ⟨u, hu, hxu⟩ := outside_large_clique_has_neighbor G hconn hS hcard hfree hx₀
  obtain ⟨v, hv, hyv⟩ := outside_large_clique_has_neighbor G hconn hS hcard hfree hy₀
  have huv := outside_large_clique_neighbors_eq G hS hcard hfree hx₀ hy₀ hxy hu hv hxu hyv
  refine ⟨u, hu, ?_⟩
  intro x hx y hxy'
  have hy : y ∈ S := by
    by_contra hy
    exact outside_large_clique_no_edge G hconn hS hcard hfree hx hy hxy'
  by_cases hxx : x = x₀
  · subst x
    exact (outside_large_clique_neighbors_eq G hS hcard hfree hx₀ hy₀ hxy hy hv hxy' hyv).trans
      huv.symm
  · exact outside_large_clique_neighbors_eq G hS hcard hfree hx hx₀ hxx hy hu hxy' hxu

end Erdos1105

#print axioms Erdos1105.large_clique_pendant_structure
