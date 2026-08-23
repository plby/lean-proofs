import ErdosProblems.Erdos1105.RootedPathEdges
import ErdosProblems.Erdos1105.SharpCoreCount

namespace Erdos1105

open SimpleGraph Finset

lemma rooted_two_no_chain {V : Type*} {G : SimpleGraph V} {u a b c : V}
    (hpath : ∀ w, ∀ p : G.Walk u w, p.IsPath → p.length ≤ 2)
    (hua : G.Adj u a) (hab : G.Adj a b) (hbc : G.Adj b c)
    (hbu : b ≠ u) (hcu : c ≠ u) (hca : c ≠ a) : False := by
  let p := Walk.cons hua (Walk.cons hab (Walk.cons hbc Walk.nil))
  have hp : p.IsPath := by
    apply Walk.IsPath.mk'
    simp only [p, Walk.support_cons, Walk.support_nil, List.nodup_cons, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, List.nodup_nil, not_or, not_false_eq_true, and_true]
    exact ⟨⟨hua.ne, hbu.symm, hcu.symm⟩, ⟨hab.ne, hca.symm⟩, hbc.ne⟩
  have h := hpath c p hp
  simp only [p, Walk.length_cons, Walk.length_nil] at h
  omega

/-- Away from the root and its neighbors, every vertex has degree at
most one when all root-starting paths have length at most two. -/
theorem rooted_two_outside_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Preconnected) (u : V)
    (hpath : ∀ w, ∀ p : G.Walk u w, p.IsPath → p.length ≤ 2)
    {v : V} (hvu : v ≠ u) (huv : ¬G.Adj u v) : G.degree v ≤ 1 := by
  classical
  obtain ⟨p, hp⟩ := hconn.exists_isPath u v
  have hlen := hpath v p hp
  cases p with
  | nil => exact (hvu rfl).elim
  | @cons _ a v hua q =>
    cases q with
    | nil => exact (huv hua).elim
    | @cons _ b v hab r =>
      cases r with
      | nil =>
        have hsub : G.neighborFinset v ⊆ {a} := by
          intro c hc
          have hbc : G.Adj v c := by simpa only [mem_neighborFinset] using hc
          apply mem_singleton.mpr
          by_contra hca
          have hcu : c ≠ u := fun h ↦ huv (h ▸ hbc.symm)
          exact rooted_two_no_chain hpath hua hab hbc hvu hcu hca
        simpa only [card_neighborFinset_eq_degree, card_singleton] using card_le_card hsub
      | cons h r => simp only [Walk.length_cons] at hlen; omega

theorem rooted_two_neighbor_cover {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Preconnected) (u : V)
    (hpath : ∀ w, ∀ p : G.Walk u w, p.IsPath → p.length ≤ 2) :
    ∀ x y, G.Adj x y → G.Adj u x ∨ G.Adj u y := by
  intro x y hxy
  by_cases hux : G.Adj u x
  · exact Or.inl hux
  by_cases hxu : x = u
  · exact Or.inr (hxu ▸ hxy)
  obtain ⟨p, hp⟩ := hconn.exists_isPath u x
  have hlen := hpath x p hp
  cases p with
  | nil => exact (hxu rfl).elim
  | @cons _ a x hua q =>
    cases q with
    | nil => exact (hux hua).elim
    | @cons _ b x hab r =>
      cases r with
      | nil =>
        by_cases hya : y = a
        · exact Or.inr (hya ▸ hua)
        have hyu : y ≠ u := fun h ↦ hux (h ▸ hxy.symm)
        exact (rooted_two_no_chain hpath hua hab hxy hxu hyu hya).elim
      | cons h r => simp only [Walk.length_cons] at hlen; omega

end Erdos1105

#print axioms Erdos1105.rooted_two_neighbor_cover
