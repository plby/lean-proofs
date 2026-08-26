import ErdosProblems.Erdos556.TwoCliqueCycles

/-! Joining two disjoint paths through a cross edge and an outside vertex. -/

namespace Erdos556

open SimpleGraph Finset

theorem exists_cycle_of_two_paths_and_outside_vertex {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {a a' b b' x : V}
    (X Y : Finset V) (hdis : Disjoint X Y) (hxX : x ∉ X) (hxY : x ∉ Y) (hb' : b' ∈ Y)
    (p : G.Walk a a') (q : G.Walk b' b) (hp : p.IsPath) (hq : q.IsPath) (hL : 1 ≤ p.length)
    (hpX : ∀ z ∈ p.support, z ∈ X) (hqY : ∀ z ∈ q.support, z ∈ Y)
    (hxa : G.Adj x a) (hxb : G.Adj x b) (hab : G.Adj a' b') :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = p.length + q.length + 3 := by
  have hxP : x ∉ p.support := fun h => hxX (hpX x h)
  have hp' : (Walk.cons hxa p).IsPath := (Walk.cons_isPath_iff _ _).mpr ⟨hp, hxP⟩
  have hdis' : Disjoint (insert x X) Y := by
    apply Finset.disjoint_left.mpr
    intro z hz hzY
    rcases mem_insert.mp hz with hzx | hzX
    · exact hxY (hzx ▸ hzY)
    · exact (Finset.disjoint_left.mp hdis hzX) hzY
  have hp'X : ∀ z ∈ (Walk.cons hxa p).support, z ∈ insert x X := by
    intro z hz
    rw [Walk.support_cons, List.mem_cons] at hz
    rcases hz with hz | hz
    · exact mem_insert.mpr (Or.inl hz)
    · exact mem_insert_of_mem (hpX z hz)
  obtain ⟨v, c, hc, hlen⟩ := exists_cycle_of_paths_and_cross_edges (insert x X) Y hdis' hb'
    (Walk.cons hxa p) q hp' hq (by rw [Walk.length_cons]; omega) hp'X hqY hxb hab
  exact ⟨v, c, hc, by rw [Walk.length_cons] at hlen; omega⟩

#print axioms exists_cycle_of_two_paths_and_outside_vertex

end Erdos556
