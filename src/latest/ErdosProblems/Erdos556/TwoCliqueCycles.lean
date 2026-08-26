import ErdosProblems.Erdos556.CliquePaths
import ErdosProblems.Erdos556.ChordCycles

/-! Two disjoint edges between cliques give a cycle of a prescribed length. -/

namespace Erdos556

open SimpleGraph Finset

theorem exists_cycle_of_paths_and_cross_edges {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {a a' b b' : V}
    (A B : Finset V) (hdis : Disjoint A B) (hb' : b' ∈ B)
    (p : G.Walk a a') (q : G.Walk b' b) (hp : p.IsPath) (hq : q.IsPath)
    (hL : 2 ≤ p.length) (hpA : ∀ x ∈ p.support, x ∈ A) (hqB : ∀ x ∈ q.support, x ∈ B)
    (hab : G.Adj a b) (hab' : G.Adj a' b') :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = p.length + q.length + 2 := by
  have hbp : b' ∉ p.support := fun h => (Finset.disjoint_left.mp hdis (hpA b' h)) hb'
  have hp' : (p.concat hab').IsPath := hp.concat hbp hab'
  have hinter : ∀ x ∈ (p.concat hab').support, x ∈ q.support → x = b' := by
    intro x hxp hxq
    simp only [Walk.support_concat, List.mem_append, List.mem_singleton] at hxp
    rcases hxp with hxp | hxb
    · exact ((Finset.disjoint_left.mp hdis (hpA x hxp)) (hqB x hxq)).elim
    · exact hxb
  have hr := isPath_append_of_support_inter (p.concat hab') q hp' hq hinter
  obtain ⟨c, hc, hlen⟩ := exists_cycle_of_path_and_edge ((p.concat hab').append q) hr
    (by simp only [Walk.length_append, Walk.length_concat]; omega) hab
  refine ⟨a, c, hc, ?_⟩
  simp only [Walk.length_append, Walk.length_concat] at hlen
  omega

theorem exists_cycle_of_two_cliques_two_edges {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V) (hdis : Disjoint A B)
    (hA : G.IsClique (A : Set V)) (hB : G.IsClique (B : Set V))
    (L M : ℕ) (hL : 2 ≤ L) (hM : 2 ≤ M) (hAc : L + 1 ≤ A.card) (hBc : M + 1 ≤ B.card)
    (a a' b b' : V) (ha : a ∈ A) (ha' : a' ∈ A) (hb : b ∈ B) (hb' : b' ∈ B)
    (haa : a ≠ a') (hbb : b ≠ b') (hab : G.Adj a b) (hab' : G.Adj a' b') :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = L + M + 2 := by
  obtain ⟨p, hp, hplen, hpA⟩ := exists_path_in_clique G A hA L hL hAc a a' ha ha' haa
  obtain ⟨q, hq, hqlen, hqB⟩ := exists_path_in_clique G B hB M hM hBc b' b hb' hb hbb.symm
  obtain ⟨v, c, hc, hlen⟩ := exists_cycle_of_paths_and_cross_edges A B hdis hb' p q hp hq
    (by omega) hpA hqB hab hab'
  exact ⟨v, c, hc, by omega⟩

theorem two_clique_cross_edges_share_endpoint {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V) (hdis : Disjoint A B)
    (hA : G.IsClique (A : Set V)) (hB : G.IsClique (B : Set V))
    (r : ℕ) (hr : 3 ≤ r) (hAc : r + 1 ≤ A.card) (hBc : r + 1 ≤ B.card)
    (hno : ¬ cycleGraph (2 * r + 1) ⊑ G)
    (a a' b b' : V) (ha : a ∈ A) (ha' : a' ∈ A) (hb : b ∈ B) (hb' : b' ∈ B)
    (hab : G.Adj a b) (hab' : G.Adj a' b') : a = a' ∨ b = b' := by
  classical
  by_contra! hne
  obtain ⟨v, c, hc, hlen⟩ := exists_cycle_of_two_cliques_two_edges G A B hdis hA hB r (r - 1)
    (by omega) (by omega) hAc (by omega) a a' b b' ha ha' hb hb' hne.1 hne.2 hab hab'
  apply hno
  apply (cycleGraph_isContained_iff (by omega : 2 < 2 * r + 1)).mpr
  exact ⟨v, c, hc, by omega⟩

#print axioms two_clique_cross_edges_share_endpoint

end Erdos556
