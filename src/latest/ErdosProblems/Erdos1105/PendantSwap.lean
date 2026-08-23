import ErdosProblems.Erdos1105.PendantCounting
import ErdosProblems.Erdos1105.FullRepresentative

namespace Erdos1105

open SimpleGraph Finset

/-- Swapping in an edge between two pendant vertices preserves
connectivity unless it isolates another pendant vertex. It also creates
a new vertex of degree at least two outside the original core. -/
theorem pendant_swap_connected {V : Type*} (G : SimpleGraph V) (S : Finset V)
    {u x y : V} (huS : u ∈ S) (hx : x ∉ S) (hy : y ∉ S) (hxy : x ≠ y)
    (e : Sym2 V) (hpend : ∀ v ∉ S, ∀ w, G.Adj v w → w = u)
    (hnoiso : ∀ v, ∃ w, G.Adj v w)
    (hnoiso' : ∀ v, ∃ w, (swapRepresentative G e s(x, y)).Adj v w)
    (hcore : ((G.deleteEdges {e}).induce (S : Set V)).Preconnected) :
    (swapRepresentative G e s(x, y)).Preconnected ∧
      ∃ z ∉ S, ∃ a b, a ≠ b ∧ (swapRepresentative G e s(x, y)).Adj z a ∧
        (swapRepresentative G e s(x, y)).Adj z b := by
  let d : (⊤ : SimpleGraph V).edgeSet := ⟨s(x, y), hxy⟩
  let R := swapRepresentative G e d.val
  have hdel : G.deleteEdges {e} ≤ R := deleteEdges_le_swapRepresentative G e d
  have hnew : R.Adj x y := (mem_swapRepresentative G e d d.val).mpr (Or.inr rfl)
  have hxu : x ≠ u := fun h ↦ hx (h ▸ huS)
  have hyu : y ≠ u := fun h ↦ hy (h ▸ huS)
  have hstar (v : V) (hv : v ∉ S) : G.Adj v u := by
    obtain ⟨w, hw⟩ := hnoiso v
    have hwu := hpend v hv w hw
    rwa [hwu] at hw
  have hpairs : R.Reachable x u ∧ R.Reachable y u ∧
      ∃ z ∉ S, ∃ a b, a ≠ b ∧ R.Adj z a ∧ R.Adj z b := by
    by_cases hxe : s(x, u) = e
    · have hye : s(y, u) ≠ e := by
        intro heq
        apply hxy
        rcases Sym2.eq_iff.mp (hxe.trans heq.symm) with h | h
        · exact h.1
        · exact h.1.trans h.2
      have hyu' : R.Adj y u := hdel (deleteEdges_adj.mpr ⟨hstar y hy, hye⟩)
      exact ⟨hnew.reachable.trans hyu'.reachable, hyu'.reachable,
        y, hy, x, u, hxu, hnew.symm, hyu'⟩
    · have hxu' : R.Adj x u := hdel (deleteEdges_adj.mpr ⟨hstar x hx, hxe⟩)
      exact ⟨hxu'.reachable, hnew.symm.reachable.trans hxu'.reachable,
        x, hx, y, u, hyu, hnew, hxu'⟩
  let f : ((G.deleteEdges {e}).induce (S : Set V)) →g R :=
    { toFun := Subtype.val
      map_rel' := fun h ↦ hdel h }
  have hreach (v : V) : R.Reachable v u := by
    by_cases hv : v ∈ S
    · exact (hcore (⟨v, hv⟩ : (S : Set V)) ⟨u, huS⟩).map f
    · by_cases hvx : v = x
      · exact hvx ▸ hpairs.1
      by_cases hvy : v = y
      · exact hvy ▸ hpairs.2.1
      obtain ⟨w, hw⟩ := hnoiso' v
      have he : s(v, w) ∈ R.edgeSet := hw
      rcases (mem_swapRepresentative G e d s(v, w)).mp he with hold | hnew'
      · have hwu := hpend v hv w hold.1
        rw [hwu] at hw
        exact hw.reachable
      · rcases Sym2.eq_iff.mp hnew' with h | h
        · exact (hvx h.1).elim
        · exact (hvy h.1).elim
  exact ⟨fun a b ↦ (hreach a).trans (hreach b).symm, hpairs.2.2⟩

lemma two_le_degree_of_two_neighbors {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {v a b : V}
    (hab : a ≠ b) (ha : G.Adj v a) (hb : G.Adj v b) : 2 ≤ G.degree v := by
  classical
  have hsub : {a, b} ⊆ G.neighborFinset v := by
    intro w hw
    rcases mem_insert.mp hw with rfl | hw
    · simpa using ha
    · have hwb : w = b := mem_singleton.mp hw
      subst w
      simpa using hb
  simpa [hab] using card_le_card hsub

end Erdos1105

#print axioms Erdos1105.pendant_swap_connected
