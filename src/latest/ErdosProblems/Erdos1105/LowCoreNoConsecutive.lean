import ErdosProblems.Erdos1105.LowCoreInitialTwins
import ErdosProblems.Erdos1105.ThreePathCycle

namespace Erdos1105

open SimpleGraph Finset

/-- Beyond its initial clique, the start of a low-core path cannot
see consecutive vertices. The initial clique's last vertex supplies
the third chord of a forbidden spanning cycle. -/
theorem low_core_no_consecutive_start_neighbors {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {u x y : V} {d : ℕ}
    (hG : NoLongCycle G (2 * d + 3)) (hu : G.IsUniversal u)
    (hconn : (G.induce {v | v ≠ u}).Preconnected)
    (p : G.Walk x y) (hp : IsLongestSetPath (vertexCore G d : Set V) p)
    (hlen : 2 * d + 3 ≤ p.length + 1) {a : ℕ} (ha : 1 ≤ a)
    (haL : a ≤ p.length) (hya : G.Adj y (p.getVert a))
    (hbefore : ∀ j < a, ¬G.Adj y (p.getVert j))
    {t : ℕ} (hat : a ≤ t) (ht : t < p.length) :
    ¬(G.Adj x (p.getVert t) ∧ G.Adj x (p.getVert (t + 1))) := by
  rintro ⟨hxt, hxt'⟩
  have hfirst := (low_core_initial_segment_twins hG hu hconn p hp hlen haL hbefore
    (a - 1) (by omega) t hat ht.le).mpr hxt
  obtain ⟨v, s, hs, hslen⟩ := cycle_of_three_segment_chords p hp.isPath ha hat ht
    hfirst hya.symm hxt'.symm
  have := hG v s hs
  omega

theorem low_core_no_consecutive_end_neighbors {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {u x y : V} {d : ℕ}
    (hG : NoLongCycle G (2 * d + 3)) (hu : G.IsUniversal u)
    (hconn : (G.induce {v | v ≠ u}).Preconnected)
    (p : G.Walk x y) (hp : IsLongestSetPath (vertexCore G d : Set V) p)
    (hlen : 2 * d + 3 ≤ p.length + 1) {b : ℕ} (hb : b < p.length)
    (hxb : G.Adj x (p.getVert b))
    (hafter : ∀ j, b < j → j ≤ p.length → ¬G.Adj x (p.getVert j))
    {t : ℕ} (ht : t < b) :
    ¬(G.Adj y (p.getVert t) ∧ G.Adj y (p.getVert (t + 1))) := by
  have hfirst : G.Adj x (p.reverse.getVert (p.length - b)) := by
    rw [Walk.getVert_reverse, Nat.sub_sub_self hb.le]
    exact hxb
  have hbefore : ∀ j < p.length - b, ¬G.Adj x (p.reverse.getVert j) := by
    intro j hj
    rw [Walk.getVert_reverse]
    exact hafter _ (by omega) (Nat.sub_le _ _)
  have h := low_core_no_consecutive_start_neighbors hG hu hconn p.reverse hp.reverse
    (by simpa only [Walk.length_reverse] using hlen)
    (a := p.length - b) (by omega) (by simp only [Walk.length_reverse]; omega)
    hfirst hbefore (t := p.length - (t + 1)) (by omega)
    (by simp only [Walk.length_reverse]; omega)
  simp only [Walk.getVert_reverse] at h
  have heq₁ : p.length - (p.length - (t + 1)) = t + 1 := by omega
  have heq₂ : p.length - (p.length - (t + 1) + 1) = t := by omega
  rw [heq₁, heq₂] at h
  exact fun ht' ↦ h ⟨ht'.2, ht'.1⟩

end Erdos1105

#print axioms Erdos1105.low_core_no_consecutive_start_neighbors
