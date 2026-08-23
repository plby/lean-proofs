import ErdosProblems.Erdos1105.ShortCoreStructure
import ErdosProblems.Erdos1105.FivePathJoin

namespace Erdos1105

open SimpleGraph Finset

/-- A path whose two end blocks are complete to the alternating
attachment positions in its middle. -/
structure AlternatingEnds {V : Type*} {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) (d a : ℕ) : Prop where
  isPath : p.IsPath
  length_eq : p.length = 2 * d + 2
  pos : 1 ≤ a
  le_core : a ≤ d
  left_join : ∀ i < a, ∀ j < d + 2 - a, G.Adj (p.getVert i) (p.getVert (a + 2 * j))
  right_join : ∀ i < a, ∀ j < d + 2 - a,
    G.Adj (p.getVert (p.length - i)) (p.getVert (a + 2 * j))

theorem AlternatingEnds.reverse {V : Type*} {G : SimpleGraph V} {x y : V}
    {p : G.Walk x y} {d a : ℕ} (hp : AlternatingEnds p d a) : AlternatingEnds p.reverse d a := by
  have hlen := hp.length_eq
  have hpos := hp.pos
  have had := hp.le_core
  refine ⟨hp.isPath.reverse, by simpa only [Walk.length_reverse] using hlen, hpos, had, ?_, ?_⟩
  · intro i hi j hj
    have hj' : d + 1 - a - j < d + 2 - a := by omega
    have heq : p.length - (a + 2 * j) = a + 2 * (d + 1 - a - j) := by omega
    simpa only [Walk.getVert_reverse, heq] using hp.right_join i hi _ hj'
  · intro i hi j hj
    have hj' : d + 1 - a - j < d + 2 - a := by omega
    have heq : p.length - (a + 2 * j) = a + 2 * (d + 1 - a - j) := by omega
    simpa only [Walk.length_reverse, Walk.getVert_reverse,
      Nat.sub_sub_self (show i ≤ p.length by omega), heq] using hp.left_join i hi _ hj'

theorem short_core_alternating_ends {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {u x y : V} {d a : ℕ}
    (hG : NoLongCycle G (2 * d + 3)) (hu : G.IsUniversal u)
    (hconn : (G.induce {v | v ≠ u}).Preconnected)
    (p : G.Walk x y) (hp : IsLongestSetPath (vertexCore G d : Set V) p)
    (hlen : p.length = 2 * d + 2) (ha : 1 ≤ a) (had : a ≤ d)
    (hbefore : ∀ j < a, ¬G.Adj y (p.getVert j))
    (hafter : ∀ j, p.length - a < j → j ≤ p.length → ¬G.Adj x (p.getVert j))
    (hmiddle : ∀ t, a ≤ t → t ≤ p.length - a →
      (G.Adj x (p.getVert t) ↔ Even (t - a)) ∧
      (G.Adj y (p.getVert t) ↔ Even (t - a))) : AlternatingEnds p d a := by
  have hbeforeR : ∀ j < a, ¬G.Adj x (p.reverse.getVert j) := by
    intro j hj
    rw [Walk.getVert_reverse]
    exact hafter _ (by omega) (by omega)
  refine ⟨hp.isPath, hlen, ha, had, ?_, ?_⟩
  · intro i hi j hj
    have hxC : G.Adj x (p.getVert (a + 2 * j)) := by
      apply (hmiddle _ (by omega) (by omega)).1.mpr
      exact ⟨j, by omega⟩
    exact (low_core_initial_segment_twins hG hu hconn p hp (by omega)
      (show a ≤ p.length by omega) hbefore i hi _ (by omega) (by omega)).mpr hxC
  · intro i hi j hj
    have hyC : G.Adj y (p.getVert (a + 2 * j)) := by
      apply (hmiddle _ (by omega) (by omega)).2.mpr
      exact ⟨j, by omega⟩
    have h := low_core_initial_segment_twins hG hu hconn p.reverse hp.reverse
      (by simpa only [Walk.length_reverse] using (show 2 * d + 3 ≤ p.length + 1 by omega))
      (show a ≤ p.reverse.length by rw [Walk.length_reverse]; omega) hbeforeR i hi
      (p.length - (a + 2 * j)) (by omega)
      (by rw [Walk.length_reverse]; omega)
    simpa only [Walk.getVert_reverse, Nat.sub_sub_self (show a + 2 * j ≤ p.length by omega)]
      using h.mpr (by simpa only [Walk.getVert_reverse,
        Nat.sub_sub_self (show a + 2 * j ≤ p.length by omega)] using hyC)

end Erdos1105

#print axioms Erdos1105.AlternatingEnds.reverse
#print axioms Erdos1105.short_core_alternating_ends
