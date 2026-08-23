import ErdosProblems.Erdos1105.ShortCoreFullDegree
import ErdosProblems.Erdos1105.MiddleChordCycle

namespace Erdos1105

open SimpleGraph Finset

/-- The initial clique twins remain twins away from that clique in the
whole graph, not just along the selected maximal path. -/
theorem low_core_initial_full_twins {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {u x y : V} {d a : ℕ}
    (hG : NoLongCycle G (2 * d + 3)) (hu : G.IsUniversal u)
    (hconn : (G.induce {v | v ≠ u}).Preconnected)
    (p : G.Walk x y) (hp : IsLongestSetPath (vertexCore G d : Set V) p)
    (hd : 1 ≤ d) (hlen : 2 * d + 2 ≤ p.length) (ha : a ≤ p.length)
    (hbefore : ∀ j < a, ¬G.Adj y (p.getVert j)) :
    ∀ r < a, ∀ z, z ∉ (range a).image p.getVert →
      (G.Adj (p.getVert r) z ↔ G.Adj x z) := by
  classical
  have hlong : 2 * d + 3 ≤ p.length + 1 := by omega
  have hstart := low_core_start_neighbors_before hG hu hconn p hp hlong ha hbefore
  have hcore := (longest_low_core_path_neighbors hG hu hconn p hp hlong).1
  intro r hr z hz
  have hrL : r < p.length := by omega
  have hrmem : p.getVert r ∈ vertexCore G d := by
    by_cases hr0 : r = 0
    · simpa only [hr0, Walk.getVert_zero, Finset.mem_coe] using hp.left_mem
    · apply hcore _ (p.getVert_mem_support r)
      have h := hstart (r - 1) (by omega)
      rwa [Nat.sub_add_cancel (by omega : 1 ≤ r)] at h
  let q := posaRotateStart p r (hstart r hr)
  have hq := hp.posaRotateStart hrL (hstart r hr) hrmem
  have hqlen : q.length = p.length := posaRotateStart_length p hrL (hstart r hr)
  have honpath : (G.Adj (p.getVert r) z ∨ G.Adj x z) → z ∈ p.support := by
    intro h
    rcases h with h | h
    · have hzcore := (longest_low_core_full_neighbors hG hu hconn q hq hd (by omega)).1 z h
      have hzq := hq.left_neighbors z hzcore h
      exact (posaRotateStart_mem_support p hrL (hstart r hr)).mp hzq
    · exact hp.left_neighbors z ((longest_low_core_full_neighbors hG hu hconn p hp hd hlen).1 z h) h
  have hiff (hzP : z ∈ p.support) : G.Adj (p.getVert r) z ↔ G.Adj x z := by
    obtain ⟨s, hs, hsL⟩ := Walk.mem_support_iff_exists_getVert.mp hzP
    have has : a ≤ s := by
      by_contra h
      exact hz (mem_image.mpr ⟨s, mem_range.mpr (by omega), hs⟩)
    simpa only [hs] using low_core_initial_segment_twins hG hu hconn p hp hlong ha hbefore r hr s has hsL
  exact ⟨fun h ↦ (hiff (honpath (Or.inl h))).mp h,
    fun h ↦ (hiff (honpath (Or.inr h))).mpr h⟩

theorem short_core_middle_independent {V : Type*} {G : SimpleGraph V} {x y : V} {d a : ℕ}
    (hG : NoLongCycle G (2 * d + 3)) (p : G.Walk x y) (hp : p.IsPath)
    (hlen : p.length = 2 * d + 2) (ha : 1 ≤ a) (had : a ≤ d)
    (hmiddle : ∀ t, a ≤ t → t ≤ p.length - a →
      (G.Adj x (p.getVert t) ↔ Even (t - a)) ∧
      (G.Adj y (p.getVert t) ↔ Even (t - a))) :
    ∀ i < d + 1 - a, ∀ j < d + 1 - a,
      ¬G.Adj (p.getVert (a + 2 * i + 1)) (p.getVert (a + 2 * j + 1)) := by
  have hone (i j : ℕ) (hi : i < d + 1 - a) (hj : j < d + 1 - a) (hij : i < j) :
      ¬G.Adj (p.getVert (a + 2 * i + 1)) (p.getVert (a + 2 * j + 1)) := by
    intro h
    have hyi : G.Adj y (p.getVert (a + 2 * i + 1 - 1)) := by
      apply (hmiddle _ (by omega) (by omega)).2.mpr
      exact ⟨i, by omega⟩
    have hxj : G.Adj x (p.getVert (a + 2 * j + 1 - 1)) := by
      apply (hmiddle _ (by omega) (by omega)).1.mpr
      exact ⟨j, by omega⟩
    obtain ⟨v, q, hq, hqLen⟩ := cycle_of_middle_chord p hp
      (by omega : 1 ≤ a + 2 * i + 1) (by omega) (by omega) hyi hxj h
    have := hG v q hq
    omega
  intro i hi j hj h
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · exact hone i j hi hj hlt h
  · exact h.ne rfl
  · exact hone j i hj hi hgt h.symm

end Erdos1105

#print axioms Erdos1105.low_core_initial_full_twins
#print axioms Erdos1105.short_core_middle_independent
