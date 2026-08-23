import ErdosProblems.Erdos1105.ShortCoreAlternation
import ErdosProblems.Erdos1105.LongCoreNeighborPattern
import ErdosProblems.Erdos1105.TwoAttachmentNeighbors

namespace Erdos1105

open SimpleGraph Finset

/-- The endpoint degree equality holds in the whole graph, not merely
inside the path: any external neighbor would extend a long cycle through
the universal vertex. -/
theorem short_low_core_neighbors_on_path {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {u x y : V} {d : ℕ}
    (hG : NoLongCycle G (2 * d + 3)) (hu : G.IsUniversal u)
    (hconn : (G.induce {v | v ≠ u}).Preconnected)
    (p : G.Walk x y) (hp : IsLongestSetPath (vertexCore G d : Set V) p)
    (hlen : p.length = 2 * d + 2) :
    ∀ z, G.Adj x z → z ∈ p.support := by
  classical
  obtain ⟨a, b, ha0, hab, hbL, habEven, hbefore, hafter, hmiddle⟩ :=
    short_low_core_middle_alternates hG hu hconn p hp hlen
  have huP := universal_mem_long_path hG (by omega) hu p hp.isPath (by omega)
  obtain ⟨t, ht, htL⟩ := Walk.mem_support_iff_exists_getVert.mp huP
  have htint := universal_index_internal hG (by omega) hu p hp.isPath (by omega) ht htL
  have hxu : x ≠ u := by
    intro heq
    have heq' : p.getVert 0 = p.getVert t := by simpa only [Walk.getVert_zero, ht] using heq
    have := hp.isPath.getVert_injOn (Nat.zero_le _) htL heq'
    omega
  have hyu : y ≠ u := by
    intro heq
    have heq' : p.getVert p.length = p.getVert t := by
      simpa only [Walk.getVert_length, ht] using heq
    have := hp.isPath.getVert_injOn (show p.length ≤ p.length from le_rfl) htL heq'
    omega
  have hxt : G.Adj x (p.getVert t) := ht.symm ▸ (hu hxu.symm).symm
  have hyt : G.Adj y (p.getVert t) := ht.symm ▸ (hu hyu.symm).symm
  have hat : a ≤ t := by by_contra h; exact hbefore t (by omega) hyt
  have htb : t ≤ b := by by_contra h; exact hafter t (by omega) htL hxt
  intro z hxz
  by_contra hz
  have huz : u ≠ z := fun h ↦ hz (h ▸ huP)
  by_cases hta : t = a
  · have hab₂ : a + 2 ≤ b := by obtain ⟨r, hr⟩ := habEven; omega
    have hxab : G.Adj x (p.getVert (a + 2)) := by
      apply (hmiddle _ (by omega) hab₂).1.mpr
      exact ⟨1, by omega⟩
    have hchord := (low_core_initial_segment_twins hG hu hconn p hp (by omega)
      (show a ≤ p.length by omega) hbefore (a - 1) (by omega)
      (a + 2) (by omega) (by omega)).mpr hxab
    obtain ⟨s, hs, hslen⟩ := cycle_of_external_early_attachment p hp.isPath ha0
      (by omega : a < a + 2) (by omega) hz hchord (hta ▸ hyt)
      (show G.Adj (p.getVert a) z by rw [← hta, ht]; exact hu huz) hxz.symm
    have := hG z s hs
    omega
  · have htaEven := (hmiddle t hat htb).2.mp hyt
    obtain ⟨r, hr⟩ := htaEven
    have hat₂ : a ≤ t - 2 := by omega
    have hyPrev : G.Adj y (p.getVert (t - 2)) := by
      apply (hmiddle _ hat₂ (by omega)).2.mpr
      exact ⟨r - 1, by omega⟩
    obtain ⟨s, hs, hslen⟩ := cycle_of_external_crossing p hp.isPath
      (by omega : t - 2 < t) htL hz hyPrev (ht.symm ▸ hu huz) hxz.symm
    have := hG z s hs
    omega

theorem longest_low_core_full_neighbors {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {u x y : V} {d : ℕ}
    (hG : NoLongCycle G (2 * d + 3)) (hu : G.IsUniversal u)
    (hconn : (G.induce {v | v ≠ u}).Preconnected)
    (p : G.Walk x y) (hp : IsLongestSetPath (vertexCore G d : Set V) p)
    (hd : 1 ≤ d) (hlen : 2 * d + 2 ≤ p.length) :
    (∀ z, G.Adj x z → z ∈ vertexCore G d) ∧
      (∀ z, G.Adj y z → z ∈ vertexCore G d) := by
  have hone {a b : V} (q : G.Walk a b)
      (hq : IsLongestSetPath (vertexCore G d : Set V) q) (hqlen : 2 * d + 2 ≤ q.length) :
      ∀ z, G.Adj a z → z ∈ vertexCore G d := by
    have hpath : ∀ z, G.Adj a z → z ∈ q.support := by
      by_cases hshort : q.length = 2 * d + 2
      · exact short_low_core_neighbors_on_path hG hu hconn q hq hshort
      · obtain ⟨hA, hB⟩ := long_low_core_neighbor_pattern hG hu hconn q hq (by omega)
        exact low_core_two_attachment_neighbors_on_path hG hu hconn q hq hd hqlen hA hB
    intro z hz
    exact (longest_low_core_path_neighbors hG hu hconn q hq (by omega)).1 z (hpath z hz) hz
  exact ⟨hone p hp hlen, hone p.reverse hp.reverse (by simpa only [Walk.length_reverse] using hlen)⟩

end Erdos1105

#print axioms Erdos1105.longest_low_core_full_neighbors
