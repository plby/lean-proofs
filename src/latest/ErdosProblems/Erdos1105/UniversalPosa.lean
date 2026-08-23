import ErdosProblems.Erdos1105.UniversalPath
import ErdosProblems.Erdos1105.PathNeighborCounts
import ErdosProblems.Erdos1105.PathEar
import ErdosProblems.Erdos1105.EarCycle

namespace Erdos1105

open SimpleGraph Finset

/-- The Pósa--Kopylov endpoint-degree lemma for a cone over a connected
graph. This is the version needed to transfer path extremal questions to
cycle extremal questions by adjoining a universal vertex. -/
theorem universal_posa_degree_bound {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {x y u : V} {k : ℕ}
    (hG : NoLongCycle G k) (hk : 3 ≤ k) (hu : G.IsUniversal u)
    (hconn : (G.induce {v | v ≠ u}).Preconnected)
    (p : G.Walk x y) (hp : p.IsPath) (hlen : k ≤ p.length + 1) :
    degreeWithin G p.support.toFinset x + degreeWithin G p.support.toFinset y < k := by
  classical
  rw [← startNeighborIndices_card p hp, ← endNeighborIndices_card p hp]
  by_cases hcross : ∃ i ∈ endNeighborIndices p, ∃ j ∈ startNeighborIndices p, i ≤ j
  · exact neighbor_indices_card_lt_of_crossing hG hk p hp hlen hcross
  · by_contra hnot
    have hsum : k ≤ (startNeighborIndices p).card + (endNeighborIndices p).card := by omega
    obtain ⟨t, ht, htL⟩ := Walk.mem_support_iff_exists_getVert.mp
      (universal_mem_long_path hG hk hu p hp hlen)
    have htint := universal_index_internal hG hk hu p hp hlen ht htL
    have hnotu (r : ℕ) (hr : r ≤ p.length) (hrt : r ≠ t) : p.getVert r ≠ u := by
      intro hru
      exact hrt (hp.getVert_injOn hr htL (hru.trans ht.symm))
    have hxu : x ≠ u := by simpa using hnotu 0 (by omega) (by omega)
    have hyu : y ≠ u := by simpa using hnotu p.length le_rfl (by omega)
    have havoid : ∃ r : G.Walk x y, r.IsPath ∧ u ∉ r.support := by
      obtain ⟨r, hr⟩ := hconn.exists_isPath ⟨x, hxu⟩ ⟨y, hyu⟩
      let f : G.induce {v | v ≠ u} →g G :=
        { toFun := Subtype.val, map_rel' := fun h ↦ h }
      refine ⟨r.map f, hr.map Subtype.val_injective, ?_⟩
      intro humem
      rw [Walk.support_map] at humem
      obtain ⟨v, _, hv⟩ := List.mem_map.mp humem
      exact v.property hv
    obtain ⟨i, j, hit, htj, hjL, q, hq, _, hmeet⟩ := exists_ear_across_path_vertex p
      htint.1 htint.2 (by simpa only [ht] using havoid)
    have hord := noncrossing_neighbors_at_universal hG hk hu p hp hlen ht htL hcross
    have htA : t - 1 ∈ startNeighborIndices p := by
      apply mem_filter.mpr
      refine ⟨mem_range.mpr (by omega), ?_⟩
      rw [Nat.sub_add_cancel htint.1, ht]
      exact (hu hxu.symm).symm
    have htB : t ∈ endNeighborIndices p := by
      apply mem_filter.mpr
      refine ⟨mem_range.mpr htint.2, ?_⟩
      rw [ht]
      exact (hu hyu.symm).symm
    obtain ⟨a, b, hia, hat, htb, hbj, haA, hbB, hcard⟩ := exists_noncrossing_gap_bound
      (startNeighborIndices p) (endNeighborIndices p) (filter_subset _ _) (filter_subset _ _)
      hit htj hjL hord.1 hord.2 htA htB
    have hxa : G.Adj x (p.getVert a) := by
      have h := (mem_filter.mp haA).2
      rwa [Nat.sub_add_cancel (by omega : 1 ≤ a)] at h
    have hyb : G.Adj y (p.getVert b) := (mem_filter.mp hbB).2
    obtain ⟨v, c, hc, hclen⟩ := cycle_of_ear_and_middle_chords p hp hia (by omega) hbj hjL
      q hq hmeet hxa hyb (by omega)
    have h := hG v c hc
    rw [hclen] at h
    omega

end Erdos1105

#print axioms Erdos1105.universal_posa_degree_bound
