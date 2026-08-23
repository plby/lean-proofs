import ErdosProblems.Erdos1105.ExternalEndpointCycle
import ErdosProblems.Erdos1105.LowCoreInitialTwins

namespace Erdos1105

open SimpleGraph Finset

theorem universal_at_two_attachments {V : Type*} {G : SimpleGraph V} {u x y : V} {d : ℕ}
    (hG : NoLongCycle G (2 * d + 3)) (hu : G.IsUniversal u)
    (p : G.Walk x y) (hp : p.IsPath) (hlen : 2 * d + 2 ≤ p.length)
    (hA : startNeighborIndices p = insert (p.length - d - 1) (range d))
    (hB : endNeighborIndices p = insert d (Ico (p.length - d) p.length)) :
    u = p.getVert d ∨ u = p.getVert (p.length - d) := by
  classical
  have huP := universal_mem_long_path hG (by omega) hu p hp (by omega)
  obtain ⟨t, ht, htL⟩ := Walk.mem_support_iff_exists_getVert.mp huP
  have htint := universal_index_internal hG (by omega) hu p hp (by omega) ht htL
  have hxu : x ≠ u := by
    intro heq
    have heq' : p.getVert 0 = p.getVert t := by simpa only [Walk.getVert_zero, ht] using heq
    have := hp.getVert_injOn (Nat.zero_le _) htL heq'
    omega
  have hyu : y ≠ u := by
    intro heq
    have heq' : p.getVert p.length = p.getVert t := by
      simpa only [Walk.getVert_length, ht] using heq
    have := hp.getVert_injOn (show p.length ≤ p.length from le_rfl) htL heq'
    omega
  have htA : t - 1 ∈ startNeighborIndices p := by
    apply mem_filter.mpr
    refine ⟨mem_range.mpr (by omega), ?_⟩
    rw [Nat.sub_add_cancel htint.1, ht]
    exact (hu hxu.symm).symm
  have htB : t ∈ endNeighborIndices p := mem_filter.mpr
    ⟨mem_range.mpr htint.2, by rw [ht]; exact (hu hyu.symm).symm⟩
  rw [hA] at htA
  rw [hB] at htB
  simp only [mem_insert, mem_range, mem_Ico] at htA htB
  have : t = d ∨ t = p.length - d := by omega
  rcases this with rfl | rfl
  · exact Or.inl ht.symm
  · exact Or.inr ht.symm

theorem low_core_two_attachment_neighbors_on_path {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {u x y : V} {d : ℕ}
    (hG : NoLongCycle G (2 * d + 3)) (hu : G.IsUniversal u)
    (hconn : (G.induce {v | v ≠ u}).Preconnected)
    (p : G.Walk x y) (hp : IsLongestSetPath (vertexCore G d : Set V) p)
    (hd : 1 ≤ d) (hlen : 2 * d + 2 ≤ p.length)
    (hA : startNeighborIndices p = insert (p.length - d - 1) (range d))
    (hB : endNeighborIndices p = insert d (Ico (p.length - d) p.length)) :
    ∀ z, G.Adj x z → z ∈ p.support := by
  classical
  have hbefore : ∀ j < d, ¬G.Adj y (p.getVert j) := by
    intro j hj hadj
    have hm : j ∈ endNeighborIndices p := mem_filter.mpr ⟨mem_range.mpr (by omega), hadj⟩
    rw [hB] at hm
    simp only [mem_insert, mem_Ico] at hm
    omega
  have hxb : G.Adj x (p.getVert (p.length - d)) := by
    have hm : p.length - d - 1 ∈ startNeighborIndices p := hA ▸ mem_insert_self _ _
    have := (mem_filter.mp hm).2
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ p.length - d)] using this
  have hchord := (low_core_initial_segment_twins hG hu hconn p hp (by omega)
    (show d ≤ p.length by omega) hbefore (d - 1) (by omega)
    (p.length - d) (by omega) (by omega)).mpr hxb
  have hya : G.Adj y (p.getVert d) := by
    have hm : d ∈ endNeighborIndices p := hB ▸ mem_insert_self _ _
    exact (mem_filter.mp hm).2
  exact endpoint_neighbors_on_path_of_two_attachments hG hu p hp.isPath hd
    (by omega) (by omega) (by omega)
    (universal_at_two_attachments hG hu p hp.isPath hlen hA hB) hya hchord

/-- In the two-attachment case, the initial clique has no neighbors
outside the clique and its two attachment vertices. -/
theorem low_core_two_attachment_initial_closed {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {u x y : V} {d : ℕ}
    (hG : NoLongCycle G (2 * d + 3)) (hu : G.IsUniversal u)
    (hconn : (G.induce {v | v ≠ u}).Preconnected)
    (p : G.Walk x y) (hp : IsLongestSetPath (vertexCore G d : Set V) p)
    (hd : 1 ≤ d) (hlen : 2 * d + 2 ≤ p.length)
    (hA : startNeighborIndices p = insert (p.length - d - 1) (range d))
    (hB : endNeighborIndices p = insert d (Ico (p.length - d) p.length)) :
    ∀ r < d, ∀ z, G.Adj (p.getVert r) z →
      z ∈ (range d).image p.getVert ∨ z = p.getVert d ∨ z = p.getVert (p.length - d) := by
  classical
  have hlong : 2 * d + 3 ≤ p.length + 1 := by omega
  have hbefore : ∀ j < d, ¬G.Adj y (p.getVert j) := by
    intro j hj hadj
    have hm : j ∈ endNeighborIndices p := mem_filter.mpr ⟨mem_range.mpr (by omega), hadj⟩
    rw [hB] at hm
    simp only [mem_insert, mem_Ico] at hm
    omega
  have hstart := low_core_start_neighbors_before hG hu hconn p hp hlong
    (show d ≤ p.length by omega) hbefore
  have hcore := (longest_low_core_path_neighbors hG hu hconn p hp hlong).1
  intro r hr z hrz
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
  have hqB : endNeighborIndices q = endNeighborIndices p :=
    posaRotateStart_end_indices p hrL (hstart r hr) (fun j hj ↦ hbefore j (by omega))
  have hqA := low_core_start_indices_unique hG hu hconn p hp q hq hlong hqlen hqB
  have hzq := low_core_two_attachment_neighbors_on_path hG hu hconn q hq hd
    (by omega) (by simpa only [hqlen] using hqA.trans hA)
    (by simpa only [hqlen] using hqB.trans hB) z hrz
  have hzP : z ∈ p.support := (posaRotateStart_mem_support p hrL (hstart r hr)).mp hzq
  obtain ⟨s, hs, hsL⟩ := Walk.mem_support_iff_exists_getVert.mp hzP
  by_cases hsd : s < d
  · exact Or.inl (mem_image.mpr ⟨s, mem_range.mpr hsd, hs⟩)
  · have hxs : G.Adj x (p.getVert s) :=
      (low_core_initial_segment_twins hG hu hconn p hp hlong
        (show d ≤ p.length by omega) hbefore r hr s (by omega) hsL).mp (hs.symm ▸ hrz)
    have hm : s - 1 ∈ startNeighborIndices p := by
      apply mem_filter.mpr
      refine ⟨mem_range.mpr (by omega), ?_⟩
      rwa [Nat.sub_add_cancel (by omega : 1 ≤ s)]
    rw [hA] at hm
    simp only [mem_insert, mem_range] at hm
    rcases (show s = d ∨ s = p.length - d by omega) with h | h
    · exact Or.inr (Or.inl (hs.symm.trans (congrArg p.getVert h)))
    · exact Or.inr (Or.inr (hs.symm.trans (congrArg p.getVert h)))

end Erdos1105

#print axioms Erdos1105.low_core_two_attachment_initial_closed
