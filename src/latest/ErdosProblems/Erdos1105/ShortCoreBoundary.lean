import ErdosProblems.Erdos1105.AlternatingExternal
import ErdosProblems.Erdos1105.ExternalIndependence

namespace Erdos1105

open SimpleGraph Finset

theorem low_core_initial_no_external {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {u x y : V} {d a : ℕ}
    (hG : NoLongCycle G (2 * d + 3)) (hu : G.IsUniversal u)
    (hconn : (G.induce {v | v ≠ u}).Preconnected)
    (p : G.Walk x y) (hp : IsLongestSetPath (vertexCore G d : Set V) p)
    (hd : 1 ≤ d) (hlen : 2 * d + 2 ≤ p.length) (ha : a ≤ p.length)
    (hbefore : ∀ j < a, ¬G.Adj y (p.getVert j)) :
    ∀ r < a, ∀ z, z ∉ p.support → ¬G.Adj (p.getVert r) z := by
  intro r hr z hz hadj
  have hzA : z ∉ (range a).image p.getVert := by
    rintro hzA
    obtain ⟨i, _, hi⟩ := mem_image.mp hzA
    exact hz (hi ▸ p.getVert_mem_support i)
  have hxz := (low_core_initial_full_twins hG hu hconn p hp hd hlen ha hbefore r hr z hzA).mp hadj
  exact hz (hp.left_neighbors z ((longest_low_core_full_neighbors hG hu hconn p hp hd hlen).1 z hxz) hxz)

theorem short_core_universal_attachment {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {u x y : V} {d a : ℕ}
    (hG : NoLongCycle G (2 * d + 3)) (hu : G.IsUniversal u)
    (p : G.Walk x y) (hp : p.IsPath)
    (hlen : p.length = 2 * d + 2) (ha : 1 ≤ a) (had : a ≤ d)
    (hbefore : ∀ j < a, ¬G.Adj y (p.getVert j))
    (hafter : ∀ j, p.length - a < j → j ≤ p.length → ¬G.Adj x (p.getVert j))
    (hmiddle : ∀ t, a ≤ t → t ≤ p.length - a →
      (G.Adj x (p.getVert t) ↔ Even (t - a)) ∧
      (G.Adj y (p.getVert t) ↔ Even (t - a))) :
    ∃ i < d + 2 - a, p.getVert (a + 2 * i) = u := by
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
  have hxt : G.Adj x (p.getVert t) := ht.symm ▸ (hu hxu.symm).symm
  have hyt : G.Adj y (p.getVert t) := ht.symm ▸ (hu hyu.symm).symm
  have hat : a ≤ t := by by_contra h; exact hbefore t (by omega) hyt
  have hta : t ≤ p.length - a := by by_contra h; exact hafter t (by omega) htL hxt
  obtain ⟨i, hi⟩ := (hmiddle t hat hta).1.mp hxt
  refine ⟨i, by omega, ?_⟩
  have heq : a + 2 * i = t := by omega
  rwa [heq]

theorem short_core_external_boundary {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {u x y : V} {d a : ℕ}
    (hG : NoLongCycle G (2 * d + 3)) (hu : G.IsUniversal u)
    (hconn : (G.induce {v | v ≠ u}).Preconnected)
    (p : G.Walk x y) (hp : IsLongestSetPath (vertexCore G d : Set V) p)
    (hlen : p.length = 2 * d + 2) (ha : 1 ≤ a) (had : a < d)
    (hbefore : ∀ j < a, ¬G.Adj y (p.getVert j))
    (hafter : ∀ j, p.length - a < j → j ≤ p.length → ¬G.Adj x (p.getVert j))
    (hmiddle : ∀ t, a ≤ t → t ≤ p.length - a →
      (G.Adj x (p.getVert t) ↔ Even (t - a)) ∧
      (G.Adj y (p.getVert t) ↔ Even (t - a))) :
    ∀ z, z ∉ p.support → ∀ v ∈ p.support, G.Adj z v →
      ∃ j < d + 2 - a, p.getVert (a + 2 * j) = v := by
  have hAlt := short_core_alternating_ends hG hu hconn p hp hlen ha had.le hbefore hafter hmiddle
  obtain ⟨i, hi, hiu⟩ := short_core_universal_attachment hG hu p hp.isPath hlen ha had.le
    hbefore hafter hmiddle
  have hbeforeR : ∀ j < a, ¬G.Adj x (p.reverse.getVert j) := by
    intro j hj
    rw [Walk.getVert_reverse]
    exact hafter _ (by omega) (by omega)
  intro z hz v hv hzv
  obtain ⟨s, hs, hsL⟩ := Walk.mem_support_iff_exists_getVert.mp hv
  have has : a ≤ s := by
    by_contra h
    exact low_core_initial_no_external hG hu hconn p hp (by omega) (by omega)
      (by omega) hbefore s (by omega) z hz (hs.symm ▸ hzv.symm)
  have hsa : s ≤ p.length - a := by
    by_contra h
    have h := low_core_initial_no_external hG hu hconn p.reverse hp.reverse (by omega)
      (by simpa only [Walk.length_reverse] using (show 2 * d + 2 ≤ p.length by omega))
      (show a ≤ p.reverse.length by rw [Walk.length_reverse]; omega) hbeforeR
      (p.length - s) (by omega) z (by simpa using hz)
    apply h
    simpa only [Walk.getVert_reverse, Nat.sub_sub_self hsL, hs] using hzv.symm
  rcases Nat.even_or_odd (s - a) with heven | hodd
  · obtain ⟨j, hj⟩ := heven
    refine ⟨j, by omega, ?_⟩
    have heq : a + 2 * j = s := by omega
    rwa [heq]
  · obtain ⟨t, ht⟩ := hodd
    have heq : a + 2 * t + 1 = s := by omega
    have hnone := hAlt.no_external_middle_edge hG had hi
      (show t < d + 1 - a by omega) (hiu.symm ▸ hu) hz
    exact (hnone (by simpa only [heq, hs] using hzv.symm)).elim

theorem short_core_outside_independent {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {u x y : V} {d a : ℕ}
    (hG : NoLongCycle G (2 * d + 3)) (hu : G.IsUniversal u)
    (hconn : (G.induce {v | v ≠ u}).Preconnected)
    (p : G.Walk x y) (hp : IsLongestSetPath (vertexCore G d : Set V) p)
    (hlen : p.length = 2 * d + 2) (ha : 1 ≤ a) (had : a < d)
    (hbefore : ∀ j < a, ¬G.Adj y (p.getVert j))
    (hafter : ∀ j, p.length - a < j → j ≤ p.length → ¬G.Adj x (p.getVert j))
    (hmiddle : ∀ t, a ≤ t → t ≤ p.length - a →
      (G.Adj x (p.getVert t) ↔ Even (t - a)) ∧
      (G.Adj y (p.getVert t) ↔ Even (t - a))) :
    ∀ z, z ∉ p.support → ∀ w, w ∉ p.support → ¬G.Adj z w := by
  have hAlt := short_core_alternating_ends hG hu hconn p hp hlen ha had.le hbefore hafter hmiddle
  obtain ⟨i, hi, hiu⟩ := short_core_universal_attachment hG hu p hp.isPath hlen ha had.le
    hbefore hafter hmiddle
  have hxu : x ≠ u := by
    intro h
    have heq : p.getVert 0 = p.getVert (a + 2 * i) := by simpa only [Walk.getVert_zero, hiu] using h
    have := hp.isPath.getVert_injOn (Nat.zero_le _) (show a + 2 * i ≤ p.length by omega) heq
    omega
  apply outside_independent_of_attachment_paths (S := {v | v ∈ p.support}) hG (by omega) hu hconn
    (hiu ▸ p.getVert_mem_support _) ⟨x, p.start_mem_support, hxu⟩
  intro z hz v hv hvu hzv
  obtain ⟨j, hj, hjv⟩ := short_core_external_boundary hG hu hconn p hp hlen ha had
    hbefore hafter hmiddle z hz v hv hzv
  have hij : i ≠ j := by
    intro h
    exact hvu (hjv.symm.trans ((congrArg (fun r ↦ p.getVert (a + 2 * r)) h.symm).trans hiu))
  obtain ⟨q, hq, hqlen, hsub⟩ := hAlt.path_C_C had hi hj hij
  refine ⟨q.copy hiu hjv, by simpa only [Walk.isPath_copy] using hq, ?_, ?_⟩
  · rw [Walk.length_copy, hqlen]
    omega
  · intro w hw
    exact hsub (by simpa only [Walk.support_copy] using hw)

end Erdos1105

#print axioms Erdos1105.short_core_external_boundary
#print axioms Erdos1105.short_core_outside_independent
