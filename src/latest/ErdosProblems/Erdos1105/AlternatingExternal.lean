import ErdosProblems.Erdos1105.AlternatingCDInitial

namespace Erdos1105

open SimpleGraph

theorem AlternatingEnds.path_C_C {V : Type*} {G : SimpleGraph V} {x y : V}
    {p : G.Walk x y} {d a i j : ℕ} (hp : AlternatingEnds p d a)
    (had : a < d) (hi : i < d + 2 - a) (hj : j < d + 2 - a) (hij : i ≠ j) :
    ∃ q : G.Walk (p.getVert (a + 2 * i)) (p.getVert (a + 2 * j)),
      q.IsPath ∧ q.length = 2 * d ∧ q.support ⊆ p.support := by
  have ha := hp.pos
  have hone {r s : ℕ} (hrs : r < s) (hs : s < d + 2 - a) :
      ∃ q : G.Walk (p.getVert (a + 2 * r)) (p.getVert (a + 2 * s)),
        q.IsPath ∧ q.length = 2 * d ∧ q.support ⊆ p.support := by
    have hs' : s - 1 < d + 1 - a := by omega
    have heq : s - 1 + 1 = s := by omega
    by_cases hr0 : r = 0
    · subst r
      by_cases hs1 : s = 1
      · subst s
        obtain ⟨q, hq, hlen, hsub, _⟩ := hp.path_C_C_via_intervals (t := 0) (by omega)
          0 0 2 (d + 1 - a) 1 (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega)
        exact ⟨q, hq, hlen, hsub⟩
      · obtain ⟨q, hq, hlen, hsub, _⟩ := hp.path_C_C_via_intervals hs'
          0 0 1 (s - 1) (d + 1 - a) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega)
        refine ⟨q.copy rfl (by rw [heq]), by simpa only [Walk.isPath_copy] using hq,
          by simpa only [Walk.length_copy] using hlen, ?_⟩
        simpa only [Walk.support_copy] using hsub
    · obtain ⟨q, hq, hlen, hsub, _⟩ := hp.path_C_C_via_intervals hs'
        r (s - 1) 0 (r - 1) (d + 1 - a) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)
      refine ⟨q.copy rfl (by rw [heq]), by simpa only [Walk.isPath_copy] using hq,
        by simpa only [Walk.length_copy] using hlen, ?_⟩
      simpa only [Walk.support_copy] using hsub
  rcases lt_or_gt_of_ne hij with h | h
  · exact hone h hj
  · obtain ⟨q, hq, hlen, hsub⟩ := hone h hi
    exact ⟨q.reverse, hq.reverse, by simpa only [Walk.length_reverse] using hlen,
      by simpa only [Walk.support_reverse, List.reverse_subset] using hsub⟩

/-- An external vertex cannot attach to one of the alternating middle
vertices when a common attachment is universal. -/
theorem AlternatingEnds.no_external_middle_edge {V : Type*} {G : SimpleGraph V} {x y z : V}
    {p : G.Walk x y} {d a i t : ℕ} (hp : AlternatingEnds p d a)
    (hG : NoLongCycle G (2 * d + 3)) (had : a < d)
    (hi : i < d + 2 - a) (ht : t < d + 1 - a)
    (hu : G.IsUniversal (p.getVert (a + 2 * i))) (hz : z ∉ p.support) :
    ¬G.Adj (p.getVert (a + 2 * t + 1)) z := by
  intro hdz
  obtain ⟨q, hq, hqlen, hsub⟩ := hp.path_C_D had hi ht
  have hdisj : q.support.Disjoint (Walk.nil : G.Walk z z).support := by
    intro w hw hwz
    have heq : w = z := by simpa using hwz
    exact hz (heq ▸ hsub hw)
  have huz : p.getVert (a + 2 * i) ≠ z := fun h ↦ hz (h ▸ p.getVert_mem_support _)
  obtain ⟨s, hs, hslen⟩ := cycle_of_two_disjoint_paths q (Walk.nil : G.Walk z z)
    hq (by simp) hdisj hdz (hu huz).symm (by simp; omega)
  have := hG z s hs
  simp only [Walk.length_nil] at hslen
  omega

end Erdos1105

#print axioms Erdos1105.AlternatingEnds.path_C_C
#print axioms Erdos1105.AlternatingEnds.no_external_middle_edge
