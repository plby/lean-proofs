import ErdosProblems.Erdos1105.ShortCoreBoundary
import ErdosProblems.Erdos1105.ShortPathBlocks

namespace Erdos1105

open SimpleGraph Finset

/-- The global short-core configuration: away from the common attachment
set, every edge lies inside one of the two end blocks. -/
theorem short_core_edge_shape {V : Type*} [Fintype V] [DecidableEq V]
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
    ∀ v w, G.Adj v w →
      v ∈ pathAttachments p d a ∨ w ∈ pathAttachments p d a ∨
      (v ∈ pathInitialBlock p a ∧ w ∈ pathInitialBlock p a) ∨
      (v ∈ pathFinalBlock p a ∧ w ∈ pathFinalBlock p a) := by
  classical
  have hAlt := short_core_alternating_ends hG hu hconn p hp hlen ha had.le hbefore hafter hmiddle
  have hbeforeR : ∀ j < a, ¬G.Adj x (p.reverse.getVert j) := by
    intro j hj
    rw [Walk.getVert_reverse]
    exact hafter _ (by omega) (by omega)
  have hforward (i j : ℕ) (hiL : i ≤ p.length) (hjL : j ≤ p.length) (hij : i < j)
      (hijAdj : G.Adj (p.getVert i) (p.getVert j)) :
      p.getVert i ∈ pathAttachments p d a ∨ p.getVert j ∈ pathAttachments p d a ∨
      (p.getVert i ∈ pathInitialBlock p a ∧ p.getVert j ∈ pathInitialBlock p a) ∨
      (p.getVert i ∈ pathFinalBlock p a ∧ p.getVert j ∈ pathFinalBlock p a) := by
    by_cases hiA : i < a
    · by_cases hjA : j < a
      · exact Or.inr (Or.inr (Or.inl ⟨mem_image.mpr ⟨i, mem_range.mpr hiA, rfl⟩,
          mem_image.mpr ⟨j, mem_range.mpr hjA, rfl⟩⟩))
      · have hxj := (low_core_initial_segment_twins hG hu hconn p hp (by omega)
          (show a ≤ p.length by omega) hbefore i hiA j (by omega) hjL).mp hijAdj
        have hja : j ≤ p.length - a := by
          by_contra h
          exact hafter j (by omega) hjL hxj
        exact Or.inr (Or.inl ((mem_pathAttachments hAlt hjL).mpr
          ⟨by omega, hja, (hmiddle j (by omega) hja).1.mp hxj⟩))
    · by_cases hiB : p.length - a < i
      · exact Or.inr (Or.inr (Or.inr
          ⟨(mem_pathFinalBlock p hp.isPath (by omega) hiL).mpr (by omega),
           (mem_pathFinalBlock p hp.isPath (by omega) hjL).mpr (by omega)⟩))
      · have hai : a ≤ i := by omega
        have hia : i ≤ p.length - a := by omega
        by_cases hiEven : Even (i - a)
        · exact Or.inl ((mem_pathAttachments hAlt hiL).mpr ⟨hai, hia, hiEven⟩)
        · by_cases hjB : p.length - a < j
          · have htwins := low_core_initial_segment_twins hG hu hconn p.reverse hp.reverse
              (by simpa only [Walk.length_reverse] using (show 2 * d + 3 ≤ p.length + 1 by omega))
              (show a ≤ p.reverse.length by rw [Walk.length_reverse]; omega) hbeforeR
              (p.length - j) (by omega) (p.length - i) (by omega)
              (by rw [Walk.length_reverse]; omega)
            have hyi : G.Adj y (p.getVert i) := by
              have h := htwins.mp (by
                simpa only [Walk.getVert_reverse, Nat.sub_sub_self hiL,
                  Nat.sub_sub_self hjL] using hijAdj.symm)
              simpa only [Walk.getVert_reverse, Nat.sub_sub_self hiL] using h
            exact (hiEven ((hmiddle i hai hia).2.mp hyi)).elim
          · have haj : a ≤ j := by omega
            have hja : j ≤ p.length - a := by omega
            by_cases hjEven : Even (j - a)
            · exact Or.inr (Or.inl ((mem_pathAttachments hAlt hjL).mpr ⟨haj, hja, hjEven⟩))
            · obtain ⟨r, hr⟩ := (Nat.even_or_odd (i - a)).resolve_left hiEven
              obtain ⟨s, hs⟩ := (Nat.even_or_odd (j - a)).resolve_left hjEven
              have heq₁ : a + 2 * r + 1 = i := by omega
              have heq₂ : a + 2 * s + 1 = j := by omega
              have hnot := short_core_middle_independent hG p hp.isPath hlen ha had.le hmiddle
                r (by omega) s (by omega)
              exact (hnot (by simpa only [heq₁, heq₂] using hijAdj)).elim
  intro v w hvw
  by_cases hv : v ∈ p.support
  · by_cases hw : w ∈ p.support
    · obtain ⟨i, rfl, hiL⟩ := Walk.mem_support_iff_exists_getVert.mp hv
      obtain ⟨j, rfl, hjL⟩ := Walk.mem_support_iff_exists_getVert.mp hw
      rcases lt_trichotomy i j with hij | rfl | hji
      · exact hforward i j hiL hjL hij hvw
      · exact (hvw.ne rfl).elim
      · rcases hforward j i hjL hiL hji hvw.symm with h | h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl h.symm))
        · exact Or.inr (Or.inr (Or.inr h.symm))
    · obtain ⟨j, hj, heq⟩ := short_core_external_boundary hG hu hconn p hp hlen ha had
        hbefore hafter hmiddle w hw v hv hvw.symm
      exact Or.inl (mem_image.mpr ⟨j, mem_range.mpr hj, heq⟩)
  · by_cases hw : w ∈ p.support
    · obtain ⟨j, hj, heq⟩ := short_core_external_boundary hG hu hconn p hp hlen ha had
        hbefore hafter hmiddle v hv w hw hvw
      exact Or.inr (Or.inl (mem_image.mpr ⟨j, mem_range.mpr hj, heq⟩))
    · exact (short_core_outside_independent hG hu hconn p hp hlen ha had
        hbefore hafter hmiddle v hv w hw hvw).elim

end Erdos1105

#print axioms Erdos1105.short_core_edge_shape
