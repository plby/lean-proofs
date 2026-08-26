import ErdosProblems.Erdos556.IndexedCyclePaths

/-!
# The interior-reservoir geometry

Two chords through an interior vertex join two disjoint cycle arcs.
The resulting long path avoids the interiors of two selected intervals,
apart from the single chord vertex which is omitted from the reservoir.
-/

namespace Erdos556

open SimpleGraph

theorem exists_long_path_between_cycle_intervals {V : Type*} {G : SimpleGraph V} {z : V}
    (c : G.Walk z z) (hc : c.IsCycle) (u v w y w' : ℕ)
    (huv : u < v) (hvw : v < w) (hwy : w < y) (hyw : y < w') (hw' : w' < c.length)
    (huy : G.Adj (c.getVert u) (c.getVert y))
    (hvy : G.Adj (c.getVert v) (c.getVert y)) :
    ∃ p : G.Walk (c.getVert w') (c.getVert w), p.IsPath ∧
      p.length + v + w' = c.length + u + w + 2 ∧
      (∀ a, u < a → a < v → c.getVert a ∉ p.support) ∧
      (∀ a, w < a → a < w' → a ≠ y → c.getVert a ∉ p.support) := by
  let q := cycleOutsideArc c u w'
  let r := pathSegment c v w (by omega)
  have hq : q.IsPath := cycleOutsideArc_isPath c hc u w' (by omega) hw'.le
  have hr : r.IsPath := by
    simp only [r, pathSegment, Walk.isPath_copy]
    exact (hc.isPath_drop (by omega : 0 < v)).take (w - v)
  have hqavoid (a : ℕ) (hua : u < a) (haw : a < w') : c.getVert a ∉ q.support := by
    intro ha
    have h := cycleOutsideArc_meets_interval_only_at_ends c hc u w' a hua.le haw.le hw' ha
    omega
  have hrmem (a : V) (ha : a ∈ r.support) :
      ∃ k, v ≤ k ∧ k ≤ w ∧ c.getVert k = a :=
    (mem_support_pathSegment_iff c v w (by omega) (by omega)).mp ha
  have hyq : c.getVert y ∉ q.support := hqavoid y (by omega) hyw
  have hyr : c.getVert y ∉ r.support := by
    intro hy
    obtain ⟨k, hvk, hkw, hky⟩ := hrmem _ hy
    have h := hc.getVert_injOn' (by change k ≤ c.length - 1; omega)
      (by change y ≤ c.length - 1; omega) hky
    omega
  have hqr : q.support.Disjoint r.support := by
    rw [List.disjoint_left]
    intro a haq har
    obtain ⟨k, hvk, hkw, hka⟩ := hrmem a har
    exact hqavoid k (by omega) (by omega) (hka ▸ haq)
  let p := (q.concat huy).append (Walk.cons hvy.symm r)
  have hp : p.IsPath := by
    apply isPath_append_of_support_inter (q.concat huy) (Walk.cons hvy.symm r)
      (hq.concat hyq huy) ((Walk.cons_isPath_iff _ _).mpr ⟨hr, hyr⟩)
    intro a ha hb
    simp only [Walk.support_concat, List.mem_append, List.mem_singleton] at ha
    simp only [Walk.support_cons, List.mem_cons] at hb
    rcases ha with haq | hay
    · rcases hb with hay | har
      · exact hay
      · exact (hqr haq har).elim
    · exact hay
  have havoid (a : ℕ) (hua : u < a) (haw : a < w')
      (havw : ¬ (v ≤ a ∧ a ≤ w)) (hay : a ≠ y) : c.getVert a ∉ p.support := by
    intro ha
    rcases (Walk.mem_support_append_iff (q.concat huy) (Walk.cons hvy.symm r)).mp ha with ha | ha
    · simp only [Walk.support_concat, List.mem_append, List.mem_singleton] at ha
      rcases ha with haq | hay'
      · exact hqavoid a hua haw haq
      · exact hay (hc.getVert_injOn' (by change a ≤ c.length - 1; omega)
          (by change y ≤ c.length - 1; omega) hay')
    · simp only [Walk.support_cons, List.mem_cons] at ha
      rcases ha with hay' | har
      · exact hay (hc.getVert_injOn' (by change a ≤ c.length - 1; omega)
          (by change y ≤ c.length - 1; omega) hay')
      · obtain ⟨k, hvk, hkw, hka⟩ := hrmem _ har
        have hka' := hc.getVert_injOn' (by change k ≤ c.length - 1; omega)
          (by change a ≤ c.length - 1; omega) hka
        exact havw (by omega)
  refine ⟨p, hp, ?_, ?_, ?_⟩
  · simp only [p, q, r, Walk.length_append, Walk.length_concat, Walk.length_cons,
      cycleOutsideArc_length c u w' (by omega), pathSegment_length c v w (by omega) (by omega)]
    omega
  · intro a hua hav
    exact havoid a hua (by omega) (by omega) (by omega)
  · intro a hwa haw hay
    exact havoid a (by omega) haw (by omega) hay

#print axioms exists_long_path_between_cycle_intervals

end Erdos556
