import ErdosProblems.Erdos1105.PathCycleSplice
import ErdosProblems.Erdos1105.SetPath

namespace Erdos1105

open SimpleGraph

/-- A path avoiding an internal vertex supplies an ear from the prefix to
the suffix of the original path. The ear's interior avoids the entire path. -/
theorem exists_ear_across_path_vertex {V : Type*} {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) {t : ℕ} (ht0 : 0 < t) (htL : t < p.length)
    (havoid : ∃ r : G.Walk x y, r.IsPath ∧ p.getVert t ∉ r.support) :
    ∃ i j : ℕ, i < t ∧ t < j ∧ j ≤ p.length ∧
      ∃ q : G.Walk (p.getVert i) (p.getVert j),
        q.IsPath ∧ p.getVert t ∉ q.support ∧
        ∀ w ∈ q.support, w ∈ p.support → w = p.getVert i ∨ w = p.getVert j := by
  classical
  let A : Set V := {w | w ∈ (p.take (t - 1)).support}
  let B : Set V := {w | w ∈ (p.drop (t + 1)).support}
  let S : Set V := {w | w ≠ p.getVert t}
  have hex : ∃ a ∈ A, ∃ b ∈ B, ∃ q : G.Walk a b,
      q.IsPath ∧ ∀ w ∈ q.support, w ∈ S := by
    obtain ⟨r, hr, hravoid⟩ := havoid
    refine ⟨x, (p.take (t - 1)).start_mem_support, y, (p.drop (t + 1)).end_mem_support,
      r, hr, ?_⟩
    intro w hw hwu
    exact hravoid (hwu ▸ hw)
  obtain ⟨a, ha, b, hb, q, hq, hqS, hqA, hqB⟩ := exists_set_path_within G A B S hex
  obtain ⟨i, hi, hiL⟩ := Walk.mem_support_iff_exists_getVert.mp ha
  have hit : i < t := by rw [Walk.take_length] at hiL; omega
  have hi' : p.getVert i = a := by
    simpa only [Walk.take_getVert, Nat.min_eq_right (show i ≤ t - 1 by omega)] using hi
  obtain ⟨j', hj, hjL⟩ := Walk.mem_support_iff_exists_getVert.mp hb
  let j := t + 1 + j'
  have htj : t < j := by dsimp [j]; omega
  have hjL' : j ≤ p.length := by
    rw [Walk.drop_length] at hjL
    dsimp [j]
    omega
  have hj' : p.getVert j = b := by simpa only [Walk.drop_getVert] using hj
  have hqmeet : ∀ w ∈ q.support, w ∈ p.support → w = a ∨ w = b := by
    intro w hw hwp
    obtain ⟨r, hr, hrL⟩ := Walk.mem_support_iff_exists_getVert.mp hwp
    by_cases hrt : r < t
    · apply Or.inl
      apply hqA w hw
      change w ∈ (p.take (t - 1)).support
      apply Walk.mem_support_iff_exists_getVert.mpr
      refine ⟨r, ?_, ?_⟩
      · rw [Walk.take_getVert, Nat.min_eq_right (by omega)]
        exact hr
      · rw [Walk.take_length, Nat.min_eq_left (by omega)]
        omega
    · have htr : t < r := by
        by_contra h
        have hrt' : r = t := by omega
        have hne := hqS w hw
        exact hne (hr.symm.trans (congrArg p.getVert hrt'))
      apply Or.inr
      apply hqB w hw
      change w ∈ (p.drop (t + 1)).support
      apply Walk.mem_support_iff_exists_getVert.mpr
      refine ⟨r - (t + 1), ?_, ?_⟩
      · rw [Walk.drop_getVert, Nat.add_sub_of_le (by omega)]
        exact hr
      · rw [Walk.drop_length]
        omega
  refine ⟨i, j, hit, htj, hjL', q.copy hi'.symm hj'.symm, ?_, ?_, ?_⟩
  · simpa only [Walk.isPath_copy] using hq
  · simp only [Walk.support_copy]
    exact fun h ↦ hqS _ h rfl
  · intro w hw hwp
    rw [Walk.support_copy] at hw
    rcases hqmeet w hw hwp with h | h
    · exact Or.inl (h.trans hi'.symm)
    · exact Or.inr (h.trans hj'.symm)

end Erdos1105

#print axioms Erdos1105.exists_ear_across_path_vertex
