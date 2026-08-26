import ErdosProblems.Erdos73.ProjectiveReferencePorts

/-! The concrete projective rotation has exactly the vertex-label fibres as its cycles. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

theorem projectiveAcrossCap_high_cell {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (j : Fin (n - 1)) (i : Fin 4) (hi : 2 ≤ i.val) :
    ∃ r c k, projectiveAcrossFace hn hnEven (Sum.inr j, i) = (Sum.inl (r, c), k) := by
  dsimp only [projectiveAcrossFace]
  rw [if_neg (by omega)]
  split_ifs <;> exact ⟨_, _, _, rfl⟩

theorem projectiveReference_cap_high {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (j : Fin (n - 1)) (i : Fin 4) (hi : 2 ≤ i.val) :
    ProjectiveReachesReference hn hnEven (Sum.inr j, i) := by
  obtain ⟨r, c, k, he⟩ := projectiveAcrossCap_high_cell hn hnEven j i hi
  apply projectiveReference_of_across
  rw [he]
  exact projectiveReference_cell hn hnEven r c k

theorem projectiveReference_cap_one {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (j : Fin (n - 1)) : ProjectiveReachesReference hn hnEven (Sum.inr j, 1) := by
  by_cases hj : j.val = 0
  · have he : projectiveAcrossFace hn hnEven (Sum.inr j, 1) =
        (Sum.inl (⟨0, by omega⟩, ⟨0, by omega⟩), 3) := by
      simp [projectiveAcrossFace, hj, Fin.ext_iff]
    apply projectiveReference_of_across
    rw [he]
    exact projectiveReference_cell hn hnEven _ _ _
  · have he : projectiveAcrossFace hn hnEven (Sum.inr j, 1) =
        (Sum.inr ⟨j.val - 1, by have hh := j.isLt; omega⟩, 3) := by
      simp [projectiveAcrossFace, hj, Fin.ext_iff]
    apply projectiveReference_of_across
    rw [he]
    exact projectiveReference_cap_high hn hnEven _ 3 (by decide)

theorem projectiveReference_cap_zero {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (k : ℕ) (hk : k < n - 1) :
    ProjectiveReachesReference hn hnEven (Sum.inr ⟨k, hk⟩, 0) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hz : k = 0
    · subst k
      have he : projectiveAcrossFace hn hnEven (Sum.inr ⟨0, hk⟩, 0) =
          (Sum.inl (⟨0, by omega⟩, ⟨0, by omega⟩), 0) := by
        simp [projectiveAcrossFace, Fin.ext_iff]
      apply projectiveReference_of_across
      rw [he]
      exact projectiveReference_cell hn hnEven _ _ _
    · have he : projectiveAcrossFace hn hnEven (Sum.inr ⟨k, hk⟩, 0) =
          (Sum.inr ⟨k - 1, by omega⟩, 0) := by
        simp [projectiveAcrossFace, hz, Fin.ext_iff]
      apply projectiveReference_of_across
      rw [he]
      exact ih (k - 1) (by omega) (by omega)

theorem projectiveReference_all {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (d : ProjectivePort n) : ProjectiveReachesReference hn hnEven d := by
  rcases d with ⟨f, i⟩
  rcases f with ⟨r, c⟩ | j
  · exact projectiveReference_cell hn hnEven r c i
  · fin_cases i
    · exact projectiveReference_cap_zero hn hnEven j.val j.isLt
    · exact projectiveReference_cap_one hn hnEven j
    · exact projectiveReference_cap_high hn hnEven j 2 (by decide)
    · exact projectiveReference_cap_high hn hnEven j 3 (by decide)

theorem projectiveRotation_fiber {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (a b : ProjectivePort n) (hab : projectivePortLabel hn a = projectivePortLabel hn b) :
    (projectiveRotation hn hnEven).SameCycle a b := by
  have ha := projectiveReference_all hn hnEven a
  have hb := projectiveReference_all hn hnEven b
  unfold ProjectiveReachesReference at ha hb
  rw [hab] at ha
  exact (ha.trans hb.symm).inv

end
end Erdos73
