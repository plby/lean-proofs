import ErdosProblems.Erdos73.ProjectiveRotationFibers

/-! Every coordinate-grid edge is represented by a paired corner port. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exists_alpha_pair_of_face_side {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (f : ProjectiveFace n) (i j : Fin 4)
    (hside : quadranglePair (projectiveFaceParity f) i = j ∨
      quadranglePair (!(projectiveFaceParity f)) i = j) :
    ∃ d, projectivePortLabel hn d = projectiveFaceCorner hn f i ∧
      projectivePortLabel hn (projectivePortPair n d) = projectiveFaceCorner hn f j := by
  rcases hside with h | h
  · refine ⟨(f, i), rfl, ?_⟩
    change projectiveFaceCorner hn f (quadranglePair (projectiveFaceParity f) i) = _
    rw [h]
  · refine ⟨projectiveRotation hn hnEven (f, i), projectiveRotation_label hn hnEven (f, i), ?_⟩
    have hh := congrArg Prod.snd (projectiveRotation_pair hn hnEven (f, i))
    change projectivePortLabel hn (projectivePortPair n (projectiveRotation hn hnEven (f, i))) =
      projectivePortLabel hn ((projectivePortOpposite n * projectivePortPair n) (f, i)) at hh
    rw [projectivePortOtherPair_apply] at hh
    exact hh.trans (congrArg (projectiveFaceCorner hn f) h)

theorem exists_projective_alpha_pair_symm {n : ℕ} (hn : 2 ≤ n) {u v : Fin n × Fin n}
    (h : ∃ d, projectivePortLabel hn d = u ∧ projectivePortLabel hn (projectivePortPair n d) = v) :
    ∃ d, projectivePortLabel hn d = v ∧ projectivePortLabel hn (projectivePortPair n d) = u := by
  obtain ⟨d, hd, ht⟩ := h
  refine ⟨projectivePortPair n d, ht, ?_⟩
  rw [projectivePortPair_involutive n d, hd]

theorem exists_projective_alpha_horizontal {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (r : Fin n) (c : Fin (n - 1)) :
    ∃ d, projectivePortLabel hn d = (r, ⟨c.val, by have hh := c.isLt; omega⟩) ∧
      projectivePortLabel hn (projectivePortPair n d) = (r, ⟨c.val + 1, by have hh := c.isLt; omega⟩) := by
  have hh := exists_alpha_pair_of_face_side hn hnEven (Sum.inl (r, c)) 0 1
    (quadranglePair_side_zero_one _)
  by_cases hr : r.val + 1 < n
  all_goals simpa only [projectiveFaceCorner, hr, dite_true, dite_false,
    Matrix.cons_val_zero, Matrix.cons_val_one] using hh

def projectiveDown {n : ℕ} (hn : 2 ≤ n) (r c : Fin n) : Fin n × Fin n :=
  if hr : r.val + 1 < n then (⟨r.val + 1, hr⟩, c)
  else (⟨0, by omega⟩, ⟨n - 1 - c.val, by omega⟩)

theorem exists_projective_alpha_down {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (r c : Fin n) :
    ∃ d, projectivePortLabel hn d = (r, c) ∧
      projectivePortLabel hn (projectivePortPair n d) = projectiveDown hn r c := by
  have hc := c.isLt
  by_cases hcol : c.val + 1 < n
  · obtain ⟨d, hd, ht⟩ := exists_alpha_pair_of_face_side hn hnEven
      (Sum.inl (r, ⟨c.val, by omega⟩)) 0 3 (quadranglePair_side_zero_three _)
    refine ⟨d, hd.trans ?_, ht.trans ?_⟩
    · dsimp only [projectiveFaceCorner]
      split <;> rfl
    · dsimp only [projectiveFaceCorner, projectiveDown]
      split <;> rfl
  · obtain ⟨d, hd, ht⟩ := exists_alpha_pair_of_face_side hn hnEven
      (Sum.inl (r, ⟨n - 2, by omega⟩)) 1 2 (quadranglePair_side_one_two _)
    refine ⟨d, hd.trans ?_, ht.trans ?_⟩
    all_goals dsimp only [projectiveFaceCorner, projectiveDown]
    all_goals split <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Prod.mk.injEq, Fin.ext_iff, Fin.val_mk, true_and, and_true]
    all_goals omega

theorem exists_projective_alpha_horizontal_step {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (u v : Fin n × Fin n) (hr : u.1 = v.1) (hc : u.2.val + 1 = v.2.val) :
    ∃ d, projectivePortLabel hn d = u ∧ projectivePortLabel hn (projectivePortPair n d) = v := by
  have hv := v.2.isLt
  obtain ⟨d, hd, ht⟩ := exists_projective_alpha_horizontal hn hnEven u.1 ⟨u.2.val, by omega⟩
  refine ⟨d, hd, ht.trans ?_⟩
  exact Prod.ext hr (Fin.ext hc)

theorem exists_projective_alpha_vertical_step {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (u v : Fin n × Fin n) (hc : u.2 = v.2) (hr : u.1.val + 1 = v.1.val) :
    ∃ d, projectivePortLabel hn d = u ∧ projectivePortLabel hn (projectivePortPair n d) = v := by
  have hv := v.1.isLt
  obtain ⟨d, hd, ht⟩ := exists_projective_alpha_down hn hnEven u.1 u.2
  refine ⟨d, hd, ht.trans ?_⟩
  rw [projectiveDown, dif_pos (by omega)]
  exact Prod.ext (Fin.ext hr) hc

theorem exists_projective_alpha_wrap_step {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (u v : Fin n × Fin n) (hu : u.1.val + 1 = n) (hv : v.1.val = 0)
    (hc : u.2.val + v.2.val + 1 = n) :
    ∃ d, projectivePortLabel hn d = u ∧ projectivePortLabel hn (projectivePortPair n d) = v := by
  obtain ⟨d, hd, ht⟩ := exists_projective_alpha_down hn hnEven u.1 u.2
  refine ⟨d, hd, ht.trans ?_⟩
  rw [projectiveDown, dif_neg (by omega)]
  apply Prod.ext <;> apply Fin.ext <;> dsimp only <;> omega

theorem projective_coordinate_edge_covered {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (u v : Fin n × Fin n) (h : (twistedCoordinateGraph n).Adj u v) :
    ∃ d, projectivePortLabel hn d = u ∧ projectivePortLabel hn (projectivePortPair n d) = v := by
  rcases h.2 with ⟨hr, hc | hc⟩ | ⟨hc, hr | hr⟩ | ⟨hr, hc⟩
  · exact exists_projective_alpha_horizontal_step hn hnEven u v hr hc
  · exact exists_projective_alpha_pair_symm hn
      (exists_projective_alpha_horizontal_step hn hnEven v u hr.symm hc)
  · exact exists_projective_alpha_vertical_step hn hnEven u v hc hr
  · exact exists_projective_alpha_pair_symm hn
      (exists_projective_alpha_vertical_step hn hnEven v u hc.symm hr)
  · rcases hr with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · exact exists_projective_alpha_wrap_step hn hnEven u v hu hv hc
    · exact exists_projective_alpha_pair_symm hn
        (exists_projective_alpha_wrap_step hn hnEven v u hv hu (by omega))

end
end Erdos73
