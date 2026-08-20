import ErdosProblems.Erdos733.ST.PlanarRot90ConeAvoidsRay

open Classical
noncomputable section

-- [TABLET NODE: PlanarRot90ConeAvoidsFiniteRays]
lemma PlanarRot90ConeAvoidsFiniteRays
    (directions : Finset (EuclideanSpace ℝ (Fin 2)))
    (d : EuclideanSpace ℝ (Fin 2)) :
    d ≠ 0 →
      (∀ v ∈ directions, ¬ ∃ a : ℝ, 0 < a ∧ v = a • d) →
        ∃ κ : ℝ, 0 < κ ∧
          ∀ v ∈ directions, ∀ c t s : ℝ,
            0 ≤ c → 0 < t → |s| < κ * t →
              c • v ≠ t • d + s • PlanarRot90 d := by
-- BODY
  intro hd
  induction directions using Finset.induction_on with
  | empty =>
      intro _hnot
      refine ⟨1, by norm_num, ?_⟩
      intro v hv
      simp at hv
  | insert a directions ha ih =>
      intro hnot
      have hnot_a : ¬ ∃ r : ℝ, 0 < r ∧ a = r • d := hnot a (by simp)
      have hnot_directions :
          ∀ v ∈ directions, ¬ ∃ r : ℝ, 0 < r ∧ v = r • d := by
        intro v hv
        exact hnot v (by simp [hv])
      obtain ⟨κa, hκa_pos, havoid_a⟩ :=
        PlanarRot90ConeAvoidsRay (d := d) (v := a) hd hnot_a
      obtain ⟨κold, hκold_pos, havoid_old⟩ := ih hnot_directions
      refine ⟨min κa κold, lt_min hκa_pos hκold_pos, ?_⟩
      intro v hv c t s hc ht hs_lt hEq
      have hs_lt_a : |s| < κa * t := by
        nlinarith [hs_lt, min_le_left κa κold, le_of_lt ht]
      have hs_lt_old : |s| < κold * t := by
        nlinarith [hs_lt, min_le_right κa κold, le_of_lt ht]
      have zero_case
          (hnot_v : ¬ ∃ r : ℝ, 0 < r ∧ v = r • d)
          (hs0 : s = 0) :
          False := by
        have hEq0 : c • v = t • d := by
          simpa [hs0] using hEq
        have hc_ne : c ≠ 0 := by
          intro hc0
          have htd0 : t • d = 0 := by
            simpa [hc0] using hEq0.symm
          exact (smul_ne_zero (ne_of_gt ht) hd) htd0
        have hc_pos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc_ne)
        have hv_ray : v = (t / c) • d := by
          have hscale := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => c⁻¹ • x) hEq0
          simpa [smul_smul, hc_ne, div_eq_inv_mul, mul_comm] using hscale
        exact hnot_v ⟨t / c, div_pos ht hc_pos, hv_ray⟩
      rw [Finset.mem_insert] at hv
      rcases hv with rfl | hv_old
      · by_cases hs0 : s = 0
        · exact zero_case hnot_a hs0
        · exact havoid_a c t s hc ht hs0 hs_lt_a hEq
      · by_cases hs0 : s = 0
        · exact zero_case (hnot_directions v hv_old) hs0
        · exact havoid_old v hv_old c t s hc ht hs_lt_old hEq
