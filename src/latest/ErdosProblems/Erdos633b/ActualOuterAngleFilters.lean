import ErdosProblems.Erdos633b.FiniteOuterFilterBase

/-! The finite integer filters hold for actual sorted counterexamples,
including exact transport of the outer vertex reindexing. -/

namespace Erdos633b

theorem ordered_outer_weight_bounds (N a b : ℕ) (ha : 0 < a) (hab : a < b)
    (hs : a + 2 * b < N) :
    (∀ i, 0 < angleTableWeights (N, a, b) i ∧ angleTableWeights (N, a, b) i < N) ∧
      ∑ i, angleTableWeights (N, a, b) i = N := by
  constructor
  · intro i
    fin_cases i <;> dsimp [angleTableWeights] <;> omega
  · simp only [Fin.sum_univ_three, angleTableWeights, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val]
    omega

namespace Tiling

theorem finite_outer_admissible_of_counterexample {T : Triangle} {n : ℕ}
    (d : Tiling T n) (hn : ¬ IsSquare n) (hnot : ¬ EightCases T)
    (v : ℕ × ℕ × ℕ) (hv : v ∈ finiteAngleCandidates)
    (hw : ∀ i, d.tile.angle i = (angleTableWeights v i : ℝ) * (Real.pi / v.1))
    (a b : ℕ) (ha : ∀ i, T.angle i =
      (angleTableWeights (v.1, a, b) i : ℝ) * (Real.pi / v.1))
    (hap : 0 < a) (hab : a < b) (has : a + 2 * b < v.1) :
    FiniteOuterAdmissible v a b := by
  obtain ⟨hN, _, _, hvab, hvs⟩ := finite_angle_candidates_valid v hv
  have hN' : (0 : ℝ) < v.1 := by exact_mod_cast (show 0 < v.1 by omega)
  have hδ : 0 < Real.pi / v.1 := div_pos Real.pi_pos hN'
  have h01 : d.tile.angle 0 < d.tile.angle 1 := by
    rw [hw 0, hw 1]
    apply mul_lt_mul_of_pos_right _ hδ
    exact_mod_cast hvab
  have h12 : d.tile.angle 1 < d.tile.angle 2 := by
    rw [hw 1, hw 2]
    apply mul_lt_mul_of_pos_right _ hδ
    exact_mod_cast (show v.2.2 < v.1 - v.2.1 - v.2.2 by omega)
  obtain ⟨_, _, _, hQ, hR, _⟩ := d.counterexample_ordered_corner_data hn hnot h01 h12
  refine ⟨hap, hab, has, ?_, ?_, ?_⟩
  · intro he
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    apply hnot
    apply d.reptiling_equal_angles_necessary hn
    intro i
    rw [hw i, ha i]
  · intro i
    exact d.finite_corner_reachable_of_row v _ i hQ hR
      (d.integer_corner_row_eq v.1 (by omega) _ _ hw ha i)
  · intro k hk
    obtain ⟨hwp, hws⟩ := angle_table_weights_bounds v hv
    obtain ⟨hbp, hbs⟩ := ordered_outer_weight_bounds v.1 a b hap hab has
    exact d.coprime_integer_angle_tests v.1 (by omega) _ _ hw ha hwp hbp hws hbs k.val hk

theorem counterexample_ordered_outer_filters {T : Triangle} {n : ℕ}
    (d : Tiling T n) (hn : ¬ IsSquare n) (hnot : ¬ EightCases T)
    (v : ℕ × ℕ × ℕ) (hv : v ∈ finiteAngleCandidates)
    (hw : ∀ i, d.tile.angle i = (angleTableWeights v i : ℝ) * (Real.pi / v.1)) :
    ∃ f : Equiv.Perm (Fin 3), ∃ a b : Fin v.1,
      (∀ i, Triangle.angle (T.reindex f) i =
        (angleTableWeights (v.1, a.val, b.val) i : ℝ) * (Real.pi / v.1)) ∧
      FiniteOuterAdmissible v a.val b.val := by
  have hN := (finite_angle_candidates_valid v hv).1
  have hscalene : Function.Injective T.angle := by
    by_contra h
    exact hnot (eightCases_of_not_injective_angles T h)
  obtain ⟨c, hc, hcp, hcs⟩ := d.integer_corner_weights v.1 (by omega) _ hw
  obtain ⟨e, hab, hbc⟩ := ordered_integer_weights T c _ hc hscalene
  have hsum : c (e 0) + c (e 1) + c (e 2) = v.1 := (sorted_weights_sum c e).trans hcs
  have heq : c (e 2) = v.1 - c (e 0) - c (e 1) := by omega
  have ha : ∀ i, Triangle.angle (T.reindex e.symm) i =
      (angleTableWeights (v.1, c (e 0), c (e 1)) i : ℝ) * (Real.pi / v.1) := by
    intro i
    fin_cases i
    · change Triangle.angle (T.reindex e.symm) 0 =
        (c (e 0) : ℝ) * (Real.pi / v.1)
      simpa only [Triangle.angle_reindex, Equiv.symm_symm] using hc (e 0)
    · change Triangle.angle (T.reindex e.symm) 1 =
        (c (e 1) : ℝ) * (Real.pi / v.1)
      simpa only [Triangle.angle_reindex, Equiv.symm_symm] using hc (e 1)
    · change Triangle.angle (T.reindex e.symm) 2 =
        ((v.1 - c (e 0) - c (e 1) : ℕ) : ℝ) * (Real.pi / v.1)
      simpa only [Triangle.angle_reindex, Equiv.symm_symm, heq] using hc (e 2)
  refine ⟨e.symm, ⟨c (e 0), by omega⟩, ⟨c (e 1), by omega⟩, ha, ?_⟩
  let d' : Tiling (T.reindex e.symm) n := d.reindexOuter e.symm
  exact d'.finite_outer_admissible_of_counterexample hn
    (fun h => hnot (eightCases_of_reindex T e.symm h)) v hv hw (c (e 0)) (c (e 1))
    ha (hcp (e 0)) hab (by omega)

theorem counterexample_finite_outer_filters {T : Triangle} {n : ℕ}
    (d : Tiling T n) (hn : ¬ IsSquare n) (hnot : ¬ EightCases T) :
    ∃ e f : Equiv.Perm (Fin 3), ∃ v ∈ finiteAngleCandidates, ∃ a b : Fin v.1,
      (∀ i, Triangle.angle (d.tile.reindex e) i =
        (angleTableWeights v i : ℝ) * (Real.pi / v.1)) ∧
      (∀ i, Triangle.angle (T.reindex f) i =
        (angleTableWeights (v.1, a.val, b.val) i : ℝ) * (Real.pi / v.1)) ∧
      FiniteOuterAdmissible v a.val b.val := by
  obtain ⟨e, v, hv, hw⟩ := d.counterexample_finite_tile_angles hn hnot
  obtain ⟨f, a, b, ha, hf⟩ :=
    (d.reindexTile e).counterexample_ordered_outer_filters hn hnot v hv hw
  exact ⟨e, f, v, hv, a, b, hw, ha, hf⟩

end Tiling
end Erdos633b
