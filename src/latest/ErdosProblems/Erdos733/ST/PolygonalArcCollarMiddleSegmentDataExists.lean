import ErdosProblems.Erdos733.ST.PolygonalArcCollarMiddleSegmentData

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcCollarMiddleSegmentDataExists]
lemma PolygonalArcCollarMiddleSegmentDataExists (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η) :
    Nonempty (PolygonalArcCollarMiddleSegmentData γ controlRadii) := by
-- BODY
  let middle : (j : ℕ) → j + 1 < γ.vertices.length →
      Set (EuclideanSpace ℝ (Fin 2)) := fun j hj =>
    (AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
      Set.Icc
        (controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
          dist γ.vertices[j] γ.vertices[j + 1])
        (1 - controlRadii.radius ⟨j + 1, hj⟩ /
          dist γ.vertices[j] γ.vertices[j + 1])
  have hparams :
      ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
        0 <
          controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
            dist γ.vertices[j] γ.vertices[j + 1] ∧
        controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
            dist γ.vertices[j] γ.vertices[j + 1] <
          1 - controlRadii.radius ⟨j + 1, hj⟩ /
            dist γ.vertices[j] γ.vertices[j + 1] ∧
        1 - controlRadii.radius ⟨j + 1, hj⟩ /
            dist γ.vertices[j] γ.vertices[j + 1] < 1 ∧
        1 - controlRadii.radius ⟨j + 1, hj⟩ /
            dist γ.vertices[j] γ.vertices[j + 1] ≤ 1 := by
    intro j hj
    let i0 : Fin γ.vertices.length := ⟨j, Nat.lt_of_succ_lt hj⟩
    let i1 : Fin γ.vertices.length := ⟨j + 1, hj⟩
    let L : ℝ := dist γ.vertices[j] γ.vertices[j + 1]
    have hleft_pos : 0 < controlRadii.radius i0 := controlRadii.radius_pos i0
    have hright_pos : 0 < controlRadii.radius i1 := controlRadii.radius_pos i1
    have hsum : controlRadii.radius i0 + controlRadii.radius i1 < L := by
      simpa [i0, i1, L] using controlRadii.adjacent_radii_sum_lt (j := j) hj
    have hLpos : 0 < L := by nlinarith
    have hleft_div_pos :
        0 < controlRadii.radius i0 / L := div_pos hleft_pos hLpos
    have hright_div_pos :
        0 < controlRadii.radius i1 / L := div_pos hright_pos hLpos
    have hright_lt_L : controlRadii.radius i1 < L := by nlinarith
    have hright_div_lt_one : controlRadii.radius i1 / L < 1 := by
      rw [div_lt_one hLpos]
      exact hright_lt_L
    have hleft_right_div_sum_lt_one :
        controlRadii.radius i0 / L + controlRadii.radius i1 / L < 1 := by
      rw [← add_div]
      rw [div_lt_one hLpos]
      exact hsum
    have hleft_lt_right :
        controlRadii.radius i0 / L < 1 - controlRadii.radius i1 / L := by
      linarith
    have hright_param_lt_one :
        1 - controlRadii.radius i1 / L < 1 := by
      linarith
    have hright_param_le_one :
        1 - controlRadii.radius i1 / L ≤ 1 := le_of_lt hright_param_lt_one
    exact ⟨by simpa [i0, L] using hleft_div_pos,
      by simpa [i0, i1, L] using hleft_lt_right,
      by simpa [i1, L] using hright_param_lt_one,
      by simpa [i1, L] using hright_param_le_one⟩
  refine ⟨
    { middle := middle
      left_parameter_pos := ?_
      left_parameter_lt_right_parameter := ?_
      right_parameter_lt_one := ?_
      middle_eq := ?_
      middle_nonempty := ?_
      middle_compact := ?_
      middle_subset_segment := ?_
      middle_subset_carrier := ?_
      middle_subset_eta_neighborhood := ?_ }⟩
  · intro j hj
    exact (hparams j hj).1
  · intro j hj
    exact (hparams j hj).2.1
  · intro j hj
    exact (hparams j hj).2.2.1
  · intro j hj
    rfl
  · intro j hj
    refine ⟨AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]
        (controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
          dist γ.vertices[j] γ.vertices[j + 1]), ?_⟩
    refine ⟨controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
          dist γ.vertices[j] γ.vertices[j + 1], ?_, rfl⟩
    exact ⟨le_rfl, le_of_lt ((hparams j hj).2.1)⟩
  · intro j hj
    dsimp [middle]
    exact isCompact_Icc.image (by fun_prop)
  · intro j hj x hx
    dsimp [middle] at hx
    rcases hx with ⟨t, ht, rfl⟩
    rw [segment_eq_image_lineMap]
    refine ⟨t, ?_, rfl⟩
    have hleft_nonneg :
        0 ≤ controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
            dist γ.vertices[j] γ.vertices[j + 1] :=
      le_of_lt (hparams j hj).1
    exact ⟨le_trans hleft_nonneg ht.1, le_trans ht.2 (hparams j hj).2.2.2⟩
  · intro j hj x hx
    rw [γ.carrier_eq]
    refine ⟨j, hj, ?_⟩
    dsimp [middle] at hx
    rcases hx with ⟨t, ht, rfl⟩
    rw [segment_eq_image_lineMap]
    refine ⟨t, ?_, rfl⟩
    have hleft_nonneg :
        0 ≤ controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
            dist γ.vertices[j] γ.vertices[j + 1] :=
      le_of_lt (hparams j hj).1
    exact ⟨le_trans hleft_nonneg ht.1, le_trans ht.2 (hparams j hj).2.2.2⟩
  · intro j hj z hz
    have hzCarrier : z ∈ γ.carrier := by
      rw [γ.carrier_eq]
      refine ⟨j, hj, ?_⟩
      dsimp [middle] at hz
      rcases hz with ⟨t, ht, rfl⟩
      rw [segment_eq_image_lineMap]
      refine ⟨t, ?_, rfl⟩
      have hleft_nonneg :
          0 ≤ controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
              dist γ.vertices[j] γ.vertices[j + 1] :=
        le_of_lt (hparams j hj).1
      exact ⟨le_trans hleft_nonneg ht.1, le_trans ht.2 (hparams j hj).2.2.2⟩
    have hηpos : 0 < η :=
      (controlRadii.radius_pos ⟨j, Nat.lt_of_succ_lt hj⟩).trans
        (controlRadii.radius_lt_eta ⟨j, Nat.lt_of_succ_lt hj⟩)
    exact ⟨z, hzCarrier, by simpa using hηpos⟩
