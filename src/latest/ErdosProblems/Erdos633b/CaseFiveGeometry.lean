import ErdosProblems.Erdos633b.CaseFiveConstruction

/-! Case-(5) geometric sufficiency and normalization, before the independent nonsquare exclusion. -/

namespace Erdos633b

theorem case_five_geometric_counts (T : Triangle) (hB : T.angle 1 = 2 * T.angle 0)
    (hrat : IsRational (Real.sqrt 3 * Real.tan (T.angle 0 / 2))) :
    ∃ a b c m : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < m ∧
      c ^ 2 = a ^ 2 + a * b + b ^ 2 ∧
      Nonempty (Tiling T (3 * m ^ 2 * (a + 2 * b) * (a + b))) := by
  have hd : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have he : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hA : T.angle 0 < Real.pi / 3 := by linarith [T.angle_sum, T.angle_pos 2]
  obtain ⟨a, b, c, ha, hb, hc, hrel, hα⟩ :=
    Sixty.integral_reference_of_rational_parameter (Real.sqrt 3) hd he
      (T.angle 0) (T.angle_pos 0) hA hrat
  obtain ⟨m, hm, ⟨patch⟩⟩ :=
    CaseFiveCoordinates.integer_tiling_exists (Real.sqrt 3) hd he a b c ha hb hc hrel
  let U := CaseFiveCoordinates.outer (Real.sqrt 3) hd a b c m (by exact_mod_cast ha)
    (by exact_mod_cast hb) (by exact_mod_cast hc) (by exact_mod_cast hm)
  let V : Triangle := U.reindex (Equiv.swap 0 1)
  let R := Sixty.groupTwoReference (Real.sqrt 3) hd a b
    (by exact_mod_cast ha) (by exact_mod_cast hb)
  have hu : U.angle 0 = 2 * R.angle 1 ∧ U.angle 1 = R.angle 1 ∧ U.angle 2 = 3 * R.angle 2 :=
    CaseFiveCoordinates.outer_angles (Real.sqrt 3) hd he a b c m (by exact_mod_cast ha)
      (by exact_mod_cast hb) (by exact_mod_cast hc) (by exact_mod_cast hm) (by exact_mod_cast hrel)
  have hv0 : V.angle 0 = T.angle 0 := by
    rw [Triangle.angle_reindex]
    exact hu.2.1.trans hα
  have hv1 : V.angle 1 = T.angle 1 := by
    rw [Triangle.angle_reindex]
    change U.angle 0 = T.angle 1
    rw [hu.1, hα, hB]
  have hv2 : V.angle 2 = T.angle 2 := by linarith [V.angle_sum, T.angle_sum]
  have hangs : ∀ i, V.angle i = T.angle i := by
    intro i
    fin_cases i
    · exact hv0
    · exact hv1
    · exact hv2
  exact ⟨a, b, c, m, ha, hb, hc, hm, hrel,
    ⟨(patch.reindexOuter (Equiv.swap 0 1)).transportAngles hangs⟩⟩

theorem case_five_geometric_counts_reindexed (T : Triangle) (e : Equiv.Perm (Fin 3))
    (hB : T.angle (e 1) = 2 * T.angle (e 0))
    (hrat : IsRational (Real.sqrt 3 * Real.tan (T.angle (e 0) / 2))) :
    ∃ a b c m : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < m ∧
      c ^ 2 = a ^ 2 + a * b + b ^ 2 ∧
      Nonempty (Tiling T (3 * m ^ 2 * (a + 2 * b) * (a + b))) := by
  obtain ⟨a, b, c, m, ha, hb, hc, hm, hrel, ⟨d⟩⟩ :=
    case_five_geometric_counts (T.reindex e.symm)
      (by simpa only [Triangle.angle_reindex, Equiv.symm_symm] using hB)
      (by simpa only [Triangle.angle_reindex, Equiv.symm_symm] using hrat)
  refine ⟨a, b, c, m, ha, hb, hc, hm, hrel, ⟨?_⟩⟩
  exact { tile := d.tile
          place := d.place
          covers := by simpa only [Triangle.support_reindex] using d.covers
          disjoint_interiors := d.disjoint_interiors }

end Erdos633b
