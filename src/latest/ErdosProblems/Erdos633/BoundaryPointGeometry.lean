import ErdosProblems.Erdos633.EdgeSectorArea

/-!
# Every nonvertex boundary point lies on an open edge

The coordinate inequalities give an explicit exhaustive boundary case split.
Together with the sector formulas this covers arbitrary points of a triangle,
including tile vertices that lie in the middle of another tile's edge.
-/

namespace Erdos633

theorem standard_boundary_mem_open_edges (w : ℂ)
    (hx : 0 ≤ w.re) (hy : 0 ≤ w.im) (hs : w.re + w.im ≤ 1)
    (hn : ¬ (0 < w.re ∧ 0 < w.im ∧ w.re + w.im < 1))
    (h0 : w ≠ 0) (h1 : w ≠ 1) (hI : w ≠ Complex.I) :
    w ∈ openSegment ℝ (0 : ℂ) 1 ∨ w ∈ openSegment ℝ (0 : ℂ) Complex.I ∨
      w ∈ openSegment ℝ (1 : ℂ) Complex.I := by
  by_cases hy0 : w.im = 0
  · have hx0 : 0 < w.re := by
      by_contra h
      have he : w.re = 0 := le_antisymm (le_of_not_gt h) hx
      exact h0 (Complex.ext (by simpa using he) (by simpa using hy0))
    have hx1 : w.re < 1 := by
      by_contra h
      have he : w.re = 1 := by linarith
      exact h1 (Complex.ext (by simpa using he) (by simpa using hy0))
    have he : AffineMap.lineMap (0 : ℂ) 1 w.re = w := by
      apply Complex.ext <;> simp [AffineMap.lineMap_apply_module, Complex.real_smul, hy0]
    exact Or.inl (he ▸ lineMap_mem_openSegment ℝ (0 : ℂ) 1 ⟨hx0, hx1⟩)
  · have hypos : 0 < w.im := lt_of_le_of_ne hy (Ne.symm hy0)
    by_cases hx0 : w.re = 0
    · have hy1 : w.im < 1 := by
        by_contra h
        have he : w.im = 1 := by linarith
        exact hI (Complex.ext (by simpa using hx0) (by simpa using he))
      have he : AffineMap.lineMap (0 : ℂ) Complex.I w.im = w := by
        apply Complex.ext <;> simp [AffineMap.lineMap_apply_module, Complex.real_smul, hx0]
      exact Or.inr (Or.inl (he ▸ lineMap_mem_openSegment ℝ (0 : ℂ) Complex.I ⟨hypos, hy1⟩))
    · have hxpos : 0 < w.re := lt_of_le_of_ne hx (Ne.symm hx0)
      have heq : w.re + w.im = 1 := by
        apply le_antisymm hs
        by_contra h
        exact hn ⟨hxpos, hypos, lt_of_not_ge h⟩
      have hy1 : w.im < 1 := by linarith
      have he : AffineMap.lineMap (1 : ℂ) Complex.I w.im = w := by
        apply Complex.ext
        · simp only [AffineMap.lineMap_apply_module, Complex.add_re, Complex.smul_re,
            Complex.one_re, Complex.I_re, smul_eq_mul, mul_one, mul_zero, add_zero]
          linarith
        · simp [AffineMap.lineMap_apply_module, Complex.real_smul]
      exact Or.inr (Or.inr (he ▸ lineMap_mem_openSegment ℝ (1 : ℂ) Complex.I ⟨hypos, hy1⟩))

theorem Triangle.boundary_nonvertex_mem_open_edges (P : Triangle) (z : ℂ)
    (hz : z ∈ P.carrier) (hint : z ∉ interior P.carrier)
    (hvertex : z ∉ Set.range P.vertex) :
    z ∈ openSegment ℝ P.a P.b ∨ z ∈ openSegment ℝ P.a P.c ∨
      z ∈ openSegment ℝ P.b P.c := by
  obtain ⟨w, rfl⟩ := P.coordinateEquiv.surjective z
  have hc := (P.mem_carrier_iff_coordinates (P.coordinateEquiv w)).mp hz
  simp only [P.coordinateEquiv.symm_apply_apply] at hc
  have hn : ¬ (0 < w.re ∧ 0 < w.im ∧ w.re + w.im < 1) := by
    intro hw
    apply hint
    apply (P.mem_interior_iff_coordinates _).mpr
    simpa only [P.coordinateEquiv.symm_apply_apply] using hw
  have h0 : w ≠ 0 := by
    intro hw
    apply hvertex
    refine ⟨0, ?_⟩
    change P.a = P.coordinateEquiv w
    rw [hw, P.coordinateEquiv_zero]
  have h1 : w ≠ 1 := by
    intro hw
    apply hvertex
    refine ⟨1, ?_⟩
    change P.b = P.coordinateEquiv w
    rw [hw, P.coordinateEquiv_one]
  have hI : w ≠ Complex.I := by
    intro hw
    apply hvertex
    refine ⟨2, ?_⟩
    change P.c = P.coordinateEquiv w
    rw [hw, P.coordinateEquiv_I]
  have himage (a b : ℂ) (hw : w ∈ openSegment ℝ a b) :
      P.coordinateEquiv w ∈ openSegment ℝ (P.coordinateEquiv a) (P.coordinateEquiv b) := by
    have he : P.coordinateEquiv '' openSegment ℝ a b =
        openSegment ℝ (P.coordinateEquiv a) (P.coordinateEquiv b) :=
      image_openSegment ℝ P.coordinateEquiv.toAffineMap a b
    rw [← he]
    exact ⟨w, hw, rfl⟩
  rcases standard_boundary_mem_open_edges w hc.1 hc.2.1 hc.2.2 hn h0 h1 hI with h | h | h
  · exact Or.inl (by simpa only [P.coordinateEquiv_zero, P.coordinateEquiv_one] using himage 0 1 h)
  · exact Or.inr (Or.inl (by
      simpa only [P.coordinateEquiv_zero, P.coordinateEquiv_I] using himage 0 Complex.I h))
  · exact Or.inr (Or.inr (by
      simpa only [P.coordinateEquiv_one, P.coordinateEquiv_I] using himage 1 Complex.I h))

theorem Triangle.localSectorArea_boundary_nonvertex (P : Triangle) (z : ℂ)
    (hz : z ∈ P.carrier) (hint : z ∉ interior P.carrier)
    (hvertex : z ∉ Set.range P.vertex) : P.localSectorArea z = Real.pi / 2 := by
  rcases P.boundary_nonvertex_mem_open_edges z hz hint hvertex with h | h | h
  · exact P.localSectorArea_openSegment_ab z h
  · exact P.localSectorArea_openSegment_ac z h
  · exact P.localSectorArea_openSegment_bc z h

theorem Triangle.localSectorArea_pos_of_mem (P : Triangle) (z : ℂ) (hz : z ∈ P.carrier) :
    0 < P.localSectorArea z := by
  by_cases hi : z ∈ interior P.carrier
  · rw [P.localSectorArea_interior z hi]
    exact Real.pi_pos
  · by_cases hv : z ∈ Set.range P.vertex
    · obtain ⟨k, rfl⟩ := hv
      rw [P.localSectorArea_vertex]
      exact div_pos (P.cornerAngle_pos k) (by norm_num)
    · rw [P.localSectorArea_boundary_nonvertex z hz hi hv]
      exact div_pos Real.pi_pos (by norm_num)

end Erdos633
