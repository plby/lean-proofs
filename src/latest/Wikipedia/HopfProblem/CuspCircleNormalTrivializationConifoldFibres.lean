import Wikipedia.HopfProblem.CuspCircleNormalTrivializationConifoldMap
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationConifoldFibresAlgebra

/-!
# Actual global fibres of the toric small-resolution map

The elementary matrix fibre calculation is compared with the original
two-chart gluing. Thus the global map is injective away from the actual
zero section, is surjective onto the determinant-zero matrices, and its
zero fibre is precisely the original embedded middle curve.
-/

noncomputable section

open Set
open scoped Matrix

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization.Conifold

open ToricCharts ConifoldStandardBoundary

/-- The matrix fibres give exactly the genuine product-chart identification. -/
theorem baseProductChart_eq_of_chartMatrix_eq (i j : Bool) (a b : ℂ) (p q : Fibre)
    (hp : p ≠ 0) (hq : q ≠ 0) (h : chartMatrix i a p = chartMatrix j b q) :
    baseProductChart i (a, fibreEquiv i a p) =
      baseProductChart j (b, fibreEquiv j b q) := by
  cases i <;> cases j
  · obtain ⟨rfl, rfl⟩ := (lowerMatrix_eq_iff a b p q hp).mp h
    rfl
  · obtain ⟨ha, rfl, rfl⟩ := (lowerMatrix_eq_upperMatrix_iff a b p q hp).mp h
    change baseProductChart false (a, lowerMap a p) =
      baseProductChart true (a⁻¹, upperMap a⁻¹ (a * p.1, a * p.2))
    rw [upper_lower_compatibility a ha p]
    exact Prod.ext (RiemannSphere.standardCharts.affineMap_inversion false a ha) rfl
  · obtain ⟨hb, rfl, rfl⟩ := (lowerMatrix_eq_upperMatrix_iff b a q p hq).mp h.symm
    change baseProductChart true (b⁻¹, upperMap b⁻¹ (b * q.1, b * q.2)) =
      baseProductChart false (b, lowerMap b q)
    rw [upper_lower_compatibility b hb q]
    exact Prod.ext (RiemannSphere.standardCharts.affineMap_inversion false b hb).symm rfl
  · obtain ⟨rfl, rfl⟩ := (upperMatrix_eq_iff a b p q hp).mp h
    rfl

theorem fibreEquiv_symm_ne_zero (b : Bool) (a : ℂ) {v : Fibre} (hv : v ≠ 0) :
    (fibreEquiv b a).symm v ≠ 0 := by
  intro h
  apply hv
  calc
    v = fibreEquiv b a ((fibreEquiv b a).symm v) :=
      ((fibreEquiv b a).apply_symm_apply v).symm
    _ = fibreEquiv b a 0 := congrArg (fibreEquiv b a) h
    _ = 0 := map_zero (fibreEquiv b a)

/-- The actual global product map has no collisions off the zero section. -/
theorem productMap_injOn : InjOn productMap {p : RiemannSphere × Fibre | p.2 ≠ 0} := by
  intro p hp q hq h
  obtain ⟨i, ⟨a, v⟩, rfl⟩ := baseProductChart_cover p
  obtain ⟨j, ⟨b, w⟩, rfl⟩ := baseProductChart_cover q
  have hv : v ≠ 0 := hp
  have hw : w ≠ 0 := hq
  rw [productMap_baseProductChart, productMap_baseProductChart] at h
  have he := baseProductChart_eq_of_chartMatrix_eq i j a b
    ((fibreEquiv i a).symm v) ((fibreEquiv j b).symm w)
    (fibreEquiv_symm_ne_zero i a hv) (fibreEquiv_symm_ne_zero j b hw) h
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using he

/-- Every actual determinant-zero matrix is attained by the original global map. -/
theorem exists_productMap_of_det_zero (M : MatrixSpace) (hdet : M.det = 0) :
    ∃ p : RiemannSphere × Fibre, productMap p = M := by
  obtain ⟨a, v, hv⟩ | ⟨a, v, hv⟩ := exists_matrix_chart_of_det_zero M hdet
  · refine ⟨baseProductChart false (a, lowerMap a v), ?_⟩
    rw [productMap_baseProductChart]
    change lowerMatrix a (lowerInverse a (lowerMap a v)) = M
    rw [lowerInverse_lowerMap, hv]
  · refine ⟨baseProductChart true (a, upperMap a v), ?_⟩
    rw [productMap_baseProductChart]
    change upperMatrix a (upperInverse a (upperMap a v)) = M
    rw [upperInverse_upperMap, hv]

theorem productMap_eq_zero_iff (p : RiemannSphere × Fibre) :
    productMap p = 0 ↔ p.2 = 0 := by
  constructor
  · intro h
    apply (radiusSq_eq_zero_iff p.2).mp
    rw [← frobeniusSq_productMap, h]
    simp [frobeniusSq]
  · intro h
    obtain ⟨b, q, rfl⟩ := baseProductChart_cover p
    have hq : q.2 = 0 := h
    rw [productMap_baseProductChart]
    unfold normalChartMatrix
    rw [hq, map_zero]
    cases b
    · exact lowerMatrix_zero q.1
    · exact upperMatrix_zero q.1

theorem range_productMap : range productMap = {M : MatrixSpace | M.det = 0} := by
  ext M
  constructor
  · rintro ⟨p, rfl⟩
    exact productMap_det p
  · exact exists_productMap_of_det_zero M

/-- The genuine toric matrix map is injective away from its original middle curve. -/
theorem toricMap_injOn : InjOn toricMap
    {y : toricNeighborhood | (toricNeighborhoodDiffeomorph.symm y).2 ≠ 0} := by
  intro y hy z hz he
  apply toricNeighborhoodDiffeomorph.symm.injective
  exact productMap_injOn hy hz he

theorem exists_toricMap_of_det_zero (M : MatrixSpace) (hdet : M.det = 0) :
    ∃ y : toricNeighborhood, toricMap y = M := by
  obtain ⟨p, hp⟩ := exists_productMap_of_det_zero M hdet
  refine ⟨toricNeighborhoodDiffeomorph p, ?_⟩
  simpa only [toricMap, toricNeighborhoodDiffeomorph.symm_apply_apply] using hp

theorem toricMap_eq_zero_iff (y : toricNeighborhood) :
    toricMap y = 0 ↔ (toricNeighborhoodDiffeomorph.symm y).2 = 0 :=
  productMap_eq_zero_iff (toricNeighborhoodDiffeomorph.symm y)

/-- Its zero fibre is exactly the unchanged original embedded toric middle curve. -/
theorem toricMap_eq_zero_iff_mem_zeroSection (y : toricNeighborhood) :
    toricMap y = 0 ↔ (y : ToricSpace.Space) ∈ range toricZeroSection :=
  (toricMap_eq_zero_iff y).trans
    (toricNeighborhoodHomeomorph_inverse_fibre_zero_iff y)

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization.Conifold
