import Wikipedia.HopfProblem.CuspCircleNormalTrivializationConifoldComparison

/-!
# The explicit unit normal direction in the boundary comparison

Real radial dilation commutes with the original small-resolution matrix
map. On radius `r`, the normal vector `F/r` therefore has literal squared
radius one and gives the matrix divided by `r`. The normalized smoothing
map is exactly the radius-two deformation of twice this unit-direction
matrix, with no lower bound on the positive native radius.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization.Conifold

open ConifoldStandardBoundary

theorem lowerMatrix_real_smul (a : ℂ) (t : ℝ) (p : Fibre) :
    lowerMatrix a (t • p) = (t : ℂ) • lowerMatrix a p := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerMatrix, Complex.real_smul] <;> ring

theorem upperMatrix_real_smul (a : ℂ) (t : ℝ) (p : Fibre) :
    upperMatrix a (t • p) = (t : ℂ) • upperMatrix a p := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperMatrix, Complex.real_smul] <;> ring

theorem chartMatrix_real_smul (b : Bool) (a : ℂ) (t : ℝ) (p : Fibre) :
    chartMatrix b a (t • p) = (t : ℂ) • chartMatrix b a p := by
  cases b
  · exact lowerMatrix_real_smul a t p
  · exact upperMatrix_real_smul a t p

theorem normalChartMatrix_real_smul (b : Bool) (a : ℂ) (t : ℝ) (v : Fibre) :
    normalChartMatrix b (a, t • v) = (t : ℂ) • normalChartMatrix b (a, v) := by
  change chartMatrix b a ((fibreEquiv b a).symm (t • v)) =
    (t : ℂ) • chartMatrix b a ((fibreEquiv b a).symm v)
  rw [map_smul, chartMatrix_real_smul]

/-- Real radial scaling gives literal scalar scaling of the original matrix. -/
theorem productMap_real_smul (t : ℝ) (p : RiemannSphere × Fibre) :
    productMap (p.1, t • p.2) = (t : ℂ) • productMap p := by
  obtain ⟨b, ⟨a, v⟩, rfl⟩ := baseProductChart_cover p
  change productMap (baseProductChart b (a, t • v)) =
    (t : ℂ) • productMap (baseProductChart b (a, v))
  rw [productMap_baseProductChart, productMap_baseProductChart,
    normalChartMatrix_real_smul]

theorem radiusSq_real_smul (t : ℝ) (v : Fibre) :
    radiusSq (t • v) = t ^ 2 * radiusSq v := by
  simp only [radiusSq, Prod.smul_fst, Prod.smul_snd, Complex.real_smul,
    Complex.normSq_mul, Complex.normSq_ofReal]
  ring

/-- Dividing the actual radius-r normal vector by r gives a unit normal vector. -/
theorem radiusSq_unit_normal {r : ℝ} (hr : r ≠ 0) {v : Fibre}
    (hv : radiusSq v = r ^ 2) : radiusSq ((r⁻¹ : ℝ) • v) = 1 := by
  rw [radiusSq_real_smul, hv, ← mul_pow, inv_mul_cancel₀ hr, one_pow]

/-- The actual unit-direction point of the product normal sphere. -/
def productBoundaryUnitDirection {r : ℝ} (hr : r ≠ 0) (p : ProductBoundary r) :
    ProductBoundary 1 :=
  ⟨(p.val.1, (r⁻¹ : ℝ) • p.val.2), by
    simpa only [one_pow] using radiusSq_unit_normal hr p.property⟩

@[simp] theorem productBoundaryUnitDirection_val {r : ℝ} (hr : r ≠ 0)
    (p : ProductBoundary r) :
    (productBoundaryUnitDirection hr p).val = (p.val.1, (r⁻¹ : ℝ) • p.val.2) := rfl

theorem productMap_productBoundaryUnitDirection {r : ℝ} (hr : r ≠ 0)
    (p : ProductBoundary r) :
    productMap (productBoundaryUnitDirection hr p).val =
      ((r⁻¹ : ℝ) : ℂ) • productMap p.val :=
  productMap_real_smul r⁻¹ p.val

/-- The radius-two normalization retains exactly twice the unit-direction matrix. -/
theorem rescaleMatrix_eq_two_unitDirection (r : ℝ) (p : RiemannSphere × Fibre) :
    rescaleMatrix r 2 (productMap p) =
      (2 : ℂ) • productMap (p.1, (r⁻¹ : ℝ) • p.2) := by
  rw [rescaleMatrix, productMap_real_smul, smul_smul]
  have hc : ((2 / r : ℝ) : ℂ) = (2 : ℂ) * ((r⁻¹ : ℝ) : ℂ) := by
    norm_num [div_eq_mul_inv, Complex.ofReal_mul]
  exact congrArg (fun t : ℂ => t • productMap p) hc

/-- The normalized comparison written on the literal product boundary. -/
def normalizedProductBoundaryHomeomorph {r : ℝ} (hr : 0 < r) :
    ProductBoundary r ≃ₜ SmoothingBoundary 2 :=
  (productBoundaryHomeomorph (ne_of_gt hr)).trans (normalizedBoundaryHomeomorph hr)

@[simp] theorem normalizedProductBoundaryHomeomorph_apply_val {r : ℝ} (hr : 0 < r)
    (p : ProductBoundary r) :
    (normalizedProductBoundaryHomeomorph hr p).val =
      forward 2 (rescaleMatrix r 2 (productMap p.val)) := rfl

/-- The actual normalized map retains the original unit normal `F/r` explicitly. -/
theorem normalizedProductBoundaryHomeomorph_unitDirection {r : ℝ} (hr : 0 < r)
    (p : ProductBoundary r) :
    (normalizedProductBoundaryHomeomorph hr p).val =
      forward 2 ((2 : ℂ) • productMap (p.val.1, (r⁻¹ : ℝ) • p.val.2)) := by
  rw [normalizedProductBoundaryHomeomorph_apply_val, rescaleMatrix_eq_two_unitDirection]

theorem normalizedProductBoundaryHomeomorph_circle {r : ℝ} (hr : 0 < r)
    (u : ℂ) (hu : ‖u‖ = 1) (p : ProductBoundary r) :
    normalizedProductBoundaryHomeomorph hr (productBoundaryCircle u hu p) =
      smoothingCircle u hu (normalizedProductBoundaryHomeomorph hr p) := by
  change normalizedBoundaryHomeomorph hr
      (productBoundaryHomeomorph (ne_of_gt hr) (productBoundaryCircle u hu p)) =
    smoothingCircle u hu
      (normalizedBoundaryHomeomorph hr (productBoundaryHomeomorph (ne_of_gt hr) p))
  rw [productBoundaryHomeomorph_circle, normalizedBoundaryHomeomorph_circle]

/-- On the original toric radius level, the same explicit normal `F/r` has radius one. -/
theorem toricBoundary_unit_normal_radius {r : ℝ} (hr : r ≠ 0) (y : ToricBoundary r) :
    radiusSq ((r⁻¹ : ℝ) • (toricNeighborhoodDiffeomorph.symm y.val).2) = 1 :=
  radiusSq_unit_normal hr y.property

theorem normalizedToricBoundaryHomeomorph_unitDirection {r : ℝ} (hr : 0 < r)
    (y : ToricBoundary r) :
    (normalizedToricBoundaryHomeomorph hr y).val =
      forward 2 ((2 : ℂ) • productMap
        ((toricNeighborhoodDiffeomorph.symm y.val).1,
          (r⁻¹ : ℝ) • (toricNeighborhoodDiffeomorph.symm y.val).2)) := by
  rw [normalizedToricBoundaryHomeomorph_apply_val]
  change forward 2 (rescaleMatrix r 2 (productMap (toricNeighborhoodDiffeomorph.symm y.val))) = _
  rw [rescaleMatrix_eq_two_unitDirection]

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization.Conifold
