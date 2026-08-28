import Wikipedia.HopfProblem.ConifoldPolarNativeFramingDefs

/-!
# The original normal coordinates of the normalized smoothing matrix

The second column of the quaternionic deformation is the original two-complex
normal vector in both native charts.  On the unit normal sphere, the explicit
radius-two smoothing has exactly this quaternionic matrix as its unitary factor.
-/

noncomputable section

open scoped ComplexConjugate

namespace Wikipedia.HopfProblem.ConifoldPolar.NativeFraming

open ConifoldStandardBoundary CuspCircleNormalTrivialization

private theorem deform_lowerMatrix_secondColumn (a : ℂ) (v : Fibre) (i : Fin 2) :
    deform 1 (Conifold.lowerMatrix a v) i 1 = ![(lowerMap a v).1, (lowerMap a v).2] i := by
  fin_cases i <;>
    simp [deform, adjointAdjugate_entries, Conifold.lowerMatrix, lowerMap, sub_eq_add_neg]

private theorem deform_upperMatrix_secondColumn (a : ℂ) (v : Fibre) (i : Fin 2) :
    deform 1 (Conifold.upperMatrix a v) i 1 = ![(upperMap a v).1, (upperMap a v).2] i := by
  fin_cases i <;>
    simp [deform, adjointAdjugate_entries, Conifold.upperMatrix, upperMap, sub_eq_add_neg]

/-- Deforming the original conifold matrix recovers the unchanged native normal vector. -/
theorem deform_productMap_secondColumn (p : RiemannSphere × Fibre) (i : Fin 2) :
    deform 1 (Conifold.productMap p) i 1 = ![p.2.1, p.2.2] i := by
  obtain ⟨b, ⟨a, v⟩, rfl⟩ := baseProductChart_cover p
  rw [Conifold.productMap_baseProductChart]
  change deform 1 (Conifold.normalChartMatrix b (a, v)) i 1 = ![v.1, v.2] i
  cases b
  · change deform 1 (Conifold.lowerMatrix a (lowerInverse a v)) i 1 = ![v.1, v.2] i
    rw [deform_lowerMatrix_secondColumn, lowerMap_lowerInverse]
  · change deform 1 (Conifold.upperMatrix a (upperInverse a v)) i 1 = ![v.1, v.2] i
    rw [deform_upperMatrix_secondColumn, upperMap_upperInverse]

private theorem two_productMap_det (p : RiemannSphere × Fibre) :
    ((2 : ℂ) • Conifold.productMap p).det = 0 := by
  rw [Matrix.det_smul, Conifold.productMap_det, mul_zero]

private theorem frobeniusSq_two_productMap (p : RiemannSphere × Fibre)
    (hp : radiusSq p.2 = 1) :
    frobeniusSq ((2 : ℂ) • Conifold.productMap p) = (2 : ℝ) ^ 2 := by
  change frobeniusSq (((2 : ℝ) : ℂ) • Conifold.productMap p) = (2 : ℝ) ^ 2
  rw [frobeniusSq_smul, Conifold.frobeniusSq_productMap, hp, mul_one]

/-- The normalized smoothing has determinant one on the original unit normal sphere. -/
theorem det_normalizedMatrix (p : RiemannSphere × Fibre) (hp : radiusSq p.2 = 1) :
    (normalizedMatrix p).det = 1 :=
  det_forward (by norm_num : (1 : ℝ) < 2)
    (two_productMap_det p) (frobeniusSq_two_productMap p hp)

/-- Radius-two normalization preserves exactly the original quaternionic normal matrix. -/
theorem unitaryPart_normalizedMatrix (p : RiemannSphere × Fibre)
    (hp : radiusSq p.2 = 1) :
    unitaryPart (normalizedMatrix p) = deform 1 (Conifold.productMap p) := by
  rw [normalizedMatrix, unitaryPart_forward (by norm_num : (1 : ℝ) < 2)
    _ (two_productMap_det p) (frobeniusSq_two_productMap p hp)]
  change (((2 : ℝ)⁻¹ : ℝ) : ℂ) •
    deform 1 (((2 : ℝ) : ℂ) • Conifold.productMap p) = _
  rw [deform_smul, smul_smul]
  norm_num

/-- The polar normal coordinates are literally the pre-existing real-four coordinate map. -/
theorem normalCoordinates_unitaryPart_normalizedMatrix (p : RiemannSphere × Fibre)
    (hp : radiusSq p.2 = 1) :
    normalCoordinates (unitaryPart (normalizedMatrix p)) = RealFour.coordinateEquiv p.2 := by
  rw [unitaryPart_normalizedMatrix p hp]
  simp only [normalCoordinates, deform_productMap_secondColumn]
  rfl

end Wikipedia.HopfProblem.ConifoldPolar.NativeFraming
