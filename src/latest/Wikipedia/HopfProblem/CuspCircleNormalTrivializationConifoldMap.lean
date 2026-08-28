import Wikipedia.HopfProblem.CuspCircleNormalTrivializationConifoldAlgebra
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationToricSmooth
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationEquivariance

/-!
# The genuine global conifold map on the original toric neighborhood

The matrix cocycle descends over the actual Riemann-sphere base and the
already proved native toric product diffeomorphism. The resulting map has
the original small-resolution matrix formula on both unchanged toric
inclusions. Its determinant is zero, and its squared Frobenius norm is
exactly the previously constructed normal radius.
-/

noncomputable section

open Set Topology OnePoint
open scoped ContDiff Manifold Matrix Matrix.Norms.Elementwise

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization.Conifold

open ToricCharts ConifoldStandardBoundary

/-- The original matrix in either affine toric chart. -/
def chartMatrix : Bool → ℂ → Fibre → MatrixSpace
  | false, a, p => lowerMatrix a p
  | true, a, p => upperMatrix a p

/-- Its expression in the actual real-trivial normal coordinates. -/
def normalChartMatrix (b : Bool) (q : Model) : MatrixSpace :=
  chartMatrix b q.1 ((fibreEquiv b q.1).symm q.2)

theorem normalChartMatrix_det (b : Bool) (q : Model) : (normalChartMatrix b q).det = 0 := by
  cases b
  · exact lowerMatrix_det _ _
  · exact upperMatrix_det _ _

theorem frobeniusSq_normalChartMatrix (b : Bool) (q : Model) :
    frobeniusSq (normalChartMatrix b q) = radiusSq q.2 := by
  cases b
  · exact frobeniusSq_lowerMatrix_lowerInverse _ _
  · exact frobeniusSq_upperMatrix_upperInverse _ _

theorem normalChartMatrix_unit_smul (b : Bool) (a u : ℂ) (hu : ‖u‖ = 1) (v : Fibre) :
    normalChartMatrix b (a, u • v) = rightCircle u (normalChartMatrix b (a, v)) := by
  cases b
  · exact lowerNormalMatrix_unit_smul a u hu v
  · exact upperNormalMatrix_unit_smul a u hu v

theorem contDiff_normalChartMatrix (b : Bool) {n : ℕ∞ω} :
    ContDiff ℝ n (normalChartMatrix b) := by
  cases b
  · exact contDiff_lowerNormalMatrix
  · exact contDiff_upperNormalMatrix

/-- The matrix on the genuine sphere/normal product, using the lower chart
at finite points and the upper chart at the actual point at infinity. -/
def productMap (p : RiemannSphere × Fibre) : MatrixSpace :=
  p.1.elim (normalChartMatrix true (0, p.2))
    (fun a => normalChartMatrix false (a, p.2))

@[simp] theorem productMap_coe (a : ℂ) (v : Fibre) :
    productMap ((a : RiemannSphere), v) = normalChartMatrix false (a, v) := rfl

@[simp] theorem productMap_infty (v : Fibre) :
    productMap ((∞ : RiemannSphere), v) = normalChartMatrix true (0, v) := rfl

/-- The original matrix cocycle proves the entire upper-chart formula. -/
theorem productMap_infinityParametrization (a : ℂ) (v : Fibre) :
    productMap (RiemannSphere.infinityParametrization a, v) =
      normalChartMatrix true (a, v) := by
  by_cases ha : a = 0
  · subst a
    rw [RiemannSphere.infinityParametrization_zero, productMap_infty]
  · rw [RiemannSphere.infinityParametrization_of_ne ha, productMap_coe]
    change lowerMatrix a⁻¹ (lowerInverse a⁻¹ v) = upperMatrix a (upperInverse a v)
    simpa only [inv_inv] using (normalMatrix_transition a⁻¹ (inv_ne_zero ha) v).symm

@[simp] theorem productMap_baseProductChart (b : Bool) (q : Model) :
    productMap (baseProductChart b q) = normalChartMatrix b q := by
  rcases q with ⟨a, v⟩
  cases b
  · rfl
  · exact productMap_infinityParametrization a v

theorem productMap_comp_baseProductChart (b : Bool) :
    productMap ∘ baseProductChart b = normalChartMatrix b :=
  funext (productMap_baseProductChart b)

theorem continuous_productMap : Continuous productMap := by
  apply continuous_of_comp_baseProductChart
  intro b
  rw [productMap_comp_baseProductChart]
  exact (contDiff_normalChartMatrix b (n := ω)).continuous

theorem productMap_det (p : RiemannSphere × Fibre) : (productMap p).det = 0 := by
  obtain ⟨b, q, rfl⟩ := baseProductChart_cover p
  rw [productMap_baseProductChart, normalChartMatrix_det]

theorem frobeniusSq_productMap (p : RiemannSphere × Fibre) :
    frobeniusSq (productMap p) = radiusSq p.2 := by
  obtain ⟨b, q, rfl⟩ := baseProductChart_cover p
  rw [productMap_baseProductChart, frobeniusSq_normalChartMatrix]
  rfl

/-- The actual scalar normal action becomes the original matrix column action. -/
theorem productMap_unit_smul (u : ℂ) (hu : ‖u‖ = 1) (p : RiemannSphere × Fibre) :
    productMap (p.1, u • p.2) = rightCircle u (productMap p) := by
  obtain ⟨b, ⟨a, v⟩, rfl⟩ := baseProductChart_cover p
  change productMap (baseProductChart b (a, u • v)) =
    rightCircle u (productMap (baseProductChart b (a, v)))
  rw [productMap_baseProductChart, productMap_baseProductChart,
    normalChartMatrix_unit_smul b a u hu]

/-- The genuine conifold map on the actual two-chart toric open submanifold. -/
def toricMap (y : toricNeighborhood) : MatrixSpace :=
  productMap (toricNeighborhoodDiffeomorph.symm y)

/-- On both native toric charts the map is exactly the original matrix. -/
@[simp] theorem toricMap_toricInclusion (b : Bool) (z : CoordinateSpace 3) :
    toricMap (toricInclusion b z) = chartMatrix b (z 1) (z 0, z 2) := by
  rw [toricMap, toricNeighborhoodDiffeomorph_symm_toricInclusion,
    productMap_baseProductChart]
  simp only [normalChartMatrix, chartCoordinates_apply,
    ContinuousLinearEquiv.symm_apply_apply]

theorem toricMap_lower (z : CoordinateSpace 3) :
    toricMap (toricInclusion false z) = !![z 0, z 2; z 1 * z 0, z 1 * z 2] :=
  toricMap_toricInclusion false z

theorem toricMap_upper (z : CoordinateSpace 3) :
    toricMap (toricInclusion true z) = !![z 1 * z 0, z 1 * z 2; z 0, z 2] :=
  toricMap_toricInclusion true z

theorem toricMap_det (y : toricNeighborhood) : (toricMap y).det = 0 :=
  productMap_det (toricNeighborhoodDiffeomorph.symm y)

/-- The Frobenius radius is the original global real-normal radius, not a new norm model. -/
theorem frobeniusSq_toricMap (y : toricNeighborhood) :
    frobeniusSq (toricMap y) = radiusSq (toricNeighborhoodDiffeomorph.symm y).2 :=
  frobeniusSq_productMap (toricNeighborhoodDiffeomorph.symm y)

theorem continuous_toricMap : Continuous toricMap :=
  continuous_productMap.comp toricNeighborhoodDiffeomorph.symm.continuous

/-- The unchanged native coordinate action multiplies the two original matrix
columns by its opposite weights. This identity holds for every complex unit. -/
theorem toricMap_toricInclusion_diagonal (b : Bool) (u : ℂˣ) (z : CoordinateSpace 3) :
    toricMap (toricInclusion b
      (SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.diagonal u z)) =
      rightCircle (u : ℂ) (toricMap (toricInclusion b z)) := by
  rw [toricMap_toricInclusion, toricMap_toricInclusion,
    SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.diagonal_apply]
  change chartMatrix b (z 1) ((u : ℂ)⁻¹ * z 0, (u : ℂ) * z 2) =
    rightCircle (u : ℂ) (chartMatrix b (z 1) (z 0, z 2))
  cases b
  · exact lowerMatrix_oppositeWeights (z 1) (u : ℂ) (z 0, z 2)
  · exact upperMatrix_oppositeWeights (z 1) (u : ℂ) (z 0, z 2)

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization.Conifold
