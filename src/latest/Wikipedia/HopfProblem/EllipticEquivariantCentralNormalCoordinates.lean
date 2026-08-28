import Wikipedia.HopfProblem.EllipticEquivariantCentralImmersion
import Wikipedia.HopfProblem.EllipticEquivariantLocalModel
import Wikipedia.HopfProblem.EllipticBundleNormalCoordinates

/-!
# Actual central tangent images for arbitrary equivariant periods

The original base coordinate in the supplied family's charts, and the
proved central hyperplane equation in its quotient charts, force the
inclusion differentials to be vertical. Their genuine immersion normal
forms give injectivity, so these tangent images are the entire vertical
subspace. No concrete-family atlas is substituted.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.Elliptic.Equivariant.Data

variable {j : Kind} (D : Equivariant.Data j)

local notation "IS" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ FamilyModel

/-- The first chart coordinate is the original base coordinate for the
actual supplied varying-period family. -/
theorem familyProjection_chart (a x : D.TotalSpace) :
    letI := D.periods.totalChartedSpace
    x ∈ (chartAt FamilyModel a).source →
      (D.periods.projection x : ℂ) = (chartAt FamilyModel a x).1 := by
  let := D.periods.totalChartedSpace
  intro hx
  have h := D.familyProjection_chart_symm a (chartAt FamilyModel a x)
    ((chartAt FamilyModel a).map_source hx)
  rwa [(chartAt FamilyModel a).left_inv hx] at h

theorem centralInclusion_mfderiv_fst (x : D.centralPeriod.val.Torus) :
    letI := D.periods.totalChartedSpace
    ∀ w, (mfderiv IS IF D.centralInclusion x w).1 = 0 := by
  let := D.periods.totalChartedSpace
  apply NormalCoordinates.mfderiv_fst_eq_zero_of_eventually
    (D.centralInclusion_holomorphic.mdifferentiableAt (by simp))
  have hs : ∀ᶠ y in 𝓝 x,
      D.centralInclusion y ∈ (chartAt FamilyModel (D.centralInclusion x)).source :=
    D.centralInclusion_continuous.continuousAt
      ((chartAt FamilyModel (D.centralInclusion x)).open_source.mem_nhds
        (mem_chart_source FamilyModel (D.centralInclusion x)))
  filter_upwards [hs] with y hy
  rw [← D.familyProjection_chart (D.centralInclusion x) (D.centralInclusion y) hy,
    D.centralInclusion_projection]
  rfl

/-- The actual tangent image of the central torus in its varying family. -/
theorem centralInclusion_mfderiv_range (x : D.centralPeriod.val.Torus) :
    letI := D.periods.totalChartedSpace
    (mfderiv IS IF D.centralInclusion x).range = NormalLinear.vertical ComplexPlane₂ := by
  let := D.periods.totalChartedSpace
  exact NormalLinear.range_eq_vertical_of_injective _ (D.centralInclusion_mfderiv_fst x)
    (NormalImmersion.mfderiv_injective (D.centralInclusion_isImmersionOfComplement x))

theorem centralFibreInclusion_mfderiv_fst (v : Lattice) (hv : AdmissibleTwist j v)
    (x : Surface j D.centralPeriod v hv) :
    letI := D.chartedSpace v hv
    ∀ w, (mfderiv IS IF (D.centralFibreInclusion v hv) x w).1 = 0 := by
  let := D.chartedSpace v hv
  apply NormalCoordinates.mfderiv_fst_eq_zero_of_eventually
    ((D.centralFibreInclusion_holomorphic v hv).mdifferentiableAt (by simp))
  have hs : ∀ᶠ y in 𝓝 x, D.centralFibreInclusion v hv y ∈
      (chartAt FamilyModel (D.centralFibreInclusion v hv x)).source :=
    (D.centralFibreInclusion_continuous v hv).continuousAt
      ((chartAt FamilyModel (D.centralFibreInclusion v hv x)).open_source.mem_nhds
        (mem_chart_source FamilyModel (D.centralFibreInclusion v hv x)))
  filter_upwards [hs] with y hy
  exact (D.central_chart_iff v hv (D.centralFibreInclusion v hv x)
    (D.centralFibreInclusion v hv y) hy).mp (D.projection_centralFibreInclusion v hv y)

/-- The literal geometric normal quotient downstairs is by this actual
image of the inclusion differential in the selected quotient atlas. -/
theorem centralFibreInclusion_mfderiv_range (v : Lattice) (hv : AdmissibleTwist j v)
    (x : Surface j D.centralPeriod v hv) :
    letI := D.chartedSpace v hv
    (mfderiv IS IF (D.centralFibreInclusion v hv) x).range =
      NormalLinear.vertical ComplexPlane₂ := by
  let := D.chartedSpace v hv
  exact NormalLinear.range_eq_vertical_of_injective _ (D.centralFibreInclusion_mfderiv_fst v hv x)
    (NormalImmersion.mfderiv_injective (D.centralFibreInclusion_isImmersionOfComplement v hv x))

end Wikipedia.HopfProblem.Elliptic.Equivariant.Data
