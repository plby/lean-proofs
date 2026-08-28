import Wikipedia.HopfProblem.SpecialPeriodsConstruction
import Wikipedia.HopfProblem.TrianglePeriodFamilyGeometry
import Wikipedia.HopfProblem.SpecialPeriodsCuspGlobalOverlapBase

/-!
# The actual constructed periods on the global cusp overlap

The global period map and cusp data constructed from a normalized sphere
equivalence give the two actual families used on a cusp overlap. Shrinking
the cusp radius preserves all three analytic corrections. The explicit
base identification multiplies the logarithm by the source cusp width,
so the already-proved cusp expansion identifies the full period points.

Only the normalized sphere equivalence and a positive common radius are
inputs. Period agreement and the regular covering are proved conclusions.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.CuspGlobalOverlap

open CuspUniformization CuspFamily

attribute [local instance] triangleCompactifiedChartedSpace

variable (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
  TriangleCompactifiedOrbitSpace RiemannSphere ω)
  (hπ : π triangleCuspPoint = (∞ : RiemannSphere))
  (h₀ : π (triangleOpenInclusion triangleOrbitCenterOne) = ((0 : ℂ) : RiemannSphere))
  (h₁ : π (triangleOpenInclusion triangleOrbitCenterTwo) = ((1 : ℂ) : RiemannSphere))

/-- The actual regular global family, supplied by the completed period
construction and its two proved generator laws. -/
def sphereRegularData : TrianglePeriodFamily.Data ℂ TriangleRegularPoint :=
  TrianglePeriodFamily.regularData (Construction.periodMapOfSphere π hπ h₀ h₁)
    (Construction.periodMapOfSphere_generator₁ π hπ h₀ h₁)
    (Construction.periodMapOfSphere_generator₂ π hπ h₀ h₁)

@[simp] theorem sphereRegularData_point (z : TriangleRegularPoint) :
    (sphereRegularData π hπ h₀ h₁).periods.point z =
      (Construction.periodMapOfSphere π hπ h₀ h₁).point (z : ℍ) := rfl

/-- The regular quotient covering is the actual one already proved for
the triangle action, not an additional overlap hypothesis. -/
theorem sphereRegularCovering :
    IsQuotientCoveringMap (sphereRegularData π hπ h₀ h₁).baseQuotient TriangleGroup :=
  TrianglePeriodFamily.regularCovering (Construction.periodMapOfSphere π hπ h₀ h₁)
    (Construction.periodMapOfSphere_generator₁ π hπ h₀ h₁)
    (Construction.periodMapOfSphere_generator₂ π hπ h₀ h₁)

variable (r : ℝ) (hr : 0 < r)
  (hrD : r ≤ (Construction.cuspDataOfSphere π hπ h₀ h₁).radius)

/-- The genuine cusp family restricted to a smaller positive radius. -/
def sphereCuspData : CuspFamily.Data :=
  (Construction.cuspDataOfSphere π hπ h₀ h₁).shrink r hr hrD

@[simp] theorem sphereCuspData_radius : (sphereCuspData π hπ h₀ h₁ r hr hrD).radius = r := rfl

@[simp] theorem sphereCuspData_correction :
    (sphereCuspData π hπ h₀ h₁ r hr hrD).correction =
      (Construction.cuspDataOfSphere π hπ h₀ h₁).correction := rfl

/-- The shrunk family retains the literal constructed period triple. -/
theorem sphereCuspData_periodPoint (s : LogBase r) :
    ((sphereCuspData π hπ h₀ h₁ r hr hrD).periods.point s).val =
      cuspPeriodPoint (Construction.cuspDataOfSphere π hπ h₀ h₁).μ
        (Construction.cuspDataOfSphere π hπ h₀ h₁).b
        (Construction.cuspDataOfSphere π hπ h₀ h₁).h (s : ℂ) := rfl

include hrD in
/-- The actual normalized logarithmic coordinate in the global cusp
formula is exactly the original logarithmic-base coordinate. -/
theorem spherePeriod_point (hrcap : r ≤ Triangle.cuspRadius Triangle.width) (s : LogBase r) :
    ((sphereRegularData π hπ h₀ h₁).periods.point
      (CuspFamily.logBaseToRegular r hrcap s)).val =
      cuspPeriodPoint (Construction.cuspDataOfSphere π hπ h₀ h₁).μ
        (Construction.cuspDataOfSphere π hπ h₀ h₁).b
        (Construction.cuspDataOfSphere π hπ h₀ h₁).h (s : ℂ) := by
  have hz : ‖Triangle.cuspQ (CuspFamily.logBaseToRegular r hrcap s : ℍ)‖ <
      (Construction.cuspDataOfSphere π hπ h₀ h₁).radius := by
    rw [CuspFamily.logBaseToRegular_cuspQ]
    exact ((mem_logBase r s).mp s.property).trans_le hrD
  have h := Construction.cuspDataOfSphere_periodPoint π hπ h₀ h₁
    (CuspFamily.logBaseToRegular r hrcap s : ℍ) hz
  rw [CuspFamily.logBaseToRegular_coe,
    mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr Triangle.width_ne_zero)] at h
  exact h

/-- The full admissible period-domain points of the global and local
families agree on the explicit overlap base. -/
theorem spherePeriod_agreement (hrcap : r ≤ Triangle.cuspRadius Triangle.width)
    (s : LogBase r) :
    (sphereRegularData π hπ h₀ h₁).periods.point (CuspFamily.logBaseToRegular r hrcap s) =
      (sphereCuspData π hπ h₀ h₁ r hr hrD).periods.point s := by
  apply Subtype.ext
  rw [sphereCuspData_periodPoint]
  exact spherePeriod_point π hπ h₀ h₁ r hrD hrcap s

/-- Exact equality of the period matrices on the common logarithmic base. -/
theorem spherePeriod_matrix (hrcap : r ≤ Triangle.cuspRadius Triangle.width) (s : LogBase r) :
    ((sphereRegularData π hπ h₀ h₁).periods.point
      (CuspFamily.logBaseToRegular r hrcap s)).val.matrix =
      ((sphereCuspData π hπ h₀ h₁ r hr hrD).periods.point s).val.matrix := by
  rw [spherePeriod_agreement π hπ h₀ h₁ r hr hrD hrcap s]

/-- The actual global left period block is the local logarithmic block. -/
theorem spherePeriod_leftBlock (hrcap : r ≤ Triangle.cuspRadius Triangle.width)
    (s : LogBase r) :
    ((sphereRegularData π hπ h₀ h₁).periods.point
      (CuspFamily.logBaseToRegular r hrcap s)).val.leftBlock =
      logarithmicPeriod (sphereCuspData π hπ h₀ h₁ r hr hrD).correction (s : ℂ) := by
  rw [spherePeriod_agreement π hπ h₀ h₁ r hr hrD hrcap s]
  exact (sphereCuspData π hπ h₀ h₁ r hr hrD).point_leftBlock s

end Wikipedia.HopfProblem.SpecialPeriods.CuspGlobalOverlap
