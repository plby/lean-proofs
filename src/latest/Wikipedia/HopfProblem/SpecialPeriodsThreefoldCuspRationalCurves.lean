import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspFibreGeometryStrata
import Wikipedia.HopfProblem.CuspRationalCurves

/-!
# The three rational double curves in the constructed threefold

The original two-axis parametrizations of the native cusp give actual
holomorphic embeddings of the Riemann sphere into the glued threefold.
Their images are exactly its three double curves, and their zero and
infinity endpoints are exactly the two global triple points. These are
curves in the cusp fibre, not three global surface components.
-/

noncomputable section

open Function Set Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspGeometry

open ToricCharts

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

attribute [local instance] nativeChartedSpace Threefold.chartedSpace Threefold.space_t2Space

/-- The genuine native sphere parametrization followed by the actual
open inclusion of the full cusp piece into the glued threefold. -/
def doubleCurveParametrization (i : Fin 3) : RiemannSphere → Threefold.Space :=
  inclusion ∘ CuspQuotient.sphereParametrization data.correction data.radius
    data.radius_pos data.radius_lt_one data.holomorphic data.smallDrift i

theorem doubleCurveParametrization_continuous (i : Fin 3) :
    Continuous (doubleCurveParametrization i) :=
  inclusion_continuous.comp
    (CuspQuotient.sphereParametrization_isEmbedding data.correction data.radius
      data.radius_pos data.radius_lt_one data.holomorphic data.smallDrift i).continuous

/-- Holomorphy uses the unchanged native cusp atlas and the actual
glued manifold atlas. -/
theorem doubleCurveParametrization_holomorphic (i : Fin 3) :
    ContMDiff 𝓘(ℂ) IF ω (doubleCurveParametrization i) :=
  inclusion_holomorphic.comp
    (CuspQuotient.sphereParametrization_holomorphic data.correction data.radius
      data.radius_pos data.radius_lt_one data.holomorphic data.smallDrift i)

theorem doubleCurveParametrization_isEmbedding (i : Fin 3) :
    IsEmbedding (doubleCurveParametrization i) :=
  inclusion_openEmbedding.isEmbedding.comp
    (CuspQuotient.sphereParametrization_isEmbedding data.correction data.radius
      data.radius_pos data.radius_lt_one data.holomorphic data.smallDrift i)

theorem doubleCurveParametrization_isClosedEmbedding (i : Fin 3) :
    IsClosedEmbedding (doubleCurveParametrization i) :=
  (doubleCurveParametrization_continuous i).isClosedEmbedding
    (doubleCurveParametrization_isEmbedding i).injective

theorem doubleCurveParametrization_proper (i : Fin 3) :
    IsProperMap (doubleCurveParametrization i) :=
  (doubleCurveParametrization_continuous i).isProperMap

/-- Each parametrization covers exactly its literal global double curve. -/
theorem doubleCurveParametrization_range (i : Fin 3) :
    range (doubleCurveParametrization i) = doubleCurve i := by
  have hr : range (CuspQuotient.sphereParametrization data.correction data.radius
      data.radius_pos data.radius_lt_one data.holomorphic data.smallDrift i :
        RiemannSphere → LocalSpace) =
      CuspQuotient.doubleCurve data.correction data.radius data.radius_pos i :=
    CuspQuotient.sphereParametrization_range data.correction data.radius
      data.radius_pos data.radius_lt_one data.holomorphic data.smallDrift i
  exact (Set.range_comp inclusion _).trans (congrArg (Set.image inclusion) hr)

theorem doubleCurveParametrization_mem (i : Fin 3) (z : RiemannSphere) :
    doubleCurveParametrization i z ∈ doubleCurve i := by
  rw [← doubleCurveParametrization_range]
  exact mem_range_self z

@[simp] theorem projectionSphere_doubleCurveParametrization (i : Fin 3)
    (z : RiemannSphere) :
    Threefold.projectionSphere (doubleCurveParametrization i z) = (∞ : RiemannSphere) :=
  doubleCurve_subset_sphereCuspFibre i (doubleCurveParametrization_mem i z)

@[simp] theorem doubleCurveParametrization_zero (i : Fin 3) :
    doubleCurveParametrization i ((0 : ℂ) : RiemannSphere) = lowerTriplePoint :=
  congrArg inclusion (CuspQuotient.curveSphereHomeomorph_zero data.correction data.radius
    data.radius_pos data.radius_lt_one data.holomorphic data.smallDrift i)

@[simp] theorem doubleCurveParametrization_infty (i : Fin 3) :
    doubleCurveParametrization i (∞ : RiemannSphere) = upperTriplePoint :=
  congrArg inclusion (CuspQuotient.curveSphereHomeomorph_infty data.correction data.radius
    data.radius_pos data.radius_lt_one data.holomorphic data.smallDrift i)

/-- No additional point of any sphere parametrizes a triple point. -/
theorem doubleCurveParametrization_mem_tripleStratum_iff (i : Fin 3)
    (z : RiemannSphere) :
    doubleCurveParametrization i z ∈ tripleStratum ↔
      z = ((0 : ℂ) : RiemannSphere) ∨ z = (∞ : RiemannSphere) := by
  rw [tripleStratum_eq_pair, mem_insert_iff, mem_singleton_iff,
    ← doubleCurveParametrization_zero i, ← doubleCurveParametrization_infty i]
  simp only [(doubleCurveParametrization_isEmbedding i).injective.eq_iff]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspGeometry
