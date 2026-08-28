import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicVectorFieldsClassificationCuspComparison
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorUniquenessCusp

/-!
# Cusp regularity of any full extension of the native vertical field

Every sufficiently high original upper-half-plane point comes from the
actual logarithmic cusp cover. The analytic germs constructed on the
filled toric reference axis therefore represent any function agreeing
with the regular vertical field there.
-/

open Filter UpperHalfPlane
open scoped Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicVectorFields.Classification

open HolomorphicForms.Cusp

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- Cusp regularity is a consequence of the actual global field and
agreement on the actual regular locus; no boundedness or germ premise is used. -/
theorem regularVertical_cuspRegular (v : Threefold.HolomorphicVectorFields.Field)
    (H : ℍ → ComplexPlane₂)
    (hH : ∀ z : TriangleRegularPoint, H z = regularVertical v z) :
    ∀ i : Fin 2, MuTorsor.CuspRegular (fun z => H z i) := by
  intro i
  refine ⟨cuspGerm v i, cuspGerm_analyticAt_zero v i, ?_⟩
  filter_upwards [eventually_mem_actual_cusp] with z hz
  have hg := cuspGerm_log v (actualLogBase z hz) i
  have h := congrFun (hH (cuspRegularBase (actualLogBase z hz))) i
  rw [cuspRegularBase_actualLogBase] at h
  rw [exponential_actualLogBase] at hg
  exact h.trans hg

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicVectorFields.Classification
