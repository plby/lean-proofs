import Wikipedia.HopfProblem.AffineBlowupManifold
import Wikipedia.HopfProblem.AffineBlowupTopology
import Wikipedia.HopfProblem.AffineSphereImmersion

/-!
# The exceptional curve is an embedded holomorphic sphere

The inclusion of the exceptional Riemann sphere is holomorphic and a closed
topological embedding. Its explicit coordinate normal forms also prove the
immersion property, including the point at infinity.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.AffineBlowup

open ToricCharts

def exceptionalCoordinates (b : Bool) (z : ℂ) : CoordinateSpace 2 :=
  if b then ![0, z] else ![z, 0]

theorem exceptionalInclusion_affineMap (b : Bool) (z : ℂ) :
    exceptionalInclusion (RiemannSphere.standardCharts.affineMap b z) =
      affineMap b (exceptionalCoordinates b z) := by
  cases b <;> apply Subtype.ext <;> apply Prod.ext
  · ext j
    fin_cases j <;> simp [exceptionalInclusion, affineMap, exceptionalCoordinates, left]
  · rfl
  · ext j
    fin_cases j <;> simp [exceptionalInclusion, affineMap, exceptionalCoordinates, right]
  · rfl

theorem exceptionalCoordinates_holomorphic (b : Bool) :
    ContDiff ℂ ω (exceptionalCoordinates b) := by
  apply contDiff_pi.mpr
  intro j
  cases b <;> fin_cases j
  · exact contDiff_id
  · exact contDiff_const
  · exact contDiff_const
  · exact contDiff_id

theorem exceptionalInclusion_holomorphic :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ (CoordinateSpace 2))
      ω exceptionalInclusion := by
  apply RiemannSphere.standardCharts.contMDiff_of_comp_affineMaps
  intro b
  have he : exceptionalInclusion ∘ RiemannSphere.standardCharts.affineMap b =
      affineMap b ∘ exceptionalCoordinates b := by
    funext z
    exact exceptionalInclusion_affineMap b z
  rw [he]
  exact (affineMap_holomorphic b).comp (exceptionalCoordinates_holomorphic b).contMDiff

theorem exceptionalInclusion_isClosedEmbedding : IsClosedEmbedding exceptionalInclusion :=
  exceptionalSet_isClosed.isClosedEmbedding_subtypeVal.comp exceptionalHomeomorph.isClosedEmbedding

def exceptionalCoordinateJoin (b : Bool) : (ℂ × ℂ) ≃L[ℂ] CoordinateSpace 2 :=
  if b then (ContinuousLinearEquiv.prodComm ℂ ℂ ℂ).trans
    (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm
  else (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm

@[simp] theorem exceptionalCoordinateJoin_apply_zero (b : Bool) (z : ℂ) :
    exceptionalCoordinateJoin b (z, 0) = exceptionalCoordinates b z := by
  cases b <;> rfl

theorem exceptionalAffine_isImmersionOfComplement (b : Bool) :
    Manifold.IsImmersionOfComplement ℂ (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω
      (exceptionalInclusion ∘ RiemannSphere.standardCharts.affineMap b) := by
  intro z
  refine Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    (continuous_exceptionalInclusion.comp
      (RiemannSphere.standardCharts.affineMap_isOpenEmbedding b).continuous).continuousAt
    (exceptionalCoordinateJoin b) (OpenPartialHomeomorph.refl ℂ) (parametrization b).symm
    (mem_univ z) ?_ ?_ ?_ ?_
  · change exceptionalInclusion (RiemannSphere.standardCharts.affineMap b z) ∈ affineTarget b
    rw [exceptionalInclusion_affineMap]
    exact affineMap_mem_target b _
  · simpa only [chartAt_self_eq] using IsManifold.chart_mem_maximalAtlas
      (I := modelWithCornersSelf ℂ ℂ) (n := ω) z
  · exact IsManifold.subset_maximalAtlas (mem_range_self b)
  · intro w _
    change (parametrization b).symm
      (exceptionalInclusion (RiemannSphere.standardCharts.affineMap b w)) =
        exceptionalCoordinateJoin b (w, 0)
    rw [exceptionalInclusion_affineMap, parametrization_symm_affineMap,
      exceptionalCoordinateJoin_apply_zero]

theorem exceptionalInclusion_isImmersionOfComplement :
    Manifold.IsImmersionOfComplement ℂ (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω exceptionalInclusion :=
  RiemannSphere.standardCharts.immersion_of_comp_affineMaps _
    continuous_exceptionalInclusion exceptionalAffine_isImmersionOfComplement

theorem exceptionalInclusion_isImmersion :
    Manifold.IsImmersion (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω exceptionalInclusion :=
  exceptionalInclusion_isImmersionOfComplement.isImmersion

end Wikipedia.HopfProblem.AffineBlowup
