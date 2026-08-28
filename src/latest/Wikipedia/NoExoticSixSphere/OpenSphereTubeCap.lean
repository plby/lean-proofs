import Wikipedia.NoExoticSixSphere.SphereNormalCapNormalization
import Wikipedia.NoExoticSixSphere.CompactSupportCapOpenEmbedding
import Wikipedia.NoExoticSixSphere.MiddleCapEvaluationPairing

/-!
# Cap of the original normal class extended through an actual sphere tube

Extend the constructed normal class along a supplied genuine open
embedding of the sphere normal product. Original cap naturality and
the proved product normalization identify its cap with the original
homology class of the core sphere. For a compact target, the absolute
class therefore computes cap-evaluation pairing with that core.
Equality with a geometric intersection count is still not asserted.
-/

noncomputable section

open Wikipedia.HopfProblem.SphereHomologyCoefficients
open scoped Topology

namespace NoExoticSixSphere.OpenSphereTubeCap

open SphereNormalCapNormalization

attribute [local instance] productChartedSpace

local instance normalDimension : Fact (Module.finrank ℝ NormalVector = (0 + 2) + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

local instance ambientDimension : Fact (Module.finrank ℝ AmbientVector = (3 + 2) + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace AmbientVector M]
  (f : C(Sphere 3 × NormalVector, M)) (hf : Topology.IsOpenEmbedding f)

/-- The original sphere core of the supplied open tube. -/
def core : C(Sphere 3, M) := f.comp (SphereNormalHomology.zeroSection NormalVector)

/-- Extend the actual compact-supported normal class along this open embedding. -/
def compactClass : CompactSupportCohomology.Cohomology M 3 :=
  CompactSupportCohomology.openMap f hf 3
    (ProductNormalCohomologyClass.normalClass NormalVector 0 (Sphere 3))

/-- Its original cap is the native fundamental class image of the original core sphere. -/
theorem cap_compactClass :
    CompactSupportCapMap.dualityMap (E := AmbientVector) 3 M 3 3 rfl (compactClass f hf) =
      modHomologyMap 2 (core f) 3 (unitSphereModTopClass 2 2) := by
  apply (CompactSupportCapMap.dualityMap_openEmbedding (E := AmbientVector) 3 f hf
    3 3 rfl (ProductNormalCohomologyClass.normalClass NormalVector 0 (Sphere 3))).trans
  apply (congrArg (modHomologyMap 2 f 3) standardCap_normalClass).trans
  exact (LinearMap.congr_fun
    (modHomologyMap_comp 2 (SphereNormalHomology.zeroSection NormalVector) f 3)
    (unitSphereModTopClass 2 2)).symm

variable [CompactSpace M]

/-- The original absolute cohomology class of the extended compact-supported normal class. -/
def absoluteClass : ModTwoCapProduct.Cohomology M 3 :=
  CompactSupportCohomology.absoluteEquiv M 3 (compactClass f hf)

/-- Absolute cap retains the same original sphere class after forgetting compact support. -/
theorem cap_absoluteClass :
    ManifoldCapMap.dualityMap (E := AmbientVector) 3 M 3 3 rfl (absoluteClass f hf) =
      modHomologyMap 2 (core f) 3 (unitSphereModTopClass 2 2) :=
  (CompactSupportCapMap.dualityMap_eq_absolute (E := AmbientVector) 3 M 3 3 rfl
    (compactClass f hf)).symm.trans (cap_compactClass f hf)

variable [SimplyConnectedSpace M] (m : M) [Subsingleton (π_ 2 M m)]

/-- Pairing with this core is literal evaluation of its constructed original tube class. -/
theorem pairing_core (b : ModHomology 2 M 3) :
    MiddleCapEvaluation.pairing (E := AmbientVector) m
        (modHomologyMap 2 (core f) 3 (unitSphereModTopClass 2 2)) b =
      NativeModTwoMiddleEvaluation.evaluation m (absoluteClass f hf) b := by
  rw [← cap_absoluteClass f hf]
  exact MiddleCapEvaluation.pairing_cap (E := AmbientVector) m (absoluteClass f hf) b

end NoExoticSixSphere.OpenSphereTubeCap
