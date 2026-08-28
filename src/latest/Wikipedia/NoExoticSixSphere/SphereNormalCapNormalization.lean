import Wikipedia.NoExoticSixSphere.SphereNormalHomology
import Wikipedia.NoExoticSixSphere.ProductNormalCohomologyClass
import Wikipedia.NoExoticSixSphere.ManifoldCompactSupportDuality
import Wikipedia.NoExoticSixSphere.SphereCompactificationChart

/-!
# Original cap normalization for the sphere normal-product class

The original cap is injective by the proved manifold duality theorem.
The actual normal-fiber class is nonzero, so its cap is nonzero. The
original zero-section equivalence shows that the actual middle homology
of this product has only one nonzero class. This identifies the cap with
the zero-section class, without a cross-product hypothesis.

For the standard three-dimensional fiber, a six-dimensional model atlas
is constructed from the original sphere-product charts by the fixed
Euclidean block homeomorphism. The underlying topology and zero-section
maps are unchanged. No candidate six-sphere atlas is replaced.
-/

noncomputable section

open Wikipedia.HopfProblem.SphereHomologyCoefficients

namespace NoExoticSixSphere.SphereNormalCapNormalization

section GeneralModel

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [Fact (Module.finrank ℝ V = (3 + 2) + 1)]
  (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = (0 + 2) + 1)]
  [ChartedSpace V (Sphere 3 × E)]

/-- Original cap of the constructed normal-fiber class is the actual zero-section class. -/
theorem cap_normalClass :
    CompactSupportCapMap.dualityMap (E := V) 3 (Sphere 3 × E) 3 3 rfl
        (ProductNormalCohomologyClass.normalClass E 0 (Sphere 3)) =
      SphereNormalHomology.zeroSectionClass E := by
  apply SphereNormalHomology.eq_zeroSectionClass_of_ne_zero
  intro he
  apply ProductNormalCohomologyClass.normalClass_ne_zero E 0 (Sphere 3) (spherePole 3)
  exact (CompactSupportCapMap.manifold_bijective (E := V) 3 (Sphere 3 × E) 3 3 rfl).1
    (he.trans (CompactSupportCapMap.dualityMap (E := V) 3 (Sphere 3 × E) 3 3 rfl).map_zero.symm)

end GeneralModel

/-- The fixed standard normal vector space. -/
abbrev NormalVector := EuclideanSpace ℝ (Fin 3)

/-- The fixed six-dimensional ambient chart model. -/
abbrev AmbientVector := EuclideanSpace ℝ (Fin 6)

/-- The fixed Euclidean block coordinates for the original product model topology. -/
def modelHomeomorph : AmbientVector ≃ₜ ModelProd NormalVector NormalVector :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 3) (m := 3)).toHomeomorph

/-- The original product charts, composed with the fixed Euclidean block coordinates. -/
@[instance_reducible]
def productChartedSpace : ChartedSpace AmbientVector (Sphere 3 × NormalVector) := by
  let : ChartedSpace AmbientVector (ModelProd NormalVector NormalVector) :=
    modelHomeomorph.chartedSpace
  exact ChartedSpace.comp AmbientVector (ModelProd NormalVector NormalVector)
    (Sphere 3 × NormalVector)

attribute [local instance] productChartedSpace

local instance normalDimension : Fact (Module.finrank ℝ NormalVector = (0 + 2) + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

local instance ambientDimension : Fact (Module.finrank ℝ AmbientVector = (3 + 2) + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- Original compact-support cap in the constructed six-dimensional product atlas. -/
def standardCap : CompactSupportCohomology.Cohomology (Sphere 3 × NormalVector) 3 →ₗ[ℤ]
    ModHomology 2 (Sphere 3 × NormalVector) 3 :=
  CompactSupportCapMap.dualityMap (E := AmbientVector) 3 (Sphere 3 × NormalVector) 3 3 rfl

/-- The standard normal-product normalization, with the model atlas and dimensions constructed. -/
theorem standardCap_normalClass :
    standardCap (ProductNormalCohomologyClass.normalClass NormalVector 0 (Sphere 3)) =
      SphereNormalHomology.zeroSectionClass NormalVector :=
  cap_normalClass (V := AmbientVector) NormalVector

end NoExoticSixSphere.SphereNormalCapNormalization
