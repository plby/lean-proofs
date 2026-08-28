import Wikipedia.NoExoticSixSphere.ManifoldFrameChartChainRule

/-!
# The global operator is the actual chart derivative plus identity normal columns

Both coordinate families are defined on the full original chart domains.
The block identity is an equality of actual continuous linear operators,
and does not require the spatial derivative to be injective at the center.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.FrameBlockCoordinates

open GLOrthonormalization ManifoldAffineSphereFamily SphereThreeTangentFrame

def identityBlockOperator (k : ℕ) {n N : ℕ} (A : Vector n →L[ℝ] Vector N) :
    Vector (k + n) →L[ℝ] Vector (k + N) :=
  (EuclideanSpace.finAddEquivProd (n := k) (m := N)).symm.toContinuousLinearMap.comp
    (((ContinuousLinearMap.fst ℝ (Vector k) (Vector n)).prod
      (A.comp (ContinuousLinearMap.snd ℝ (Vector k) (Vector n)))).comp
        EuclideanSpace.finAddEquivProd.toContinuousLinearMap)

theorem identityBlockOperator_apply (k : ℕ) {n N : ℕ} (A : Vector n →L[ℝ] Vector N)
    (v : Vector (k + n)) :
    identityBlockOperator k A v = EuclideanSpace.finAddEquivProd.symm
      ((EuclideanSpace.finAddEquivProd v).1, A (EuclideanSpace.finAddEquivProd v).2) := rfl

theorem identityBlockOperator_injective (k : ℕ) {n N : ℕ} (A : Vector n →L[ℝ] Vector N)
    (hi : Injective A) : Injective (identityBlockOperator k A) := by
  intro v w h
  apply (EuclideanSpace.finAddEquivProd (n := k) (m := n)).injective
  have he := congrArg (EuclideanSpace.finAddEquivProd (n := k) (m := N)) h
  simp only [identityBlockOperator_apply, ContinuousLinearEquiv.apply_symm_apply] at he
  have hfst := congrArg (fun p : Vector k × Vector N ↦ p.1) he
  have hsnd := congrArg (fun p : Vector k × Vector N ↦ p.2) he
  exact Prod.ext hfst (hi hsnd)

theorem continuous_identityBlockOperator {X : Type*} [TopologicalSpace X]
    (k : ℕ) {n N : ℕ} (A : X → Vector n →L[ℝ] Vector N) (hA : Continuous A) :
    Continuous (fun x ↦ identityBlockOperator k (A x)) := by
  apply continuous_clm_apply.mpr
  intro v
  exact EuclideanSpace.finAddEquivProd.symm.continuous.comp
    (continuous_const.prodMk (hA.clm_apply continuous_const))

def sourceCoordinates (k : ℕ) (s : SourceChart) (x : s.source) :
    Vector (k + 3) ≃L[ℝ] Vector (k + 3) :=
  EuclideanSpace.finAddEquivProd.trans
    (((ContinuousLinearEquiv.refl ℝ (Vector k)).prodCongr (chartCoordinates s x).symm).trans
      EuclideanSpace.finAddEquivProd.symm)

theorem sourceCoordinates_apply (k : ℕ) (s : SourceChart) (x : s.source)
    (v : Vector (k + 3)) :
    sourceCoordinates k s x v = EuclideanSpace.finAddEquivProd.symm
      ((EuclideanSpace.finAddEquivProd v).1,
        (chartCoordinates s x).symm (EuclideanSpace.finAddEquivProd v).2) := rfl

theorem continuous_sourceCoordinates (k : ℕ) (s : SourceChart) :
    Continuous (fun x : s.source ↦ (sourceCoordinates k s x).toContinuousLinearMap) := by
  apply continuous_clm_apply.mpr
  intro v
  change Continuous (fun x : s.source ↦ sourceCoordinates k s x v)
  simp_rw [sourceCoordinates_apply]
  exact EuclideanSpace.finAddEquivProd.symm.continuous.comp
    (continuous_const.prodMk ((continuous_inverse_chartCoordinates s).clm_apply continuous_const))

theorem sourceCoordinates_symm_apply (k : ℕ) (s : SourceChart) (x : s.source)
    (v : Vector (k + 3)) :
    (sourceCoordinates k s x).symm v = EuclideanSpace.finAddEquivProd.symm
      ((EuclideanSpace.finAddEquivProd v).1,
        chartCoordinates s x (EuclideanSpace.finAddEquivProd v).2) := by
  apply (sourceCoordinates k s x).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, sourceCoordinates_apply,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
  exact (EuclideanSpace.finAddEquivProd.symm_apply_apply v).symm

theorem continuous_inverse_sourceCoordinates (k : ℕ) (s : SourceChart) :
    Continuous (fun x : s.source ↦ (sourceCoordinates k s x).symm.toContinuousLinearMap) := by
  apply continuous_clm_apply.mpr
  intro v
  change Continuous (fun x : s.source ↦ (sourceCoordinates k s x).symm v)
  simp_rw [sourceCoordinates_symm_apply]
  exact EuclideanSpace.finAddEquivProd.symm.continuous.comp
    (continuous_const.prodMk ((continuous_chartCoordinates s).clm_apply continuous_const))

end NoExoticSixSphere.FrameBlockCoordinates

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization ManifoldAffineSphereFamily FrameBlockCoordinates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)

theorem normalSpatialOperator_in_charts (g : ℝ → Sphere 3 → M)
    (hg : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 6) ∞ (uncurry g))
    (s : SourceChart) (c : TargetChart 6 M) (p : ℝ × Sphere 3)
    (hs : p.2 ∈ s.source) (hc : g p.1 p.2 ∈ c.source) :
    e.normalSpatialOperator a g p =
      (e.normalChartCoordinates a c ⟨g p.1 p.2, hc⟩).toContinuousLinearMap.comp
        ((identityBlockOperator (e.ambientDimension - 6)
          (SphereFamily.spatialInCharts g s c p)).comp
            (sourceCoordinates (e.ambientDimension - 6) s ⟨p.2, hs⟩).toContinuousLinearMap) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [e.normalSpatialOperator_apply, e.familyTangentOperator_in_charts g hg s c p hs hc]
  change _ = e.normalChartOperator a c ⟨g p.1 p.2, hc⟩
    (identityBlockOperator (e.ambientDimension - 6) (SphereFamily.spatialInCharts g s c p)
      (sourceCoordinates (e.ambientDimension - 6) s ⟨p.2, hs⟩ v))
  rw [sourceCoordinates_apply, identityBlockOperator_apply,
    ContinuousLinearEquiv.apply_symm_apply, e.normalChartOperator_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  rfl

end NoExoticSixSphere.EuclideanEmbedding
