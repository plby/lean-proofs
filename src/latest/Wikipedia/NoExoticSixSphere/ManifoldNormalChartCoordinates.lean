import Wikipedia.NoExoticSixSphere.ManifoldFamilyGlobalFrame
import Wikipedia.NoExoticSixSphere.PartialDiffeomorphDifferential

/-!
# Actual ambient coordinates from a target chart and the given normal frame

The normal columns and the derivative of the embedding in an original target
chart form complementary subspaces. Their combined operator is a genuine
linear equivalence, continuous with continuous inverse throughout that chart.
No tangent or normal bundle trivialization is chosen pointwise without a
continuity proof.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M)
  (a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel)
  (c : PartialDiffeomorph (𝓡 n) (𝓡 n) M (Vector n) ∞)

def targetInverseChartDifferential (x : c.source) : Vector n ≃L[ℝ] Vector n :=
  (show IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ c.symm (c x.val) from
    ⟨c.symm, c.map_source x.property, fun _ _ ↦ rfl⟩).mfderivToContinuousLinearEquiv (by simp)

def chartEmbeddingDerivative (x : c.source) : Vector n →L[ℝ] Vector e.ambientDimension :=
  fderiv ℝ (e.toFun ∘ c.symm) (c x.val)

theorem chartEmbeddingDerivative_eq (x : c.source) :
    e.chartEmbeddingDerivative c x =
      (mfderiv (𝓡 n) (𝓡 e.ambientDimension) e.toFun x.val).comp
        (targetInverseChartDifferential c x).toContinuousLinearMap := by
  have hc := c.contMDiffOn_invFun.contMDiffAt
    (c.open_target.mem_nhds (c.map_source x.property))
  have h := mfderiv_comp (c x.val) (e.smooth.mdifferentiableAt (by simp))
    (hc.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at h
  change e.chartEmbeddingDerivative c x =
    (mfderiv (𝓡 n) (𝓡 e.ambientDimension) e.toFun (c.symm (c x.val))).comp
      (targetInverseChartDifferential c x).toContinuousLinearMap at h
  have he : c.symm (c x.val) = x.val := c.left_inv x.property
  rw [he] at h
  exact h

theorem chartEmbeddingDerivative_injective (x : c.source) :
    Injective (e.chartEmbeddingDerivative c x) := by
  rw [e.chartEmbeddingDerivative_eq]
  exact (e.injective_mfderiv x.val).comp (targetInverseChartDifferential c x).injective

theorem chartEmbeddingDerivative_range (x : c.source) :
    (e.chartEmbeddingDerivative c x).range = e.tangentImage x.val := by
  let D : Vector n →L[ℝ] Vector e.ambientDimension :=
    mfderiv (𝓡 n) (𝓡 e.ambientDimension) e.toFun x.val
  have he : e.chartEmbeddingDerivative c x =
      D.comp (targetInverseChartDifferential c x).toContinuousLinearMap :=
    e.chartEmbeddingDerivative_eq c x
  rw [he]
  change (D.toLinearMap.comp
    (targetInverseChartDifferential c x).toLinearMap).range = _
  rw [LinearMap.range_comp_of_range_eq_top _
    (targetInverseChartDifferential c x).toLinearEquiv.range]
  rfl

theorem continuous_chartEmbeddingDerivative : Continuous (e.chartEmbeddingDerivative c) := by
  have hc : ContDiffOn ℝ ∞ (e.toFun ∘ c.symm) c.target :=
    (e.smooth.comp_contMDiffOn c.contMDiffOn_invFun).contDiffOn
  exact (hc.continuousOn_fderiv_of_isOpen c.open_target (by simp)).comp_continuous
    c.toOpenPartialHomeomorph.continuousOn.domRestrict (fun x ↦ c.map_source x.property)

def normalChartOperator (x : c.source) :
    Vector ((e.ambientDimension - n) + n) →L[ℝ] Vector e.ambientDimension :=
  (((a.orthonormal x.val).val.comp (ContinuousLinearMap.fst ℝ _ _)) +
    ((e.chartEmbeddingDerivative c x).comp (ContinuousLinearMap.snd ℝ _ _))).comp
      EuclideanSpace.finAddEquivProd.toContinuousLinearMap

theorem normalChartOperator_apply (x : c.source)
    (v : Vector ((e.ambientDimension - n) + n)) :
    e.normalChartOperator a c x v =
      (a.orthonormal x.val).val (EuclideanSpace.finAddEquivProd v).1 +
        e.chartEmbeddingDerivative c x (EuclideanSpace.finAddEquivProd v).2 := rfl

theorem normalChartOperator_injective (x : c.source) :
    Injective (e.normalChartOperator a c x) := by
  let A := (a.orthonormal x.val).val
  let B := e.chartEmbeddingDerivative c x
  have hA : Injective A := Stiefel.injective (a.orthonormal x.val)
  have hB : Injective B := e.chartEmbeddingDerivative_injective c x
  have hr : A.range = (e.tangentImage x.val)ᗮ :=
    (a.orthonormal_range x.val).trans (e.range_normalProjection x.val)
  have hd : Disjoint A.range B.range := by
    rw [hr, e.chartEmbeddingDerivative_range]
    exact (e.tangentImage x.val).orthogonal_disjoint.symm
  have hc : Injective (A.toLinearMap.coprod B.toLinearMap) := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_coprod_of_disjoint_range _ _ hd,
      LinearMap.ker_eq_bot.mpr hA, LinearMap.ker_eq_bot.mpr hB, Submodule.prod_bot]
  exact hc.comp EuclideanSpace.finAddEquivProd.injective

theorem normalChartOperator_bijective (x : c.source) :
    Bijective (e.normalChartOperator a c x) := by
  have hi := e.normalChartOperator_injective a c x
  refine ⟨hi, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (show Module.finrank ℝ (Vector ((e.ambientDimension - n) + n)) =
      Module.finrank ℝ (Vector e.ambientDimension) from ?_)).mp hi
  simp only [finrank_euclideanSpace_fin]
  exact Nat.sub_add_cancel (e.dimension_le_ambient x.val)

def normalChartCoordinates (x : c.source) :
    Vector ((e.ambientDimension - n) + n) ≃L[ℝ] Vector e.ambientDimension :=
  (LinearEquiv.ofBijective (e.normalChartOperator a c x).toLinearMap
    (e.normalChartOperator_bijective a c x)).toContinuousLinearEquiv

theorem normalChartCoordinates_toContinuousLinearMap (x : c.source) :
    (e.normalChartCoordinates a c x).toContinuousLinearMap = e.normalChartOperator a c x := rfl

theorem normalChartCoordinates_symm_toContinuousLinearMap (x : c.source) :
    (e.normalChartCoordinates a c x).symm.toContinuousLinearMap =
      (e.normalChartOperator a c x).inverse :=
  (ContinuousLinearMap.inverse_equiv (e.normalChartCoordinates a c x)).symm

theorem continuous_normalChartCoordinates :
    Continuous (fun x : c.source ↦ (e.normalChartCoordinates a c x).toContinuousLinearMap) := by
  have hA : Continuous (fun x : c.source ↦ (a.orthonormal x.val).val) :=
    a.contMDiff_orthonormal.continuous.comp continuous_subtype_val
  exact ((hA.clm_comp continuous_const).add
    ((e.continuous_chartEmbeddingDerivative c).clm_comp continuous_const)).clm_comp continuous_const

theorem continuous_inverse_normalChartCoordinates :
    Continuous (fun x : c.source ↦
      (e.normalChartCoordinates a c x).symm.toContinuousLinearMap) := by
  rw [continuous_iff_continuousAt]
  intro x
  simp_rw [e.normalChartCoordinates_symm_toContinuousLinearMap]
  have hi : (e.normalChartOperator a c x).IsInvertible := ⟨e.normalChartCoordinates a c x, rfl⟩
  exact (hi.contDiffAt_map_inverse (n := ∞)).continuousAt.comp
    (e.continuous_normalChartCoordinates a c).continuousAt

end NoExoticSixSphere.EuclideanEmbedding
