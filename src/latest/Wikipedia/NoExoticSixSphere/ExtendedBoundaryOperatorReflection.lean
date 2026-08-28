import Wikipedia.NoExoticSixSphere.ExtendedBoundaryOperatorParity
import Wikipedia.NoExoticSixSphere.CollaredDiskCombinedTargetChange
import Wikipedia.NoExoticSixSphere.CollaredDiskHeightReflection

/-!
# Negative collar height for an extending original boundary operator

Reflect the height coordinate of the actual disk map and transport the
given operator extension by the corresponding fixed target equivalence.
The prescribed raw normal columns and the original boundary map are fixed.
Only the boundary radial height changes sign; no interior immersion is used.
-/

noncomputable section

open Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel CollaredDiskFrame
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)

theorem sphereParity_zero_of_extended_boundary_operator_negative
    (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
    (F : Vector 4 → Vector e.ambientDimension × ℝ)
    (hF : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ F x)
    (hb : ∀ s : Sphere 3, F s.val = (e.toFun (f s), 0))
    (G : C(Disk (E := Vector 4),
      Monomorphism.Space (e.ambientDimension + 6) (((e.ambientDimension - 6) + 5) + 4)))
    (hG : ∀ s, (G (boundaryToDisk s)).val =
      combined ((ContinuousLinearMap.inl ℝ (Vector e.ambientDimension) ℝ).comp
        (a.ambient (f s))) (fderiv ℝ F s.val))
    (hheight : ∀ s : Sphere 3, (fderiv ℝ F s.val s.val).2 < 0) :
    e.sphereParity a f hf hi hd = 0 := by
  let L := heightReflection e.ambientDimension
  let F' := L ∘ F
  let G' := (combinedTargetMap (k := e.ambientDimension - 6) L).comp G
  have hF' (x : Vector 4) (hx : x ∈ Metric.closedBall 0 1) : ContDiffAt ℝ ∞ F' x :=
    L.contDiff.contDiffAt.comp x (hF x hx)
  have hdF' (x : Vector 4) (hx : x ∈ Metric.closedBall 0 1) :
      fderiv ℝ F' x = L.toContinuousLinearMap.comp (fderiv ℝ F x) := by
    change fderiv ℝ (L ∘ F) x = _
    rw [fderiv_comp x L.differentiableAt ((hF x hx).differentiableAt (by simp)), L.fderiv]
  apply e.sphereParity_zero_of_extended_boundary_operator a f hf hi hd F' hF' ?_ G' ?_ ?_
  · intro s
    change heightReflection e.ambientDimension (F s.val) = _
    rw [hb, heightReflection_apply, neg_zero]
  · intro s
    change (combinedTargetMap L (G (boundaryToDisk s))).val = _
    rw [combinedTargetMap_operator L _ _ _ (hG s),
      heightReflection_normal, hdF' s.val (Metric.sphere_subset_closedBall s.property)]
  · intro s
    rw [hdF' s.val (Metric.sphere_subset_closedBall s.property)]
    change 0 < (heightReflection e.ambientDimension (fderiv ℝ F s.val s.val)).2
    rw [heightReflection_apply]
    exact neg_pos.mpr (hheight s)

end NoExoticSixSphere.EuclideanEmbedding
