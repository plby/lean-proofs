import Wikipedia.NoExoticSixSphere.EmbeddedNegativeTimeGraph
import Wikipedia.NoExoticSixSphere.OutwardGraphParityCriterion
import Wikipedia.NoExoticSixSphere.ManifoldFourDiskRawFrame
import Wikipedia.NoExoticSixSphere.OrthonormalRangeFrame

/-!
# The actual regular-time boundary parity from the original disk operator

Use the original embedded seven-manifold, its actual normal frame, and
its regular time-zero boundary. The negative-time graph is constructed
from the given disk map. Its derivative, positive height, normal columns,
and signed normal-coordinate change are all proved from those data.
The conclusion concerns the actual induced outward boundary frame on
the native zero atlas. No arbitrary framed-bordism invariance is assumed.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EmbeddedTime

open GLOrthonormalization Stiefel DiskBoundary

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector (6 + 1)) M]
  [IsManifold (𝓡 (6 + 1)) ∞ M] (e : EuclideanEmbedding (6 + 1) M)
  (r : e.TubularRetraction) (t : C(M, ℝ))
  (ht : ContMDiff (𝓡 (6 + 1)) 𝓘(ℝ, ℝ) ∞ t)
  (hreg : ∀ x, t x = 0 → Surjective (mfderiv (𝓡 (6 + 1)) 𝓘(ℝ, ℝ) t x))
  (a : SmoothRangeFrame (𝓡 (6 + 1)) e.normalProjection e.NormalModel) (m : M)

theorem sphereParity_zero_iff_diskOperator_extends
    (f : C(Sphere 3, {x : M // t x = 0})) (g : Vector 4 → M)
    (hg : ∀ x ∈ closedBall (0 : Vector 4) 1, ContMDiffAt (𝓡 4) (𝓡 (6 + 1)) ∞ g x)
    (hb : ∀ s : Sphere 3, g s.val = (f s).val)
    (P : C(Sphere 3, Monomorphism.Space e.ambientDimension ((e.ambientDimension - 7) + 4)))
    (hP : ∀ s : Sphere 3, (P s).val = e.normalFourDiskOperator a g s.val)
    (hheight : ∀ s : Sphere 3, fderiv ℝ (t ∘ g) s.val s.val < 0) :
    letI := zeroAtlas t ht hreg;
    ∀ (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
      (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)),
      (zeroEmbedding e t ht hreg).sphereParity (zeroNormalFrame e r t ht hreg a m)
        f hf hi hd = 0 ↔ Extends P := by
  let := zeroAtlas t ht hreg
  intro hf hi hd
  let eZ := zeroEmbedding (n := 6) e t ht hreg
  let aZ := zeroNormalFrame (n := 6) e r t ht hreg a m
  let F := negativeTimeGraph e t g
  let A : C(Sphere 3, Vector (e.ambientDimension - 7) →L[ℝ] Vector e.ambientDimension) :=
    ⟨fun s ↦ (a.orthonormal (f s).val).val,
      a.contMDiff_orthonormal.continuous.comp (continuous_subtype_val.comp f.continuous)⟩
  have hDc : ContinuousOn (e.fourDiskDerivative g) (closedBall (0 : Vector 4) 1) :=
    fun x hx ↦ (e.contDiffAt_fourDiskDerivative g x (hg x hx)).continuousAt.continuousWithinAt
  let D : C(Sphere 3, Vector 4 →L[ℝ] Vector e.ambientDimension) :=
    ⟨fun s ↦ e.fourDiskDerivative g s.val,
      hDc.comp_continuous continuous_subtype_val (fun s ↦ sphere_subset_closedBall s.property)⟩
  let ν : C(Sphere 3, Vector e.ambientDimension) :=
    ⟨fun s ↦ inwardNormal e r t (f s),
      (contMDiff_inwardNormal e r t ht hreg).continuous.comp f.continuous⟩
  let ξ : C(Sphere 3, Vector e.ambientDimension →L[ℝ] ℝ) :=
    ⟨fun s ↦ inwardTimeCovector e r t (f s),
      (contMDiff_inwardTimeCovector e r t ht hreg).continuous.comp f.continuous⟩
  let Q := inwardNormalCoordinates (n := 6) e m
  have hN : eZ.ambientDimension = 3 + ((e.ambientDimension - 7) + 4) := by
    have h := e.dimension_le_ambient m
    change e.ambientDimension = 3 + ((e.ambientDimension - 7) + 4)
    omega
  have hF : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ F x :=
    fun x hx ↦ contDiffAt_negativeTimeGraph e t ht g x (hg x hx)
  have hFb : ∀ s : Sphere 3, F s.val = (eZ.toFun (f s), 0) := by
    intro s
    change (e.toFun (g s.val), -t (g s.val)) = (e.toFun (f s).val, 0)
    rw [hb, (f s).property, neg_zero]
  have hP' : ∀ s : Sphere 3, (P s).val = OperatorSum.operator (A s) (D s) := by
    intro s
    rw [hP]
    change OperatorSum.operator (a.orthonormal (g s.val)).val (e.fourDiskDerivative g s.val) =
      OperatorSum.operator (a.orthonormal (f s).val).val (e.fourDiskDerivative g s.val)
    rw [hb]
  have haZ : ∀ s : Sphere 3, aZ.ambient (f s) =
      (OrthogonalFrameAppend.operator (A s) (ν s)).comp Q.toContinuousLinearMap :=
    fun s ↦ zeroNormalFrame_inward_columns e r t ht hreg a m (f s)
  have hD : ∀ s : Sphere 3, fderiv ℝ F s.val = OutwardGraphFrame.graph (D s) (ξ s) := by
    intro s
    have h := negativeTimeGraph_derivative e r t ht g s.val
      (hg s.val (sphere_subset_closedBall s.property))
    rw [hb s] at h
    exact h
  have hA : ∀ s u, ξ s (A s u) = 0 :=
    fun s u ↦ inwardTimeCovector_frame e r t a.normalized (f s) u
  have hν : ∀ s, ξ s (ν s) < 0 :=
    fun s ↦ inwardTimeCovector_inward_neg e r t ht hreg (f s)
  have hH : ∀ s : Sphere 3, 0 < (fderiv ℝ F s.val s.val).2 :=
    fun s ↦ negativeTimeGraph_height_pos e r t ht g s
      (hg s.val (sphere_subset_closedBall s.property)) (hheight s)
  exact eZ.sphereParity_zero_iff_outwardOperator_extends aZ hN f hf hi hd F hF hFb
    A D ν ξ Q P hP' haZ hD hA hν hH

end NoExoticSixSphere.EmbeddedTime
