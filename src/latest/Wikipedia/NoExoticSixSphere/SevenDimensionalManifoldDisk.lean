import Wikipedia.NoExoticSixSphere.SevenDimensionalSpanningDiskFrame
import Wikipedia.NoExoticSixSphere.SmoothDiskNormalComplement
import Wikipedia.NoExoticSixSphere.SmoothRangeOrthonormalization
import Wikipedia.NoExoticSixSphere.NormalBundle
import Wikipedia.NoExoticSixSphere.SpanningDiskBoundaryComplementFrame

/-!
# Actual framed spanning disks for three-spheres in a framed seven-manifold

Starting with the original smooth embedding, its given normal frame, and an
embedded immersive three-sphere, we construct the actual stabilized disk.
The orthonormalized original normal frame and five new axes extend smoothly
over that disk and retain their exact radial collar values. Four further
smooth orthonormal directions span the complement of the frame and actual
disk derivative. Their boundary values project, without loss of norm, to
a full frame of the sphere's normal space inside the original manifold.
No disk, frame extension, or complementary frame is assumed.

The attaching tube and the eight-dimensional surgery trace are not yet
constructed here.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel StabilizedSpanningDisk

universe u

theorem exists_framedSphereDisk_of_dimension_seven {M : Type u}
    [TopologicalSpace M] [ChartedSpace (Vector 7) M]
    (e : EuclideanEmbedding 7 M)
    (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
    (b : Sphere 3) (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f)
    (hi : Injective f) (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s)) :
    ∃ D : DiskData b (e.toFun ∘ f), ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∃ T : Vector 4 → Vector ((e.ambientDimension - 7) + 5) →L[ℝ]
          Vector (e.ambientDimension + 6),
        (∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ T x) ∧
        (∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖T x w‖ = ‖w‖) ∧
        (∀ x ∈ closedBall (0 : Vector 4) 1,
          (T x).range ≤ (fderiv ℝ D.toFun x).rangeᗮ) ∧
        (∀ s : Sphere 3, T s.val = boundaryFrameOperator (a.orthonormal (f s)).val) ∧
        (∀ x ∈ closedBall (0 : Vector 4) 1, r ≤ ‖x‖ →
          D.toFun x = collar b (e.toFun ∘ f) x ∧
          T x = boundaryFrameOperator
            (a.orthonormal (f (SphereRadialRetraction.retract b x))).val) ∧
        ∃ C : Vector 4 → Vector 4 →L[ℝ] Vector (e.ambientDimension + 6),
          (∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ C x) ∧
          (∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖C x w‖ = ‖w‖) ∧
          (∀ x ∈ closedBall (0 : Vector 4) 1,
            (C x).range = (OperatorSum.operator (T x) (fderiv ℝ D.toFun x)).rangeᗮ) ∧
          ContMDiff (𝓡 3) 𝓘(ℝ, Vector 4 →L[ℝ] Vector e.ambientDimension) ∞
            (boundaryComplementOperator C) ∧
          (∀ s v, ‖boundaryComplementOperator C s v‖ = ‖v‖) ∧
          (∀ s, (boundaryComplementOperator C s).range = e.tangentImage (f s) ⊓
            (mfderiv (𝓡 3) (𝓡 e.ambientDimension) (e.toFun ∘ f) s).rangeᗮ) ∧
          ∀ s v, appendZeroMap e.ambientDimension 6 (boundaryComplementOperator C s v) =
            C s.val v := by
  have hes : ContMDiff (𝓡 3) (𝓡 e.ambientDimension) ∞ (e.toFun ∘ f) :=
    e.smooth.comp hf
  have hed (s : Sphere 3) :
      Injective (mfderiv (𝓡 3) (𝓡 e.ambientDimension) (e.toFun ∘ f) s) := by
    rw [mfderiv_comp s (e.smooth.mdifferentiableAt (by simp))
      (hf.mdifferentiableAt (by simp))]
    exact (e.injective_mfderiv (f s)).comp (hd s)
  obtain ⟨D⟩ := nonempty_diskData b (e.toFun ∘ f) hes
    (e.closedEmbedding.injective.comp hi) hed
  have hN : e.ambientDimension = (e.ambientDimension - 7) + 7 := by
    have h := e.dimension_le_ambient (f b)
    omega
  have has : ContMDiff (𝓡 3)
      𝓘(ℝ, Vector (e.ambientDimension - 7) →L[ℝ] Vector e.ambientDimension) ∞
      (fun s ↦ (a.orthonormal (f s)).val) := a.contMDiff_orthonormal.comp hf
  have han (s : Sphere 3) : (a.orthonormal (f s)).val.range ≤
      (mfderiv (𝓡 3) (𝓡 e.ambientDimension) (e.toFun ∘ f) s).rangeᗮ := by
    rw [a.orthonormal_range, e.range_normalProjection]
    apply Submodule.orthogonal_le
    rw [mfderiv_comp s (e.smooth.mdifferentiableAt (by simp))
      (hf.mdifferentiableAt (by simp))]
    rintro _ ⟨v, rfl⟩
    exact ⟨_, rfl⟩
  obtain ⟨r, hr, hr1, T, hTs, hTn, hTr, hTb, hTc⟩ :=
    D.exists_normalFrame_collar_of_dimension_seven hes hN
      (fun s ↦ a.orthonormal (f s)) has han
  obtain ⟨C, hCs, hCn, hCr⟩ := exists_smoothDiskNormalComplement_of_dimension
    D.toFun (fun _ _ ↦ D.smooth.contDiffAt) D.immersive T hTs hTn hTr
    (by omega : ((e.ambientDimension - 7) + 5) + 4 + 4 = e.ambientDimension + 6)
  have hCbr (s : Sphere 3) : (C s.val).range =
      (OperatorSum.operator (boundaryFrameOperator (a.orthonormal (f s)).val)
        (fderiv ℝ D.toFun s.val)).rangeᗮ := by
    rw [hCr s.val (sphere_subset_closedBall s.property), hTb s]
  refine ⟨D, r, hr, hr1, T, hTs, hTn, hTr, hTb, hTc, C, hCs, hCn, hCr,
    contMDiff_boundaryComplementOperator C hCs, ?_, ?_, ?_⟩
  · exact D.norm_boundaryComplementOperator hes hed
      (fun s ↦ a.orthonormal (f s)) han C hCbr hCn
  · intro s
    rw [D.range_boundaryComplementOperator hes hed
      (fun s ↦ a.orthonormal (f s)) han C hCbr s,
      a.orthonormal_range, e.range_normalProjection]
    change (e.tangentImage (f s))ᗮᗮ ⊓ _ = _
    rw [Submodule.orthogonal_orthogonal]
  · exact D.append_boundaryComplementOperator hes hed
      (fun s ↦ a.orthonormal (f s)) han C hCbr

end NoExoticSixSphere.EuclideanEmbedding
