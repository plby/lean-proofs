import Wikipedia.NoExoticSixSphere.SevenDimensionalAttachingTube
import Wikipedia.NoExoticSixSphere.FramedCompactCurvedDiskProduct

/-!
# A framed embedded curved product with the original seven-manifold attaching face

The actual disk, radial partial and transverse frames, local retraction,
supported correction, and full normal frame of the corrected embedded product
are all constructed. The map agrees with the original manifold tube on its
whole attaching face and outer collar, and its whole interior avoids the old
ambient space. The original manifold need not be compact.

The full normal frame retains the prescribed disk-core values. Agreement of
that full frame with the original manifold framing on the whole collar, and
the actual attached and rounded surgery trace, are not yet asserted.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff
open Wikipedia.SmoothSixDPoincare.SphereBoundary

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel StabilizedSpanningDisk

universe u

theorem exists_curvedProduct_of_dimension_seven {M : Type u}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 7) M]
    [IsManifold (𝓡 7) ∞ M] (e : EuclideanEmbedding 7 M)
    (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
    (b : Sphere 3) (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f)
    (hi : Injective f) (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s)) :
    ∃ D : DiskData b (e.toFun ∘ f), ∃ r : ℝ, (1 / 2 : ℝ) < r ∧ r < 1 ∧
      ∃ T : Vector 4 → Vector ((e.ambientDimension - 7) + 5) →L[ℝ]
          Vector (e.ambientDimension + 6),
        ∃ A : DiskThickening.FramedProduct D.toFun T 4,
          ∃ R : e.RetractionNear (range f), ∃ χ : ContDiffBump (0 : Vector 4),
            χ.rIn = r ∧ χ.rOut = (r + 1) / 2 ∧
            ∃ B : DiskThickening.FramedCoreProduct (e.compactCurvedDiskProduct f D A R χ) T,
              (∀ s : Sphere 3, T s.val = boundaryFrameOperator (a.orthonormal (f s)).val) ∧
              (∀ x ∈ closedBall (0 : Vector 4) 1, r ≤ ‖x‖ →
                D.toFun x = collar b (e.toFun ∘ f) x ∧
                T x = boundaryFrameOperator
                  (a.orthonormal (f (SphereRadialRetraction.retract b x))).val ∧
                A.transverse x = A.transverse (SphereRadialRetraction.retract b x).val) ∧
              (∀ s v, appendZeroMap e.ambientDimension 6
                (boundaryComplementOperator A.transverse s v) = A.transverse s.val v) ∧
              B.radius ≤ A.radius ∧
              IsClosedEmbedding (fun p : Sphere 3 × closedBall (0 : Vector 4) B.radius ↦
                e.compactSphereTube f (boundaryComplementOperator A.transverse) R (p.1, p.2.val)) ∧
              (∀ s : Sphere 3, ∀ v ∈ closedBall (0 : Vector 4) B.radius,
                (s, v) ∈ e.compactSphereTubeDomain f (boundaryComplementOperator A.transverse) R ∧
                  IsLocalDiffeomorphAt ((𝓡 3).prod (𝓡 4)) (𝓡 7) ∞
                    (e.compactSphereTube f (boundaryComplementOperator A.transverse) R) (s, v)) ∧
              (∀ s : Sphere 3, ∀ v : Vector 4,
                e.compactCurvedDiskProduct f D A R χ (s.val, v) = appendZeroMap e.ambientDimension 6
                  (e.toFun (e.compactSphereTube f
                    (boundaryComplementOperator A.transverse) R (s, v)))) ∧
              (∀ x ∈ closedBall (0 : Vector 4) 1, χ.rOut ≤ ‖x‖ → ∀ v : Vector 4,
                e.compactCurvedDiskProduct f D A R χ (x, v) = coordinates e.ambientDimension 4
                  ((e.toFun (e.compactSphereTube f (boundaryComplementOperator A.transverse) R
                    (SphereRadialRetraction.retract b x, v)), definingFunction x), 0)) ∧
              ∀ x ∈ ball (0 : Vector 4) 1, ∀ v ∈ closedBall (0 : Vector 4) B.radius,
                e.compactCurvedDiskProduct f D A R χ (x, v) ∉
                  range (appendZeroMap e.ambientDimension 6) := by
  obtain ⟨D, r, hr, hr1, T, A, hTb, hc, _, hCn, hCr, hCb, R, ε, hε, hεA,
    havoid, hemb, hlocal, _, _⟩ := e.exists_product_and_tube_of_dimension_seven a b f hf hi hd
  let χ : ContDiffBump (0 : Vector 4) := {
    rIn := r
    rOut := (r + 1) / 2
    rIn_pos := by linarith
    rIn_lt_rOut := by linarith }
  have hχ : χ.rOut ≤ 1 := by change (r + 1) / 2 ≤ 1; linarith
  have hrχ : r ≤ χ.rOut := by change r ≤ (r + 1) / 2; linarith
  have hiC (s : Sphere 3) : Injective (boundaryComplementOperator A.transverse s) :=
    Stiefel.injective ⟨_, hCn s⟩
  have hN : ((e.ambientDimension - 7) + 5) + 4 + 4 = e.ambientDimension + 6 := by
    have h := e.dimension_le_ambient (f b)
    omega
  obtain ⟨B, hBε⟩ := e.exists_framed_compactCurvedDiskProduct f hf hd D A R χ hiC hCr hN ε hε
    (fun s v hv ↦ (hlocal s v hv).1)
  refine ⟨D, r, hr, hr1, T, A, R, χ, rfl, rfl, B, hTb, hc, hCb,
    hBε.trans hεA, ?_, ?_, ?_, ?_, ?_⟩
  · exact restrict_closedProduct_embedding
      (e.compactSphereTube f (boundaryComplementOperator A.transverse) R) hBε hemb
  · intro s v hv
    exact hlocal s v ((closedBall_subset_closedBall hBε) hv)
  · exact e.compactCurvedDiskProduct_boundary f D A R χ hCb hχ
  · intro x hx hχx v
    have hxr : r ≤ ‖x‖ := hrχ.trans hχx
    have hxc := hc x hx hxr
    exact e.compactCurvedDiskProduct_collar f D A R χ hCb (hr.trans_le hxr)
      hxc.1 hxc.2.2 hχx v
  · intro x hx v hv
    exact e.compactCurvedDiskProduct_avoids f D A R χ
      (havoid x hx v ((closedBall_subset_closedBall hBε) hv))

end NoExoticSixSphere.EuclideanEmbedding
