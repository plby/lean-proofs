import Wikipedia.NoExoticSixSphere.SixSphereRadialAttachingData
import Wikipedia.NoExoticSixSphere.FramedCurvedDiskProduct
import Wikipedia.NoExoticSixSphere.CurvedDiskCollar

/-!
# The candidate's embedded curved product with its exact original attaching face

The disk, both radial frame extensions, actual tubular retraction, supported
correction, and a full normal framing of the corrected embedded product are
all constructed. Its whole boundary face is exactly the original-manifold
tube, and its whole interior avoids the old ambient space.

The full product normal frame retains the original boundary-core columns.
Matching that frame to the original manifold's normal frame on the whole
face remains unproved, as do the attached trace and global classification.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)

theorem exists_curvedAttachingProduct (h : M ≃ₜ Sphere 6) (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) :
    ∃ D : DiskData (pole 3) (e.toFun ∘ f), ∃ r : ℝ, (1 / 2 : ℝ) < r ∧ r < 1 ∧
      ∃ T : Vector 4 → Vector ((e.ambientDimension - 6) + 5) →L[ℝ]
          Vector (e.ambientDimension + 6),
        ∃ A : DiskThickening.FramedProduct D.toFun T, ∃ R : TubularRetraction e,
          ∃ χ : ContDiffBump (0 : Vector 4), χ.rIn = r ∧ χ.rOut = (r + 1) / 2 ∧
            ∃ B : DiskThickening.FramedCoreProduct (e.curvedDiskProduct f D A R χ) T,
              (∀ s : Sphere 3, T s.val =
                boundaryFrameOperator (e.normalFrameOnSphere a f s).val) ∧
              (∀ x ∈ closedBall (0 : Vector 4) 1, r ≤ ‖x‖ →
                D.toFun x = collar (pole 3) (e.toFun ∘ f) x ∧
                T x = boundaryFrameOperator
                  (e.normalFrameOnSphere a f (SphereRadialRetraction.retract (pole 3) x)).val ∧
                A.transverse x = A.transverse (SphereRadialRetraction.retract (pole 3) x).val) ∧
              IsClosedEmbedding
                (fun p : Sphere 3 × closedBall (0 : Vector 3) B.radius ↦
                  e.internalSphereTube f A.boundaryTransverse R (p.1, p.2.val)) ∧
              (∀ s : Sphere 3, ∀ v ∈ closedBall (0 : Vector 3) B.radius,
                (s, v) ∈ e.sphereTubeDomain f A.boundaryTransverse R ∧
                  IsLocalDiffeomorphAt ((𝓡 3).prod (𝓡 3)) (𝓡 6) ∞
                    (e.internalSphereTube f A.boundaryTransverse R) (s, v)) ∧
              (∀ s : Sphere 3, ∀ v : Vector 3,
                e.curvedDiskProduct f D A R χ (s.val, v) = appendZeroMap e.ambientDimension 6
                  (e.toFun (e.internalSphereTube f A.boundaryTransverse R (s, v)))) ∧
              ∀ x ∈ ball (0 : Vector 4) 1, ∀ v ∈ closedBall (0 : Vector 3) B.radius,
                e.curvedDiskProduct f D A R χ (x, v) ∉
                  range (appendZeroMap e.ambientDimension 6) := by
  obtain ⟨D, r, hr, hr1, T, A, hTb, hc, R, ε, hε, _, hemb, hlocal, havoid⟩ :=
    e.exists_radialAttachingData a h f hf hi hd
  let χ : ContDiffBump (0 : Vector 4) := {
    rIn := r
    rOut := (r + 1) / 2
    rIn_pos := by linarith
    rIn_lt_rOut := by linarith }
  have hχ : χ.rOut ≤ 1 := by change (r + 1) / 2 ≤ 1; linarith
  obtain ⟨B, hBε⟩ := e.exists_framed_curvedDiskProduct a f hf hd D A R χ hTb ε hε
    (fun s v hv ↦ (hlocal s v hv).1)
  refine ⟨D, r, hr, hr1, T, A, R, χ, rfl, rfl, B, hTb, hc, ?_, ?_, ?_, ?_⟩
  · exact restrict_closedProduct_embedding
      (e.internalSphereTube f A.boundaryTransverse R) hBε hemb
  · intro s v hv
    exact hlocal s v ((closedBall_subset_closedBall hBε) hv)
  · intro s v
    exact e.curvedDiskProduct_boundary a f hf hd D A R χ hTb hχ s v
  · intro x hx v hv
    exact e.curvedDiskProduct_avoids f D A R χ
      (havoid x hx v ((closedBall_subset_closedBall hBε) hv))

end NoExoticSixSphere.EuclideanEmbedding
