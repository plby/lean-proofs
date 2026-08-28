import Wikipedia.HopfProblem.DegreeCollapseLowRadialAttachingData
import Wikipedia.HopfProblem.DegreeCollapseLowFramedCurvedProduct

/-!

# Constructed curved low-surgery products with exact native attaching collars

The original native sphere supplies the disk, radial data, corrected embedded
product, full core normal frame and embedded native tube. The whole corrected
collar agrees with that tube in the original ambient coordinates, and the
entire product interior avoids the original ambient space. Matching the full
normal frame on the whole attaching collar remains a separate construction.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff
open Wikipedia.SmoothSixDPoincare.SphereBoundary

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Vector 7) M] [IsManifold (𝓡 7) ∞ M]
  (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)

theorem exists_curvedAttachingProduct (hdim : 0 < d) (hsmall : d ≤ 3)
    (R : EuclideanEmbedding.TubularRetraction e) (f : NoExoticSixSphere.Sphere d → M)
    (hf : ContMDiff (𝓡 d) (𝓡 7) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 d) (𝓡 7) f s)) :
    ∃ D : CollaredFramedDisk (spherePole d)
        (e.toFun ∘ f) (fun s => a.orthonormal (f s)),
      ∃ r : ℝ, (1 / 2 : ℝ) < r ∧ r < 1 ∧
        ∃ A : LowFramedProduct.FramedProduct (q := 7 - d) D.map D.frame,
          ∃ χ : ContDiffBump (0 : Vector (d + 1)),
            χ.rIn = r ∧ χ.rOut = (r + 1) / 2 ∧
            ∃ B : LowDiskThickening.FramedCoreProduct
                (curvedDiskProduct e f D.toFramedDisk A R χ) D.frame,
              (∀ x ∈ closedBall (0 : Vector (d + 1)) 1, r ≤ ‖x‖ →
                D.map x = collar (spherePole d) (e.toFun ∘ f) x ∧
                D.frame x = boundaryFrameOperator d
                  (a.orthonormal (f (SphereRadialRetraction.retract (spherePole d) x))).val ∧
                A.transverse x =
                  A.transverse (SphereRadialRetraction.retract (spherePole d) x).val) ∧
              IsClosedEmbedding
                (fun p : NoExoticSixSphere.Sphere d ×
                    closedBall (0 : Vector (7 - d)) B.radius ↦
                  internalSphereTube e f A.boundaryTransverse R (p.1, p.2.val)) ∧
              (∀ s : NoExoticSixSphere.Sphere d,
                ∀ v ∈ closedBall (0 : Vector (7 - d)) B.radius,
                  (s, v) ∈ sphereTubeDomain e f A.boundaryTransverse R ∧
                    IsLocalDiffeomorphAt ((𝓡 d).prod (𝓡 (7 - d))) (𝓡 7) ∞
                      (internalSphereTube e f A.boundaryTransverse R) (s, v)) ∧
              (∀ s : NoExoticSixSphere.Sphere d, ∀ v : Vector (7 - d),
                curvedDiskProduct e f D.toFramedDisk A R χ (s.val, v) =
                  appendZeroMap e.ambientDimension (1 + (1 + (d + 1)))
                    (e.toFun (internalSphereTube e f A.boundaryTransverse R (s, v)))) ∧
              (∀ x ∈ closedBall (0 : Vector (d + 1)) 1, χ.rOut ≤ ‖x‖ →
                ∀ v : Vector (7 - d),
                  curvedDiskProduct e f D.toFramedDisk A R χ (x, v) =
                    coordinates e.ambientDimension (d + 1)
                      ((e.toFun (internalSphereTube e f A.boundaryTransverse R
                        (SphereRadialRetraction.retract (spherePole d) x, v)),
                          definingFunction x), 0)) ∧
              ∀ x ∈ ball (0 : Vector (d + 1)) 1,
                ∀ v ∈ closedBall (0 : Vector (7 - d)) B.radius,
                  curvedDiskProduct e f D.toFramedDisk A R χ (x, v) ∉
                    range (appendZeroMap e.ambientDimension (1 + (1 + (d + 1)))) := by
  obtain ⟨D, r, hr, hr1, A, hc, ε, hε, _, hemb, hlocal, havoid⟩ :=
    exists_radialAttachingData e a hdim hsmall R f hf hi hd
  let χ : ContDiffBump (0 : Vector (d + 1)) := {
    rIn := r
    rOut := (r + 1) / 2
    rIn_pos := by linarith
    rIn_lt_rOut := by linarith }
  have hχ : χ.rOut ≤ 1 := by change (r + 1) / 2 ≤ 1; linarith
  have hrχ : r ≤ χ.rOut := by change r ≤ (r + 1) / 2; linarith
  obtain ⟨B, hBε⟩ :=
    exists_framed_curvedDiskProduct e a f hf hd D.toFramedDisk A R χ ε hε
      (fun s v hv ↦ (hlocal s v hv).1)
  refine ⟨D, r, hr, hr1, A, χ, rfl, rfl, B, hc, ?_, ?_, ?_, ?_, ?_⟩
  · exact LowDiskThickening.restrict_closedProduct_embedding
      (internalSphereTube e f A.boundaryTransverse R) hBε hemb
  · intro s v hv
    exact hlocal s v ((closedBall_subset_closedBall hBε) hv)
  · intro s v
    exact curvedDiskProduct_boundary e a f hf hd D.toFramedDisk A R χ hχ s v
  · intro x hx hxr v
    have hrx := hrχ.trans hxr
    exact curvedDiskProduct_collar e a f hf hd D.toFramedDisk A R χ
      (hr.trans_le hrx) hxr (hc x hx hrx).1 (hc x hx hrx).2.2 v
  · intro x hx v hv
    exact curvedDiskProduct_avoids e f D.toFramedDisk A R χ
      (havoid x hx v ((closedBall_subset_closedBall hBε) hv))

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery
