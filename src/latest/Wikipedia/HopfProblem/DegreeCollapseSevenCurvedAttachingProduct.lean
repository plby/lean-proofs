import Wikipedia.HopfProblem.DegreeCollapseSevenRadialAttachingData
import Wikipedia.HopfProblem.DegreeCollapseSevenFramedCurvedProduct

/-!
# Seven-dimensional surgery data with original attaching-face control

The sphere, its induced normal frame, radial disk, positive product radius,
and actual manifold tube are retained. The tubular retraction is an explicit
input. No compactness of a filling's interior or existence of a filling is
assumed implicitly. Whole-face normal-frame matching remains separate.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 7) M]
  [IsManifold (𝓡 7) ∞ M] (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)

theorem exists_curvedAttachingProduct (R : EuclideanEmbedding.TubularRetraction e) (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s)) :
    ∃ D : DiskData (pole 3) (e.toFun ∘ f), ∃ r : ℝ, (1 / 2 : ℝ) < r ∧ r < 1 ∧
      ∃ T : Vector 4 → Vector ((e.ambientDimension - 7) + 5) →L[ℝ]
          Vector (e.ambientDimension + 6),
        ∃ A : EightDimensionalFramedProduct.FramedProduct D.toFun T,
          ∃ χ : ContDiffBump (0 : Vector 4), χ.rIn = r ∧ χ.rOut = (r + 1) / 2 ∧
            ∃ B : GeneralDiskThickening.FramedCoreProduct (SevenSurgery.curvedDiskProduct e f D A R χ) T,
              (∀ s : Sphere 3, T s.val =
                boundaryFrameOperator (SevenSurgery.normalFrameOnSphere e a f s).val) ∧
              (∀ x ∈ closedBall (0 : Vector 4) 1, r ≤ ‖x‖ →
                D.toFun x = collar (pole 3) (e.toFun ∘ f) x ∧
                T x = boundaryFrameOperator
                  (SevenSurgery.normalFrameOnSphere e a f (SphereRadialRetraction.retract (pole 3) x)).val ∧
                A.transverse x = A.transverse (SphereRadialRetraction.retract (pole 3) x).val) ∧
              IsClosedEmbedding
                (fun p : Sphere 3 × closedBall (0 : Vector 4) B.radius ↦
                  SevenSurgery.internalSphereTube e f A.boundaryTransverse R (p.1, p.2.val)) ∧
              (∀ s : Sphere 3, ∀ v ∈ closedBall (0 : Vector 4) B.radius,
                (s, v) ∈ SevenSurgery.sphereTubeDomain e f A.boundaryTransverse R ∧
                  IsLocalDiffeomorphAt ((𝓡 3).prod (𝓡 4)) (𝓡 7) ∞
                    (SevenSurgery.internalSphereTube e f A.boundaryTransverse R) (s, v)) ∧
              (∀ s : Sphere 3, ∀ v : Vector 4,
                SevenSurgery.curvedDiskProduct e f D A R χ (s.val, v) = appendZeroMap e.ambientDimension 6
                  (e.toFun (SevenSurgery.internalSphereTube e f A.boundaryTransverse R (s, v)))) ∧
              ∀ x ∈ ball (0 : Vector 4) 1, ∀ v ∈ closedBall (0 : Vector 4) B.radius,
                SevenSurgery.curvedDiskProduct e f D A R χ (x, v) ∉
                  range (appendZeroMap e.ambientDimension 6) := by
  obtain ⟨D, r, hr, hr1, T, A, hTb, hc, ε, hε, _, hemb, hlocal, havoid⟩ :=
    SevenSurgery.exists_radialAttachingData e a R f hf hi hd
  let χ : ContDiffBump (0 : Vector 4) := {
    rIn := r
    rOut := (r + 1) / 2
    rIn_pos := by linarith
    rIn_lt_rOut := by linarith }
  have hχ : χ.rOut ≤ 1 := by change (r + 1) / 2 ≤ 1; linarith
  obtain ⟨B, hBε⟩ := SevenSurgery.exists_framed_curvedDiskProduct e a f hf hd D A R χ hTb ε hε
    (fun s v hv ↦ (hlocal s v hv).1)
  refine ⟨D, r, hr, hr1, T, A, χ, rfl, rfl, B, hTb, hc, ?_, ?_, ?_, ?_⟩
  · exact GeneralDiskThickening.restrict_closedProduct_embedding
      (SevenSurgery.internalSphereTube e f A.boundaryTransverse R) hBε hemb
  · intro s v hv
    exact hlocal s v ((closedBall_subset_closedBall hBε) hv)
  · intro s v
    exact SevenSurgery.curvedDiskProduct_boundary e a f hf hd D A R χ hTb hχ s v
  · intro x hx v hv
    exact SevenSurgery.curvedDiskProduct_avoids e f D A R χ
      (havoid x hx v ((closedBall_subset_closedBall hBε) hv))

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
