import Wikipedia.NoExoticSixSphere.SixSphereGeometricParity
import Wikipedia.NoExoticSixSphere.FramedDiskThickening
import Wikipedia.NoExoticSixSphere.SpanningDiskCollaredNormalFrame

/-!
# A framed embedded disk thickening for every sphere in the candidate

The candidate's proved zero geometric parity supplies the smooth extension of
its original normal columns across an actual stabilized spanning four-disk.
The complementary three-frame and a thin embedded seven-dimensional product
are constructed. The partial normal frame is exactly radial on a whole inner
annulus, and the full product normal frame retains these zero-section values.

No disk, extension, transverse frame, or product radius is an extra input.
The attaching face is not yet matched to an original manifold neighborhood;
no attached surgery trace, framed nullbordism, or classification is asserted.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)

theorem exists_framedDiskThickening_collar (h : M ≃ₜ Sphere 6) (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) :
    ∃ D : DiskData (pole 3) (e.toFun ∘ f), ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∃ T : Vector 4 → Vector ((e.ambientDimension - 6) + 5) →L[ℝ]
          Vector (e.ambientDimension + 6),
        ∃ A : DiskThickening.FramedProduct D.toFun T,
          (∀ s : Sphere 3, T s.val =
            boundaryFrameOperator (e.normalFrameOnSphere a f s).val) ∧
          (∀ s : Sphere 3, DiskThickening.map D.toFun A.transverse (s.val, 0) =
            appendZeroMap e.ambientDimension 6 (e.toFun (f s))) ∧
          (∀ s : Sphere 3, A.normalFrame (s.val, 0) =
            boundaryFrameOperator (e.normalFrameOnSphere a f s).val) ∧
          ∀ x ∈ closedBall (0 : Vector 4) 1, r ≤ ‖x‖ →
            D.toFun x = collar (pole 3) (e.toFun ∘ f) x ∧
            T x = boundaryFrameOperator
              (e.normalFrameOnSphere a f (SphereRadialRetraction.retract (pole 3) x)).val := by
  obtain ⟨D⟩ := e.nonempty_sphereDiskData f (pole 3) hf hi hd
  have hz := e.sphereParity_zero_of_homeomorph_sixSphere a h f hf hi hd
  obtain ⟨T₀, hT₀s, hT₀n, hT₀r, hT₀b⟩ :=
    (e.sphereParity_zero_iff_smooth_extension a f hf hi hd D).mp hz
  obtain ⟨r, hr, hr1, T, hTs, hTn, hTr, hTb, hTc⟩ :=
    D.exists_normalFrame_collar (e.smooth.comp hf) (e.normalFrameOnSphere a f)
      (e.contMDiff_normalFrameOnSphere a f hf) (e.normalFrameOnSphere_normal a f hf)
      T₀ hT₀s hT₀n hT₀r hT₀b
  have hDi : InjOn D.toFun (closedBall (0 : Vector 4) 1) := by
    intro x hx y hy hxy
    have he : (⟨x, hx⟩ : closedBall (0 : Vector 4) 1) = ⟨y, hy⟩ :=
      D.embedded.injective hxy
    exact congrArg Subtype.val he
  have hN : ((e.ambientDimension - 6) + 5) + 4 + 3 = e.ambientDimension + 6 := by
    have := e.dimension_le_ambient (f (pole 3))
    omega
  obtain ⟨A⟩ := DiskThickening.nonempty_framedProduct D.toFun T
    (fun _ _ ↦ D.smooth.contDiffAt) hDi D.immersive hTs hTn hTr hN
  refine ⟨D, r, hr, hr1, T, A, hTb, ?_, ?_, hTc⟩
  · intro s
    exact (DiskThickening.map_core D.toFun A.transverse s.val).trans (D.boundary s)
  · intro s
    exact (A.normalFrame_core s.val (sphere_subset_closedBall s.property)).trans (hTb s)

theorem exists_framedDiskThickening (h : M ≃ₜ Sphere 6) (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) :
    ∃ D : DiskData (pole 3) (e.toFun ∘ f),
      ∃ T : Vector 4 → Vector ((e.ambientDimension - 6) + 5) →L[ℝ]
          Vector (e.ambientDimension + 6),
        ∃ A : DiskThickening.FramedProduct D.toFun T,
          (∀ s : Sphere 3, T s.val =
            boundaryFrameOperator (e.normalFrameOnSphere a f s).val) ∧
          (∀ s : Sphere 3, DiskThickening.map D.toFun A.transverse (s.val, 0) =
            appendZeroMap e.ambientDimension 6 (e.toFun (f s))) ∧
          ∀ s : Sphere 3, A.normalFrame (s.val, 0) =
            boundaryFrameOperator (e.normalFrameOnSphere a f s).val := by
  obtain ⟨D, _, _, _, T, A, hTb, hcore, hnormal, _⟩ :=
    e.exists_framedDiskThickening_collar a h f hf hi hd
  exact ⟨D, T, A, hTb, hcore, hnormal⟩

end NoExoticSixSphere.EuclideanEmbedding
