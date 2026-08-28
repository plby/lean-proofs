import Wikipedia.NoExoticSixSphere.SixSphereFramedDiskThickening
import Wikipedia.NoExoticSixSphere.ManifoldCollaredTransverseProduct

/-!
# A framed disk thickening with both frames exactly radial on its collar

The candidate's zero geometric parity constructs the partial normal extension.
The complementary transverse frame is then replaced, retaining its original
boundary columns and the full framed embedded product. The disk and both
frames have exact radial collar formulas on one common positive-width annulus.
This is not yet a curved attaching-face identification or a surgery trace.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)

theorem exists_radialFramedDiskThickening (h : M ≃ₜ Sphere 6) (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) :
    ∃ D : DiskData (pole 3) (e.toFun ∘ f), ∃ r : ℝ, (1 / 2 : ℝ) < r ∧ r < 1 ∧
      ∃ T : Vector 4 → Vector ((e.ambientDimension - 6) + 5) →L[ℝ]
          Vector (e.ambientDimension + 6),
        ∃ A : DiskThickening.FramedProduct D.toFun T,
          (∀ s : Sphere 3, T s.val =
            boundaryFrameOperator (e.normalFrameOnSphere a f s).val) ∧
          ∀ x ∈ closedBall (0 : Vector 4) 1, r ≤ ‖x‖ →
            D.toFun x = collar (pole 3) (e.toFun ∘ f) x ∧
            T x = boundaryFrameOperator
              (e.normalFrameOnSphere a f (SphereRadialRetraction.retract (pole 3) x)).val ∧
            A.transverse x = A.transverse (SphereRadialRetraction.retract (pole 3) x).val := by
  obtain ⟨D, r₀, _, hr₀, T, A₀, hTb, _, _, hTc⟩ :=
    e.exists_framedDiskThickening_collar a h f hf hi hd
  obtain ⟨r, _, hr1, A, _, hAc⟩ :=
    e.exists_radialTransverseProduct a f hf hd D A₀ hTb r₀ hr₀
      (fun x hx hxr ↦ (hTc x hx hxr).2)
  refine ⟨D, max r (3 / 4), ?_, max_lt hr1 (by norm_num), T, A, hTb, ?_⟩
  · exact lt_of_lt_of_le (by norm_num : (1 / 2 : ℝ) < 3 / 4) (le_max_right _ _)
  · intro x hx hxr
    exact hAc x hx ((le_max_left _ _).trans hxr)

end NoExoticSixSphere.EuclideanEmbedding
