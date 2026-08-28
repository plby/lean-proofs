import Wikipedia.NoExoticSixSphere.FramedSpanningDisk
import Wikipedia.NoExoticSixSphere.SmoothRangeOrthonormalization
import Wikipedia.NoExoticSixSphere.NormalBundle

/-!
# Spanning disks for spheres in the original normally framed manifold

The frame is obtained from the given smooth frame of the actual normal
projection. Restriction along the original smooth sphere map preserves
normality. The constructed disk therefore has the required smooth partial
normal frame, without changing the manifold's atlas or replacing its tangent
spaces by abstract plane data.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel StabilizedSpanningDisk

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (f : Sphere 3 → M)

def normalFrameOnSphere (s : Sphere 3) : Space e.ambientDimension (e.ambientDimension - 6) :=
  a.orthonormal (f s)

theorem contMDiff_normalFrameOnSphere (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) :
    ContMDiff (𝓡 3) 𝓘(ℝ, Vector (e.ambientDimension - 6) →L[ℝ] Vector e.ambientDimension)
      ∞ (fun s ↦ (e.normalFrameOnSphere a f s).val) :=
  a.contMDiff_orthonormal.comp hf

theorem normalFrameOnSphere_range (s : Sphere 3) :
    (e.normalFrameOnSphere a f s).val.range = e.normalFiber (f s) :=
  (a.orthonormal_range (f s)).trans (e.range_normalProjection (f s))

theorem normalFrameOnSphere_normal (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (s : Sphere 3) :
    (e.normalFrameOnSphere a f s).val.range ≤
      (mfderiv (𝓡 3) (𝓡 e.ambientDimension) (e.toFun ∘ f) s).rangeᗮ := by
  rw [e.normalFrameOnSphere_range]
  apply Submodule.orthogonal_le
  rw [mfderiv_comp s (e.smooth.mdifferentiableAt (by simp))
    (hf.mdifferentiableAt (by simp))]
  rintro _ ⟨v, rfl⟩
  exact ⟨_, rfl⟩

omit a in
/-- An embedded immersive sphere in the original manifold has actual spanning-disk data. -/
theorem nonempty_sphereDiskData (b : Sphere 3) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hi : Injective f) (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) :
    Nonempty (DiskData b (e.toFun ∘ f)) := by
  apply nonempty_diskData b (e.toFun ∘ f) (e.smooth.comp hf)
    (e.closedEmbedding.injective.comp hi)
  intro s
  rw [mfderiv_comp s (e.smooth.mdifferentiableAt (by simp))
    (hf.mdifferentiableAt (by simp))]
  exact (e.injective_mfderiv (f s)).comp (hd s)

/-- Its boundary partial frame comes from the actual original normal frame and the five new axes. -/
theorem normalFrameOnSphere_normal_disk {b : Sphere 3}
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (D : DiskData b (e.toFun ∘ f)) (s : Sphere 3) :
    (boundaryFrame (e.normalFrameOnSphere a f s)).val.range ≤
      (fderiv ℝ D.toFun s.val).rangeᗮ := by
  obtain ⟨V, hV, hSV, heq⟩ := D.collar_eq
  exact boundaryFrame_normal_disk b (e.toFun ∘ f) (e.smooth.comp hf)
    (e.normalFrameOnSphere a f) (e.normalFrameOnSphere_normal a f hf) hV hSV heq s

end NoExoticSixSphere.EuclideanEmbedding
