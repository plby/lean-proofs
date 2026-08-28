import Wikipedia.HopfProblem.DegreeCollapseSevenDimensionalSurgeryDisk
import Wikipedia.NoExoticSixSphere.SmoothRangeOrthonormalization
import Wikipedia.NoExoticSixSphere.NormalBundle

/-!
# Prescribed surgery frames from the actual seven-manifold normal bundle

Restrict the original full normal frame along the original smooth embedded
three-sphere. Its normality follows from the actual native chain rule.
The preceding construction then produces a framed spanning product without
any parity hypothesis. The ambient embedding, normal frame, and embedded
sphere are explicit geometric inputs; existence of a filling is not inferred.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
  (f : NoExoticSixSphere.Sphere 3 → M)

def normalFrameOnSphere (s : NoExoticSixSphere.Sphere 3) :
    Space e.ambientDimension (e.ambientDimension - 7) :=
  a.orthonormal (f s)

theorem contMDiff_normalFrameOnSphere (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f) :
    ContMDiff (𝓡 3) 𝓘(ℝ, Vector (e.ambientDimension - 7) →L[ℝ] Vector e.ambientDimension)
      ∞ (fun s ↦ (normalFrameOnSphere e a f s).val) :=
  a.contMDiff_orthonormal.comp hf

theorem normalFrameOnSphere_range (s : NoExoticSixSphere.Sphere 3) :
    (normalFrameOnSphere e a f s).val.range = e.normalFiber (f s) :=
  (a.orthonormal_range (f s)).trans (e.range_normalProjection (f s))

theorem normalFrameOnSphere_normal (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f)
    (s : NoExoticSixSphere.Sphere 3) :
    (normalFrameOnSphere e a f s).val.range ≤
      (mfderiv (𝓡 3) (𝓡 e.ambientDimension) (e.toFun ∘ f) s).rangeᗮ := by
  rw [normalFrameOnSphere_range]
  apply Submodule.orthogonal_le
  rw [mfderiv_comp s (e.smooth.mdifferentiableAt (by simp))
    (hf.mdifferentiableAt (by simp))]
  rintro _ ⟨v, rfl⟩
  exact ⟨_, rfl⟩

theorem nonempty_diskProduct_of_native_sphere (b : NoExoticSixSphere.Sphere 3)
    (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s)) :
    Nonempty (DiskProduct b (e.toFun ∘ f) (normalFrameOnSphere e a f)) := by
  have hdim := e.dimension_le_ambient (f b)
  apply nonempty_diskProduct (by omega : (e.ambientDimension - 7) + 7 = e.ambientDimension)
    b (e.toFun ∘ f) (e.smooth.comp hf) (e.closedEmbedding.injective.comp hi)
    ?_ (normalFrameOnSphere e a f) (contMDiff_normalFrameOnSphere e a f hf)
    (normalFrameOnSphere_normal e a f hf)
  intro s
  rw [mfderiv_comp s (e.smooth.mdifferentiableAt (by simp))
    (hf.mdifferentiableAt (by simp))]
  exact (e.injective_mfderiv (f s)).comp (hd s)

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
