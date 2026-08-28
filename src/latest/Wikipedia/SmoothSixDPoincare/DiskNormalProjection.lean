import Wikipedia.SmoothSixDPoincare.NativeTangentProjection
import Wikipedia.SmoothSixDPoincare.NestedProjectionDifference

/-!
# The actual normal spaces of an immersed disk in the native manifold

After a genuine Euclidean embedding of the manifold, the disk tangent image
is contained in the manifold tangent image by the native chain rule. Their
orthogonal difference is the normal space inside the manifold, not the larger
normal space in the Euclidean ambient space. Its projection is smooth wherever
the disk derivative is injective.
-/

noncomputable section

open Function Module Set
open scoped Manifold ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.NativeEuclideanEmbedding

variable {E M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [NormedAddCommGroup D] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] (e : NativeEuclideanEmbedding E M)

/-- The actual tangent image of the disk's Euclidean realization. -/
def diskTangentImage (f : D → M) (x : D) :
    Submodule ℝ (EuclideanSpace ℝ (Fin e.ambientDimension)) :=
  (fderiv ℝ (e.toFun ∘ f) x).range

/-- The disk normal space inside the native manifold's embedded tangent space. -/
def diskNormalSpace (f : D → M) (x : D) :
    Submodule ℝ (EuclideanSpace ℝ (Fin e.ambientDimension)) :=
  (e.diskTangentImage f x)ᗮ ⊓ e.tangentImage (f x)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ D] in
/-- The native chain rule identifies the actual Euclidean disk derivative. -/
theorem fderiv_comp_eq {f : D → M} (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) (x : D) :
    fderiv ℝ (e.toFun ∘ f) x =
      (mvfderiv 𝓘(ℝ, E) e.toFun (f x)).comp (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x) := by
  rw [← mfderiv_eq_fderiv, mfderiv_comp x (e.smooth.mdifferentiableAt (by simp))
    (hf.mdifferentiableAt (by simp))]
  rfl

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ D] in
/-- Disk tangent vectors really belong to the manifold tangent space. -/
theorem diskTangentImage_le {f : D → M} (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) (x : D) :
    e.diskTangentImage f x ≤ e.tangentImage (f x) := by
  rw [diskTangentImage, e.fderiv_comp_eq hf x]
  exact LinearMap.range_comp_le_range _ _

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ D] in
/-- An injective native disk derivative remains injective in the actual Euclidean embedding. -/
theorem injective_fderiv_comp {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) {x : D}
    (hi : Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x)) :
    Injective (fderiv ℝ (e.toFun ∘ f) x) := by
  rw [e.fderiv_comp_eq hf x]
  exact (e.injective_mvfderiv (f x)).comp hi

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ D] in
/-- The intrinsic normal space has exactly the expected dimension. -/
theorem finrank_diskTangent_add_normal {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) {x : D}
    (hi : Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x)) :
    finrank ℝ D + finrank ℝ (e.diskNormalSpace f x) = finrank ℝ E := by
  have hd : finrank ℝ (e.diskTangentImage f x) = finrank ℝ D :=
    LinearMap.finrank_range_of_inj (e.injective_fderiv_comp hf hi)
  calc
    finrank ℝ D + finrank ℝ (e.diskNormalSpace f x) =
        finrank ℝ (e.diskTangentImage f x) + finrank ℝ (e.diskNormalSpace f x) :=
      congrArg (fun n => n + finrank ℝ (e.diskNormalSpace f x)) hd.symm
    _ = finrank ℝ (e.tangentImage (f x)) :=
      Submodule.finrank_add_inf_finrank_orthogonal (e.diskTangentImage_le hf x)
    _ = finrank ℝ E := e.finrank_tangentImage (f x)

/-- A total operator formula whose value on the immersion locus is the normal projection. -/
def diskNormalProjection (f : D → M) (x : D) :
    EuclideanSpace ℝ (Fin e.ambientDimension) →L[ℝ]
      EuclideanSpace ℝ (Fin e.ambientDimension) :=
  e.tangentProjection (f x) - NoExoticSixSphere.gramProjection (fderiv ℝ (e.toFun ∘ f) x)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- On the immersion locus the formula is exactly the intrinsic normal projection. -/
theorem diskNormalProjection_eq {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) {x : D}
    (hi : Injective (fderiv ℝ (e.toFun ∘ f) x)) :
    e.diskNormalProjection f x = (e.diskNormalSpace f x).starProjection := by
  rw [diskNormalProjection, NoExoticSixSphere.gramProjection_eq_starProjection _ hi]
  exact (DiskFraming.starProjection_orthogonal_inf_eq_sub (e.diskTangentImage_le hf x)).symm

/-- The normal projection is smooth on the actual open Euclidean immersion locus. -/
theorem contDiffOn_diskNormalProjection {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) :
    ContDiffOn ℝ ∞ (e.diskNormalProjection f)
      {x | Injective (fderiv ℝ (e.toFun ∘ f) x)} := by
  have hs : ContDiff ℝ ∞ (e.toFun ∘ f) := (e.smooth.comp hf).contDiff
  have hd : ContDiff ℝ ∞ (fderiv ℝ (e.toFun ∘ f)) := (contDiff_infty_iff_fderiv.mp hs).2
  have hT : ContDiff ℝ ∞ (fun x => e.tangentProjection (f x)) :=
    (e.contMDiff_tangentProjection.comp hf).contDiff
  intro x hx
  have hp : ContDiffAt ℝ ∞ (e.diskNormalProjection f) x := hT.contDiffAt.sub
    (NoExoticSixSphere.contMDiffAt_gramProjection hd.contMDiff.contMDiffAt hx).contDiffAt
  exact hp.contDiffWithinAt

/-- This genuine open immersion locus contains every compact region of native immersion. -/
theorem exists_open_diskNormalProjection {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) {K : Set D}
    (hi : ∀ x ∈ K, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x)) :
    ∃ U : Set D, IsOpen U ∧ K ⊆ U ∧ ContDiffOn ℝ ∞ (e.diskNormalProjection f) U ∧
      ∀ x ∈ U, e.diskNormalProjection f x = (e.diskNormalSpace f x).starProjection := by
  have hs : ContDiff ℝ ∞ (e.toFun ∘ f) := (e.smooth.comp hf).contDiff
  have hd : ContDiff ℝ ∞ (fderiv ℝ (e.toFun ∘ f)) := (contDiff_infty_iff_fderiv.mp hs).2
  refine ⟨{x | Injective (fderiv ℝ (e.toFun ∘ f) x)},
    ContinuousLinearMap.isOpen_injective.preimage hd.continuous,
    fun x hx => e.injective_fderiv_comp hf (hi x hx),
    e.contDiffOn_diskNormalProjection hf, ?_⟩
  exact fun _ hx => e.diskNormalProjection_eq hf hx

end Wikipedia.SmoothSixDPoincare.NativeEuclideanEmbedding
