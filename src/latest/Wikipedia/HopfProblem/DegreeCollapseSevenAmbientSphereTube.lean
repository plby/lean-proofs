import Wikipedia.HopfProblem.DegreeCollapseSevenSphereNormalSpace

/-!
# The actual sphere tube's derivative spans the original seven-dimensional tangent image

The sphere derivative and its internal normal four-frame give an injective
native derivative on the actual product S3 x R4. Its range is the original
seven-manifold tangent image, retaining the original ambient embedding.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

open NoExoticSixSphere GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M) (f : Sphere 3 → M)
  (C : Sphere 3 → Vector 4 →L[ℝ] Vector e.ambientDimension)

def ambientSphereTube (p : Sphere 3 × Vector 4) : Vector e.ambientDimension :=
  e.toFun (f p.1) + C p.1 p.2

theorem ambientSphereTube_core (s : Sphere 3) :
    SevenSurgery.ambientSphereTube e f C (s, 0) = e.toFun (f s) := by simp [ambientSphereTube]

variable (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f)
  (hC : ContMDiff (𝓡 3) 𝓘(ℝ, Vector 4 →L[ℝ] Vector e.ambientDimension) ∞ C)

include hf hC in
theorem contMDiff_ambientSphereTube :
    ContMDiff ((𝓡 3).prod (𝓡 4)) (𝓡 e.ambientDimension) ∞ (SevenSurgery.ambientSphereTube e f C) :=
  ((e.smooth.comp hf).comp contMDiff_fst).add
    ((hC.comp contMDiff_fst).clm_apply contMDiff_snd)

include hf hC in
theorem mfderiv_ambientSphereTube_core (s : Sphere 3) :
    mfderiv ((𝓡 3).prod (𝓡 4)) (𝓡 e.ambientDimension) (SevenSurgery.ambientSphereTube e f C) (s, 0) =
      (mfderiv (𝓡 3) (𝓡 e.ambientDimension) (e.toFun ∘ f) s).coprod (C s) := by
  have hl : (fun t : Sphere 3 ↦ SevenSurgery.ambientSphereTube e f C (t, 0)) = e.toFun ∘ f :=
    funext (SevenSurgery.ambientSphereTube_core e f C)
  have hr : mfderiv (𝓡 4) (𝓡 e.ambientDimension)
      (fun v : Vector 4 ↦ SevenSurgery.ambientSphereTube e f C (s, v)) 0 = C s := by
    rw [mfderiv_eq_fderiv]
    have h := (hasFDerivAt_const (e.toFun (f s)) (0 : Vector 4)).add (C s).hasFDerivAt
    simpa only [zero_add] using! h.fderiv
  apply ContinuousLinearMap.ext
  intro v
  rw [mfderiv_prod_eq_add_apply
    ((SevenSurgery.contMDiff_ambientSphereTube e f C hf hC).mdifferentiableAt (by simp)), hl, hr]
  rfl

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

open NoExoticSixSphere GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M) (f : Sphere 3 → M)
  (C : Sphere 3 → Vector 4 →L[ℝ] Vector e.ambientDimension)
  (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f)
  (hC : ContMDiff (𝓡 3) 𝓘(ℝ, Vector 4 →L[ℝ] Vector e.ambientDimension) ∞ C)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s))
  (hiC : ∀ s, Injective (C s)) (hCr : ∀ s, (C s).range = SevenSurgery.sphereNormalSpace e f s)

include hf hC hd hiC hCr in
theorem injective_mfderiv_ambientSphereTube_core (s : Sphere 3) :
    Injective (mfderiv ((𝓡 3).prod (𝓡 4)) (𝓡 e.ambientDimension)
      (SevenSurgery.ambientSphereTube e f C) (s, 0)) := by
  rw [SevenSurgery.mfderiv_ambientSphereTube_core e f C hf hC s]
  let B : Vector 3 →L[ℝ] Vector e.ambientDimension :=
    mfderiv (𝓡 3) (𝓡 e.ambientDimension) (e.toFun ∘ f) s
  have horth : (C s).range ≤ B.rangeᗮ := by
    rw [hCr s]
    exact inf_le_right
  change Injective (B.toLinearMap.coprod (C s).toLinearMap)
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_coprod_of_disjoint_range _ _
    (B.range.orthogonal_disjoint.mono_right horth),
    LinearMap.ker_eq_bot.mpr (show Injective B from SevenSurgery.injective_mfderiv_embeddedSphere e f hf hd s),
    LinearMap.ker_eq_bot.mpr (hiC s), Submodule.prod_bot]

include hf hC hd hiC hCr in
theorem range_mfderiv_ambientSphereTube_core (s : Sphere 3) :
    (mfderiv ((𝓡 3).prod (𝓡 4)) (𝓡 e.ambientDimension)
      (SevenSurgery.ambientSphereTube e f C) (s, 0)).range = e.tangentImage (f s) := by
  let B : Vector 3 →L[ℝ] Vector e.ambientDimension :=
    mfderiv (𝓡 3) (𝓡 e.ambientDimension) (e.toFun ∘ f) s
  let G : (Vector 3 × Vector 4) →L[ℝ] Vector e.ambientDimension :=
    mfderiv ((𝓡 3).prod (𝓡 4)) (𝓡 e.ambientDimension) (SevenSurgery.ambientSphereTube e f C) (s, 0)
  have hG : G = B.coprod (C s) := SevenSurgery.mfderiv_ambientSphereTube_core e f C hf hC s
  have hiG : Injective G := SevenSurgery.injective_mfderiv_ambientSphereTube_core e f C hf hC hd hiC hCr s
  change G.range = e.tangentImage (f s)
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [hG]
    change (B.toLinearMap.coprod (C s).toLinearMap).range ≤ _
    rw [LinearMap.range_coprod]
    exact sup_le (SevenSurgery.range_mfderiv_embeddedSphere_le e f hf s) ((hCr s).le.trans inf_le_left)
  · rw [LinearMap.finrank_range_of_inj hiG, e.finrank_tangentImage]
    simp [Module.finrank_prod]

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
