import Wikipedia.HopfProblem.DegreeCollapseLowSphereNormalSpace

/-!

# Actual low-dimensional ambient tubes span the original tangent image

The sphere derivative and its internal normal frame give an injective native
derivative on the actual product S^d times R^(7-d). Its range equals the
original seven-manifold tangent image. Injectivity of the original sphere
derivative supplies the required dimension inequality.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

open NoExoticSixSphere GLOrthonormalization

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M) (f : NoExoticSixSphere.Sphere d → M)
  (C : NoExoticSixSphere.Sphere d → Vector (7 - d) →L[ℝ] Vector e.ambientDimension)

def ambientSphereTube (p : NoExoticSixSphere.Sphere d × Vector (7 - d)) :
    Vector e.ambientDimension :=
  e.toFun (f p.1) + C p.1 p.2

theorem ambientSphereTube_core (s : NoExoticSixSphere.Sphere d) :
    ambientSphereTube e f C (s, 0) = e.toFun (f s) := by simp [ambientSphereTube]

variable (hf : ContMDiff (𝓡 d) (𝓡 7) ∞ f)
  (hC : ContMDiff (𝓡 d) 𝓘(ℝ, Vector (7 - d) →L[ℝ] Vector e.ambientDimension) ∞ C)

include hf hC in
theorem contMDiff_ambientSphereTube :
    ContMDiff ((𝓡 d).prod (𝓡 (7 - d))) (𝓡 e.ambientDimension) ∞ (ambientSphereTube e f C) :=
  ((e.smooth.comp hf).comp contMDiff_fst).add
    ((hC.comp contMDiff_fst).clm_apply contMDiff_snd)

include hf hC in
theorem mfderiv_ambientSphereTube_core (s : NoExoticSixSphere.Sphere d) :
    mfderiv ((𝓡 d).prod (𝓡 (7 - d))) (𝓡 e.ambientDimension) (ambientSphereTube e f C) (s, 0) =
      (mfderiv (𝓡 d) (𝓡 e.ambientDimension) (e.toFun ∘ f) s).coprod (C s) := by
  have hl : (fun t : NoExoticSixSphere.Sphere d ↦ ambientSphereTube e f C (t, 0)) =
      e.toFun ∘ f :=
    funext (ambientSphereTube_core e f C)
  have hr : mfderiv (𝓡 (7 - d)) (𝓡 e.ambientDimension)
      (fun v : Vector (7 - d) ↦ ambientSphereTube e f C (s, v)) 0 = C s := by
    rw [mfderiv_eq_fderiv]
    have h := (hasFDerivAt_const (e.toFun (f s)) (0 : Vector (7 - d))).add (C s).hasFDerivAt
    simpa only [zero_add] using! h.fderiv
  apply ContinuousLinearMap.ext
  intro v
  rw [mfderiv_prod_eq_add_apply
    ((contMDiff_ambientSphereTube e f C hf hC).mdifferentiableAt (by simp)), hl, hr]
  rfl

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

open NoExoticSixSphere GLOrthonormalization

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M) (f : NoExoticSixSphere.Sphere d → M)
  (C : NoExoticSixSphere.Sphere d → Vector (7 - d) →L[ℝ] Vector e.ambientDimension)
  (hf : ContMDiff (𝓡 d) (𝓡 7) ∞ f)
  (hC : ContMDiff (𝓡 d) 𝓘(ℝ, Vector (7 - d) →L[ℝ] Vector e.ambientDimension) ∞ C)
  (hd : ∀ s, Injective (mfderiv (𝓡 d) (𝓡 7) f s))
  (hiC : ∀ s, Injective (C s)) (hCr : ∀ s, (C s).range = sphereNormalSpace e f s)

include hf hC hd hiC hCr in
theorem injective_mfderiv_ambientSphereTube_core (s : NoExoticSixSphere.Sphere d) :
    Injective (mfderiv ((𝓡 d).prod (𝓡 (7 - d))) (𝓡 e.ambientDimension)
      (ambientSphereTube e f C) (s, 0)) := by
  rw [mfderiv_ambientSphereTube_core e f C hf hC s]
  let B : Vector d →L[ℝ] Vector e.ambientDimension :=
    mfderiv (𝓡 d) (𝓡 e.ambientDimension) (e.toFun ∘ f) s
  have horth : (C s).range ≤ B.rangeᗮ := by
    rw [hCr s]
    exact inf_le_right
  change Injective (B.toLinearMap.coprod (C s).toLinearMap)
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_coprod_of_disjoint_range _ _
    (B.range.orthogonal_disjoint.mono_right horth),
    LinearMap.ker_eq_bot.mpr (show Injective B from injective_mfderiv_embeddedSphere e f hf hd s),
    LinearMap.ker_eq_bot.mpr (hiC s), Submodule.prod_bot]

include hf hC hd hiC hCr in
theorem range_mfderiv_ambientSphereTube_core (s : NoExoticSixSphere.Sphere d) :
    (mfderiv ((𝓡 d).prod (𝓡 (7 - d))) (𝓡 e.ambientDimension)
      (ambientSphereTube e f C) (s, 0)).range = e.tangentImage (f s) := by
  let B : Vector d →L[ℝ] Vector e.ambientDimension :=
    mfderiv (𝓡 d) (𝓡 e.ambientDimension) (e.toFun ∘ f) s
  let G : (Vector d × Vector (7 - d)) →L[ℝ] Vector e.ambientDimension :=
    mfderiv ((𝓡 d).prod (𝓡 (7 - d))) (𝓡 e.ambientDimension) (ambientSphereTube e f C) (s, 0)
  have hG : G = B.coprod (C s) := mfderiv_ambientSphereTube_core e f C hf hC s
  have hiG : Injective G := injective_mfderiv_ambientSphereTube_core e f C hf hC hd hiC hCr s
  change G.range = e.tangentImage (f s)
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [hG]
    change (B.toLinearMap.coprod (C s).toLinearMap).range ≤ _
    rw [LinearMap.range_coprod]
    exact sup_le (range_mfderiv_embeddedSphere_le e f hf s) ((hCr s).le.trans inf_le_left)
  · rw [LinearMap.finrank_range_of_inj hiG, e.finrank_tangentImage]
    simp only [Module.finrank_prod, finrank_euclideanSpace_fin]
    exact Nat.add_sub_of_le (sphere_dimension_le_seven f hd s)

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery
