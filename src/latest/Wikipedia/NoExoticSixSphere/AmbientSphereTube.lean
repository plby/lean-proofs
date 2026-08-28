import Wikipedia.NoExoticSixSphere.SphereInternalNormalSpace

/-!
# The actual ambient sphere tube and its native core derivative

Add the internal normal vectors to the original embedded sphere. At the zero
section its native derivative consists of the original sphere derivative and
the transverse columns. No global ambient product inner product is used.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization

variable {n q : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (f : Sphere 3 → M)
  (C : Sphere 3 → Vector q →L[ℝ] Vector e.ambientDimension)

def ambientSphereTube (p : Sphere 3 × Vector q) : Vector e.ambientDimension :=
  e.toFun (f p.1) + C p.1 p.2

theorem ambientSphereTube_core (s : Sphere 3) :
    e.ambientSphereTube f C (s, 0) = e.toFun (f s) := by simp [ambientSphereTube]

variable (hf : ContMDiff (𝓡 3) (𝓡 n) ∞ f)
  (hC : ContMDiff (𝓡 3) 𝓘(ℝ, Vector q →L[ℝ] Vector e.ambientDimension) ∞ C)

include hf hC in
theorem contMDiff_ambientSphereTube :
    ContMDiff ((𝓡 3).prod (𝓡 q)) (𝓡 e.ambientDimension) ∞ (e.ambientSphereTube f C) :=
  ((e.smooth.comp hf).comp contMDiff_fst).add
    ((hC.comp contMDiff_fst).clm_apply contMDiff_snd)

include hf hC in
theorem mfderiv_ambientSphereTube_core (s : Sphere 3) :
    mfderiv ((𝓡 3).prod (𝓡 q)) (𝓡 e.ambientDimension) (e.ambientSphereTube f C) (s, 0) =
      (mfderiv (𝓡 3) (𝓡 e.ambientDimension) (e.toFun ∘ f) s).coprod (C s) := by
  have hl : (fun t : Sphere 3 ↦ e.ambientSphereTube f C (t, 0)) = e.toFun ∘ f :=
    funext (e.ambientSphereTube_core f C)
  have hr : mfderiv (𝓡 q) (𝓡 e.ambientDimension)
      (fun v : Vector q ↦ e.ambientSphereTube f C (s, v)) 0 = C s := by
    rw [mfderiv_eq_fderiv]
    have h := (hasFDerivAt_const (e.toFun (f s)) (0 : Vector q)).add (C s).hasFDerivAt
    simpa only [zero_add] using! h.fderiv
  apply ContinuousLinearMap.ext
  intro v
  rw [mfderiv_prod_eq_add_apply
    ((e.contMDiff_ambientSphereTube f C hf hC).mdifferentiableAt (by simp)), hl, hr]
  rfl

end NoExoticSixSphere.EuclideanEmbedding
