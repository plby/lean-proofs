import Wikipedia.NoExoticSixSphere.InternalSphereTube

/-!
# The curved-minus-affine sphere-tube difference and its zero core jet

The difference is formed from the actual original-manifold retraction and
ambient tube. It is smooth on the genuine retraction domain, zero on the
core, and has zero native derivative there when the transverse frame spans
the original internal normal bundle. No equality away from the core is assumed.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M) (f : Sphere 3 → M)
  (C : Sphere 3 → Vector 3 →L[ℝ] Vector e.ambientDimension) (R : TubularRetraction e)

def sphereTubeDifference : Sphere 3 × Vector 3 → Vector e.ambientDimension :=
  (e.toFun ∘ e.internalSphereTube f C R) - e.ambientSphereTube f C

theorem sphereTubeDifference_core (s : Sphere 3) : e.sphereTubeDifference f C R (s, 0) = 0 := by
  simp only [sphereTubeDifference, Pi.sub_apply, comp_apply,
    e.internalSphereTube_core, e.ambientSphereTube_core, sub_self]

theorem ambientSphereTube_add_difference (p : Sphere 3 × Vector 3) :
    e.ambientSphereTube f C p + e.sphereTubeDifference f C R p =
      e.toFun (e.internalSphereTube f C R p) := by
  change e.ambientSphereTube f C p +
    (e.toFun (e.internalSphereTube f C R p) - e.ambientSphereTube f C p) = _
  abel

variable (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
  (hC : ContMDiff (𝓡 3) 𝓘(ℝ, Vector 3 →L[ℝ] Vector e.ambientDimension) ∞ C)

include hf hC in
theorem contMDiffOn_sphereTubeDifference :
    ContMDiffOn ((𝓡 3).prod (𝓡 3)) (𝓡 e.ambientDimension) ∞
      (e.sphereTubeDifference f C R) (e.sphereTubeDomain f C R) := by
  exact (e.smooth.comp_contMDiffOn (e.contMDiffOn_internalSphereTube f C R hf hC)).sub
    (e.contMDiff_ambientSphereTube f C hf hC).contMDiffOn

include hf hC in
theorem contMDiffAt_sphereTubeDifference {p : Sphere 3 × Vector 3}
    (hp : p ∈ e.sphereTubeDomain f C R) :
    ContMDiffAt ((𝓡 3).prod (𝓡 3)) (𝓡 e.ambientDimension) ∞
      (e.sphereTubeDifference f C R) p :=
  (e.contMDiffOn_sphereTubeDifference f C R hf hC).contMDiffAt
    ((e.isOpen_sphereTubeDomain f C R hf hC).mem_nhds hp)

include hf hC in
theorem mfderiv_sphereTubeDifference_core
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
    (hiC : ∀ s, Injective (C s)) (hCr : ∀ s, (C s).range = e.sphereNormalSpace f s)
    (s : Sphere 3) :
    mfderiv ((𝓡 3).prod (𝓡 3)) (𝓡 e.ambientDimension)
      (e.sphereTubeDifference f C R) (s, 0) = 0 := by
  have hs := (e.contMDiffOn_internalSphereTube f C R hf hC).contMDiffAt
    ((e.isOpen_sphereTubeDomain f C R hf hC).mem_nhds (e.core_mem_sphereTubeDomain f C R s))
  have he := e.smooth.contMDiffAt.comp (s, (0 : Vector 3)) hs
  have ha := (e.contMDiff_ambientSphereTube f C hf hC).contMDiffAt (x := (s, 0))
  let L : (Vector 3 × Vector 3) →L[ℝ] Vector e.ambientDimension :=
    mfderiv ((𝓡 3).prod (𝓡 3)) (𝓡 e.ambientDimension)
      (e.toFun ∘ e.internalSphereTube f C R) (s, 0)
  let B : (Vector 3 × Vector 3) →L[ℝ] Vector e.ambientDimension :=
    mfderiv ((𝓡 3).prod (𝓡 3)) (𝓡 e.ambientDimension)
      (e.ambientSphereTube f C) (s, 0)
  have hLB : L = B := e.mfderiv_embedded_internalSphereTube_core f C R hf hC hd hiC hCr s
  have hsub : (mfderiv ((𝓡 3).prod (𝓡 3)) (𝓡 e.ambientDimension)
      (e.sphereTubeDifference f C R) (s, 0) :
        (Vector 3 × Vector 3) →L[ℝ] Vector e.ambientDimension) = L - B :=
    mfderiv_sub (he.mdifferentiableAt (by simp)) (ha.mdifferentiableAt (by simp))
  exact hsub.trans (by rw [hLB, sub_self]; rfl)

end NoExoticSixSphere.EuclideanEmbedding
