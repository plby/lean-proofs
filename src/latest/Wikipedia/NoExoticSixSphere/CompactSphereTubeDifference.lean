import Wikipedia.NoExoticSixSphere.CompactSphereTube

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

variable {n q : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (f : Sphere 3 → M)
  (C : Sphere 3 → Vector q →L[ℝ] Vector e.ambientDimension) (R : e.RetractionNear (range f))

def compactSphereTubeDifference : Sphere 3 × Vector q → Vector e.ambientDimension :=
  (e.toFun ∘ e.compactSphereTube f C R) - e.ambientSphereTube f C

theorem compactSphereTubeDifference_core (s : Sphere 3) :
    e.compactSphereTubeDifference f C R (s, 0) = 0 := by
  simp only [compactSphereTubeDifference, Pi.sub_apply, comp_apply,
    e.compactSphereTube_core, e.ambientSphereTube_core, sub_self]

theorem ambientSphereTube_add_compactDifference (p : Sphere 3 × Vector q) :
    e.ambientSphereTube f C p + e.compactSphereTubeDifference f C R p =
      e.toFun (e.compactSphereTube f C R p) := by
  change e.ambientSphereTube f C p +
    (e.toFun (e.compactSphereTube f C R p) - e.ambientSphereTube f C p) = _
  abel

variable (hf : ContMDiff (𝓡 3) (𝓡 n) ∞ f)
  (hC : ContMDiff (𝓡 3) 𝓘(ℝ, Vector q →L[ℝ] Vector e.ambientDimension) ∞ C)

include hf hC in
theorem contMDiffOn_compactSphereTubeDifference :
    ContMDiffOn ((𝓡 3).prod (𝓡 q)) (𝓡 e.ambientDimension) ∞
      (e.compactSphereTubeDifference f C R) (e.compactSphereTubeDomain f C R) := by
  exact (e.smooth.comp_contMDiffOn (e.contMDiffOn_compactSphereTube f C R hf hC)).sub
    (e.contMDiff_ambientSphereTube f C hf hC).contMDiffOn

include hf hC in
theorem contMDiffAt_compactSphereTubeDifference {p : Sphere 3 × Vector q}
    (hp : p ∈ e.compactSphereTubeDomain f C R) :
    ContMDiffAt ((𝓡 3).prod (𝓡 q)) (𝓡 e.ambientDimension) ∞
      (e.compactSphereTubeDifference f C R) p :=
  (e.contMDiffOn_compactSphereTubeDifference f C R hf hC).contMDiffAt
    ((e.isOpen_compactSphereTubeDomain f C R hf hC).mem_nhds hp)

include hf hC in
theorem mfderiv_compactSphereTubeDifference_core
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 n) f s))
    (hiC : ∀ s, Injective (C s)) (hCr : ∀ s, (C s).range = e.sphereNormalSpace f s)
    (s : Sphere 3) :
    mfderiv ((𝓡 3).prod (𝓡 q)) (𝓡 e.ambientDimension)
      (e.compactSphereTubeDifference f C R) (s, 0) = 0 := by
  have hs := (e.contMDiffOn_compactSphereTube f C R hf hC).contMDiffAt
    ((e.isOpen_compactSphereTubeDomain f C R hf hC).mem_nhds
      (e.core_mem_compactSphereTubeDomain f C R s))
  have he := e.smooth.contMDiffAt.comp (s, (0 : Vector q)) hs
  have ha := (e.contMDiff_ambientSphereTube f C hf hC).contMDiffAt (x := (s, 0))
  let L : (Vector 3 × Vector q) →L[ℝ] Vector e.ambientDimension :=
    mfderiv ((𝓡 3).prod (𝓡 q)) (𝓡 e.ambientDimension)
      (e.toFun ∘ e.compactSphereTube f C R) (s, 0)
  let B : (Vector 3 × Vector q) →L[ℝ] Vector e.ambientDimension :=
    mfderiv ((𝓡 3).prod (𝓡 q)) (𝓡 e.ambientDimension)
      (e.ambientSphereTube f C) (s, 0)
  have hLB : L = B := e.mfderiv_embedded_compactSphereTube_core f C R hf hC hd hiC hCr s
  have hsub : (mfderiv ((𝓡 3).prod (𝓡 q)) (𝓡 e.ambientDimension)
      (e.compactSphereTubeDifference f C R) (s, 0) :
        (Vector 3 × Vector q) →L[ℝ] Vector e.ambientDimension) = L - B :=
    mfderiv_sub (he.mdifferentiableAt (by simp)) (ha.mdifferentiableAt (by simp))
  exact hsub.trans (by rw [hLB, sub_self]; rfl)

end NoExoticSixSphere.EuclideanEmbedding
