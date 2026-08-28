import Wikipedia.HopfProblem.DegreeCollapseLowInternalSphereTube

/-!

# Actual native tube difference with zero core value and derivative

The corrected tube and the affine tube are compared in the original ambient
embedding. Their difference has zero value and native derivative at every
core point. The actual retraction domain controls all smoothness statements.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

open NoExoticSixSphere GLOrthonormalization

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M) (f : NoExoticSixSphere.Sphere d → M)
  (C : NoExoticSixSphere.Sphere d → Vector (7 - d) →L[ℝ] Vector e.ambientDimension)
  (R : EuclideanEmbedding.TubularRetraction e)

def sphereTubeDifference : NoExoticSixSphere.Sphere d × Vector (7 - d) →
    Vector e.ambientDimension :=
  (e.toFun ∘ internalSphereTube e f C R) - ambientSphereTube e f C

theorem sphereTubeDifference_core (s : NoExoticSixSphere.Sphere d) :
    sphereTubeDifference e f C R (s, 0) = 0 := by
  simp only [sphereTubeDifference, Pi.sub_apply, comp_apply,
    internalSphereTube_core e, ambientSphereTube_core e, sub_self]

theorem ambientSphereTube_add_difference (p : NoExoticSixSphere.Sphere d × Vector (7 - d)) :
    ambientSphereTube e f C p + sphereTubeDifference e f C R p =
      e.toFun (internalSphereTube e f C R p) := by
  change ambientSphereTube e f C p +
    (e.toFun (internalSphereTube e f C R p) - ambientSphereTube e f C p) = _
  abel

variable (hf : ContMDiff (𝓡 d) (𝓡 7) ∞ f)
  (hC : ContMDiff (𝓡 d) 𝓘(ℝ, Vector (7 - d) →L[ℝ] Vector e.ambientDimension) ∞ C)

include hf hC in
theorem contMDiffOn_sphereTubeDifference :
    ContMDiffOn ((𝓡 d).prod (𝓡 (7 - d))) (𝓡 e.ambientDimension) ∞
      (sphereTubeDifference e f C R) (sphereTubeDomain e f C R) := by
  exact (e.smooth.comp_contMDiffOn (contMDiffOn_internalSphereTube e f C R hf hC)).sub
    (contMDiff_ambientSphereTube e f C hf hC).contMDiffOn

include hf hC in
theorem contMDiffAt_sphereTubeDifference {p : NoExoticSixSphere.Sphere d × Vector (7 - d)}
    (hp : p ∈ sphereTubeDomain e f C R) :
    ContMDiffAt ((𝓡 d).prod (𝓡 (7 - d))) (𝓡 e.ambientDimension) ∞
      (sphereTubeDifference e f C R) p :=
  (contMDiffOn_sphereTubeDifference e f C R hf hC).contMDiffAt
    ((isOpen_sphereTubeDomain e f C R hf hC).mem_nhds hp)

include hf hC in
theorem mfderiv_sphereTubeDifference_core
    (hd : ∀ s, Injective (mfderiv (𝓡 d) (𝓡 7) f s))
    (hiC : ∀ s, Injective (C s)) (hCr : ∀ s, (C s).range = sphereNormalSpace e f s)
    (s : NoExoticSixSphere.Sphere d) :
    mfderiv ((𝓡 d).prod (𝓡 (7 - d))) (𝓡 e.ambientDimension)
      (sphereTubeDifference e f C R) (s, 0) = 0 := by
  have hs := (contMDiffOn_internalSphereTube e f C R hf hC).contMDiffAt
    ((isOpen_sphereTubeDomain e f C R hf hC).mem_nhds (core_mem_sphereTubeDomain e f C R s))
  have he := e.smooth.contMDiffAt.comp (s, (0 : Vector (7 - d))) hs
  have ha := (contMDiff_ambientSphereTube e f C hf hC).contMDiffAt (x := (s, 0))
  let L : (Vector d × Vector (7 - d)) →L[ℝ] Vector e.ambientDimension :=
    mfderiv ((𝓡 d).prod (𝓡 (7 - d))) (𝓡 e.ambientDimension)
      (e.toFun ∘ internalSphereTube e f C R) (s, 0)
  let B : (Vector d × Vector (7 - d)) →L[ℝ] Vector e.ambientDimension :=
    mfderiv ((𝓡 d).prod (𝓡 (7 - d))) (𝓡 e.ambientDimension)
      (ambientSphereTube e f C) (s, 0)
  have hLB : L = B := mfderiv_embedded_internalSphereTube_core e f C R hf hC hd hiC hCr s
  have hsub : (mfderiv ((𝓡 d).prod (𝓡 (7 - d))) (𝓡 e.ambientDimension)
      (sphereTubeDifference e f C R) (s, 0) :
        (Vector d × Vector (7 - d)) →L[ℝ] Vector e.ambientDimension) = L - B :=
    mfderiv_sub (he.mdifferentiableAt (by simp)) (ha.mdifferentiableAt (by simp))
  exact hsub.trans (by rw [hLB, sub_self]; rfl)

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery
