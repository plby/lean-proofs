import Wikipedia.HopfProblem.DegreeCollapseSevenInternalSphereTube

/-!
# SevenSphereTubeDifference

The actual curved-minus-affine tube difference has zero value and native derivative on its core.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

open NoExoticSixSphere GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M) (f : Sphere 3 → M)
  (C : Sphere 3 → Vector 4 →L[ℝ] Vector e.ambientDimension) (R : EuclideanEmbedding.TubularRetraction e)

def sphereTubeDifference : Sphere 3 × Vector 4 → Vector e.ambientDimension :=
  (e.toFun ∘ SevenSurgery.internalSphereTube e f C R) - SevenSurgery.ambientSphereTube e f C

theorem sphereTubeDifference_core (s : Sphere 3) : SevenSurgery.sphereTubeDifference e f C R (s, 0) = 0 := by
  simp only [sphereTubeDifference, Pi.sub_apply, comp_apply,
    SevenSurgery.internalSphereTube_core e, SevenSurgery.ambientSphereTube_core e, sub_self]

theorem ambientSphereTube_add_difference (p : Sphere 3 × Vector 4) :
    SevenSurgery.ambientSphereTube e f C p + SevenSurgery.sphereTubeDifference e f C R p =
      e.toFun (SevenSurgery.internalSphereTube e f C R p) := by
  change SevenSurgery.ambientSphereTube e f C p +
    (e.toFun (SevenSurgery.internalSphereTube e f C R p) - SevenSurgery.ambientSphereTube e f C p) = _
  abel

variable (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f)
  (hC : ContMDiff (𝓡 3) 𝓘(ℝ, Vector 4 →L[ℝ] Vector e.ambientDimension) ∞ C)

include hf hC in
theorem contMDiffOn_sphereTubeDifference :
    ContMDiffOn ((𝓡 3).prod (𝓡 4)) (𝓡 e.ambientDimension) ∞
      (SevenSurgery.sphereTubeDifference e f C R) (SevenSurgery.sphereTubeDomain e f C R) := by
  exact (e.smooth.comp_contMDiffOn (SevenSurgery.contMDiffOn_internalSphereTube e f C R hf hC)).sub
    (SevenSurgery.contMDiff_ambientSphereTube e f C hf hC).contMDiffOn

include hf hC in
theorem contMDiffAt_sphereTubeDifference {p : Sphere 3 × Vector 4}
    (hp : p ∈ SevenSurgery.sphereTubeDomain e f C R) :
    ContMDiffAt ((𝓡 3).prod (𝓡 4)) (𝓡 e.ambientDimension) ∞
      (SevenSurgery.sphereTubeDifference e f C R) p :=
  (SevenSurgery.contMDiffOn_sphereTubeDifference e f C R hf hC).contMDiffAt
    ((SevenSurgery.isOpen_sphereTubeDomain e f C R hf hC).mem_nhds hp)

include hf hC in
theorem mfderiv_sphereTubeDifference_core
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s))
    (hiC : ∀ s, Injective (C s)) (hCr : ∀ s, (C s).range = SevenSurgery.sphereNormalSpace e f s)
    (s : Sphere 3) :
    mfderiv ((𝓡 3).prod (𝓡 4)) (𝓡 e.ambientDimension)
      (SevenSurgery.sphereTubeDifference e f C R) (s, 0) = 0 := by
  have hs := (SevenSurgery.contMDiffOn_internalSphereTube e f C R hf hC).contMDiffAt
    ((SevenSurgery.isOpen_sphereTubeDomain e f C R hf hC).mem_nhds (SevenSurgery.core_mem_sphereTubeDomain e f C R s))
  have he := e.smooth.contMDiffAt.comp (s, (0 : Vector 4)) hs
  have ha := (SevenSurgery.contMDiff_ambientSphereTube e f C hf hC).contMDiffAt (x := (s, 0))
  let L : (Vector 3 × Vector 4) →L[ℝ] Vector e.ambientDimension :=
    mfderiv ((𝓡 3).prod (𝓡 4)) (𝓡 e.ambientDimension)
      (e.toFun ∘ SevenSurgery.internalSphereTube e f C R) (s, 0)
  let B : (Vector 3 × Vector 4) →L[ℝ] Vector e.ambientDimension :=
    mfderiv ((𝓡 3).prod (𝓡 4)) (𝓡 e.ambientDimension)
      (SevenSurgery.ambientSphereTube e f C) (s, 0)
  have hLB : L = B := SevenSurgery.mfderiv_embedded_internalSphereTube_core e f C R hf hC hd hiC hCr s
  have hsub : (mfderiv ((𝓡 3).prod (𝓡 4)) (𝓡 e.ambientDimension)
      (SevenSurgery.sphereTubeDifference e f C R) (s, 0) :
        (Vector 3 × Vector 4) →L[ℝ] Vector e.ambientDimension) = L - B :=
    mfderiv_sub (he.mdifferentiableAt (by simp)) (ha.mdifferentiableAt (by simp))
  exact hsub.trans (by rw [hLB, sub_self]; rfl)

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
