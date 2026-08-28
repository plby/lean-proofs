import Wikipedia.HopfProblem.DegreeCollapseSevenAmbientSphereTube
import Wikipedia.NoExoticSixSphere.TubularRetractionDifferential
import Wikipedia.SmoothSixDPoincare.BoundarylessLocalInverse

/-!
# The original seven-manifold tube and its genuine local inverses

Retraction of the actual ambient tube retains the native atlas. The exact
core derivative is invertible, and compactness of the original sphere
supplies a positive embedded closed product in the actual retraction domain.
The retraction is supplied explicitly; no filling is inferred.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

open NoExoticSixSphere GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M) (f : Sphere 3 → M)
  (C : Sphere 3 → Vector 4 →L[ℝ] Vector e.ambientDimension)
  (r : EuclideanEmbedding.TubularRetraction e)

def sphereTubeDomain : Set (Sphere 3 × Vector 4) := (SevenSurgery.ambientSphereTube e f C) ⁻¹' r.domain

def internalSphereTube : Sphere 3 × Vector 4 → M := r.toFun ∘ SevenSurgery.ambientSphereTube e f C

theorem internalSphereTube_core (s : Sphere 3) : SevenSurgery.internalSphereTube e f C r (s, 0) = f s := by
  change r.toFun (SevenSurgery.ambientSphereTube e f C (s, 0)) = f s
  rw [SevenSurgery.ambientSphereTube_core e]
  exact r.fixes (f s)

theorem core_mem_sphereTubeDomain (s : Sphere 3) : (s, 0) ∈ SevenSurgery.sphereTubeDomain e f C r := by
  change SevenSurgery.ambientSphereTube e f C (s, 0) ∈ r.domain
  rw [SevenSurgery.ambientSphereTube_core e]
  exact r.contains ⟨f s, rfl⟩

variable (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f)
  (hC : ContMDiff (𝓡 3) 𝓘(ℝ, Vector 4 →L[ℝ] Vector e.ambientDimension) ∞ C)

include hf hC in
theorem isOpen_sphereTubeDomain : IsOpen (SevenSurgery.sphereTubeDomain e f C r) :=
  r.domain.isOpen.preimage (SevenSurgery.contMDiff_ambientSphereTube e f C hf hC).continuous

include hf hC in
theorem contMDiffOn_internalSphereTube :
    ContMDiffOn ((𝓡 3).prod (𝓡 4)) (𝓡 7) ∞ (SevenSurgery.internalSphereTube e f C r)
      (SevenSurgery.sphereTubeDomain e f C r) :=
  r.smooth.comp (SevenSurgery.contMDiff_ambientSphereTube e f C hf hC).contMDiffOn (fun _ hp ↦ hp)

include hf hC in
theorem mfderiv_internalSphereTube_core (s : Sphere 3) :
    mfderiv ((𝓡 3).prod (𝓡 4)) (𝓡 7) (SevenSurgery.internalSphereTube e f C r) (s, 0) =
      (mfderiv (𝓡 e.ambientDimension) (𝓡 7) r.toFun (e.toFun (f s))).comp
        (mfderiv ((𝓡 3).prod (𝓡 4)) (𝓡 e.ambientDimension)
          (SevenSurgery.ambientSphereTube e f C) (s, 0)) := by
  have hr := r.smooth.contMDiffAt
    (r.domain.isOpen.mem_nhds (SevenSurgery.core_mem_sphereTubeDomain e f C r s))
  change mfderiv ((𝓡 3).prod (𝓡 4)) (𝓡 7) (r.toFun ∘ SevenSurgery.ambientSphereTube e f C) (s, 0) = _
  rw [mfderiv_comp (s, 0) (hr.mdifferentiableAt (by simp))
    ((SevenSurgery.contMDiff_ambientSphereTube e f C hf hC).mdifferentiableAt (by simp)),
    SevenSurgery.ambientSphereTube_core e]

variable (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s))
  (hiC : ∀ s, Injective (C s)) (hCr : ∀ s, (C s).range = SevenSurgery.sphereNormalSpace e f s)

include hf hC hd hiC hCr in
theorem injective_mfderiv_internalSphereTube_core (s : Sphere 3) :
    Injective (mfderiv ((𝓡 3).prod (𝓡 4)) (𝓡 7) (SevenSurgery.internalSphereTube e f C r) (s, 0)) := by
  rw [SevenSurgery.mfderiv_internalSphereTube_core e f C r hf hC s]
  intro v w hvw
  apply SevenSurgery.injective_mfderiv_ambientSphereTube_core e f C hf hC hd hiC hCr s
  apply r.injective_mfderiv_on_tangent (f s) _ _ hvw
  · rw [← SevenSurgery.range_mfderiv_ambientSphereTube_core e f C hf hC hd hiC hCr s]
    exact ⟨v, rfl⟩
  · rw [← SevenSurgery.range_mfderiv_ambientSphereTube_core e f C hf hC hd hiC hCr s]
    exact ⟨w, rfl⟩

include hf hC hd hiC hCr in
theorem isInvertible_mfderiv_internalSphereTube_core (s : Sphere 3) :
    (mfderiv ((𝓡 3).prod (𝓡 4)) (𝓡 7) (SevenSurgery.internalSphereTube e f C r) (s, 0)).IsInvertible := by
  let L : (Vector 3 × Vector 4) →L[ℝ] Vector 7 :=
    mfderiv ((𝓡 3).prod (𝓡 4)) (𝓡 7) (SevenSurgery.internalSphereTube e f C r) (s, 0)
  have hi : Injective L := SevenSurgery.injective_mfderiv_internalSphereTube_core e f C r hf hC hd hiC hCr s
  have hs : Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simp [Module.finrank_prod])).mp hi
  exact ⟨(LinearEquiv.ofBijective L.toLinearMap ⟨hi, hs⟩).toContinuousLinearEquiv, rfl⟩

include hf hC hd hiC hCr in
theorem mfderiv_embedded_internalSphereTube_core (s : Sphere 3) :
    mfderiv ((𝓡 3).prod (𝓡 4)) (𝓡 e.ambientDimension)
      (e.toFun ∘ SevenSurgery.internalSphereTube e f C r) (s, 0) =
    mfderiv ((𝓡 3).prod (𝓡 4)) (𝓡 e.ambientDimension)
      (SevenSurgery.ambientSphereTube e f C) (s, 0) := by
  have hs := (SevenSurgery.contMDiffOn_internalSphereTube e f C r hf hC).contMDiffAt
    ((SevenSurgery.isOpen_sphereTubeDomain e f C r hf hC).mem_nhds (SevenSurgery.core_mem_sphereTubeDomain e f C r s))
  rw [mfderiv_comp (s, 0) (e.smooth.mdifferentiableAt (by simp))
    (hs.mdifferentiableAt (by simp)), SevenSurgery.internalSphereTube_core e,
    SevenSurgery.mfderiv_internalSphereTube_core e f C r hf hC s]
  apply ContinuousLinearMap.ext
  intro v
  apply r.mfderiv_embedding_retract_tangent (f s)
  rw [← SevenSurgery.range_mfderiv_ambientSphereTube_core e f C hf hC hd hiC hCr s]
  exact ⟨v, rfl⟩

variable [IsManifold (𝓡 7) ∞ M]

include hf hC hd hiC hCr in
theorem isLocalDiffeomorphAt_internalSphereTube_core (s : Sphere 3) :
    IsLocalDiffeomorphAt ((𝓡 3).prod (𝓡 4)) (𝓡 7) ∞ (SevenSurgery.internalSphereTube e f C r) (s, 0) :=
  Wikipedia.SmoothSixDPoincare.isLocalDiffeomorphAt_boundaryless
    (SevenSurgery.isOpen_sphereTubeDomain e f C r hf hC) (SevenSurgery.core_mem_sphereTubeDomain e f C r s)
    (SevenSurgery.contMDiffOn_internalSphereTube e f C r hf hC)
    (SevenSurgery.isInvertible_mfderiv_internalSphereTube_core e f C r hf hC hd hiC hCr s)

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
