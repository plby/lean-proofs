import Wikipedia.HopfProblem.DegreeCollapseLowAmbientSphereTube
import Wikipedia.NoExoticSixSphere.TubularRetractionDifferential
import Wikipedia.SmoothSixDPoincare.BoundarylessLocalInverse

/-!

# Native low-dimensional sphere tubes and their actual core derivatives

Retract the ambient tube to the original seven-manifold. The actual derivative
is invertible in the native atlas, and composing with the original embedding
retains the entire ambient core derivative. The supplied retraction is used
only on its actual open domain.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

open NoExoticSixSphere GLOrthonormalization

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M) (f : NoExoticSixSphere.Sphere d → M)
  (C : NoExoticSixSphere.Sphere d → Vector (7 - d) →L[ℝ] Vector e.ambientDimension)
  (r : EuclideanEmbedding.TubularRetraction e)

def sphereTubeDomain : Set (NoExoticSixSphere.Sphere d × Vector (7 - d)) :=
  (ambientSphereTube e f C) ⁻¹' r.domain

def internalSphereTube : NoExoticSixSphere.Sphere d × Vector (7 - d) → M :=
  r.toFun ∘ ambientSphereTube e f C

theorem internalSphereTube_core (s : NoExoticSixSphere.Sphere d) :
    internalSphereTube e f C r (s, 0) = f s := by
  change r.toFun (ambientSphereTube e f C (s, 0)) = f s
  rw [ambientSphereTube_core e]
  exact r.fixes (f s)

theorem core_mem_sphereTubeDomain (s : NoExoticSixSphere.Sphere d) :
    (s, 0) ∈ sphereTubeDomain e f C r := by
  change ambientSphereTube e f C (s, 0) ∈ r.domain
  rw [ambientSphereTube_core e]
  exact r.contains ⟨f s, rfl⟩

variable (hf : ContMDiff (𝓡 d) (𝓡 7) ∞ f)
  (hC : ContMDiff (𝓡 d) 𝓘(ℝ, Vector (7 - d) →L[ℝ] Vector e.ambientDimension) ∞ C)

include hf hC in
theorem isOpen_sphereTubeDomain : IsOpen (sphereTubeDomain e f C r) :=
  r.domain.isOpen.preimage (contMDiff_ambientSphereTube e f C hf hC).continuous

include hf hC in
theorem contMDiffOn_internalSphereTube :
    ContMDiffOn ((𝓡 d).prod (𝓡 (7 - d))) (𝓡 7) ∞ (internalSphereTube e f C r)
      (sphereTubeDomain e f C r) :=
  r.smooth.comp (contMDiff_ambientSphereTube e f C hf hC).contMDiffOn (fun _ hp ↦ hp)

include hf hC in
theorem mfderiv_internalSphereTube_core (s : NoExoticSixSphere.Sphere d) :
    mfderiv ((𝓡 d).prod (𝓡 (7 - d))) (𝓡 7) (internalSphereTube e f C r) (s, 0) =
      (mfderiv (𝓡 e.ambientDimension) (𝓡 7) r.toFun (e.toFun (f s))).comp
        (mfderiv ((𝓡 d).prod (𝓡 (7 - d))) (𝓡 e.ambientDimension)
          (ambientSphereTube e f C) (s, 0)) := by
  have hr := r.smooth.contMDiffAt
    (r.domain.isOpen.mem_nhds (core_mem_sphereTubeDomain e f C r s))
  change mfderiv ((𝓡 d).prod (𝓡 (7 - d))) (𝓡 7) (r.toFun ∘ ambientSphereTube e f C) (s, 0) = _
  rw [mfderiv_comp (s, 0) (hr.mdifferentiableAt (by simp))
    ((contMDiff_ambientSphereTube e f C hf hC).mdifferentiableAt (by simp)),
    ambientSphereTube_core e]

variable (hd : ∀ s, Injective (mfderiv (𝓡 d) (𝓡 7) f s))
  (hiC : ∀ s, Injective (C s)) (hCr : ∀ s, (C s).range = sphereNormalSpace e f s)

include hf hC hd hiC hCr in
theorem injective_mfderiv_internalSphereTube_core (s : NoExoticSixSphere.Sphere d) :
    Injective (mfderiv ((𝓡 d).prod (𝓡 (7 - d))) (𝓡 7) (internalSphereTube e f C r) (s, 0)) := by
  rw [mfderiv_internalSphereTube_core e f C r hf hC s]
  intro v w hvw
  apply injective_mfderiv_ambientSphereTube_core e f C hf hC hd hiC hCr s
  apply r.injective_mfderiv_on_tangent (f s) _ _ hvw
  · rw [← range_mfderiv_ambientSphereTube_core e f C hf hC hd hiC hCr s]
    exact ⟨v, rfl⟩
  · rw [← range_mfderiv_ambientSphereTube_core e f C hf hC hd hiC hCr s]
    exact ⟨w, rfl⟩

include hf hC hd hiC hCr in
theorem isInvertible_mfderiv_internalSphereTube_core (s : NoExoticSixSphere.Sphere d) :
    (mfderiv ((𝓡 d).prod (𝓡 (7 - d))) (𝓡 7) (internalSphereTube e f C r) (s, 0)).IsInvertible := by
  let L : (Vector d × Vector (7 - d)) →L[ℝ] Vector 7 :=
    mfderiv ((𝓡 d).prod (𝓡 (7 - d))) (𝓡 7) (internalSphereTube e f C r) (s, 0)
  have hi : Injective L := injective_mfderiv_internalSphereTube_core e f C r hf hC hd hiC hCr s
  have hs : Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by
        simp only [Module.finrank_prod, finrank_euclideanSpace_fin]
        exact Nat.add_sub_of_le (sphere_dimension_le_seven f hd s))).mp hi
  exact ⟨(LinearEquiv.ofBijective L.toLinearMap ⟨hi, hs⟩).toContinuousLinearEquiv, rfl⟩

include hf hC hd hiC hCr in
theorem mfderiv_embedded_internalSphereTube_core (s : NoExoticSixSphere.Sphere d) :
    mfderiv ((𝓡 d).prod (𝓡 (7 - d))) (𝓡 e.ambientDimension)
      (e.toFun ∘ internalSphereTube e f C r) (s, 0) =
    mfderiv ((𝓡 d).prod (𝓡 (7 - d))) (𝓡 e.ambientDimension)
      (ambientSphereTube e f C) (s, 0) := by
  have hs := (contMDiffOn_internalSphereTube e f C r hf hC).contMDiffAt
    ((isOpen_sphereTubeDomain e f C r hf hC).mem_nhds (core_mem_sphereTubeDomain e f C r s))
  rw [mfderiv_comp (s, 0) (e.smooth.mdifferentiableAt (by simp))
    (hs.mdifferentiableAt (by simp)), internalSphereTube_core e,
    mfderiv_internalSphereTube_core e f C r hf hC s]
  apply ContinuousLinearMap.ext
  intro v
  apply r.mfderiv_embedding_retract_tangent (f s)
  rw [← range_mfderiv_ambientSphereTube_core e f C hf hC hd hiC hCr s]
  exact ⟨v, rfl⟩

variable [IsManifold (𝓡 7) ∞ M]

include hf hC hd hiC hCr in
theorem isLocalDiffeomorphAt_internalSphereTube_core (s : NoExoticSixSphere.Sphere d) :
    IsLocalDiffeomorphAt ((𝓡 d).prod (𝓡 (7 - d))) (𝓡 7) ∞ (internalSphereTube e f C r) (s, 0) :=
  Wikipedia.SmoothSixDPoincare.isLocalDiffeomorphAt_boundaryless
    (isOpen_sphereTubeDomain e f C r hf hC) (core_mem_sphereTubeDomain e f C r s)
    (contMDiffOn_internalSphereTube e f C r hf hC)
    (isInvertible_mfderiv_internalSphereTube_core e f C r hf hC hd hiC hCr s)

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery
