import Wikipedia.NoExoticSixSphere.SphereTubeCoreImmersion
import Wikipedia.NoExoticSixSphere.TubularRetractionDifferential
import Wikipedia.SmoothSixDPoincare.BoundarylessLocalInverse

/-!
# The sphere tube in the original manifold and its actual local inverses

Apply the actual tubular retraction to the ambient tube on its genuine open
domain. Its native derivative at the zero section is invertible: the ambient
derivative parametrizes the original tangent image and the retraction is
inverse there. Local diffeomorphisms retain both original manifold models.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization

variable {n q : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (f : Sphere 3 → M)
  (C : Sphere 3 → Vector q →L[ℝ] Vector e.ambientDimension) (r : TubularRetraction e)

def sphereTubeDomain : Set (Sphere 3 × Vector q) := (e.ambientSphereTube f C) ⁻¹' r.domain

def internalSphereTube : Sphere 3 × Vector q → M := r.toFun ∘ e.ambientSphereTube f C

theorem internalSphereTube_core (s : Sphere 3) : e.internalSphereTube f C r (s, 0) = f s := by
  change r.toFun (e.ambientSphereTube f C (s, 0)) = f s
  rw [e.ambientSphereTube_core]
  exact r.fixes (f s)

theorem core_mem_sphereTubeDomain (s : Sphere 3) : (s, 0) ∈ e.sphereTubeDomain f C r := by
  change e.ambientSphereTube f C (s, 0) ∈ r.domain
  rw [e.ambientSphereTube_core]
  exact r.contains ⟨f s, rfl⟩

variable (hf : ContMDiff (𝓡 3) (𝓡 n) ∞ f)
  (hC : ContMDiff (𝓡 3) 𝓘(ℝ, Vector q →L[ℝ] Vector e.ambientDimension) ∞ C)

include hf hC in
theorem isOpen_sphereTubeDomain : IsOpen (e.sphereTubeDomain f C r) :=
  r.domain.isOpen.preimage (e.contMDiff_ambientSphereTube f C hf hC).continuous

include hf hC in
theorem contMDiffOn_internalSphereTube :
    ContMDiffOn ((𝓡 3).prod (𝓡 q)) (𝓡 n) ∞ (e.internalSphereTube f C r)
      (e.sphereTubeDomain f C r) :=
  r.smooth.comp (e.contMDiff_ambientSphereTube f C hf hC).contMDiffOn (fun _ hp ↦ hp)

include hf hC in
theorem mfderiv_internalSphereTube_core (s : Sphere 3) :
    mfderiv ((𝓡 3).prod (𝓡 q)) (𝓡 n) (e.internalSphereTube f C r) (s, 0) =
      (mfderiv (𝓡 e.ambientDimension) (𝓡 n) r.toFun (e.toFun (f s))).comp
        (mfderiv ((𝓡 3).prod (𝓡 q)) (𝓡 e.ambientDimension)
          (e.ambientSphereTube f C) (s, 0)) := by
  have hr := r.smooth.contMDiffAt
    (r.domain.isOpen.mem_nhds (e.core_mem_sphereTubeDomain f C r s))
  change mfderiv ((𝓡 3).prod (𝓡 q)) (𝓡 n) (r.toFun ∘ e.ambientSphereTube f C) (s, 0) = _
  rw [mfderiv_comp (s, 0) (hr.mdifferentiableAt (by simp))
    ((e.contMDiff_ambientSphereTube f C hf hC).mdifferentiableAt (by simp)),
    e.ambientSphereTube_core]

variable (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 n) f s))
  (hiC : ∀ s, Injective (C s)) (hCr : ∀ s, (C s).range = e.sphereNormalSpace f s)

include hf hC hd hiC hCr in
theorem injective_mfderiv_internalSphereTube_core (s : Sphere 3) :
    Injective (mfderiv ((𝓡 3).prod (𝓡 q)) (𝓡 n) (e.internalSphereTube f C r) (s, 0)) := by
  rw [e.mfderiv_internalSphereTube_core f C r hf hC s]
  intro v w hvw
  apply e.injective_mfderiv_ambientSphereTube_core f C hf hC hd hiC hCr s
  apply r.injective_mfderiv_on_tangent (f s) _ _ hvw
  · rw [← e.range_mfderiv_ambientSphereTube_core f C hf hC hd hiC hCr s]
    exact ⟨v, rfl⟩
  · rw [← e.range_mfderiv_ambientSphereTube_core f C hf hC hd hiC hCr s]
    exact ⟨w, rfl⟩

include hf hC hd hiC hCr in
theorem isInvertible_mfderiv_internalSphereTube_core (s : Sphere 3) :
    (mfderiv ((𝓡 3).prod (𝓡 q)) (𝓡 n) (e.internalSphereTube f C r) (s, 0)).IsInvertible := by
  let L : (Vector 3 × Vector q) →L[ℝ] Vector n :=
    mfderiv ((𝓡 3).prod (𝓡 q)) (𝓡 n) (e.internalSphereTube f C r) (s, 0)
  have hi : Injective L := e.injective_mfderiv_internalSphereTube_core f C r hf hC hd hiC hCr s
  have hs : Surjective L := by
    intro w
    let v : Vector e.ambientDimension :=
      mfderiv (𝓡 n) (𝓡 e.ambientDimension) e.toFun (f s) w
    have hv : v ∈ e.tangentImage (f s) := ⟨w, rfl⟩
    rw [← e.range_mfderiv_ambientSphereTube_core f C hf hC hd hiC hCr s] at hv
    obtain ⟨z, hz⟩ := hv
    refine ⟨z, ?_⟩
    change mfderiv ((𝓡 3).prod (𝓡 q)) (𝓡 n)
      (e.internalSphereTube f C r) (s, 0) z = w
    rw [e.mfderiv_internalSphereTube_core f C r hf hC s]
    change mfderiv (𝓡 e.ambientDimension) (𝓡 n) r.toFun (e.toFun (f s))
      (mfderiv ((𝓡 3).prod (𝓡 q)) (𝓡 e.ambientDimension)
        (e.ambientSphereTube f C) (s, 0) z) = w
    exact (congrArg (fun y : Vector e.ambientDimension ↦
      mfderiv (𝓡 e.ambientDimension) (𝓡 n) r.toFun (e.toFun (f s)) y) hz).trans
      (congrArg (fun A : Vector n →L[ℝ] Vector n ↦ A w)
        (r.mfderiv_comp_embedding (f s)))
  exact ⟨(LinearEquiv.ofBijective L.toLinearMap ⟨hi, hs⟩).toContinuousLinearEquiv, rfl⟩

include hf hC hd hiC hCr in
theorem mfderiv_embedded_internalSphereTube_core (s : Sphere 3) :
    mfderiv ((𝓡 3).prod (𝓡 q)) (𝓡 e.ambientDimension)
      (e.toFun ∘ e.internalSphereTube f C r) (s, 0) =
    mfderiv ((𝓡 3).prod (𝓡 q)) (𝓡 e.ambientDimension)
      (e.ambientSphereTube f C) (s, 0) := by
  have hs := (e.contMDiffOn_internalSphereTube f C r hf hC).contMDiffAt
    ((e.isOpen_sphereTubeDomain f C r hf hC).mem_nhds (e.core_mem_sphereTubeDomain f C r s))
  rw [mfderiv_comp (s, 0) (e.smooth.mdifferentiableAt (by simp))
    (hs.mdifferentiableAt (by simp)), e.internalSphereTube_core,
    e.mfderiv_internalSphereTube_core f C r hf hC s]
  apply ContinuousLinearMap.ext
  intro v
  apply r.mfderiv_embedding_retract_tangent (f s)
  rw [← e.range_mfderiv_ambientSphereTube_core f C hf hC hd hiC hCr s]
  exact ⟨v, rfl⟩

variable [IsManifold (𝓡 n) ∞ M]

include hf hC hd hiC hCr in
theorem isLocalDiffeomorphAt_internalSphereTube_core (s : Sphere 3) :
    IsLocalDiffeomorphAt ((𝓡 3).prod (𝓡 q)) (𝓡 n) ∞ (e.internalSphereTube f C r) (s, 0) :=
  Wikipedia.SmoothSixDPoincare.isLocalDiffeomorphAt_boundaryless
    (e.isOpen_sphereTubeDomain f C r hf hC) (e.core_mem_sphereTubeDomain f C r s)
    (e.contMDiffOn_internalSphereTube f C r hf hC)
    (e.isInvertible_mfderiv_internalSphereTube_core f C r hf hC hd hiC hCr s)

end NoExoticSixSphere.EuclideanEmbedding
