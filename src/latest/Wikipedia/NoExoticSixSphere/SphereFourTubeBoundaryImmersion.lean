import Wikipedia.NoExoticSixSphere.SphereFourTubeBoundaryQuadraticValue
import Wikipedia.NoExoticSixSphere.QuaternionicHopfProductAtlas

/-!
# The actual tube boundary is a native smooth injective immersion

The unit normal inclusion is an immersion, and the original tube has a
smooth local inverse. Their composite lands in the actual regular zero
fiber. The regular-fiber atlas and the proved Euclidean model change on
the product give a six-dimensional native smooth injective immersion.
-/

noncomputable section

open Function Set ContinuousMap
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SphereFourTube

open GLOrthonormalization EmbeddedTime QuaternionicHopf

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M]
  (Φ : PartialDiffeomorph ((𝓡 3).prod (𝓡 4)) (𝓡 7) (Sphere 3 × Vector 4) M ∞)
  (hΦ : Φ.source = univ) (τ : C(M, ℝ))
  (hinner : ∀ p : Sphere 3 × Vector 4, ‖p.2‖ ≤ 3 / 2 → τ (Φ p) = ‖p.2‖ ^ 2 - 1)

theorem boundaryMap_injective : Injective (boundaryMap Φ hΦ τ hinner) := by
  intro p q hpq
  have h := (Φ.toOpenPartialHomeomorph.isOpenEmbedding hΦ).injective
    (congrArg (fun z : {x : M // τ x = 0} ↦ z.val) hpq)
  exact Prod.ext (congrArg (Prod.fst : Sphere 3 × Vector 4 → Sphere 3) h)
    (Subtype.ext (congrArg Prod.snd h))

variable (hτ : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ τ)
  (hreg : ∀ x, τ x = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) τ x))

theorem contMDiff_boundaryMap_product : letI := zeroAtlas (n := 6) τ hτ hreg;
    ContMDiff ((𝓡 3).prod (𝓡 3)) (𝓡 6) ∞ (boundaryMap Φ hΦ τ hinner) := by
  let := zeroAtlas (n := 6) τ hτ hreg
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨by simp⟩
  apply (regularFiber_contMDiff_iff_ambient τ hτ 0 hreg 6
    (by simp) (boundaryMap Φ hΦ τ hinner)).mpr
  exact (contMDiff Φ hΦ).comp (contMDiff_fst.prodMk
    ((contMDiff_coe_sphere (E := Vector 4) (n := 3)).comp contMDiff_snd))

theorem boundaryMap_product_mfderiv_injective (p : Sphere 3 × Sphere 3) :
    letI := zeroAtlas (n := 6) τ hτ hreg;
    Injective (mfderiv ((𝓡 3).prod (𝓡 3)) (𝓡 6) (boundaryMap Φ hΦ τ hinner) p) := by
  let := zeroAtlas (n := 6) τ hτ hreg
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨by simp⟩
  let j : Sphere 3 × Sphere 3 → Sphere 3 × Vector 4 := Prod.map id Subtype.val
  have hcoe : ContMDiff (𝓡 3) (𝓡 4) ∞ (Subtype.val : Sphere 3 → Vector 4) :=
    contMDiff_coe_sphere (E := Vector 4) (n := 3)
  have hj : ContMDiff ((𝓡 3).prod (𝓡 3)) ((𝓡 3).prod (𝓡 4)) ∞ j :=
    contMDiff_fst.prodMk (hcoe.comp contMDiff_snd)
  have hji : Injective (mfderiv ((𝓡 3).prod (𝓡 3)) ((𝓡 3).prod (𝓡 4)) j p) := by
    change Injective (mfderiv ((𝓡 3).prod (𝓡 3)) ((𝓡 3).prod (𝓡 4))
      (Prod.map id (Subtype.val : Sphere 3 → Vector 4)) p)
    rw [mfderiv_prodMap mdifferentiableAt_id (hcoe.mdifferentiableAt (by simp)), mfderiv_id]
    intro a b hab
    exact Prod.ext (congrArg (Prod.fst : Vector 3 × Vector 4 → Vector 3) hab)
      ((mfderiv_coe_sphere_injective (n := 3) p.2) (congrArg Prod.snd hab))
  have hloc : IsLocalDiffeomorphAt ((𝓡 3).prod (𝓡 4)) (𝓡 7) ∞ Φ (j p) :=
    ⟨Φ, hΦ.symm ▸ mem_univ _, fun _ _ ↦ rfl⟩
  have hi : Injective (mfderiv ((𝓡 3).prod (𝓡 3)) (𝓡 7) (Φ ∘ j) p) := by
    rw [mfderiv_comp p ((contMDiff Φ hΦ).mdifferentiableAt (by simp))
      (hj.mdifferentiableAt (by simp))]
    exact (hloc.mfderivToContinuousLinearEquiv (by simp)).injective.comp hji
  have hf := contMDiff_boundaryMap_product Φ hΦ τ hinner hτ hreg
  have hc : mfderiv ((𝓡 3).prod (𝓡 3)) (𝓡 7) (Φ ∘ j) p =
      (inclusionDerivative τ hτ hreg (boundaryMap Φ hΦ τ hinner p)).comp
        (mfderiv ((𝓡 3).prod (𝓡 3)) (𝓡 6) (boundaryMap Φ hΦ τ hinner) p) :=
    mfderiv_comp p ((contMDiff_zeroInclusion τ hτ hreg).mdifferentiableAt (by simp))
      (hf.mdifferentiableAt (by simp))
  intro a b hab
  apply hi
  rw [hc]
  exact congrArg (inclusionDerivative τ hτ hreg (boundaryMap Φ hΦ τ hinner p)) hab

theorem contMDiff_boundaryMap_euclidean :
    letI := southPairEuclideanAtlas;
    letI := zeroAtlas (n := 6) τ hτ hreg;
    ContMDiff (𝓡 6) (𝓡 6) ∞ (boundaryMap Φ hΦ τ hinner) := by
  let := southPairEuclideanAtlas
  let := zeroAtlas (n := 6) τ hτ hreg
  exact (contMDiff_boundaryMap_product Φ hΦ τ hinner hτ hreg).comp
    southPairEuclideanToProduct.contMDiff

theorem boundaryMap_euclidean_mfderiv_injective (p : Sphere 3 × Sphere 3) :
    letI := southPairEuclideanAtlas;
    letI := zeroAtlas (n := 6) τ hτ hreg;
    Injective (mfderiv (𝓡 6) (𝓡 6) (boundaryMap Φ hΦ τ hinner) p) := by
  let := southPairEuclideanAtlas
  let := southPairEuclideanIsManifold
  let := zeroAtlas (n := 6) τ hτ hreg
  change Injective (mfderiv (𝓡 6) (𝓡 6)
    ((boundaryMap Φ hΦ τ hinner) ∘ southPairEuclideanToProduct) p)
  rw [mfderiv_comp p
    ((contMDiff_boundaryMap_product Φ hΦ τ hinner hτ hreg).mdifferentiableAt (by simp))
    (southPairEuclideanToProduct.contMDiff.mdifferentiableAt (by simp))]
  exact (boundaryMap_product_mfderiv_injective Φ hΦ τ hinner hτ hreg p).comp
    (southPairEuclideanToProduct.mfderivToContinuousLinearEquiv (by simp) p).injective

end NoExoticSixSphere.SphereFourTube
