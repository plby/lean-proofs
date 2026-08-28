import Wikipedia.NoExoticSixSphere.SphereFourTubeMeridianDisk

/-!
# The actual meridian in the native regular zero atlas

The unit normal sphere gives an injective smooth immersion into the
actual zero set. Smoothness and derivative injectivity are proved for
the constructed regular-fiber atlas, not transported from a model
product boundary. Its inclusion into the half is the original meridian
map used in the integral half-image comparison.
-/

noncomputable section

open Function Set ContinuousMap
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SphereFourTube

open GLOrthonormalization EmbeddedTime

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M]
  (Φ : PartialDiffeomorph ((𝓡 3).prod (𝓡 4)) (𝓡 7) (Sphere 3 × Vector 4) M ∞)
  (hΦ : Φ.source = univ) (τ : C(M, ℝ))
  (hinner : ∀ p : Sphere 3 × Vector 4, ‖p.2‖ ≤ 3 / 2 → τ (Φ p) = ‖p.2‖ ^ 2 - 1)

def meridianMap (s : Sphere 3) : C(Sphere 3, {x : M // τ x = 0}) :=
  ⟨fun v ↦ ⟨normalDisk Φ s v.val, unitBoundary_time_zero Φ τ hinner (s, v)⟩,
    ((contMDiff_normalDisk Φ hΦ s).continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem meridianMap_injective (s : Sphere 3) : Injective (meridianMap Φ hΦ τ hinner s) := by
  intro v w h
  apply Subtype.ext
  apply normalDisk_injective Φ hΦ s
  exact congrArg (fun z : {x : M // τ x = 0} ↦ z.val) h

theorem meridianMap_to_half (s : Sphere 3) :
    (zeroToHalf τ).comp (meridianMap Φ hΦ τ hinner s) =
      (boundaryInNewHalf Φ hΦ τ hinner).comp (ProductThirdHomology.rightSection s) := rfl

variable (hτ : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ τ)
  (hreg : ∀ x, τ x = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) τ x))

theorem contMDiff_meridianMap (s : Sphere 3) : letI := zeroAtlas (n := 6) τ hτ hreg;
    ContMDiff (𝓡 3) (𝓡 6) ∞ (meridianMap Φ hΦ τ hinner s) := by
  let := zeroAtlas (n := 6) τ hτ hreg
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨by simp⟩
  exact (regularFiber_contMDiff_iff_ambient τ hτ 0 hreg 6
    (by simp) (meridianMap Φ hΦ τ hinner s)).mpr
      ((contMDiff_normalDisk Φ hΦ s).comp (contMDiff_coe_sphere (E := Vector 4) (n := 3)))

theorem meridianMap_mfderiv_injective (s v : Sphere 3) : letI := zeroAtlas (n := 6) τ hτ hreg;
    Injective (mfderiv (𝓡 3) (𝓡 6) (meridianMap Φ hΦ τ hinner s) v) := by
  let := zeroAtlas (n := 6) τ hτ hreg
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨by simp⟩
  let f := meridianMap Φ hΦ τ hinner s
  let g := normalDisk Φ s
  have hg : ContMDiff (𝓡 4) (𝓡 7) ∞ g := contMDiff_normalDisk Φ hΦ s
  have hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f := contMDiff_meridianMap Φ hΦ τ hinner hτ hreg s
  have hcoe : ContMDiff (𝓡 3) (𝓡 4) ∞ (Subtype.val : Sphere 3 → Vector 4) :=
    contMDiff_coe_sphere (E := Vector 4) (n := 3)
  have hi : Injective (mfderiv (𝓡 3) (𝓡 7) (g ∘ Subtype.val) v) := by
    rw [mfderiv_comp v (hg.mdifferentiableAt (by simp)) (hcoe.mdifferentiableAt (by simp))]
    exact (normalDisk_mfderiv_injective Φ hΦ s v.val).comp
      (mfderiv_coe_sphere_injective (n := 3) v)
  have hc : mfderiv (𝓡 3) (𝓡 7) (g ∘ Subtype.val) v =
      (inclusionDerivative τ hτ hreg (f v)).comp (mfderiv (𝓡 3) (𝓡 6) f v) :=
    mfderiv_comp v ((contMDiff_zeroInclusion τ hτ hreg).mdifferentiableAt (by simp))
      (hf.mdifferentiableAt (by simp))
  intro a b hab
  apply hi
  rw [hc]
  exact congrArg (inclusionDerivative τ hτ hreg (f v)) hab

end NoExoticSixSphere.SphereFourTube
