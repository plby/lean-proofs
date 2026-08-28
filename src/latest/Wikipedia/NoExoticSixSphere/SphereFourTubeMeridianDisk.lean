import Wikipedia.NoExoticSixSphere.SphereFourTubeOldBoundaryRelation

/-!
# The actual immersive normal four-disk and its boundary time sign

The disk is the fixed-core-point slice of the original partial
diffeomorphism, on its entire normal four-space. The local inverse gives
injectivity of its native differential. At a unit normal vector, the
modified-time radial derivative is exactly two.
-/

noncomputable section

open Function Set Filter
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SphereFourTube

open GLOrthonormalization

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [IsManifold (𝓡 7) ∞ M]
  (Φ : PartialDiffeomorph ((𝓡 3).prod (𝓡 4)) (𝓡 7) (Sphere 3 × Vector 4) M ∞)

def normalDisk (s : Sphere 3) : Vector 4 → M := fun v ↦ Φ (s, v)

theorem contMDiff_normalDisk (hΦ : Φ.source = univ) (s : Sphere 3) :
    ContMDiff (𝓡 4) (𝓡 7) ∞ (normalDisk Φ s) :=
  (contMDiff Φ hΦ).comp (contMDiff_const.prodMk contMDiff_id)

theorem normalDisk_injective (hΦ : Φ.source = univ) (s : Sphere 3) :
    Injective (normalDisk Φ s) := by
  intro v w h
  exact congrArg Prod.snd ((Φ.toOpenPartialHomeomorph.isOpenEmbedding hΦ).injective h)

theorem normalDisk_mfderiv_injective (hΦ : Φ.source = univ) (s : Sphere 3) (v : Vector 4) :
    Injective (mfderiv (𝓡 4) (𝓡 7) (normalDisk Φ s) v) := by
  have hloc : IsLocalDiffeomorphAt ((𝓡 3).prod (𝓡 4)) (𝓡 7) ∞ Φ (s, v) :=
    ⟨Φ, hΦ.symm ▸ mem_univ _, fun _ _ ↦ rfl⟩
  have hsection : ContMDiff (𝓡 4) ((𝓡 3).prod (𝓡 4)) ∞
      (fun w : Vector 4 ↦ (s, w)) := contMDiff_const.prodMk contMDiff_id
  change Injective (mfderiv (𝓡 4) (𝓡 7) (Φ ∘ fun w : Vector 4 ↦ (s, w)) v)
  rw [mfderiv_comp v ((contMDiff Φ hΦ).mdifferentiableAt (by simp))
    (hsection.mdifferentiableAt (by simp))]
  apply (hloc.mfderivToContinuousLinearEquiv (by simp)).injective.comp
  rw [mfderiv_prod_right]
  intro a b hab
  exact congrArg Prod.snd hab

theorem normalDisk_radial_time_derivative (τ : C(M, ℝ))
    (hinner : ∀ p : Sphere 3 × Vector 4, ‖p.2‖ ≤ 3 / 2 → τ (Φ p) = ‖p.2‖ ^ 2 - 1)
    (s v : Sphere 3) : fderiv ℝ (τ ∘ normalDisk Φ s) v.val v.val = 2 := by
  have hn : ‖v.val‖ = 1 := ClosedHemisphere.unit_norm v
  have he : (τ ∘ normalDisk Φ s) =ᶠ[𝓝 v.val] (fun w : Vector 4 ↦ ‖w‖ ^ 2 - 1) := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds
      (show ‖v.val‖ < (3 / 2 : ℝ) by rw [hn]; norm_num)] with w hw
    exact hinner (s, w) hw.le
  have hs : HasFDerivAt (fun w : Vector 4 ↦ ‖w‖ ^ 2 - 1)
      (2 • innerSL ℝ v.val) v.val :=
    (hasStrictFDerivAt_norm_sq v.val).hasFDerivAt.sub_const 1
  rw [he.fderiv_eq, hs.fderiv]
  norm_num [ContinuousLinearMap.smul_apply, innerSL_apply_apply,
    real_inner_self_eq_norm_sq, hn]

end NoExoticSixSphere.SphereFourTube
