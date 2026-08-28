import Wikipedia.NoExoticSixSphere.SphereFourTubeTimeLevels

/-!
# The tube exterior has an actual smooth regular defining time

On the new unit tube boundary, the radial derivative is exactly two.
Near the old zero set, the modified and original times have the same
manifold derivative. These two calculations prove regularity at every
new zero, while the checked level identities identify the actual exterior.
-/

noncomputable section

open Function Set Metric Filter
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SphereFourTube

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [IsManifold (𝓡 7) ∞ M]
  (Φ : PartialDiffeomorph ((𝓡 3).prod (𝓡 4)) (𝓡 7) (Sphere 3 × Vector 4) M ∞)

theorem regular_modified_time_at_unit_tube (hΦ : Φ.source = univ)
    (τ : C(M, ℝ)) (hτ : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ τ)
    (hinner : ∀ p : Sphere 3 × Vector 4, ‖p.2‖ ≤ 3 / 2 → τ (Φ p) = ‖p.2‖ ^ 2 - 1)
    (p : Sphere 3 × Vector 4) (hp : ‖p.2‖ = 1) :
    Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) τ (Φ p)) := by
  let g : Vector 4 → M := fun v ↦ Φ (p.1, v)
  have hg : ContMDiff (𝓡 4) (𝓡 7) ∞ g :=
    (contMDiff Φ hΦ).comp (contMDiff_const.prodMk contMDiff_id)
  have he : (τ ∘ g) =ᶠ[𝓝 p.2] (fun v : Vector 4 ↦ ‖v‖ ^ 2 - 1) := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds
      (show ‖p.2‖ < (3 / 2 : ℝ) by rw [hp]; norm_num)] with v hv
    exact hinner (p.1, v) hv.le
  have hsq : HasFDerivAt (fun v : Vector 4 ↦ ‖v‖ ^ 2 - 1)
      (2 • innerSL ℝ p.2) p.2 :=
    (hasStrictFDerivAt_norm_sq p.2).hasFDerivAt.sub_const 1
  have hrad : fderiv ℝ (τ ∘ g) p.2 p.2 = 2 := by
    rw [he.fderiv_eq, hsq.fderiv]
    norm_num [ContinuousLinearMap.smul_apply, innerSL_apply_apply,
      real_inner_self_eq_norm_sq, hp]
  have hcomp := mfderiv_comp p.2 (hτ.mdifferentiableAt (by simp))
    (hg.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hcomp
  let v : Vector 7 := mfderiv (𝓡 4) (𝓡 7) g p.2 p.2
  let L : Vector 7 →L[ℝ] ℝ := mfderiv (𝓡 7) 𝓘(ℝ, ℝ) τ (Φ p)
  have hv : L v = 2 := by
    rw [hcomp] at hrad
    exact hrad
  change Surjective L
  intro z
  refine ⟨(z / 2 : ℝ) • v, ?_⟩
  rw [map_smul, hv]
  change (z / 2) * 2 = z
  ring

theorem regular_modified_time_zero [T2Space M] (hΦ : Φ.source = univ)
    (t τ : C(M, ℝ)) (hτ : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ τ)
    (hreg : ∀ x, t x = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) t x))
    (hpos : ∀ x ∈ Φ.target, 0 < t x)
    (hout : ∀ x ∉ closedRegion Φ 2, τ x = t x)
    (hinner : ∀ p : Sphere 3 × Vector 4, ‖p.2‖ ≤ 3 / 2 → τ (Φ p) = ‖p.2‖ ^ 2 - 1)
    (houter : ∀ p : Sphere 3 × Vector 4, 1 < ‖p.2‖ → 0 < τ (Φ p)) :
    ∀ x, τ x = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) τ x) := by
  intro x hx
  rcases (modified_time_zero_iff Φ τ hinner houter hΦ t hpos hout x).mp hx with
    hxold | ⟨p, hp, rfl⟩
  · have he : (τ : M → ℝ) =ᶠ[𝓝 x] t :=
      modified_time_eventuallyEq_old_zero Φ τ hΦ t hpos hout hxold
    rw [he.mfderiv_eq]
    exact hreg x hxold
  · exact regular_modified_time_at_unit_tube Φ hΦ τ hτ hinner p hp

theorem exists_regular_time_modification [CompactSpace M] [T2Space M]
    (hΦ : Φ.source = univ) (t : C(M, ℝ))
    (ht : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ t)
    (hreg : ∀ x, t x = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) t x))
    (hpos : ∀ x ∈ Φ.target, 0 < t x) :
    ∃ τ : C(M, ℝ), ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ τ ∧
      (∀ x, τ x = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) τ x)) ∧
      (∀ x ∉ closedRegion Φ 2, τ x = t x) ∧
      (∀ p : Sphere 3 × Vector 4, ‖p.2‖ ≤ 3 / 2 → τ (Φ p) = ‖p.2‖ ^ 2 - 1) ∧
      (∀ p : Sphere 3 × Vector 4, 1 < ‖p.2‖ → 0 < τ (Φ p)) ∧
      (∀ x, τ x = 0 ↔ t x = 0 ∨ ∃ p : Sphere 3 × Vector 4, ‖p.2‖ = 1 ∧ Φ p = x) ∧
      ∀ x, 0 ≤ τ x ↔ 0 ≤ t x ∧ x ∉ openRegion Φ 1 := by
  obtain ⟨τ, hτ, hout, hinner, houter⟩ := exists_time_modification Φ hΦ t ht hpos
  exact ⟨τ, hτ, regular_modified_time_zero Φ hΦ t τ hτ hreg hpos hout hinner houter,
    hout, hinner, houter,
    modified_time_zero_iff Φ τ hinner houter hΦ t hpos hout,
    modified_time_nonneg_iff Φ τ hinner houter hΦ t hpos hout⟩

end NoExoticSixSphere.SphereFourTube
