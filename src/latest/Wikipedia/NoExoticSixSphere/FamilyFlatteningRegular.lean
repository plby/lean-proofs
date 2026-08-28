import Wikipedia.NoExoticSixSphere.FamilyFlatteningVertical

/-!
# Nondegeneracy survives the actual flattening

The inverse source-coordinate map has bijective derivative. The identity
between the flattened vertical derivative and the original Schur residual
holds on an open neighborhood, so differentiating it preserves regularity.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Topology Manifold

namespace NoExoticSixSphere.FamilyFlattening

open CorankOne

variable {T E F : Type}
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : T → E × ℝ → E × F}

theorem Data.bijective_fderiv_inverse (d : Data f) {r : (T × E) × ℝ}
    (hr : r ∈ d.target) : Bijective (fderiv ℝ d.inverse r) := by
  have hc : IsLocalDiffeomorphAt 𝓘(ℝ, E × (T × ℝ)) 𝓘(ℝ, E × (T × ℝ)) ∞
      d.coord.symm (flatOrder r) :=
    ⟨d.coord.symm, hr, fun _ _ ↦ rfl⟩
  have hb := (hc.mfderivToContinuousLinearEquiv (by simp)).bijective
  change Bijective (mfderiv 𝓘(ℝ, E × (T × ℝ)) 𝓘(ℝ, E × (T × ℝ))
    d.coord.symm (flatOrder r)) at hb
  rw [mfderiv_eq_fderiv] at hb
  have hs₀ := d.coord.contMDiffOn_invFun.contDiffOn.contDiffAt
    (d.coord.open_target.mem_nhds hr)
  have hs : DifferentiableAt ℝ d.coord.symm (flatOrder r) :=
    hs₀.differentiableAt (by simp)
  have hder := hs.hasFDerivAt.comp r (flatOrder (T := T) (E := E)).hasFDerivAt
  change Bijective (fderiv ℝ (d.coord.symm ∘ flatOrder) r)
  rw [hder.fderiv]
  exact hb.comp (flatOrder (T := T) (E := E)).bijective

theorem Data.bijective_fderiv_vertical (hf : ContDiff ℝ ∞ (uncurry f)) (d : Data f)
    {r : (T × E) × ℝ} (hr : r ∈ d.target)
    (hb : Bijective (fderiv ℝ (fun q ↦ residual (spatial f q)) (d.inverse r))) :
    Bijective (fderiv ℝ (SymmetricDifference.vertical d.flattened) r) := by
  have he : SymmetricDifference.vertical d.flattened =ᶠ[𝓝 r]
      (fun q ↦ residual (spatial f (d.inverse q))) := by
    filter_upwards [d.target.isOpen.mem_nhds hr] with q hq
    exact d.vertical_flattened_eq hf hq
  rw [he.fderiv_eq]
  have hR₀ := (contDiffAt_residual _
    (leading_invertible (d.source_chart _ (d.inverse_mem_source hr)))).comp
      (d.inverse r) (contDiff_spatial f hf).contDiffAt
  have hR : DifferentiableAt ℝ (fun q ↦ residual (spatial f q)) (d.inverse r) :=
    hR₀.differentiableAt (by simp)
  have hγ₀ := d.contDiffOn_inverse.contDiffAt (d.target.isOpen.mem_nhds hr)
  have hγ : DifferentiableAt ℝ d.inverse r := hγ₀.differentiableAt (by simp)
  change Bijective (fderiv ℝ ((fun q ↦ residual (spatial f q)) ∘ d.inverse) r)
  rw [(hR.hasFDerivAt.comp r hγ.hasFDerivAt).fderiv]
  exact hb.comp (d.bijective_fderiv_inverse hr)

end NoExoticSixSphere.FamilyFlattening
