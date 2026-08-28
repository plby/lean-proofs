import Wikipedia.NoExoticSixSphere.CorankOneScaling
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Recovering residual regularity from a scaled pullback

At a residual zero, differentiating a varying scalar factor contributes no
extra term. Thus regularity of the actual scaled pullback implies regularity
of the original residual. The source map need not be a diffeomorphism.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff

namespace NoExoticSixSphere.CorankOne

variable {X Y E F : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem surjective_residual_of_scaled_pullback
    (D : X → BlockMap E F) (φ : Y → X) (a : Y → ℝ) (p : Y)
    (hD : ContDiffAt ℝ ∞ D (φ p)) (hφ : DifferentiableAt ℝ φ p)
    (ha : DifferentiableAt ℝ a p) (ha0 : a p ≠ 0)
    (hL : D (φ p) ∈ chart) (hz : residual (D (φ p)) = 0)
    (hs : Surjective (fderiv ℝ (fun q ↦ residual (a q • D (φ q))) p)) :
    Surjective (fderiv ℝ (fun x ↦ residual (D x)) (φ p)) := by
  let R : X → F := fun x ↦ residual (D x)
  have hR : DifferentiableAt ℝ R (φ p) :=
    (((contDiffAt_residual (D (φ p)) (leading_invertible hL)).comp (φ p) hD).differentiableAt
      (by simp))
  have hc : ∀ᶠ q in 𝓝 p, D (φ q) ∈ chart :=
    (hD.continuousAt.comp hφ.continuousAt).eventually
      ((chart (E := E) (F := F)).isOpen.mem_nhds hL)
  have hn : ∀ᶠ q in 𝓝 p, a q ≠ 0 := ha.continuousAt.eventually_ne ha0
  have he : (fun q ↦ residual (a q • D (φ q))) =ᶠ[𝓝 p]
      (fun q ↦ a q • R (φ q)) := by
    filter_upwards [hc, hn] with q hq hqa
    exact residual_smul hq hqa
  have hd : fderiv ℝ (fun q ↦ a q • R (φ q)) p =
      a p • (fderiv ℝ R (φ p)).comp (fderiv ℝ φ p) := by
    have hz' : R (φ p) = 0 := hz
    simpa only [Pi.smul_def', Function.comp_def, hz',
      ContinuousLinearMap.smulRight_zero, add_zero] using
      (ha.hasFDerivAt.smul (hR.hasFDerivAt.comp p hφ.hasFDerivAt)).fderiv
  rw [he.fderiv_eq, hd] at hs
  intro y
  obtain ⟨v, hv⟩ := hs (a p • y)
  refine ⟨fderiv ℝ φ p v, ?_⟩
  have h := congrArg ((a p)⁻¹ • ·) hv
  change (a p)⁻¹ • (a p • fderiv ℝ R (φ p) (fderiv ℝ φ p v)) =
    (a p)⁻¹ • (a p • y) at h
  simpa only [inv_smul_smul₀ ha0] using h

end NoExoticSixSphere.CorankOne
