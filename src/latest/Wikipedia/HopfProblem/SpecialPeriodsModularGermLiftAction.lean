import Wikipedia.HopfProblem.SpecialPeriodsModular
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

/-!
# Analytic modular actions on local lift representatives

The genuine `SL(2, ℤ)` action, applied to a complex-valued representative
through `UpperHalfPlane.ofComplex`, is analytic wherever that representative
is analytic and has positive imaginary part.  Positivity at the point
suffices; no hypothesis on the representative away from a neighborhood of
that point is required.
-/

noncomputable section

open Matrix Set UpperHalfPlane
open scoped MatrixGroups Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.ModularGermLift

/-- The denominator of an integer modular transformation is nonzero in the upper half-plane. -/
theorem modular_denom_ne_zero (γ : SL(2, ℤ)) {w : ℂ} (hw : 0 < w.im) :
    (γ 1 0 : ℂ) * w + (γ 1 1 : ℂ) ≠ 0 := by
  have h := UpperHalfPlane.denom_ne_zero
    (SpecialLinearGroup.mapGL ℝ γ) (⟨w, hw⟩ : ℍ)
  simpa [UpperHalfPlane.denom, SpecialLinearGroup.mapGL] using h

/-- The actual modular action agrees with its complex rational formula. -/
theorem modular_smul_eq_fraction (γ : SL(2, ℤ)) {w : ℂ} (hw : 0 < w.im) :
    ((γ • ofComplex w : ℍ) : ℂ) =
      ((γ 0 0 : ℂ) * w + (γ 0 1 : ℂ)) /
        ((γ 1 0 : ℂ) * w + (γ 1 1 : ℂ)) := by
  rw [ofComplex_apply_of_im_pos hw, coe_specialLinearGroup_apply]
  simp

/-- A modular transformation is analytic as a complex-valued map at every upper-half-plane point. -/
theorem analyticAt_modular_smul_of_im_pos (γ : SL(2, ℤ)) {w : ℂ} (hw : 0 < w.im) :
    AnalyticAt ℂ (fun v : ℂ => ((γ • ofComplex v : ℍ) : ℂ)) w := by
  change AnalyticAt ℂ
    (fun v : ℂ => ((SpecialLinearGroup.mapGL ℝ γ • ofComplex v : ℍ) : ℂ)) w
  apply UpperHalfPlane.analyticAt_smul (τ := (⟨w, hw⟩ : ℍ))
  change 0 < ((SpecialLinearGroup.mapGL ℝ γ).det : ℝ)
  simp

/-- Composing a local analytic lift with any modular transformation preserves analyticity. -/
theorem analyticAt_modular_smul (γ : SL(2, ℤ)) {σ : ℂ → ℂ} {a : ℂ}
    (hσ : AnalyticAt ℂ σ a) (hσa : 0 < (σ a).im) :
    AnalyticAt ℂ (fun z => ((γ • ofComplex (σ z) : ℍ) : ℂ)) a :=
  (analyticAt_modular_smul_of_im_pos γ hσa).comp hσ

/-- Analyticity of the modular action along any representative mapping into the upper half-plane.
The source set need not be open. -/
theorem analyticOnNhd_modular_smul (γ : SL(2, ℤ)) {σ : ℂ → ℂ} {U : Set ℂ}
    (hσ : AnalyticOnNhd ℂ σ U) (hσU : MapsTo σ U upperHalfPlaneSet) :
    AnalyticOnNhd ℂ (fun z => ((γ • ofComplex (σ z) : ℍ) : ℂ)) U :=
  fun a ha => analyticAt_modular_smul γ (hσ a ha) (hσU ha)

/-- Continuity at a point only requires continuity of the original representative there. -/
theorem continuousAt_modular_smul (γ : SL(2, ℤ)) {σ : ℂ → ℂ} {a : ℂ}
    (hσ : ContinuousAt σ a) (hσa : 0 < (σ a).im) :
    ContinuousAt (fun z => ((γ • ofComplex (σ z) : ℍ) : ℂ)) a :=
  (analyticAt_modular_smul_of_im_pos γ hσa).continuousAt.comp hσ

/-- Continuity of the modular action on a set of upper-half-plane-valued representatives. -/
theorem continuousOn_modular_smul (γ : SL(2, ℤ)) {σ : ℂ → ℂ} {U : Set ℂ}
    (hσ : ContinuousOn σ U) (hσU : MapsTo σ U upperHalfPlaneSet) :
    ContinuousOn (fun z => ((γ • ofComplex (σ z) : ℍ) : ℂ)) U :=
  fun a ha => (analyticAt_modular_smul_of_im_pos γ (hσU ha)).continuousAt.comp_continuousWithinAt
    (hσ a ha)

/-- The transformed representative always has positive imaginary part. -/
theorem modular_smul_im_pos (γ : SL(2, ℤ)) (w : ℂ) :
    0 < (((γ • ofComplex w : ℍ) : ℂ)).im :=
  (γ • ofComplex w).im_pos

/-- The actual modular function is unchanged by acting on a local representative. -/
theorem modularJ_modular_smul (γ : SL(2, ℤ)) (w : ℂ) :
    modularJ (ofComplex ((γ • ofComplex w : ℍ) : ℂ)) = modularJ (ofComplex w) := by
  rw [ofComplex_apply]
  exact modularJ_SL_invariant γ (ofComplex w)

end Wikipedia.HopfProblem.SpecialPeriods.ModularGermLift
