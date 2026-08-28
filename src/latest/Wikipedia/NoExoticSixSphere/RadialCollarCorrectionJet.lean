import Wikipedia.NoExoticSixSphere.RadialCollarCorrection

/-!
# The radial collar correction preserves a zero core jet

If the original sphere-product map has zero value and native derivative on
its core, the supported disk-product correction has zero ordinary derivative
on the entire disk core, including its center.
-/

noncomputable section

open Set Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.RadialCollarCorrection

open GLOrthonormalization

variable {q : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_correction_core (χ : ContDiffBump (0 : Vector 4)) (b : Sphere 3)
    (g : Sphere 3 × Vector q → F)
    (hgs : ∀ s : Sphere 3, ContMDiffAt ((𝓡 3).prod (𝓡 q)) 𝓘(ℝ, F) ∞ g (s, 0))
    (hg : ∀ s : Sphere 3, g (s, 0) = 0)
    (hzero : ∀ s : Sphere 3, mfderiv ((𝓡 3).prod (𝓡 q)) 𝓘(ℝ, F) g (s, 0) = 0)
    (x : Vector 4) : fderiv ℝ (correction χ b g) (x, 0) = 0 := by
  by_cases hx : x = 0
  · subst x
    rw [(correction_eventuallyEq_zero χ b g (mem_ball_self χ.rIn_pos) 0).fderiv_eq]
    simp
  · have hss : ContDiffAt ℝ ∞ (fun p : Vector 4 × Vector q ↦ 1 - χ p.1) (x, 0) :=
      contDiffAt_const.sub (χ.contDiff.contDiffAt.comp (x, (0 : Vector q)) contDiffAt_fst)
    have hs := hss.differentiableAt (by simp)
    have hG := (SphereRadialProduct.contDiffAt_pullback b g hx 0
      (hgs (SphereRadialRetraction.retract b x))).differentiableAt (by simp)
    have hGj := SphereRadialProduct.fderiv_pullback_eq_zero b g hx 0
      (hgs (SphereRadialRetraction.retract b x)) (hzero (SphereRadialRetraction.retract b x))
    have hG' := hG.hasFDerivAt
    rw [hGj] at hG'
    have he := (hs.hasFDerivAt.smul hG').fderiv
    change fderiv ℝ (correction χ b g) (x, 0) = _ at he
    simpa [SphereRadialProduct.pullback, hg] using he

end NoExoticSixSphere.RadialCollarCorrection
