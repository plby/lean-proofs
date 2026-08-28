import Wikipedia.HopfProblem.SpecialPeriodsModularGermLiftOrders

/-!
# Orders of native upper-half-plane modular lifts

The ambient composition-order theorems apply to every actual holomorphic map
from the upper half-plane to itself.  This file provides the native versions,
including exact orders of the pulled-back Eisenstein series.  In particular,
source orders divisible by four over `1728` give finite even orders at every
zero of the actual `E₆` pullback.
-/

noncomputable section

open Filter Set UpperHalfPlane ModularForm
open scoped Topology Manifold ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.ModularGermLift

/-- A holomorphic native map to the upper half-plane is analytic in its
actual ambient complex coordinate near every point. -/
theorem analyticAt_upperHalfPlane_lift {τ : ℍ → ℍ}
    (hτ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) τ) (a : ℍ) :
    AnalyticAt ℂ (fun z => (τ (ofComplex z) : ℂ)) (a : ℂ) :=
  (UpperHalfPlane.mdifferentiable_iff.mp
    (UpperHalfPlane.mdifferentiable_coe.comp hτ)).analyticAt
      (isOpen_upperHalfPlaneSet.mem_nhds a.im_pos)

/-- The native modular equation gives the exact ambient germ equation. -/
theorem native_modular_equation_eventually {τ : ℍ → ℍ} {F : ℍ → ℂ}
    (hJ : ∀ a : ℍ, modularJ (τ a) = F a) (a : ℍ) :
    (fun z : ℂ => modularJ (ofComplex (τ (ofComplex z)))) =ᶠ[𝓝 (a : ℂ)]
      (F ∘ ofComplex) := by
  filter_upwards with z
  simpa only [ofComplex_apply, Function.comp_apply] using hJ (ofComplex z)

/-- Every native lift over a source zero of order `3n` has order `n`. -/
theorem native_modularJ_lift_order_of_zero {τ : ℍ → ℍ} {F : ℍ → ℂ}
    (hτ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) τ)
    (hJ : ∀ a : ℍ, modularJ (τ a) = F a) {a : ℍ} {n : ℕ}
    (ha : F a = 0)
    (horder : analyticOrderAt (F ∘ ofComplex) (a : ℂ) = (3 * n : ℕ)) :
    analyticOrderAt (fun z : ℂ => (τ (ofComplex z) : ℂ) - (τ a : ℂ)) (a : ℂ) = n := by
  simpa only [ofComplex_apply] using modularJ_lift_order_of_zero
    (analyticAt_upperHalfPlane_lift hτ a)
    (by simpa only [ofComplex_apply, coe_im] using (τ a).im_pos)
    (native_modular_equation_eventually hJ a)
    (by simpa only [Function.comp_apply, ofComplex_apply] using ha) horder

/-- Every native lift over a `1728`-point of source order `2n` has order `n`. -/
theorem native_modularJ_lift_order_of_1728 {τ : ℍ → ℍ} {F : ℍ → ℂ}
    (hτ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) τ)
    (hJ : ∀ a : ℍ, modularJ (τ a) = F a) {a : ℍ} {n : ℕ}
    (ha : F a = 1728)
    (horder : analyticOrderAt (fun z : ℂ => F (ofComplex z) - 1728) (a : ℂ) =
      (2 * n : ℕ)) :
    analyticOrderAt (fun z : ℂ => (τ (ofComplex z) : ℂ) - (τ a : ℂ)) (a : ℂ) = n := by
  simpa only [ofComplex_apply] using modularJ_lift_order_of_1728
    (analyticAt_upperHalfPlane_lift hτ a)
    (by simpa only [ofComplex_apply, coe_im] using (τ a).im_pos)
    (native_modular_equation_eventually hJ a)
    (by simpa only [Function.comp_apply, ofComplex_apply] using ha) horder

/-- The order of the native `E₄` pullback at a zero is exactly the order of
the lift in the ambient complex coordinate. -/
theorem native_E₄_lift_order_of_zero {τ : ℍ → ℍ}
    (hτ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) τ) {a : ℍ} (ha : E₄ (τ a) = 0) :
    analyticOrderAt (fun z : ℂ => E₄ (τ (ofComplex z))) (a : ℂ) =
      analyticOrderAt (fun z : ℂ => (τ (ofComplex z) : ℂ) - (τ a : ℂ)) (a : ℂ) := by
  simpa only [ofComplex_apply] using E₄_lift_order_of_zero
    (analyticAt_upperHalfPlane_lift hτ a)
    (by simpa only [ofComplex_apply, coe_im] using (τ a).im_pos)
    (by simpa only [ofComplex_apply] using ha)

/-- The order of the native `E₆` pullback at a zero is exactly the order of
the lift in the ambient complex coordinate. -/
theorem native_E₆_lift_order_of_zero {τ : ℍ → ℍ}
    (hτ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) τ) {a : ℍ} (ha : E₆ (τ a) = 0) :
    analyticOrderAt (fun z : ℂ => E₆ (τ (ofComplex z))) (a : ℂ) =
      analyticOrderAt (fun z : ℂ => (τ (ofComplex z) : ℂ) - (τ a : ℂ)) (a : ℂ) := by
  simpa only [ofComplex_apply] using E₆_lift_order_of_zero
    (analyticAt_upperHalfPlane_lift hτ a)
    (by simpa only [ofComplex_apply, coe_im] using (τ a).im_pos)
    (by simpa only [ofComplex_apply] using ha)

/-- Source order `3n` gives exact order `n` for the actual `E₄` pullback. -/
theorem native_E₄_order_of_source_order {τ : ℍ → ℍ} {F : ℍ → ℂ}
    (hτ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) τ)
    (hJ : ∀ a : ℍ, modularJ (τ a) = F a) {a : ℍ} {n : ℕ}
    (ha : F a = 0)
    (horder : analyticOrderAt (F ∘ ofComplex) (a : ℂ) = (3 * n : ℕ)) :
    analyticOrderAt (fun z : ℂ => E₄ (τ (ofComplex z))) (a : ℂ) = n := by
  have hE : E₄ (τ a) = 0 :=
    (modularJ_eq_zero_iff (τ a)).mp ((hJ a).trans ha)
  exact (native_E₄_lift_order_of_zero hτ hE).trans
    (native_modularJ_lift_order_of_zero hτ hJ ha horder)

/-- Source order `2n` gives exact order `n` for the actual `E₆` pullback. -/
theorem native_E₆_order_of_source_order {τ : ℍ → ℍ} {F : ℍ → ℂ}
    (hτ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) τ)
    (hJ : ∀ a : ℍ, modularJ (τ a) = F a) {a : ℍ} {n : ℕ}
    (ha : F a = 1728)
    (horder : analyticOrderAt (fun z : ℂ => F (ofComplex z) - 1728) (a : ℂ) =
      (2 * n : ℕ)) :
    analyticOrderAt (fun z : ℂ => E₆ (τ (ofComplex z))) (a : ℂ) = n := by
  have hE : E₆ (τ a) = 0 :=
    (modularJ_eq_1728_iff (τ a)).mp ((hJ a).trans ha)
  exact (native_E₆_lift_order_of_zero hτ hE).trans
    (native_modularJ_lift_order_of_1728 hτ hJ ha horder)

/-- Exact source order `4k` gives even order `2k` of the native `E₆` pullback. -/
theorem native_E₆_order_of_source_four_order {τ : ℍ → ℍ} {F : ℍ → ℂ}
    (hτ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) τ)
    (hJ : ∀ a : ℍ, modularJ (τ a) = F a) {a : ℍ} {k : ℕ}
    (ha : F a = 1728)
    (horder : analyticOrderAt (fun z : ℂ => F (ofComplex z) - 1728) (a : ℂ) =
      (4 * k : ℕ)) :
    analyticOrderAt (fun z : ℂ => E₆ (τ (ofComplex z))) (a : ℂ) = (2 * k : ℕ) := by
  apply native_E₆_order_of_source_order hτ hJ ha
  simpa only [← Nat.mul_assoc] using horder

/-- **Finite even zeros of the actual `E₆` pullback.** The only order
assumptions are on the original source function at its `1728`-points. -/
theorem native_E₆_finite_even_zeros {τ : ℍ → ℍ} {F : ℍ → ℂ}
    (hτ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) τ)
    (hJ : ∀ a : ℍ, modularJ (τ a) = F a)
    (hsource : ∀ a : ℍ, F a = 1728 → ∃ k : ℕ,
      analyticOrderAt (fun z : ℂ => F (ofComplex z) - 1728) (a : ℂ) = (4 * k : ℕ)) :
    ∀ a : ℍ, E₆ (τ a) = 0 → ∃ n : ℕ,
      analyticOrderAt (fun z : ℂ => E₆ (τ (ofComplex z))) (a : ℂ) = (2 * n : ℕ) := by
  intro a ha
  have hFa : F a = 1728 :=
    (hJ a).symm.trans ((modularJ_eq_1728_iff (τ a)).mpr ha)
  obtain ⟨k, hk⟩ := hsource a hFa
  exact ⟨k, native_E₆_order_of_source_four_order hτ hJ hFa hk⟩

end Wikipedia.HopfProblem.SpecialPeriods.ModularGermLift
