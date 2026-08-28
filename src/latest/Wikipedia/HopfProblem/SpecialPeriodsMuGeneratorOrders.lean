import Wikipedia.HopfProblem.SpecialPeriodsMuGeneratorBasic
import Wikipedia.HopfProblem.SpecialPeriodsGlobalTauUniqueness

/-!
# Exact orders of the homogeneous μ-generator

The order formula is valid at every actual point of the upper half-plane.
The orders two and one at the two distinguished elliptic points follow
from the supplied lift orders one and two and the actual covariance laws.
No assertion about other fibres follows merely from these two local orders.
-/

noncomputable section

open UpperHalfPlane ModularForm ModularGroup
open scoped Manifold ContDiff MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods.MuGenerator

theorem modularForm_pullback_analyticAt {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) {k : ℤ}
    (f : ModularForm 𝒮ℒ k) (a : ℍ) :
    AnalyticAt ℂ (fun z : ℂ => f (τ (ofComplex z))) (a : ℂ) :=
  (UpperHalfPlane.contMDiffAt_iff.mp ((modularForm_holomorphic f).comp hτ a)).analyticAt

namespace Root

variable {τ : ℍ → ℍ} (r : Root τ)

theorem generator_analyticAt (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (a : ℍ) :
    AnalyticAt ℂ (r.generator ∘ ofComplex) (a : ℂ) :=
  (UpperHalfPlane.contMDiffAt_iff.mp (r.generator_holomorphic hτ a)).analyticAt

/-- The full pointwise order formula, including infinite orders. -/
theorem generator_order (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (a : ℍ) :
    analyticOrderAt (r.generator ∘ ofComplex) (a : ℂ) =
      2 • analyticOrderAt (fun z : ℂ => E₄ (τ (ofComplex z))) (a : ℂ) +
        analyticOrderAt (r ∘ ofComplex) (a : ℂ) := by
  let f4 : ℂ → ℂ := fun z => E₄ (τ (ofComplex z))
  let fD : ℂ → ℂ := fun z => discriminant (τ (ofComplex z))
  have h4 : AnalyticAt ℂ f4 (a : ℂ) := modularForm_pullback_analyticAt hτ E₄ a
  have hD : AnalyticAt ℂ fD (a : ℂ) :=
    modularForm_pullback_analyticAt hτ (CuspForm.discriminant : ModularForm 𝒮ℒ 12) a
  have hD0 : fD (a : ℂ) ≠ 0 := by
    simpa only [fD, ofComplex_apply] using discriminant_ne_zero (τ a)
  have hDi := hD.inv hD0
  have hDiorder : analyticOrderAt fD⁻¹ (a : ℂ) = 0 :=
    hDi.analyticOrderAt_eq_zero.mpr (inv_ne_zero hD0)
  have he : r.generator ∘ ofComplex =
      (f4 ^ 2 * (r ∘ ofComplex)) * fD⁻¹ := by
    funext z
    exact div_eq_mul_inv _ _
  rw [he, analyticOrderAt_mul ((h4.pow 2).mul (r.analyticAt a)) hDi,
    analyticOrderAt_mul (h4.pow 2) (r.analyticAt a), analyticOrderAt_pow h4,
    hDiorder, add_zero]

/-- The exact finite order obtained from both genuine Eisenstein pullbacks. -/
theorem generator_order_of_pullback_orders
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (a : ℍ) (m n : ℕ)
    (h4 : analyticOrderAt (fun z : ℂ => E₄ (τ (ofComplex z))) (a : ℂ) = m)
    (h6 : analyticOrderAt (fun z : ℂ => E₆ (τ (ofComplex z))) (a : ℂ) = (2 * n : ℕ)) :
    analyticOrderAt (r.generator ∘ ofComplex) (a : ℂ) = (2 * m + n : ℕ) := by
  rw [r.generator_order hτ, h4, r.order_of_square_order a n h6]
  simp only [two_nsmul, ← Nat.cast_add]
  congr 1
  omega

/-- The chosen or any other square root has a simple zero at the second
elliptic point when the actual lift has order two there. -/
theorem order_centerTwo_of_tau_order
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hc : TauCovariant τ)
    (ho : analyticOrderAt (fun z : ℂ => (τ (ofComplex z) : ℂ) - Complex.I)
      (Triangle.centerTwo : ℂ) = 2) :
    analyticOrderAt (r ∘ ofComplex) (Triangle.centerTwo : ℂ) = 1 := by
  have hv := (tau_covariant_values hc).2
  have h6 := ModularGermLift.native_E₆_lift_order_of_zero
    (hτ.mdifferentiable (by simp)) (a := Triangle.centerTwo) (by rw [hv, E₆_I])
  rw [hv, coe_I] at h6
  apply r.order_of_square_order Triangle.centerTwo 1
  simpa only [Nat.mul_one, Nat.cast_ofNat] using h6.trans ho

/-- Exact order two at the first elliptic point of the actual triangle action. -/
theorem generator_order_centerOne_of_tau_order
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hc : TauCovariant τ)
    (ho : analyticOrderAt (fun z : ℂ => (τ (ofComplex z) : ℂ) - rho)
      (Triangle.centerOne : ℂ) = 1) :
    analyticOrderAt (r.generator ∘ ofComplex) (Triangle.centerOne : ℂ) = 2 := by
  have hv := (tau_covariant_values hc).1
  have h4 := ModularGermLift.native_E₄_lift_order_of_zero
    (hτ.mdifferentiable (by simp)) (a := Triangle.centerOne) (by rw [hv, E₄_rhoPoint])
  rw [hv, coe_rhoPoint] at h4
  have h6 : analyticOrderAt (fun z : ℂ => E₆ (τ (ofComplex z)))
      (Triangle.centerOne : ℂ) = (2 * 0 : ℕ) := by
    apply analyticOrderAt_eq_zero.mpr
    right
    simpa only [ofComplex_apply, hv] using E₆_rhoPoint_ne_zero
  simpa only [Nat.mul_one, Nat.add_zero, Nat.cast_ofNat] using
    r.generator_order_of_pullback_orders hτ Triangle.centerOne 1 0 (h4.trans ho) h6

/-- Exact order one at the second elliptic point of the actual triangle action. -/
theorem generator_order_centerTwo_of_tau_order
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hc : TauCovariant τ)
    (ho : analyticOrderAt (fun z : ℂ => (τ (ofComplex z) : ℂ) - Complex.I)
      (Triangle.centerTwo : ℂ) = 2) :
    analyticOrderAt (r.generator ∘ ofComplex) (Triangle.centerTwo : ℂ) = 1 := by
  have hv := (tau_covariant_values hc).2
  have h4 : analyticOrderAt (fun z : ℂ => E₄ (τ (ofComplex z)))
      (Triangle.centerTwo : ℂ) = 0 := by
    apply analyticOrderAt_eq_zero.mpr
    right
    simpa only [ofComplex_apply, hv] using E₄_I_ne_zero
  rw [r.generator_order hτ, h4, r.order_centerTwo_of_tau_order hτ hc ho,
    smul_zero, zero_add]

end Root

end Wikipedia.HopfProblem.SpecialPeriods.MuGenerator
