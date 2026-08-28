import Wikipedia.HopfProblem.SpecialPeriodsGlobalTauUniqueness
import Wikipedia.HopfProblem.SpecialPeriodsModularForms

/-!
# The global signs of a square root of the pulled-back Eisenstein series

Holomorphic functions on the actual upper half-plane have no zero divisors,
by its connected analytic identity theorem. Consequently, two holomorphic
square roots differ by one constant sign, including across their zeros.

The modular weight-six transformation law supplies the two sign candidates
for a square root of `E₆ ∘ τ`. At the order-three fixed point, the nonzero
Eisenstein value forces the negative candidate. Selecting the order-four
candidate from the root's local vanishing order is a separate argument.

The holomorphic maps `τ` and its square root are explicit inputs; this file
does not assume either generator sign or assert their global construction.
-/

noncomputable section

open Set UpperHalfPlane ModularForm ModularGroup
open scoped Topology ContDiff Manifold MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- The actual connected identity theorem on `ℍ` prevents two holomorphic
square roots from switching their relative sign at a zero. -/
theorem upperHalfPlane_holomorphic_sq_eq_sq_dichotomy {f g : ℍ → ℂ}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (hsq : ∀ z, f z ^ 2 = g z ^ 2) : f = g ∨ f = -g := by
  have hprod : (f - g) * (f + g) = 0 := by
    funext z
    change (f z - g z) * (f z + g z) = 0
    calc
      _ = f z ^ 2 - g z ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr (hsq z)
  rcases (UpperHalfPlane.mul_eq_zero_iff
    ((hf.sub hg).mdifferentiable (by simp))
    ((hf.add hg).mdifferentiable (by simp))).mp hprod with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

/-- The order-three generator gives equal squares by the actual modular
weight-six transformation law. No choice of square-root sign enters. -/
theorem eisensteinSix_root_generatorOne_sq {τ : ℍ → ℍ} {r : ℍ → ℂ}
    (hτc : TauCovariant τ) (hrsq : ∀ z, r z ^ 2 = E₆ (τ z)) (z : ℍ) :
    r (Triangle.generatorOneSL • z) ^ 2 = ((τ z : ℂ) ^ 3 * r z) ^ 2 := by
  have hτg : τ (Triangle.generatorOneSL • z) = (T * S) • τ z := by
    apply UpperHalfPlane.ext
    rw [← modularRhoAction_coe]
    exact hτc.1 z
  have hd : denom (T * S : SL(2, ℤ)) (τ z) = (τ z : ℂ) := by
    have h10 : (T * S : SL(2, ℤ)) 1 0 = 1 := by decide
    have h11 : (T * S : SL(2, ℤ)) 1 1 = 0 := by decide
    rw [denom_apply, h10, h11]
    simp
  calc
    _ = E₆ (τ (Triangle.generatorOneSL • z)) := hrsq _
    _ = (τ z : ℂ) ^ 6 * E₆ (τ z) := by
      rw [hτg, levelOne_transform, hd, zpow_ofNat]
    _ = ((τ z : ℂ) ^ 3 * r z) ^ 2 := by
      rw [← hrsq z]
      ring

/-- The analogous square identity for the order-four generator. -/
theorem eisensteinSix_root_generatorTwo_sq {τ : ℍ → ℍ} {r : ℍ → ℂ}
    (hτc : TauCovariant τ) (hrsq : ∀ z, r z ^ 2 = E₆ (τ z)) (z : ℍ) :
    r (Triangle.generatorTwoSL • z) ^ 2 = ((τ z : ℂ) ^ 3 * r z) ^ 2 := by
  have hτg : τ (Triangle.generatorTwoSL • z) = S • τ z := by
    apply UpperHalfPlane.ext
    rw [← modularIAction_coe]
    exact hτc.2 z
  calc
    _ = E₆ (τ (Triangle.generatorTwoSL • z)) := hrsq _
    _ = (τ z : ℂ) ^ 6 * E₆ (τ z) := by
      rw [hτg, levelOne_transform, denom_S, zpow_ofNat]
    _ = ((τ z : ℂ) ^ 3 * r z) ^ 2 := by
      rw [← hrsq z]
      ring

/-- Every such square root is nonzero at the actual order-three center. -/
theorem eisensteinSix_root_centerOne_ne_zero {τ : ℍ → ℍ} {r : ℍ → ℂ}
    (hτc : TauCovariant τ) (hrsq : ∀ z, r z ^ 2 = E₆ (τ z)) :
    r Triangle.centerOne ≠ 0 := by
  intro hrzero
  have h := hrsq Triangle.centerOne
  rw [hrzero, zero_pow (by decide), (tau_covariant_values hτc).1] at h
  exact E₆_rhoPoint_ne_zero h.symm

/-- Holomorphicity and the nonzero value at the order-three fixed point
force the global negative generator sign. -/
theorem eisensteinSix_root_generatorOne {τ : ℍ → ℍ} {r : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : TauCovariant τ)
    (hr : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω r)
    (hrsq : ∀ z, r z ^ 2 = E₆ (τ z)) :
    ∀ z, r (Triangle.generatorOneSL • z) = -(τ z : ℂ) ^ 3 * r z := by
  have hweight : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => (τ z : ℂ) ^ 3 * r z) :=
    ((UpperHalfPlane.contMDiff_coe.comp hτ).pow 3).mul hr
  rcases upperHalfPlane_holomorphic_sq_eq_sq_dichotomy
    (hr.comp (Triangle.specialLinear_holomorphic Triangle.generatorOneSL)) hweight
    (eisensteinSix_root_generatorOne_sq hτc hrsq) with hpos | hneg
  · exfalso
    have h := congrFun hpos Triangle.centerOne
    change r (Triangle.generatorOneSL • Triangle.centerOne) =
      (τ Triangle.centerOne : ℂ) ^ 3 * r Triangle.centerOne at h
    rw [Triangle.generatorOne_fix, (tau_covariant_values hτc).1,
      coe_rhoPoint, rho_cube, neg_one_mul] at h
    apply eisensteinSix_root_centerOne_ne_zero hτc hrsq
    linear_combination h / 2
  · intro z
    simpa only [Function.comp_apply, Pi.neg_apply, neg_mul] using congrFun hneg z

/-- For the order-four generator there is one global sign, not a sign
depending on the point. The local simple-zero calculation selects it later. -/
theorem eisensteinSix_root_generatorTwo_dichotomy {τ : ℍ → ℍ} {r : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : TauCovariant τ)
    (hr : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω r)
    (hrsq : ∀ z, r z ^ 2 = E₆ (τ z)) :
    (∀ z, r (Triangle.generatorTwoSL • z) = (τ z : ℂ) ^ 3 * r z) ∨
      (∀ z, r (Triangle.generatorTwoSL • z) = -(τ z : ℂ) ^ 3 * r z) := by
  have hweight : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => (τ z : ℂ) ^ 3 * r z) :=
    ((UpperHalfPlane.contMDiff_coe.comp hτ).pow 3).mul hr
  rcases upperHalfPlane_holomorphic_sq_eq_sq_dichotomy
    (hr.comp (Triangle.specialLinear_holomorphic Triangle.generatorTwoSL)) hweight
    (eisensteinSix_root_generatorTwo_sq hτc hrsq) with hpos | hneg
  · exact Or.inl (congrFun hpos)
  · right
    intro z
    simpa only [Function.comp_apply, Pi.neg_apply, neg_mul] using congrFun hneg z

end Wikipedia.HopfProblem.SpecialPeriods
