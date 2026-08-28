import Wikipedia.HopfProblem.EllipticHigherHomologyMappingTorusCompact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Circle-lift arithmetic for the finite quotient mapping-torus model

Equality of scaled real times in the actual additive circle records
exactly an integer deck shift, including the multiples of the finite order.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology.MappingTorusQuotient

open MappingTorus

/-- Equality of the actual scaled circle coordinates is exactly an
integer time change congruent to the indicated fibre exponent. -/
theorem circle_scaled_eq_iff (m : ℕ) [NeZero m] (s t : ℝ) (n : ℤ) :
    ((s / m : ℝ) : Circle) = ((t / m + (n : ℝ) / m : ℝ) : Circle) ↔
      ∃ k : ℤ, s = t + ((n + (m : ℤ) * k : ℤ) : ℝ) := by
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  constructor
  · intro h
    obtain ⟨k, hk⟩ := (circle_coe_eq_iff _ _).mp h.symm
    refine ⟨k, ?_⟩
    push_cast
    calc
      s = (s / m) * m := (div_mul_cancel₀ s hm).symm
      _ = (t / m + (n : ℝ) / m + (k : ℝ)) * m := by rw [hk]
      _ = t + ((n : ℝ) + (m : ℝ) * k) := by
        rw [add_mul, add_mul, div_mul_cancel₀ _ hm, div_mul_cancel₀ _ hm]
        ring
  · rintro ⟨k, hk⟩
    apply Eq.symm
    apply (circle_coe_eq_iff _ _).mpr
    refine ⟨k, ?_⟩
    rw [hk]
    push_cast
    field_simp [hm]
    ring

/-- The inverse-monodromy convention makes the mapping-torus deck
transformation apply the positive power of the original fibre map. -/
theorem symm_zpow_neg {X : Type*} [TopologicalSpace X] (B : X ≃ₜ X) (n : ℤ) :
    B.symm ^ (-n) = B ^ n := by
  change (B⁻¹) ^ (-n) = B ^ n
  rw [inv_zpow, zpow_neg, inv_inv]

end Wikipedia.HopfProblem.Elliptic.HigherHomology.MappingTorusQuotient
