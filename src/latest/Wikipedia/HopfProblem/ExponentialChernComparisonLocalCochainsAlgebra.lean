import Wikipedia.HopfProblem.PeriodTorusLineBundleChernCocycleBasic
import Mathlib.Data.Complex.Basic

/-!
# The local integral two-cocycle identities

These are the literal inhomogeneous cocycle identities which occur in a
local primitive and in the difference of two local primitives. No
normalization of the two-cocycle is required.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ExponentialChernComparison.LocalCochains

open PeriodTorusLineBundle.ChernCocycle

variable {A : Type*} [AddCommGroup A]

/-- The alternating triangle defect of the local one-cochain is the
original group two-cocycle. -/
theorem integral_triangle_defect (k : IntegralTwoCocycle A) (r a b : A) :
    k (r + a) b - k r (a + b) + k r a = k a b := by
  have h := k.cocycle r a b
  omega

/-- Translating a local lift changes its one-cochain by the endpoint
difference of the original two-cocycle. -/
theorem integral_shift_difference (k : IntegralTwoCocycle A) (d r a : A) :
    k (d + r) a - k r a = k d (r + a) - k d r := by
  have h := k.cocycle d r a
  omega

/-- The triangle identity, written in terms of the three local vertex
lifts rather than their differences. -/
theorem integral_vertex_triangle_defect (k : IntegralTwoCocycle A)
    (r₀ r₁ r₂ : A) :
    k r₁ (r₂ - r₁) - k r₀ (r₂ - r₀) + k r₀ (r₁ - r₀) =
      k (r₁ - r₀) (r₂ - r₁) := by
  have h₁ : r₀ + (r₁ - r₀) = r₁ := by abel
  have h₂ : (r₁ - r₀) + (r₂ - r₁) = r₂ - r₀ := by abel
  simpa only [h₁, h₂] using integral_triangle_defect k r₀ (r₁ - r₀) (r₂ - r₁)

/-- The same translation identity with endpoint vertex lifts. -/
theorem integral_vertex_shift_difference (k : IntegralTwoCocycle A)
    (d r₀ r₁ : A) :
    k (d + r₀) (r₁ - r₀) - k r₀ (r₁ - r₀) = k d r₁ - k d r₀ := by
  have h : r₀ + (r₁ - r₀) = r₁ := by abel
  simpa only [h] using integral_shift_difference k d r₀ (r₁ - r₀)

/-- Multiplication by the chosen complex period is an actual additive
coefficient map on the integers. -/
def integerPeriodHom (P : ℂ) : ℤ →+ ℂ where
  toFun n := (n : ℂ) * P
  map_zero' := by simp
  map_add' m n := by simp only [Int.cast_add, add_mul]

@[simp] theorem integerPeriodHom_apply (P : ℂ) (n : ℤ) :
    integerPeriodHom P n = (n : ℂ) * P := rfl

end Wikipedia.HopfProblem.ExponentialChernComparison.LocalCochains
