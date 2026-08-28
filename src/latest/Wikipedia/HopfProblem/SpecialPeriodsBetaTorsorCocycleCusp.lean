import Wikipedia.HopfProblem.SpecialPeriodsBetaTorsorCocycle

/-!
# The beta shift of the actual cusp subgroup

The supplied relation between the two generator functions makes their
product shift by minus one. Since the actual cusp generator is the
inverse of that product, its shift is one, and every integral cusp power
has precisely its integer exponent as shift.
-/

noncomputable section

open UpperHalfPlane

namespace Wikipedia.HopfProblem.SpecialPeriods.BetaTorsor

variable (φ₁ φ₂ : ℍ → ℂ)
variable (h₁ : ∀ z, (∑ k ∈ Finset.range 3, φ₁ ((Triangle.generatorOnePerm ^ k) z)) = 0)
variable (h₂ : ∀ z, (∑ k ∈ Finset.range 4, φ₂ ((Triangle.generatorTwoPerm ^ k) z)) = 0)

/-- A constant generator shift accumulates linearly under natural powers. -/
theorem triangleAdditiveShift_pow_of_const (g : TriangleGroup) (c : ℂ)
    (hg : ∀ z, triangleAdditiveShift φ₁ φ₂ h₁ h₂ g z = c) (n : ℕ) (z : ℍ) :
    triangleAdditiveShift φ₁ φ₂ h₁ h₂ (g ^ n) z = (n : ℂ) * c := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, triangleAdditiveShift_mul, ih, hg]
      push_cast
      ring

/-- A constant generator shift accumulates linearly under all integer powers. -/
theorem triangleAdditiveShift_zpow_of_const (g : TriangleGroup) (c : ℂ)
    (hg : ∀ z, triangleAdditiveShift φ₁ φ₂ h₁ h₂ g z = c) (n : ℤ) (z : ℍ) :
    triangleAdditiveShift φ₁ φ₂ h₁ h₂ (g ^ n) z = (n : ℂ) * c := by
  cases n with
  | ofNat n =>
      simpa using
        triangleAdditiveShift_pow_of_const φ₁ φ₂ h₁ h₂ g c hg n z
  | negSucc n =>
      rw [zpow_negSucc, triangleAdditiveShift_inv,
        triangleAdditiveShift_pow_of_const φ₁ φ₂ h₁ h₂ g c hg]
      push_cast
      ring

variable (hproduct : ∀ z, φ₁ (Triangle.generatorTwoPerm z) + φ₂ z = -1)

include hproduct

/-- The product of the two distinguished generators shifts by minus one. -/
theorem triangleAdditiveShift_product (z : ℍ) :
    triangleAdditiveShift φ₁ φ₂ h₁ h₂ (triangleGenerator₁ * triangleGenerator₂) z = -1 := by
  rw [triangleAdditiveShift_mul, triangleAdditiveShift_generator₁,
    triangleAdditiveShift_generator₂, triangleGeometricRepresentation_generator₂]
  exact hproduct z

/-- The actual cusp generator has additive beta shift one. -/
theorem triangleAdditiveShift_cusp (z : ℍ) :
    triangleAdditiveShift φ₁ φ₂ h₁ h₂ triangleCuspGenerator z = 1 := by
  rw [triangleCuspGenerator, triangleAdditiveShift_inv,
    triangleAdditiveShift_product φ₁ φ₂ h₁ h₂ hproduct]
  norm_num

/-- Every integral cusp iterate has its prescribed integer shift. -/
theorem triangleAdditiveShift_cusp_zpow (n : ℤ) (z : ℍ) :
    triangleAdditiveShift φ₁ φ₂ h₁ h₂ (triangleCuspGenerator ^ n) z = (n : ℂ) := by
  simpa only [mul_one] using triangleAdditiveShift_zpow_of_const φ₁ φ₂ h₁ h₂
    triangleCuspGenerator 1 (triangleAdditiveShift_cusp φ₁ φ₂ h₁ h₂ hproduct) n z

end Wikipedia.HopfProblem.SpecialPeriods.BetaTorsor
