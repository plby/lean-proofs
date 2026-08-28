import Wikipedia.HopfProblem.TrianglePeriodFamilyCanonicalRegular

/-!
# The actual regular fibre-determinant cocycle

The two proved generator laws imply the transformation law under the
entire triangle group.  The multiplier is the determinant of the actual
varying-period fibre matrix, with its proved cocycle identity.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalRegular

open TrianglePeriodFamily.Canonical

/-- Generator covariance extends to every element of the actual triangle group. -/
theorem determinant_covariant_of_generators (F : TriangleRegularPoint → ℂ)
    (h₁ : ∀ z, F (triangleGenerator₁ • z) =
      specialRegularData.determinantFactor triangleGenerator₁ z * F z)
    (h₂ : ∀ z, F (triangleGenerator₂ • z) =
      specialRegularData.determinantFactor triangleGenerator₂ z * F z)
    (g : TriangleGroup) :
    ∀ z, F (g • z) = specialRegularData.determinantFactor g z * F z := by
  have hg : g ∈ Subgroup.closure
      ({triangleGenerator₁, triangleGenerator₂} : Set TriangleGroup) := by
    rw [triangle_generators_generate]
    trivial
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with rfl | rfl
    · exact h₁
    · exact h₂
  | one =>
    intro z
    rw [one_smul, specialRegularData.determinantFactor_one, one_mul]
  | mul g h _ _ ihg ihh =>
    intro z
    rw [mul_smul, ihg, ihh, specialRegularData.determinantFactor_mul, mul_assoc]
  | inv g _ ih =>
    intro z
    have h := ih (g⁻¹ • z)
    rw [smul_inv_smul] at h
    have hd := specialRegularData.determinantFactor_inv g (g⁻¹ • z)
    rw [smul_inv_smul] at hd
    rw [hd, h, ← mul_assoc,
      inv_mul_cancel₀ (specialRegularData.determinantFactor_ne_zero g (g⁻¹ • z)), one_mul]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalRegular
