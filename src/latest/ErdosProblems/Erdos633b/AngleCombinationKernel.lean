import ErdosProblems.Erdos633b.AngleRelationCounts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Subgroup.Basic

/-! The integer kernel of the direction lattice, and its parity characters.
This supplies a direct alternative to a path-based coloring construction. -/

namespace Erdos633b

noncomputable def realAngleCombination (a b : ℝ) : (ℤ × ℤ) →+ ℝ where
  toFun z := (z.1 : ℝ) * a + (z.2 : ℝ) * b
  map_zero' := by simp
  map_add' z w := by
    change ((z.1 + w.1 : ℤ) : ℝ) * a + ((z.2 + w.2 : ℤ) : ℝ) * b = _
    push_cast
    ring

noncomputable def angleCombination (a b : ℝ) : (ℤ × ℤ) →+ Real.Angle :=
  Real.Angle.coeHom.comp (realAngleCombination a b)

theorem angleCombination_eq_zero_iff {a b : ℝ} (P Q : ℤ) (hQ : Q ≠ 0)
    (hrel : (P : ℝ) * a + (Q : ℝ) * b = Real.pi) (ha : Irrational (a / Real.pi))
    (z : ℤ × ℤ) : angleCombination a b z = 0 ↔ ∃ k : ℤ, z = (2 * k * P, 2 * k * Q) := by
  change (((z.1 : ℝ) * a + (z.2 : ℝ) * b : ℝ) : Real.Angle) = 0 ↔ _
  rw [Real.Angle.coe_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    have he : ((z.1 - 2 * k * P : ℤ) : ℝ) * a +
        ((z.2 - 2 * k * Q : ℤ) : ℝ) * b = 0 := by
      push_cast
      simp only [zsmul_eq_mul] at hk
      linear_combination -hk - 2 * (k : ℝ) * hrel
    obtain ⟨hu, hv⟩ := two_angle_integer_coefficients P Q hQ hrel ha _ _ he
    exact ⟨k, Prod.ext (by omega) (by omega)⟩
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_ofNat]
    linear_combination 2 * (k : ℝ) * hrel.symm

def parityCombination (w₀ w₁ : ZMod 2) : (ℤ × ℤ) →+ ZMod 2 where
  toFun z := (z.1 : ZMod 2) * w₀ + (z.2 : ZMod 2) * w₁
  map_zero' := by simp
  map_add' z w := by
    change ((z.1 + w.1 : ℤ) : ZMod 2) * w₀ + ((z.2 + w.2 : ℤ) : ZMod 2) * w₁ = _
    push_cast
    ring

theorem angleCombination_ker_le_parity {a b : ℝ} (P Q : ℤ) (hQ : Q ≠ 0)
    (hrel : (P : ℝ) * a + (Q : ℝ) * b = Real.pi) (ha : Irrational (a / Real.pi))
    (w₀ w₁ : ZMod 2) : (angleCombination a b).ker ≤ (parityCombination w₀ w₁).ker := by
  intro z hz
  obtain ⟨k, rfl⟩ := (angleCombination_eq_zero_iff P Q hQ hrel ha z).mp hz
  change (((2 * k * P : ℤ) : ZMod 2) * w₀ + ((2 * k * Q : ℤ) : ZMod 2) * w₁) = 0
  have htwo : (2 : ZMod 2) = 0 := by decide
  simp only [Int.cast_mul, Int.cast_ofNat]
  rw [htwo]
  simp

end Erdos633b
