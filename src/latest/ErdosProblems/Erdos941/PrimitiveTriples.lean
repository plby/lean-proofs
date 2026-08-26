import ErdosProblems.Erdos941.Spheres
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Squarefree

/-! # Primitive integral triples -/

namespace Erdos941

def PrimitiveTriple (v : Triple) : Prop :=
  ∃ a b c : ℤ, a * v.1 + b * v.2.1 + c * v.2.2 = 1

theorem PrimitiveTriple.ne_zero {v : Triple} (hv : PrimitiveTriple v) : v ≠ 0 := by
  rintro rfl
  obtain ⟨a, b, c, h⟩ := hv
  norm_num at h

theorem primitiveTriple_of_squarefree_norm {v : Triple} {n : ℕ}
    (hv : tripleNorm v = n) (hn : Squarefree n) : PrimitiveTriple v := by
  let h : ℤ := Int.gcd v.2.1 v.2.2
  let g : ℕ := Int.gcd v.1 h
  have hA : (g : ℤ) ∣ v.1 := Int.gcd_dvd_left _ _
  have hh : (g : ℤ) ∣ h := Int.gcd_dvd_right _ _
  have hB : (g : ℤ) ∣ v.2.1 := dvd_trans hh (Int.gcd_dvd_left _ _)
  have hC : (g : ℤ) ∣ v.2.2 := dvd_trans hh (Int.gcd_dvd_right _ _)
  have hnorm : (g : ℤ) * g ∣ (n : ℤ) := by
    rw [← hv]
    dsimp [tripleNorm, norm3]
    simp only [pow_two]
    exact dvd_add (dvd_add (mul_dvd_mul hA hA) (mul_dvd_mul hB hB)) (mul_dvd_mul hC hC)
  have hg : g = 1 := Nat.isUnit_iff.mp (hn g (by exact_mod_cast hnorm))
  have h₁ := Int.gcd_eq_gcd_ab v.1 h
  have h₂ := Int.gcd_eq_gcd_ab v.2.1 v.2.2
  change (g : ℤ) = _ at h₁
  change h = _ at h₂
  rw [hg, Nat.cast_one] at h₁
  refine ⟨Int.gcdA v.1 h, Int.gcdA v.2.1 v.2.2 * Int.gcdB v.1 h,
    Int.gcdB v.2.1 v.2.2 * Int.gcdB v.1 h, ?_⟩
  linear_combination -h₁ - (Int.gcdB v.1 h) * h₂

end Erdos941
