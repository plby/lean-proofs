import ErdosProblems.Erdos394.PrimeSubset

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Euler bounds for the quadratic corner and constant lattice errors
-/

open Nat Finset

namespace Erdos394

/-- Euler product arising from the `D/L²` corner term after the three-state
sum. -/
noncomputable def nonRationalCornerEuler (P : Finset ℕ) (c z : ℕ) : ℝ :=
  ∏ p ∈ P,
    (1 + (c : ℝ) / ((p - 1 : ℕ) : ℝ) +
      (c : ℝ) * (p : ℝ) /
        (((z * z : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ)))

/-- Euler product arising from the `+1` term in every lattice discrepancy. -/
noncomputable def pairStateConstantEuler (P : Finset ℕ) (c : ℕ) : ℝ :=
  ∏ p ∈ P, (1 + 2 * (c : ℝ) / ((p - 1 : ℕ) : ℝ))

/-- If `z²≤p`, the corner product is bounded by the uniform correction
`(1+4c/z²)^|P|`. -/
theorem nonRationalCornerEuler_le (P : Finset ℕ) (c z : ℕ)
    (hz : 1 ≤ z) (hprime : ∀ p ∈ P, p.Prime)
    (hzp : ∀ p ∈ P, z * z ≤ p) :
    nonRationalCornerEuler P c z ≤
      ∏ _p ∈ P, (1 + 4 * (c : ℝ) / ((z * z : ℕ) : ℝ)) := by
  have hzz : (0 : ℝ) < (z * z : ℕ) := by positivity
  unfold nonRationalCornerEuler
  apply Finset.prod_le_prod
  · intro p hp
    positivity
  · intro p hp
    have hp2 : 2 ≤ p := (hprime p hp).two_le
    have hp1nat : 0 < p - 1 := by omega
    have hp1 : (0 : ℝ) < (p - 1 : ℕ) := by exact_mod_cast hp1nat
    have hzpR : ((z * z : ℕ) : ℝ) ≤ p := by exact_mod_cast hzp p hp
    have hp_le : (p : ℝ) ≤ 2 * ((p - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (hprime p hp).one_le]
      norm_num only [Nat.cast_one]
      have hp2R : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      nlinarith
    have hfirst : (1 : ℝ) / ((p - 1 : ℕ) : ℝ) ≤
        2 / ((z * z : ℕ) : ℝ) := by
      apply (div_le_div_iff₀ hp1 hzz).mpr
      nlinarith
    have hsecond : (p : ℝ) /
          (((z * z : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ)) ≤
        2 / ((z * z : ℕ) : ℝ) := by
      apply (div_le_iff₀ (mul_pos hzz hp1)).mpr
      calc
        (p : ℝ) ≤ 2 * ((p - 1 : ℕ) : ℝ) := hp_le
        _ = (2 / ((z * z : ℕ) : ℝ)) *
              (((z * z : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ)) := by
          field_simp
    have hc : (0 : ℝ) ≤ c := by positivity
    calc
      1 + (c : ℝ) / ((p - 1 : ℕ) : ℝ) +
          (c : ℝ) * (p : ℝ) /
            (((z * z : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ)) =
        1 + (c : ℝ) * (1 / ((p - 1 : ℕ) : ℝ)) +
          (c : ℝ) * ((p : ℝ) /
            (((z * z : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ))) := by ring
      _ ≤ 1 + (c : ℝ) * (2 / ((z * z : ℕ) : ℝ)) +
          (c : ℝ) * (2 / ((z * z : ℕ) : ℝ)) := by gcongr
      _ = 1 + 4 * (c : ℝ) / ((z * z : ℕ) : ℝ) := by ring

/-- Under the same prime-size condition, the constant-error product obeys the
same correction bound. -/
theorem pairStateConstantEuler_le (P : Finset ℕ) (c z : ℕ)
    (hz : 1 ≤ z) (hprime : ∀ p ∈ P, p.Prime)
    (hzp : ∀ p ∈ P, z * z ≤ p) :
    pairStateConstantEuler P c ≤
      ∏ _p ∈ P, (1 + 4 * (c : ℝ) / ((z * z : ℕ) : ℝ)) := by
  have hzz : (0 : ℝ) < (z * z : ℕ) := by positivity
  unfold pairStateConstantEuler
  apply Finset.prod_le_prod
  · intro p hp
    positivity
  · intro p hp
    have hp2 : 2 ≤ p := (hprime p hp).two_le
    have hp1 : (0 : ℝ) < (p - 1 : ℕ) := by exact_mod_cast (by omega : 0 < p - 1)
    have hzpR : ((z * z : ℕ) : ℝ) ≤ p := by exact_mod_cast hzp p hp
    have hrecip : (1 : ℝ) / ((p - 1 : ℕ) : ℝ) ≤
        2 / ((z * z : ℕ) : ℝ) := by
      apply (div_le_div_iff₀ hp1 hzz).mpr
      have hpcast : (p : ℝ) ≤ 2 * ((p - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub (hprime p hp).one_le]
        norm_num only [Nat.cast_one]
        have hp2R : (2 : ℝ) ≤ p := by exact_mod_cast hp2
        nlinarith
      nlinarith
    have hc : (0 : ℝ) ≤ c := by positivity
    calc
      1 + 2 * (c : ℝ) / ((p - 1 : ℕ) : ℝ) =
          1 + 2 * (c : ℝ) * (1 / ((p - 1 : ℕ) : ℝ)) := by ring
      _ ≤ 1 + 2 * (c : ℝ) * (2 / ((z * z : ℕ) : ℝ)) := by gcongr
      _ = 1 + 4 * (c : ℝ) / ((z * z : ℕ) : ℝ) := by ring

end Erdos394
