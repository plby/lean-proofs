/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
A uniform finite-field point count for the affine diagonal sextic.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.SurfaceFourier

namespace Erdos477.Counting

open scoped BigOperators

lemma norm_sextic_fourier_term_le (p : ℕ) [Fact p.Prime] (c t : ZMod p) (ht : t ≠ 0) :
    ‖ZMod.stdAddChar (-t * c) * sexticSum p t ^ 2 * sexticSum p (-t)‖ ≤
      (7 * Real.sqrt p) ^ 3 := by
  have hphase : ‖ZMod.stdAddChar (-t * c)‖ = 1 := by
    rw [ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  rw [norm_mul, norm_mul, norm_pow, hphase, one_mul]
  calc
    _ ≤ (7 * Real.sqrt p) ^ 2 * (7 * Real.sqrt p) := by
      gcongr
      · exact norm_sexticSum_le p t ht
      · exact norm_sexticSum_le p (-t) (neg_ne_zero.mpr ht)
    _ = _ := by ring

/-- The number of affine sextic surface points is `p^2 + O(p^(3/2))`,
with an explicit coefficient-independent constant. No algebraic-geometric
point-count theorem is assumed. -/
theorem sexticResidues_card_error (p : ℕ) [Fact p.Prime] (c : ℤ) :
    |((sexticResidues p c).card : ℝ) - (p : ℝ) ^ 2| ≤ 343 * p * Real.sqrt p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hnorm : ‖(p : ℂ) * (sexticResidues p c).card - (p : ℂ) ^ 3‖ =
      (p : ℝ) * |((sexticResidues p c).card : ℝ) - (p : ℝ) ^ 2| := by
    have heq : (p : ℂ) * (sexticResidues p c).card - (p : ℂ) ^ 3 =
        ((p : ℝ) * (((sexticResidues p c).card : ℝ) - (p : ℝ) ^ 2) : ℝ) := by
      push_cast
      ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hp]
  have hbound : (p : ℝ) * |((sexticResidues p c).card : ℝ) - (p : ℝ) ^ 2| ≤
      (p : ℝ) * (7 * Real.sqrt p) ^ 3 := by
    rw [← hnorm, sextic_fourier_error]
    calc
      _ ≤ ∑ t ∈ Finset.univ.erase (0 : ZMod p),
          ‖ZMod.stdAddChar (-t * (c : ZMod p)) * sexticSum p t ^ 2 * sexticSum p (-t)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _t ∈ Finset.univ.erase (0 : ZMod p), (7 * Real.sqrt p) ^ 3 := by
        apply Finset.sum_le_sum
        intro t ht
        exact norm_sextic_fourier_term_le p c t (Finset.mem_erase.mp ht).1
      _ ≤ (p : ℝ) * (7 * Real.sqrt p) ^ 3 := by
        rw [Finset.sum_const, nsmul_eq_mul]
        gcongr
        have h := Finset.card_le_card (Finset.erase_subset (0 : ZMod p) Finset.univ)
        simpa only [Finset.card_univ, ZMod.card] using h
  have hroot : (Real.sqrt (p : ℝ)) ^ 2 = p := Real.sq_sqrt hp.le
  have hcub : (7 * Real.sqrt (p : ℝ)) ^ 3 = 343 * p * Real.sqrt p := by
    calc
      _ = 343 * (Real.sqrt (p : ℝ)) ^ 2 * Real.sqrt p := by ring
      _ = _ := by rw [hroot]
  rw [hcub] at hbound
  exact (mul_le_mul_iff_right₀ hp).mp hbound

theorem sexticResidues_card_upper (p : ℕ) [Fact p.Prime] (c : ℤ) :
    ((sexticResidues p c).card : ℝ) ≤ (p : ℝ) ^ 2 + 343 * p * Real.sqrt p := by
  have h := (abs_le.mp (sexticResidues_card_error p c)).2
  linarith

#print axioms sexticResidues_card_error
-- 'Erdos477.Counting.sexticResidues_card_error' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
