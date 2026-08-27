import Mathlib

/-!
# Square-root cutoff iteration

Using the integer square-root cutoff makes the prime-error estimate a
finite induction. Its logarithm lies between one quarter and one half
of the original logarithm, already for cutoffs at least four.
-/

namespace Erdos587

lemma delta_sqrt_cutoff_bounds {x : ℕ} (hx : 4 ≤ x) :
    2 ≤ x.sqrt ∧ x.sqrt < x := by
  refine ⟨Nat.le_sqrt.mpr hx, Nat.sqrt_lt_self (by omega)⟩

lemma delta_sqrt_cutoff_log_bounds {x : ℕ} (hx : 4 ≤ x) :
    Real.log (x : ℝ) ≤ 4 * Real.log (x.sqrt : ℝ) ∧
      2 * Real.log (x.sqrt : ℝ) ≤ Real.log (x : ℝ) := by
  have hy : 2 ≤ x.sqrt := (delta_sqrt_cutoff_bounds hx).1
  have hyR : (0 : ℝ) < x.sqrt := by exact_mod_cast (show 0 < x.sqrt by omega)
  have hxR : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hsmall : x.sqrt + 1 ≤ x.sqrt ^ 2 := by nlinarith
  have hfour : x ≤ x.sqrt ^ 4 := by
    have hp := Nat.pow_le_pow_left hsmall 2
    have hx' := Nat.lt_succ_sqrt' x
    have heq : (x.sqrt ^ 2) ^ 2 = x.sqrt ^ 4 := by rw [← pow_mul]
    rw [heq] at hp
    exact hx'.le.trans hp
  have hlo := Real.log_le_log hxR (show (x : ℝ) ≤ (x.sqrt : ℝ) ^ 4 by exact_mod_cast hfour)
  have hhi := Real.log_le_log (pow_pos hyR 2)
    (show (x.sqrt : ℝ) ^ 2 ≤ x by exact_mod_cast Nat.sqrt_le' x)
  rw [Real.log_pow] at hlo hhi
  norm_num at hlo hhi
  exact ⟨hlo, hhi⟩

/-- A logarithmic high-block error sums geometrically under the integer
square-root cutoff. Only the two initial cutoffs need a separate bound. -/
theorem delta_sqrt_recursion_log_bound (F : ℕ → ℝ) {C K : ℝ}
    (hC : 0 ≤ C) (hKC : 2 * K ≤ C)
    (hbase : ∀ x : ℕ, 2 ≤ x → x ≤ 3 → F x ≤ C * Real.log (x : ℝ))
    (hstep : ∀ x : ℕ, 4 ≤ x → F x ≤ F x.sqrt + K * Real.log (x : ℝ))
    (x : ℕ) (hx : 2 ≤ x) : F x ≤ C * Real.log (x : ℝ) := by
  induction x using Nat.strong_induction_on with
  | h x ih =>
    by_cases hx3 : x ≤ 3
    · exact hbase x hx hx3
    · have hx4 : 4 ≤ x := by omega
      obtain ⟨hy, hyx⟩ := delta_sqrt_cutoff_bounds hx4
      have hprevious := ih x.sqrt hyx hy
      have hhalf := mul_le_mul_of_nonneg_left (delta_sqrt_cutoff_log_bounds hx4).2 hC
      have hlog : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
      have hcost := mul_le_mul_of_nonneg_right hKC hlog
      have hnext := hstep x hx4
      linarith

/-- The same iteration with hypotheses only up to a fixed ambient cutoff. -/
theorem delta_sqrt_recursion_log_bound_upto (F : ℕ → ℝ) {C K : ℝ} {X : ℕ}
    (hC : 0 ≤ C) (hKC : 2 * K ≤ C)
    (hbase : ∀ x : ℕ, 2 ≤ x → x ≤ 3 → x ≤ X → F x ≤ C * Real.log (x : ℝ))
    (hstep : ∀ x : ℕ, 4 ≤ x → x ≤ X → F x ≤ F x.sqrt + K * Real.log (x : ℝ))
    (x : ℕ) (hx : 2 ≤ x) (hxX : x ≤ X) : F x ≤ C * Real.log (x : ℝ) := by
  induction x using Nat.strong_induction_on with
  | h x ih =>
    by_cases hx3 : x ≤ 3
    · exact hbase x hx hx3 hxX
    · have hx4 : 4 ≤ x := by omega
      obtain ⟨hy, hyx⟩ := delta_sqrt_cutoff_bounds hx4
      have hprevious := ih x.sqrt hyx hy (hyx.le.trans hxX)
      have hhalf := mul_le_mul_of_nonneg_left (delta_sqrt_cutoff_log_bounds hx4).2 hC
      have hlog : 0 ≤ Real.log (x : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
      have hcost := mul_le_mul_of_nonneg_right hKC hlog
      have hnext := hstep x hx4 hxX
      linarith

end Erdos587
