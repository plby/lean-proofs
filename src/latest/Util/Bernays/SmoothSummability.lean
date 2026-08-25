import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# Summability of reciprocal square roots on a fixed finite prime support
-/

namespace Bernays

theorem sqrt_nat_pow (p k : ℕ) : Real.sqrt ((p ^ k : ℕ) : ℝ) = Real.sqrt (p : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), ih, pow_succ]

theorem summable_factored_inv_sqrt (P : Finset ℕ) :
    Summable (fun m : Nat.factoredNumbers P => 1 / Real.sqrt (m.val : ℝ)) := by
  let f : ℕ → ℝ := fun n => 1 / Real.sqrt (n : ℝ)
  have hf₁ : f 1 = 1 := by simp [f]
  have hmul {m n : ℕ} (_ : m.Coprime n) : f (m * n) = f m * f n := by
    simp only [f, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), one_div, mul_inv]
  have hsum {p : ℕ} (hp : p.Prime) : Summable (fun k : ℕ => ‖f (p ^ k)‖) := by
    have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hs : 1 < Real.sqrt (p : ℝ) := by
      simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hpR
    have hr : 1 / Real.sqrt (p : ℝ) < 1 := (div_lt_one (by positivity)).mpr hs
    have hg := summable_geometric_of_lt_one (by positivity : 0 ≤ 1 / Real.sqrt (p : ℝ)) hr
    have hge : Summable (fun k : ℕ => f (p ^ k)) := by
      simpa only [f, sqrt_nat_pow, one_div, inv_pow] using hg
    apply hge.congr
    intro k
    exact (Real.norm_of_nonneg (by dsimp only [f]; positivity)).symm
  have h := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum hf₁
    (fun h => hmul h) (fun hp => hsum hp) P).1
  exact h.of_norm

end Bernays
