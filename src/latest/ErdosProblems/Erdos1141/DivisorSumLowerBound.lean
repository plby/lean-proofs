import ErdosProblems.Erdos1141.DivisorComparisonAsymptotics

/-!
# Uniform lower bounds for the quadratic divisor sum
-/

namespace Pollack17

open Filter
open scoped BigOperators

theorem one_le_principal_divisorCoefficient {m n : ℕ} (hn : 0 < n) :
    1 ≤ divisorCoefficient (1 : DirichletCharacter ℂ m) n := by
  rw [divisorCoefficient_eq_sum]
  have hnonneg (d : ℕ) : 0 ≤ ((1 : DirichletCharacter ℂ m) (d : ℕ)).re := by
    by_cases hd : IsUnit (d : ZMod m)
    · rw [MulChar.one_apply hd, Complex.one_re]
      norm_num
    · rw [MulChar.map_nonunit _ hd, Complex.zero_re]
  have h := Finset.single_le_sum (fun d _ => hnonneg d)
    (show 1 ∈ n.divisors from Nat.one_mem_divisors.mpr hn.ne')
  simpa only [Nat.cast_one, map_one, Complex.one_re] using h

theorem principal_divisor_sum_lower (m X : ℕ) :
    (X : ℝ) ≤ ∑ n ∈ Finset.Icc 1 X, divisorCoefficient (1 : DirichletCharacter ℂ m) n := by
  calc
    _ = ∑ _n ∈ Finset.Icc 1 X, (1 : ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum fun n hn =>
      one_le_principal_divisorCoefficient (Finset.mem_Icc.mp hn).1

theorem eventually_divisor_sum_lower_bound {c δ : ℝ} (hc : 1 / 4 < c) (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, ∀ (χ : DirichletCharacter ℂ m), χ.IsQuadratic →
      (m : ℝ) ^ (c - δ) ≤ ∑ n ∈ Finset.Icc 1 ⌊(m : ℝ) ^ c⌋₊, divisorCoefficient χ n := by
  have hc0 : 0 < c := by linarith
  obtain ⟨τ, hτ, hcomp⟩ := eventually_divisor_sum_asymptotic hc
  let u : ℝ := min δ τ / 4
  have hu : 0 < u := by dsimp [u]; positivity
  have huδ : u < δ := by
    have h := min_le_left δ τ
    dsimp [u] at hu ⊢
    linarith
  have huτ : u < τ := by
    have h := min_le_right δ τ
    dsimp [u] at hu ⊢
    linarith
  have herr := Burgess.eventually_const_mul_rpow_le (C := 1) (d := 1 / 4)
    (a := c - τ) (b := c - u) (by norm_num) (by linarith)
  have htarget := Burgess.eventually_const_mul_rpow_le (C := 1) (d := 1 / 4)
    (a := c - δ) (b := c - u) (by norm_num) (by linarith)
  have hprincipal := Burgess.eventually_const_mul_rpow_le (C := 1) (d := 1 / 2)
    (a := c - δ) (b := c) (by norm_num) (by linarith)
  filter_upwards [hcomp, eventually_quadratic_LFunction_one_re_ge_rpow hu,
    herr, htarget, hprincipal, Burgess.eventually_floor_rpow_bounds hc0, eventually_ge_atTop 1]
    with m hcomp hL herr htarget hprincipal hfloor hm1
  intro χ hχ
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm1
  have : NeZero m := ⟨by omega⟩
  by_cases hχ1 : χ = 1
  · rw [hχ1]
    have htarget' : (m : ℝ) ^ (c - δ) ≤ (m : ℝ) ^ c / 2 := by
      nlinarith only [hprincipal]
    exact (htarget'.trans hfloor.1).trans (principal_divisor_sum_lower m _)
  · have hLv := hL χ hχ1 hχ
    have hmain : (1 / 2 : ℝ) * (m : ℝ) ^ (c - u) ≤
        (⌊(m : ℝ) ^ c⌋₊ : ℝ) * (DirichletCharacter.LFunction χ 1).re := by
      calc
        _ = ((m : ℝ) ^ c / 2) * (m : ℝ) ^ (-u) := by
          rw [sub_eq_add_neg, Real.rpow_add hm0]
          ring
        _ ≤ _ := mul_le_mul hfloor.1 hLv (Real.rpow_nonneg hm0.le _) (Nat.cast_nonneg _)
    have herror := (abs_le.mp (hcomp χ hχ hχ1)).1
    have herr' : (m : ℝ) ^ (c - τ) ≤ (1 / 4 : ℝ) * (m : ℝ) ^ (c - u) := by
      simpa only [one_mul] using herr
    have htarget' : (m : ℝ) ^ (c - δ) ≤ (1 / 4 : ℝ) * (m : ℝ) ^ (c - u) := by
      simpa only [one_mul] using htarget
    linarith only [hmain, herror, herr', htarget']

end Pollack17
