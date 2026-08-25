import Util.Bernays.LocalParity

/-!
# Exact Euler factors of the local norm indicator
-/

open Filter Topology Real
open scoped Classical

namespace Bernays

theorem tsum_even_geometric {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1) :
    (∑' k : ℕ, if Even k then r ^ k else 0) = (1 - r ^ 2)⁻¹ := by
  have hr₂ : r ^ 2 < 1 := by nlinarith
  have he (k : ℕ) : (if Even (2 * k) then r ^ (2 * k) else 0) = (r ^ 2) ^ k := by
    rw [if_pos (show Even (2 * k) from ⟨k, by omega⟩), pow_mul]
  have ho (k : ℕ) : (if Even (2 * k + 1) then r ^ (2 * k + 1) else 0) = 0 := by
    apply if_neg
    rintro ⟨j, hj⟩
    omega
  have heS : Summable (fun k : ℕ => if Even (2 * k) then r ^ (2 * k) else 0) := by
    simpa only [he] using summable_geometric_of_lt_one (sq_nonneg r) hr₂
  have hoS : Summable (fun k : ℕ => if Even (2 * k + 1) then r ^ (2 * k + 1) else 0) := by
    simp only [ho]
    exact summable_zero
  have hsum := tsum_even_add_odd (f := fun k : ℕ => if Even k then r ^ k else 0) heS hoS
  simpa only [he, ho, tsum_zero, add_zero, tsum_geometric_of_lt_one (sq_nonneg r) hr₂] using hsum.symm

theorem localDirichletTerm_prime_pow (S : ℕ → Prop) {p : ℕ} (hp : p.Prime)
    (s : ℝ) (k : ℕ) :
    localDirichletTerm S s (p ^ k) =
      (if S p ∧ Odd k then 0 else 1) * (((p : ℝ) ^ s)⁻¹) ^ k := by
  rw [localDirichletTerm, localParity_prime_pow S hp, Nat.cast_pow,
    ← rpow_natCast_mul (Nat.cast_nonneg p), mul_comm (k : ℝ) s,
    rpow_mul_natCast (Nat.cast_nonneg p), div_eq_mul_inv, inv_pow]

theorem localDirichletTerm_eulerFactor (S : ℕ → Prop) {p : ℕ} (hp : p.Prime)
    {s : ℝ} (hs : 0 < s) :
    (∑' k : ℕ, localDirichletTerm S s (p ^ k)) =
      if S p then (1 - (((p : ℝ) ^ s)⁻¹) ^ 2)⁻¹ else (1 - ((p : ℝ) ^ s)⁻¹)⁻¹ := by
  classical
  have hpR : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hr₀ : 0 ≤ ((p : ℝ) ^ s)⁻¹ := inv_nonneg.mpr (rpow_nonneg (Nat.cast_nonneg p) s)
  have hr₁ : ((p : ℝ) ^ s)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_rpow hpR hs)
  simp_rw [localDirichletTerm_prime_pow S hp s]
  by_cases hS : S p
  · rw [if_pos hS]
    have heq (k : ℕ) :
        (if S p ∧ Odd k then (0 : ℝ) else 1) * (((p : ℝ) ^ s)⁻¹) ^ k =
          if Even k then (((p : ℝ) ^ s)⁻¹) ^ k else 0 := by
      by_cases hk : Even k
      · simp [hS, hk, Nat.not_odd_iff_even.mpr hk]
      · simp [hS, hk, Nat.not_even_iff_odd.mp hk]
    simp_rw [heq]
    exact tsum_even_geometric hr₀ hr₁
  · simp only [hS, false_and, if_false, one_mul]
    exact tsum_geometric_of_lt_one hr₀ hr₁

theorem localParity_explicitEulerProduct (S : ℕ → Prop) {s : ℝ} (hs : 1 < s) :
    HasProd (fun p : Nat.Primes =>
        if S p then (1 - ((((p : ℕ) : ℝ) ^ s)⁻¹) ^ 2)⁻¹
        else (1 - (((p : ℕ) : ℝ) ^ s)⁻¹)⁻¹)
      (realDirichlet (localParity S) s) := by
  convert localParity_eulerProduct S hs using 1
  ext p
  exact (localDirichletTerm_eulerFactor S p.property (zero_lt_one.trans hs)).symm

end Bernays
