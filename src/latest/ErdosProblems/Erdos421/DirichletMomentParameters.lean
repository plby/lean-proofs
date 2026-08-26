import ErdosProblems.Erdos421.VerticalDirichletLargeValues
import ErdosProblems.Erdos421.ProperPrimePowers
import ErdosProblems.Erdos421.UnsmoothingParameters

/-! # Explicit dyadic and coefficient-energy parameters for higher large values -/

namespace Erdos421

def dirichletDyadicExponent (U k : ℕ) : ℕ := Nat.log 2 (U ^ k) + 1

theorem dirichletDyadicExponent_pos (U k : ℕ) : 0 < dirichletDyadicExponent U k := by
  unfold dirichletDyadicExponent
  omega

theorem dirichletDyadicExponent_support (U k : ℕ) : U ^ k < 2 ^ dirichletDyadicExponent U k :=
  Nat.lt_pow_succ_log_self (by omega) _

theorem dirichletDyadicExponent_power_le {U : ℕ} (hU : 1 ≤ U) (k : ℕ) :
    2 ^ dirichletDyadicExponent U k ≤ 2 * U ^ k := by
  have hp : U ^ k ≠ 0 := (pow_pos (by omega : 0 < U) _).ne'
  have h := Nat.pow_log_le_self 2 hp
  simpa only [dirichletDyadicExponent, pow_succ, mul_comm] using Nat.mul_le_mul_left 2 h

theorem dirichlet_log_length_le {X M U : ℕ} (hX : 2 ≤ X) (hU : 1 ≤ U)
    (hMX : M ≤ X) (hUM : U ≤ 2 * M) : Real.log U ≤ 2 * Real.log X := by
  have hXp : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hUp : (0 : ℝ) < U := by exact_mod_cast (show 0 < U by omega)
  have hb := Real.log_le_log hUp (by exact_mod_cast
    (show U ≤ 2 * X by omega) : (U : ℝ) ≤ 2 * X)
  apply hb.trans
  simpa only [two_mul] using
    (unsmoothing_log_bounds (by exact_mod_cast hX) hXp.le le_rfl).2

theorem dirichletDyadicExponent_le_log {X M U : ℕ} (hX : 2 ≤ X) (hU : 1 ≤ U)
    (hMX : M ≤ X) (hUM : U ≤ 2 * M) (hlog : 1 ≤ Real.log X) (k : ℕ) :
    (dirichletDyadicExponent U k : ℝ) ≤ (2 * k / Real.log 2 + 1) * Real.log X := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb : (Nat.log 2 (U ^ k) : ℝ) ≤ k * Real.log U / Real.log 2 := by
    simpa only [Real.logb, Nat.cast_ofNat, Nat.cast_pow, Real.log_pow] using
      Real.natLog_le_logb (U ^ k) 2
  have hL := dirichlet_log_length_le hX hU hMX hUM
  have hm := mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg k)
  have hd := div_le_div_of_nonneg_right hm hlog2.le
  simp only [dirichletDyadicExponent, Nat.cast_add, Nat.cast_one]
  simp only [div_eq_mul_inv] at hb hd ⊢
  nlinarith

theorem dirichletMomentEnergy_dyadic_bound {M U : ℕ} (hM : 1 ≤ M) (hU : 1 ≤ U)
    (hUM : U ≤ 2 * M) (k : ℕ) :
    dirichletMomentEnergy M U k ≤
      (2 : ℝ) ^ k * ((M : ℝ)⁻¹) ^ k * (1 + k * Real.log (2 * M : ℕ)) ^ (k ^ 2) := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hUp : (0 : ℝ) < U := by exact_mod_cast (show 0 < U by omega)
  have hUr : (U : ℝ) ≤ 2 * M := by exact_mod_cast hUM
  have hsize : ((M : ℝ)⁻¹) ^ (2 * k) * (U ^ k : ℕ) ≤
      (2 : ℝ) ^ k * ((M : ℝ)⁻¹) ^ k := by
    have hu := pow_le_pow_left₀ hUp.le hUr k
    calc
      _ ≤ ((M : ℝ)⁻¹) ^ (2 * k) * (2 * M) ^ k :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hu) (by positivity)
      _ = _ := by
        rw [show 2 * k = k + k by omega, pow_add, mul_pow]
        have he : ((M : ℝ)⁻¹) ^ k * (M : ℝ) ^ k = 1 := by
          rw [← mul_pow, inv_mul_cancel₀ hMp.ne', one_pow]
        calc
          _ = (2 : ℝ) ^ k * ((M : ℝ)⁻¹) ^ k *
              (((M : ℝ)⁻¹) ^ k * (M : ℝ) ^ k) := by ring
          _ = _ := by rw [he, mul_one]
  have hlength : Real.log (U ^ k : ℕ) ≤ k * Real.log (2 * M : ℕ) := by
    rw [Nat.cast_pow, Real.log_pow]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg k)
    exact Real.log_le_log hUp (by exact_mod_cast hUM)
  exact mul_le_mul hsize
    (pow_le_pow_left₀ (by positivity) (add_le_add le_rfl hlength) (k ^ 2))
    (by positivity) (by positivity)

theorem dirichletMomentEnergy_ambient_bound {X M U : ℕ} (hX : 2 ≤ X) (hM : 1 ≤ M)
    (hU : 1 ≤ U) (hMX : M ≤ X) (hUM : U ≤ 2 * M) (hlog : 1 ≤ Real.log X) (k : ℕ) :
    dirichletMomentEnergy M U k ≤
      ((2 : ℝ) ^ k * (2 * k + 1) ^ (k ^ 2)) * (Real.log X) ^ (k ^ 2) / (M : ℝ) ^ k := by
  have hL := dirichlet_log_length_le hX (by omega : 1 ≤ 2 * M) hMX le_rfl
  have hm := mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg k)
  have hlinear : 1 + k * Real.log (2 * M : ℕ) ≤ (2 * k + 1) * Real.log X := by nlinarith
  have hb := dirichletMomentEnergy_dyadic_bound hM hU hUM k
  apply (hb.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) hlinear (k ^ 2)) (by positivity))).trans_eq
  rw [mul_pow]
  simp only [div_eq_mul_inv, inv_pow]
  ring

end Erdos421
