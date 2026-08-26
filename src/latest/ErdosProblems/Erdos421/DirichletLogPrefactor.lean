import ErdosProblems.Erdos421.DirichletMomentParameters

/-! # Logarithmic control of the explicit Halász prefactor -/

namespace Erdos421

noncomputable def dirichletDyadicLogConstant (k : ℕ) : ℝ := 2 * k / Real.log 2 + 1

noncomputable def dirichletMomentConstant (k : ℕ) : ℝ :=
  (2 : ℝ) ^ k * (2 * k + 1) ^ (k ^ 2)

noncomputable def dirichletHalaszPrefactorConstant (k : ℕ) : ℝ :=
  10240 * dirichletDyadicLogConstant k * 2 ^ (k + 1) * (3 + 2 * k)

theorem dirichletDyadicLogConstant_pos (k : ℕ) : 0 < dirichletDyadicLogConstant k := by
  unfold dirichletDyadicLogConstant
  positivity

theorem dirichletMomentConstant_pos (k : ℕ) : 0 < dirichletMomentConstant k := by
  unfold dirichletMomentConstant
  positivity

theorem dirichletHalaszPrefactorConstant_pos (k : ℕ) :
    0 < dirichletHalaszPrefactorConstant k := by
  have := dirichletDyadicLogConstant_pos k
  unfold dirichletHalaszPrefactorConstant
  positivity

theorem dirichletDyadic_power_ambient {M U : ℕ} (hU : 1 ≤ U) (hUM : U ≤ 2 * M) (k : ℕ) :
    ((2 ^ dirichletDyadicExponent U k : ℕ) : ℝ) ≤ (2 : ℝ) ^ (k + 1) * (M : ℝ) ^ k := by
  have hp := dirichletDyadicExponent_power_le hU k
  have hu := Nat.pow_le_pow_left hUM k
  have hb : 2 ^ dirichletDyadicExponent U k ≤ 2 ^ (k + 1) * M ^ k := by
    calc
      _ ≤ 2 * U ^ k := hp
      _ ≤ 2 * (2 * M) ^ k := Nat.mul_le_mul_left 2 hu
      _ = _ := by rw [mul_pow, pow_succ]; ring
  exact_mod_cast hb

theorem dirichletDyadic_log_ambient {X M U : ℕ} (hX : 2 ≤ X) (hU : 1 ≤ U)
    (hMX : M ≤ X) (hUM : U ≤ 2 * M) (hlog : 1 ≤ Real.log X) (k : ℕ) :
    Real.log ((2 ^ dirichletDyadicExponent U k : ℕ) + 2 : ℝ) ≤
      (3 + 2 * k) * Real.log X := by
  have hUp : (0 : ℝ) < U := by exact_mod_cast (show 0 < U by omega)
  have hp := dirichletDyadicExponent_power_le hU k
  have hUk : 1 ≤ U ^ k := one_le_pow₀ hU
  have hnum : ((2 ^ dirichletDyadicExponent U k : ℕ) : ℝ) + 2 ≤ 4 * (U : ℝ) ^ k := by
    have hp' : ((2 ^ dirichletDyadicExponent U k : ℕ) : ℝ) ≤ 2 * (U : ℝ) ^ k := by
      exact_mod_cast hp
    have hUk' : (1 : ℝ) ≤ (U : ℝ) ^ k := by exact_mod_cast hUk
    linarith
  have hpositive : (0 : ℝ) < (2 ^ dirichletDyadicExponent U k : ℕ) + 2 := by positivity
  have hb := Real.log_le_log hpositive hnum
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (pow_pos hUp _).ne', Real.log_pow] at hb
  have hfour : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hlength := dirichlet_log_length_le hX hU hMX hUM
  have hm := mul_le_mul_of_nonneg_left hlength (Nat.cast_nonneg k)
  nlinarith

theorem dirichletHalasz_prefactor_ambient {X M U : ℕ} (hX : 2 ≤ X) (hU : 1 ≤ U)
    (hMX : M ≤ X) (hUM : U ≤ 2 * M) (hlog : 1 ≤ Real.log X) (k : ℕ) :
    10240 * dirichletDyadicExponent U k * (2 ^ dirichletDyadicExponent U k : ℕ) *
      Real.log ((2 ^ dirichletDyadicExponent U k : ℕ) + 2 : ℝ) ≤
        (dirichletHalaszPrefactorConstant k * (Real.log X) ^ 2) * (M : ℝ) ^ k := by
  have hK := dirichletDyadicExponent_le_log hX hU hMX hUM hlog k
  have hpower := dirichletDyadic_power_ambient hU hUM k
  have hL := dirichletDyadic_log_ambient hX hU hMX hUM hlog k
  have hlognonneg : 0 ≤ Real.log ((2 ^ dirichletDyadicExponent U k : ℕ) + 2 : ℝ) := by
    apply Real.log_nonneg
    have := Nat.cast_nonneg (2 ^ dirichletDyadicExponent U k) (α := ℝ)
    linarith
  have hbound : 10240 * dirichletDyadicExponent U k * (2 ^ dirichletDyadicExponent U k : ℕ) *
      Real.log ((2 ^ dirichletDyadicExponent U k : ℕ) + 2 : ℝ) ≤
      10240 * ((2 * k / Real.log 2 + 1) * Real.log X) *
        ((2 : ℝ) ^ (k + 1) * (M : ℝ) ^ k) * ((3 + 2 * k) * Real.log X) := by
    gcongr
  apply hbound.trans_eq
  unfold dirichletHalaszPrefactorConstant dirichletDyadicLogConstant
  ring

end Erdos421
