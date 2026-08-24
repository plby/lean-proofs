import ErdosProblems.Erdos587.ProgressionGeometry
import ErdosProblems.Erdos587.WideScales

/-!
# The power-separated terminal branch

The geometric size and span inequalities imply both the density and
Fourier-cutoff budgets for the inner rectangle.
-/

open Filter

namespace Erdos587

lemma primitive_width_density_budget {q H J T Λ : ℝ} {B : ℕ}
    (hq : 0 ≤ q) (hH : 0 ≤ H) (hJ : 0 < J) (hT : 0 < T) (hΛ : 0 ≤ Λ)
    (hspan : q * J ≤ T) (hside : T ^ (1 / 4 : ℝ) * Λ ^ B ≤ H)
    (hprod : T ^ (3 / 4 : ℝ) * Λ ^ B ≤ H * J) :
    Real.sqrt q * Λ ^ B ≤ H := by
  have hbudget : q * (Λ ^ B) ^ 2 * J ≤ H ^ 2 * J := by
    calc
      _ = (q * J) * (Λ ^ B) ^ 2 := by ring
      _ ≤ T * (Λ ^ B) ^ 2 := mul_le_mul_of_nonneg_right hspan (sq_nonneg _)
      _ = (T ^ (1 / 4 : ℝ) * Λ ^ B) * (T ^ (3 / 4 : ℝ) * Λ ^ B) := by
        rw [mul_mul_mul_comm, ← Real.rpow_add hT,
          show (1 / 4 + 3 / 4 : ℝ) = 1 by norm_num, Real.rpow_one, pow_two]
      _ ≤ H * (H * J) := mul_le_mul hside hprod (by positivity) hH
      _ = _ := by ring
  have hsq : q * (Λ ^ B) ^ 2 ≤ H ^ 2 := (mul_le_mul_iff_left₀ hJ).mp hbudget
  apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hΛ B)) hH).mp
  simpa only [mul_pow, Real.sq_sqrt hq] using hsq

lemma primitive_width_cutoff_budget {q H J T Λ : ℝ} {B : ℕ}
    (hq : 0 ≤ q) (hH : 0 ≤ H) (hJ : 0 < J) (hT : 0 < T) (hΛ : 8 ≤ Λ)
    (hspan : q * J ≤ T)
    (hprod : T ^ (3 / 4 : ℝ) * Λ ^ (B + 1) ≤ H * J) :
    q * Λ ^ B ≤ (H / 8) * T ^ (1 / 4 : ℝ) := by
  have hΛ0 : 0 ≤ Λ := by linarith
  have hweighted : 8 * T * Λ ^ B ≤ H * J * T ^ (1 / 4 : ℝ) := by
    calc
      _ = (T * Λ ^ B) * 8 := by ring
      _ ≤ (T * Λ ^ B) * Λ :=
        mul_le_mul_of_nonneg_left hΛ (mul_nonneg hT.le (pow_nonneg hΛ0 B))
      _ = (T ^ (3 / 4 : ℝ) * Λ ^ (B + 1)) * T ^ (1 / 4 : ℝ) := by
        rw [pow_succ]
        rw [show T ^ (3 / 4 : ℝ) * (Λ ^ B * Λ) * T ^ (1 / 4 : ℝ) =
          (T ^ (3 / 4 : ℝ) * T ^ (1 / 4 : ℝ)) * (Λ ^ B * Λ) by ring,
          ← Real.rpow_add hT]
        norm_num
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hprod (Real.rpow_nonneg hT.le _)
  have hbudget : (q * Λ ^ B) * J ≤ ((H / 8) * T ^ (1 / 4 : ℝ)) * J := by
    calc
      _ = (q * J) * Λ ^ B := by ring
      _ ≤ T * Λ ^ B := mul_le_mul_of_nonneg_right hspan (pow_nonneg hΛ0 B)
      _ ≤ _ := by linarith
  exact (mul_le_mul_iff_left₀ hJ).mp hbudget

lemma modulus_upper_of_large_second_side {q J T : ℝ} (hq : 0 ≤ q) (hT : 0 < T)
    (hspan : q * J ≤ T) (hJ : T ^ (1 / 4 + 1 / 1000 : ℝ) ≤ J) :
    q ≤ T ^ (3 / 4 - 1 / 1000 : ℝ) := by
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hT (1 / 4 + 1 / 1000 : ℝ))).mp
  calc
    _ ≤ q * J := mul_le_mul_of_nonneg_left hJ hq
    _ ≤ T := hspan
    _ = _ := by rw [← Real.rpow_add hT]; norm_num

theorem exists_wide_primitive_terminal (C : ℝ) (hC : 0 < C) :
    ∃ B : ℕ, 0 < B ∧ ∃ T₀ : ℝ, ∀ (t u v H J T : ℕ), T₀ ≤ (T : ℝ) →
      0 < v → 0 < J → u.Coprime v → t + u * H + v * J ≤ T → u * H ≤ v * J →
      (T : ℝ) ≤ C * ((u * H + v * J : ℕ) : ℝ) →
      (T : ℝ) ^ (1 / 4 : ℝ) * (1 + Real.log T) ^ B ≤ H →
      (T : ℝ) ^ (3 / 4 : ℝ) * (1 + Real.log T) ^ B ≤ (H : ℝ) * J →
      (T : ℝ) ^ (1 / 4 + 1 / 1000 : ℝ) ≤ J →
      ∃ x ≤ H, ∃ y ≤ J, ∃ z : ℕ, 0 < z ∧ z ^ 2 = t + u * x + v * y := by
  let c := 1 / (32 * C)
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨A₀, hA₀, B, hB, hcong⟩ := exists_eventual_wide_quadratic_congruence c hc
  have hroot : ∀ᶠ T : ℝ in atTop, 32 * C ≤ Real.sqrt T := by
    simpa only [Real.sqrt_eq_rpow] using
      (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).eventually_ge_atTop (32 * C)
  have hconditions := hcong.and ((eventually_ge_atTop (1 : ℝ)).and
    ((Real.tendsto_log_atTop.eventually_ge_atTop (max 8 (8 * A₀))).and hroot))
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hconditions
  refine ⟨B + 1, by omega, T₀, ?_⟩
  intro t u v H J T hbig hv hJ hu hambient horient hspan hside hprod hJlarge
  obtain ⟨hcongT, hT1, hlog, hrootT⟩ := hT₀ (T : ℝ) hbig
  have hTpos : (0 : ℝ) < T := by linarith
  have hTnat : 0 < T := by exact_mod_cast hTpos
  let Λ := 1 + Real.log (T : ℝ)
  have hΛ8 : 8 ≤ Λ := by
    have hh := le_max_left (8 : ℝ) (8 * A₀)
    dsimp [Λ]
    linarith
  have hΛA : 8 * A₀ ≤ Λ := by
    have hh := le_max_right (8 : ℝ) (8 * A₀)
    dsimp [Λ]
    linarith
  have hΛ1 : 1 ≤ Λ := by linarith
  have hΛpos : 0 < Λ := by linarith
  have hΛpow : Λ ≤ Λ ^ (B + 1) := by
    calc
      Λ = 1 * Λ := (one_mul _).symm
      _ ≤ Λ ^ B * Λ := mul_le_mul_of_nonneg_right (one_le_pow₀ hΛ1) hΛpos.le
      _ = _ := (pow_succ _ _).symm
  have hH4 : 4 ≤ H := by
    have hpower : 1 ≤ (T : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow hT1 (by norm_num)
    have hh : (4 : ℝ) ≤ H := by
      change (T : ℝ) ^ (1 / 4 : ℝ) * Λ ^ (B + 1) ≤ H at hside
      have hpow0 : 0 ≤ Λ ^ (B + 1) := pow_nonneg hΛpos.le _
      nlinarith
    exact_mod_cast hh
  have hquarter : (H : ℝ) / 8 ≤ ((H / 4 : ℕ) : ℝ) := by
    simpa only [Nat.cast_ofNat, show (2 : ℝ) * 4 = 8 by norm_num] using
      half_div_le_nat_div 4 H (by norm_num) hH4
  have hvJ : (v : ℝ) * J ≤ T := by
    exact_mod_cast (show v * J ≤ T by omega)
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hdensity := primitive_width_density_budget (Nat.cast_nonneg v) (Nat.cast_nonneg H)
    hJR hTpos hΛpos.le hvJ hside hprod
  have hcutoff := primitive_width_cutoff_budget (Nat.cast_nonneg v) (Nat.cast_nonneg H)
    hJR hTpos hΛ8 hvJ hprod
  let U := H / 4
  let Z := Nat.sqrt (t + u * U) + 1
  let L := Nat.sqrt (t + v * J) - Nat.sqrt (t + u * U)
  have hUdensity : A₀ * Real.sqrt v ≤ (U : ℝ) := by
    apply le_trans _ hquarter
    have hh : 8 * A₀ * Real.sqrt v ≤ H := by
      calc
        _ ≤ Λ ^ (B + 1) * Real.sqrt v :=
          mul_le_mul_of_nonneg_right (hΛA.trans hΛpow) (Real.sqrt_nonneg _)
        _ ≤ H := by simpa only [mul_comm] using hdensity
    linarith
  have hUcutoff : (v : ℝ) * (1 + Real.log T) ^ B ≤ U * (T : ℝ) ^ (1 / 4 : ℝ) :=
    hcutoff.trans (mul_le_mul_of_nonneg_right hquarter (Real.rpow_nonneg hTpos.le _))
  have hLlo : c * Real.sqrt T ≤ (L : ℝ) :=
    primitive_root_window_real_lower hC hTnat hambient horient hspan hrootT
  have hLT : (L : ℝ) ≤ T := by
    have hh : L ≤ T := by
      calc
        L ≤ Nat.sqrt (t + v * J) := Nat.sub_le _ _
        _ ≤ t + v * J := Nat.sqrt_le_self _
        _ ≤ T := by omega
    exact_mod_cast hh
  have hqsize := modulus_upper_of_large_second_side (Nat.cast_nonneg v) hTpos hvJ hJlarge
  obtain ⟨x, hx, z, hz, heq⟩ := hcongT v u t Z L U hv hu hqsize hLlo hLT hUdensity hUcutoff
  apply exists_positive_square_in_progression_of_root_rectangle hv hx
    (show Nat.sqrt (t + u * (H / 4)) + 1 ≤ Z + z by dsimp [Z, U]; omega)
    (show Z + z ≤ Nat.sqrt (t + v * J) by dsimp [Z, L, U] at *; omega)
  exact heq

end Erdos587
