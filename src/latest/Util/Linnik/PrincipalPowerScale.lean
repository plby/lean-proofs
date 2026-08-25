import Util.Linnik.PowerScale
import Util.Linnik.ZetaRepulsion

/-!
# Principal error relative to an exceptional gap on a power scale

The geometric mean of the strong-PNT error and the repulsion error is
small compared with the exceptional main-term saving.  This avoids any
need to assume a log-free density theorem for the zeta function.
-/

namespace Linnik

open Filter Erdos48 BoundedGaps.Maynard
open scoped Topology

theorem div_pow_four_le_mul_sq {x n lambda : ℝ}
    (hx : 0 ≤ x) (hn : 1 ≤ n) (hlambda : 1 / n ≤ lambda) :
    x / n ^ 4 ≤ x * lambda ^ 2 := by
  have hn₀ : 0 < n := by linarith
  have hlambda₀ : 0 ≤ lambda := (one_div_pos.mpr hn₀).le.trans hlambda
  have hmul := (div_le_iff₀ hn₀).mp hlambda
  have hprod : 1 ≤ lambda ^ 2 * n ^ 4 := by
    have hsq : 1 ≤ (lambda * n) ^ 2 := one_le_pow₀ hmul
    have hn₂ : 1 ≤ n ^ 2 := one_le_pow₀ hn
    have h := mul_le_mul hsq hn₂ (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
    nlinarith
  apply (div_le_iff₀ (by positivity : 0 < n ^ 4)).mpr
  have := mul_le_mul_of_nonneg_left hprod hx
  nlinarith

theorem error_le_of_complementary_bounds
    {E x H lambda C epsilon : ℝ}
    (hE : 0 ≤ E) (hx : 0 ≤ x) (hlambda : 0 ≤ lambda)
    (hC : 0 < C) (hepsilon : 0 ≤ epsilon)
    (hlog : E * H ^ 2 ≤ epsilon ^ 2 / C * x)
    (hrep : E ≤ C * x * lambda ^ 2 * H ^ 2) :
    E ≤ epsilon * x * lambda := by
  have h₁ := mul_le_mul_of_nonneg_left hrep hE
  have h₂ := mul_le_mul_of_nonneg_left hlog
    (mul_nonneg (mul_nonneg hC.le hx) (sq_nonneg lambda))
  have hcancel : (C * x * lambda ^ 2) * (epsilon ^ 2 / C * x) =
      (epsilon * x * lambda) ^ 2 := by field_simp
  rw [hcancel] at h₂
  have hsquare : E ^ 2 ≤ (epsilon * x * lambda) ^ 2 := by nlinarith
  exact (sq_le_sq₀ hE (by positivity)).mp hsquare

theorem exists_principal_powerScale_exceptional_error :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ L : ℕ, 64 ≤ L → 6 * R ≤ L →
      ∀ epsilon : ℝ, 0 < epsilon →
        ∀ᶠ n : ℕ in atTop,
          ∀ (q : ℕ) [NeZero q], 1 < q → q ≤ n →
            ∀ (chi : DirichletCharacter ℂ q), chi ≠ 1 → chi ^ 2 = 1 →
              ∀ beta : ℝ, 0 < beta → beta < 1 →
                DirichletCharacter.LFunction chi (beta : ℂ) = 0 →
                |Chebyshev.psi ((n ^ L : ℕ) : ℝ) - ((n ^ L : ℕ) : ℝ)| ≤
                  epsilon * ((n ^ L : ℕ) : ℝ) * (logScale n * (1 - beta)) := by
  obtain ⟨R, C, hR, hC, hkernel⟩ := exists_zetaKernel_exceptional_bound
  obtain ⟨K, hK, hformula⟩ := exists_nat_abs_psi_sub_le_error_add_zetaKernel
  refine ⟨R, hR, ?_⟩
  intro L hL hLR epsilon hepsilon
  let C' : ℝ := 2 * C + (K : ℝ) * (L : ℝ) ^ 2
  have hC' : 0 < C' := by dsimp [C']; positivity
  have hPNT := eventually_abs_psi_pow_sub_mul_logScale_sq_le
    (div_pos (sq_pos_of_pos hepsilon) hC') (by omega : 1 ≤ L)
  filter_upwards [hPNT, eventually_uniform_quadratic_real_zero_gap,
    tendsto_logScale.eventually_ge_atTop 1, eventually_ge_atTop 2]
    with n hPNT hgap hH hn
  intro q _ hq hqn chi hchi hsquare beta hbeta₀ hbeta₁ hzero
  let x : ℝ := ((n ^ L : ℕ) : ℝ)
  let H : ℝ := logScale n
  let lambda : ℝ := H * (1 - beta)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn₀ : (0 : ℝ) < n := by linarith
  have hbetaGap := hgap q hq hqn chi hchi hsquare beta hbeta₁.le hzero
  have hlambda : 1 / (n : ℝ) ≤ lambda := by
    dsimp [lambda, H]
    nlinarith [one_div_pos.mpr hn₀]
  have hlambda₀ : 0 ≤ lambda := (one_div_pos.mpr hn₀).le.trans hlambda
  have hx : (4 : ℕ) ≤ n ^ L := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ n ^ 2 := Nat.pow_le_pow_left hn 2
      _ ≤ n ^ L := Nat.pow_le_pow_right (by omega) (by omega)
  have hheight : 2 ≤ n ^ 4 := hn.trans (Nat.le_pow (by norm_num))
  have hheightX : n ^ 4 ≤ n ^ L := Nat.pow_le_pow_right (by omega) (by omega)
  have hxR : 4 ≤ x := by dsimp [x]; exact_mod_cast hx
  have hx₀ : 0 ≤ x := by dsimp [x]; positivity
  have hscale := logScale_mul_le_log_pow hn (by linarith : 0 ≤ R) hLR
  have hz := hkernel q n hq hqn chi hchi hsquare beta hbeta₀ hbeta₁ hzero
    ((n ^ 4 : ℕ) : ℝ) x (by exact_mod_cast hheight) hxR
    (by simpa only [Nat.cast_pow, logScale, H, x] using hscale)
  simp only [Nat.cast_pow] at hz
  have hfar := natPow_rpow_fifteen_sixteen_le_div_four (by omega : 1 ≤ n) hL
  have hdiv : x / (n : ℝ) ^ 4 ≤ x * lambda ^ 2 := div_pow_four_le_mul_sq hx₀ hnR hlambda
  have hfar' : x ^ (15 / 16 : ℝ) ≤ x * lambda ^ 2 := hfar.trans hdiv
  have hz' : ‖dirichletNontrivialZeroKernelSum (1 : DirichletCharacter ℂ 1) x (n ^ 4 : ℕ)‖ ≤
      2 * C * x * lambda ^ 2 * H ^ 2 := by
    rw [Nat.cast_pow]
    apply hz.trans
    change C * (x * lambda ^ 2 + x ^ (15 / 16 : ℝ)) * H ^ 2 ≤ _
    have := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hfar' (by linarith : 0 ≤ C)) (sq_nonneg H)
    nlinarith
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have hlogH : Real.log (n : ℝ) ^ 2 ≤ H ^ 2 := by
    apply (sq_le_sq₀ hlogn (by dsimp [H]; linarith)).mpr
    exact (logScale_bounds hn).1
  have herr : (K : ℝ) * (x * Real.log x ^ 2 / ((n ^ 4 : ℕ) : ℝ)) ≤
      (K : ℝ) * (L : ℝ) ^ 2 * x * lambda ^ 2 * H ^ 2 := by
    have hlogx : Real.log x = (L : ℝ) * Real.log (n : ℝ) := log_natCast_pow n L
    rw [hlogx, Nat.cast_pow]
    calc
      _ = (K : ℝ) * (L : ℝ) ^ 2 * (x / (n : ℝ) ^ 4) * Real.log (n : ℝ) ^ 2 := by ring
      _ ≤ (K : ℝ) * (L : ℝ) ^ 2 * (x * lambda ^ 2) * H ^ 2 := by gcongr
      _ = _ := by ring
  have hpsi := hformula ((n ^ 4 : ℕ) : ℝ) (by exact_mod_cast hheight)
    (n ^ L) hx (by exact_mod_cast hheightX)
  have hrep : |Chebyshev.psi x - x| ≤ C' * x * lambda ^ 2 * H ^ 2 := by
    dsimp [C']
    nlinarith [hpsi]
  exact error_le_of_complementary_bounds (abs_nonneg _) hx₀ hlambda₀ hC' hepsilon.le hPNT hrep

end Linnik
