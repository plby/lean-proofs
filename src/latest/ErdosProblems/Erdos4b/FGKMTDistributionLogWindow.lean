/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTEffectivePrimeDistribution

/-!
# The logarithmically extended prime-distribution window

The natural window endpoint is the floor of x log(x)^4. The modulus bound
remains x^(1/3), and one excluded prime controls every endpoint in this
larger window. The fixed logarithmic factor is absorbed exponentially.
-/

namespace Erdos4b.FGKMT

noncomputable section

open Filter BoundedGaps.Maynard

def primeDistributionLogWindow (x : ℕ) : ℕ :=
  ⌊(x : ℝ) * Real.log (x : ℝ) ^ 4⌋₊

theorem primeDistributionLogWindow_le (x : ℕ) :
    (primeDistributionLogWindow x : ℝ) ≤ (x : ℝ) * Real.log (x : ℝ) ^ 4 :=
  Nat.floor_le (by positivity)

theorem eventually_primeDistributionLogWindow_bounds :
    ∀ᶠ x : ℕ in atTop, x ≤ primeDistributionLogWindow x ∧ primeDistributionLogWindow x ≤ x ^ 2 := by
  have hlogTop : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogdom := ((isLittleO_log_rpow_rpow_atTop ((4 : ℕ) : ℝ)
    (by norm_num : (0 : ℝ) < 1)).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventuallyLE
  filter_upwards [hlogTop.eventually (eventually_ge_atTop (1 : ℝ)), hlogdom] with x hlog hpow
  have hlog1 : 1 ≤ Real.log (x : ℝ) := hlog
  have hlog4 : 1 ≤ Real.log (x : ℝ) ^ 4 := one_le_pow₀ hlog1
  have hlog0 := Real.log_natCast_nonneg x
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  simp only [Function.comp_apply, Real.norm_eq_abs, Real.rpow_natCast, Real.rpow_one,
    abs_of_nonneg (pow_nonneg hlog0 4), abs_of_nonneg hx0] at hpow
  have hxx : (x : ℝ) ≤ (x : ℝ) * Real.log (x : ℝ) ^ 4 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hlog4 hx0
  refine ⟨Nat.le_floor hxx, ?_⟩
  have hbound := (primeDistributionLogWindow_le x).trans
    (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg x))
  exact_mod_cast (by simpa only [sq] using hbound :
    (primeDistributionLogWindow x : ℝ) ≤ (x : ℝ) ^ 2)

theorem sqrtLog_le_two_mul_of_le_sq {x z : ℕ} (hz1 : 1 ≤ z) (hzx : z ≤ x ^ 2) :
    Real.sqrt (Real.log (z : ℝ)) ≤ 2 * Real.sqrt (Real.log (x : ℝ)) := by
  have hzpos : (0 : ℝ) < z := by exact_mod_cast hz1
  have hlog : Real.log (z : ℝ) ≤ 2 * Real.log (x : ℝ) := by
    calc
      _ ≤ Real.log ((x : ℝ) ^ 2) :=
        Real.log_le_log hzpos (by exact_mod_cast hzx)
      _ = _ := by rw [Real.log_pow]; norm_num
  have hu := Real.sqrt_nonneg (Real.log (z : ℝ))
  have hv := Real.sqrt_nonneg (Real.log (x : ℝ))
  have hu2 := Real.sq_sqrt (Real.log_natCast_nonneg z)
  have hv2 := Real.sq_sqrt (Real.log_natCast_nonneg x)
  exact (sq_le_sq₀ hu (by positivity)).mp (by nlinarith [Real.log_natCast_nonneg x])

theorem logWindow_expDecay_le {x z : ℕ} {d : ℝ} (hd : 0 ≤ d) (hx1 : 1 ≤ x)
    (hxz : x ≤ z) (hz : (z : ℝ) ≤ (x : ℝ) * Real.log (x : ℝ) ^ 4)
    (hlog : Real.log (x : ℝ) ^ 4 ≤ Real.exp ((d / 2) * Real.sqrt (Real.log (x : ℝ)))) :
    (z : ℝ) * Real.exp (-d * Real.sqrt (Real.log (z : ℝ))) ≤
      (x : ℝ) * Real.exp (-(d / 2) * Real.sqrt (Real.log (x : ℝ))) := by
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx1
  have hlogxz : Real.log (x : ℝ) ≤ Real.log (z : ℝ) :=
    Real.log_le_log hxpos (by exact_mod_cast hxz)
  have hsqrt := Real.sqrt_le_sqrt hlogxz
  have hexp : Real.exp (-d * Real.sqrt (Real.log (z : ℝ))) ≤
      Real.exp (-d * Real.sqrt (Real.log (x : ℝ))) := by
    apply Real.exp_monotone
    exact mul_le_mul_of_nonpos_left hsqrt (neg_nonpos.mpr hd)
  calc
    _ ≤ ((x : ℝ) * Real.log (x : ℝ) ^ 4) *
        Real.exp (-d * Real.sqrt (Real.log (x : ℝ))) :=
      mul_le_mul hz hexp (Real.exp_pos _).le (by positivity)
    _ ≤ ((x : ℝ) * Real.exp ((d / 2) * Real.sqrt (Real.log (x : ℝ)))) *
        Real.exp (-d * Real.sqrt (Real.log (x : ℝ))) := by gcongr
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

theorem exists_effective_primePrefix_logWindow_distribution :
    ∃ D a d : ℝ, 0 < D ∧ 0 < a ∧ 0 < d ∧ ∃ X0 : ℕ, 4 ≤ X0 ∧
      ∀ x : ℕ, X0 ≤ x → ∃ B : ℕ,
        1 ≤ B ∧ (B : ℝ) ≤ Real.exp (2 * a * Real.sqrt (Real.log (x : ℝ))) ∧
        (B = 1 ∨ B.Prime) ∧ ∀ L : ℕ, (L : ℝ) ≤ vaughanCubeRoot x →
          coprimePrimeDiscrepancyPrefixSum B L (primeDistributionLogWindow x) ≤
            D * ((x : ℝ) * Real.exp (-d * Real.sqrt (Real.log (x : ℝ)))) := by
  obtain ⟨D, a, d, hD, ha, hd, Xs, hXs, hdist⟩ := exists_effective_primePrefix_distribution
  obtain ⟨Xg, hXg⟩ := eventually_atTop.mp
    (eventually_primeDistributionLogWindow_bounds.and
      (eventually_log_pow_le_exp_mul_sqrtLog 4 (by positivity : 0 < d / 2)))
  refine ⟨D, a, d / 2, hD, ha, by positivity, max Xs Xg, hXs.trans (le_max_left _ _), ?_⟩
  intro x hx
  have hxs : Xs ≤ x := (le_max_left _ _).trans hx
  have hxg : Xg ≤ x := (le_max_right _ _).trans hx
  have hx1 : 1 ≤ x := by omega
  obtain ⟨⟨hxz, hzx⟩, hlog⟩ := hXg x hxg
  let z := primeDistributionLogWindow x
  obtain ⟨B, hBpos, hBbound, hB, hbound⟩ := hdist z (hxs.trans hxz)
  have hsqrt := sqrtLog_le_two_mul_of_le_sq (hx1.trans hxz) hzx
  have hexp : Real.exp (a * Real.sqrt (Real.log (z : ℝ))) ≤
      Real.exp (2 * a * Real.sqrt (Real.log (x : ℝ))) := by
    apply Real.exp_monotone
    nlinarith
  refine ⟨B, hBpos, hBbound.trans hexp, hB, ?_⟩
  intro L hL
  have hcube : vaughanCubeRoot x ≤ vaughanCubeRoot z := by
    apply Real.rpow_le_rpow (Nat.cast_nonneg x) (by exact_mod_cast hxz)
    norm_num
  exact (hbound L (hL.trans hcube)).trans
    (mul_le_mul_of_nonneg_left
      (logWindow_expDecay_le hd.le hx1 hxz (primeDistributionLogWindow_le x) hlog) hD.le)

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.eventually_primeDistributionLogWindow_bounds
#print axioms Erdos4b.FGKMT.exists_effective_primePrefix_logWindow_distribution
