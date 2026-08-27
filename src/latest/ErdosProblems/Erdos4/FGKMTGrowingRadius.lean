import ErdosProblems.Erdos4.FGKMTGrowingParameters

/-! A fixed positive power sieve radius at every sufficiently large endpoint. -/

namespace Erdos4.FGKMT

open Filter

noncomputable def growingRadius (x : ℕ) : ℕ := ⌊(x : ℝ) ^ (1 / 50 : ℝ)⌋₊

theorem growingRadius_upper (x : ℕ) : (growingRadius x : ℝ) ≤ (x : ℝ) ^ (1 / 50 : ℝ) :=
  Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg x) _)

theorem growingRadius_pow_upper (x m : ℕ) :
    (growingRadius x : ℝ) ^ m ≤ (x : ℝ) ^ ((m : ℝ) / 50) := by
  apply (pow_le_pow_left₀ (Nat.cast_nonneg _) (growingRadius_upper x) m).trans_eq
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg x)]
  congr 1
  ring

theorem growingRadius_tendsto : Tendsto growingRadius atTop atTop := by
  have hp : Tendsto (fun x : ℕ => (x : ℝ) ^ (1 / 50 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 50)).comp tendsto_natCast_atTop_atTop
  apply tendsto_atTop.2
  intro n
  filter_upwards [hp.eventually (eventually_ge_atTop (n : ℝ))] with x hx
  exact Nat.le_floor hx

theorem growingRadius_pow_fifty_le (x : ℕ) : growingRadius x ^ 50 ≤ x := by
  have hh := growingRadius_pow_upper x 50
  norm_num at hh
  exact_mod_cast hh

theorem eventually_growingRadius_bounds :
    ∀ᶠ x : ℕ in atTop, 2 ≤ growingRadius x ∧
      Real.log (x : ℝ) / 100 ≤ Real.log (growingRadius x : ℝ) := by
  have hp : Tendsto (fun x : ℕ => (x : ℝ) ^ (1 / 50 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 50)).comp tendsto_natCast_atTop_atTop
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hp.eventually (eventually_ge_atTop 2),
    hlog.eventually (eventually_ge_atTop (100 * Real.log 2)), eventually_ge_atTop 1]
    with x hpow hlarge hx
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hR : 2 ≤ growingRadius x := Nat.le_floor hpow
  have hRreal : (2 : ℝ) ≤ growingRadius x := by exact_mod_cast hR
  have hlo : (x : ℝ) ^ (1 / 50 : ℝ) / 2 ≤ (growingRadius x : ℝ) := by
    have hh := Nat.lt_floor_add_one ((x : ℝ) ^ (1 / 50 : ℝ))
    change (x : ℝ) ^ (1 / 50 : ℝ) < (growingRadius x : ℝ) + 1 at hh
    linarith
  have hlogR := Real.log_le_log (by positivity : 0 < (x : ℝ) ^ (1 / 50 : ℝ) / 2) hlo
  rw [Real.log_div (Real.rpow_pos_of_pos hxpos _).ne' (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_rpow hxpos] at hlogR
  change 100 * Real.log 2 ≤ Real.log (x : ℝ) at hlarge
  exact ⟨hR, by linarith⟩

end Erdos4.FGKMT
