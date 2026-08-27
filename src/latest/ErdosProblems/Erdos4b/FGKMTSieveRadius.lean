/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTConductorCutoff

/-! # The natural radius and its uniform logarithmic window -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

def dimensionSieveRadius (x : ℕ) : ℕ := ⌊((x : ℝ) / 4) ^ (1 / 9 : ℝ)⌋₊

theorem dimensionSieveRadius_le_rpow (x : ℕ) :
    (dimensionSieveRadius x : ℝ) ≤ (x : ℝ) ^ (1 / 9 : ℝ) := by
  calc
    _ ≤ ((x : ℝ) / 4) ^ (1 / 9 : ℝ) := Nat.floor_le (by positivity)
    _ ≤ _ := Real.rpow_le_rpow (by positivity)
      (by nlinarith [show (0 : ℝ) ≤ x from Nat.cast_nonneg x]) (by norm_num)

theorem eventually_dimensionSieveRadius_window :
    ∀ᶠ x : ℕ in atTop,
      1 < dimensionSieveRadius x ∧ dimensionSieveRadius x ≤ x ∧
      1 ≤ Real.log (dimensionSieveRadius x : ℝ) ∧
      (1 / 18 : ℝ) * Real.log (x : ℝ) ≤ Real.log (dimensionSieveRadius x : ℝ) := by
  have hlogTop : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (4 : ℕ),
    hlogTop.eventually (eventually_ge_atTop (18 : ℝ)),
    hlogTop.eventually (eventually_ge_atTop (2 * Real.log 4 + 18 * Real.log 2))] with
      x hx4 hL18 hLbound
  have hxR : (4 : ℝ) ≤ x := by exact_mod_cast hx4
  have hxpos : (0 : ℝ) < x := by positivity
  have hbase : (1 : ℝ) ≤ (x : ℝ) / 4 := by linarith
  let r := ((x : ℝ) / 4) ^ (1 / 9 : ℝ)
  have hr1 : 1 ≤ r := Real.one_le_rpow hbase (by norm_num)
  have hrpos : 0 < r := by linarith
  have hfloor : r / 2 < (dimensionSieveRadius x : ℝ) := Nat.div_two_lt_floor hr1
  have hRpos : (0 : ℝ) < dimensionSieveRadius x := (by positivity : 0 < r / 2).trans hfloor
  have hlogR := Real.log_le_log (by positivity : 0 < r / 2) hfloor.le
  have hlogr : Real.log (r / 2) = (Real.log (x : ℝ) - Real.log 4) / 9 - Real.log 2 := by
    rw [Real.log_div hrpos.ne' (by norm_num)]
    dsimp only [r]
    rw [Real.log_rpow (by positivity), Real.log_div hxpos.ne' (by norm_num)]
    ring
  rw [hlogr] at hlogR
  have hlower : (1 / 18 : ℝ) * Real.log (x : ℝ) ≤ Real.log (dimensionSieveRadius x : ℝ) := by
    linarith
  have hlogone : 1 ≤ Real.log (dimensionSieveRadius x : ℝ) := by linarith
  have hR : 1 < dimensionSieveRadius x := by
    by_contra! hbad
    have hle : (dimensionSieveRadius x : ℝ) ≤ 1 := by exact_mod_cast hbad
    have hnonpos := Real.log_nonpos hRpos.le hle
    linarith
  have hRx : dimensionSieveRadius x ≤ x := by
    have hpow := Real.rpow_le_self_of_one_le (by linarith : (1 : ℝ) ≤ x)
      (by norm_num : (1 / 9 : ℝ) ≤ 1)
    exact_mod_cast (dimensionSieveRadius_le_rpow x).trans hpow
  exact ⟨hR, hRx, hlogone, hlower⟩

theorem dimensionSieveRadius_sq_le_rpow (x : ℕ) :
    ((dimensionSieveRadius x ^ 2 : ℕ) : ℝ) ≤ (x : ℝ) ^ (2 / 9 : ℝ) := by
  calc
    _ ≤ ((x : ℝ) ^ (1 / 9 : ℝ)) ^ 2 := by
      rw [Nat.cast_pow]
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) (dimensionSieveRadius_le_rpow x) 2
    _ = ((x : ℝ) ^ (1 / 9 : ℝ)) ^ ((2 : ℕ) : ℝ) := (Real.rpow_natCast _ 2).symm
    _ = _ := by rw [← Real.rpow_mul (Nat.cast_nonneg x)]; norm_num

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.eventually_dimensionSieveRadius_window
#print axioms Erdos4b.FGKMT.dimensionSieveRadius_sq_le_rpow
