import ErdosProblems.Erdos67b.MRGSA10SourceYSchedule

/-! # A natural fixed-power cutoff and its structural thresholds -/

open Filter Asymptotics
open scoped Topology

namespace Erdos67b

noncomputable section

def mrCofactorPowerCutoff (delta : ℝ) (X : ℕ) : ℕ :=
  ⌈Real.exp (delta * Real.log (X : ℝ))⌉₊

theorem mrCofactorPowerCutoff_pos (delta : ℝ) (X : ℕ) :
    0 < mrCofactorPowerCutoff delta X := Nat.ceil_pos.mpr (Real.exp_pos _)

theorem mrCofactorPowerCutoff_exp_le (delta : ℝ) (X : ℕ) :
    Real.exp (delta * Real.log (X : ℝ)) ≤ (mrCofactorPowerCutoff delta X : ℝ) := Nat.le_ceil _

theorem mrCofactorPowerCutoff_log_lower (delta : ℝ) (X : ℕ) :
    delta * Real.log (X : ℝ) ≤ Real.log (mrCofactorPowerCutoff delta X : ℝ) := by
  calc
    _ = Real.log (Real.exp (delta * Real.log (X : ℝ))) := (Real.log_exp _).symm
    _ ≤ _ := Real.log_le_log (Real.exp_pos _) (mrCofactorPowerCutoff_exp_le delta X)

theorem mrCofactorPowerCutoff_log_upper {delta : ℝ} (hdelta : 0 ≤ delta) {X : ℕ}
    (hX : 1 ≤ X) :
    Real.log (mrCofactorPowerCutoff delta X : ℝ) ≤ delta * Real.log (X : ℝ) + Real.log 2 := by
  have hL : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX)
  have hone : 1 ≤ Real.exp (delta * Real.log (X : ℝ)) := Real.one_le_exp_iff.2 (mul_nonneg hdelta hL)
  have hceil : (mrCofactorPowerCutoff delta X : ℝ) < Real.exp (delta * Real.log (X : ℝ)) + 1 :=
    Nat.ceil_lt_add_one (Real.exp_pos _).le
  calc
    _ ≤ Real.log (2 * Real.exp (delta * Real.log (X : ℝ))) :=
      Real.log_le_log (by exact_mod_cast mrCofactorPowerCutoff_pos delta X) (by linarith)
    _ = _ := by rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]; ring

theorem mrCofactorPowerCutoff_le_self {delta : ℝ} (hdelta : delta ≤ 1) {X : ℕ} (hX : 1 ≤ X) :
    mrCofactorPowerCutoff delta X ≤ X := by
  apply Nat.ceil_le.2
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  calc
    Real.exp (delta * Real.log (X : ℝ)) ≤ Real.exp (Real.log (X : ℝ)) :=
      Real.exp_le_exp.2 (mul_le_of_le_one_left (Real.log_nonneg (by exact_mod_cast hX)) hdelta)
    _ = _ := Real.exp_log hXpos

theorem mrTendsto_cofactorPowerCutoff {delta : ℝ} (hdelta : 0 < delta) :
    Tendsto (mrCofactorPowerCutoff delta) atTop atTop := by
  have hscale : Tendsto (fun X : ℕ ↦ delta * Real.log (X : ℝ)) atTop atTop :=
    EulerSubpower.tendsto_log_nat_atTop.const_mul_atTop hdelta
  have hexp := Real.tendsto_exp_atTop.comp hscale
  apply tendsto_atTop.2
  intro N
  filter_upwards [hexp.eventually (eventually_ge_atTop (N : ℝ))] with X hX
  exact_mod_cast hX.trans (mrCofactorPowerCutoff_exp_le delta X)

theorem mrEventually_cofactorPowerCutoff_log_upper {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ X : ℕ in atTop,
      Real.log (mrCofactorPowerCutoff delta X : ℝ) ≤ 2 * delta * Real.log (X : ℝ) := by
  have hscale := EulerSubpower.tendsto_log_nat_atTop.const_mul_atTop hdelta
  filter_upwards [hscale.eventually (eventually_ge_atTop (Real.log 2)), eventually_ge_atTop 1]
    with X hlog hX
  exact (mrCofactorPowerCutoff_log_upper hdelta.le hX).trans (by linarith)

theorem mrEventually_log_pow_le_cofactorPowerCutoff {delta : ℝ} (hdelta : 0 < delta) (k : ℕ) :
    ∀ᶠ X : ℕ in atTop, Real.log (X : ℝ) ^ k ≤ (mrCofactorPowerCutoff delta X : ℝ) := by
  have hpoly : (fun r : ℝ ↦ r ^ k) =o[atTop] (fun r : ℝ ↦ Real.exp (delta * r)) := by
    simpa only [Real.rpow_natCast] using isLittleO_rpow_exp_pos_mul_atTop (k : ℝ) hdelta
  have hbound := (hpoly.comp_tendsto EulerSubpower.tendsto_log_nat_atTop).bound zero_lt_one
  filter_upwards [hbound] with X hX
  have hle : Real.log (X : ℝ) ^ k ≤ Real.exp (delta * Real.log (X : ℝ)) := by
    have habs : |Real.log (X : ℝ) ^ k| ≤ Real.exp (delta * Real.log (X : ℝ)) := by
      simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul] using hX
    exact (le_abs_self _).trans habs
  exact hle.trans (mrCofactorPowerCutoff_exp_le delta X)

theorem mrEventually_cofactorPowerCutoff_log_square {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ X : ℕ in atTop,
      4 * Real.log (X : ℝ) ≤ Real.log (mrCofactorPowerCutoff delta X : ℝ) ^ 2 := by
  filter_upwards [EulerSubpower.tendsto_log_nat_atTop.eventually
    (eventually_ge_atTop (4 / delta ^ 2)), eventually_ge_atTop 1] with X hlarge hX
  have hL : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX)
  have hcut := mrCofactorPowerCutoff_log_lower delta X
  have hfour : (4 : ℝ) ≤ delta ^ 2 * Real.log (X : ℝ) := by
    have h := (div_le_iff₀ (sq_pos_of_pos hdelta)).1 hlarge
    nlinarith
  have hmain : 4 * Real.log (X : ℝ) ≤ (delta * Real.log (X : ℝ)) ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hfour hL
    nlinarith
  exact hmain.trans (pow_le_pow_left₀ (mul_nonneg hdelta.le hL) hcut 2)

theorem mrEventually_cofactorPowerCutoff_conditions {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1) (Y : ℕ) :
    ∀ᶠ X : ℕ in atTop,
      let y := mrCofactorPowerCutoff delta X
      Y ≤ y ∧ 23 ≤ y ∧ y ≤ X ∧ 6 ≤ Real.log (y : ℝ) ∧
        Real.log (X : ℝ) ^ 12 ≤ (y : ℝ) ∧
        4 * Real.log (X : ℝ) ≤ Real.log (y : ℝ) ^ 2 ∧
        delta * Real.log (X : ℝ) ≤ Real.log (y : ℝ) ∧
        Real.log (y : ℝ) ≤ 2 * delta * Real.log (X : ℝ) := by
  have hscale := EulerSubpower.tendsto_log_nat_atTop.const_mul_atTop hdelta
  filter_upwards [(mrTendsto_cofactorPowerCutoff hdelta).eventually (eventually_ge_atTop Y),
    (mrTendsto_cofactorPowerCutoff hdelta).eventually (eventually_ge_atTop 23),
    eventually_ge_atTop 1, hscale.eventually (eventually_ge_atTop 6),
    mrEventually_log_pow_le_cofactorPowerCutoff hdelta 12,
    mrEventually_cofactorPowerCutoff_log_square hdelta,
    mrEventually_cofactorPowerCutoff_log_upper hdelta] with X hY hy hX hlog hpow hsq hu
  exact ⟨hY, hy, mrCofactorPowerCutoff_le_self hdeltaOne hX,
    hlog.trans (mrCofactorPowerCutoff_log_lower delta X), hpow, hsq,
    mrCofactorPowerCutoff_log_lower delta X, hu⟩

end

end Erdos67b
