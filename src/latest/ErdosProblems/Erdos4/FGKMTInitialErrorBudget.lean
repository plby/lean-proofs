import ErdosProblems.Erdos4.FGKMTGrowingDensityPowers
import ErdosProblems.Erdos4.FGKMTFullTupleNormalizerLoss

/-! Close the initial conditioning error and marginal budgets at the actual growing parameters. -/

namespace Erdos4.FGKMT

open Filter Asymptotics

theorem eventually_const_log_power_le_rpow (m : ℕ) (C : ℝ) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ x : ℕ in atTop, C * Real.log (x : ℝ) ^ m ≤ (x : ℝ) ^ a := by
  have hh := (((isLittleO_log_rpow_rpow_atTop (m : ℝ) ha).const_mul_left C).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventuallyLE
  filter_upwards [hh] with x hx
  have hnorm : |C * Real.log (x : ℝ) ^ m| ≤ (x : ℝ) ^ a := by
    simpa only [Function.comp_apply, Real.rpow_natCast, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg x) a)] using hx
  exact (le_abs_self _).trans hnorm

theorem initial_degree_error_le {k : ℕ} (hk : 1 ≤ k) {σ α β ε : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hα : 0 ≤ α) (hβ : 24 * σ ≤ β) :
    76 * ε + 4 * (k : ℝ) * α / (σ ^ (2 * k - 2) * β) +
      80 * (k : ℝ) ^ 2 * α / σ ^ (3 * k - 1) ≤
        76 * ε + 81 * (k : ℝ) ^ 2 * α / σ ^ (3 * k) := by
  have hβpos : 0 < β := (by positivity : 0 < 24 * σ).trans_le hβ
  have hp : σ ^ (3 * k) ≤ σ ^ (2 * k - 2) * σ := by
    rw [← pow_succ]
    exact pow_le_pow_of_le_one hσ0.le hσ1 (by omega)
  have hden : 24 * σ ^ (3 * k) ≤ σ ^ (2 * k - 2) * β := by
    have hh := mul_le_mul_of_nonneg_left hβ (pow_nonneg hσ0.le (2 * k - 2))
    nlinarith
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hnum : ((k : ℝ) * α) / 6 ≤ (k : ℝ) ^ 2 * α := by
    have hh : (k : ℝ) / 6 ≤ (k : ℝ) ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hh hα
    nlinarith
  have hfirst : 4 * (k : ℝ) * α / (σ ^ (2 * k - 2) * β) ≤
      (k : ℝ) ^ 2 * α / σ ^ (3 * k) := by
    calc
      _ ≤ 4 * (k : ℝ) * α / (24 * σ ^ (3 * k)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = (((k : ℝ) * α) / 6) / σ ^ (3 * k) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hnum (pow_nonneg hσ0.le _)
  have hsecond : 80 * (k : ℝ) ^ 2 * α / σ ^ (3 * k - 1) ≤
      80 * (k : ℝ) ^ 2 * α / σ ^ (3 * k) :=
    div_le_div_of_nonneg_left (by positivity) (pow_pos hσ0 _)
      (pow_le_pow_of_le_one hσ0.le hσ1 (Nat.sub_le _ _))
  calc
    _ ≤ 76 * ε + (k : ℝ) ^ 2 * α / σ ^ (3 * k) +
        80 * (k : ℝ) ^ 2 * α / σ ^ (3 * k) := add_le_add (add_le_add le_rfl hfirst) hsecond
    _ = _ := by ring

theorem eventually_growing_initial_loss_bounds :
    ∀ᶠ x : ℕ in atTop,
      let k := sieveDimension (growingIndex x)
      let σ := UnitFourier.unitDensity (growingRandomValue x)
      81 * (k : ℝ) ^ 2 * (x : ℝ) ^ (-9 / 10 : ℝ) / σ ^ (3 * k) ≤
        (x : ℝ) ^ (-4 / 5 : ℝ) ∧
      2 * (k : ℝ) * (x : ℝ) ^ (-9 / 10 : ℝ) / σ ^ k ≤ (x : ℝ) ^ (-4 / 5 : ℝ) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_growingDimension_bounds,
    growingDimension_tendsto.eventually (eventually_ge_atTop 1),
    eventually_growing_random_inverse_power (by norm_num : (0 : ℝ) < 1 / 100),
    eventually_const_log_power_le_rpow 2 81 (by norm_num : (0 : ℝ) < 9 / 100),
    hlog.eventually (eventually_ge_atTop 1), eventually_ge_atTop 1]
    with x hdim hk1 hinv hlogpow hL hx
  let k := sieveDimension (growingIndex x)
  let σ := UnitFourier.unitDensity (growingRandomValue x)
  change 1 ≤ Real.log (x : ℝ) at hL
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hσpos : 0 < σ := UnitFourier.unitDensity_pos (growingRandomValue x)
  have hσ1 : σ ≤ 1 := sieve_unitDensity_le_one (growingRandomValue x)
  have hkL : (k : ℝ) ≤ Real.log (x : ℝ) := by
    apply hdim.2.trans
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL
      (by norm_num : (1 / 100 : ℝ) ≤ 1)
  have hcoef : 81 * (k : ℝ) ^ 2 ≤ (x : ℝ) ^ (9 / 100 : ℝ) := by
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hkL 2)
      (by norm_num)).trans hlogpow
  have hratio : (x : ℝ) ^ (-9 / 10 : ℝ) / σ ^ (3 * k) ≤ (x : ℝ) ^ (-89 / 100 : ℝ) := by
    calc
      _ = (x : ℝ) ^ (-9 / 10 : ℝ) * (1 / σ ^ (3 * k)) := by ring
      _ ≤ (x : ℝ) ^ (-9 / 10 : ℝ) * (x : ℝ) ^ (1 / 100 : ℝ) :=
        mul_le_mul_of_nonneg_left hinv (Real.rpow_nonneg hxpos.le _)
      _ = _ := by rw [← Real.rpow_add hxpos]; norm_num
  have hloss : 81 * (k : ℝ) ^ 2 * (x : ℝ) ^ (-9 / 10 : ℝ) / σ ^ (3 * k) ≤
      (x : ℝ) ^ (-4 / 5 : ℝ) := by
    calc
      _ = (81 * (k : ℝ) ^ 2) * ((x : ℝ) ^ (-9 / 10 : ℝ) / σ ^ (3 * k)) := by ring
      _ ≤ (x : ℝ) ^ (9 / 100 : ℝ) * (x : ℝ) ^ (-89 / 100 : ℝ) :=
        mul_le_mul hcoef hratio (by positivity) (Real.rpow_nonneg hxpos.le _)
      _ = _ := by rw [← Real.rpow_add hxpos]; norm_num
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hsmall : 2 * (k : ℝ) ≤ 81 * (k : ℝ) ^ 2 := by nlinarith
  refine ⟨hloss, ?_⟩
  calc
    _ ≤ 2 * (k : ℝ) * (x : ℝ) ^ (-9 / 10 : ℝ) / σ ^ (3 * k) :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hσpos _)
        (pow_le_pow_of_le_one hσpos.le hσ1 (by omega))
    _ ≤ 81 * (k : ℝ) ^ 2 * (x : ℝ) ^ (-9 / 10 : ℝ) / σ ^ (3 * k) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hxpos.le _))
        (pow_nonneg hσpos.le _)
    _ ≤ _ := hloss

theorem eventually_growing_initial_error_budget :
    ∀ᶠ x : ℕ in atTop, ∀ β : ℝ,
      24 * UnitFourier.unitDensity (growingRandomValue x) ≤ β →
      let k := sieveDimension (growingIndex x)
      let σ := UnitFourier.unitDensity (growingRandomValue x)
      76 * (1 / Real.log (x : ℝ) ^ (80 : ℕ)) +
        4 * (k : ℝ) * (x : ℝ) ^ (-9 / 10 : ℝ) / (σ ^ (2 * k - 2) * β) +
        80 * (k : ℝ) ^ 2 * (x : ℝ) ^ (-9 / 10 : ℝ) / σ ^ (3 * k - 1) ≤
          1 / Real.log (x : ℝ) ^ (40 : ℕ) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_growing_initial_loss_bounds,
    growingDimension_tendsto.eventually (eventually_ge_atTop 1),
    eventually_const_log_power_le_rpow 40 2 (by norm_num : (0 : ℝ) < 4 / 5),
    hlog.eventually (eventually_ge_atTop 152), eventually_ge_atTop 1]
    with x hloss hk hpower hL hx
  let L := Real.log (x : ℝ)
  let k := sieveDimension (growingIndex x)
  let σ := UnitFourier.unitDensity (growingRandomValue x)
  change 152 ≤ L at hL
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hL1 : 1 ≤ L := by linarith
  have hL40 : 152 ≤ L ^ (40 : ℕ) := by
    apply hL.trans
    simpa only [pow_one] using pow_le_pow_right₀ hL1 (by norm_num : 1 ≤ (40 : ℕ))
  have hfirst : 76 / L ^ (80 : ℕ) ≤ 1 / (2 * L ^ (40 : ℕ)) := by
    apply (div_le_div_iff₀ (pow_pos hLpos 80) (by positivity : 0 < 2 * L ^ (40 : ℕ))).mpr
    have h80 : L ^ (80 : ℕ) = (L ^ (40 : ℕ)) ^ 2 := by rw [← pow_mul]
    rw [h80]
    nlinarith
  have hsecond : (x : ℝ) ^ (-4 / 5 : ℝ) ≤ 1 / (2 * L ^ (40 : ℕ)) := by
    calc
      _ = 1 / (x : ℝ) ^ (4 / 5 : ℝ) := by
        rw [show (-4 / 5 : ℝ) = -(4 / 5) by ring, Real.rpow_neg hxpos.le]
        simp only [one_div]
      _ ≤ _ := one_div_le_one_div_of_le (by positivity) hpower
  intro β hβ
  have he := initial_degree_error_le hk (UnitFourier.unitDensity_pos (growingRandomValue x))
    (sieve_unitDensity_le_one (growingRandomValue x)) (Real.rpow_nonneg hxpos.le (-9 / 10)) hβ
    (ε := 1 / L ^ (80 : ℕ))
  calc
    _ ≤ 76 * (1 / L ^ (80 : ℕ)) +
        81 * (k : ℝ) ^ 2 * (x : ℝ) ^ (-9 / 10 : ℝ) / σ ^ (3 * k) := he
    _ ≤ 76 / L ^ (80 : ℕ) + (x : ℝ) ^ (-4 / 5 : ℝ) := by
      simpa only [mul_one_div, k, σ] using
        add_le_add (le_refl (76 * (1 / L ^ (80 : ℕ)))) hloss.1
    _ ≤ 1 / (2 * L ^ (40 : ℕ)) + 1 / (2 * L ^ (40 : ℕ)) := add_le_add hfirst hsecond
    _ = _ := by change _ = 1 / L ^ (40 : ℕ); ring

end Erdos4.FGKMT
