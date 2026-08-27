import ErdosProblems.Erdos4.FGKMTPowerLevelEnvelope

/-! Natural conductor and modulus cutoffs on every sufficiently large endpoint. -/

namespace Erdos4.FGKMT

open Filter BoundedGaps.Maynard

noncomputable def exponentialConductorCutoff (a : ℝ) (x : ℕ) : ℕ :=
  ⌊Real.exp (a * Real.sqrt (Real.log (x : ℝ)))⌋₊

noncomputable def powerDistributionLevel (x : ℕ) : ℕ := ⌊vaughanCubeRoot x⌋₊

theorem eventually_distribution_cutoffs {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) :
    ∀ᶠ x : ℕ in atTop,
      1 ≤ x ∧ 2 ≤ exponentialConductorCutoff a x ∧
      exponentialConductorCutoff a x ≤ powerDistributionLevel x ∧
      (powerDistributionLevel x : ℝ) ≤ Real.sqrt (x : ℝ) ∧
      (exponentialConductorCutoff a x : ℝ) ≤ Real.exp (Real.sqrt (Real.log (x : ℝ)) / 2) ∧
      Real.exp (a * Real.sqrt (Real.log (x : ℝ))) / 2 ≤ (exponentialConductorCutoff a x : ℝ) ∧
      (exponentialConductorCutoff a x : ℝ) ≤ Real.exp (a * Real.sqrt (Real.log (x : ℝ))) ∧
      (powerDistributionLevel x : ℝ) ≤ vaughanCubeRoot x := by
  have hlarge₁ := sqrtLog_tendsto_atTop.eventually (eventually_ge_atTop (Real.log 2 / a))
  have hlarge₂ := sqrtLog_tendsto_atTop.eventually (eventually_ge_atTop (3 * a))
  filter_upwards [hlarge₁, hlarge₂, eventually_ge_atTop 1] with x hlarge₁ hlarge₂ hx
  let u := Real.sqrt (Real.log (x : ℝ))
  change Real.log 2 / a ≤ u at hlarge₁
  change 3 * a ≤ u at hlarge₂
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have husq : u ^ 2 = Real.log (x : ℝ) := Real.sq_sqrt (Real.log_natCast_nonneg x)
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hlog2 : Real.log 2 ≤ a * u := by
    have hh := (div_le_iff₀ ha0).mp hlarge₁
    nlinarith
  have hexp2 : 2 ≤ Real.exp (a * u) := by
    calc
      _ = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlog2
  have hR2 : 2 ≤ exponentialConductorCutoff a x := Nat.le_floor hexp2
  have hRhi : (exponentialConductorCutoff a x : ℝ) ≤ Real.exp (a * u) :=
    Nat.floor_le (Real.exp_pos _).le
  have hRlo : Real.exp (a * u) / 2 ≤ (exponentialConductorCutoff a x : ℝ) := by
    have hfloor := Nat.lt_floor_add_one (Real.exp (a * u))
    have hRreal : (2 : ℝ) ≤ exponentialConductorCutoff a x := by exact_mod_cast hR2
    change Real.exp (a * u) < (exponentialConductorCutoff a x : ℝ) + 1 at hfloor
    linarith
  have hexpCube : Real.exp (a * u) ≤ vaughanCubeRoot x := by
    calc
      _ ≤ Real.exp (Real.log (x : ℝ) * (1 / 3 : ℝ)) := by
        apply Real.exp_le_exp.mpr
        have hh := mul_nonneg (sub_nonneg.mpr hlarge₂) hu
        rw [← husq]
        nlinarith
      _ = _ := by
        change Real.exp (Real.log (x : ℝ) * (1 / 3 : ℝ)) = (x : ℝ) ^ (1 / 3 : ℝ)
        exact (Real.rpow_def_of_pos hxpos (1 / 3 : ℝ)).symm
  have hRQ : exponentialConductorCutoff a x ≤ powerDistributionLevel x := Nat.floor_mono hexpCube
  have hQhi : (powerDistributionLevel x : ℝ) ≤ vaughanCubeRoot x := Nat.floor_le (vaughanCubeRoot_nonneg x)
  have hCubeSqrt : vaughanCubeRoot x ≤ Real.sqrt (x : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    change (x : ℝ) ^ (1 / 3 : ℝ) ≤ (x : ℝ) ^ (1 / 2 : ℝ)
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hRheight : (exponentialConductorCutoff a x : ℝ) ≤ Real.exp (u / 2) := by
    apply hRhi.trans
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right ha1 hu
    nlinarith
  exact ⟨hx, hR2, hRQ, hQhi.trans hCubeSqrt, hRheight, hRlo, hRhi, hQhi⟩

end Erdos4.FGKMT
