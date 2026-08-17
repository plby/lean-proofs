import ErdosProblems.Erdos543.Asymptotics
import ErdosProblems.Erdos543.BonferroniAnalytic
import ErdosProblems.Erdos543.RankCountAsymptotics

/-!
# Asymptotic estimates for the Poisson step

This file packages the elementary analytic consequences of an
`o(log log N)` cutoff error.  We use the Bonferroni order
`floor ((log N)^(1/3)/3)`.  It is a fixed fraction of the available moment
range `momentRadius`, leaving room for both adjacent Bonferroni truncations.
-/

open Filter
open scoped Topology
open scoped Asymptotics

namespace Erdos543

noncomputable section

/-- The growing order at which the Bonferroni expansion is truncated. -/
def poissonCutoff (N : ℕ) : ℕ :=
  ⌊Real.log (N : ℝ) ^ ((1 : ℝ) / 3) / 3⌋₊

lemma tendsto_log_rpow_one_third_nat_atTop :
    Tendsto (fun N : ℕ ↦ Real.log (N : ℝ) ^ ((1 : ℝ) / 3)) atTop atTop := by
  exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
    tendsto_log_nat_atTop

lemma tendsto_log_rpow_one_third_div_three_nat_atTop :
    Tendsto (fun N : ℕ ↦ Real.log (N : ℝ) ^ ((1 : ℝ) / 3) / 3)
      atTop atTop :=
  tendsto_log_rpow_one_third_nat_atTop.atTop_div_const (by norm_num)

lemma tendsto_poissonCutoff_atTop :
    Tendsto poissonCutoff atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    tendsto_log_rpow_one_third_div_three_nat_atTop

lemma tendsto_poissonCutoff_cast_atTop :
    Tendsto (fun N : ℕ ↦ (poissonCutoff N : ℝ)) atTop atTop := by
  exact tendsto_natCast_atTop_atTop.comp tendsto_poissonCutoff_atTop

lemma poissonCutoff_cast_isEquivalent :
    ((fun N : ℕ ↦ (poissonCutoff N : ℝ)) ~[atTop]
      (fun N : ℕ ↦ Real.log (N : ℝ) ^ ((1 : ℝ) / 3) / 3)) := by
  simpa [poissonCutoff, Function.comp_def] using
    (Asymptotics.isEquivalent_nat_floor.comp_tendsto
      tendsto_log_rpow_one_third_div_three_nat_atTop)

/-- The collision parameter is negligible compared with the available
Bonferroni order. -/
lemma collisionParameter_isLittleO_poissonCutoff {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (nhds 0)) :
    (collisionParameter g) =o[atTop]
      (fun N : ℕ ↦ (poissonCutoff N : ℝ)) := by
  have hpow : (collisionParameter g) =o[atTop]
      (fun N : ℕ ↦ Real.log (N : ℝ) ^ ((1 : ℝ) / 3) / 3) := by
    simpa only [div_eq_mul_inv, mul_comm] using
      (collisionParameter_isLittleO_log_rpow_one_third hg).const_mul_right
        (by norm_num : (3 : ℝ)⁻¹ ≠ 0)
  exact hpow.trans_isEquivalent poissonCutoff_cast_isEquivalent.symm

/-- The square of the collision parameter is still negligible compared with
the Bonferroni half-order.  This is the quantitative input behind the
factorial-tail estimate. -/
lemma collisionParameter_sq_isLittleO_poissonCutoff {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (nhds 0)) :
    (fun N : ℕ ↦ collisionParameter g N ^ 2) =o[atTop]
      (fun N : ℕ ↦ (poissonCutoff N : ℝ)) := by
  have hsquare0 :=
    (collisionParameter_isBigO_log_rpow hg
      (ε := (1 : ℝ) / 12) (by norm_num)).pow 2
  have heq :
      (fun N : ℕ ↦ (Real.log (N : ℝ) ^ ((1 : ℝ) / 12)) ^ 2) =ᶠ[atTop]
        (fun N : ℕ ↦ Real.log (N : ℝ) ^ ((1 : ℝ) / 6)) := by
    filter_upwards
        [tendsto_log_nat_atTop.eventually (eventually_ge_atTop 0)] with N hlog
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlog]
    norm_num
  have hsquare : (fun N : ℕ ↦ collisionParameter g N ^ 2) =O[atTop]
      (fun N : ℕ ↦ Real.log (N : ℝ) ^ ((1 : ℝ) / 6)) :=
    hsquare0.congr' (Eventually.of_forall fun _ ↦ rfl) heq
  have hgap0 := isLittleO_log_rpow_log_rpow_nat
    (a := (1 : ℝ) / 6) (b := (1 : ℝ) / 3) (by norm_num)
  have hgap : (fun N : ℕ ↦ Real.log (N : ℝ) ^ ((1 : ℝ) / 6)) =o[atTop]
      (fun N : ℕ ↦ Real.log (N : ℝ) ^ ((1 : ℝ) / 3) / 3) := by
    simpa only [div_eq_mul_inv, mul_comm] using
      hgap0.const_mul_right (by norm_num : (3 : ℝ)⁻¹ ≠ 0)
  exact (hsquare.trans_isLittleO hgap).trans_isEquivalent
    poissonCutoff_cast_isEquivalent.symm

lemma eventually_collisionParameter_sq_le_mul_poissonCutoff {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (nhds 0))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop,
      collisionParameter g N ^ 2 ≤ epsilon * (poissonCutoff N : ℝ) := by
  have h := (collisionParameter_sq_isLittleO_poissonCutoff hg).bound hepsilon
  filter_upwards [h] with N hN
  rw [Real.norm_of_nonneg (sq_nonneg _),
    Real.norm_of_nonneg (show (0 : ℝ) ≤ poissonCutoff N by positivity)] at hN
  exact hN

/-- Eventual epsilon form of `collisionParameter_isLittleO_poissonCutoff`. -/
lemma eventually_collisionParameter_le_mul_poissonCutoff {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (nhds 0))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop,
      collisionParameter g N ≤ epsilon * (poissonCutoff N : ℝ) := by
  have h := (collisionParameter_isLittleO_poissonCutoff hg).bound hepsilon
  filter_upwards [h] with N hN
  rw [Real.norm_eq_abs, abs_of_nonneg (collisionParameter_nonneg g N)] at hN
  rw [Real.norm_of_nonneg (show (0 : ℝ) ≤ poissonCutoff N by positivity)] at hN
  exact hN

/-- The selected odd Bonferroni order lies in the rank-counting moment
range. -/
lemma eventually_two_mul_poissonCutoff_add_one_le_momentRadius :
    ∀ᶠ N : ℕ in atTop,
      2 * poissonCutoff N + 1 ≤ momentRadius N := by
  filter_upwards
      [tendsto_log_rpow_one_third_nat_atTop.eventually (eventually_ge_atTop 3)]
      with N hbase
  let x : ℝ := Real.log (N : ℝ) ^ ((1 : ℝ) / 3)
  have hx : 3 ≤ x := by simpa [x] using hbase
  have hcut : (poissonCutoff N : ℝ) ≤ x / 3 := by
    rw [poissonCutoff]
    exact Nat.floor_le (by linarith)
  rw [momentRadius]
  apply Nat.le_floor
  push_cast
  nlinarith

/-- In particular, the Poisson parameter is eventually no larger than the
chosen half-order (up to the harmless `+1` required by the Taylor bound). -/
lemma eventually_collisionParameter_le_poissonCutoff_add_one {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (nhds 0)) :
    ∀ᶠ N : ℕ in atTop,
      collisionParameter g N ≤ (poissonCutoff N + 1 : ℕ) := by
  filter_upwards [eventually_collisionParameter_le_mul_poissonCutoff hg
      (epsilon := 1) one_pos] with N hN
  norm_num at hN ⊢
  exact hN.trans (le_add_of_nonneg_right zero_le_one)

/-- Any fixed negative power of `N` dominates an exponential of a fixed
multiple of the collision parameter.  This is the form needed to absorb the
rank-stratification error after taking one or two target points. -/
lemma tendsto_rpow_neg_mul_exp_collisionParameter {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (nhds 0))
    (m : ℕ) {eta : ℝ} (heta : 0 < eta) :
    Tendsto (fun N : ℕ ↦
      (N : ℝ) ^ (-eta) *
        Real.exp ((2 * m : ℝ) * collisionParameter g N))
      atTop (nhds 0) := by
  let c : ℝ := eta / (4 * (m + 1 : ℝ))
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hb := (collisionParameter_isLittleO_log hg).bound hc
  have hupper : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-eta) *
          Real.exp ((2 * m : ℝ) * collisionParameter g N) ≤
        (N : ℝ) ^ (-(eta / 2)) := by
    filter_upwards [hb,
      tendsto_log_nat_atTop.eventually (eventually_gt_atTop 0),
      eventually_gt_atTop (0 : ℕ)] with N hbound hlog hN
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    rw [Real.norm_of_nonneg (collisionParameter_nonneg g N),
      Real.norm_of_nonneg hlog.le] at hbound
    have hmnonneg : (0 : ℝ) ≤ m := by positivity
    have hratio : (m : ℝ) / (m + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    have hexponent :
        -eta * Real.log (N : ℝ) +
            (2 * m : ℝ) * collisionParameter g N ≤
          -(eta / 2) * Real.log (N : ℝ) := by
      have hscaled :
          (2 * (m : ℝ)) * collisionParameter g N ≤
            (2 * (m : ℝ)) * (c * Real.log (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
      dsimp [c] at hscaled
      have hcoef :
          (2 * (m : ℝ)) * (eta / (4 * ((m : ℝ) + 1))) ≤ eta / 2 := by
        calc
          (2 * (m : ℝ)) * (eta / (4 * ((m : ℝ) + 1))) =
              (eta / 2) * ((m : ℝ) / (m + 1)) := by field_simp; ring
          _ ≤ (eta / 2) * 1 :=
            mul_le_mul_of_nonneg_left hratio (by positivity)
          _ = eta / 2 := mul_one _
      nlinarith [mul_le_mul_of_nonneg_right hcoef hlog.le]
    calc
      (N : ℝ) ^ (-eta) *
          Real.exp ((2 * m : ℝ) * collisionParameter g N) =
          Real.exp (-eta * Real.log (N : ℝ) +
            (2 * m : ℝ) * collisionParameter g N) := by
        rw [Real.rpow_def_of_pos hNreal, Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-(eta / 2) * Real.log (N : ℝ)) :=
        Real.exp_le_exp.mpr hexponent
      _ = (N : ℝ) ^ (-(eta / 2)) := by
        rw [Real.rpow_def_of_pos hNreal]
        congr 1
        ring
  apply squeeze_zero' (Eventually.of_forall fun N ↦ by positivity) hupper
  exact (tendsto_rpow_neg_atTop (by linarith : 0 < eta / 2)).comp
    tendsto_natCast_atTop_atTop

/-- The expected number of missed targets has the basic divergent scale
`N * exp (-lambda)`. -/
lemma tendsto_nat_mul_exp_neg_collisionParameter_atTop {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (nhds 0)) :
    Tendsto (fun N : ℕ ↦
      (N : ℝ) * Real.exp (-collisionParameter g N)) atTop atTop := by
  have hexp := eventually_exp_collisionParameter_le_rpow hg
    (δ := (1 : ℝ) / 2) (by norm_num)
  have hlower : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ ((1 : ℝ) / 2) ≤
        (N : ℝ) * Real.exp (-collisionParameter g N) := by
    filter_upwards [hexp, eventually_gt_atTop (0 : ℕ)] with N hExp hN
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    rw [Real.exp_neg]
    rw [le_mul_inv_iff₀ (Real.exp_pos _)]
    calc
      (N : ℝ) ^ ((1 : ℝ) / 2) *
          Real.exp (collisionParameter g N) ≤
          (N : ℝ) ^ ((1 : ℝ) / 2) *
            (N : ℝ) ^ ((1 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hExp (Real.rpow_nonneg hNreal.le _)
      _ = (N : ℝ) := by
        rw [← Real.rpow_add hNreal, show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num,
          Real.rpow_one]
  exact tendsto_atTop_mono' atTop hlower
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop)

/-- Sampling collisions disappear: the square of the rounded cutoff is
negligible compared with the ambient group size. -/
lemma tendsto_cutoffSize_sq_div_nat_zero {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (nhds 0)) :
    Tendsto (fun N : ℕ ↦ (cutoffSize g N : ℝ) ^ 2 / (N : ℝ))
      atTop (nhds 0) := by
  have hk : (fun N : ℕ ↦ (cutoffSize g N : ℝ) ^ 2) =O[atTop]
      (fun N : ℕ ↦ Real.log (N : ℝ) ^ 2) :=
    (cutoffSize_isBigO_log hg).pow 2
  have hlog : (fun N : ℕ ↦ Real.log (N : ℝ) ^ 2) =o[atTop]
      (fun N : ℕ ↦ (N : ℝ)) := by
    simpa only [Function.comp_def, Real.rpow_one, Real.rpow_ofNat] using
      (isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0 : ℝ) < 1)).comp_tendsto
        tendsto_natCast_atTop_atTop
  exact (hk.trans_isLittleO hlog).tendsto_div_nhds_zero

/-- The characteristic is eventually larger than every factorial occurring
in the moment range.  This is the rank-stability hypothesis used to compare
rational and finite-field ranks. -/
lemma eventually_momentRadius_factorial_lt_nat :
    ∀ᶠ N : ℕ in atTop, (momentRadius N).factorial < N := by
  filter_upwards
      [tendsto_log_rpow_one_third_nat_atTop.eventually (eventually_ge_atTop 2),
       tendsto_log_nat_atTop.eventually (eventually_gt_atTop 1),
       eventually_gt_atTop (0 : ℕ)] with N hbase hlog hN
  let L : ℝ := Real.log (N : ℝ)
  let x : ℝ := L ^ ((1 : ℝ) / 3)
  let R : ℕ := momentRadius N
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : 1 < L := by simpa [L] using hlog
  have hx : 2 ≤ x := by simpa [x, L] using hbase
  have hRle : (R : ℝ) ≤ x := by
    dsimp [R, momentRadius, x, L]
    exact Nat.floor_le (by positivity)
  have hRpos : 0 < R := by
    have : (1 : ℕ) ≤ R := by
      dsimp [R, momentRadius]
      apply Nat.le_floor
      simpa [x, L] using hx.trans' (by norm_num : (1 : ℝ) ≤ 2)
    omega
  have hlogR : Real.log (R : ℝ) ≤ (R : ℝ) := by
    exact (Real.log_le_sub_one_of_pos (by exact_mod_cast hRpos)).trans (by linarith)
  have hRsq : (R : ℝ) ^ 2 ≤ x ^ 2 := by
    exact pow_le_pow_left₀ (Nat.cast_nonneg R) hRle 2
  have hxsq : x ^ 2 = L ^ ((2 : ℝ) / 3) := by
    dsimp [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans hL.le)]
    norm_num
  have htwoThird : L ^ ((2 : ℝ) / 3) < L := by
    simpa only [Real.rpow_one] using
      Real.rpow_lt_rpow_of_exponent_lt hL (by norm_num : (2 : ℝ) / 3 < 1)
  have hpowlt : (R : ℝ) ^ R < (N : ℝ) := by
    calc
      (R : ℝ) ^ R = Real.exp ((R : ℝ) * Real.log (R : ℝ)) := by
        rw [Real.exp_nat_mul, Real.exp_log (by exact_mod_cast hRpos : (0 : ℝ) < R)]
      _ ≤ Real.exp ((R : ℝ) ^ 2) := by
        apply Real.exp_le_exp.mpr
        rw [pow_two]
        exact mul_le_mul_of_nonneg_left hlogR (Nat.cast_nonneg R)
      _ ≤ Real.exp (x ^ 2) := Real.exp_le_exp.mpr hRsq
      _ < Real.exp L := Real.exp_lt_exp.mpr (by simpa [hxsq] using htwoThird)
      _ = (N : ℝ) := by dsimp [L]; rw [Real.exp_log hNreal]
  have hfact : (R.factorial : ℝ) ≤ (R : ℝ) ^ R := by
    exact_mod_cast R.factorial_le_pow
  exact_mod_cast hfact.trans_lt hpowlt

/-- Every smaller moment order therefore also satisfies rank stability. -/
lemma eventually_factorial_lt_nat_of_le_momentRadius :
    ∀ᶠ N : ℕ in atTop, ∀ j : ℕ,
      j ≤ momentRadius N → j.factorial < N := by
  filter_upwards [eventually_momentRadius_factorial_lt_nat] with N hN
  intro j hj
  exact (Nat.factorial_le hj).trans_lt hN

end

end Erdos543
