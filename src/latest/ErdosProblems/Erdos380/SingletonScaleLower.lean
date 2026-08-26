import ErdosProblems.Erdos380.LowerCost
import ErdosProblems.Erdos380.SingletonLower

/-! # An unconditional singleton lower bound at the integer scale -/

open Filter
open scoped Topology

namespace Erdos380

lemma lowerTotalExponent_pow_le {N : ℕ} (hN : 1 ≤ N) :
    2 ^ lowerTotalExponent N ≤ N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hf := Nat.floor_le (show 0 ≤ (1 / Real.log 2) * Real.log (N : ℝ) by positivity)
  change (lowerTotalExponent N : ℝ) ≤ (1 / Real.log 2) * Real.log (N : ℝ) at hf
  have hm := mul_le_mul_of_nonneg_right hf log_two_pos.le
  have hid : (1 / Real.log 2) * Real.log (N : ℝ) * Real.log 2 = Real.log (N : ℝ) := by field_simp
  rw [hid] at hm
  have hp : (0 : ℝ) < (2 : ℝ) ^ lowerTotalExponent N := by positivity
  have hreal : (2 : ℝ) ^ lowerTotalExponent N ≤ N := by
    apply (Real.log_le_log_iff hp hNpos).mp
    rwa [Real.log_pow]
  exact_mod_cast hreal

theorem eventually_lower_exponent_hypotheses (Y₀ : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      Y₀ ≤ lowerPrimeExponent N ∧ 1 ≤ lowerPrimeExponent N ∧ 1 ≤ lowerSmoothParameter N ∧
      4 ≤ ε * lowerPrimeExponent N ∧
      8 * (lowerSmoothExponent N : ℝ) ≤ ε * (lowerPrimeExponent N : ℝ) ^ 2 ∧
      Real.log (20 * lowerPrimeExponent N : ℝ) ≤
        (1 + ε) * Real.log (lowerSmoothParameter N) := by
  have hYcast : Tendsto (fun N => (lowerPrimeExponent N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp lowerPrimeExponent_tendsto_atTop
  filter_upwards [lowerPrimeExponent_tendsto_atTop.eventually (eventually_ge_atTop (max Y₀ 1)),
    hYcast.eventually (eventually_ge_atTop (4 / ε)),
    lowerSmoothParameter_tendsto_atTop.eventually (eventually_ge_atTop (2 : ℝ)),
    lowerSmoothExponent_div_prime_sq_tendsto_zero.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 8)),
    lowerPrimeExponent_log_budget_ratio.eventually (gt_mem_nhds (by linarith : (1 : ℝ) < 1 + ε))]
      with N hY hεY hu hXY hlog
  have hY1 : 1 ≤ lowerPrimeExponent N := (le_max_right _ _).trans hY
  have hYpos : (0 : ℝ) < lowerPrimeExponent N := by exact_mod_cast (by omega : 0 < lowerPrimeExponent N)
  have hlogu : 0 < Real.log (lowerSmoothParameter N) := Real.log_pos (by linarith)
  refine ⟨(le_max_left _ _).trans hY, hY1, by linarith, ?_, ?_, ?_⟩
  · have h := (div_le_iff₀ hε).mp hεY
    linarith
  · have h := (div_le_iff₀ (pow_pos hYpos 2)).mp hXY.le
    linarith
  · exact (div_le_iff₀ hlogu).mp hlog.le

noncomputable def dyadicSingletonLower (ε : ℝ) (N : ℕ) : ℝ :=
  (2 : ℝ) ^ (lowerSmoothExponent N + lowerPrimeExponent N) *
    Real.exp (-(1 + 3 * ε) * lowerSmoothParameter N * Real.log (lowerSmoothParameter N)) /
      (10 * lowerPrimeExponent N)

lemma dyadicSingletonLower_pos {N : ℕ} (hY : 1 ≤ lowerPrimeExponent N) (ε : ℝ) :
    0 < dyadicSingletonLower ε N := by
  have hYpos : (0 : ℝ) < lowerPrimeExponent N := by exact_mod_cast (by omega : 0 < lowerPrimeExponent N)
  unfold dyadicSingletonLower
  positivity

lemma log_dyadicSingletonLower {N : ℕ} (hY : 1 ≤ lowerPrimeExponent N) (ε : ℝ) :
    Real.log (dyadicSingletonLower ε N) =
      (lowerSmoothExponent N + lowerPrimeExponent N : ℕ) * Real.log 2 -
        (1 + 3 * ε) * lowerSmoothParameter N * Real.log (lowerSmoothParameter N) -
          Real.log (10 * lowerPrimeExponent N : ℝ) := by
  have hYpos : (0 : ℝ) < lowerPrimeExponent N := by exact_mod_cast (by omega : 0 < lowerPrimeExponent N)
  unfold dyadicSingletonLower
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_pow, Real.log_exp]
  ring

theorem eventually_dyadicSingletonLower_le_count {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᶠ N : ℕ in atTop, dyadicSingletonLower ε N ≤ ((singletonBadUpTo N).card : ℝ) := by
  obtain ⟨Y₀, hbound⟩ := exists_singletonBadUpTo_dyadic_exponential_lower
  filter_upwards [eventually_lower_exponent_hypotheses Y₀ hε,
    eventually_lowerExponent_padding_le, eventually_ge_atTop 1] with N hparams hpad hN
  obtain ⟨hY₀, hY1, hu, hεY, hXY, hlog⟩ := hparams
  have hY0 : (lowerPrimeExponent N : ℝ) ≠ 0 := by exact_mod_cast (by omega : lowerPrimeExponent N ≠ 0)
  have hX : (lowerSmoothExponent N : ℝ) = lowerSmoothParameter N * lowerPrimeExponent N := by
    rw [lowerSmoothParameter, div_mul_cancel₀ _ hY0]
  have h := hbound (lowerSmoothExponent N) (lowerPrimeExponent N) hY₀ ε (lowerSmoothParameter N)
    hε hε1 hu hX hεY hXY hlog
  have hsize : 2 ^ (lowerSmoothExponent N + 2 * (lowerPrimeExponent N + 1)) ≤ N := by
    rw [lowerSmoothExponent, Nat.sub_add_cancel hpad]
    exact lowerTotalExponent_pow_le hN
  have hmono : (singletonBadUpTo (2 ^ (lowerSmoothExponent N + 2 * (lowerPrimeExponent N + 1)))).card ≤
      (singletonBadUpTo N).card := by
    apply Finset.card_le_card
    intro n hn
    obtain ⟨hn1, hnsize, hnbad⟩ := mem_singletonBadUpTo.mp hn
    exact mem_singletonBadUpTo.mpr ⟨hn1, hnsize.trans hsize, hnbad⟩
  exact h.trans (by exact_mod_cast hmono)

/-- The lower bound needed to normalize every remaining error term. -/
theorem eventually_singletonBadUpTo_scale_lower : ∀ᶠ N : ℕ in atTop,
    (N : ℝ) / (scaleBase N : ℝ) ^ 2001 ≤ ((singletonBadUpTo N).card : ℝ) := by
  let ε : ℝ := 1 / 10000
  have hε : 0 < ε := by norm_num [ε]
  have hε1 : ε ≤ 1 := by norm_num [ε]
  have hlim := lowerSingletonCost_tendsto ε
  have hgap : 2000 + 3000 * ε < (2001 : ℝ) := by norm_num [ε]
  filter_upwards [eventually_dyadicSingletonLower_le_count hε hε1,
    hlim.eventually (gt_mem_nhds hgap),
    lowerPrimeExponent_tendsto_atTop.eventually (eventually_ge_atTop 1),
    log_scaleBase_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_ge_atTop 1] with N hcount hcost hY hS hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hSpos : (0 : ℝ) < scaleBase N := by exact_mod_cast
    (lt_of_lt_of_le Nat.zero_lt_one (one_le_scaleBase N))
  have hcost' := (div_le_iff₀ hS).mp hcost.le
  have hlower : (N : ℝ) / (scaleBase N : ℝ) ^ 2001 ≤ dyadicSingletonLower ε N := by
    apply (Real.log_le_log_iff (div_pos hNpos (pow_pos hSpos 2001)) (dyadicSingletonLower_pos hY ε)).mp
    rw [Real.log_div hNpos.ne' (pow_ne_zero 2001 hSpos.ne'), Real.log_pow,
      log_dyadicSingletonLower hY ε]
    norm_num only [Nat.cast_ofNat]
    change Real.log (N : ℝ) - (lowerSmoothExponent N + lowerPrimeExponent N : ℕ) * Real.log 2 +
      (1 + 3 * ε) * lowerSmoothParameter N * Real.log (lowerSmoothParameter N) +
        Real.log (10 * lowerPrimeExponent N : ℝ) ≤ 2001 * Real.log (scaleBase N : ℝ) at hcost'
    norm_num [ε] at hcost' ⊢
    linarith
  exact hlower.trans hcount

end Erdos380
