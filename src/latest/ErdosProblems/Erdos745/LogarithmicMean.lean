import ErdosProblems.Erdos745.LogarithmicScale
import ErdosProblems.Erdos745.FixedTreeMean

/-! # Diverging tree-component means below the logarithmic threshold -/

open Filter
open scoped BigOperators Topology

namespace Erdos745

noncomputable section

theorem fallingProduct_lower_linear {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    1 - (k : ℝ) ^ 2 / n ≤ fallingProduct n k := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkR : (k : ℝ) ≤ n := by exact_mod_cast hk
  have hkn : (k : ℝ) / n ≤ 1 := (div_le_one hnR).mpr hkR
  calc
    _ = 1 + (k : ℝ) * (-(k : ℝ) / n) := by ring
    _ ≤ (1 + (-(k : ℝ) / n)) ^ k :=
      one_add_mul_le_pow (by rw [neg_div]; linarith) k
    _ = ∏ _i ∈ Finset.range k, (1 - (k : ℝ) / n) := by
      simp only [Finset.prod_const, Finset.card_range, neg_div, sub_eq_add_neg]
    _ ≤ fallingProduct n k := by
      apply Finset.prod_le_prod (fun _ _ ↦ by linarith)
      intro i hi
      have hiR : (i : ℝ) ≤ k := by exact_mod_cast (Finset.mem_range.mp hi).le
      have hd := div_le_div_of_nonneg_right hiR hnR.le
      linarith

theorem eventually_fallingProduct_log_lower {B : ℝ} (hB : 0 ≤ B) :
    ∀ᶠ n : ℕ in atTop, (1 : ℝ) / 2 ≤ fallingProduct n (logarithmicOrder B n) := by
  filter_upwards [eventually_logarithmicOrder_le_half hB,
    (tendsto_logarithmicOrder_pow_div hB 2).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    eventually_ge_atTop 1] with n hkn hsq hn
  have hf := fallingProduct_lower_linear (by omega : 0 < n)
    (show logarithmicOrder B n ≤ n by omega)
  linarith

theorem tree_absence_lower_of_log {n k : ℕ} (hn : 0 < n) (hk : 2 ≤ k) (hkn : k ≤ n)
    {lam u : ℝ} (hu : 0 ≤ u) (hln : lam < n)
    (hlog : -u ≤ (n : ℝ) * Real.log (1 - lam / n)) :
    Real.exp (-u * k) ≤
      (1 - lam / (n : ℝ)) ^ (n.choose 2 - (n - k).choose 2 - (k - 1)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hq : 0 < 1 - lam / (n : ℝ) := sub_pos.mpr ((div_lt_one hnR).mpr hln)
  let b := n.choose 2 - (n - k).choose 2 - (k - 1)
  have hb : (b : ℝ) / n ≤ k := (div_le_iff₀ hnR).mpr (tree_absent_count_le_mul hk hkn)
  have hl := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ (b : ℝ) / n)
  have heq : (b : ℝ) / n * ((n : ℝ) * Real.log (1 - lam / n)) =
      (b : ℝ) * Real.log (1 - lam / n) := by field_simp
  rw [heq] at hl
  have he : -u * (k : ℝ) ≤ (b : ℝ) * Real.log (1 - lam / n) := by
    have hm := mul_le_mul_of_nonneg_left hb hu
    nlinarith
  calc
    _ ≤ Real.exp ((b : ℝ) * Real.log (1 - lam / n)) := Real.exp_le_exp.mpr he
    _ = _ := by rw [Real.exp_nat_mul, Real.exp_log hq]

theorem factorial_le_exp_mul {k : ℕ} (hk : 0 < k) :
    (k.factorial : ℝ) ≤ Real.exp 1 * k * ((k : ℝ) / Real.exp 1) ^ k := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hs : Real.sqrt (k : ℝ) ≤ k := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    nlinarith
  exact (factorial_le_exp_sqrt hk).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le)
      (by positivity))

theorem logarithmic_prefactor_identity {k : ℕ} (hk : 2 ≤ k) {lam : ℝ} (hlam : 0 < lam)
    (n u : ℝ) :
    (n * ((k : ℝ) ^ (k - 2) * lam ^ (k - 1)) /
      (Real.exp 1 * k * ((k : ℝ) / Real.exp 1) ^ k)) *
        ((1 : ℝ) / 2 * Real.exp (-u * k)) =
      n / (2 * Real.exp 1 * lam * (k : ℝ) ^ 3) *
        Real.exp (-(u - 1 - Real.log lam) * k) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hpow : (k : ℝ) ^ k = (k : ℝ) ^ (k - 2) * (k : ℝ) ^ 2 := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  have hlamPow : lam ^ k = lam ^ (k - 1) * lam := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
  have he : Real.exp (-(u - 1 - Real.log lam) * k) =
      Real.exp (-u * k) * (Real.exp 1 ^ k * lam ^ k) := by
    rw [show -(u - 1 - Real.log lam) * k = -u * k +
      ((k : ℝ) * 1 + (k : ℝ) * Real.log lam) by ring,
      Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log hlam]
  rw [he, hlamPow, div_pow, hpow]
  field_simp

theorem treeMean_lower_of_log {n k : ℕ} (hn : 0 < n) (hk : 2 ≤ k) (hkn : k ≤ n)
    {lam u : ℝ} (hlam : 0 < lam) (hu : 0 ≤ u) (hln : lam < n)
    (hlog : -u ≤ (n : ℝ) * Real.log (1 - lam / n))
    (hfall : (1 : ℝ) / 2 ≤ fallingProduct n k) :
    (n : ℝ) / (2 * Real.exp 1 * lam * (k : ℝ) ^ 3) *
      Real.exp (-(u - 1 - Real.log lam) * k) ≤ treeMean lam n k := by
  have hk0 : 0 < k := by omega
  have hcount : (k : ℝ) ^ (k - 2) ≤ labelledTreeCount k := by
    exact_mod_cast labelledTreeCount_lower hk
  have hpref : (n : ℝ) * ((k : ℝ) ^ (k - 2) * lam ^ (k - 1)) /
      (Real.exp 1 * k * ((k : ℝ) / Real.exp 1) ^ k) ≤
        (n : ℝ) * ((labelledTreeCount k : ℝ) * lam ^ (k - 1)) / k.factorial := by
    apply le_trans (div_le_div_of_nonneg_left (by positivity) (by positivity)
      (factorial_le_exp_mul hk0))
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hcount (pow_nonneg hlam.le _)) (Nat.cast_nonneg _))
        (by positivity)
  have habs := tree_absence_lower_of_log hn hk hkn hu hln hlog
  have hprod : (1 : ℝ) / 2 * Real.exp (-u * k) ≤
      fallingProduct n k * (1 - lam / (n : ℝ)) ^
        (n.choose 2 - (n - k).choose 2 - (k - 1)) :=
    mul_le_mul hfall habs (Real.exp_pos _).le (by linarith)
  have h := mul_le_mul hpref hprod (by positivity) (by positivity)
  rw [logarithmic_prefactor_identity hk hlam n u] at h
  apply h.trans_eq
  have he := treeMean_div_eq_product hn hk0 hkn hlam.le hln.le
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  apply (div_left_inj' hnR).mp
  rw [he]
  field_simp

theorem eventually_treeMean_log_lower {lam B : ℝ} (hlam : 0 < lam) (hne : lam ≠ 1)
    (hB : 0 < B) (hBa : B < logarithmicConstant lam) :
    ∃ γ : ℝ, 0 < γ ∧ B * γ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      (n : ℝ) / (2 * Real.exp 1 * lam * (logarithmicOrder B n : ℝ) ^ 3) *
        Real.exp (-γ * logarithmicOrder B n) ≤ treeMean lam n (logarithmicOrder B n) := by
  have hα := logarithmicDecay_pos hlam hne
  have hBα : B * logarithmicDecay lam < 1 := by
    apply (lt_div_iff₀ hα).mp
    simpa only [logarithmicConstant, one_div] using hBa
  have hαB : logarithmicDecay lam < 1 / B := (lt_div_iff₀ hB).mpr (by nlinarith)
  let η := (1 / B - logarithmicDecay lam) / 2
  have hη : 0 < η := by dsimp [η]; linarith
  have hγ : 0 < logarithmicDecay lam + η := by positivity
  have hBγ : B * (logarithmicDecay lam + η) < 1 := by
    have hc : B * (1 / B) = 1 := by field_simp
    dsimp [η]
    nlinarith
  refine ⟨logarithmicDecay lam + η, hγ, hBγ, ?_⟩
  filter_upwards [eventually_fallingProduct_log_lower hB.le,
    eventually_logarithmicOrder_le_half hB.le,
    (tendsto_logarithmicOrder hB).eventually_ge_atTop 2,
    (tendsto_n_mul_log_absence lam).eventually
      (lt_mem_nhds (by linarith : -(lam + η) < -lam)),
    eventually_ge_atTop 1,
    tendsto_natCast_atTop_atTop.eventually_gt_atTop lam] with n hfall hkn hk hlog hn hln
  have hk' : 2 ≤ logarithmicOrder B n := by exact_mod_cast hk
  have he := treeMean_lower_of_log (by omega : 0 < n) hk' (by omega)
    hlam (show 0 ≤ lam + η by positivity) hln hlog.le hfall
  convert he using 1
  congr 2
  dsimp [logarithmicDecay]
  ring

theorem exp_logarithmicOrder_div_le {n : ℕ} (hn : 0 < n) {B γ : ℝ}
    (hB : 0 ≤ B) (hγ : 0 ≤ γ) :
    Real.exp (γ * logarithmicOrder B n) / n ≤
      Real.exp γ * Real.exp (-(1 - B * γ) * Real.log (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hr := Nat.ceil_lt_add_one (mul_nonneg hB (Real.log_nonneg hn1))
  change (logarithmicOrder B n : ℝ) < B * Real.log (n : ℝ) + 1 at hr
  rw [← Real.exp_add, ← Real.exp_log hnR, ← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_left hr.le hγ
  rw [Real.log_exp]
  nlinarith

theorem tendsto_inverse_logarithmic_envelope {lam B γ : ℝ} (hlam : 0 ≤ lam)
    (hB : 0 ≤ B) (hγ : 0 ≤ γ) (hBγ : B * γ < 1) :
    Tendsto (fun n : ℕ ↦
      (2 * Real.exp 1 * lam * (logarithmicOrder B n : ℝ) ^ 3) / n *
        Real.exp (γ * logarithmicOrder B n)) atTop (𝓝 0) := by
  have ht := (tendsto_log_pow_mul_exp (show 0 < 1 - B * γ by linarith) 3).const_mul
    (2 * Real.exp 1 * lam * (B + 1) ^ 3 * Real.exp γ)
  simp only [mul_zero] at ht
  apply squeeze_zero' (Eventually.of_forall fun n ↦ by positivity) _ ht
  filter_upwards [eventually_logarithmicOrder_le hB, eventually_ge_atTop 1] with n hk hn
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (logarithmicOrder B n)) hk 3
  calc
    _ = (2 * Real.exp 1 * lam) * (logarithmicOrder B n : ℝ) ^ 3 *
        (Real.exp (γ * logarithmicOrder B n) / n) := by ring
    _ ≤ (2 * Real.exp 1 * lam) * ((B + 1) * Real.log (n : ℝ)) ^ 3 *
        (Real.exp γ * Real.exp (-(1 - B * γ) * Real.log (n : ℝ))) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity))
        (exp_logarithmicOrder_div_le (by omega) hB hγ) (by positivity)
      have hh := (Nat.cast_nonneg (logarithmicOrder B n)).trans hk
      positivity
    _ = _ := by rw [mul_pow]; ring

theorem eventually_treeMean_log_pos {lam B : ℝ} (hlam : 0 < lam) (hne : lam ≠ 1)
    (hB : 0 < B) (hBa : B < logarithmicConstant lam) :
    ∀ᶠ n : ℕ in atTop, 0 < treeMean lam n (logarithmicOrder B n) := by
  obtain ⟨γ, _, _, hb⟩ := eventually_treeMean_log_lower hlam hne hB hBa
  filter_upwards [hb, (tendsto_logarithmicOrder hB).eventually_gt_atTop 0,
    eventually_ge_atTop 1] with n hn hk hn1
  exact lt_of_lt_of_le (by positivity) hn

theorem tendsto_inverse_treeMean_log {lam B : ℝ} (hlam : 0 < lam) (hne : lam ≠ 1)
    (hB : 0 < B) (hBa : B < logarithmicConstant lam) :
    Tendsto (fun n : ℕ ↦ 1 / treeMean lam n (logarithmicOrder B n)) atTop (𝓝 0) := by
  obtain ⟨γ, hγ, hBγ, hb⟩ := eventually_treeMean_log_lower hlam hne hB hBa
  apply squeeze_zero' (Eventually.of_forall fun n ↦ div_nonneg zero_le_one (treeMean_nonneg _ _ _))
    _ (tendsto_inverse_logarithmic_envelope hlam.le hB.le hγ.le hBγ)
  filter_upwards [hb, (tendsto_logarithmicOrder hB).eventually_gt_atTop 0,
    eventually_ge_atTop 1] with n hn hk hn1
  have hlower : 0 < (n : ℝ) / (2 * Real.exp 1 * lam * (logarithmicOrder B n : ℝ) ^ 3) *
      Real.exp (-γ * logarithmicOrder B n) := by positivity
  have hi := one_div_le_one_div_of_le hlower hn
  apply hi.trans_eq
  rw [neg_mul, Real.exp_neg]
  field_simp

theorem eventually_treeMean_log_ge_two {lam B : ℝ} (hlam : 0 < lam) (hne : lam ≠ 1)
    (hB : 0 < B) (hBa : B < logarithmicConstant lam) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ treeMean lam n (logarithmicOrder B n) := by
  filter_upwards [eventually_treeMean_log_pos hlam hne hB hBa,
    (tendsto_inverse_treeMean_log hlam hne hB hBa).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with n hm hi
  have hh := (div_lt_iff₀ hm).mp hi
  linarith

end

end Erdos745
