import ErdosProblems.Erdos157b.JointTargetFailure

/-! Summable joint failure bounds after counting all integers in a level window. -/

namespace Erdos157.Binary

open Elementary Filter
open scoped Topology

theorem eventually_quadratic_sub_fourth_le_neg (C : ℝ) :
    ∀ᶠ k : ℕ in atTop, C * (k : ℝ) ^ 2 - (k : ℝ) ^ 4 / 1024 ≤ -(k : ℝ) := by
  have ht : Tendsto (fun k : ℕ => (k : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop (1024 * (C + 1))),
    eventually_ge_atTop 1] with k hk h1
  have h1' : (1 : ℝ) ≤ k := by exact_mod_cast h1
  have hm := mul_le_mul_of_nonneg_right hk (sq_nonneg (k : ℝ))
  nlinarith

theorem eventually_quadratic_sub_two_pow_le_neg (C : ℝ) :
    ∀ᶠ k : ℕ in atTop, C * (k : ℝ) ^ 2 - (2 : ℝ) ^ k ≤ -(k : ℝ) := by
  have h2 := (tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : (1 : ℝ) < 2)).const_mul C
  have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 2)
  have ht : Tendsto (fun k : ℕ => (C * (k : ℝ) ^ 2 + k) / (2 : ℝ) ^ k) atTop (𝓝 0) := by
    convert h2.add h1 using 1
    · ext k
      simp only [pow_one]
      ring
    · simp
  filter_upwards [ht.eventually (gt_mem_nhds zero_lt_one)] with k hk
  have hp : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hh := (div_lt_iff₀ hp).mp hk
  linarith

theorem eventually_window_bound_decay :
    ∀ᶠ k in atTop,
      (6 * blockPlace CoefficientField 0 (k + 1) : ℝ) * targetFailureBound k ≤
        2 * Real.exp (-(k : ℝ)) := by
  let C : ℝ := 10 * Real.log 2
  filter_upwards [eventually_windowCount_dyadic,
    eventually_quadratic_sub_fourth_le_neg C,
    eventually_quadratic_sub_two_pow_le_neg C] with k hc hfour htwo
  have hcount : (6 * blockPlace CoefficientField 0 (k + 1) : ℝ) ≤
      Real.exp (C * (k : ℝ) ^ 2) := by
    have hn : (6 * blockPlace CoefficientField 0 (k + 1) : ℝ) ≤
        (2 : ℝ) ^ (10 * k ^ 2) := by exact_mod_cast hc
    have he : (2 : ℝ) ^ (10 * k ^ 2) = Real.exp (C * (k : ℝ) ^ 2) := by
      rw [show C * (k : ℝ) ^ 2 = ((10 * k ^ 2 : ℕ) : ℝ) * Real.log 2 by
        dsimp only [C]; push_cast; ring, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact hn.trans_eq he
  have hfirst : (6 * blockPlace CoefficientField 0 (k + 1) : ℝ) *
      Real.exp (-(k : ℝ) ^ 4 / 1024) ≤ Real.exp (-(k : ℝ)) := by
    calc
      _ ≤ Real.exp (C * (k : ℝ) ^ 2) * Real.exp (-(k : ℝ) ^ 4 / 1024) :=
        mul_le_mul_of_nonneg_right hcount (Real.exp_nonneg _)
      _ = Real.exp (C * (k : ℝ) ^ 2 - (k : ℝ) ^ 4 / 1024) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr hfour
  have hsecond : (6 * blockPlace CoefficientField 0 (k + 1) : ℝ) *
      Real.exp (-(2 : ℝ) ^ k) ≤ Real.exp (-(k : ℝ)) := by
    calc
      _ ≤ Real.exp (C * (k : ℝ) ^ 2) * Real.exp (-(2 : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_right hcount (Real.exp_nonneg _)
      _ = Real.exp (C * (k : ℝ) ^ 2 - (2 : ℝ) ^ k) := by rw [← Real.exp_add, sub_eq_add_neg]
      _ ≤ _ := Real.exp_le_exp.mpr htwo
  unfold targetFailureBound
  rw [mul_add]
  linarith

noncomputable def JointWindowFailure (k : ℕ)
    (x : LevelMasks CoefficientField k × LevelParameters CoefficientField k) : Prop :=
  ∃ m : Fin (6 * blockPlace CoefficientField 0 (k + 1)),
    6 * blockPlace CoefficientField 0 k ≤ m.1 ∧ JointTargetFailure CoefficientField k m.1 x

theorem eventually_joint_window_failure :
    ∀ᶠ k in atTop, finiteDensity (JointWindowFailure k) ≤ 2 * Real.exp (-(k : ℝ)) := by
  classical
  filter_upwards [eventually_joint_target_failure, eventually_window_bound_decay] with k hk hd
  have hbound (m : Fin (6 * blockPlace CoefficientField 0 (k + 1))) :
      finiteDensity (fun x : LevelMasks CoefficientField k × LevelParameters CoefficientField k =>
        6 * blockPlace CoefficientField 0 k ≤ m.1 ∧ JointTargetFailure CoefficientField k m.1 x) ≤
        targetFailureBound k := by
    by_cases hm : 6 * blockPlace CoefficientField 0 k ≤ m.1
    · exact (finiteDensity_mono (fun _ h => h.2)).trans (hk m hm m.2)
    · have he : finiteDensity (fun x : LevelMasks CoefficientField k × LevelParameters CoefficientField k =>
          6 * blockPlace CoefficientField 0 k ≤ m.1 ∧ JointTargetFailure CoefficientField k m.1 x) = 0 := by
        letI : IsEmpty {x : LevelMasks CoefficientField k × LevelParameters CoefficientField k //
            6 * blockPlace CoefficientField 0 k ≤ m.1 ∧ JointTargetFailure CoefficientField k m.1 x} :=
          ⟨fun x => hm x.2.1⟩
        unfold finiteDensity
        rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero, Nat.cast_zero, zero_div]
      rw [he]
      exact targetFailureBound_nonneg k
  have hb := finiteDensity_exists_le _ (targetFailureBound k) hbound
  have hcount : finiteDensity (JointWindowFailure k) ≤
      (6 * blockPlace CoefficientField 0 (k + 1) : ℝ) * targetFailureBound k := by
    change finiteDensity (fun x : LevelMasks CoefficientField k × LevelParameters CoefficientField k =>
      ∃ m : Fin (6 * blockPlace CoefficientField 0 (k + 1)),
        6 * blockPlace CoefficientField 0 k ≤ m.1 ∧ JointTargetFailure CoefficientField k m.1 x) ≤ _
    simpa only [Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat] using hb
  exact hcount.trans hd

end Erdos157.Binary
