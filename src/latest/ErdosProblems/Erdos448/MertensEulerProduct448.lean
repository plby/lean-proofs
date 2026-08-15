import UnitFractions.ForMathlib.BasicEstimates

open Asymptotics Filter Finset Real
open scoped BigOperators Topology

namespace Erdos448

/-! A sharp-enough consequence of the formalized second Mertens theorem. -/

lemma eventually_prime_reciprocal_sum_le_loglog_add_one :
    ∀ᶠ N : ℕ in atTop,
      (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (p : ℝ)⁻¹) ≤
        Real.log (Real.log (N : ℝ)) + meissel_mertens + 1 := by
  obtain ⟨c, hc⟩ := prime_reciprocal.bound
  have hcnat := tendsto_natCast_atTop_atTop.eventually hc
  have hlarge : ∀ᶠ N : ℕ in atTop,
      max 1 |c| ≤ Real.log (N : ℝ) :=
    tendsto_log_coe_at_top.eventually_ge_atTop (max 1 |c|)
  filter_upwards [hcnat, hlarge] with N hN hlog
  have hlogpos : 0 < Real.log (N : ℝ) :=
    zero_lt_one.trans_le ((le_max_left 1 |c|).trans hlog)
  have hnorm_inv : ‖(Real.log (N : ℝ))⁻¹‖ = (Real.log (N : ℝ))⁻¹ :=
    norm_of_nonneg (inv_nonneg.mpr hlogpos.le)
  have hc_le_log : c ≤ Real.log (N : ℝ) :=
    (le_abs_self c).trans ((le_max_right 1 |c|).trans hlog)
  have hmul : c * ‖(Real.log (N : ℝ))⁻¹‖ ≤ 1 := by
    rw [hnorm_inv]
    change c / Real.log (N : ℝ) ≤ 1
    exact (div_le_one hlogpos).2 hc_le_log
  have herr :
      prime_summatory (fun p : ℕ => (p : ℝ)⁻¹) 1 (N : ℝ) -
          (Real.log (Real.log (N : ℝ)) + meissel_mertens) ≤ 1 :=
    (le_norm_self _).trans (hN.trans hmul)
  simpa [prime_summatory] using (sub_le_iff_le_add'.mp herr)

lemma sum_Icc_two_inv_mul_pred_eq {N : ℕ} (hN : 2 ≤ N) :
    (∑ n ∈ Finset.Icc 2 N,
        (((n : ℝ) * ((n : ℝ) - 1))⁻¹)) = 1 - (N : ℝ)⁻¹ := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hmem : n + 1 ∉ Finset.Icc 2 n := by simp
      have hIcc : Finset.Icc 2 (n + 1) = insert (n + 1) (Finset.Icc 2 n) := by
        ext m
        simp
        omega
      rw [hIcc, Finset.sum_insert hmem, ih]
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hspos : (0 : ℝ) < n + 1 := by positivity
      push_cast
      field_simp [hnpos.ne', hspos.ne']
      ring

lemma prime_correction_sum_le_one (N : ℕ) :
    (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        (((p : ℝ) * ((p : ℝ) - 1))⁻¹)) ≤ 1 := by
  classical
  by_cases hN : 2 ≤ N
  · have hsub : (Finset.Icc 1 N).filter Nat.Prime ⊆ Finset.Icc 2 N := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      exact Finset.mem_Icc.mpr ⟨hp'.2.two_le, (Finset.mem_Icc.mp hp'.1).2⟩
    calc
      (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
          (((p : ℝ) * ((p : ℝ) - 1))⁻¹))
          ≤ ∑ n ∈ Finset.Icc 2 N, (((n : ℝ) * ((n : ℝ) - 1))⁻¹) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
            intro n hn _
            have hn' := Finset.mem_Icc.mp hn
            have hncast : (2 : ℝ) ≤ n := by exact_mod_cast hn'.1
            exact inv_nonneg.mpr
              (mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr (by linarith)))
      _ = 1 - (N : ℝ)⁻¹ := sum_Icc_two_inv_mul_pred_eq hN
      _ ≤ 1 := sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg N))
  · have hNle : N ≤ 1 := by omega
    have hempty : (Finset.Icc 1 N).filter Nat.Prime = ∅ := by
      ext p
      constructor
      · intro hp
        have hp' := Finset.mem_filter.mp hp
        have hp2 := hp'.2.two_le
        have hpN := (Finset.mem_Icc.mp hp'.1).2
        omega
      · intro hp
        simp at hp
    simp [hempty]

lemma half_inv_pred_eq (p : ℕ) (hp : Nat.Prime p) :
    (2 * ((p : ℝ) - 1))⁻¹ =
      (1 / 2 : ℝ) * ((p : ℝ)⁻¹ + ((p : ℝ) * ((p : ℝ) - 1))⁻¹) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    linarith
  field_simp [hp0, hp1]
  ring

lemma half_prime_pred_sum_le (N : ℕ) :
    (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        (2 * ((p : ℝ) - 1))⁻¹) ≤
      (1 / 2 : ℝ) *
          (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (p : ℝ)⁻¹) + 1 / 2 := by
  calc
    (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        (2 * ((p : ℝ) - 1))⁻¹)
        = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
            (1 / 2 : ℝ) *
              ((p : ℝ)⁻¹ + ((p : ℝ) * ((p : ℝ) - 1))⁻¹) := by
            apply Finset.sum_congr rfl
            intro p hp
            exact half_inv_pred_eq p (Finset.mem_filter.mp hp).2
    _ = (1 / 2 : ℝ) *
          (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (p : ℝ)⁻¹) +
        (1 / 2 : ℝ) *
          (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
            ((p : ℝ) * ((p : ℝ) - 1))⁻¹) := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ (1 / 2 : ℝ) *
          (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (p : ℝ)⁻¹) +
        (1 / 2 : ℝ) * 1 := by
          gcongr
          exact prime_correction_sum_le_one N
    _ = (1 / 2 : ℝ) *
          (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (p : ℝ)⁻¹) + 1 / 2 := by ring

lemma finite_product_one_add_le_exp_sum
    (s : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ n ∈ s, 0 ≤ f n) :
    s.prod (fun n => 1 + f n) ≤ Real.exp (s.sum f) := by
  calc
    s.prod (fun n => 1 + f n) ≤ s.prod (fun n => Real.exp (f n)) := by
      exact Finset.prod_le_prod
        (fun n hn => add_nonneg zero_le_one (hf n hn))
        (fun n hn => by simpa [add_comm] using Real.add_one_le_exp (f n))
    _ = Real.exp (s.sum f) := by rw [← Real.exp_sum]

noncomputable def mertensHalfEulerConstant : ℝ :=
  Real.exp (meissel_mertens / 2 + 1)

lemma mertensHalfEulerConstant_pos : 0 < mertensHalfEulerConstant := by
  exact Real.exp_pos _

theorem eventually_prime_half_euler_product_le :
    ∀ᶠ N : ℕ in atTop,
      ((Finset.Icc 1 N).filter Nat.Prime).prod
          (fun p => 1 + (2 * ((p : ℝ) - 1))⁻¹) ≤
        mertensHalfEulerConstant * Real.sqrt (Real.log (N : ℝ)) := by
  filter_upwards [eventually_prime_reciprocal_sum_le_loglog_add_one,
      tendsto_log_coe_at_top.eventually_gt_atTop 0] with N hrec hlogpos
  let S := (Finset.Icc 1 N).filter Nat.Prime
  let w : ℕ → ℝ := fun p => (2 * ((p : ℝ) - 1))⁻¹
  have hw : ∀ p ∈ S, 0 ≤ w p := by
    intro p hp
    have hp' : (1 : ℝ) < p := by
      exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
    dsimp [w]
    positivity
  have hsum : S.sum w ≤
      (1 / 2 : ℝ) * Real.log (Real.log (N : ℝ)) +
        (meissel_mertens / 2 + 1) := by
    have hhalf := half_prime_pred_sum_le N
    dsimp [S, w]
    calc
      (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
          (2 * ((p : ℝ) - 1))⁻¹)
          ≤ (1 / 2 : ℝ) *
              (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (p : ℝ)⁻¹) + 1 / 2 :=
            hhalf
      _ ≤ (1 / 2 : ℝ) *
              (Real.log (Real.log (N : ℝ)) + meissel_mertens + 1) + 1 / 2 := by
            gcongr
      _ = (1 / 2 : ℝ) * Real.log (Real.log (N : ℝ)) +
            (meissel_mertens / 2 + 1) := by ring
  have hprod : S.prod (fun p => 1 + w p) ≤ Real.exp (S.sum w) :=
    finite_product_one_add_le_exp_sum S w hw
  have hexp : Real.exp (S.sum w) ≤
      Real.exp ((1 / 2 : ℝ) * Real.log (Real.log (N : ℝ)) +
        (meissel_mertens / 2 + 1)) := Real.exp_le_exp.mpr hsum
  have hsqrt :
      Real.exp ((1 / 2 : ℝ) * Real.log (Real.log (N : ℝ))) =
        Real.sqrt (Real.log (N : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hlogpos]
    congr 1
    ring
  calc
    ((Finset.Icc 1 N).filter Nat.Prime).prod
        (fun p => 1 + (2 * ((p : ℝ) - 1))⁻¹)
        = S.prod (fun p => 1 + w p) := rfl
    _ ≤ Real.exp (S.sum w) := hprod
    _ ≤ Real.exp ((1 / 2 : ℝ) * Real.log (Real.log (N : ℝ)) +
        (meissel_mertens / 2 + 1)) := hexp
    _ = mertensHalfEulerConstant * Real.sqrt (Real.log (N : ℝ)) := by
      rw [Real.exp_add, hsqrt]
      simp [mertensHalfEulerConstant, mul_comm]

theorem exists_prime_half_euler_product_threshold :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ((Finset.Icc 1 N).filter Nat.Prime).prod
          (fun p => 1 + (2 * ((p : ℝ) - 1))⁻¹) ≤
        mertensHalfEulerConstant * Real.sqrt (Real.log (N : ℝ)) := by
  exact eventually_atTop.1 eventually_prime_half_euler_product_le

end Erdos448
