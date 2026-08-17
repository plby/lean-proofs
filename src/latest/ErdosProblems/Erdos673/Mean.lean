import ErdosProblems.Erdos448.HalberstamComplete448
import ErdosProblems.Erdos448.MertensEulerProduct448

open scoped BigOperators Topology
open Asymptotics Filter Finset

/-!
Analytic helper estimates for Erdős Problem 673.  The main file supplies the
ordered-divisor statistic and applies the weighted deficit theorem proved here.
-/

namespace Erdos673Mean

noncomputable def sqrtTau (n : ℕ) : ℝ :=
  Real.sqrt (n.divisors.card : ℝ)

@[simp] lemma sqrtTau_zero : sqrtTau 0 = 0 := by
  simp [sqrtTau]

@[simp] lemma sqrtTau_one : sqrtTau 1 = 1 := by
  norm_num [sqrtTau]

lemma sqrtTau_nonneg (n : ℕ) : 0 ≤ sqrtTau n :=
  Real.sqrt_nonneg _

lemma sqrtTau_mul {m n : ℕ} (hmn : m.Coprime n) :
    sqrtTau (m * n) = sqrtTau m * sqrtTau n := by
  rw [sqrtTau, sqrtTau, sqrtTau, hmn.card_divisors_mul, Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg _)]

lemma nat_succ_le_nine_four_pow : ∀ j : ℕ,
    ((j + 1 : ℕ) : ℝ) ≤ (9 / 4 : ℝ) ^ j := by
  intro j
  induction j with
  | zero => norm_num
  | succ j ih =>
      rw [pow_succ]
      calc
        ((j + 1 + 1 : ℕ) : ℝ) ≤ (9 / 4 : ℝ) * (j + 1 : ℕ) := by
          push_cast
          nlinarith [show (0 : ℝ) ≤ (j : ℝ) by positivity]
        _ ≤ (9 / 4 : ℝ) * (9 / 4 : ℝ) ^ j := by
          exact mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (9 / 4 : ℝ) ^ j * (9 / 4 : ℝ) := by ring

lemma sqrt_nat_succ_le_three_halves_pow (j : ℕ) :
    Real.sqrt ((j + 1 : ℕ) : ℝ) ≤ (3 / 2 : ℝ) ^ j := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  calc
    ((j + 1 : ℕ) : ℝ) ≤ (9 / 4 : ℝ) ^ j := nat_succ_le_nine_four_pow j
    _ = ((3 / 2 : ℝ) ^ j) ^ 2 := by
      rw [show (9 / 4 : ℝ) = (3 / 2 : ℝ) ^ 2 by norm_num,
        ← pow_mul, ← pow_mul, Nat.mul_comm]

lemma sqrtTau_prime_pow {p j : ℕ} (hp : p.Prime) :
    sqrtTau (p ^ j) = Real.sqrt ((j + 1 : ℕ) : ℝ) := by
  rw [sqrtTau, ← ArithmeticFunction.sigma_zero_apply,
    ArithmeticFunction.sigma_zero_apply_prime_pow hp]

lemma sqrtTau_prime_pow_succ {p : ℕ} (hp : p.Prime) (j : ℕ) :
    sqrtTau (p ^ (j + 1)) ≤ (3 / 2 : ℝ) * (3 / 2 : ℝ) ^ j := by
  rw [sqrtTau_prime_pow hp]
  simpa [pow_succ'] using sqrt_nat_succ_le_three_halves_pow (j + 1)

lemma sqrtTau_local_summable {p : ℕ} (hp : p.Prime) :
    Summable (fun j : ℕ =>
      sqrtTau (p ^ j) / ((p ^ j : ℕ) : ℝ)) := by
  have hnorm := (HalberstamScratch.prime_power_local_mass
    sqrtTau p (3 / 2) (3 / 2) hp sqrtTau_nonneg sqrtTau_one
    (by norm_num) (by norm_num) (by norm_num)
    (sqrtTau_prime_pow_succ hp)).1
  exact hnorm.of_norm

lemma sqrtTau_local_split {p : ℕ} (hp : p.Prime) :
    (∑' j : ℕ, sqrtTau (p ^ j) / ((p ^ j : ℕ) : ℝ)) =
      1 + Real.sqrt 2 / (p : ℝ) +
        ∑' j : ℕ, sqrtTau (p ^ (j + 2)) / ((p ^ (j + 2) : ℕ) : ℝ) := by
  let f : ℕ → ℝ := fun j => sqrtTau (p ^ j) / ((p ^ j : ℕ) : ℝ)
  have hf : Summable f := sqrtTau_local_summable hp
  rw [← hf.sum_add_tsum_nat_add 2]
  change (∑ i ∈ Finset.range 2, f i) + ∑' i : ℕ, f (i + 2) = _
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  norm_num [f, sqrtTau_prime_pow hp, Nat.add_comm]
  apply tsum_congr
  intro i
  congr 2
  ring

lemma sqrtTau_local_tail_le {p : ℕ} (hp : p.Prime) :
    (∑' j : ℕ, sqrtTau (p ^ (j + 2)) / ((p ^ (j + 2) : ℕ) : ℝ)) ≤
      (9 : ℝ) / (p : ℝ) ^ 2 := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  let r : ℝ := (3 / 2 : ℝ) / p
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := by
    dsimp [r]
    exact (div_lt_one hpR).2 ((show (3 / 2 : ℝ) < 2 by norm_num).trans_le hpTwo)
  have hmajor : Summable (fun j : ℕ => r ^ (j + 2)) := by
    exact ((summable_geometric_of_lt_one hr0 hr1).mul_left (r ^ 2)).congr
      (fun j => by rw [pow_add]; ring)
  have hpoint : ∀ j : ℕ,
      sqrtTau (p ^ (j + 2)) / ((p ^ (j + 2) : ℕ) : ℝ) ≤ r ^ (j + 2) := by
    intro j
    calc
      sqrtTau (p ^ (j + 2)) / ((p ^ (j + 2) : ℕ) : ℝ)
          = Real.sqrt (((j + 2 + 1 : ℕ) : ℝ)) /
              ((p ^ (j + 2) : ℕ) : ℝ) := by rw [sqrtTau_prime_pow hp]
      _ ≤ (3 / 2 : ℝ) ^ (j + 2) / ((p ^ (j + 2) : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right
          (sqrt_nat_succ_le_three_halves_pow (j + 2)) (by positivity)
      _ = r ^ (j + 2) := by
        dsimp [r]
        rw [Nat.cast_pow, ← div_pow]
  have htail : Summable (fun j : ℕ =>
      sqrtTau (p ^ (j + 2)) / ((p ^ (j + 2) : ℕ) : ℝ)) :=
    (summable_nat_add_iff 2).2 (sqrtTau_local_summable hp)
  calc
    (∑' j : ℕ, sqrtTau (p ^ (j + 2)) / ((p ^ (j + 2) : ℕ) : ℝ)) ≤
        ∑' j : ℕ, r ^ (j + 2) := htail.tsum_le_tsum hpoint hmajor
    _ = r ^ 2 / (1 - r) := by
      rw [show (fun j : ℕ => r ^ (j + 2)) = fun j => r ^ 2 * r ^ j by
        funext j; rw [pow_add]; ring]
      rw [tsum_mul_left, (hasSum_geometric_of_lt_one hr0 hr1).tsum_eq]
      ring
    _ ≤ 9 / (p : ℝ) ^ 2 := by
      dsimp [r]
      have hden : 0 < 1 - (3 / 2 : ℝ) / p := by
        rw [sub_pos]
        exact (div_lt_one hpR).2
          ((show (3 / 2 : ℝ) < 2 by norm_num).trans_le hpTwo)
      rw [div_le_iff₀ hden]
      have hpne : (p : ℝ) ≠ 0 := hpR.ne'
      field_simp [hpne]
      nlinarith

lemma sqrt_two_le_seventeen_twelfths :
    Real.sqrt 2 ≤ (17 / 12 : ℝ) := by
  rw [Real.sqrt_le_iff]
  norm_num

lemma sqrtTau_localFactor_le {p : ℕ} (hp : p.Prime) :
    (∑' j : ℕ, sqrtTau (p ^ j) / ((p ^ j : ℕ) : ℝ)) ≤
      1 + (17 / 12 : ℝ) / p + 9 / (p : ℝ) ^ 2 := by
  rw [sqrtTau_local_split hp]
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hfirst := div_le_div_of_nonneg_right sqrt_two_le_seventeen_twelfths hpR.le
  have htail := sqrtTau_local_tail_le hp
  linarith

lemma primesBelow_succ_eq_primeIcc (N : ℕ) :
    (N + 1).primesBelow = (Finset.Icc 1 N).filter Nat.Prime := by
  ext p
  rw [Nat.mem_primesBelow, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hpN, hp⟩
    exact ⟨⟨hp.one_le, Nat.le_of_lt_succ hpN⟩, hp⟩
  · rintro ⟨⟨_hp1, hpN⟩, hp⟩
    exact ⟨Nat.lt_succ_of_le hpN, hp⟩

lemma prime_inv_sq_le_correction {p : ℕ} (hp : p.Prime) :
    1 / (p : ℝ) ^ 2 ≤ (((p : ℝ) * ((p : ℝ) - 1))⁻¹) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hpOne : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hden : 0 < (p : ℝ) * ((p : ℝ) - 1) :=
    mul_pos hpR (sub_pos.mpr hpOne)
  simpa only [one_div] using
    (one_div_le_one_div_of_le hden (by nlinarith) :
      1 / (p : ℝ) ^ 2 ≤ 1 / ((p : ℝ) * ((p : ℝ) - 1)))

lemma sum_prime_inv_sq_le_one (N : ℕ) :
    (∑ p ∈ (N + 1).primesBelow, 1 / (p : ℝ) ^ 2) ≤ 1 := by
  rw [primesBelow_succ_eq_primeIcc]
  calc
    (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, 1 / (p : ℝ) ^ 2) ≤
        ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
          (((p : ℝ) * ((p : ℝ) - 1))⁻¹) := by
      apply Finset.sum_le_sum
      intro p hp
      exact prime_inv_sq_le_correction (Finset.mem_filter.mp hp).2
    _ ≤ 1 := Erdos448.prime_correction_sum_le_one N

lemma sqrtTau_eulerProduct_nonneg (N : ℕ) :
    0 ≤ ∏ p ∈ (N + 1).primesBelow,
      ∑' j : ℕ, sqrtTau (p ^ j) / ((p ^ j : ℕ) : ℝ) := by
  apply Finset.prod_nonneg
  intro p hp
  exact tsum_nonneg fun j =>
    div_nonneg (sqrtTau_nonneg _) (by positivity)

lemma sqrtTau_eulerProduct_le_exp (N : ℕ) :
    (∏ p ∈ (N + 1).primesBelow,
      ∑' j : ℕ, sqrtTau (p ^ j) / ((p ^ j : ℕ) : ℝ)) ≤
      Real.exp ((17 / 12 : ℝ) *
          (∑ p ∈ (N + 1).primesBelow, (p : ℝ)⁻¹) + 9) := by
  let S := (N + 1).primesBelow
  let u : ℕ → ℝ := fun p => (17 / 12 : ℝ) / p + 9 / (p : ℝ) ^ 2
  have hu : ∀ p ∈ S, 0 ≤ u p := by
    intro p hp
    dsimp [u]
    positivity
  have hfactor :
      (∏ p ∈ S, ∑' j : ℕ,
        sqrtTau (p ^ j) / ((p ^ j : ℕ) : ℝ)) ≤
        ∏ p ∈ S, (1 + u p) := by
    apply Finset.prod_le_prod
    · intro p hp
      exact tsum_nonneg fun j =>
        div_nonneg (sqrtTau_nonneg _) (by positivity)
    · intro p hp
      simpa only [u, add_assoc] using
        (sqrtTau_localFactor_le (Nat.prime_of_mem_primesBelow hp))
  have hsum :
      (∑ p ∈ S, u p) ≤
        (17 / 12 : ℝ) * (∑ p ∈ S, (p : ℝ)⁻¹) + 9 := by
    have hsquare := sum_prime_inv_sq_le_one N
    calc
      (∑ p ∈ S, u p) =
          (17 / 12 : ℝ) * (∑ p ∈ S, (p : ℝ)⁻¹) +
            9 * (∑ p ∈ S, 1 / (p : ℝ) ^ 2) := by
        dsimp [u]
        simp_rw [div_eq_mul_inv]
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        simp
      _ ≤ (17 / 12 : ℝ) * (∑ p ∈ S, (p : ℝ)⁻¹) + 9 * 1 := by
        gcongr
      _ = (17 / 12 : ℝ) * (∑ p ∈ S, (p : ℝ)⁻¹) + 9 := by ring
  calc
    (∏ p ∈ (N + 1).primesBelow,
        ∑' j : ℕ, sqrtTau (p ^ j) / ((p ^ j : ℕ) : ℝ)) ≤
        ∏ p ∈ S, (1 + u p) := hfactor
    _ ≤ Real.exp (∑ p ∈ S, u p) :=
      Erdos448.finite_product_one_add_le_exp_sum S u hu
    _ ≤ Real.exp ((17 / 12 : ℝ) *
        (∑ p ∈ (N + 1).primesBelow, (p : ℝ)⁻¹) + 9) := by
      exact Real.exp_le_exp.mpr hsum

noncomputable def sqrtTauEulerConstant : ℝ :=
  Real.exp ((17 / 12 : ℝ) * (meissel_mertens + 1) + 9)

lemma sqrtTauEulerConstant_pos : 0 < sqrtTauEulerConstant :=
  Real.exp_pos _

theorem eventually_sqrtTau_eulerProduct_le :
    ∀ᶠ N : ℕ in atTop,
      (∏ p ∈ (N + 1).primesBelow,
        ∑' j : ℕ, sqrtTau (p ^ j) / ((p ^ j : ℕ) : ℝ)) ≤
        sqrtTauEulerConstant *
          (Real.log (N : ℝ)).rpow (17 / 12 : ℝ) := by
  filter_upwards [Erdos448.eventually_prime_reciprocal_sum_le_loglog_add_one,
      tendsto_log_coe_at_top.eventually_gt_atTop 0] with N hrec hlog
  have hraw := sqrtTau_eulerProduct_le_exp N
  have hsumEq :
      (∑ p ∈ (N + 1).primesBelow, (p : ℝ)⁻¹) =
        ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (p : ℝ)⁻¹ := by
    rw [primesBelow_succ_eq_primeIcc]
  calc
    (∏ p ∈ (N + 1).primesBelow,
        ∑' j : ℕ, sqrtTau (p ^ j) / ((p ^ j : ℕ) : ℝ)) ≤
        Real.exp ((17 / 12 : ℝ) *
          (∑ p ∈ (N + 1).primesBelow, (p : ℝ)⁻¹) + 9) := hraw
    _ =
        Real.exp ((17 / 12 : ℝ) *
          (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (p : ℝ)⁻¹) + 9) := by
      rw [hsumEq]
    _ ≤ Real.exp ((17 / 12 : ℝ) *
        (Real.log (Real.log (N : ℝ)) + meissel_mertens + 1) + 9) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = sqrtTauEulerConstant *
        (Real.log (N : ℝ)).rpow (17 / 12 : ℝ) := by
      unfold sqrtTauEulerConstant
      change Real.exp _ = Real.exp _ * (Real.log (N : ℝ)) ^ (17 / 12 : ℝ)
      rw [Real.rpow_def_of_pos hlog, ← Real.exp_add]
      congr 1
      ring

noncomputable def sqrtTauMeanConstant : ℝ :=
  (HalberstamScratch.explicitMassConstant (3 / 2) (3 / 2) + 1) *
    sqrtTauEulerConstant

lemma sqrtTauMeanConstant_pos : 0 < sqrtTauMeanConstant := by
  unfold sqrtTauMeanConstant
  have hmass := HalberstamScratch.explicitMassConstant_nonneg
    (show (0 : ℝ) ≤ 3 / 2 by norm_num)
    (show (0 : ℝ) ≤ 3 / 2 by norm_num)
  exact mul_pos (by linarith) sqrtTauEulerConstant_pos

theorem eventually_partialSum_sqrtTau_le :
    ∀ᶠ N : ℕ in atTop,
      HalberstamScratch.partialSum sqrtTau N ≤
        sqrtTauMeanConstant * (N : ℝ) *
          (Real.log (N : ℝ)).rpow (5 / 12 : ℝ) := by
  filter_upwards [eventually_sqrtTau_eulerProduct_le,
      eventually_ge_atTop (2 : ℕ),
      tendsto_log_coe_at_top.eventually_gt_atTop 0] with N heuler hN hlog
  have hHR := HalberstamComplete448.halberstam_richert_explicit
    sqrtTau sqrtTau_zero sqrtTau_one
    (fun {_m _n} hmn => sqrtTau_mul hmn) sqrtTau_nonneg
    (3 / 2) (3 / 2) (by norm_num) (by norm_num) (by norm_num)
    (fun p hp j => sqrtTau_prime_pow_succ hp j) N hN
  have hcoeff :
      0 ≤ (HalberstamScratch.explicitMassConstant (3 / 2) (3 / 2) + 1) *
        (N : ℝ) / Real.log (N : ℝ) := by
    have hmass := HalberstamScratch.explicitMassConstant_nonneg
      (show (0 : ℝ) ≤ 3 / 2 by norm_num)
      (show (0 : ℝ) ≤ 3 / 2 by norm_num)
    positivity
  calc
    HalberstamScratch.partialSum sqrtTau N ≤
        (HalberstamScratch.explicitMassConstant (3 / 2) (3 / 2) + 1) *
          (N : ℝ) / Real.log (N : ℝ) *
            ∏ p ∈ (N + 1).primesBelow,
              ∑' j : ℕ, sqrtTau (p ^ j) / ((p ^ j : ℕ) : ℝ) := hHR
    _ ≤ (HalberstamScratch.explicitMassConstant (3 / 2) (3 / 2) + 1) *
          (N : ℝ) / Real.log (N : ℝ) *
            (sqrtTauEulerConstant *
              (Real.log (N : ℝ)).rpow (17 / 12 : ℝ)) :=
      mul_le_mul_of_nonneg_left heuler hcoeff
    _ = sqrtTauMeanConstant * (N : ℝ) *
          (Real.log (N : ℝ)).rpow (5 / 12 : ℝ) := by
      unfold sqrtTauMeanConstant
      have hrpow :
          (Real.log (N : ℝ)).rpow (17 / 12 : ℝ) /
              Real.log (N : ℝ) =
            (Real.log (N : ℝ)).rpow (5 / 12 : ℝ) := by
        calc
          (Real.log (N : ℝ)).rpow (17 / 12 : ℝ) /
              Real.log (N : ℝ) =
              (Real.log (N : ℝ)).rpow (17 / 12 : ℝ) /
                (Real.log (N : ℝ)).rpow 1 := by
            congr 1
            exact (Real.rpow_one _).symm
          _ = (Real.log (N : ℝ)).rpow ((17 / 12 : ℝ) - 1) :=
            (Real.rpow_sub hlog (17 / 12 : ℝ) 1).symm
          _ = (Real.log (N : ℝ)).rpow (5 / 12 : ℝ) := by norm_num
      rw [show
        (HalberstamScratch.explicitMassConstant (3 / 2) (3 / 2) + 1) *
            (N : ℝ) / Real.log (N : ℝ) *
              (sqrtTauEulerConstant *
                (Real.log (N : ℝ)).rpow (17 / 12 : ℝ)) =
          ((HalberstamScratch.explicitMassConstant (3 / 2) (3 / 2) + 1) *
            sqrtTauEulerConstant) * (N : ℝ) *
              ((Real.log (N : ℝ)).rpow (17 / 12 : ℝ) /
                Real.log (N : ℝ)) by ring,
        hrpow]

theorem sqrtTau_partialSum_isBigO :
    (fun N : ℕ => HalberstamScratch.partialSum sqrtTau N) =O[atTop]
      (fun N : ℕ => (N : ℝ) *
        (Real.log (N : ℝ)).rpow (5 / 12 : ℝ)) := by
  refine IsBigO.of_bound sqrtTauMeanConstant ?_
  filter_upwards [eventually_partialSum_sqrtTau_le,
      eventually_ge_atTop (2 : ℕ)] with N hN hNtwo
  have hsum : 0 ≤ HalberstamScratch.partialSum sqrtTau N := by
    exact Finset.sum_nonneg fun n hn => sqrtTau_nonneg n
  have hlog : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hbase : 0 ≤ (N : ℝ) * (Real.log (N : ℝ)).rpow (5 / 12 : ℝ) :=
    mul_nonneg (Nat.cast_nonneg N) (Real.rpow_nonneg hlog _)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hsum,
    abs_of_nonneg hbase]
  simpa [mul_assoc] using hN

lemma rpow_five_twelfths_isLittleO_rpow_one :
    (fun x : ℝ => x.rpow (5 / 12 : ℝ)) =o[atTop]
      (fun x : ℝ => x.rpow 1) := by
  rw [isLittleO_iff_tendsto']
  · apply (tendsto_rpow_neg_atTop (show (0 : ℝ) < 7 / 12 by norm_num)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    convert Real.rpow_sub hx (5 / 12 : ℝ) 1 using 1 <;> norm_num
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx hzero
    exact ((Real.rpow_pos_of_pos hx _).ne' hzero).elim

lemma log_rpow_five_twelfths_isLittleO_log :
    (fun N : ℕ => (Real.log (N : ℝ)).rpow (5 / 12 : ℝ)) =o[atTop]
      (fun N : ℕ => Real.log (N : ℝ)) := by
  have h := rpow_five_twelfths_isLittleO_rpow_one.comp_tendsto
    tendsto_log_coe_at_top
  exact h.congr' (Filter.Eventually.of_forall fun _ => rfl)
    (Filter.Eventually.of_forall fun N => Real.rpow_one _)

lemma mean_model_isLittleO :
    (fun N : ℕ => (N : ℝ) *
      (Real.log (N : ℝ)).rpow (5 / 12 : ℝ)) =o[atTop]
      (fun N : ℕ => (N : ℝ) * Real.log (N : ℝ)) := by
  exact (isBigO_refl (fun N : ℕ => (N : ℝ)) atTop).mul_isLittleO
    log_rpow_five_twelfths_isLittleO_log

theorem sqrtTau_partialSum_isLittleO :
    (fun N : ℕ => HalberstamScratch.partialSum sqrtTau N) =o[atTop]
      (fun N : ℕ => (N : ℝ) * Real.log (N : ℝ)) :=
  sqrtTau_partialSum_isBigO.trans_isLittleO mean_model_isLittleO

theorem deficit_partialSum_isLittleO
    (D : ℕ → ℝ)
    (hDnonneg : ∀ n, 0 ≤ D n)
    (hDle : ∀ n, D n ≤ sqrtTau n) :
    (fun N : ℕ => HalberstamScratch.partialSum D N) =o[atTop]
      (fun N : ℕ => (N : ℝ) * Real.log (N : ℝ)) := by
  have hDsumO :
      (fun N : ℕ => HalberstamScratch.partialSum D N) =O[atTop]
        (fun N : ℕ => HalberstamScratch.partialSum sqrtTau N) := by
    refine IsBigO.of_bound 1 (Eventually.of_forall ?_)
    intro N
    have hsumD : 0 ≤ HalberstamScratch.partialSum D N :=
      Finset.sum_nonneg fun n hn => hDnonneg n
    have hsumSqrt : 0 ≤ HalberstamScratch.partialSum sqrtTau N :=
      Finset.sum_nonneg fun n hn => sqrtTau_nonneg n
    have hle : HalberstamScratch.partialSum D N ≤
        HalberstamScratch.partialSum sqrtTau N := by
      exact Finset.sum_le_sum fun n hn => hDle n
    simpa [Real.norm_eq_abs, abs_of_nonneg hsumD, abs_of_nonneg hsumSqrt]
      using hle
  exact hDsumO.trans_isLittleO sqrtTau_partialSum_isLittleO

lemma sqrt_one_add_log_le
    {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) (hN : 3 ≤ N) :
    Real.sqrt (1 + Real.log (n : ℝ)) ≤
      Real.sqrt 2 * (Real.log (N : ℝ)).rpow (1 / 2 : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnNR : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have hlogle : Real.log (n : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by positivity) hnNR
  have hlogOne : 1 ≤ Real.log (N : ℝ) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have h3R : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    exact Real.exp_one_lt_d9.le.trans
      ((by norm_num : (2.7182818286 : ℝ) ≤ 3).trans h3R)
  have hinside : 1 + Real.log (n : ℝ) ≤ 2 * Real.log (N : ℝ) := by
    linarith
  calc
    Real.sqrt (1 + Real.log (n : ℝ)) ≤
        Real.sqrt (2 * Real.log (N : ℝ)) := Real.sqrt_le_sqrt hinside
    _ = Real.sqrt 2 * Real.sqrt (Real.log (N : ℝ)) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    _ = Real.sqrt 2 * (Real.log (N : ℝ)).rpow (1 / 2 : ℝ) := by
      congr 1
      change Real.sqrt (Real.log (N : ℝ)) =
        (Real.log (N : ℝ)) ^ (1 / 2 : ℝ)
      exact Real.sqrt_eq_rpow _

theorem eventually_weighted_deficit_partialSum_le
    (D : ℕ → ℝ)
    (_hDnonneg : ∀ n, 0 ≤ D n)
    (hDle : ∀ n,
      D n ≤ sqrtTau n * Real.sqrt (1 + Real.log (n : ℝ))) :
    ∀ᶠ N : ℕ in atTop,
      HalberstamScratch.partialSum D N ≤
        (Real.sqrt 2 * sqrtTauMeanConstant) * (N : ℝ) *
          (Real.log (N : ℝ)).rpow (11 / 12 : ℝ) := by
  filter_upwards [eventually_partialSum_sqrtTau_le,
      eventually_ge_atTop (3 : ℕ)] with N hsqrt hN
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  let w : ℝ := Real.sqrt 2 * (Real.log (N : ℝ)).rpow (1 / 2 : ℝ)
  have hw : 0 ≤ w := mul_nonneg (Real.sqrt_nonneg _)
    (Real.rpow_nonneg hlog.le _)
  have hsum : HalberstamScratch.partialSum D N ≤
      w * HalberstamScratch.partialSum sqrtTau N := by
    unfold HalberstamScratch.partialSum
    calc
      (∑ n ∈ Finset.Icc 1 N, D n) ≤
          ∑ n ∈ Finset.Icc 1 N, sqrtTau n * w := by
        apply Finset.sum_le_sum
        intro n hn
        have hn' := Finset.mem_Icc.mp hn
        exact (hDle n).trans (mul_le_mul_of_nonneg_left
          (sqrt_one_add_log_le hn'.1 hn'.2 hN) (sqrtTau_nonneg n))
      _ = w * ∑ n ∈ Finset.Icc 1 N, sqrtTau n := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        ring
  calc
    HalberstamScratch.partialSum D N ≤
        w * HalberstamScratch.partialSum sqrtTau N := hsum
    _ ≤ w * (sqrtTauMeanConstant * (N : ℝ) *
        (Real.log (N : ℝ)).rpow (5 / 12 : ℝ)) :=
      mul_le_mul_of_nonneg_left hsqrt hw
    _ = (Real.sqrt 2 * sqrtTauMeanConstant) * (N : ℝ) *
        (Real.log (N : ℝ)).rpow (11 / 12 : ℝ) := by
      dsimp [w]
      have hrpow :
          (Real.log (N : ℝ)) ^ (1 / 2 : ℝ) *
              (Real.log (N : ℝ)) ^ (5 / 12 : ℝ) =
            (Real.log (N : ℝ)) ^ (11 / 12 : ℝ) := by
        rw [← Real.rpow_add hlog]
        norm_num
      change Real.sqrt 2 * (Real.log (N : ℝ)) ^ (1 / 2 : ℝ) *
          (sqrtTauMeanConstant * (N : ℝ) *
            (Real.log (N : ℝ)) ^ (5 / 12 : ℝ)) =
        (Real.sqrt 2 * sqrtTauMeanConstant) * (N : ℝ) *
          (Real.log (N : ℝ)) ^ (11 / 12 : ℝ)
      calc
        _ = (Real.sqrt 2 * sqrtTauMeanConstant) * (N : ℝ) *
            ((Real.log (N : ℝ)) ^ (1 / 2 : ℝ) *
              (Real.log (N : ℝ)) ^ (5 / 12 : ℝ)) := by ring
        _ = _ := by rw [hrpow]

theorem weighted_deficit_partialSum_isBigO
    (D : ℕ → ℝ)
    (hDnonneg : ∀ n, 0 ≤ D n)
    (hDle : ∀ n,
      D n ≤ sqrtTau n * Real.sqrt (1 + Real.log (n : ℝ))) :
    (fun N : ℕ => HalberstamScratch.partialSum D N) =O[atTop]
      (fun N : ℕ => (N : ℝ) *
        (Real.log (N : ℝ)).rpow (11 / 12 : ℝ)) := by
  refine IsBigO.of_bound (Real.sqrt 2 * sqrtTauMeanConstant) ?_
  filter_upwards [eventually_weighted_deficit_partialSum_le D hDnonneg hDle,
      eventually_ge_atTop (3 : ℕ)] with N hbound hN
  have hsum : 0 ≤ HalberstamScratch.partialSum D N :=
    Finset.sum_nonneg fun n hn => hDnonneg n
  have hlog : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hbase : 0 ≤ (N : ℝ) * (Real.log (N : ℝ)).rpow (11 / 12 : ℝ) :=
    mul_nonneg (Nat.cast_nonneg N) (Real.rpow_nonneg hlog _)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hsum,
    abs_of_nonneg hbase]
  simpa [mul_assoc] using hbound

lemma rpow_eleven_twelfths_isLittleO_rpow_one :
    (fun x : ℝ => x.rpow (11 / 12 : ℝ)) =o[atTop]
      (fun x : ℝ => x.rpow 1) := by
  rw [isLittleO_iff_tendsto']
  · apply (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 12 by norm_num)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    convert Real.rpow_sub hx (11 / 12 : ℝ) 1 using 1 <;> norm_num
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx hzero
    exact ((Real.rpow_pos_of_pos hx _).ne' hzero).elim

lemma weighted_mean_model_isLittleO :
    (fun N : ℕ => (N : ℝ) *
      (Real.log (N : ℝ)).rpow (11 / 12 : ℝ)) =o[atTop]
      (fun N : ℕ => (N : ℝ) * Real.log (N : ℝ)) := by
  have hlog := rpow_eleven_twelfths_isLittleO_rpow_one.comp_tendsto
    tendsto_log_coe_at_top
  have hlog' :
      (fun N : ℕ => (Real.log (N : ℝ)).rpow (11 / 12 : ℝ)) =o[atTop]
        (fun N : ℕ => Real.log (N : ℝ)) :=
    hlog.congr' (Filter.Eventually.of_forall fun _ => rfl)
      (Filter.Eventually.of_forall fun N => Real.rpow_one _)
  exact (isBigO_refl (fun N : ℕ => (N : ℝ)) atTop).mul_isLittleO hlog'

theorem weighted_deficit_partialSum_isLittleO
    (D : ℕ → ℝ)
    (hDnonneg : ∀ n, 0 ≤ D n)
    (hDle : ∀ n,
      D n ≤ sqrtTau n * Real.sqrt (1 + Real.log (n : ℝ))) :
    (fun N : ℕ => HalberstamScratch.partialSum D N) =o[atTop]
      (fun N : ℕ => (N : ℝ) * Real.log (N : ℝ)) :=
  (weighted_deficit_partialSum_isBigO D hDnonneg hDle).trans_isLittleO
    weighted_mean_model_isLittleO

noncomputable def tauSum (X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 X, (n.divisors.card : ℝ)

lemma tauSum_eq_floorSum (X : ℕ) :
    tauSum X = ∑ d ∈ Finset.Ioc 0 X, ((X / d : ℕ) : ℝ) := by
  rw [tauSum, show Finset.Icc 1 X = Finset.Ioc 0 X by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega]
  norm_cast
  simpa only [ArithmeticFunction.sigma_zero_apply] using
    ArithmeticFunction.sum_Ioc_sigma0_eq_sum_div X

lemma mul_harmonic_eq (X : ℕ) :
    (X : ℝ) * (harmonic X : ℝ) =
      ∑ d ∈ Finset.Ioc 0 X, (X : ℝ) / d := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  rw [Finset.mul_sum,
    show Finset.Icc 1 X = Finset.Ioc 0 X by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      omega]
  simp only [div_eq_mul_inv]

lemma floorSum_le_mul_harmonic (X : ℕ) :
    (∑ d ∈ Finset.Ioc 0 X, ((X / d : ℕ) : ℝ)) ≤
      (X : ℝ) * (harmonic X : ℝ) := by
  rw [mul_harmonic_eq]
  exact Finset.sum_le_sum fun _ _ => Nat.cast_div_le

lemma mul_harmonic_le_floorSum_add (X : ℕ) :
    (X : ℝ) * (harmonic X : ℝ) ≤
      (∑ d ∈ Finset.Ioc 0 X, ((X / d : ℕ) : ℝ)) + X := by
  rw [mul_harmonic_eq]
  calc
    ∑ d ∈ Finset.Ioc 0 X, (X : ℝ) / d
        ≤ ∑ d ∈ Finset.Ioc 0 X, (((X / d : ℕ) : ℝ) + 1) := by
          apply Finset.sum_le_sum
          intro d hd
          have hdpos : 0 < d := (Finset.mem_Ioc.mp hd).1
          exact le_of_lt <| by
            rw [div_lt_iff₀ (Nat.cast_pos.mpr hdpos)]
            norm_cast
            simpa [mul_comm] using Nat.lt_mul_div_succ X hdpos
    _ = (∑ d ∈ Finset.Ioc 0 X, ((X / d : ℕ) : ℝ)) + X := by
      simp [Finset.sum_add_distrib]

lemma tauSum_sub_mul_harmonic_isBigO :
    (fun X : ℕ => tauSum X - (X : ℝ) * (harmonic X : ℝ))
      =O[atTop] (fun X : ℕ => (X : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound 1 (.of_forall fun X => ?_)
  simp only [Real.norm_eq_abs, one_mul]
  nth_rewrite 2 [abs_of_nonneg (Nat.cast_nonneg X)]
  rw [tauSum_eq_floorSum]
  have hle := floorSum_le_mul_harmonic X
  have hlt := mul_harmonic_le_floorSum_add X
  rw [abs_of_nonpos (sub_nonpos.mpr hle)]
  linarith

lemma natCast_isLittleO_natCast_mul_log :
    (fun X : ℕ => (X : ℝ)) =o[atTop]
      (fun X : ℕ => (X : ℝ) * Real.log X) := by
  have hlog : (fun _ : ℕ => (1 : ℝ)) =o[atTop]
      (fun X : ℕ => Real.log X) := by
    rw [Asymptotics.isLittleO_const_left]
    right
    have ht := tendsto_norm_atTop_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    exact ht.congr' (Filter.Eventually.of_forall fun _ => rfl)
  simpa only [mul_one] using
    (Asymptotics.isBigO_refl (fun X : ℕ => (X : ℝ)) atTop).mul_isLittleO hlog

lemma harmonic_isEquivalent_log :
    (fun X : ℕ => (harmonic X : ℝ)) ~[atTop]
      (fun X : ℕ => Real.log X) := by
  apply Asymptotics.IsLittleO.isEquivalent
  exact (Real.tendsto_harmonic_sub_log.isBigO_one ℝ).trans_isLittleO
    ((Real.isLittleO_const_log_atTop (c := (1 : ℝ))).comp_tendsto
      tendsto_natCast_atTop_atTop)

theorem tauSum_isEquivalent :
    (fun X : ℕ => tauSum X) ~[atTop]
      (fun X : ℕ => (X : ℝ) * Real.log X) := by
  have hmain :
      (fun X : ℕ => (X : ℝ) * (harmonic X : ℝ)) ~[atTop]
        (fun X : ℕ => (X : ℝ) * Real.log X) :=
    (Asymptotics.IsEquivalent.refl :
      (fun X : ℕ => (X : ℝ)) ~[atTop] (fun X : ℕ => (X : ℝ))).mul
        harmonic_isEquivalent_log
  rw [Asymptotics.IsEquivalent]
  have herr :
      (fun X : ℕ => tauSum X - (X : ℝ) * (harmonic X : ℝ))
        =o[atTop] (fun X : ℕ => (X : ℝ) * Real.log X) :=
    tauSum_sub_mul_harmonic_isBigO.trans_isLittleO
      natCast_isLittleO_natCast_mul_log
  have hsum := herr.add hmain.isLittleO
  refine hsum.congr' ?_ (Filter.Eventually.of_forall fun _ => rfl)
  filter_upwards with X
  simp only [Pi.sub_apply]
  ring

noncomputable def statisticSum (G : ℕ → ℝ) (X : ℕ) : ℝ :=
  HalberstamScratch.partialSum G X

theorem statisticSum_isEquivalent_of_sqrtTau_deficit
    (G : ℕ → ℝ)
    (hdef_nonneg : ∀ n, 0 ≤ (n.divisors.card : ℝ) - G n)
    (hdef_le : ∀ n, (n.divisors.card : ℝ) - G n ≤ sqrtTau n) :
    (fun X : ℕ => statisticSum G X) ~[atTop]
      (fun X : ℕ => (X : ℝ) * Real.log X) := by
  let D : ℕ → ℝ := fun n => (n.divisors.card : ℝ) - G n
  have hDsmall :
      (fun X : ℕ => HalberstamScratch.partialSum D X) =o[atTop]
        (fun X : ℕ => (X : ℝ) * Real.log X) :=
    deficit_partialSum_isLittleO D hdef_nonneg hdef_le
  have hsub := tauSum_isEquivalent.sub_isLittleO hDsmall
  refine hsub.congr_left (Filter.Eventually.of_forall ?_)
  intro X
  simp only [Pi.sub_apply]
  unfold statisticSum tauSum HalberstamScratch.partialSum D
  rw [Finset.sum_sub_distrib]
  ring

theorem statisticSum_isEquivalent_of_weighted_sqrtTau_deficit
    (G : ℕ → ℝ)
    (hdef_nonneg : ∀ n, 0 ≤ (n.divisors.card : ℝ) - G n)
    (hdef_le : ∀ n,
      (n.divisors.card : ℝ) - G n ≤
        sqrtTau n * Real.sqrt (1 + Real.log (n : ℝ))) :
    (fun X : ℕ => statisticSum G X) ~[atTop]
      (fun X : ℕ => (X : ℝ) * Real.log X) := by
  let D : ℕ → ℝ := fun n => (n.divisors.card : ℝ) - G n
  have hDsmall :
      (fun X : ℕ => HalberstamScratch.partialSum D X) =o[atTop]
        (fun X : ℕ => (X : ℝ) * Real.log X) :=
    weighted_deficit_partialSum_isLittleO D hdef_nonneg hdef_le
  have hsub := tauSum_isEquivalent.sub_isLittleO hDsmall
  refine hsub.congr_left (Filter.Eventually.of_forall ?_)
  intro X
  simp only [Pi.sub_apply]
  unfold statisticSum tauSum HalberstamScratch.partialSum D
  rw [Finset.sum_sub_distrib]
  ring

end Erdos673Mean
