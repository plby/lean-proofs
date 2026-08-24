import ErdosProblems.Erdos360.Core

namespace Erdos360

open Filter
open scoped BigOperators Topology

private lemma one_le_prime_ratio {p : ℕ} (hp : p.Prime) :
    1 ≤ (p : ℝ) / ((p : ℝ) - 1) := by
  have hden : 0 < (p : ℝ) - 1 := by
    exact sub_pos.mpr (by exact_mod_cast hp.one_lt)
  rw [one_le_div hden]
  linarith

private lemma prime_ratio_le_cutoff {Y p : ℕ} (hY : 1 ≤ Y)
    (hp : p.Prime) (hYp : Y < p) :
    (p : ℝ) / ((p : ℝ) - 1) ≤ ((Y + 1 : ℕ) : ℝ) / Y := by
  have hpden : 0 < (p : ℝ) - 1 := by
    exact sub_pos.mpr (by exact_mod_cast hp.one_lt)
  have hYpos : 0 < (Y : ℝ) := by exact_mod_cast hY
  rw [div_le_div_iff₀ hpden hYpos]
  have hle : (Y + 1 : ℝ) ≤ p := by exact_mod_cast hYp
  push_cast at hle ⊢
  nlinarith

private lemma small_prime_ratio_product_eq (Y : ℕ) :
    (∏ p ∈ (Finset.Icc 1 Y).filter Nat.Prime,
      (p : ℝ) / ((p : ℝ) - 1)) = partial_euler_product Y := by
  unfold partial_euler_product
  apply Finset.prod_congr rfl
  intro p hp
  have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpPrime.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hpPrime.ne_one)
  field_simp [hp0, hp1]

private lemma totientRatio_le_split_bound (b Y : ℕ) (hb : 0 < b)
    (hY : 1 ≤ Y) :
    (b : ℝ) / Nat.totient b ≤
      partial_euler_product Y * (((Y + 1 : ℕ) : ℝ) / Y) ^
        (b.primeFactors.filter fun p => Y < p).card := by
  classical
  let small := b.primeFactors.filter (fun p => p ≤ Y)
  let large := b.primeFactors.filter (fun p => ¬ p ≤ Y)
  have hsplit :
      (∏ p ∈ b.primeFactors, (p : ℝ) / ((p : ℝ) - 1)) =
        (∏ p ∈ small, (p : ℝ) / ((p : ℝ) - 1)) *
          (∏ p ∈ large, (p : ℝ) / ((p : ℝ) - 1)) := by
    dsimp [small, large]
    exact (Finset.prod_filter_mul_prod_filter_not b.primeFactors
      (fun p => p ≤ Y) (fun p => (p : ℝ) / ((p : ℝ) - 1))).symm
  have hsmall_subset : small ⊆ (Finset.Icc 1 Y).filter Nat.Prime := by
    intro p hp
    rw [show small = b.primeFactors.filter (fun p => p ≤ Y) by rfl] at hp
    rcases Finset.mem_filter.mp hp with ⟨hpb, hpY⟩
    have hpPrime := Nat.prime_of_mem_primeFactors hpb
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hpPrime.one_le, hpY⟩, hpPrime⟩
  have hsmall_le :
      (∏ p ∈ small, (p : ℝ) / ((p : ℝ) - 1)) ≤
        partial_euler_product Y := by
    rw [← small_prime_ratio_product_eq]
    apply Finset.prod_le_prod_of_subset_of_one_le hsmall_subset
    · intro p hp
      exact (one_le_prime_ratio
        (Nat.prime_of_mem_primeFactors
          ((Finset.mem_filter.mp hp).1))).trans' (by norm_num)
    · intro p hp _
      exact one_le_prime_ratio (Finset.mem_filter.mp hp).2
  have hlarge_le :
      (∏ p ∈ large, (p : ℝ) / ((p : ℝ) - 1)) ≤
        (((Y + 1 : ℕ) : ℝ) / Y) ^ large.card := by
    calc
      (∏ p ∈ large, (p : ℝ) / ((p : ℝ) - 1)) ≤
          ∏ _p ∈ large, (((Y + 1 : ℕ) : ℝ) / Y) := by
        refine Finset.prod_le_prod ?_ ?_
        · intro p hp
          have hpb : p ∈ b.primeFactors :=
            (Finset.mem_filter.mp (show p ∈ b.primeFactors.filter
              (fun p => ¬ p ≤ Y) from hp)).1
          exact (one_le_prime_ratio
            (Nat.prime_of_mem_primeFactors hpb)).trans' (by norm_num)
        · intro p hp
          rcases Finset.mem_filter.mp (show p ∈ b.primeFactors.filter
              (fun p => ¬ p ≤ Y) from hp) with ⟨hpb, hpY⟩
          exact prime_ratio_le_cutoff hY
            (Nat.prime_of_mem_primeFactors hpb) (Nat.lt_of_not_ge hpY)
      _ = (((Y + 1 : ℕ) : ℝ) / Y) ^ large.card := by
        rw [Finset.prod_const]
  rw [Erdos4.cofactor_ratio_eq_primeFactors_product b hb.ne', hsplit]
  have hlarge_le' :
      (∏ p ∈ large, (p : ℝ) / ((p : ℝ) - 1)) ≤
        (((Y + 1 : ℕ) : ℝ) / Y) ^
          (b.primeFactors.filter fun p => Y < p).card := by
    simpa [large, not_le] using hlarge_le
  exact mul_le_mul hsmall_le hlarge_le'
    (Finset.prod_nonneg fun p hp => by
      have hpb : p ∈ b.primeFactors :=
        (Finset.mem_filter.mp (show p ∈ b.primeFactors.filter
          (fun p => ¬ p ≤ Y) from hp)).1
      exact (one_le_prime_ratio
        (Nat.prime_of_mem_primeFactors hpb)).trans' (by norm_num))
    (zero_le_one.trans partial_euler_trivial_lower_bound)

/-- A pure finite form of the maximal-order estimate for the totient ratio.
The chosen cutoff is the square of one plus the number of distinct prime
factors; the factors above the cutoff cost less than `exp 1`. -/
lemma totientRatio_le_three_mul_partial_euler_cardSq
    (b : ℕ) (hb : 0 < b) :
    (b : ℝ) / Nat.totient b ≤
      3 * partial_euler_product ((b.primeFactors.card + 1) ^ 2) := by
  let r := b.primeFactors.card
  let Y := (r + 1) ^ 2
  have hY : 1 ≤ Y := by
    simp [Y, r, pow_two]
  have hsplit := totientRatio_le_split_bound b Y hb hY
  have hcard : (b.primeFactors.filter fun p => Y < p).card ≤ Y := by
    calc
      (b.primeFactors.filter fun p => Y < p).card ≤ b.primeFactors.card :=
        Finset.card_filter_le _ _
      _ ≤ Y := by
        dsimp [Y, r]
        nlinarith [Nat.zero_le b.primeFactors.card]
  have hbase :
      (((Y + 1 : ℕ) : ℝ) / Y) = 1 + (Y : ℝ)⁻¹ := by
    have hYR : (Y : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp [hYR]
  have hbaseOne : (1 : ℝ) ≤ (((Y + 1 : ℕ) : ℝ) / Y) := by
    rw [hbase]
    exact le_add_of_nonneg_right (inv_nonneg.mpr (Nat.cast_nonneg Y))
  have hpow :
      (((Y + 1 : ℕ) : ℝ) / Y) ^
          (b.primeFactors.filter fun p => Y < p).card ≤ Real.exp 1 := by
    calc
      (((Y + 1 : ℕ) : ℝ) / Y) ^
          (b.primeFactors.filter fun p => Y < p).card ≤
          (((Y + 1 : ℕ) : ℝ) / Y) ^ Y := by
        exact pow_le_pow_right₀ hbaseOne hcard
      _ = (1 + (Y : ℝ)⁻¹) ^ Y := by rw [hbase]
      _ ≤ Real.exp 1 := Real.one_add_inv_pow_le_exp
  have hexp : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
  have hpep : 0 ≤ partial_euler_product Y :=
    (zero_le_one.trans partial_euler_trivial_lower_bound)
  calc
    (b : ℝ) / Nat.totient b ≤
        partial_euler_product Y *
          (((Y + 1 : ℕ) : ℝ) / Y) ^
            (b.primeFactors.filter fun p => Y < p).card := hsplit
    _ ≤ partial_euler_product Y * Real.exp 1 :=
      mul_le_mul_of_nonneg_left hpow hpep
    _ ≤ 3 * partial_euler_product Y := by
      nlinarith

private lemma card_primeFactors_cast_le_two_mul_log
    (b : ℕ) (hb : 0 < b) :
    (b.primeFactors.card : ℝ) ≤ 2 * Real.log (b : ℝ) := by
  have hpow : 2 ^ b.primeFactors.card ≤ b := by
    calc
      2 ^ b.primeFactors.card ≤ ∏ p ∈ b.primeFactors, p := by
        apply Finset.pow_card_le_prod
        intro p hp
        exact (Nat.prime_of_mem_primeFactors hp).two_le
      _ ≤ b := Nat.le_of_dvd hb (Nat.prod_primeFactors_dvd b)
  have hpowR : (2 : ℝ) ^ b.primeFactors.card ≤ (b : ℝ) := by
    exact_mod_cast hpow
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ b.primeFactors.card) hpowR
  rw [Real.log_pow] at hlog
  have hlogTwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hcard : (0 : ℝ) ≤ b.primeFactors.card := by positivity
  nlinarith

private lemma log_cardSq_le_six_mul_loglog
    (n b : ℕ) (hb : 0 < b) (hbn : b ≤ n)
    (hll : 1 ≤ Real.log (Real.log (n : ℝ))) :
    Real.log (((b.primeFactors.card + 1) ^ 2 : ℕ) : ℝ) ≤
      6 * Real.log (Real.log (n : ℝ)) := by
  have hn : 0 < n := hb.trans_le hbn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlognNonneg : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hlognPos : 0 < Real.log (n : ℝ) := by
    refine lt_of_le_of_ne hlognNonneg ?_
    intro heq
    rw [← heq, Real.log_zero] at hll
    norm_num at hll
  have hlognOne : 1 ≤ Real.log (n : ℝ) := by
    have hexp := Real.exp_le_exp.mpr hll
    rw [Real.exp_log hlognPos] at hexp
    exact (Real.one_le_exp (by norm_num)).trans hexp
  have hlogb_le : Real.log (b : ℝ) ≤ Real.log (n : ℝ) := by
    exact Real.log_le_log (by exact_mod_cast hb) (by exact_mod_cast hbn)
  have hr := card_primeFactors_cast_le_two_mul_log b hb
  have hr1 : ((b.primeFactors.card + 1 : ℕ) : ℝ) ≤
      3 * Real.log (n : ℝ) := by
    push_cast
    nlinarith
  have hr1pos : (0 : ℝ) < (b.primeFactors.card + 1 : ℕ) := by positivity
  have hthreeLogPos : 0 < 3 * Real.log (n : ℝ) := by positivity
  have hlogr : Real.log ((b.primeFactors.card + 1 : ℕ) : ℝ) ≤
      Real.log (3 * Real.log (n : ℝ)) :=
    Real.log_le_log hr1pos hr1
  have hlogmul : Real.log (3 * Real.log (n : ℝ)) =
      Real.log 3 + Real.log (Real.log (n : ℝ)) := by
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hlognPos.ne']
  rw [hlogmul] at hlogr
  have hlog3 : Real.log 3 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    nlinarith
  have hlogr' : Real.log ((b.primeFactors.card + 1 : ℕ) : ℝ) ≤
      3 * Real.log (Real.log (n : ℝ)) := by
    nlinarith
  rw [Nat.cast_pow, Real.log_pow]
  norm_num [Nat.cast_add, Nat.cast_one] at hlogr' ⊢
  linarith

/-- Uniform maximal-order estimate for the totient ratio, in the precise
eventual form needed when a progression step is only known to be at most the
target.  The constant is absolute and the quantifier over `b` is uniform. -/
theorem exists_eventually_totientRatio_le_loglog :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ b : ℕ, 0 < b → b ≤ n →
        (b : ℝ) / Nat.totient b ≤
          C * Real.log (Real.log (n : ℝ)) := by
  obtain ⟨Cu, hCu, hMertens⟩ := weak_mertens_third_upper_all
  refine ⟨18 * (Cu + 1), by positivity, ?_⟩
  filter_upwards
    [tendsto_log_log_coe_at_top.eventually
      (eventually_ge_atTop (1 : ℝ))] with n hll
  intro b hb hbn
  have hllNonneg : 0 ≤ Real.log (Real.log (n : ℝ)) := zero_le_one.trans hll
  by_cases hb1 : b = 1
  · subst b
    simp only [Nat.cast_one, Nat.totient_one, div_one]
    have hconst : 1 ≤ 18 * (Cu + 1) := by nlinarith
    have hmul := mul_le_mul hconst hll zero_le_one (by positivity :
      0 ≤ 18 * (Cu + 1))
    norm_num at hmul
    exact hmul
  · have hbTwo : 2 ≤ b := by omega
    let Y := (b.primeFactors.card + 1) ^ 2
    have hrpos : 0 < b.primeFactors.card :=
      Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr (by omega))
    have hYtwo : 2 ≤ Y := by
      dsimp [Y]
      nlinarith
    have hlogYNonneg : 0 ≤ Real.log (Y : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ Y by omega))
    have hPEP : partial_euler_product Y ≤ Cu * Real.log (Y : ℝ) := by
      have h := hMertens (Y : ℝ) (by exact_mod_cast hYtwo)
      simpa [Real.norm_of_nonneg hlogYNonneg,
        Real.norm_of_nonneg (zero_le_one.trans
          (partial_euler_trivial_lower_bound (n := Y)))] using h
    have hlogY : Real.log (Y : ℝ) ≤
        6 * Real.log (Real.log (n : ℝ)) := by
      simpa [Y] using log_cardSq_le_six_mul_loglog n b hb hbn hll
    have hratio := totientRatio_le_three_mul_partial_euler_cardSq b hb
    calc
      (b : ℝ) / Nat.totient b ≤ 3 * partial_euler_product Y := by
        simpa [Y] using hratio
      _ ≤ 3 * (Cu * Real.log (Y : ℝ)) := by gcongr
      _ ≤ 18 * Cu * Real.log (Real.log (n : ℝ)) := by
        have := mul_le_mul_of_nonneg_left hlogY hCu.le
        nlinarith
      _ ≤ 18 * (Cu + 1) * Real.log (Real.log (n : ℝ)) := by
        nlinarith

/-- A single maximal-order bound controls the totient ratio of the combined
target and progression step.  This is the sharp form needed by the CFP
sieve: applying Mertens directly to `n * step` avoids counting prime factors
shared by `n` and `step` twice. -/
theorem exists_eventually_mul_totientRatio_le_loglog :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ b : ℕ, 0 < b → b ≤ n →
        ((n * b : ℕ) : ℝ) / Nat.totient (n * b) ≤
          C * Real.log (Real.log (n : ℝ)) := by
  obtain ⟨C, hC, hratio⟩ := exists_eventually_totientRatio_le_loglog
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hratio
  refine ⟨2 * C, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max N 3),
    tendsto_log_log_coe_at_top.eventually
      (eventually_ge_atTop (Real.log 2))] with n hn hll
  intro b hb hbn
  have hnN : N ≤ n * n := by
    have hNn : N ≤ n := le_trans (le_max_left _ _) hn
    have hnpos : 0 < n := by omega
    exact hNn.trans (Nat.le_mul_of_pos_right n hnpos)
  have hnb : n * b ≤ n * n := Nat.mul_le_mul_left n hbn
  have hmain := hN (n * n) hnN (n * b) (Nat.mul_pos (by omega) hb) hnb
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogn : (0 : ℝ) < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlogSq : Real.log (((n * n : ℕ) : ℝ)) =
      2 * Real.log (n : ℝ) := by
    push_cast
    rw [Real.log_mul hnR.ne' hnR.ne']
    ring
  have hloglogSq : Real.log (Real.log (((n * n : ℕ) : ℝ))) =
      Real.log 2 + Real.log (Real.log (n : ℝ)) := by
    rw [hlogSq, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hlogn.ne']
  rw [hloglogSq] at hmain
  have hll0 : 0 ≤ Real.log (Real.log (n : ℝ)) := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  nlinarith

private lemma mul_totientRatio_le_mul_totientRatios
    (n b : ℕ) (hn : 0 < n) (hb : 0 < b) :
    ((n * b : ℕ) : ℝ) / Nat.totient (n * b) ≤
      ((n : ℝ) / Nat.totient n) *
        ((b : ℝ) / Nat.totient b) := by
  have hphiN : 0 < Nat.totient n := Nat.totient_pos.mpr hn
  have hphiB : 0 < Nat.totient b := Nat.totient_pos.mpr hb
  have hphiProd : (0 : ℝ) < Nat.totient n * Nat.totient b := by
    positivity
  have hsuper : (Nat.totient n : ℝ) * Nat.totient b ≤
      Nat.totient (n * b) := by
    exact_mod_cast Nat.totient_super_multiplicative n b
  calc
    ((n * b : ℕ) : ℝ) / Nat.totient (n * b) ≤
        ((n * b : ℕ) : ℝ) /
          ((Nat.totient n : ℝ) * Nat.totient b) := by
      exact div_le_div_of_nonneg_left (by positivity) hphiProd hsuper
    _ = ((n : ℝ) / Nat.totient n) *
        ((b : ℝ) / Nat.totient b) := by
      push_cast
      field_simp

/-- The arbitrary-progression-step Euler-product estimate.  It is uniform
over every positive step `b ≤ n`; no coprimality between `b` and `n` is
assumed. -/
theorem exists_eventually_missingEulerProduct_mul_step_le_loglog :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ b y : ℕ, 0 < b → b ≤ n → 2 ≤ y →
        missingEulerProduct (n * b) y ≤
          C * ((n : ℝ) / Nat.totient n) *
            Real.log (Real.log (n : ℝ)) / Real.log (y : ℝ) := by
  obtain ⟨CM, hCM, hMertens⟩ := exists_missingEulerProduct_upper
  obtain ⟨CT, hCT, hratioEventually⟩ :=
    exists_eventually_totientRatio_le_loglog
  refine ⟨CM * CT, mul_pos hCM hCT, ?_⟩
  filter_upwards [hratioEventually] with n hratio
  intro b y hb hbn hy
  have hn : 0 < n := hb.trans_le hbn
  have hnb : 0 < n * b := Nat.mul_pos hn hb
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hnRatioNonneg : 0 ≤ (n : ℝ) / Nat.totient n := by positivity
  have hbRatioNonneg : 0 ≤ (b : ℝ) / Nat.totient b := by positivity
  have hllNonneg : 0 ≤ Real.log (Real.log (n : ℝ)) := by
    have h := hratio b hb hbn
    by_contra hneg
    have hratioPos : 0 < (b : ℝ) / Nat.totient b := by positivity
    have hrightNonpos :
        CT * Real.log (Real.log (n : ℝ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hCT.le (le_of_not_ge hneg)
    exact (not_lt_of_ge (h.trans hrightNonpos)) hratioPos
  have hnbRatio := mul_totientRatio_le_mul_totientRatios n b hn hb
  have hbRatio := hratio b hb hbn
  calc
    missingEulerProduct (n * b) y ≤
        CM * (((n * b : ℕ) : ℝ) / Nat.totient (n * b)) /
          Real.log (y : ℝ) := hMertens (n * b) y hnb hy
    _ ≤ CM * (((n : ℝ) / Nat.totient n) *
          ((b : ℝ) / Nat.totient b)) / Real.log (y : ℝ) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hnbRatio hCM.le) hlog.le
    _ ≤ CM * (((n : ℝ) / Nat.totient n) *
          (CT * Real.log (Real.log (n : ℝ)))) /
            Real.log (y : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hbRatio hnRatioNonneg
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmul hCM.le) hlog.le
    _ = (CM * CT) * ((n : ℝ) / Nat.totient n) *
          Real.log (Real.log (n : ℝ)) / Real.log (y : ℝ) := by
      ring

end Erdos360

#print axioms Erdos360.exists_eventually_totientRatio_le_loglog
#print axioms Erdos360.exists_eventually_missingEulerProduct_mul_step_le_loglog
