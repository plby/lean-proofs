/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1149.SuperlinearSieve
import ErdosProblems.Erdos239
import UnitFractions.ForMathlib.BasicEstimates

/-!
# The sublinear case of Erdős Problem 1149

For `0 < α < 1`, the function `floor (n ^ α)` is constant on the exact
blocks bounded by the ceilings of consecutive `1 / α` powers.  This file
uses those blocks, finite Möbius inversion, and partial summation to prove the
required density without any equidistribution theorem.
-/

namespace Erdos1149

open Filter
open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

/-- Left endpoint of the block on which `floor (n ^ α)` equals `m`. -/
def powerBlockStart (α : ℝ) (m : ℕ) : ℕ :=
  ⌈(m : ℝ) ^ α⁻¹⌉₊

lemma powerBlockStart_zero {α : ℝ} (hα : 0 < α) : powerBlockStart α 0 = 0 := by
  simp [powerBlockStart, Real.zero_rpow (inv_ne_zero (ne_of_gt hα))]

lemma floor_rpow_eq_iff_mem_powerBlock { α : ℝ }
    (hα : 0 < α) (n m : ℕ) :
    ⌊(n : ℝ) ^ α⌋₊ = m ↔
      powerBlockStart α m ≤ n ∧ n < powerBlockStart α (m + 1) := by
  have hαne : α ≠ 0 := ne_of_gt hα
  have hinv : 0 < α⁻¹ := inv_pos.mpr hα
  have hfloor :
      ⌊(n : ℝ) ^ α⌋₊ = m ↔
        (m : ℝ) ≤ (n : ℝ) ^ α ∧
          (n : ℝ) ^ α < (m : ℝ) + 1 :=
    Nat.floor_eq_iff (Real.rpow_nonneg (Nat.cast_nonneg n) α)
  rw [hfloor]
  constructor
  · rintro ⟨hl, hu⟩
    constructor
    · rw [powerBlockStart, Nat.ceil_le]
      calc
        (m : ℝ) ^ α⁻¹ ≤ ((n : ℝ) ^ α) ^ α⁻¹ :=
          Real.rpow_le_rpow (Nat.cast_nonneg m) hl hinv.le
        _ = n := by rw [Real.rpow_rpow_inv (Nat.cast_nonneg n) hαne]
    · rw [powerBlockStart, Nat.lt_ceil]
      calc
        (n : ℝ) = ((n : ℝ) ^ α) ^ α⁻¹ := by
          rw [Real.rpow_rpow_inv (Nat.cast_nonneg n) hαne]
        _ < (((m + 1 : ℕ) : ℝ) ^ α⁻¹) :=
          Real.rpow_lt_rpow (Real.rpow_nonneg (Nat.cast_nonneg n) α)
            (by simpa using hu) hinv
  · rintro ⟨hl, hu⟩
    constructor
    · rw [powerBlockStart, Nat.ceil_le] at hl
      calc
        (m : ℝ) = ((m : ℝ) ^ α⁻¹) ^ α := by
          rw [Real.rpow_inv_rpow (Nat.cast_nonneg m) hαne]
        _ ≤ (n : ℝ) ^ α :=
          Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg m) α⁻¹)
            hl hα.le
    · rw [powerBlockStart, Nat.lt_ceil] at hu
      calc
        (n : ℝ) ^ α < ((((m + 1 : ℕ) : ℝ) ^ α⁻¹) ^ α) :=
          Real.rpow_lt_rpow (Nat.cast_nonneg n) hu hα
        _ = (m : ℝ) + 1 := by
          rw [Real.rpow_inv_rpow (Nat.cast_nonneg (m + 1)) hαne]
          norm_num

/-- Multiples of `d` in a prefix.  The extra term records the multiple zero
at the left endpoint and the possible incomplete final period. -/
lemma card_filter_dvd_range (b d : ℕ) (hd : 0 < d) :
    ((Finset.range b).filter (d ∣ ·)).card =
      b / d + if 0 < b % d then 1 else 0 := by
  have hset : (Finset.range b).filter (d ∣ ·) =
      (Finset.range b).filter (fun n ↦ n ≡ 0 [MOD d]) := by
    ext n
    simp [Nat.modEq_zero_iff_dvd]
  calc
    ((Finset.range b).filter (d ∣ ·)).card =
        ((Finset.range b).filter (fun n ↦ n ≡ 0 [MOD d])).card :=
      congrArg Finset.card hset
    _ = b / d + if 0 < b % d then 1 else 0 := by
      have h := Nat.count_modEq_card b hd 0
      rw [Nat.count_eq_card_filter_range] at h
      convert h using 1
      simp only [Nat.zero_mod]
      split_ifs with hh <;> simp [hh]

/-- The real prefix count of multiples differs from `b / d` by at most one. -/
lemma abs_card_filter_dvd_range_sub_div_le_one (b d : ℕ) (hd : 0 < d) :
    |(((Finset.range b).filter (d ∣ ·)).card : ℝ) - (b : ℝ) / d| ≤ 1 := by
  rw [card_filter_dvd_range b d hd]
  have hcastdiv : ((b / d : ℕ) : ℝ) ≤ (b : ℝ) / d := Nat.cast_div_le
  have hlt : (b : ℝ) / d < (b / d : ℕ) + 1 := by
    rw [div_lt_iff₀ (by exact_mod_cast hd)]
    exact_mod_cast ((Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self (b / d)))
  split_ifs with hrem
  · rw [Nat.cast_add, Nat.cast_one]
    rw [abs_le]
    constructor <;> linarith
  · norm_num
    rw [abs_le]
    constructor <;> linarith

/-- Multiples in a half-open integer interval have the expected length
divided by the modulus, with an absolute endpoint error at most two. -/
lemma abs_card_filter_dvd_Ico_sub_div_le_two (a b d : ℕ)
    (hab : a ≤ b) (hd : 0 < d) :
    |(((Finset.Ico a b).filter (d ∣ ·)).card : ℝ) -
        ((b - a : ℕ) : ℝ) / d| ≤ 2 := by
  have hunion : Finset.range b = Finset.range a ∪ Finset.Ico a b := by
    ext n
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  have hdis : Disjoint (Finset.range a) (Finset.Ico a b) := by
    rw [Finset.disjoint_left]
    intro n hna hnIco
    simp only [Finset.mem_range] at hna
    exact (not_lt_of_ge (Finset.mem_Ico.mp hnIco).1) hna
  have hdisf :
      Disjoint ((Finset.range a).filter (d ∣ ·))
        ((Finset.Ico a b).filter (d ∣ ·)) :=
    hdis.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hcount :
      ((Finset.range a).filter (d ∣ ·)).card +
          ((Finset.Ico a b).filter (d ∣ ·)).card =
        ((Finset.range b).filter (d ∣ ·)).card := by
    rw [hunion, Finset.filter_union, Finset.card_union_of_disjoint hdisf]
  have hcountR :
      (((Finset.range a).filter (d ∣ ·)).card : ℝ) +
          (((Finset.Ico a b).filter (d ∣ ·)).card : ℝ) =
        (((Finset.range b).filter (d ∣ ·)).card : ℝ) := by
    exact_mod_cast hcount
  have ha := abs_card_filter_dvd_range_sub_div_le_one a d hd
  have hb := abs_card_filter_dvd_range_sub_div_le_one b d hd
  rw [abs_le] at ha hb ⊢
  have hdiv : ((b - a : ℕ) : ℝ) / d =
      (b : ℝ) / d - (a : ℝ) / d := by
    rw [Nat.cast_sub hab]
    ring
  constructor
  · rw [hdiv]
    linarith
  · rw [hdiv]
    linarith

lemma powerBlockStart_mono {α : ℝ} (hα : 0 < α) :
    Monotone (powerBlockStart α) := by
  intro a b hab
  apply Nat.ceil_le_ceil
  exact Real.rpow_le_rpow (Nat.cast_nonneg a) (by exact_mod_cast hab)
    (inv_nonneg.mpr hα.le)

/-- Cardinality of the coprime integers in one complete power block. -/
def coprimePowerBlockCount (α : ℝ) (m : ℕ) : ℕ :=
  ((Finset.Ico (powerBlockStart α m) (powerBlockStart α (m + 1))).filter
    (fun n ↦ n.Coprime m)).card

/-- The normalized totient value, written in its Möbius form. -/
def mobiusCoprimeMean (m : ℕ) : ℝ :=
  ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℝ) / d

lemma coprimePowerBlockCount_eq_mobius_sum {α : ℝ} {m : ℕ}
    (hm : 0 < m) :
    (coprimePowerBlockCount α m : ℝ) =
      ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℝ) *
        (((Finset.Ico (powerBlockStart α m)
          (powerBlockStart α (m + 1))).filter (d ∣ ·)).card : ℝ) := by
  classical
  unfold coprimePowerBlockCount
  calc
    ((((Finset.Ico (powerBlockStart α m)
        (powerBlockStart α (m + 1))).filter
          (fun n ↦ n.Coprime m)).card : ℕ) : ℝ) =
        ∑ n ∈ Finset.Ico (powerBlockStart α m)
          (powerBlockStart α (m + 1)),
            (if n.Coprime m then 1 else 0 : ℝ) := by
      rw [Finset.sum_boole]
    _ = ∑ n ∈ Finset.Ico (powerBlockStart α m)
          (powerBlockStart α (m + 1)),
            ∑ d ∈ m.divisors.filter (fun d ↦ d ∣ n),
              (ArithmeticFunction.moebius d : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact finite_sieve_indicator_mobius hm.ne'
    _ = ∑ n ∈ Finset.Ico (powerBlockStart α m)
          (powerBlockStart α (m + 1)),
            ∑ d ∈ m.divisors,
              (ArithmeticFunction.moebius d : ℝ) *
                (if d ∣ n then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d hd
      split_ifs <;> simp_all
    _ = ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℝ) *
        (((Finset.Ico (powerBlockStart α m)
          (powerBlockStart α (m + 1))).filter (d ∣ ·)).card : ℝ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.mul_sum, Finset.sum_boole]

/-- One complete block differs from its Möbius main term by at most twice
the number of divisors of its label. -/
lemma abs_coprimePowerBlockCount_sub_main_le {α : ℝ}
    (hα : 0 < α) {m : ℕ} (hm : 0 < m) :
    |(coprimePowerBlockCount α m : ℝ) -
        ((powerBlockStart α (m + 1) - powerBlockStart α m : ℕ) : ℝ) *
          mobiusCoprimeMean m| ≤ 2 * m.divisors.card := by
  classical
  rw [coprimePowerBlockCount_eq_mobius_sum hm]
  unfold mobiusCoprimeMean
  rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ d ∈ m.divisors,
        ((ArithmeticFunction.moebius d : ℝ) *
          (((Finset.Ico (powerBlockStart α m)
            (powerBlockStart α (m + 1))).filter (d ∣ ·)).card : ℝ) -
        ((powerBlockStart α (m + 1) - powerBlockStart α m : ℕ) : ℝ) *
          ((ArithmeticFunction.moebius d : ℝ) / d))| ≤
        ∑ d ∈ m.divisors,
          |(ArithmeticFunction.moebius d : ℝ)| * 2 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos
        (Nat.dvd_of_mem_divisors hd) hm
      have herr := abs_card_filter_dvd_Ico_sub_div_le_two
        (powerBlockStart α m) (powerBlockStart α (m + 1)) d
        (powerBlockStart_mono hα (Nat.le_succ m)) hdpos
      rw [show
        (ArithmeticFunction.moebius d : ℝ) *
              (((Finset.Ico (powerBlockStart α m)
                (powerBlockStart α (m + 1))).filter (d ∣ ·)).card : ℝ) -
            ((powerBlockStart α (m + 1) - powerBlockStart α m : ℕ) : ℝ) *
              ((ArithmeticFunction.moebius d : ℝ) / d) =
          (ArithmeticFunction.moebius d : ℝ) *
            ((((Finset.Ico (powerBlockStart α m)
              (powerBlockStart α (m + 1))).filter (d ∣ ·)).card : ℝ) -
              ((powerBlockStart α (m + 1) - powerBlockStart α m : ℕ) : ℝ) / d) by
          ring, abs_mul]
      exact mul_le_mul_of_nonneg_left herr (abs_nonneg _)
    _ ≤ ∑ _d ∈ m.divisors, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
      nlinarith [abs_nonneg (ArithmeticFunction.moebius d : ℝ)]
    _ = 2 * m.divisors.card := by simp [mul_comm]

/-- The arithmetic function `μ(n)/n`, with the mandated value zero at
zero. -/
def mobiusOverId : ArithmeticFunction ℝ :=
  ⟨fun n ↦ if n = 0 then 0 else (ArithmeticFunction.moebius n : ℝ) / n,
    by simp⟩

@[simp] lemma mobiusOverId_apply_of_pos {n : ℕ} (hn : 0 < n) :
    mobiusOverId n = (ArithmeticFunction.moebius n : ℝ) / n := by
  simp [mobiusOverId, hn.ne']

lemma mobiusOverId_mul_zeta_apply {n : ℕ} (hn : 0 < n) :
    (mobiusOverId * ArithmeticFunction.zeta) n = mobiusCoprimeMean n := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  unfold mobiusCoprimeMean
  apply Finset.sum_congr rfl
  intro d hd
  exact mobiusOverId_apply_of_pos
    (Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd) hn)

lemma mobiusOverId_summable :
    Summable (fun n : ℕ ↦ |mobiusOverId n| / (n : ℝ)) := by
  apply mobius_abs_div_sq_summable.congr
  intro n
  rcases n with _ | n
  · simp [mobiusOverId, ArithmeticFunction.moebius]
  · simp only [mobiusOverId_apply_of_pos (Nat.succ_pos n), abs_div,
      pow_two]
    have hnabs : |(((n + 1 : ℕ) : ℝ))| = (n + 1 : ℕ) :=
      abs_of_nonneg (Nat.cast_nonneg _)
    rw [hnabs]
    ring

lemma mobiusOverId_tsum :
    ∑' n : ℕ, mobiusOverId n / (n : ℝ) = 6 / Real.pi ^ 2 := by
  have hs : HasSum (fun n : ℕ ↦ mobiusOverId n / (n : ℝ))
      (6 / Real.pi ^ 2) :=
    HasSum.congr_fun mobius_div_sq_hasSum (fun n ↦ by
      rcases n with _ | n
      · simp [mobiusOverId, ArithmeticFunction.moebius]
      · simp only [mobiusOverId_apply_of_pos (Nat.succ_pos n), pow_two]
        ring)
  exact hs.tsum_eq

/-- Cesàro mean of the normalized totient/Möbius factor. -/
theorem tendsto_mobiusCoprimeMean_average_Ioc :
    Tendsto
      (fun N : ℕ ↦ (∑ n ∈ Finset.Ioc 0 N, mobiusCoprimeMean n) / (N : ℝ))
      atTop (nhds (6 / Real.pi ^ 2)) := by
  have h := Erdos239.tendsto_mean_dirichlet_mul_zeta mobiusOverId
    mobiusOverId_summable
  rw [mobiusOverId_tsum] at h
  convert h using 1
  ext N
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  exact (mobiusOverId_mul_zeta_apply (Finset.mem_Ioc.mp hn).1).symm

/-- Cesàro mean in the zero-based `range` convention.  The zeroth term is
zero, and a one-step shift only changes the normalizing denominator by a
factor tending to one. -/
theorem tendsto_mobiusCoprimeMean_average_range :
    Tendsto
      (fun N : ℕ ↦ (∑ n ∈ Finset.range N, mobiusCoprimeMean n) / (N : ℝ))
      atTop (nhds (6 / Real.pi ^ 2)) := by
  let L : ℝ := 6 / Real.pi ^ 2
  have hratio : Tendsto (fun N : ℕ ↦ (N : ℝ) / (N + 1 : ℕ)) atTop (nhds 1) := by
    simpa using (tendsto_natCast_div_add_atTop (1 : ℝ))
  have hprod := tendsto_mobiusCoprimeMean_average_Ioc.mul hratio
  have hshift : Tendsto
      (fun N : ℕ ↦
        (∑ n ∈ Finset.range (N + 1), mobiusCoprimeMean n) / (N + 1 : ℕ))
      atTop (nhds L) := by
    convert hprod using 1
    · ext N
      have hsets : Finset.range (N + 1) = insert 0 (Finset.Ioc 0 N) := by
        ext n
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
        omega
      rw [hsets, Finset.sum_insert]
      · have hzero : mobiusCoprimeMean 0 = 0 := by
          simp [mobiusCoprimeMean]
        rw [hzero, zero_add]
        rcases N with _ | N
        · simp
        · field_simp
      · simp
    · simp [L]
  exact (tendsto_add_atTop_iff_nat 1).mp (by simpa [L] using hshift)

/-- Smooth real length of the `m`th inverse-power block. -/
def smoothPowerBlockWeight (α : ℝ) (m : ℕ) : ℝ :=
  (m + 1 : ℕ) ^ α⁻¹ - (m : ℝ) ^ α⁻¹

lemma smoothPowerBlockWeight_nonneg {α : ℝ} (hα : 0 < α) (m : ℕ) :
    0 ≤ smoothPowerBlockWeight α m := by
  unfold smoothPowerBlockWeight
  exact sub_nonneg.mpr (Real.rpow_le_rpow (Nat.cast_nonneg m)
    (by norm_num) (inv_nonneg.mpr hα.le))

lemma smoothPowerBlockWeight_mono {α : ℝ} (hα : 0 < α) (hαone : α < 1) :
    Monotone (smoothPowerBlockWeight α) := by
  have hbeta : 1 ≤ α⁻¹ := one_le_inv_iff₀.mpr ⟨hα, hαone.le⟩
  apply monotone_nat_of_le_succ
  intro m
  have hslope := (convexOn_rpow hbeta).slope_mono_adjacent
    (x := (m : ℝ)) (y := (m + 1 : ℕ)) (z := (m + 2 : ℕ))
    (by simp) (by
      show (0 : ℝ) ≤ (m + 2 : ℕ)
      exact_mod_cast (Nat.zero_le (m + 2))) (by norm_num) (by norm_num)
  unfold smoothPowerBlockWeight
  norm_num at hslope ⊢
  have heq : (m : ℝ) + 1 + 1 = (m : ℝ) + 2 := by ring
  rw [heq]
  linarith

/-- Rounding both endpoints of a real block to natural ceilings costs at
most two in its length. -/
lemma abs_powerBlockLength_sub_smooth_le_two {α : ℝ}
    (hα : 0 < α) (m : ℕ) :
    |((powerBlockStart α (m + 1) - powerBlockStart α m : ℕ) : ℝ) -
        smoothPowerBlockWeight α m| ≤ 2 := by
  have hmono := powerBlockStart_mono hα (Nat.le_succ m)
  have hx0 : 0 ≤ (m : ℝ) ^ α⁻¹ := Real.rpow_nonneg (Nat.cast_nonneg m) _
  have hy0 : 0 ≤ ((m + 1 : ℕ) : ℝ) ^ α⁻¹ :=
    Real.rpow_nonneg (Nat.cast_nonneg (m + 1)) _
  have hxlo : (m : ℝ) ^ α⁻¹ ≤ (powerBlockStart α m : ℕ) := by
    exact Nat.le_ceil _
  have hxhi : (powerBlockStart α m : ℕ) < (m : ℝ) ^ α⁻¹ + 1 := by
    exact Nat.ceil_lt_add_one hx0
  have hylo : ((m + 1 : ℕ) : ℝ) ^ α⁻¹ ≤
      (powerBlockStart α (m + 1) : ℕ) := by
    exact Nat.le_ceil _
  have hyhi : (powerBlockStart α (m + 1) : ℕ) <
      ((m + 1 : ℕ) : ℝ) ^ α⁻¹ + 1 := by
    exact Nat.ceil_lt_add_one hy0
  rw [Nat.cast_sub hmono, abs_le]
  unfold smoothPowerBlockWeight
  constructor <;> linarith

/-- Finite summation by parts in the zero-based convention. -/
lemma sum_range_mul_eq_boundary_add_differences_real
    (w f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, w n * f n) =
      w N * (∑ n ∈ Finset.range N, f n) +
        ∑ n ∈ Finset.range N,
          (w n - w (n + 1)) *
            (∑ j ∈ Finset.range (n + 1), f j) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ,
        Finset.sum_range_succ]
      have hsum : (∑ n ∈ Finset.range (N + 1), f n) =
          (∑ n ∈ Finset.range N, f n) + f N := by
        rw [Finset.sum_range_succ]
      rw [hsum]
      ring

lemma sum_smoothPowerBlockWeight (α : ℝ) (N : ℕ) :
    ∑ m ∈ Finset.range N, smoothPowerBlockWeight α m =
      (N : ℝ) ^ α⁻¹ - (0 : ℝ) ^ α⁻¹ := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      unfold smoothPowerBlockWeight
      norm_num

lemma sum_smoothPowerBlockWeight_differences {α : ℝ} (N : ℕ) :
    ∑ m ∈ Finset.range N,
        (smoothPowerBlockWeight α (m + 1) - smoothPowerBlockWeight α m) =
      smoothPowerBlockWeight α N - smoothPowerBlockWeight α 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      ring

lemma smoothPowerBlockWeight_le_deriv {α : ℝ}
    (hα : 0 < α) (hαone : α < 1) (N : ℕ) :
    smoothPowerBlockWeight α N ≤
      α⁻¹ * ((N + 1 : ℕ) : ℝ) ^ (α⁻¹ - 1) := by
  have hbeta : 1 ≤ α⁻¹ := one_le_inv_iff₀.mpr ⟨hα, hαone.le⟩
  have hslope := (convexOn_rpow hbeta).slope_le_of_hasDerivAt
    (x := (N : ℝ)) (y := ((N + 1 : ℕ) : ℝ))
    (by simp) (by
      show (0 : ℝ) ≤ (N + 1 : ℕ)
      exact_mod_cast Nat.zero_le (N + 1)) (by norm_num)
    (Real.hasDerivAt_rpow_const (Or.inr hbeta))
  unfold smoothPowerBlockWeight
  simpa [slope, div_eq_mul_inv] using hslope

lemma mul_smoothPowerBlockWeight_div_rpow_le {α : ℝ}
    (hα : 0 < α) (hαone : α < 1) (N : ℕ) :
    (N : ℝ) * smoothPowerBlockWeight α N /
        ((N + 1 : ℕ) : ℝ) ^ α⁻¹ ≤ α⁻¹ := by
  have hw := smoothPowerBlockWeight_le_deriv hα hαone N
  have hbase : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have hpow : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) ^ α⁻¹ :=
    Real.rpow_pos_of_pos hbase _
  have hNle : (N : ℝ) ≤ (N + 1 : ℕ) := by norm_num
  calc
    (N : ℝ) * smoothPowerBlockWeight α N /
        ((N + 1 : ℕ) : ℝ) ^ α⁻¹ ≤
      (N : ℝ) *
          (α⁻¹ * ((N + 1 : ℕ) : ℝ) ^ (α⁻¹ - 1)) /
        ((N + 1 : ℕ) : ℝ) ^ α⁻¹ := by
          gcongr
    _ = α⁻¹ * ((N : ℝ) / (N + 1 : ℕ)) := by
      rw [Real.rpow_sub_one hbase.ne']
      field_simp
    _ ≤ α⁻¹ := by
      have hratio : (N : ℝ) / (N + 1 : ℕ) ≤ 1 :=
        (div_le_one hbase).mpr hNle
      nlinarith [inv_pos.mpr hα]

/-- Summation by parts with the last weight, rather than the first unused
weight, as boundary term. -/
lemma sum_range_succ_mul_eq_last_boundary_sub_differences
    (w f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), w n * f n) =
      w N * (∑ n ∈ Finset.range (N + 1), f n) -
        ∑ n ∈ Finset.range N,
          (w (n + 1) - w n) *
            (∑ j ∈ Finset.range (n + 1), f j) := by
  have hsign :
      (∑ n ∈ Finset.range N,
          (w n - w (n + 1)) * (∑ j ∈ Finset.range (n + 1), f j)) =
        -(∑ n ∈ Finset.range N,
          (w (n + 1) - w n) * (∑ j ∈ Finset.range (n + 1), f j)) := by
    calc
      _ = ∑ n ∈ Finset.range N,
          -((w (n + 1) - w n) * (∑ j ∈ Finset.range (n + 1), f j)) := by
            apply Finset.sum_congr rfl
            intro n hn
            ring
      _ = -(∑ n ∈ Finset.range N,
          (w (n + 1) - w n) * (∑ j ∈ Finset.range (n + 1), f j)) := by
            rw [Finset.sum_neg_distrib]
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
    sum_range_mul_eq_boundary_add_differences_real, hsign]
  ring

lemma succ_mul_smoothPowerBlockWeight_div_rpow_le {α : ℝ}
    (hα : 0 < α) (hαone : α < 1) (N : ℕ) :
    ((N + 1 : ℕ) : ℝ) * smoothPowerBlockWeight α N /
        ((N + 1 : ℕ) : ℝ) ^ α⁻¹ ≤ α⁻¹ := by
  have hw := smoothPowerBlockWeight_le_deriv hα hαone N
  have hbase : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have hpow : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) ^ α⁻¹ :=
    Real.rpow_pos_of_pos hbase _
  calc
    ((N + 1 : ℕ) : ℝ) * smoothPowerBlockWeight α N /
        ((N + 1 : ℕ) : ℝ) ^ α⁻¹ ≤
      ((N + 1 : ℕ) : ℝ) *
          (α⁻¹ * ((N + 1 : ℕ) : ℝ) ^ (α⁻¹ - 1)) /
        ((N + 1 : ℕ) : ℝ) ^ α⁻¹ := by
          gcongr
    _ = α⁻¹ := by
      rw [Real.rpow_sub_one hbase.ne']
      field_simp

/-- Abel transfer: the ordinary Cesàro mean of the Möbius factor remains
unchanged after weighting by the smooth inverse-power block lengths. -/
theorem tendsto_smoothPowerBlockWeighted_mobiusCoprimeMean {α : ℝ}
    (hα : 0 < α) (hαone : α < 1) :
    Tendsto
      (fun N : ℕ ↦
        (∑ m ∈ Finset.range N,
          smoothPowerBlockWeight α m * mobiusCoprimeMean m) /
            ((N : ℝ) ^ α⁻¹))
      atTop (nhds (6 / Real.pi ^ 2)) := by
  let L : ℝ := 6 / Real.pi ^ 2
  let e : ℕ → ℝ := fun n ↦ mobiusCoprimeMean n - L
  let A : ℕ → ℝ := fun N ↦ ∑ n ∈ Finset.range N, e n
  let w : ℕ → ℝ := smoothPowerBlockWeight α
  have hmean := tendsto_mobiusCoprimeMean_average_range
  have hcenter : Tendsto (fun N : ℕ ↦ A N / (N : ℝ)) atTop (nhds 0) := by
    have hsub : Tendsto
        (fun N : ℕ ↦
          (∑ n ∈ Finset.range N, mobiusCoprimeMean n) / (N : ℝ) - L)
        atTop (nhds 0) := by
      simpa [L] using hmean.sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ L) atTop (nhds L))
    apply hsub.congr'
    filter_upwards [eventually_atTop.2 ⟨1, fun N hN ↦ hN⟩] with N hN
    simp only [A, e]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    simp only [nsmul_eq_mul]
    field_simp
  have hwmono : Monotone w := smoothPowerBlockWeight_mono hα hαone
  have hw0 : ∀ n, 0 ≤ w n := smoothPowerBlockWeight_nonneg hα
  have hden : Tendsto (fun N : ℕ ↦ ((N + 1 : ℕ) : ℝ) ^ α⁻¹)
      atTop atTop :=
    (tendsto_rpow_atTop (inv_pos.mpr hα)).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hshift : Tendsto
      (fun N : ℕ ↦
        (∑ m ∈ Finset.range (N + 1), w m * mobiusCoprimeMean m) /
          (((N + 1 : ℕ) : ℝ) ^ α⁻¹))
      atTop (nhds L) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hbeta : 0 < α⁻¹ := inv_pos.mpr hα
    let δ : ℝ := ε / (4 * (α⁻¹ + 1))
    have hδ : 0 < δ := by
      dsimp [δ]
      positivity
    obtain ⟨K, hKraw⟩ := (Metric.tendsto_atTop.1 hcenter) δ hδ
    have hK : ∀ N ≥ K, |A N / (N : ℝ)| < δ := by
      intro N hN
      simpa only [Real.dist_eq, sub_zero, abs_div] using hKraw N hN
    let C : ℝ := ∑ n ∈ Finset.range K,
      (w (n + 1) - w n) * |A (n + 1)|
    have hC : 0 ≤ C := by
      apply Finset.sum_nonneg
      intro n hn
      exact mul_nonneg (sub_nonneg.mpr (hwmono (Nat.le_succ n))) (abs_nonneg _)
    have hCevent : ∀ᶠ N : ℕ in atTop,
        C / (((N + 1 : ℕ) : ℝ) ^ α⁻¹) < ε / 2 := by
      have ht : Tendsto
          (fun N : ℕ ↦ C / (((N + 1 : ℕ) : ℝ) ^ α⁻¹))
          atTop (nhds 0) := tendsto_const_nhds.div_atTop hden
      obtain ⟨K', hK'⟩ := (Metric.tendsto_atTop.1 ht) (ε / 2) (half_pos hε)
      refine eventually_atTop.2 ⟨K', fun N hN ↦ ?_⟩
      have hpowpos : (0 : ℝ) < (((N + 1 : ℕ) : ℝ) ^ α⁻¹) :=
        Real.rpow_pos_of_pos (by positivity) _
      have hval := hK' N hN
      rw [Real.dist_eq, sub_zero, abs_div, abs_of_nonneg hC,
        abs_of_pos hpowpos] at hval
      exact hval
    obtain ⟨K', hK'⟩ := eventually_atTop.1 hCevent
    refine ⟨max K K', fun N hN ↦ ?_⟩
    have hNK : K ≤ N := (le_max_left K K').trans hN
    have hCN := hK' N ((le_max_right K K').trans hN)
    have hNK' : K ≤ N + 1 := hNK.trans (Nat.le_succ N)
    have hAN : |A (N + 1)| < δ * (N + 1 : ℕ) := by
      have hraw := hK (N + 1) hNK'
      have hpos : (0 : ℝ) < (N + 1 : ℕ) := by positivity
      rw [abs_div, abs_of_pos hpos] at hraw
      exact (div_lt_iff₀ hpos).mp hraw
    have hsum :
        ∑ n ∈ Finset.range N,
            (w (n + 1) - w n) * |A (n + 1)| ≤
          C + δ * (N + 1 : ℕ) * w N := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.range N)
        (fun n ↦ n < K)]
      apply add_le_add
      · dsimp [C]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
          exact hn.2
        · intro n hnN hnnot
          exact mul_nonneg (sub_nonneg.mpr (hwmono (Nat.le_succ n))) (abs_nonneg _)
      · calc
          ∑ n ∈ (Finset.range N).filter (fun n ↦ ¬n < K),
              (w (n + 1) - w n) * |A (n + 1)| ≤
            ∑ n ∈ (Finset.range N).filter (fun n ↦ ¬n < K),
              (w (n + 1) - w n) * (δ * (N + 1 : ℕ)) := by
                apply Finset.sum_le_sum
                intro n hn
                have hnK : K ≤ n + 1 := by
                  simp only [Finset.mem_filter, Finset.mem_range] at hn
                  omega
                have hraw := hK (n + 1) hnK
                have hnpos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
                rw [abs_div, abs_of_pos hnpos] at hraw
                have hAn : |A (n + 1)| ≤ δ * (N + 1 : ℕ) := by
                  have hlt : |A (n + 1)| < δ * (n + 1 : ℕ) :=
                    (div_lt_iff₀ hnpos).mp hraw
                  have hnle : (n + 1 : ℕ) ≤ N := by
                    simpa using (Finset.mem_range.mp (Finset.mem_filter.mp hn).1)
                  have : δ * (n + 1 : ℕ) ≤ δ * (N + 1 : ℕ) := by
                    gcongr
                    exact_mod_cast (Nat.le_succ n).trans hnle
                  exact hlt.le.trans this
                exact mul_le_mul_of_nonneg_left hAn
                  (sub_nonneg.mpr (hwmono (Nat.le_succ n)))
          _ ≤ δ * (N + 1 : ℕ) *
              (∑ n ∈ Finset.range N, (w (n + 1) - w n)) := by
                calc
                  _ = δ * (N + 1 : ℕ) *
                      (∑ n ∈ (Finset.range N).filter (fun n ↦ ¬n < K),
                        (w (n + 1) - w n)) := by
                          rw [Finset.mul_sum]
                          apply Finset.sum_congr rfl
                          intro n hn
                          ring
                  _ ≤ δ * (N + 1 : ℕ) *
                      (∑ n ∈ Finset.range N, (w (n + 1) - w n)) := by
                        apply mul_le_mul_of_nonneg_left
                        · apply Finset.sum_le_sum_of_subset_of_nonneg
                          · exact Finset.filter_subset _ _
                          · intro n hn hnnot
                            exact sub_nonneg.mpr (hwmono (Nat.le_succ n))
                        · positivity
          _ ≤ δ * (N + 1 : ℕ) * w N := by
                rw [sum_smoothPowerBlockWeight_differences]
                dsimp [w]
                have hwzero := smoothPowerBlockWeight_nonneg hα 0
                gcongr
                linarith
    have habel := sum_range_succ_mul_eq_last_boundary_sub_differences w e N
    have hcenterBound :
        |(∑ n ∈ Finset.range (N + 1), w n * e n)| ≤
          2 * δ * (N + 1 : ℕ) * w N + C := by
      rw [habel]
      calc
        |w N * A (N + 1) -
            ∑ n ∈ Finset.range N,
              (w (n + 1) - w n) * A (n + 1)| ≤
          w N * |A (N + 1)| +
            ∑ n ∈ Finset.range N,
              (w (n + 1) - w n) * |A (n + 1)| := by
                calc
                  _ ≤ |w N * A (N + 1)| +
                      |∑ n ∈ Finset.range N,
                        (w (n + 1) - w n) * A (n + 1)| := abs_sub _ _
                  _ ≤ w N * |A (N + 1)| +
                      ∑ n ∈ Finset.range N,
                        (w (n + 1) - w n) * |A (n + 1)| := by
                          rw [abs_mul, abs_of_nonneg (hw0 N)]
                          gcongr
                          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
                          apply Finset.sum_le_sum
                          intro n hn
                          rw [abs_mul, abs_of_nonneg
                            (sub_nonneg.mpr (hwmono (Nat.le_succ n)))]
        _ ≤ w N * (δ * (N + 1 : ℕ)) +
            (C + δ * (N + 1 : ℕ) * w N) := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left hAN.le (hw0 N)) hsum
        _ = 2 * δ * (N + 1 : ℕ) * w N + C := by ring
    have hdenpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) ^ α⁻¹ :=
      Real.rpow_pos_of_pos (by positivity) _
    have hratioBound :
        |(∑ n ∈ Finset.range (N + 1), w n * e n)| /
            (((N + 1 : ℕ) : ℝ) ^ α⁻¹) < ε := by
      calc
        _ ≤ (2 * δ * (N + 1 : ℕ) * w N + C) /
            (((N + 1 : ℕ) : ℝ) ^ α⁻¹) :=
          div_le_div_of_nonneg_right hcenterBound hdenpos.le
        _ = 2 * δ *
              (((N + 1 : ℕ) : ℝ) * w N /
                (((N + 1 : ℕ) : ℝ) ^ α⁻¹)) +
            C / (((N + 1 : ℕ) : ℝ) ^ α⁻¹) := by ring
        _ ≤ 2 * δ * α⁻¹ +
            C / (((N + 1 : ℕ) : ℝ) ^ α⁻¹) := by
              gcongr
              exact succ_mul_smoothPowerBlockWeight_div_rpow_le hα hαone N
        _ < ε := by
              dsimp [δ] at *
              have hbetapos : 0 < α⁻¹ := inv_pos.mpr hα
              have hfrac : 2 * (ε / (4 * (α⁻¹ + 1))) * α⁻¹ ≤ ε / 2 := by
                have heq :
                    2 * (ε / (4 * (α⁻¹ + 1))) * α⁻¹ =
                      (ε / 2) * (α⁻¹ / (α⁻¹ + 1)) := by
                  field_simp
                  ring
                rw [heq]
                apply mul_le_of_le_one_right (by positivity)
                exact (div_le_one (by positivity)).mpr (by linarith)
              linarith
    rw [Real.dist_eq]
    have hsumw : ∑ m ∈ Finset.range (N + 1), w m =
        (((N + 1 : ℕ) : ℝ) ^ α⁻¹) := by
      dsimp [w]
      rw [sum_smoothPowerBlockWeight]
      simp [Real.zero_rpow (inv_ne_zero (ne_of_gt hα))]
    have hrewrite :
        (∑ m ∈ Finset.range (N + 1), w m * mobiusCoprimeMean m) /
              (((N + 1 : ℕ) : ℝ) ^ α⁻¹) - L =
          (∑ m ∈ Finset.range (N + 1), w m * e m) /
              (((N + 1 : ℕ) : ℝ) ^ α⁻¹) := by
      simp only [e, mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
      rw [hsumw]
      field_simp
    rw [hrewrite, abs_div, abs_of_pos hdenpos]
    exact hratioBound
  exact (tendsto_add_atTop_iff_nat 1).mp (by simpa [w, L] using hshift)

lemma abs_mobiusCoprimeMean_le_divisors (m : ℕ) :
    |mobiusCoprimeMean m| ≤ m.divisors.card := by
  classical
  rcases m with _ | m
  · simp [mobiusCoprimeMean]
  · unfold mobiusCoprimeMean
    calc
      |∑ d ∈ (m + 1).divisors,
          (ArithmeticFunction.moebius d : ℝ) / d| ≤
        ∑ d ∈ (m + 1).divisors,
          |(ArithmeticFunction.moebius d : ℝ) / d| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d ∈ (m + 1).divisors, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        have hdpos : 0 < d := Nat.pos_of_dvd_of_pos
          (Nat.dvd_of_mem_divisors hd) (Nat.succ_pos m)
        have hdposR : (0 : ℝ) < d := by exact_mod_cast hdpos
        have hdabs : |(d : ℝ)| = (d : ℝ) := abs_of_pos hdposR
        rw [abs_div, hdabs]
        apply (div_le_one hdposR).mpr
        calc
          |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
            exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
          _ ≤ d := by exact_mod_cast hdpos
      _ = ((m + 1).divisors.card : ℕ) := by simp

/-- The exact coprime count on one inverse-power block differs from its
smooth Möbius model by at most four times the divisor count. -/
lemma abs_coprimePowerBlockCount_sub_smooth_main_le {α : ℝ}
    (hα : 0 < α) (m : ℕ) :
    |(coprimePowerBlockCount α m : ℝ) -
        smoothPowerBlockWeight α m * mobiusCoprimeMean m| ≤
      4 * m.divisors.card := by
  rcases m with _ | m
  · simp [coprimePowerBlockCount, powerBlockStart,
      smoothPowerBlockWeight, mobiusCoprimeMean,
      Real.zero_rpow (inv_ne_zero (ne_of_gt hα))]
  · let B : ℝ :=
      ((powerBlockStart α (m + 1 + 1) - powerBlockStart α (m + 1) : ℕ) : ℝ)
    let q : ℝ := mobiusCoprimeMean (m + 1)
    have hblock := abs_coprimePowerBlockCount_sub_main_le
      hα (m := m + 1) (Nat.succ_pos m)
    have hround := abs_powerBlockLength_sub_smooth_le_two hα (m + 1)
    have hq := abs_mobiusCoprimeMean_le_divisors (m + 1)
    calc
      |(coprimePowerBlockCount α (m + 1) : ℝ) -
          smoothPowerBlockWeight α (m + 1) * mobiusCoprimeMean (m + 1)| ≤
        |(coprimePowerBlockCount α (m + 1) : ℝ) - B * q| +
          |(B - smoothPowerBlockWeight α (m + 1)) * q| := by
            calc
              _ ≤ |(coprimePowerBlockCount α (m + 1) : ℝ) - B * q| +
                  |B * q - smoothPowerBlockWeight α (m + 1) * q| :=
                    abs_sub_le _ _ _
              _ = _ := by rw [← sub_mul]
      _ ≤ 2 * (m + 1).divisors.card +
          2 * (m + 1).divisors.card := by
            apply add_le_add hblock
            rw [abs_mul]
            exact mul_le_mul hround hq (abs_nonneg _)
              (by positivity)
      _ = 4 * (m + 1).divisors.card := by ring

/-- A fixed positive power smaller than `β - 1` bounds the total divisor
error by `o(N^β)`. -/
theorem tendsto_sum_divisors_div_rpow_zero {β : ℝ} (hβ : 1 < β) :
    Tendsto
      (fun N : ℕ ↦
        (∑ m ∈ Finset.range N, (m.divisors.card : ℝ)) / (N : ℝ) ^ β)
      atTop (nhds 0) := by
  let γ : ℝ := (β - 1) / 2
  have hγ : 0 < γ := by dsimp [γ]; linarith
  have hdiv : ∀ᶠ m : ℕ in atTop,
      (m.divisors.card : ℝ) ≤ (m : ℝ) ^ γ := by
    simpa [ArithmeticFunction.sigma_zero_apply] using weak_divisor_bound γ hγ
  obtain ⟨K, hK⟩ := eventually_atTop.1 hdiv
  let C : ℝ := ∑ m ∈ Finset.range K, (m.divisors.card : ℝ)
  have hbound : ∀ N ≥ K,
      (∑ m ∈ Finset.range N, (m.divisors.card : ℝ)) ≤
        C + (N : ℝ) * (N : ℝ) ^ γ := by
    intro N hNK
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range N)
      (fun m ↦ m < K)]
    apply add_le_add
    · dsimp [C]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro m hm
        simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢
        exact hm.2
      · intro m hmN hmnot
        positivity
    · calc
        ∑ m ∈ (Finset.range N).filter (fun m ↦ ¬m < K),
            (m.divisors.card : ℝ) ≤
          ∑ _m ∈ (Finset.range N).filter (fun m ↦ ¬m < K),
            (N : ℝ) ^ γ := by
              apply Finset.sum_le_sum
              intro m hm
              have hmK : K ≤ m := by
                simpa only [Finset.mem_filter, Finset.mem_range,
                  not_lt] using (Finset.mem_filter.mp hm).2
              exact (hK m hmK).trans (Real.rpow_le_rpow
                (Nat.cast_nonneg m)
                (by exact_mod_cast (Nat.le_of_lt
                  (Finset.mem_range.mp (Finset.mem_filter.mp hm).1))) hγ.le)
        _ ≤ (N : ℝ) * (N : ℝ) ^ γ := by
              rw [Finset.sum_const, nsmul_eq_mul]
              gcongr
              have hc : ((Finset.range N).filter (fun m ↦ ¬m < K)).card ≤ N := by
                simpa using (Finset.card_filter_le (Finset.range N)
                  (fun m ↦ ¬m < K))
              exact_mod_cast hc
  have hexp : 1 + γ - β < 0 := by dsimp [γ]; linarith
  have hpow : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (1 + γ - β))
      atTop (nhds 0) := by
    have heta : 0 < β - 1 - γ := by linarith
    convert (tendsto_rpow_neg_atTop heta).comp tendsto_natCast_atTop_atTop using 1
    ext N
    congr 1
    linarith
  have hC : Tendsto (fun N : ℕ ↦ C / (N : ℝ) ^ β) atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop
      ((tendsto_rpow_atTop (by linarith : 0 < β)).comp
        tendsto_natCast_atTop_atTop)
  have hupper : Tendsto
      (fun N : ℕ ↦ C / (N : ℝ) ^ β + (N : ℝ) ^ (1 + γ - β))
      atTop (nhds 0) := by simpa using hC.add hpow
  refine squeeze_zero' (g := fun N : ℕ ↦
    C / (N : ℝ) ^ β + (N : ℝ) ^ (1 + γ - β)) ?_ ?_ hupper
  · exact Filter.Eventually.of_forall fun N ↦ div_nonneg
      (Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)
      (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  · filter_upwards [eventually_atTop.2 ⟨max K 1, fun N hN ↦ hN⟩] with N hN
    have hNK : K ≤ N := (le_max_left K 1).trans hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast
      ((le_max_right K 1).trans hN)
    calc
      (∑ m ∈ Finset.range N, (m.divisors.card : ℝ)) / (N : ℝ) ^ β ≤
          (C + (N : ℝ) * (N : ℝ) ^ γ) / (N : ℝ) ^ β :=
        div_le_div_of_nonneg_right (hbound N hNK)
          (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      _ = C / (N : ℝ) ^ β + (N : ℝ) ^ (1 + γ - β) := by
        rw [add_div]
        rw [show (N : ℝ) * (N : ℝ) ^ γ = (N : ℝ) ^ (1 + γ) by
          rw [Real.rpow_add hNpos, Real.rpow_one]]
        rw [← Real.rpow_sub hNpos]

/-- The total rounding-and-sieving error in complete blocks is negligible
on the natural inverse-power scale. -/
theorem tendsto_coprimeBlock_error_div_rpow_zero {α : ℝ}
    (hα : 0 < α) (hαone : α < 1) :
    Tendsto
      (fun N : ℕ ↦
        ((∑ m ∈ Finset.range N, (coprimePowerBlockCount α m : ℝ)) -
          ∑ m ∈ Finset.range N,
            smoothPowerBlockWeight α m * mobiusCoprimeMean m) /
          (N : ℝ) ^ α⁻¹)
      atTop (nhds 0) := by
  have hβ : 1 < α⁻¹ := (one_lt_inv₀ hα).mpr hαone
  have hdiv := (tendsto_sum_divisors_div_rpow_zero hβ).const_mul 4
  have habs : Tendsto
      (fun N : ℕ ↦
        |((∑ m ∈ Finset.range N, (coprimePowerBlockCount α m : ℝ)) -
          ∑ m ∈ Finset.range N,
            smoothPowerBlockWeight α m * mobiusCoprimeMean m) /
          (N : ℝ) ^ α⁻¹|)
      atTop (nhds 0) := by
    apply squeeze_zero' (g := fun N : ℕ ↦
      4 * ((∑ m ∈ Finset.range N, (m.divisors.card : ℝ)) /
        (N : ℝ) ^ α⁻¹))
    · exact Filter.Eventually.of_forall fun N ↦ abs_nonneg _
    · exact Filter.Eventually.of_forall fun N ↦ by
        rw [abs_div]
        rw [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)]
        calc
          |(∑ m ∈ Finset.range N, (coprimePowerBlockCount α m : ℝ)) -
              ∑ m ∈ Finset.range N,
                smoothPowerBlockWeight α m * mobiusCoprimeMean m| /
                (N : ℝ) ^ α⁻¹ ≤
            (4 * ∑ m ∈ Finset.range N, (m.divisors.card : ℝ)) /
                (N : ℝ) ^ α⁻¹ := by
              apply div_le_div_of_nonneg_right
              · rw [← Finset.sum_sub_distrib]
                calc
                  |∑ m ∈ Finset.range N,
                      ((coprimePowerBlockCount α m : ℝ) -
                        smoothPowerBlockWeight α m * mobiusCoprimeMean m)| ≤
                    ∑ m ∈ Finset.range N,
                      |(coprimePowerBlockCount α m : ℝ) -
                        smoothPowerBlockWeight α m * mobiusCoprimeMean m| :=
                          Finset.abs_sum_le_sum_abs _ _
                  _ ≤ ∑ m ∈ Finset.range N, 4 * (m.divisors.card : ℝ) := by
                    apply Finset.sum_le_sum
                    intro m hm
                    exact abs_coprimePowerBlockCount_sub_smooth_main_le hα m
                  _ = 4 * ∑ m ∈ Finset.range N, (m.divisors.card : ℝ) := by
                    rw [Finset.mul_sum]
              · exact Real.rpow_nonneg (Nat.cast_nonneg N) _
          _ = 4 * ((∑ m ∈ Finset.range N, (m.divisors.card : ℝ)) /
              (N : ℝ) ^ α⁻¹) := by ring
    · simpa only [Function.comp_apply, mul_zero] using hdiv
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  change Tendsto
    (fun N : ℕ ↦
      |((∑ m ∈ Finset.range N, (coprimePowerBlockCount α m : ℝ)) -
        ∑ m ∈ Finset.range N,
          smoothPowerBlockWeight α m * mobiusCoprimeMean m) /
        (N : ℝ) ^ α⁻¹|) atTop (nhds 0)
  exact habs

/-- Complete inverse-power blocks have the claimed normalized density. -/
theorem tendsto_coprimePowerBlockCount_div_rpow {α : ℝ}
    (hα : 0 < α) (hαone : α < 1) :
    Tendsto
      (fun N : ℕ ↦
        (∑ m ∈ Finset.range N, (coprimePowerBlockCount α m : ℝ)) /
          (N : ℝ) ^ α⁻¹)
      atTop (nhds (6 / Real.pi ^ 2)) := by
  have hmain := tendsto_smoothPowerBlockWeighted_mobiusCoprimeMean hα hαone
  have herr := tendsto_coprimeBlock_error_div_rpow_zero hα hαone
  have hadd := herr.add hmain
  convert hadd using 1
  · ext N
    rw [sub_div]
    ring_nf
  · ring

lemma exactOneEvent_powerFloorGCD_iff_coprime_on_block {α : ℝ}
    (hα : 0 < α) {m n : ℕ}
    (hn : n ∈ Finset.Ico (powerBlockStart α m)
      (powerBlockStart α (m + 1))) :
    exactOneEvent (powerFloorGCD α) n ↔ n.Coprime m := by
  have hfloor : ⌊(n : ℝ) ^ α⌋₊ = m :=
    (floor_rpow_eq_iff_mem_powerBlock hα n m).mpr (Finset.mem_Ico.mp hn)
  rw [Nat.coprime_iff_gcd_eq_one]
  constructor
  · rintro ⟨hnpos, hone⟩
    simpa [powerFloorGCD, hfloor] using hone
  · intro hcop
    have hnpos : 0 < n := by
      by_contra hnnot
      have hnzero : n = 0 := Nat.eq_zero_of_not_pos hnnot
      have hmzero : m = 0 := by
        exact (by simpa [hnzero, Real.zero_rpow (ne_of_gt hα)] using hfloor.symm)
      subst n
      subst m
      simp at hcop
    refine ⟨hnpos, ?_⟩
    simpa [powerFloorGCD, hfloor] using hcop

lemma prefixCount_powerFloorGCD_block_succ {α : ℝ}
    (hα : 0 < α) (m : ℕ) :
    prefixCount (exactOneEvent (powerFloorGCD α)) (powerBlockStart α (m + 1)) =
      prefixCount (exactOneEvent (powerFloorGCD α)) (powerBlockStart α m) +
        coprimePowerBlockCount α m := by
  classical
  let P : ℕ → Prop := exactOneEvent (powerFloorGCD α)
  letI : DecidablePred P := Classical.decPred P
  have hmono := powerBlockStart_mono hα (Nat.le_succ m)
  have hmono' : powerBlockStart α m ≤ powerBlockStart α (m + 1) := by
    simpa only [Nat.succ_eq_add_one] using hmono
  have hunion : Finset.range (powerBlockStart α (m + 1)) =
      Finset.range (powerBlockStart α m) ∪
        Finset.Ico (powerBlockStart α m) (powerBlockStart α (m + 1)) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  have hdis : Disjoint
      (Finset.range (powerBlockStart α m))
      (Finset.Ico (powerBlockStart α m) (powerBlockStart α (m + 1))) := by
    rw [Finset.disjoint_left]
    intro n hnrange hnIco
    exact (not_lt_of_ge (Finset.mem_Ico.mp hnIco).1)
      (Finset.mem_range.mp hnrange)
  have hdisf : Disjoint
      ((Finset.range (powerBlockStart α m)).filter P)
      ((Finset.Ico (powerBlockStart α m)
        (powerBlockStart α (m + 1))).filter P) :=
    hdis.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hblock :
      ((Finset.Ico (powerBlockStart α m)
        (powerBlockStart α (m + 1))).filter P).card =
        coprimePowerBlockCount α m := by
    unfold coprimePowerBlockCount
    congr 1
    ext n
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hn, hP⟩
      exact ⟨hn, (exactOneEvent_powerFloorGCD_iff_coprime_on_block hα hn).mp hP⟩
    · rintro ⟨hn, hcop⟩
      exact ⟨hn, (exactOneEvent_powerFloorGCD_iff_coprime_on_block hα hn).mpr hcop⟩
  unfold prefixCount
  dsimp [P] at hdisf hblock
  rw [hunion, Finset.filter_union]
  calc
    _ = ((Finset.range (powerBlockStart α m)).filter
          (exactOneEvent (powerFloorGCD α))).card +
        ((Finset.Ico (powerBlockStart α m)
          (powerBlockStart α (m + 1))).filter
            (exactOneEvent (powerFloorGCD α))).card :=
      Finset.card_union_of_disjoint hdisf
    _ = _ := by rw [hblock]

/-- The sum of the complete block counts is exactly the prefix count at the
right endpoint. -/
lemma sum_coprimePowerBlockCount_eq_prefixCount {α : ℝ}
    (hα : 0 < α) (N : ℕ) :
    ∑ m ∈ Finset.range N, coprimePowerBlockCount α m =
      prefixCount (exactOneEvent (powerFloorGCD α)) (powerBlockStart α N) := by
  induction N with
  | zero => simp [powerBlockStart_zero hα, prefixCount]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih,
        prefixCount_powerFloorGCD_block_succ hα]

lemma tendsto_powerBlockStart_div_rpow {α : ℝ} (hα : 0 < α) :
    Tendsto
      (fun N : ℕ ↦ (powerBlockStart α N : ℝ) / (N : ℝ) ^ α⁻¹)
      atTop (nhds 1) := by
  exact tendsto_nat_ceil_div_atTop.comp
    ((tendsto_rpow_atTop (inv_pos.mpr hα)).comp tendsto_natCast_atTop_atTop)

/-- Density along the complete inverse-power block endpoints. -/
theorem tendsto_prefixRatio_powerBlockStart {α : ℝ}
    (hα : 0 < α) (hαone : α < 1) :
    Tendsto
      (fun N : ℕ ↦ prefixRatio (exactOneEvent (powerFloorGCD α))
        (powerBlockStart α N))
      atTop (nhds (6 / Real.pi ^ 2)) := by
  have hblocks := tendsto_coprimePowerBlockCount_div_rpow hα hαone
  have hceil := tendsto_powerBlockStart_div_rpow hα
  have hquot := hblocks.div hceil (by norm_num : (1 : ℝ) ≠ 0)
  have hquot' : Tendsto
      ((fun N : ℕ ↦
        (∑ m ∈ Finset.range N, (coprimePowerBlockCount α m : ℝ)) /
          (N : ℝ) ^ α⁻¹) /
        (fun N : ℕ ↦ (powerBlockStart α N : ℝ) / (N : ℝ) ^ α⁻¹))
      atTop (nhds (6 / Real.pi ^ 2)) := by simpa using hquot
  apply hquot'.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hpowpos : (0 : ℝ) < (N : ℝ) ^ α⁻¹ :=
    Real.rpow_pos_of_pos (by exact_mod_cast hN) _
  have hsumcast :
      (∑ m ∈ Finset.range N, (coprimePowerBlockCount α m : ℝ)) =
        (prefixCount (exactOneEvent (powerFloorGCD α))
          (powerBlockStart α N) : ℝ) := by
    exact_mod_cast sum_coprimePowerBlockCount_eq_prefixCount hα N
  rw [prefixRatio]
  change
    ((∑ m ∈ Finset.range N, (coprimePowerBlockCount α m : ℝ)) /
      (N : ℝ) ^ α⁻¹) /
      ((powerBlockStart α N : ℝ) / (N : ℝ) ^ α⁻¹) =
    (prefixCount (exactOneEvent (powerFloorGCD α))
      (powerBlockStart α N) : ℝ) / (powerBlockStart α N : ℝ)
  rw [hsumcast]
  field_simp

lemma tendsto_powerBlockStart_atTop {α : ℝ} (hα : 0 < α) :
    Tendsto (powerBlockStart α) atTop atTop := by
  exact tendsto_nat_ceil_atTop.comp
    ((tendsto_rpow_atTop (inv_pos.mpr hα)).comp
      tendsto_natCast_atTop_atTop)

/-- An abstract squeeze between adjacent endpoints of an asymptotically
dense increasing scale. -/
theorem tendsto_of_tendsto_on_adjacent_endpoints
    {a j : ℕ → ℕ} {c : ℕ → ℝ} {L : ℝ}
    (haTop : Tendsto a atTop atTop)
    (hjTop : Tendsto j atTop atTop)
    (hbracket : ∀ N, a (j N) ≤ N ∧ N < a (j N + 1))
    (hc : Monotone c)
    (hendpoint : Tendsto (fun m ↦ c (a m) / (a m : ℝ)) atTop (nhds L))
    (hlowerRatio : Tendsto (fun N ↦ (a (j N) : ℝ) / (N : ℝ)) atTop (nhds 1))
    (hupperRatio : Tendsto (fun N ↦ (a (j N + 1) : ℝ) / (N : ℝ)) atTop (nhds 1)) :
    Tendsto (fun N ↦ c N / (N : ℝ)) atTop (nhds L) := by
  have hjSuccTop : Tendsto (fun N ↦ j N + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hjTop
  have haLowerTop : Tendsto (fun N ↦ a (j N)) atTop atTop :=
    haTop.comp hjTop
  have haUpperTop : Tendsto (fun N ↦ a (j N + 1)) atTop atTop :=
    haTop.comp hjSuccTop
  have hlower :
      Tendsto (fun N ↦ c (a (j N)) / (N : ℝ)) atTop (nhds L) := by
    have h := (hendpoint.comp hjTop).mul hlowerRatio
    have h' : Tendsto
        (fun N ↦ (c (a (j N)) / (a (j N) : ℝ)) *
          ((a (j N) : ℝ) / (N : ℝ))) atTop (nhds L) := by
      simpa only [Function.comp_apply, mul_one] using h
    exact h'.congr' (by
      filter_upwards [haLowerTop.eventually_gt_atTop 0] with N hN
      have hne : (a (j N) : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      field_simp)
  have hupper :
      Tendsto (fun N ↦ c (a (j N + 1)) / (N : ℝ)) atTop (nhds L) := by
    have h := (hendpoint.comp hjSuccTop).mul hupperRatio
    have h' : Tendsto
        (fun N ↦ (c (a (j N + 1)) / (a (j N + 1) : ℝ)) *
          ((a (j N + 1) : ℝ) / (N : ℝ))) atTop (nhds L) := by
      simpa only [Function.comp_apply, mul_one] using h
    exact h'.congr' (by
      filter_upwards [haUpperTop.eventually_gt_atTop 0] with N hN
      have hne : (a (j N + 1) : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      field_simp)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [eventually_gt_atTop 0] with N hN
    exact div_le_div_of_nonneg_right (hc (hbracket N).1)
      (by positivity : (0 : ℝ) ≤ N)
  · filter_upwards [eventually_gt_atTop 0] with N hN
    exact div_le_div_of_nonneg_right (hc (hbracket N).2.le)
      (by positivity : (0 : ℝ) ≤ N)

lemma tendsto_floor_rpow_atTop {α : ℝ} (hα : 0 < α) :
    Tendsto (fun N : ℕ ↦ ⌊(N : ℝ) ^ α⌋₊) atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop)

lemma tendsto_floor_rpow_inv_div_nat {α : ℝ} (hα : 0 < α) :
    Tendsto
      (fun N : ℕ ↦
        ((⌊(N : ℝ) ^ α⌋₊ : ℝ) ^ α⁻¹) / (N : ℝ))
      atTop (nhds 1) := by
  let x : ℕ → ℝ := fun N ↦ (N : ℝ) ^ α
  have hxTop : Tendsto x atTop atTop :=
    (tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop
  have hfloorRatio :
      Tendsto (fun N ↦ (⌊x N⌋₊ : ℝ) / x N) atTop (nhds 1) :=
    tendsto_nat_floor_div_atTop.comp hxTop
  have hrpowRatio :
      Tendsto (fun N ↦ (((⌊x N⌋₊ : ℝ) / x N) ^ α⁻¹))
        atTop (nhds 1) := by
    simpa using hfloorRatio.rpow tendsto_const_nhds (Or.inl one_ne_zero)
  apply hrpowRatio.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hxpos : 0 < x N := Real.rpow_pos_of_pos hNpos α
  rw [Real.div_rpow (Nat.cast_nonneg _) hxpos.le]
  have hxpow : (x N) ^ α⁻¹ = (N : ℝ) := by
    dsimp [x]
    rw [Real.rpow_rpow_inv (Nat.cast_nonneg N) (ne_of_gt hα)]
  rw [hxpow]

lemma tendsto_powerBlockStart_floor_rpow_div_nat {α : ℝ}
    (hα : 0 < α) :
    Tendsto
      (fun N : ℕ ↦
        (powerBlockStart α ⌊(N : ℝ) ^ α⌋₊ : ℝ) / (N : ℝ))
      atTop (nhds 1) := by
  let y : ℕ → ℝ := fun N ↦ ((⌊(N : ℝ) ^ α⌋₊ : ℝ) ^ α⁻¹)
  have hyTop : Tendsto y atTop atTop := by
    have hfloorTop : Tendsto
        (fun N : ℕ ↦ (⌊(N : ℝ) ^ α⌋₊ : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_floor_rpow_atTop hα)
    exact (tendsto_rpow_atTop (inv_pos.mpr hα)).comp hfloorTop
  have hceilRatio :
      Tendsto (fun N ↦ (⌈y N⌉₊ : ℝ) / y N) atTop (nhds 1) :=
    tendsto_nat_ceil_div_atTop.comp hyTop
  have hyRatio : Tendsto (fun N ↦ y N / (N : ℝ)) atTop (nhds 1) := by
    simpa [y] using tendsto_floor_rpow_inv_div_nat hα
  have hprod : Tendsto
      (fun N ↦ ((⌈y N⌉₊ : ℝ) / y N) * (y N / (N : ℝ)))
        atTop (nhds 1) := by
    simpa only [mul_one] using hceilRatio.mul hyRatio
  exact hprod.congr' (by
    filter_upwards [hyTop.eventually_gt_atTop 0] with N hN
    have hyne : y N ≠ 0 := ne_of_gt hN
    dsimp [powerBlockStart]
    change ((⌈y N⌉₊ : ℝ) / y N) * (y N / (N : ℝ)) =
      (⌈y N⌉₊ : ℝ) / (N : ℝ)
    field_simp)

lemma tendsto_powerBlockStart_succ_floor_rpow_div_nat {α : ℝ}
    (hα : 0 < α) :
    Tendsto
      (fun N : ℕ ↦
        (powerBlockStart α (⌊(N : ℝ) ^ α⌋₊ + 1) : ℝ) / (N : ℝ))
      atTop (nhds 1) := by
  let z : ℕ → ℝ := fun N ↦
    (((⌊(N : ℝ) ^ α⌋₊ + 1 : ℕ) : ℝ) ^ α⁻¹)
  have hbaseRatio : Tendsto
      (fun N : ℕ ↦ (((⌊(N : ℝ) ^ α⌋₊ + 1 : ℕ) : ℝ) /
        ((N : ℝ) ^ α))) atTop (nhds 1) := by
    have hfloorRatio := tendsto_nat_floor_div_atTop.comp
      ((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop)
    have hone : Tendsto (fun N : ℕ ↦ (1 : ℝ) / ((N : ℝ) ^ α))
        atTop (nhds 0) := tendsto_const_nhds.div_atTop
          ((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop)
    have hsum : Tendsto
        (fun N : ℕ ↦ (⌊(N : ℝ) ^ α⌋₊ : ℝ) / ((N : ℝ) ^ α) +
          (1 : ℝ) / ((N : ℝ) ^ α)) atTop (nhds 1) := by
      simpa only [Function.comp_apply, add_zero] using hfloorRatio.add hone
    exact hsum.congr' (by
      filter_upwards with N
      push_cast
      ring)
  have hpowRatio : Tendsto
      (fun N : ℕ ↦ ((((⌊(N : ℝ) ^ α⌋₊ + 1 : ℕ) : ℝ) /
        ((N : ℝ) ^ α)) ^ α⁻¹)) atTop (nhds 1) := by
    simpa using hbaseRatio.rpow tendsto_const_nhds (Or.inl one_ne_zero)
  have hzRatio : Tendsto (fun N ↦ z N / (N : ℝ)) atTop (nhds 1) := by
    exact hpowRatio.congr' (by
      filter_upwards [eventually_gt_atTop 0] with N hN
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      change ((((⌊(N : ℝ) ^ α⌋₊ + 1 : ℕ) : ℝ) /
        ((N : ℝ) ^ α)) ^ α⁻¹) = z N / (N : ℝ)
      rw [Real.div_rpow (by positivity) (Real.rpow_nonneg hNpos.le _)]
      dsimp [z]
      rw [Real.rpow_rpow_inv hNpos.le (ne_of_gt hα)])
  have hzTop : Tendsto z atTop atTop := by
    exact (tendsto_rpow_atTop (inv_pos.mpr hα)).comp
      (tendsto_natCast_atTop_atTop.comp
        ((tendsto_add_atTop_nat 1).comp (tendsto_floor_rpow_atTop hα)))
  have hceilRatio : Tendsto (fun N ↦ (⌈z N⌉₊ : ℝ) / z N) atTop (nhds 1) :=
    tendsto_nat_ceil_div_atTop.comp hzTop
  have hprod : Tendsto
      (fun N ↦ ((⌈z N⌉₊ : ℝ) / z N) * (z N / (N : ℝ)))
        atTop (nhds 1) := by
    simpa only [mul_one] using hceilRatio.mul hzRatio
  exact hprod.congr' (by
    filter_upwards [hzTop.eventually_gt_atTop 0] with N hN
    have hzne : z N ≠ 0 := ne_of_gt hN
    dsimp [powerBlockStart]
    change ((⌈z N⌉₊ : ℝ) / z N) * (z N / (N : ℝ)) =
      (⌈z N⌉₊ : ℝ) / (N : ℝ)
    field_simp)

lemma prefixCount_mono (P : ℕ → Prop) : Monotone (prefixCount P) := by
  classical
  intro M N hMN
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
  exact ⟨hn.1.trans_le hMN, hn.2⟩

/-- Interpolation from complete inverse-power blocks to every prefix. -/
theorem tendsto_prefixRatio_of_powerBlock_endpoints
    {α L : ℝ} (hα : 0 < α) (P : ℕ → Prop)
    (hendpoint : Tendsto
      (fun m ↦ prefixRatio P (powerBlockStart α m)) atTop (nhds L)) :
    Tendsto (prefixRatio P) atTop (nhds L) := by
  unfold prefixRatio at hendpoint ⊢
  apply tendsto_of_tendsto_on_adjacent_endpoints
    (tendsto_powerBlockStart_atTop hα)
    (tendsto_floor_rpow_atTop hα)
    (fun N ↦ (floor_rpow_eq_iff_mem_powerBlock hα N _).mp rfl)
    (fun _ _ h ↦ by exact_mod_cast prefixCount_mono P h)
    hendpoint
    (tendsto_powerBlockStart_floor_rpow_div_nat hα)
    (tendsto_powerBlockStart_succ_floor_rpow_div_nat hα)

/-- Erdős 1149 in the sublinear range, proved by exact inverse-power blocks
and Möbius summation. -/
theorem sublinear_exactOne_tendsto (α : ℝ) (hα : 0 < α) (hαone : α < 1) :
    Tendsto (prefixRatio (exactOneEvent (powerFloorGCD α))) atTop
      (nhds (6 / Real.pi ^ 2)) := by
  exact tendsto_prefixRatio_of_powerBlock_endpoints hα
    (exactOneEvent (powerFloorGCD α))
    (tendsto_prefixRatio_powerBlockStart hα hαone)

end

end Erdos1149
