import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped BigOperators
open Filter Finset

namespace Erdos1211DensityNat

noncomputable section

open Classical

def harmonicPrefix (X : Set ℕ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico 1 N, if n ∈ X then (n : ℝ)⁻¹ else 0

def logRatio (X : Set ℕ) (N : ℕ) : ℝ :=
  harmonicPrefix X N / Real.log (N : ℝ)

def upperLogDensity (X : Set ℕ) : ℝ :=
  Filter.limsup (logRatio X) Filter.atTop

lemma harmonicPrefix_eq_sum_filter (X : Set ℕ) (N : ℕ) :
    harmonicPrefix X N =
      ∑ n ∈ (Finset.Ico 1 N).filter (fun n ↦ n ∈ X), (n : ℝ)⁻¹ := by
  simp [harmonicPrefix, Finset.sum_filter]

lemma harmonicPrefix_univ (N : ℕ) :
    harmonicPrefix Set.univ N = ((harmonic (N - 1) : ℚ) : ℝ) := by
  cases N with
  | zero => simp [harmonicPrefix, harmonic]
  | succ N =>
      simp only [harmonicPrefix, Set.mem_univ, if_true]
      rw [Finset.sum_Ico_eq_sum_range]
      simp [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, add_comm]

lemma harmonicPrefix_nonneg (X : Set ℕ) (N : ℕ) : 0 ≤ harmonicPrefix X N := by
  apply Finset.sum_nonneg
  intro i hi
  split_ifs
  · positivity
  · exact le_rfl

lemma harmonicPrefix_mono {X Y : Set ℕ} (hXY : X ⊆ Y) (N : ℕ) :
    harmonicPrefix X N ≤ harmonicPrefix Y N := by
  apply Finset.sum_le_sum
  intro i hi
  by_cases hiX : i ∈ X
  · have hiY : i ∈ Y := hXY hiX
    simp [hiX, hiY]
  · simp [hiX]
    split_ifs
    · positivity
    · exact le_rfl

lemma log_natCast_nonneg (N : ℕ) : 0 ≤ Real.log (N : ℝ) := by
  cases N with
  | zero => simp
  | succ N =>
      exact Real.log_nonneg (by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le N))

lemma logRatio_nonneg (X : Set ℕ) (N : ℕ) : 0 ≤ logRatio X N := by
  exact div_nonneg (harmonicPrefix_nonneg X N) (log_natCast_nonneg N)

lemma logRatio_mono {X Y : Set ℕ} (hXY : X ⊆ Y) (N : ℕ) :
    logRatio X N ≤ logRatio Y N := by
  exact div_le_div_of_nonneg_right (harmonicPrefix_mono hXY N)
    (log_natCast_nonneg N)

lemma tendsto_nat_sub_one_atTop : Tendsto (fun N : ℕ ↦ N - 1) atTop atTop := by
  exact Filter.tendsto_sub_atTop_nat 1

lemma tendsto_harmonic_cast_sub_one_sub_log :
    Tendsto
      (fun N : ℕ ↦ ((harmonic (N - 1) : ℚ) : ℝ) - Real.log ((N - 1 : ℕ) : ℝ))
      atTop (nhds Real.eulerMascheroniConstant) := by
  exact Real.tendsto_harmonic_sub_log.comp tendsto_nat_sub_one_atTop

lemma tendsto_log_nat_atTop : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop := by
  exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma tendsto_log_sub_one_div_log :
    Tendsto (fun N : ℕ ↦ Real.log ((N - 1 : ℕ) : ℝ) / Real.log (N : ℝ)) atTop (nhds 1) := by
  have hdiff' :
      Tendsto (fun N : ℕ ↦ Real.log (N : ℝ) - Real.log ((N - 1 : ℕ) : ℝ))
        atTop (nhds 0) := by
    refine (Real.tendsto_log_nat_add_one_sub_log.comp tendsto_nat_sub_one_atTop).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    norm_num [Function.comp_apply, Nat.cast_sub hN]
  have hdiff :
      Tendsto (fun N : ℕ ↦ Real.log ((N - 1 : ℕ) : ℝ) - Real.log (N : ℝ))
        atTop (nhds 0) := by
    simpa only [neg_sub, neg_zero] using hdiff'.neg
  have hzero :
      Tendsto
        (fun N : ℕ ↦
          (Real.log ((N - 1 : ℕ) : ℝ) - Real.log (N : ℝ)) / Real.log (N : ℝ))
        atTop (nhds 0) := hdiff.div_atTop tendsto_log_nat_atTop
  have hone := (tendsto_const_nhds (x := (1 : ℝ))).add hzero
  have heq :
      (fun N : ℕ ↦
          (1 : ℝ) +
            (Real.log ((N - 1 : ℕ) : ℝ) - Real.log (N : ℝ)) / Real.log (N : ℝ)) =ᶠ[atTop]
        (fun N : ℕ ↦ Real.log ((N - 1 : ℕ) : ℝ) / Real.log (N : ℝ)) := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hlog : Real.log (N : ℝ) ≠ 0 := by
      have hNpos : (0 : ℝ) < N := by
        exact_mod_cast Nat.zero_lt_of_lt (Nat.lt_of_lt_of_le Nat.one_lt_two hN)
      apply Real.log_ne_zero_of_pos_of_ne_one hNpos
      have hN1 : N ≠ 1 := ne_of_gt (Nat.lt_of_lt_of_le Nat.one_lt_two hN)
      exact_mod_cast hN1
    field_simp
    ring
  simpa only [add_zero] using hone.congr' heq

lemma logRatio_univ_tendsto_one : Tendsto (logRatio Set.univ) atTop (nhds 1) := by
  have herrorZero :
      Tendsto
        (fun N : ℕ ↦
          (((harmonic (N - 1) : ℚ) : ℝ) - Real.log ((N - 1 : ℕ) : ℝ)) /
            Real.log (N : ℝ))
        atTop (nhds 0) :=
    tendsto_harmonic_cast_sub_one_sub_log.div_atTop tendsto_log_nat_atTop
  have hsum := herrorZero.add tendsto_log_sub_one_div_log
  have heq :
      (fun N : ℕ ↦
          (((harmonic (N - 1) : ℚ) : ℝ) - Real.log ((N - 1 : ℕ) : ℝ)) /
              Real.log (N : ℝ) +
            Real.log ((N - 1 : ℕ) : ℝ) / Real.log (N : ℝ)) =ᶠ[atTop]
        logRatio Set.univ := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    rw [logRatio, harmonicPrefix_univ]
    have hlog : Real.log (N : ℝ) ≠ 0 := by
      have hNpos : (0 : ℝ) < N := by
        exact_mod_cast Nat.zero_lt_of_lt (Nat.lt_of_lt_of_le Nat.one_lt_two hN)
      apply Real.log_ne_zero_of_pos_of_ne_one hNpos
      have hN1 : N ≠ 1 := ne_of_gt (Nat.lt_of_lt_of_le Nat.one_lt_two hN)
      exact_mod_cast hN1
    field_simp
    ring
  simpa only [zero_add] using hsum.congr' heq

lemma isCoboundedUnder_le_logRatio (X : Set ℕ) :
    IsCoboundedUnder (· ≤ ·) atTop (logRatio X) := by
  exact (isBoundedUnder_of ⟨0, fun N ↦ logRatio_nonneg X N⟩).isCoboundedUnder_le

lemma isBoundedUnder_le_logRatio (X : Set ℕ) :
    IsBoundedUnder (· ≤ ·) atTop (logRatio X) := by
  have hu : ∀ᶠ N in atTop, logRatio Set.univ N ≤ 2 :=
    (logRatio_univ_tendsto_one.eventually (Iic_mem_nhds (show (1 : ℝ) < 2 by norm_num)))
  apply isBoundedUnder_of_eventually_le
  filter_upwards [hu] with N hN
  exact (logRatio_mono (Set.subset_univ X) N).trans hN

lemma upperLogDensity_mono {X Y : Set ℕ} (hXY : X ⊆ Y) :
    upperLogDensity X ≤ upperLogDensity Y := by
  exact Filter.limsup_le_limsup
    (Filter.Eventually.of_forall (logRatio_mono hXY))
    (isCoboundedUnder_le_logRatio X) (isBoundedUnder_le_logRatio Y)

lemma upperLogDensity_le_of_eventually_logRatio_le {X Y : Set ℕ}
    (h : ∀ᶠ N in atTop, logRatio X N ≤ logRatio Y N) :
    upperLogDensity X ≤ upperLogDensity Y := by
  exact Filter.limsup_le_limsup h
    (isCoboundedUnder_le_logRatio X) (isBoundedUnder_le_logRatio Y)

lemma upperLogDensity_le_of_eventually_le {X : Set ℕ} {c : ℝ}
    (h : ∀ᶠ N in atTop, logRatio X N ≤ c) : upperLogDensity X ≤ c := by
  exact Filter.limsup_le_of_le (isCoboundedUnder_le_logRatio X) h

lemma le_upperLogDensity_of_frequently_le {X : Set ℕ} {c : ℝ}
    (h : ∃ᶠ N in atTop, c ≤ logRatio X N) : c ≤ upperLogDensity X := by
  exact Filter.le_limsup_of_frequently_le h (isBoundedUnder_le_logRatio X)

lemma upperLogDensity_eq_of_tendsto {X : Set ℕ} {c : ℝ}
    (h : Tendsto (logRatio X) atTop (nhds c)) : upperLogDensity X = c := by
  exact h.limsup_eq

lemma upperLogDensity_univ : upperLogDensity Set.univ = 1 := by
  exact logRatio_univ_tendsto_one.limsup_eq

lemma upperLogDensity_nonneg (X : Set ℕ) : 0 ≤ upperLogDensity X := by
  exact le_limsup_of_frequently_le
    (Frequently.of_forall (logRatio_nonneg X)) (isBoundedUnder_le_logRatio X)

lemma upperLogDensity_le_one (X : Set ℕ) : upperLogDensity X ≤ 1 := by
  rw [← upperLogDensity_univ]
  exact upperLogDensity_mono (Set.subset_univ X)

end

end Erdos1211DensityNat
