/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
An integrated maximal estimate for the analytic part of Erdős 521.
The logarithmic loss is harmless in the polynomially decaying probability estimates.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.Maximal
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Erdos521

open MeasureTheory Filter
open scoped BigOperators

/-- Integrating a weak tail bound up to a deterministic cutoff incurs only a
logarithm. This form avoids needing the full Doob `L²` inequality. -/
theorem integral_le_of_weak_tail_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ} {V M : ℝ}
    (hf : Integrable f μ) (hnonneg : ∀ᵐ ω ∂μ, 0 ≤ f ω) (hbounded : ∀ᵐ ω ∂μ, f ω ≤ M)
    (hV : 0 < V) (hVM : V ≤ M)
    (htail : ∀ t : ℝ, 0 < t → μ.real {ω | t ≤ f ω} ≤ V / t) :
    (∫ ω, f ω ∂μ) ≤ V * (1 + Real.log (M / V)) := by
  let q : ℝ → ℝ := fun t ↦ μ.real {ω | t ≤ f ω}
  have hqmono : Antitone q := by
    intro s t hst
    exact measureReal_mono (fun _ h ↦ hst.trans h)
  have hqint (a b : ℝ) : IntervalIntegrable q volume a b := by
    apply IntervalIntegrable.mono_fun' (g := fun _ ↦ (1 : ℝ)) (by simp)
      hqmono.measurable.aestronglyMeasurable
    exact Eventually.of_forall fun t ↦ by
      change ‖μ.real {ω | t ≤ f ω}‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (measureReal_nonneg)]
      exact measureReal_le_one
  have hM : 0 < M := hV.trans_le hVM
  have hdivint : IntervalIntegrable (fun t : ℝ ↦ V / t) volume V M := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div continuousOn_id
    intro t ht
    rw [Set.uIcc_of_le hVM] at ht
    exact (hV.trans_le ht.1).ne'
  have hfirst : (∫ t in (0 : ℝ)..V, q t) ≤ V := by
    have h := intervalIntegral.integral_mono_on hV.le (hqint 0 V) intervalIntegrable_const
      (fun _ _ ↦ (measureReal_le_one : μ.real _ ≤ 1))
    simpa using h
  have hsecond : (∫ t in V..M, q t) ≤ V * Real.log (M / V) := by
    calc
      (∫ t in V..M, q t) ≤ ∫ t in V..M, V / t :=
        intervalIntegral.integral_mono_on hVM (hqint V M) hdivint
          (fun t ht ↦ htail t (hV.trans_le ht.1))
      _ = V * Real.log (M / V) := by
        simp only [div_eq_mul_inv, intervalIntegral.integral_const_mul]
        rw [integral_inv_of_pos hV hM]
        rw [div_eq_mul_inv]
  rw [hf.integral_eq_integral_Ioc_meas_le hnonneg hbounded,
    ← intervalIntegral.integral_of_le hM.le]
  change (∫ t in (0 : ℝ)..M, q t) ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals (hqint 0 V) (hqint V M)]
  linarith

noncomputable def maximumSquaredPartialSum (a : ℕ → ℝ) (n : ℕ) (ε : ℕ → ℝ) : ℝ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
    (fun k ↦ (weightedPartialSum a k ε) ^ 2)

theorem maximumSquaredPartialSum_nonneg (a : ℕ → ℝ) (n : ℕ) (ε : ℕ → ℝ) :
    0 ≤ maximumSquaredPartialSum a n ε := by
  exact (sq_nonneg (weightedPartialSum a 0 ε)).trans
    (Finset.le_sup' (fun k ↦ (weightedPartialSum a k ε) ^ 2) (by simp))

theorem maximumSquaredPartialSum_measurable (a : ℕ → ℝ) (n : ℕ) :
    Measurable (maximumSquaredPartialSum a n) := by
  apply Finset.measurable_range_sup''
  intro k _
  have hm : Measurable (weightedPartialSum a k) :=
    (weightedPartialSum_stronglyAdapted a k).measurable.le ((weightedFiltration a).le k)
  exact hm.pow_const 2

theorem ae_maximumSquaredPartialSum_le (a : ℕ → ℝ) (n : ℕ) :
    ∀ᵐ ε ∂sequenceLaw, maximumSquaredPartialSum a n ε ≤
      (n + 1 : ℝ) * ∑ i ∈ Finset.range (n + 1), (a i) ^ 2 := by
  filter_upwards [ae_sequence_signs] with ε hε
  apply Finset.sup'_le
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (k + 1))
    (fun i ↦ a i * ε i) (fun _ ↦ (1 : ℝ))
  have hsquare (i : ℕ) : (a i * ε i) ^ 2 = (a i) ^ 2 := by
    rcases hε i with h | h <;> simp [h]
  simp only [mul_one, hsquare, one_pow, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_one] at hcs
  have hvars : (∑ i ∈ Finset.range (k + 1), (a i) ^ 2) ≤
      ∑ i ∈ Finset.range (n + 1), (a i) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun _ _ _ ↦ sq_nonneg _)
  have hkn' : (k : ℝ) + 1 ≤ n + 1 := by exact_mod_cast Nat.add_le_add_right hkn 1
  exact hcs.trans ((mul_le_mul hvars hkn' (by positivity) (by positivity)).trans_eq (mul_comm _ _))

theorem maximumSquaredPartialSum_integrable (a : ℕ → ℝ) (n : ℕ) :
    Integrable (maximumSquaredPartialSum a n) sequenceLaw := by
  apply Integrable.mono'
    (integrable_const ((n + 1 : ℝ) * ∑ i ∈ Finset.range (n + 1), (a i) ^ 2))
    (maximumSquaredPartialSum_measurable a n).aestronglyMeasurable
  filter_upwards [ae_maximumSquaredPartialSum_le a n] with ε hε
  simpa only [Real.norm_eq_abs, abs_of_nonneg (maximumSquaredPartialSum_nonneg a n ε)] using hε

/-- The maximal second moment is bounded by the terminal variance times a
logarithmic factor. This suffices for the near-endpoint probability estimates. -/
theorem integral_maximumSquaredPartialSum_le (a : ℕ → ℝ) (n : ℕ) :
    (∫ ε, maximumSquaredPartialSum a n ε ∂sequenceLaw) ≤
      (∑ i ∈ Finset.range (n + 1), (a i) ^ 2) * (1 + Real.log (n + 1)) := by
  let V : ℝ := ∑ i ∈ Finset.range (n + 1), (a i) ^ 2
  have hV : 0 ≤ V := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  obtain hzero | hpos := hV.eq_or_lt
  · have hbound := ae_maximumSquaredPartialSum_le a n
    have heq : maximumSquaredPartialSum a n =ᵐ[sequenceLaw] fun _ ↦ (0 : ℝ) := by
      filter_upwards [hbound] with ε hε
      change maximumSquaredPartialSum a n ε ≤ (n + 1 : ℝ) * V at hε
      rw [← hzero, mul_zero] at hε
      exact le_antisymm hε (maximumSquaredPartialSum_nonneg a n ε)
    rw [integral_congr_ae heq]
    change _ ≤ V * _
    simp [← hzero]
  · have hbound := integral_le_of_weak_tail_bound sequenceLaw
      (maximumSquaredPartialSum_integrable a n)
      (Eventually.of_forall (maximumSquaredPartialSum_nonneg a n))
      (ae_maximumSquaredPartialSum_le a n) hpos
      (show V ≤ (n + 1 : ℝ) * V by nlinarith [Nat.cast_nonneg (α := ℝ) n]) ?_
    · change _ ≤ V * _
      change (∫ ε, maximumSquaredPartialSum a n ε ∂sequenceLaw) ≤
        V * (1 + Real.log (((n + 1 : ℝ) * V) / V)) at hbound
      simpa only [mul_div_cancel_right₀ _ hpos.ne'] using hbound
    · intro t ht
      have h := weightedPartialSum_maximal a n (Real.sqrt_pos.mpr ht)
      simpa only [Real.sq_sqrt ht.le, maximumSquaredPartialSum, V] using h

end Erdos521
