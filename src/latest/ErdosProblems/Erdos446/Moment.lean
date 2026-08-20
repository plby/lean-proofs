import ErdosProblems.Erdos446.Cluster
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

open Finset Set MeasureTheory Real
open scoped BigOperators ENNReal NNReal Topology

/-!
# Erdős Problem 446: the divisor-cluster second moment

This module proves the finite-union second-moment inequality used in Ford's
argument.  It is then specialized below to the logarithmic intervals attached
to the divisors of an integer.
-/

namespace Erdos446

variable {X ι : Type*} [MeasurableSpace X] {μ : Measure X}

private noncomputable def ind (A : ι → Set X) (i : ι) (x : X) : ℝ :=
  (A i).indicator (fun _ ↦ (1 : ℝ)) x

private lemma ind_nonneg (A : ι → Set X) (i : ι) (x : X) :
    0 ≤ ind A i x := by
  by_cases hx : x ∈ A i <;> simp [ind, hx]

private lemma ind_mul_ind (A : ι → Set X) (i j : ι) (x : X) :
    ind A i x * ind A j x = (A i ∩ A j).indicator (fun _ ↦ (1 : ℝ)) x := by
  by_cases hi : x ∈ A i <;> by_cases hj : x ∈ A j <;>
    simp [ind, hi, hj]

/-- The finite-set form of the Cauchy--Schwarz second-moment inequality:
the square of the sum of the individual measures is at most the measure of
their union times the sum of all pairwise intersection measures. -/
theorem finite_union_second_moment
    (s : Finset ι) (A : ι → Set X)
    (hA : ∀ i ∈ s, MeasurableSet (A i))
    (hAfin : ∀ i ∈ s, μ (A i) ≠ ∞) :
    (∑ i ∈ s, μ.real (A i)) ^ 2 ≤
      μ.real (⋃ i ∈ s, A i) *
        (∑ i ∈ s, ∑ j ∈ s, μ.real (A i ∩ A j)) := by
  classical
  let U : Set X := ⋃ i ∈ s, A i
  let f : X → ℝ := fun x ↦ ∑ i ∈ s, ind A i x
  let g : X → ℝ := U.indicator (fun _ ↦ (1 : ℝ))
  have hUmeas : MeasurableSet U := by
    dsimp [U]
    exact Finset.measurableSet_biUnion s hA
  have hUfin : μ U ≠ ∞ := by
    have hle : μ U ≤ ∑ i ∈ s, μ (A i) := by
      simpa [U] using measure_biUnion_finset_le (μ := μ) s A
    exact ne_of_lt (lt_of_le_of_lt hle
      (ENNReal.sum_lt_top.mpr fun i hi ↦ lt_top_iff_ne_top.mpr (hAfin i hi)))
  have hind_memLp (i : ι) (hi : i ∈ s) :
      MemLp (ind A i) (ENNReal.ofReal 2) μ := by
    change MemLp ((A i).indicator fun _ ↦ (1 : ℝ)) (ENNReal.ofReal 2) μ
    exact memLp_indicator_const (μ := μ) (ENNReal.ofReal 2) (hA i hi)
      (1 : ℝ) (Or.inr (hAfin i hi))
  have hsum_memLp : ∀ t : Finset ι,
      (∀ i ∈ t, MemLp (ind A i) (ENNReal.ofReal 2) μ) →
        MemLp (fun x ↦ ∑ i ∈ t, ind A i x) (ENNReal.ofReal 2) μ := by
    intro t ht
    induction t using Finset.induction_on with
    | empty => simpa using
        (MemLp.zero : MemLp (fun _ : X ↦ (0 : ℝ)) (ENNReal.ofReal 2) μ)
    | @insert i t hi ih =>
        have hiLp := ht i (Finset.mem_insert_self i t)
        have htLp : ∀ j ∈ t, MemLp (ind A j) (ENNReal.ofReal 2) μ :=
          fun j hj ↦ ht j (Finset.mem_insert_of_mem hj)
        convert hiLp.add (ih htLp) using 1 <;> ext x <;>
          simp only [Pi.add_apply, Finset.sum_insert hi]
  have hf_memLp : MemLp f (ENNReal.ofReal 2) μ := by
    dsimp [f]
    exact hsum_memLp s hind_memLp
  have hg_memLp : MemLp g (ENNReal.ofReal 2) μ := by
    change MemLp (U.indicator fun _ ↦ (1 : ℝ)) (ENNReal.ofReal 2) μ
    exact memLp_indicator_const (μ := μ) (ENNReal.ofReal 2) hUmeas
      (1 : ℝ) (Or.inr hUfin)
  have hf_nonneg : 0 ≤ f := by
    intro x
    exact Finset.sum_nonneg fun i hi ↦ ind_nonneg A i x
  have hg_nonneg : 0 ≤ g := by
    intro x
    by_cases hx : x ∈ U <;> simp [g, hx]
  have hprod : (fun x ↦ f x * g x) = f := by
    funext x
    by_cases hx : x ∈ U
    · simp [g, hx]
    · have hzero : f x = 0 := by
        dsimp [f]
        apply Finset.sum_eq_zero
        intro i hi
        have hxi : x ∉ A i := by
          intro hmem
          apply hx
          exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, hmem⟩⟩
        simp [ind, hxi]
      simp [g, hx, hzero]
  have hind_integrable (i : ι) (hi : i ∈ s) : Integrable (ind A i) μ := by
    change Integrable ((A i).indicator fun _ ↦ (1 : ℝ)) μ
    exact (integrableOn_const (hAfin i hi)).integrable_indicator (hA i hi)
  have hf_int : Integrable f μ := by
    dsimp [f]
    exact integrable_finsetSum s hind_integrable
  have hf_integral : ∫ x, f x ∂μ = ∑ i ∈ s, μ.real (A i) := by
    dsimp [f]
    rw [integral_finsetSum s]
    · apply Finset.sum_congr rfl
      intro i hi
      change ∫ x, (A i).indicator (fun _ ↦ (1 : ℝ)) x ∂μ = μ.real (A i)
      exact integral_indicator_one (hA i hi)
    · intro i hi
      exact hind_integrable i hi
  have hpair_integrable (i j : ι) (hi : i ∈ s) (hj : j ∈ s) :
      Integrable (fun x ↦ ind A i x * ind A j x) μ := by
    have hmeas : MeasurableSet (A i ∩ A j) := (hA i hi).inter (hA j hj)
    have hfin : μ (A i ∩ A j) ≠ ∞ := by
      exact ne_of_lt (lt_of_le_of_lt (measure_mono inter_subset_left) (lt_top_iff_ne_top.mpr (hAfin i hi)))
    have hiint : Integrable ((A i ∩ A j).indicator (fun _ ↦ (1 : ℝ))) μ :=
      (integrableOn_const hfin).integrable_indicator hmeas
    simpa only [ind_mul_ind A i j] using hiint
  have hf_sq_integral : ∫ x, f x ^ 2 ∂μ =
      ∑ i ∈ s, ∑ j ∈ s, μ.real (A i ∩ A j) := by
    calc
      ∫ x, f x ^ 2 ∂μ =
          ∫ x, ∑ i ∈ s, ∑ j ∈ s, ind A i x * ind A j x ∂μ := by
            apply integral_congr_ae
            filter_upwards [] with x
            dsimp [f]
            rw [pow_two, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
      _ = ∑ i ∈ s, ∫ x, ∑ j ∈ s, ind A i x * ind A j x ∂μ :=
        integral_finsetSum s fun i hi ↦
          integrable_finsetSum s fun j hj ↦ hpair_integrable i j hi hj
      _ = ∑ i ∈ s, ∑ j ∈ s, ∫ x, ind A i x * ind A j x ∂μ := by
        apply Finset.sum_congr rfl
        intro i hi
        exact integral_finsetSum s fun j hj ↦ hpair_integrable i j hi hj
      _ = ∑ i ∈ s, ∑ j ∈ s, μ.real (A i ∩ A j) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [show (fun x ↦ ind A i x * ind A j x) =
            (A i ∩ A j).indicator (fun _ ↦ (1 : ℝ)) by
              funext x; exact ind_mul_ind A i j x]
        exact integral_indicator_one ((hA i hi).inter (hA j hj))
  have hg_sq_integral : ∫ x, g x ^ 2 ∂μ = μ.real U := by
    calc
      ∫ x, g x ^ 2 ∂μ = ∫ x, g x ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        by_cases hx : x ∈ U <;> simp [g, hx]
      _ = μ.real U := by
        change ∫ x, U.indicator (fun _ ↦ (1 : ℝ)) x ∂μ = μ.real U
        exact integral_indicator_one hUmeas
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall hf_nonneg)
    (Filter.Eventually.of_forall hg_nonneg)
    hf_memLp hg_memLp
  rw [hprod, hf_integral] at hholder
  have hsqrt : (∑ i ∈ s, μ.real (A i)) ≤
      √(∑ i ∈ s, ∑ j ∈ s, μ.real (A i ∩ A j)) * √(μ.real U) := by
    have hholderNat : (∑ i ∈ s, μ.real (A i)) ≤
        (∫ a, f a ^ (2 : ℕ) ∂μ) ^ (1 / (2 : ℝ)) *
          (∫ a, g a ^ (2 : ℕ) ∂μ) ^ (1 / (2 : ℝ)) := by
      simpa only [Real.rpow_two] using hholder
    rw [hf_sq_integral, hg_sq_integral,
      ← Real.sqrt_eq_rpow (∑ i ∈ s, ∑ j ∈ s, μ.real (A i ∩ A j)),
      ← Real.sqrt_eq_rpow (μ.real U)] at hholderNat
    exact hholderNat
  have hleft_nonneg : 0 ≤ ∑ i ∈ s, μ.real (A i) := by positivity
  have hpair_nonneg : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, μ.real (A i ∩ A j) := by positivity
  have hU_nonneg : 0 ≤ μ.real U := by positivity
  have hsquared := (sq_le_sq₀ hleft_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr hsqrt
  rw [mul_pow, Real.sq_sqrt hpair_nonneg, Real.sq_sqrt hU_nonneg] at hsquared
  simpa [U, mul_comm] using hsquared

/-- Logarithmic divisor intervals can overlap only when their logarithmic
endpoints are within `log 2`. -/
theorem divisorLogInterval_inter_eq_empty_of_not_close {d e : ℕ}
    (hde : ¬ |Real.log (d : ℝ) - Real.log (e : ℝ)| ≤ Real.log 2) :
    divisorLogInterval d ∩ divisorLogInterval e = ∅ := by
  ext u
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hud
  rw [divisorLogInterval, Set.mem_Ico] at hud ⊢
  have hlt : Real.log 2 < |Real.log (d : ℝ) - Real.log (e : ℝ)| :=
    lt_of_not_ge hde
  rcases (lt_abs.mp hlt) with hleft | hright
  · intro hue
    linarith
  · intro hue
    linarith

/-- Every pairwise overlap has length at most `log 2`, and a non-close pair
has zero overlap. -/
theorem measureReal_inter_divisorLogInterval_le (d e : ℕ) :
    volume.real (divisorLogInterval d ∩ divisorLogInterval e) ≤
      if |Real.log (d : ℝ) - Real.log (e : ℝ)| ≤ Real.log 2
      then Real.log 2 else 0 := by
  classical
  by_cases hde : |Real.log (d : ℝ) - Real.log (e : ℝ)| ≤ Real.log 2
  · simp only [hde, if_true]
    calc
      volume.real (divisorLogInterval d ∩ divisorLogInterval e) ≤
          volume.real (divisorLogInterval d) := by
        exact measureReal_mono inter_subset_left
          (ne_of_lt (volume_divisorLogInterval d ▸ ENNReal.ofReal_lt_top))
      _ = Real.log 2 := by
        rw [Measure.real, volume_divisorLogInterval,
          ENNReal.toReal_ofReal (Real.log_nonneg one_le_two)]
  · simp only [hde, if_false]
    rw [divisorLogInterval_inter_eq_empty_of_not_close hde]
    exact le_of_eq measureReal_empty

/-- The sum of all pairwise overlap lengths is bounded by Ford's close-pair
count times the common interval length. -/
theorem sum_measureReal_inter_divisorLogInterval_le (a : ℕ) :
    (∑ d ∈ a.divisors, ∑ e ∈ a.divisors,
        volume.real (divisorLogInterval d ∩ divisorLogInterval e)) ≤
      (closePairCount a : ℝ) * Real.log 2 := by
  classical
  calc
    (∑ d ∈ a.divisors, ∑ e ∈ a.divisors,
        volume.real (divisorLogInterval d ∩ divisorLogInterval e)) ≤
        ∑ d ∈ a.divisors, ∑ e ∈ a.divisors,
          if |Real.log (d : ℝ) - Real.log (e : ℝ)| ≤ Real.log 2
          then Real.log 2 else 0 := by
      exact Finset.sum_le_sum fun d hd ↦ Finset.sum_le_sum fun e he ↦
        measureReal_inter_divisorLogInterval_le d e
    _ = (closePairCount a : ℝ) * Real.log 2 := by
      rw [← Finset.sum_product']
      simp only [closePairCount, closeDivisorPairs, Finset.card_filter]
      push_cast
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro de hde
      by_cases hclose : |Real.log (de.1 : ℝ) - Real.log (de.2 : ℝ)| ≤ Real.log 2 <;>
        simp [hclose]

/-- Ford's elementary divisor-cluster moment inequality. -/
theorem divisor_cluster_second_moment (a : ℕ) :
    ((a.divisors.card : ℝ) * Real.log 2) ^ 2 ≤
      clusterLength a * ((closePairCount a : ℝ) * Real.log 2) := by
  have hmoment := finite_union_second_moment
    (μ := volume) a.divisors divisorLogInterval
    (fun d hd ↦ measurableSet_divisorLogInterval d)
    (fun d hd ↦ ne_of_lt (volume_divisorLogInterval d ▸ ENNReal.ofReal_lt_top))
  have hleft : (∑ d ∈ a.divisors, volume.real (divisorLogInterval d)) =
      (a.divisors.card : ℝ) * Real.log 2 := by
    simp only [Measure.real, volume_divisorLogInterval,
      ENNReal.toReal_ofReal (Real.log_nonneg one_le_two), Finset.sum_const,
      nsmul_eq_mul]
  have hunion : volume.real (⋃ d ∈ a.divisors, divisorLogInterval d) =
      clusterLength a := rfl
  rw [hleft, hunion] at hmoment
  calc
    ((a.divisors.card : ℝ) * Real.log 2) ^ 2 ≤
        clusterLength a *
          (∑ d ∈ a.divisors, ∑ e ∈ a.divisors,
            volume.real (divisorLogInterval d ∩ divisorLogInterval e)) := hmoment
    _ ≤ clusterLength a * ((closePairCount a : ℝ) * Real.log 2) := by
      exact mul_le_mul_of_nonneg_left
        (sum_measureReal_inter_divisorLogInterval_le a) (clusterLength_nonneg a)

end Erdos446
