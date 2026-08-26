import ErdosProblems.Erdos520.HarperFiniteSlicing
import ErdosProblems.Erdos520.HarperScheduledGaussianBarrier

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos.Problem520

theorem harperCumulativeScheduledRelativeCellWidth_le_two
    (start n : ℕ) (k : Fin n) :
    harperCumulativeCellWidth (harperScheduledRelativeCellWidth start n) k ≤ 2 := by
  let e : Fin n ↪ ℕ :=
    ⟨fun i ↦ start + i.val + 1, by
      intro i j hij
      change start + i.val + 1 = start + j.val + 1 at hij
      apply Fin.ext
      change i.val = j.val
      omega⟩
  have hsum : harperCumulativeCellWidth
      (harperScheduledRelativeCellWidth start n) k =
        ∑ m ∈ (Finset.Iic k).map e, (((m : ℕ) : ℝ) ^ 2)⁻¹ := by
    unfold harperCumulativeCellWidth harperScheduledRelativeCellWidth
    rw [Finset.sum_map]
    rfl
  have hsubset : (Finset.Iic k).map e ⊆
      Finset.Ioo 0 (start + k.val + 2) := by
    intro m hm
    rw [Finset.mem_map] at hm
    obtain ⟨i, hi, rfl⟩ := hm
    rw [Finset.mem_Ioo]
    dsimp only [e]
    have hikFin : i ≤ k := by
      simpa only [Finset.mem_Iic] using! hi
    have hik : i.val ≤ k.val := hikFin
    change 0 < start + i.val + 1 ∧
      start + i.val + 1 < start + k.val + 2
    constructor <;> omega
  rw [hsum]
  calc
    (∑ m ∈ (Finset.Iic k).map e, (((m : ℕ) : ℝ) ^ 2)⁻¹) ≤
        ∑ m ∈ Finset.Ioo 0 (start + k.val + 2),
          (((m : ℕ) : ℝ) ^ 2)⁻¹ := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun m _hm _hnot ↦ by positivity)
    _ ≤ 2 := by
      have h := sum_Ioo_inv_sq_le (α := ℝ) 0 (start + k.val + 2)
      norm_num at h
      exact h

theorem harperExpandedPartialSumBarrierSet_subset_gaussianWalkTimeBarrierSet
    {n : ℕ} (lower upper delta : Fin n → ℝ) :
    harperExpandedPartialSumBarrierSet lower upper delta ⊆
      gaussianWalkTimeBarrierSet n 0
        (fun k ↦ upper k + harperCumulativeCellWidth delta k) := by
  exact harperPartialSumBarrierSet_subset_gaussianWalkTimeBarrierSet
    (fun k ↦ lower k - harperCumulativeCellWidth delta k)
    (fun k ↦ upper k + harperCumulativeCellWidth delta k)

theorem harperExpandedLogBarrierSet_subset_gaussianWalkTimeBarrierSet
    {n : ℕ} (lower delta : Fin n → ℝ) (x c A : ℝ)
    (hwidth : ∀ k, harperCumulativeCellWidth delta k ≤ A) :
    harperExpandedPartialSumBarrierSet lower
        (fun k ↦ x + c * Real.log ((k.val + 2 : ℕ) : ℝ)) delta ⊆
      gaussianWalkTimeBarrierSet n 0
        (fun k ↦ x + A + c * Real.log ((k.val + 2 : ℕ) : ℝ)) := by
  refine (harperExpandedPartialSumBarrierSet_subset_gaussianWalkTimeBarrierSet lower
    (fun k ↦ x + c * Real.log ((k.val + 2 : ℕ) : ℝ)) delta).trans ?_
  intro omega homega
  exact gaussianWalkTimeBarrierSurvives_mono n 0
    (fun k ↦ by
      have := hwidth k
      linarith)
    homega

theorem exists_eventually_harperScheduledGaussianWalk_expandedLogBarrier_probability_le
    (M : ℕ) :
    ∃ J : ℕ, ∀ start : ℕ, J ≤ start →
      ∀ n : ℕ, 0 < n → ∀ y : ℕ,
        harperBlockEndpoint (start + n) ≤ y →
          ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
            ∀ x : ℝ, 0 ≤ x → ∀ lower : Fin n → ℝ,
              (harperScheduledGaussianProductMeasure y start n t).real
                  (harperExpandedPartialSumBarrierSet lower
                    (fun k ↦ x + 8 * Real.log ((k.val + 2 : ℕ) : ℝ))
                    (harperScheduledRelativeCellWidth start n)) ≤
                64 * (x + 2 + 8 * Real.log ((n + 1 : ℕ) : ℝ) + 2) /
                  Real.sqrt (n : ℝ) := by
  obtain ⟨J, hJ⟩ :=
    exists_eventually_harperScheduledGaussianWalk_logBarrier_probability_le M
  refine ⟨J, ?_⟩
  intro start hstart n hn y hy t htLower htUpper x hx lower
  have hsubset := harperExpandedLogBarrierSet_subset_gaussianWalkTimeBarrierSet
    lower (harperScheduledRelativeCellWidth start n) x 8 2
    (harperCumulativeScheduledRelativeCellWidth_le_two start n)
  refine (measureReal_mono hsubset).trans ?_
  have h := hJ start hstart n hn y hy t htLower htUpper (x + 2) 8
    (by positivity) (by norm_num)
  simpa only [add_assoc] using! h

noncomputable def harperNormalizedReverseLogBarrier
    (n : ℕ) (x c : ℝ) (i : Fin n) : ℝ :=
  x + c * Real.log
    (((n + 1 - i.val : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))

theorem harperNormalizedReverseLogBarrier_le
    (n : ℕ) (x : ℝ) {c : ℝ} (hc : 0 ≤ c) (i : Fin n) :
    harperNormalizedReverseLogBarrier n x c i ≤ x := by
  have hden : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hnum : (0 : ℝ) ≤ ((n + 1 - i.val : ℕ) : ℝ) := by positivity
  have hnumle : ((n + 1 - i.val : ℕ) : ℝ) ≤
      ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_le (n + 1) i.val
  have hratio0 : 0 ≤
      ((n + 1 - i.val : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) :=
    div_nonneg hnum hden.le
  have hratio1 :
      ((n + 1 - i.val : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ 1 :=
    (div_le_one hden).2 hnumle
  have hlog := Real.log_nonpos hratio0 hratio1
  unfold harperNormalizedReverseLogBarrier
  nlinarith

theorem exists_eventually_harperScheduledGaussianWalk_expandedUpperBarrier_probability_le
    (M : ℕ) :
    ∃ J : ℕ, ∀ start : ℕ, J ≤ start →
      ∀ n : ℕ, 0 < n → ∀ y : ℕ,
        harperBlockEndpoint (start + n) ≤ y →
          ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
            ∀ (x A : ℝ), 0 ≤ x → 0 ≤ A →
              ∀ (lower upper delta : Fin n → ℝ),
                (∀ k, upper k ≤ x) →
                (∀ k, harperCumulativeCellWidth delta k ≤ A) →
                (harperScheduledGaussianProductMeasure y start n t).real
                    (harperExpandedPartialSumBarrierSet lower upper delta) ≤
                  64 * (x + 2 + A) / Real.sqrt (n : ℝ) := by
  obtain ⟨J, hJ⟩ :=
    exists_eventually_harperScheduledGaussianWalk_timeBarrier_probability_le M
  refine ⟨J, ?_⟩
  intro start hstart n hn y hy t htLower htUpper x A hx hA
    lower upper delta hupper hwidth
  have hsubset :=
    harperExpandedPartialSumBarrierSet_subset_gaussianWalkTimeBarrierSet
      lower upper delta
  refine (measureReal_mono hsubset).trans ?_
  have h := hJ start hstart n hn y hy t htLower htUpper 0 (x + A)
    (fun k ↦ upper k + harperCumulativeCellWidth delta k)
    (by linarith) (fun k ↦ by
      have hu := hupper k
      have hw := hwidth k
      linarith)
  simpa only [sub_zero, add_assoc, add_comm, add_left_comm] using! h

theorem exists_eventually_harperScheduledGaussianWalk_expandedReverseLogBarrier_probability_le
    (M : ℕ) :
    ∃ J : ℕ, ∀ start : ℕ, J ≤ start →
      ∀ n : ℕ, 0 < n → ∀ y : ℕ,
        harperBlockEndpoint (start + n) ≤ y →
          ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
            ∀ (x c : ℝ), 0 ≤ x → 0 ≤ c →
              ∀ lower : Fin n → ℝ,
                (harperScheduledGaussianProductMeasure y start n t).real
                    (harperExpandedPartialSumBarrierSet lower
                      (harperNormalizedReverseLogBarrier n x c)
                      (harperScheduledRelativeCellWidth start n)) ≤
                  64 * (x + 4) / Real.sqrt (n : ℝ) := by
  obtain ⟨J, hJ⟩ :=
    exists_eventually_harperScheduledGaussianWalk_expandedUpperBarrier_probability_le M
  refine ⟨J, ?_⟩
  intro start hstart n hn y hy t htLower htUpper x c hx hc lower
  have h := hJ start hstart n hn y hy t htLower htUpper x 2 hx
    (by norm_num) lower (harperNormalizedReverseLogBarrier n x c)
    (harperScheduledRelativeCellWidth start n)
    (harperNormalizedReverseLogBarrier_le n x hc)
    (harperCumulativeScheduledRelativeCellWidth_le_two start n)
  calc
    _ ≤ 64 * (x + 2 + 2) / Real.sqrt (n : ℝ) := h
    _ = 64 * (x + 4) / Real.sqrt (n : ℝ) := by ring

end Erdos.Problem520
