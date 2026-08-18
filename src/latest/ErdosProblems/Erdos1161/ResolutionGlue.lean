/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1161.LocalError
import ErdosProblems.Erdos1161.Structural

/-!
# Final logical and asymptotic glue for Erdős Problem 1161

This file contains no analytic input.  Its hypotheses isolate the two deep
outputs of the preceding development: the eventual structural theorem and
the uniform local expansion.  The results below turn those outputs into the
unique-mode statement, the two asymptotic formulations, and the integer
threshold formulation used in the final theorem.
-/

open scoped Topology
open Filter Asymptotics

namespace Erdos1161

/-- The unconditional local input, under the stable name used by the public
resolution theorem. -/
theorem uniform_local_expansion :
    HasUniformLocalExpansion orderProbability :=
  orderProbability_hasUniformLocalExpansion

/-- The exact interface required from the global structural argument. -/
def HasEventualThresholdStructure : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
    (1 : ℝ) / n ≤ orderProbability n m →
      m ≤ n ∧ BekerCandidate n m

/-- The unconditional global input, under the stable name used by the public
resolution theorem. -/
theorem eventual_threshold_structure : HasEventualThresholdStructure :=
  eventually_orderProbability_ge_one_div_imp_bekerCandidate

/-- The global threshold theorem and the local expansion force the unique
mode to be the complement of the greatest admissible remainder. -/
theorem eventually_isMode_iff_eq_sub_largest_of_inputs
    (hstruct : HasEventualThresholdStructure)
    (hlocal : HasUniformLocalExpansion orderProbability) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
      IsMode n m ↔ m = n - largestAdmissibleRemainder n := by
  have hstrict :=
    eventually_strictOn_admissible_of_hasUniformLocalExpansion hlocal
  filter_upwards [hstruct, hstrict, eventually_gt_atTop 0] with n hnstruct hnstrict hn
  let R := largestAdmissibleRemainder n
  let target := n - R
  have hRmem : R ∈ admissibleRemainders n := by
    simpa [R] using largestAdmissibleRemainder_mem hn
  have hRlt : R < n := (mem_admissibleRemainders_iff.mp hRmem).1
  have hRdvd : Nat.lcmUpto R ∣ n - R :=
    (mem_admissibleRemainders_iff.mp hRmem).2
  have mode_eq_target : ∀ q : ℕ, IsMode n q → q = target := by
    intro q hq
    have hthreshold : (1 : ℝ) / n ≤ orderProbability n q :=
      (one_div_le_orderProbability_iff hn).2 <|
        (pred_factorial_le_orderCount_self hn).trans (hq n)
    obtain ⟨hqn, hqcand⟩ := hnstruct q hthreshold
    let r := n - q
    have hrmem : r ∈ admissibleRemainders n := by
      simpa [r] using
        (bekerCandidate_iff_sub_mem_admissibleRemainders hqn).mp hqcand
    have hrlt : r < n := (mem_admissibleRemainders_iff.mp hrmem).1
    have hrdvd : Nat.lcmUpto r ∣ n - r :=
      (mem_admissibleRemainders_iff.mp hrmem).2
    have hrle : r ≤ R := by
      simpa [R] using admissibleRemainder_le_largest hrmem
    have hre : r = R := by
      apply le_antisymm hrle
      by_contra hnot
      have hrR : r < R := by omega
      have hprob_lt : orderProbability n q < orderProbability n target := by
        have h := hnstrict r R hrR hRlt hrdvd hRdvd
        simpa [r, R, target, Nat.sub_sub_self hqn] using h
      have hprob_ge : orderProbability n target ≤ orderProbability n q := by
        unfold orderProbability
        exact div_le_div_of_nonneg_right
          (by exact_mod_cast hq target) (Nat.cast_nonneg _)
      exact (not_lt_of_ge hprob_ge) hprob_lt
    calc
      q = n - r := (Nat.sub_sub_self hqn).symm
      _ = target := by simp [hre, target, R]
  have htarget : IsMode n target := by
    obtain ⟨q, hq⟩ := exists_isMode n
    simpa [mode_eq_target q hq] using hq
  intro m
  constructor
  · intro hm
    simpa [target] using mode_eq_target m hm
  · intro hm
    simpa [target, hm] using htarget

/-- Equivalent formulation of the unique mode as the least positive integer
satisfying Beker's least-common-multiple condition. -/
theorem eventually_isMode_iff_isLeast_bekerCandidate_of_inputs
    (hstruct : HasEventualThresholdStructure)
    (hlocal : HasUniformLocalExpansion orderProbability) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
      IsMode n m ↔ IsLeast {k : ℕ | BekerCandidate n k} m := by
  filter_upwards [eventually_isMode_iff_eq_sub_largest_of_inputs hstruct hlocal,
    eventually_gt_atTop 0] with n hnmode hn m
  rw [hnmode m,
    isLeast_bekerCandidate_iff_eq_sub_largestAdmissibleRemainder hn]

/-- The real threshold theorem implies the exact factorial-count version. -/
theorem eventually_orderCount_ge_pred_factorial_imp_bekerCandidate_of_structure
    (hstruct : HasEventualThresholdStructure) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
      (n - 1).factorial ≤ orderCount n m →
        m ≤ n ∧ BekerCandidate n m := by
  filter_upwards [hstruct, eventually_gt_atTop 0] with n hnstruct hn m hm
  exact hnstruct m ((one_div_le_orderProbability_iff hn).2 hm)

/-- The local expansion at the greatest admissible remainder has main term
`1 / (n - max K_n)`, and its error is little-o of that main term.  Together
with `n - max K_n ~ n`, this gives the probability asymptotic. -/
theorem selectedOrderProbability_isEquivalent_one_div
    (hlocal : HasUniformLocalExpansion orderProbability) :
    (fun n : ℕ ↦
      orderProbability n (n - largestAdmissibleRemainder n)) ~[atTop]
      (fun n : ℕ ↦ (1 : ℝ) / n) := by
  rcases hlocal with ⟨e, he_nonneg, he_scaled, he_bound⟩
  let m : ℕ → ℕ := fun n ↦ n - largestAdmissibleRemainder n
  let main : ℕ → ℝ := fun n ↦ (1 : ℝ) / (m n : ℝ)
  let err : ℕ → ℝ := fun n ↦
    orderProbability n (m n) - main n
  have hm_equiv : (fun n : ℕ ↦ (m n : ℝ)) ~[atTop]
      (fun n : ℕ ↦ (n : ℝ)) := by
    simpa [m] using sub_largestAdmissibleRemainder_isEquivalent
  have hmain_equiv : main ~[atTop] (fun n : ℕ ↦ (1 : ℝ) / n) := by
    have hinv := hm_equiv.inv
    change (fun n : ℕ ↦ ((m n : ℝ))⁻¹) ~[atTop]
      (fun n : ℕ ↦ ((n : ℝ))⁻¹) at hinv
    simpa only [main, one_div] using hinv
  have hmain_zero : Tendsto main atTop (nhds 0) :=
    hmain_equiv.tendsto_nhds_iff.mpr
      tendsto_one_div_atTop_nhds_zero_nat
  have hm_pos : ∀ᶠ n : ℕ in atTop, 0 < m n := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    simpa [m] using Nat.sub_pos_of_lt
      (largestAdmissibleRemainder_lt hn)
  have hRbound : ∀ᶠ n : ℕ in atTop,
      |orderProbability n (m n) -
        localMainTerm n (largestAdmissibleRemainder n)| ≤ e n := by
    filter_upwards [he_bound, eventually_gt_atTop 0] with n hnexp hn
    have hRmem := largestAdmissibleRemainder_mem hn
    have hRdata := mem_admissibleRemainders_iff.mp hRmem
    simpa [m] using hnexp (largestAdmissibleRemainder n)
      hRdata.1 hRdata.2
  have herr_norm_bound : ∀ᶠ n : ℕ in atTop,
      |err n * (m n : ℝ)| ≤
        (n : ℝ) ^ 2 * e n + main n := by
    filter_upwards [hRbound, hm_pos, eventually_gt_atTop 0] with n hnerr hmpos hn
    have hRlt := largestAdmissibleRemainder_lt hn
    have hmleNat : m n ≤ n := by simp [m]
    have hmle : (m n : ℝ) ≤ n := by exact_mod_cast hmleNat
    have hnleSq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    have heta_nonneg :
        0 ≤ halfCycleCorrection n (largestAdmissibleRemainder n) :=
      halfCycleCorrection_nonneg _ _
    have heta_le :
        halfCycleCorrection n (largestAdmissibleRemainder n) ≤
          1 / (m n : ℝ) ^ 2 := by
      by_cases hsmall : largestAdmissibleRemainder n ≤ 1
      · rw [halfCycleCorrection_of_le_one hsmall]
        positivity
      · have htwo : 2 ≤ largestAdmissibleRemainder n := by omega
        simpa [m] using
          (halfCycleCorrection_le_inv_sq (n := n) htwo)
    have habs_err :
        |err n| ≤ e n +
          halfCycleCorrection n (largestAdmissibleRemainder n) := by
      have htriangle := abs_add_le
        (orderProbability n (m n) -
          localMainTerm n (largestAdmissibleRemainder n))
        (halfCycleCorrection n (largestAdmissibleRemainder n))
      have hid : err n =
          (orderProbability n (m n) -
            localMainTerm n (largestAdmissibleRemainder n)) +
          halfCycleCorrection n (largestAdmissibleRemainder n) := by
        simp only [err, main, localMainTerm, m]
        ring
      rw [hid]
      calc
        |(orderProbability n (m n) -
              localMainTerm n (largestAdmissibleRemainder n)) +
            halfCycleCorrection n (largestAdmissibleRemainder n)|
            ≤ |orderProbability n (m n) -
                localMainTerm n (largestAdmissibleRemainder n)| +
              |halfCycleCorrection n (largestAdmissibleRemainder n)| :=
              htriangle
        _ = |orderProbability n (m n) -
                localMainTerm n (largestAdmissibleRemainder n)| +
              halfCycleCorrection n (largestAdmissibleRemainder n) := by
              rw [abs_of_nonneg heta_nonneg]
        _ ≤ e n + halfCycleCorrection n
              (largestAdmissibleRemainder n) := add_le_add hnerr le_rfl
    have he_mul : e n * (m n : ℝ) ≤ (n : ℝ) ^ 2 * e n := by
      have hem : e n * (m n : ℝ) ≤ e n * n :=
        mul_le_mul_of_nonneg_left hmle (he_nonneg n)
      calc
        e n * (m n : ℝ) ≤ e n * n := hem
        _ ≤ e n * (n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hnleSq (he_nonneg n)
        _ = (n : ℝ) ^ 2 * e n := by ring
    have heta_mul :
        halfCycleCorrection n (largestAdmissibleRemainder n) * (m n : ℝ) ≤
          main n := by
      calc
        halfCycleCorrection n (largestAdmissibleRemainder n) * (m n : ℝ)
            ≤ (1 / (m n : ℝ) ^ 2) * (m n : ℝ) :=
              mul_le_mul_of_nonneg_right heta_le (by positivity)
        _ = main n := by
          simp only [main]
          field_simp
    rw [abs_mul,
      abs_of_pos (show (0 : ℝ) < (m n : ℝ) by exact_mod_cast hmpos)]
    calc
      |err n| * (m n : ℝ) ≤
          (e n + halfCycleCorrection n
            (largestAdmissibleRemainder n)) * (m n : ℝ) :=
        mul_le_mul_of_nonneg_right habs_err (by positivity)
      _ = e n * (m n : ℝ) +
          halfCycleCorrection n (largestAdmissibleRemainder n) * (m n : ℝ) :=
        by ring
      _ ≤ (n : ℝ) ^ 2 * e n + main n := add_le_add he_mul heta_mul
  have hupper_zero : Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 2 * e n + main n) atTop (nhds 0) := by
    simpa using he_scaled.add hmain_zero
  have herr_mul_zero : Tendsto (fun n : ℕ ↦ err n * (m n : ℝ))
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    exact squeeze_zero'
      (Filter.Eventually.of_forall fun n ↦ abs_nonneg _)
      herr_norm_bound hupper_zero
  have herr_littleO : err =o[atTop] main := by
    have hmain_zero_imp : ∀ᶠ n : ℕ in atTop,
        main n = 0 → err n = 0 := by
      filter_upwards [hm_pos] with n hn hzero
      simp [main, hn.ne'] at hzero
    rw [isLittleO_iff_tendsto' hmain_zero_imp]
    apply herr_mul_zero.congr'
    filter_upwards [hm_pos] with n hn
    simp [main, div_eq_mul_inv]
  have hp_main : (fun n : ℕ ↦ orderProbability n (m n)) ~[atTop] main := by
    apply (IsEquivalent.refl : main ~[atTop] main).add_isLittleO herr_littleO
      |>.congr_left
    filter_upwards [] with n
    simp [err]
  simpa [m] using hp_main.trans hmain_equiv

/-- Once the structural theorem identifies the mode, the selected-order
asymptotic is exactly the asymptotic of the maximum probability. -/
theorem maxOrderProbability_isEquivalent_of_inputs
    (hstruct : HasEventualThresholdStructure)
    (hlocal : HasUniformLocalExpansion orderProbability) :
    (fun n : ℕ ↦ maxOrderProbability n) ~[atTop]
      (fun n : ℕ ↦ (1 : ℝ) / n) := by
  have hselected := selectedOrderProbability_isEquivalent_one_div hlocal
  apply hselected.congr_left
  filter_upwards [eventually_isMode_iff_eq_sub_largest_of_inputs hstruct hlocal]
    with n hnmode
  exact (maxOrderProbability_eq_orderProbability_of_isMode
    ((hnmode (n - largestAdmissibleRemainder n)).2 rfl)).symm

/-- Count form of the maximum asymptotic. -/
theorem maxOrderCount_isEquivalent_pred_factorial_of_inputs
    (hstruct : HasEventualThresholdStructure)
    (hlocal : HasUniformLocalExpansion orderProbability) :
    (fun n : ℕ ↦ (maxOrderCount n : ℝ)) ~[atTop]
      (fun n : ℕ ↦ ((n - 1).factorial : ℝ)) :=
  maxOrderCount_isEquivalent_pred_factorial_of_probability
    (maxOrderProbability_isEquivalent_of_inputs hstruct hlocal)

/-- The three components consumed verbatim by the public resolution theorem.
Keeping this theorem parametrized makes the logical assembly independently
checkable while the two analytic inputs are proved in their dedicated files. -/
theorem resolution_components_of_inputs
    (hstruct : HasEventualThresholdStructure)
    (hlocal : HasUniformLocalExpansion orderProbability) :
    ((fun n : ℕ ↦ (maxOrderCount n : ℝ)) ~[atTop]
      (fun n : ℕ ↦ ((n - 1).factorial : ℝ))) ∧
    (∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
      (n - 1).factorial ≤ orderCount n m →
        m ≤ n ∧ BekerCandidate n m) ∧
    (∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
      IsMode n m ↔ IsLeast {k : ℕ | BekerCandidate n k} m) := by
  exact ⟨maxOrderCount_isEquivalent_pred_factorial_of_inputs hstruct hlocal,
    eventually_orderCount_ge_pred_factorial_imp_bekerCandidate_of_structure
      hstruct,
    eventually_isMode_iff_isLeast_bekerCandidate_of_inputs hstruct hlocal⟩

end Erdos1161
