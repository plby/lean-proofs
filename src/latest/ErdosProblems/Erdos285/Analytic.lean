/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Analytic infrastructure for Erdős Problem 285

This file records the elementary harmonic-interval estimate, algebraic facts
about the constant `e / (e - 1)`, and generic ratio/error-term conversions used
in the proof of the formal-conjectures statement.
-/

namespace Erdos285.Analytic

open Filter Finset Real
open scoped BigOperators Topology

noncomputable section

/-! ## The constant `e / (e - 1)` -/

/-- The density constant occurring in Erdős Problem 285. -/
def densityConstant : ℝ := Real.exp 1 / (Real.exp 1 - 1)

lemma one_lt_exp_one : (1 : ℝ) < Real.exp 1 :=
  Real.one_lt_exp_iff.mpr zero_lt_one

lemma exp_one_sub_one_pos : (0 : ℝ) < Real.exp 1 - 1 :=
  sub_pos.mpr one_lt_exp_one

lemma exp_one_sub_one_ne_zero : Real.exp 1 - 1 ≠ 0 :=
  ne_of_gt exp_one_sub_one_pos

lemma densityConstant_pos : 0 < densityConstant := by
  exact div_pos (Real.exp_pos 1) exp_one_sub_one_pos

lemma densityConstant_ne_zero : densityConstant ≠ 0 :=
  ne_of_gt densityConstant_pos

lemma densityConstant_eq_inv_one_sub_exp_neg :
    densityConstant = (1 - Real.exp (-1))⁻¹ := by
  have he : Real.exp (1 : ℝ) ≠ 0 := ne_of_gt (Real.exp_pos 1)
  rw [Real.exp_neg]
  simp only [densityConstant]
  field_simp

lemma densityConstant_mul_one_sub_exp_neg :
    densityConstant * (1 - Real.exp (-1)) = 1 := by
  rw [densityConstant_eq_inv_one_sub_exp_neg]
  exact inv_mul_cancel₀
    (sub_ne_zero.mpr (ne_of_gt (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr zero_lt_one))))

lemma densityConstant_inv : densityConstant⁻¹ = 1 - Real.exp (-1) := by
  rw [densityConstant_eq_inv_one_sub_exp_neg, inv_inv]

lemma one_sub_densityConstant_inv : 1 - densityConstant⁻¹ = Real.exp (-1) := by
  rw [densityConstant_inv]
  ring

lemma densityConstant_sub_one :
    densityConstant - 1 = 1 / (Real.exp 1 - 1) := by
  simp only [densityConstant]
  field_simp [exp_one_sub_one_ne_zero]
  ring_nf

/-! ## Terminal intervals of the harmonic series -/

/-- The reciprocal sum of the `m` consecutive positive integers beginning at `L`. -/
def terminalReciprocalSum (L m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range m, (1 : ℝ) / (L + i : ℕ)

/-- A single logarithmic increment is at most the corresponding reciprocal. -/
lemma log_succ_ratio_le_reciprocal {a : ℕ} (ha : 0 < a) :
    Real.log (((a + 1 : ℕ) : ℝ) / a) ≤ (1 : ℝ) / a := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hratio : (0 : ℝ) < (((a + 1 : ℕ) : ℝ) / a) := by positivity
  calc
    Real.log (((a + 1 : ℕ) : ℝ) / a)
        ≤ (((a + 1 : ℕ) : ℝ) / a) - 1 :=
      Real.log_le_sub_one_of_pos hratio
    _ = (1 : ℝ) / a := by
      field_simp
      norm_num [Nat.cast_add]

/-- The logarithmic increments over a consecutive interval telescope. -/
lemma sum_log_succ_ratio {L m : ℕ} (hL : 0 < L) :
    (∑ i ∈ Finset.range m,
        Real.log ((((L + i + 1 : ℕ) : ℝ) / (L + i : ℕ)))) =
      Real.log (L + m : ℕ) - Real.log L := by
  have hterm (i : ℕ) :
      Real.log ((((L + i + 1 : ℕ) : ℝ) / (L + i : ℕ))) =
        Real.log (L + i + 1 : ℕ) - Real.log (L + i : ℕ) := by
    rw [Real.log_div]
    · positivity
    · positivity
  rw [Finset.sum_congr rfl (fun i _ ↦ hterm i)]
  simpa [Nat.add_assoc] using
    (Finset.sum_range_sub (fun i : ℕ ↦ Real.log (L + i : ℕ)) m)

/-- A terminal harmonic interval dominates the logarithm of its endpoint ratio. -/
lemma log_div_le_terminalReciprocalSum {L m : ℕ} (hL : 0 < L) :
    Real.log (((L + m : ℕ) : ℝ) / L) ≤ terminalReciprocalSum L m := by
  rw [Real.log_div (by positivity) (by positivity), ← sum_log_succ_ratio hL]
  exact Finset.sum_le_sum fun i hi ↦ by
    simpa [terminalReciprocalSum] using
      log_succ_ratio_le_reciprocal (a := L + i) (Nat.add_pos_left hL i)

/-- Rearranging `log ((L+m)/L) ≤ 1` gives the sharp linear coefficient. -/
lemma densityConstant_mul_le_of_log_div_le_one {L m : ℕ} (hL : 0 < L)
    (hlog : Real.log (((L + m : ℕ) : ℝ) / L) ≤ 1) :
    densityConstant * (m : ℝ) ≤ (L + m : ℕ) := by
  have hratio_pos : (0 : ℝ) < (((L + m : ℕ) : ℝ) / L) := by positivity
  have hratio : (((L + m : ℕ) : ℝ) / L) ≤ Real.exp 1 := by
    have h := Real.exp_le_exp.mpr hlog
    rwa [Real.exp_log hratio_pos] at h
  have hlinear : ((L + m : ℕ) : ℝ) ≤ Real.exp 1 * L := by
    exact (div_le_iff₀ (by exact_mod_cast hL)).mp hratio
  rw [densityConstant, div_mul_eq_mul_div, div_le_iff₀ exp_one_sub_one_pos]
  push_cast at hlinear ⊢
  nlinarith

/-- If a terminal harmonic interval has reciprocal mass at most one, then its
endpoint is at least `e / (e - 1)` times its cardinality. -/
lemma densityConstant_mul_le_of_terminalReciprocalSum_le_one {L m : ℕ}
    (hL : 0 < L) (hsum : terminalReciprocalSum L m ≤ 1) :
    densityConstant * (m : ℝ) ≤ (L + m : ℕ) := by
  apply densityConstant_mul_le_of_log_div_le_one hL
  exact (log_div_le_terminalReciprocalSum hL).trans hsum

/-! ## Little-error and ratio packaging -/

lemma isLittleO_one_of_tendsto_zero {o : ℕ → ℝ}
    (ho : Tendsto o atTop (nhds 0)) :
    o =o[atTop] (1 : ℕ → ℝ) :=
  (Asymptotics.isLittleO_one_iff ℝ).2 ho

lemma tendsto_zero_of_isLittleO_one {o : ℕ → ℝ}
    (ho : o =o[atTop] (1 : ℕ → ℝ)) :
    Tendsto o atTop (nhds 0) :=
  (Asymptotics.isLittleO_one_iff ℝ).1 ho

/-- Subtracting one from a ratio tending to one produces a little error term. -/
lemma error_isLittleO_of_tendsto_one {u : ℕ → ℝ}
    (hu : Tendsto u atTop (nhds 1)) :
    (fun n ↦ u n - 1) =o[atTop] (1 : ℕ → ℝ) := by
  apply isLittleO_one_of_tendsto_zero
  simpa using hu.sub
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1))

/-- Package a ratio limit into an exact multiplicative error formula. -/
lemma exists_error_of_ratio_tendsto_one {a scale : ℕ → ℝ}
    (hscale : ∀ n, scale n ≠ 0)
    (hratio : Tendsto (fun n ↦ a n / scale n) atTop (nhds 1)) :
    ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ n, a n = (1 + o n) * scale n := by
  let o : ℕ → ℝ := fun n ↦ a n / scale n - 1
  refine ⟨o, ?_, ?_⟩
  · exact error_isLittleO_of_tendsto_one hratio
  · intro n
    dsimp [o]
    rw [show 1 + (a n / scale n - 1) = a n / scale n by ring,
      div_mul_cancel₀ _ (hscale n)]

/-- An exact multiplicative little-error formula implies the corresponding
ratio limit. -/
lemma ratio_tendsto_one_of_exists_error {a scale o : ℕ → ℝ}
    (hscale : ∀ n, scale n ≠ 0)
    (ho : o =o[atTop] (1 : ℕ → ℝ))
    (ha : ∀ n, a n = (1 + o n) * scale n) :
    Tendsto (fun n ↦ a n / scale n) atTop (nhds 1) := by
  have ho0 : Tendsto o atTop (nhds 0) := tendsto_zero_of_isLittleO_one ho
  have hone : Tendsto (fun n ↦ 1 + o n) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add ho0
  apply hone.congr'
  filter_upwards [] with n
  rw [ha n, mul_div_cancel_right₀ _ (hscale n)]

/-- Inversion preserves convergence to one. -/
lemma tendsto_inv_of_tendsto_one {u : ℕ → ℝ}
    (hu : Tendsto u atTop (nhds 1)) :
    Tendsto (fun n ↦ (u n)⁻¹) atTop (nhds 1) := by
  simpa using hu.inv₀ one_ne_zero

/-- Invert a ratio limit when both numerator and denominator are nonzero. -/
lemma tendsto_reverse_ratio_of_tendsto_ratio {a scale : ℕ → ℝ}
    (ha : ∀ n, a n ≠ 0) (hscale : ∀ n, scale n ≠ 0)
    (hratio : Tendsto (fun n ↦ a n / scale n) atTop (nhds 1)) :
    Tendsto (fun n ↦ scale n / a n) atTop (nhds 1) := by
  have hinv := tendsto_inv_of_tendsto_one hratio
  apply hinv.congr'
  filter_upwards [] with n
  field_simp [ha n, hscale n]

end

end Erdos285.Analytic
