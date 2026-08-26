import ErdosProblems.Erdos1038.RecoveryPositivePotentialLp
import ErdosProblems.Erdos1038.RecoveryDiagonal
import ErdosProblems.Erdos1038.ExteriorRoots

/-!
# Assembly of the positive-buffer recovery

This file fixes a canonical sequence of endpoint masses decreasing to the
zero-platform mass `A(q)`.  Once the two pointwise analytic facts from
Section 9 are supplied—null zero sets for every positive buffer and
convergence of their negative-set volumes—the already-verified empirical
and diagonal machinery produces one sequence of admissible polynomials.
-/

open scoped ENNReal
open Filter MeasureTheory Set Topology

namespace Erdos1038

noncomputable section

/-- Canonical endpoint masses decreasing to `A(q)` while staying strictly
inside the positive-platform interval. -/
def positiveBufferAlpha (q : ℝ) (n : ℕ) : ℝ :=
  A q + (s q - A q) / (n + 2)

theorem positiveBufferAlpha_nonneg
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) (n : ℕ) :
    0 ≤ positiveBufferAlpha q n := by
  have hqdom := q_mem_Ioo_of_pos_le_qSoft hq hqs.le
  have hA : 0 < A q := A_pos_of_mem_Ioo hqdom
  have hAs : A q < s q := A_lt_s_of_pos_lt_qSoft hq hqs
  unfold positiveBufferAlpha
  have hquot : 0 ≤ (s q - A q) / ((n : ℝ) + 2) := by
    exact div_nonneg (sub_nonneg.mpr hAs.le) (by positivity)
  linarith

theorem A_lt_positiveBufferAlpha
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) (n : ℕ) :
    A q < positiveBufferAlpha q n := by
  have hAs : A q < s q := A_lt_s_of_pos_lt_qSoft hq hqs
  unfold positiveBufferAlpha
  have hden : 0 < (n : ℝ) + 2 := by positivity
  have hquot : 0 < (s q - A q) / ((n : ℝ) + 2) :=
    div_pos (sub_pos.mpr hAs) hden
  linarith

theorem positiveBufferAlpha_le_s
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft) (n : ℕ) :
    positiveBufferAlpha q n ≤ s q := by
  have hAs : A q < s q := A_lt_s_of_pos_lt_qSoft hq hqs
  have hden : (1 : ℝ) ≤ (n : ℝ) + 2 := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hdiff : 0 ≤ s q - A q := (sub_pos.mpr hAs).le
  have hquot : (s q - A q) / ((n : ℝ) + 2) ≤ s q - A q := by
    exact div_le_self hdiff hden
  unfold positiveBufferAlpha
  linarith

theorem tendsto_positiveBufferAlpha
    {q : ℝ} : Tendsto (positiveBufferAlpha q) atTop (𝓝 (A q)) := by
  have htwo : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 2)) atTop (𝓝 0) := by
    have hshift :=
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
        (tendsto_add_atTop_nat 2)
    simpa [Function.comp_def, Nat.cast_add] using! hshift
  have hscaled : Tendsto
      (fun n : ℕ ↦ (s q - A q) * ((1 : ℝ) / (n + 2))) atTop (𝓝 0) := by
    simpa only [mul_zero] using! tendsto_const_nhds.mul htwo
  have hconst : Tendsto (fun _n : ℕ ↦ A q) atTop (𝓝 (A q)) :=
    tendsto_const_nhds
  have hadd := hconst.add hscaled
  have hfun : positiveBufferAlpha q =
      fun n : ℕ ↦ A q + (s q - A q) * ((n : ℝ) + 2)⁻¹ := by
    funext n
    simp only [positiveBufferAlpha, div_eq_mul_inv]
  rw [hfun]
  simpa only [one_div, add_zero] using! hadd

/-- Pointwise analytic certificate left by the positive-buffer construction
at a fixed one-cut parameter. -/
def PositiveBufferRecoveryAt (q : ℝ) : Prop :=
  (∀ n : ℕ, volume {x | x ∈ Icc (-2 : ℝ) 2 ∧
      positiveBufferPotential (s q) (positiveBufferAlpha q n) x = 0} = 0) ∧
    Tendsto
      (fun n ↦ volume {x | x ∈ Icc (-2 : ℝ) 2 ∧
        positiveBufferPotential (s q) (positiveBufferAlpha q n) x < 0})
      atTop (𝓝 (ENNReal.ofReal (Lambda q)))

/-- The positive-buffer pointwise certificate at `q` produces actual
admissible polynomials with sublevel volumes tending to `Lambda(q)`. -/
theorem exists_recoveryPolynomials_of_positiveBufferRecoveryAt
    {q : ℝ} (hq : 0 < q) (hqs : q < qSoft)
    (hcertificate : PositiveBufferRecoveryAt q) :
    ∃ f : ℕ → AdmissiblePolynomial,
      Tendsto (fun n ↦ sublevelVolume (f n).1) atTop
        (𝓝 (ENNReal.ofReal (Lambda q))) := by
  have hqdom := q_mem_Ioo_of_pos_le_qSoft hq hqs.le
  have hs := s_mem_Ioo_of_mem_Ioo hqdom
  exact exists_admissiblePolynomials_tendsto_of_positiveBuffers
    (fun _n ↦ s q) (positiveBufferAlpha q)
    (fun _n ↦ hs.1) (fun _n ↦ hs.2)
    (positiveBufferAlpha_nonneg hq hqs)
    (positiveBufferAlpha_le_s hq hqs)
    hcertificate.1 hcertificate.2

/-- Exact recovery leaf used by the final theorem. -/
def PositiveBufferRecoveryCertificate : Prop :=
  0 < qStar ∧ qStar < qSoft ∧ PositiveBufferRecoveryAt qStar

theorem mainTheorem_recovery_clause_of_positiveBufferRecoveryCertificate
    (hcertificate : PositiveBufferRecoveryCertificate) :
    ∃ f : ℕ → AdmissiblePolynomial,
      Tendsto (fun n ↦ sublevelVolume (f n).1) atTop
        (𝓝 (ENNReal.ofReal L)) := by
  obtain ⟨hq, hqs, hrecovery⟩ := hcertificate
  simpa only [L] using!
    exists_recoveryPolynomials_of_positiveBufferRecoveryAt hq hqs hrecovery

end

end Erdos1038
