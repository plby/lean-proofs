/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTAbsorptionBounds

/-! # The source covering scale controls every scalar loss -/

namespace Erdos4b.FGKMT

noncomputable section

def coveringScale (A : ℕ) (D κ : ℝ) : ℝ :=
  256 * Real.exp ((A : ℝ) * D) * (1 / κ ^ A)

theorem coveringScale_bounds (A : ℕ) {D κ : ℝ} (hD : 0 ≤ D)
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) :
    256 ≤ coveringScale A D κ ∧ Real.exp ((A : ℝ) * D) ≤ coveringScale A D κ ∧
      1 / κ ^ A ≤ coveringScale A D κ := by
  let E := Real.exp ((A : ℝ) * D)
  let K := 1 / κ ^ A
  have hE : 1 ≤ E := Real.one_le_exp_iff.mpr (by positivity)
  have hK : 1 ≤ K := (le_div_iff₀ (pow_pos hκ0 A)).mpr
    (by simpa only [one_mul] using pow_le_one₀ hκ0.le hκ1 (n := A))
  have hE0 : 0 ≤ E := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hEK : 1 ≤ E * K := (by norm_num : (1 : ℝ) = 1 * 1).trans_le
    (mul_le_mul hE hK (by norm_num) hE0)
  have hscale : E * K ≤ coveringScale A D κ := by
    change E * K ≤ 256 * E * K
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · change 256 ≤ 256 * E * K
    nlinarith
  · have hle : E ≤ E * K := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hK hE0
    exact hle.trans hscale
  · have hle : K ≤ E * K := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hE hK0
    exact hle.trans hscale

namespace FiniteEdgeFamily

variable {I Ω α : Type*} [Fintype I] [Fintype Ω] [DecidableEq α]

theorem stageAbsorptionBounds_coveringScale (F : FiniteEdgeFamily I Ω α)
    (e : Finset α) {A : ℕ} {D κ : ℝ} (hA : 1 ≤ A) (hD : 1 ≤ D)
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hsize : e.card + 2 * F.rank ≤ A) :
    F.StageAbsorptionBounds e κ D (coveringScale A D κ) := by
  have hD0 : 0 ≤ D := by linarith
  have hAr : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hb := coveringScale_bounds A hD0 hκ0 hκ1
  have hAexp : (A : ℝ) ≤ Real.exp ((A : ℝ) * D) := by
    have hmul : (A : ℝ) ≤ (A : ℝ) * D := by nlinarith
    linarith [Real.add_one_le_exp ((A : ℝ) * D)]
  have hDexp : D ≤ Real.exp ((A : ℝ) * D) := by
    have hmul : D ≤ (A : ℝ) * D := by nlinarith
    linarith [Real.add_one_le_exp ((A : ℝ) * D)]
  have hnat (j : ℕ) (hj : j ≤ A) : (j : ℝ) ≤ coveringScale A D κ :=
    (by exact_mod_cast hj : (j : ℝ) ≤ A).trans (hAexp.trans hb.2.1)
  have hinv (j : ℕ) (hj : j ≤ A) : 1 / κ ^ j ≤ coveringScale A D κ :=
    (one_div_le_one_div_of_le (pow_pos hκ0 A)
      (absorption_power_antitone hκ0.le hκ1 hj)).trans hb.2.2
  refine ⟨hb.1, hκ0, hD0, hnat e.card (by omega), hnat F.rank (by omega),
    hDexp.trans hb.2.1, ?_, hinv F.rank (by omega), hinv e.card (by omega), ?_⟩
  · simpa only [pow_one] using hinv 1 hA
  · refine (Real.exp_le_exp.mpr ?_).trans hb.2.1
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show e.card ≤ A by omega)) hD0

end FiniteEdgeFamily

end

end Erdos4b.FGKMT
