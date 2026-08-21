import ErdosProblems.Erdos239.External.Erdos67.LogBandCoverage
import ErdosProblems.Erdos239.External.Erdos67.LogFixedDepth

/-! # Uniform decay across finitely many logarithmic Weyl bands -/

open Filter

namespace Erdos67.LogBandDecay

noncomputable section

open Erdos1149
open Erdos67.LogWeylParameters

/-- The fixed coefficient of the robust real-start estimate at depth `r`. -/
def realStartBandConstant (r : ℕ) : ℝ :=
  AnalyticParameters.envelopeConstant 10
    ((2 : ℝ) ^ (depth r + 1) * terminalConstant r) (depth r)

/-- A single nonnegative function which majorizes the normalized saving in
the second-derivative band and in every fixed higher-derivative band up to
`R`. -/
def finiteBandDecay (R X : ℕ) : ℝ :=
  9 * (X : ℝ) ^ (-1 / 64 : ℝ) +
    ∑ r ∈ Finset.Icc 2 R,
      realStartBandConstant r * (X : ℝ) ^ (-savingExponent r)

theorem realStartBandConstant_nonneg (r : ℕ) :
    0 ≤ realStartBandConstant r := by
  unfold realStartBandConstant
  apply AnalyticParameters.envelopeConstant_nonneg
  · norm_num
  · unfold terminalConstant
    positivity

theorem finiteBandDecay_nonneg (R X : ℕ) : 0 ≤ finiteBandDecay R X := by
  unfold finiteBandDecay
  apply add_nonneg
  · exact mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg X) _)
  · apply Finset.sum_nonneg
    intro r hr
    exact mul_nonneg (realStartBandConstant_nonneg r)
      (Real.rpow_nonneg (Nat.cast_nonneg X) _)

private theorem tendsto_one_band (r : ℕ) :
    Tendsto
      (fun X : ℕ ↦ realStartBandConstant r *
        (X : ℝ) ^ (-savingExponent r)) atTop (nhds 0) := by
  have ht : Tendsto (fun x : ℝ ↦ x ^ (-savingExponent r)) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (savingExponent_pos r)
  have hcomp := ht.comp tendsto_natCast_atTop_atTop
  simpa using (hcomp.const_mul (realStartBandConstant r))

private theorem tendsto_band_sum (s : Finset ℕ) :
    Tendsto
      (fun X : ℕ ↦ ∑ r ∈ s,
        realStartBandConstant r * (X : ℝ) ^ (-savingExponent r))
      atTop (nhds 0) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert r s hrs ih =>
      simp only [Finset.sum_insert hrs]
      simpa using (tendsto_one_band r).add ih

theorem tendsto_finiteBandDecay (R : ℕ) :
    Tendsto (finiteBandDecay R) atTop (nhds 0) := by
  have hfirstR :
      Tendsto (fun x : ℝ ↦ x ^ (-(1 / 64 : ℝ))) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have hfirst := hfirstR.comp tendsto_natCast_atTop_atTop
  have hfirst' : Tendsto
      (fun X : ℕ ↦ 9 * (X : ℝ) ^ (-1 / 64 : ℝ)) atTop (nhds 0) := by
    convert hfirst.const_mul 9 using 1 <;> norm_num
  have hsum := tendsto_band_sum (Finset.Icc 2 R)
  change Tendsto (fun X : ℕ ↦
    9 * (X : ℝ) ^ (-1 / 64 : ℝ) +
      ∑ r ∈ Finset.Icc 2 R,
        realStartBandConstant r * (X : ℝ) ^ (-savingExponent r))
    atTop (nhds 0)
  simpa only [zero_add] using hfirst'.add hsum

/-- Uniform epsilon form of the finite-band decay. -/
theorem exists_finiteBandDecay_threshold (R : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀, finiteBandDecay R X ≤ η := by
  have hevent : ∀ᶠ X : ℕ in atTop, finiteBandDecay R X < η :=
    (tendsto_order.1 (tendsto_finiteBandDecay R)).2 _ hη
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 hevent
  exact ⟨X₀, fun X hX ↦ (hX₀ X hX).le⟩

end

end Erdos67.LogBandDecay
