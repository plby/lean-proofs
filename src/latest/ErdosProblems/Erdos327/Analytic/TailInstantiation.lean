import ErdosProblems.Erdos327.Analytic.CanonicalReduction
import ErdosProblems.Erdos327.Analytic.CenteredTailBounds
import ErdosProblems.Erdos327.Parameters

/-!
# Concrete centered-tail parameters

This file instantiates the two regularity tails used by the canonical
reduction.  The source budget is chosen before the roughness cutoff; the odd
host budget is chosen after the cutoff because its required error is measured
against the resulting rough density.
-/

namespace Erdos327.Analytic

open Real Filter

noncomputable section

def sourceAnatomySlope : ℝ := 1.000001
def sourceTailBase : ℝ := 1.000001
def oddAnatomySlope : ℝ := 1.16312
def oddTailBase : ℝ := 1.34305

theorem sourceAnatomySlope_nonneg :
    0 ≤ sourceAnatomySlope := by norm_num [sourceAnatomySlope]

theorem oddAnatomySlope_nonneg :
    0 ≤ oddAnatomySlope := by norm_num [oddAnatomySlope]

theorem sourceTailBase_gt_one :
    1 < sourceTailBase := by norm_num [sourceTailBase]

theorem sourceTailBase_le_five_halves :
    sourceTailBase ≤ 5 / 2 := by
  norm_num [sourceTailBase]

theorem oddTailBase_gt_one :
    1 < oddTailBase := by norm_num [oddTailBase]

theorem oddTailBase_le_five_halves :
    oddTailBase ≤ 5 / 2 := by
  norm_num [oddTailBase]

/-- The near-one source base gives geometric decay while retaining the
strict source exponent window. -/
theorem sourceTail_gap :
    sourceTailBase - 1 <
      sourceAnatomySlope * log sourceTailBase := by
  have hlog :=
    Real.lt_log_one_add_of_pos
      (x := (1 / 1000000 : ℝ)) (by norm_num)
  norm_num [sourceTailBase, sourceAnatomySlope] at hlog ⊢
  nlinarith

theorem oddTail_gap :
    oddTailBase - 1 <
      oddAnatomySlope * log oddTailBase := by
  simpa [oddTailBase, oddAnatomySlope] using
    Erdos327.odd_tail_exponent_positive

/-- A fixed base greater than one raised to a sufficiently negative real
exponent beats any prescribed positive tolerance. -/
theorem exists_mul_rpow_neg_le
    {z C ε : ℝ} (hz : 1 < z) (hε : 0 < ε) :
    ∃ K : ℝ, C * z ^ (-K) ≤ ε := by
  have hzinvPos : 0 < z⁻¹ := inv_pos.mpr (by linarith)
  have hzinvLower : -1 < z⁻¹ := by linarith
  have hzinvUpper : z⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ hz
  have ht :
      Tendsto (fun K : ℝ ↦ C * z⁻¹ ^ K) atTop (nhds 0) :=
    by
      simpa using
        ((tendsto_const_nhds :
            Tendsto (fun _ : ℝ ↦ C) atTop (nhds C)).mul
          (tendsto_rpow_atTop_of_base_lt_one
            z⁻¹ hzinvLower hzinvUpper))
  obtain ⟨K, hK⟩ :=
    ((tendsto_order.1 ht).2 ε hε).exists
  refine ⟨K, ?_⟩
  rw [Real.rpow_neg_eq_inv_rpow]
  exact hK.le

/-- The source regularity budget can be selected independently of `L`. -/
theorem exists_sourceTailBudget :
    ∃ Kb : ℝ,
      roughCenteredTailConstant sourceAnatomySlope sourceTailBase *
          sourceTailBase ^ (-Kb) ≤ 1 / 8 := by
  exact exists_mul_rpow_neg_le sourceTailBase_gt_one (by norm_num)

/-- Once `L` is fixed, choose the odd-host budget to make its unrestricted
tail smaller than one sixty-fourth of the rough density. -/
theorem exists_oddTailBudget (L : ℕ) (hL : 3 ≤ L) :
    ∃ Ko : ℝ,
      2 * unrestrictedCenteredTailConstant
          oddAnatomySlope oddTailBase *
          oddTailBase ^ (-Ko) ≤
        Erdos327.roughDensity L / 64 := by
  apply exists_mul_rpow_neg_le oddTailBase_gt_one
  positivity [Erdos327.roughDensity_pos hL]

/-- Concrete discharge of the canonical irregular-source estimate. -/
theorem irregularRoughSource_le_one_eighth
    {L N : ℕ} {Kb : ℝ}
    (hL : 3 ≤ L) (hLN : L ≤ N) (hN : 2 ≤ N)
    (hKb :
      roughCenteredTailConstant sourceAnatomySlope sourceTailBase *
          sourceTailBase ^ (-Kb) ≤ 1 / 8) :
    ((irregularRoughSource L sourceAnatomySlope Kb N).card : ℝ) ≤
      (N : ℝ) * Erdos327.roughDensity L / 8 := by
  have hraw :=
    card_irregularRoughSource_le_explicit
      (A := sourceAnatomySlope) (K := Kb) (z := sourceTailBase)
      hL hLN hN sourceAnatomySlope_nonneg
      sourceTailBase_gt_one sourceTailBase_le_five_halves sourceTail_gap
  have hρ : 0 ≤ Erdos327.roughDensity L :=
    (Erdos327.roughDensity_pos hL).le
  unfold Erdos327.roughDensity at hraw hρ ⊢
  calc
    ((irregularRoughSource L sourceAnatomySlope Kb N).card : ℝ)
        ≤ roughCenteredTailConstant sourceAnatomySlope sourceTailBase *
            N *
            (((roughPrimeModulus L).totient : ℝ) /
              roughPrimeModulus L) *
            sourceTailBase ^ (-Kb) :=
      hraw
    _ = ((N : ℝ) *
          (((roughPrimeModulus L).totient : ℝ) /
            roughPrimeModulus L)) *
        (roughCenteredTailConstant sourceAnatomySlope sourceTailBase *
          sourceTailBase ^ (-Kb)) := by ring
    _ ≤ ((N : ℝ) *
          (((roughPrimeModulus L).totient : ℝ) /
            roughPrimeModulus L)) * (1 / 8) := by
      gcongr
    _ = (N : ℝ) *
          (((roughPrimeModulus L).totient : ℝ) /
            roughPrimeModulus L) / 8 := by ring

/-- Concrete discharge of the canonical irregular odd-host estimate. -/
theorem irregularOddHost_le_one_sixty_fourth
    {L N : ℕ} {Ko : ℝ}
    (hL : 3 ≤ L) (hLN : L ≤ 2 * N) (hN : 1 ≤ N)
    (hKo :
      2 * unrestrictedCenteredTailConstant
          oddAnatomySlope oddTailBase *
          oddTailBase ^ (-Ko) ≤
        Erdos327.roughDensity L / 64) :
    ((irregularOddHost L oddAnatomySlope Ko N).card : ℝ) ≤
      (N : ℝ) * Erdos327.roughDensity L / 64 := by
  have hraw :=
    card_irregularOddHost_le_explicit
      (A := oddAnatomySlope) (K := Ko) (z := oddTailBase)
      hL hLN hN oddAnatomySlope_nonneg
      oddTailBase_gt_one oddTailBase_le_five_halves oddTail_gap
  calc
    ((irregularOddHost L oddAnatomySlope Ko N).card : ℝ)
        ≤ unrestrictedCenteredTailConstant oddAnatomySlope oddTailBase *
            (2 * N) * oddTailBase ^ (-Ko) :=
      hraw
    _ = (N : ℝ) *
        (2 * unrestrictedCenteredTailConstant
          oddAnatomySlope oddTailBase *
          oddTailBase ^ (-Ko)) := by
      ring
    _ ≤ (N : ℝ) * (Erdos327.roughDensity L / 64) := by
      gcongr
    _ = (N : ℝ) * Erdos327.roughDensity L / 64 := by ring

end

end Erdos327.Analytic
