import ErdosProblems.Erdos67b.MRInitialEnergyBudget
import ErdosProblems.Erdos67b.MRLastBlockRemainder

/-! # An index-free energy budget at any fixed relative cutoff -/

open Filter

namespace Erdos67b

noncomputable section

def mrFirstSmallRelativeBudget (eta p q c : ℝ) : ℝ :=
  2048 * Real.exp 1 * (1 + Real.pi) * (c * Real.exp q + 1) *
      Real.exp (Real.log q / 3 - (1 / 6 - eta) * p) +
    8192 * Real.exp 13 * (1 + Real.pi) * (c + 1) * Real.exp (-p) +
    128 * (1 + Real.pi) * (c + 1) *
      (12 / mrLogBlockResolution eta p q 1 + 2 * Real.exp (-p))

theorem mrFirstSmallRelativeBudget_nonneg (eta p q : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ mrFirstSmallRelativeBudget eta p q c := by
  unfold mrFirstSmallRelativeBudget mrLogBlockResolution
  positivity

theorem mrFirstSmallEnergyBudget_le_relativeBudget
    {eta p q c T : ℝ} {X : ℕ} (hX : 0 < X) (J : ℕ)
    (_hc0 : 0 ≤ c) (hc1 : c ≤ 1 / 2) (_hT : 0 ≤ T) (hTX : T ≤ c * X) :
    mrFirstSmallEnergyBudget eta p q X J T ≤
      mrFirstSmallRelativeBudget eta p q c + 192 * (1 + Real.pi) * (J : ℝ) / X := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hquot : T / X ≤ c := (div_le_iff₀ hXR).2 (by simpa only [mul_comm] using hTX)
  have hres : 0 < mrLogBlockResolution eta p q 1 := by
    unfold mrLogBlockResolution
    positivity
  unfold mrFirstSmallEnergyBudget
  calc
    _ ≤ 2048 * Real.exp 1 * (1 + Real.pi) * (c * Real.exp q + 1) *
        Real.exp (Real.log q / 3 - (1 / 6 - eta) * p) +
      8192 * Real.exp 13 * (1 + Real.pi) * (c + 1) * Real.exp (-p) +
      128 * (1 + Real.pi) * (c + 1) *
        (12 / mrLogBlockResolution eta p q 1 + (J : ℝ) / X + 2 * Real.exp (-p)) := by
      gcongr
    _ = mrFirstSmallRelativeBudget eta p q c +
        (128 * (1 + Real.pi) * (c + 1)) * ((J : ℝ) / X) := by
      unfold mrFirstSmallRelativeBudget
      ring
    _ ≤ mrFirstSmallRelativeBudget eta p q c +
        (192 * (1 + Real.pi)) * ((J : ℝ) / X) := by
      have hcoef : 128 * (1 + Real.pi) * (c + 1) ≤ 192 * (1 + Real.pi) := by
        nlinarith [Real.pi_pos]
      exact add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_right hcoef (by positivity))
    _ = _ := by ring

/-- Every maximal final family eventually contains any prescribed fixed prefix. -/
theorem mrEventually_maximal_index_ge
    {eta p q : ℝ} (heta : eta ≤ 1 / 12) (hp : 2 ≤ p) (hq : 1 ≤ q)
    (hpq : p ≤ q) (hlogq : 1 ≤ Real.log q) (hbudget : 4096 * Real.log q ≤ eta * p)
    (K : ℕ) :
    ∀ᶠ X : ℕ in atTop, ∀ J : ℕ,
      Real.sqrt (Real.log (X : ℝ)) < mrLogScheduleUpper q (J + 1) → K ≤ J := by
  filter_upwards [EulerSubpower.tendsto_log_nat_atTop.eventually
    (eventually_ge_atTop ((mrLogScheduleUpper q K) ^ 2))] with X hscale
  intro J hnext
  by_contra hKJ
  have hJK : J + 1 ≤ K := by omega
  have hmono := mrLogScheduleUpper_mono_positive heta hp hq hpq hlogq hbudget
    (by omega : 1 ≤ J + 1) hJK
  have hroot := Real.le_sqrt_of_sq_le hscale
  linarith

end

end Erdos67b
