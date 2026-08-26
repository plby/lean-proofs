import ErdosProblems.Erdos67b.MRInitialScheduleChoice
import ErdosProblems.Erdos67b.MRScheduledDensitySmall
import ErdosProblems.Erdos67b.MRFixedPowerTypicalEnergy

/-! # One original schedule with small total energy and typicality error -/

open Filter MeasureTheory
open scoped Interval

namespace Erdos67b

noncomputable section

theorem mrExp_neg_initial_le_half {q : ℝ} (hq : Real.exp 1 ≤ q) :
    Real.exp (-q) ≤ (1 : ℝ) / 2 := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hlogtwo : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  calc
    _ ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num

theorem mrExists_scheduled_small_energy_and_density
    {eta epsilon delta : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta) (Q : ℝ) :
    ∃ p q : ℝ, Q ≤ q ∧ Real.exp 1 ≤ q ∧ 2 ≤ p ∧ 2 * p ≤ q ∧
      1 ≤ Real.log q ∧ 4096 * Real.log q ≤ eta * p ∧
      Real.log 2 + 2 * PrimeEstimates.mertensBound ≤ Real.log q - Real.log p ∧
      ∃ M₀ X₀ : ℕ, 0 < M₀ ∧ 2 ≤ X₀ ∧
      ∀ {M X : ℕ}, M₀ ≤ M → X₀ ≤ X →
      ∃ J : ℕ, 1 ≤ J ∧ mrLogScheduleUpper q J ≤ Real.sqrt (Real.log (X : ℝ)) ∧
        Real.sqrt (Real.log (X : ℝ)) < mrLogScheduleUpper q (J + 1) ∧
        (∀ Z : ℕ, Z ≤ 3 * X →
          ((atypicalFactorizationSet (mrScheduledBlocks p q J) Z).card : ℝ) ≤ delta * X) ∧
      ∀ {f : ℕ → ℂ}, IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) → MRArchimedeanNonpretentious f M X →
      ∀ {T : ℝ}, 0 ≤ T → T ≤ (X : ℝ) * Real.exp (-q) →
        (∫ t in -T..T, ‖mrTypicalDyadicPolynomial (mrScheduledBlocks p q J) f X t‖ ^ 2) ≤
          epsilon := by
  obtain ⟨rhoMax, hrhoMax, X₂, _, hdensity⟩ := mrExists_scheduled_atypical_density_small hdelta
  obtain ⟨p, q, hQ, hqexp, hp, hpq, hratio, hlogq, hbudget, hmertens, hinitial⟩ :=
    mrExists_initial_small_energy heta0 heta1 hrhoMax (by positivity : 0 < epsilon / 3) Q
  have hq : 1 ≤ q := (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)).trans hqexp
  obtain ⟨M₀, X₁, hM₀, hX₁, henergy⟩ := mrExists_typical_energy_le_firstSmall_add_small
    heta0 heta1 hp hq hpq hlogq hbudget hmertens (by positivity : 0 < epsilon / 3)
  obtain ⟨X₃, hindex⟩ := eventually_atTop.1
    (mrEventually_lastBlock_index_error (by positivity : 0 < epsilon / (768 * (1 + Real.pi))))
  refine ⟨p, q, hQ, hqexp, hp, hpq, hlogq, hbudget, hmertens,
    M₀, max X₁ (max X₂ X₃), hM₀, hX₁.trans (le_max_left _ _), ?_⟩
  intro M X hM hX
  obtain ⟨J, hJ, hupper, hnext, henergy⟩ := henergy hM ((le_max_left _ _).trans hX)
  have hbad := hdensity X (((le_max_left _ _).trans (le_max_right _ _)).trans hX)
    heta1 hp hq hpq hlogq hbudget hratio hJ hupper
  refine ⟨J, hJ, hupper, hnext, hbad, ?_⟩
  intro f hmul hbound hnonpret T hT hTX
  have hXtwo : 2 ≤ X := (hX₁.trans (le_max_left _ _)).trans hX
  have hXpos : 0 < X := by omega
  have hTMain : T ≤ (X : ℝ) / 2 := by
    have hh := mul_le_mul_of_nonneg_left (mrExp_neg_initial_le_half hqexp) (Nat.cast_nonneg X)
    nlinarith
  have hfull := henergy hmul hbound hnonpret hT hTMain
  have hfirst := mrFirstSmallEnergyBudget_le_initialEnvelope (eta := eta) (p := p)
    (by linarith : 0 ≤ q)
    hXpos J hT hTX
  have hindex' := (hindex X (((le_max_right _ _).trans (le_max_right _ _)).trans hX)).2.2
    hq hJ hupper
  have hindexCost : 256 * (1 + Real.pi) * (J : ℝ) / X ≤ epsilon / 3 := by
    have hh := mul_le_mul_of_nonneg_left hindex' (by positivity : 0 ≤ 256 * (1 + Real.pi))
    have heq : 256 * (1 + Real.pi) * (epsilon / (768 * (1 + Real.pi))) = epsilon / 3 := by
      field_simp
      ring
    rw [heq] at hh
    simpa only [mul_div_assoc] using hh
  linarith

end

end Erdos67b
