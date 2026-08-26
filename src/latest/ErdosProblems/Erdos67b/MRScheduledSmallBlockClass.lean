import ErdosProblems.Erdos67b.MRBlockScheduleParameters
import ErdosProblems.Erdos67b.MRFirstSmallBlockClass

/-!
# First-small-block estimate on the actual uniform schedule

The global logarithmic schedule discharges every scalar hypothesis of
the class bound. Polynomial support and frequency-class hypotheses stay
explicit for connection with the arithmetic Ramaré decomposition.
-/

open scoped BigOperators Interval
open Finset MeasureTheory

namespace Erdos67b

noncomputable section

def mrScheduledSubblocks (eta p₁ q₁ : ℝ) (j : ℕ) : Finset ℕ :=
  mrLogBlockIndices (mrLogBlockResolution eta p₁ q₁ (j : ℝ))
    (mrLogScheduleLower p₁ q₁ j) (mrLogScheduleUpper q₁ j)

def mrScheduledParameter (eta p₁ q₁ : ℝ) (j r : ℕ) : ℝ :=
  (r : ℝ) / mrLogBlockResolution eta p₁ q₁ (j : ℝ)

theorem mrScheduledParameter_bounds
    {eta p₁ q₁ : ℝ} (heta : eta ≤ 1 / 12) (hp : 2 ≤ p₁) (hq : 1 ≤ q₁)
    (hlogq : 1 ≤ Real.log q₁) (hbudget : 4096 * Real.log q₁ ≤ eta * p₁)
    {j r : ℕ} (hj : 1 ≤ j) (hr : r ∈ mrScheduledSubblocks eta p₁ q₁ j) :
    mrLogScheduleLower p₁ q₁ j - 1 ≤ mrScheduledParameter eta p₁ q₁ j r ∧
      mrScheduledParameter eta p₁ q₁ j r ≤ mrLogScheduleUpper q₁ j := by
  have hH := mrLogSchedule_resolution_one_le heta (by linarith) hlogq hbudget hj
  have hP := mrLogScheduleLower_ge (by linarith : 0 ≤ p₁) hq hj
  have hQ := mrLogScheduleUpper_ge hq hj
  exact mrLogBlockIndices_parameter_bounds hH (by linarith) (by linarith) hr

theorem scheduled_firstSmallBlock_frequencyClass_energy_le
    {eta p₁ q₁ : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hp : 2 ≤ p₁) (hqexp : Real.exp 1 ≤ q₁) (hpq : p₁ ≤ q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁) {j : ℕ} (hj : 2 ≤ j)
    (P S : ℕ → Finset ℕ) (a b : ℕ → ℕ → ℂ) (F : ℕ → ℝ → ℂ)
    (hP : ∀ r ∈ mrScheduledSubblocks eta p₁ q₁ (j - 1), ∀ p ∈ P r, p.Prime)
    (ha : ∀ r ∈ mrScheduledSubblocks eta p₁ q₁ (j - 1), ∀ p ∈ P r, ‖a r p‖ ≤ (p : ℝ)⁻¹)
    (hb : ∀ s ∈ mrScheduledSubblocks eta p₁ q₁ j, ∀ m ∈ S s, ‖b s m‖ ≤ (m : ℝ)⁻¹)
    (hPlo : ∀ r ∈ mrScheduledSubblocks eta p₁ q₁ (j - 1), ∀ p ∈ P r,
      Real.exp (mrScheduledParameter eta p₁ q₁ (j - 1) r) ≤ p)
    (hPhi : ∀ r ∈ mrScheduledSubblocks eta p₁ q₁ (j - 1), ∀ p ∈ P r,
      (p : ℝ) ≤ 2 * Real.exp (mrScheduledParameter eta p₁ q₁ (j - 1) r))
    {X : ℕ} (hX : 0 < X)
    (hSlo : ∀ s ∈ mrScheduledSubblocks eta p₁ q₁ j, ∀ m ∈ S s,
      (X : ℝ) / Real.exp (mrScheduledParameter eta p₁ q₁ j s) ≤ m)
    (hShi : ∀ s ∈ mrScheduledSubblocks eta p₁ q₁ j, ∀ m ∈ S s,
      (m : ℝ) ≤ 2 * X / Real.exp (mrScheduledParameter eta p₁ q₁ j s))
    (hF : ∀ s ∈ mrScheduledSubblocks eta p₁ q₁ j, Continuous (F s))
    {E : Set ℝ} (hE : MeasurableSet E) {T : ℝ} (hT : 0 ≤ T)
    (hsmall : ∀ s ∈ mrScheduledSubblocks eta p₁ q₁ j, ∀ t ∈ E, t ∈ Set.Icc (-T) T →
      ‖F s t‖ ≤ Real.exp (-mrThresholdExponent eta (j : ℝ) * mrScheduledParameter eta p₁ q₁ j s))
    (hcover : ∀ t ∈ E, t ∈ Set.Icc (-T) T →
      ∃ r ∈ mrScheduledSubblocks eta p₁ q₁ (j - 1),
        Real.exp (-mrThresholdExponent eta ((j - 1 : ℕ) : ℝ) *
          mrScheduledParameter eta p₁ q₁ (j - 1) r) ≤
            ‖logarithmicDirichletPolynomial (P r) (a r) t‖) :
    mrLogBlockResolution eta p₁ q₁ (j : ℝ) * mrLogScheduleUpper q₁ j *
      (∑ s ∈ mrScheduledSubblocks eta p₁ q₁ j, ∫ t in -T..T, E.indicator
        (fun t ↦ ‖F s t * logarithmicDirichletPolynomial (S s) (b s) t‖ ^ 2) t) ≤
      128 * Real.exp 12 * (1 + Real.pi) * (T / X + 1) /
        ((j : ℝ) ^ 2 * Real.exp (mrLogScheduleUpper q₁ (j - 1))) := by
  have hj1 : 1 ≤ j := by omega
  have hjprev : 1 ≤ j - 1 := by omega
  have hq : 1 ≤ q₁ := (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)).trans hqexp
  have hlogq : 1 ≤ Real.log q₁ := by
    have hh := Real.log_le_log (Real.exp_pos 1) hqexp
    rwa [Real.log_exp] at hh
  have hHcur := mrLogSchedule_resolution_one_le heta1 (by linarith) hlogq hbudget hj1
  have hHprev := mrLogSchedule_resolution_one_le heta1 (by linarith) hlogq hbudget hjprev
  have hQcur : 1 ≤ mrLogScheduleUpper q₁ j := hq.trans (mrLogScheduleUpper_ge hq hj1)
  have hQprev : 2 ≤ mrLogScheduleUpper q₁ (j - 1) :=
    (hp.trans hpq).trans (mrLogScheduleUpper_ge hq hjprev)
  have hPprev : 2 ≤ mrLogScheduleLower p₁ q₁ (j - 1) :=
    hp.trans (mrLogScheduleLower_ge (by linarith) hq hjprev)
  have hPcur : 2 ≤ mrLogScheduleLower p₁ q₁ j :=
    hp.trans (mrLogScheduleLower_ge (by linarith) hq hj1)
  have hblockgap := mrLogSchedule_block_gap heta1 hp hq hlogq hbudget hj
  have hcurPQ := mrLogScheduleLower_le_upper hq hpq hj1
  have hQmono : mrLogScheduleUpper q₁ (j - 1) ≤ mrLogScheduleUpper q₁ j := by linarith
  have hHmono : mrLogBlockResolution eta p₁ q₁ ((j - 1 : ℕ) : ℝ) ≤
      mrLogBlockResolution eta p₁ q₁ (j : ℝ) :=
    mrLogBlockResolution_mono (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le j 1)
  have hcurProd : 1 ≤ mrLogBlockResolution eta p₁ q₁ (j : ℝ) * mrLogScheduleUpper q₁ j := by
    have hh := mul_le_mul hHcur hQcur (by norm_num : (0 : ℝ) ≤ 1) (by linarith)
    simpa only [one_mul] using hh
  have hprevProd : 1 ≤ mrLogBlockResolution eta p₁ q₁ ((j - 1 : ℕ) : ℝ) *
      mrLogScheduleUpper q₁ (j - 1) := by
    have hh := mul_le_mul hHprev (show 1 ≤ mrLogScheduleUpper q₁ (j - 1) by linarith)
      (by norm_num : (0 : ℝ) ≤ 1) (by linarith)
    simpa only [one_mul] using hh
  have hprevParam (r : ℕ) (hr : r ∈ mrScheduledSubblocks eta p₁ q₁ (j - 1)) :=
    mrScheduledParameter_bounds heta1 hp hq hlogq hbudget hjprev hr
  have hcurParam (s : ℕ) (hs : s ∈ mrScheduledSubblocks eta p₁ q₁ j) :=
    mrScheduledParameter_bounds heta1 hp hq hlogq hbudget hj1 hs
  have halpha := mrThresholdExponent_bounds heta0.le (by linarith : eta ≤ 1 / 6)
    (by exact_mod_cast hjprev : (1 : ℝ) ≤ (j - 1 : ℕ))
  apply firstSmallBlock_frequencyClass_energy_le
    (mrScheduledSubblocks eta p₁ q₁ j) (mrScheduledSubblocks eta p₁ q₁ (j - 1)) P S a b
    (mrScheduledParameter eta p₁ q₁ (j - 1)) (mrScheduledParameter eta p₁ q₁ j) F
    hP ha hb (by linarith : 0 < mrLogBlockResolution eta p₁ q₁ (j : ℝ))
    (by linarith : 0 < mrLogScheduleUpper q₁ j) (by exact_mod_cast hj1) hQprev hblockgap
    ?_ ?_ halpha.1 halpha.2 (mrSchedule_delta_pos heta0 hj1) (mrSchedule_delta_le_one heta1 hj1)
    ?_ (mrLogSchedule_threshold_gap heta0.le hj) ?_
    (mrLogSchedule_resolution_prefactor heta0 heta1 hp hq hpq hlogq hbudget hj)
    (mrLogSchedule_gap_separation hq hlogq hbudget hj) hPlo hPhi hX hSlo hShi hF hE hT hsmall hcover
  · intro r hr
    have hb := hprevParam r hr
    exact ⟨by linarith [hb.1], hb.2⟩
  · intro s hs
    exact (hcurParam s hs).1
  · intro s hs r hr
    have hvs : 1 ≤ mrScheduledParameter eta p₁ q₁ j s := by linarith [(hcurParam s hs).1]
    exact amplification_cost_le_of_block_range hPprev (hprevParam r hr).1 hvs (hcurParam s hs).2
      (mrLogSchedule_cost_separation heta0 hp hq hlogq hbudget hj)
  · exact mrLogBlock_covering_cost_le (by linarith) (by linarith) (by linarith) (by linarith)
      hHmono hQmono hcurProd hprevProd

/-- The uniform schedule bound for enlarged cofactor intervals. The same
initial parameter budget absorbs the shifted factorial cost. -/
theorem scheduled_firstSmallBlock_enlarged_frequencyClass_energy_le
    {eta p₁ q₁ : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hp : 2 ≤ p₁) (hqexp : Real.exp 1 ≤ q₁) (hpq : p₁ ≤ q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁) {j : ℕ} (hj : 2 ≤ j)
    (P S : ℕ → Finset ℕ) (a b : ℕ → ℕ → ℂ) (F : ℕ → ℝ → ℂ)
    (hP : ∀ r ∈ mrScheduledSubblocks eta p₁ q₁ (j - 1), ∀ p ∈ P r, p.Prime)
    (ha : ∀ r ∈ mrScheduledSubblocks eta p₁ q₁ (j - 1), ∀ p ∈ P r, ‖a r p‖ ≤ (p : ℝ)⁻¹)
    (hb : ∀ s ∈ mrScheduledSubblocks eta p₁ q₁ j, ∀ m ∈ S s, ‖b s m‖ ≤ (m : ℝ)⁻¹)
    (hPlo : ∀ r ∈ mrScheduledSubblocks eta p₁ q₁ (j - 1), ∀ p ∈ P r,
      Real.exp (mrScheduledParameter eta p₁ q₁ (j - 1) r) ≤ p)
    (hPhi : ∀ r ∈ mrScheduledSubblocks eta p₁ q₁ (j - 1), ∀ p ∈ P r,
      (p : ℝ) ≤ 2 * Real.exp (mrScheduledParameter eta p₁ q₁ (j - 1) r))
    {X : ℕ} (hX : 0 < X)
    (hSlo : ∀ s ∈ mrScheduledSubblocks eta p₁ q₁ j, ∀ m ∈ S s,
      (X : ℝ) / Real.exp (mrScheduledParameter eta p₁ q₁ j s + 1) ≤ m)
    (hShi : ∀ s ∈ mrScheduledSubblocks eta p₁ q₁ j, ∀ m ∈ S s,
      (m : ℝ) ≤ 8 * X / Real.exp (mrScheduledParameter eta p₁ q₁ j s + 1))
    (hF : ∀ s ∈ mrScheduledSubblocks eta p₁ q₁ j, Continuous (F s))
    {E : Set ℝ} (hE : MeasurableSet E) {T : ℝ} (hT : 0 ≤ T)
    (hsmall : ∀ s ∈ mrScheduledSubblocks eta p₁ q₁ j, ∀ t ∈ E, t ∈ Set.Icc (-T) T →
      ‖F s t‖ ≤ Real.exp (-mrThresholdExponent eta (j : ℝ) * mrScheduledParameter eta p₁ q₁ j s))
    (hcover : ∀ t ∈ E, t ∈ Set.Icc (-T) T →
      ∃ r ∈ mrScheduledSubblocks eta p₁ q₁ (j - 1),
        Real.exp (-mrThresholdExponent eta ((j - 1 : ℕ) : ℝ) *
          mrScheduledParameter eta p₁ q₁ (j - 1) r) ≤
            ‖logarithmicDirichletPolynomial (P r) (a r) t‖) :
    mrLogBlockResolution eta p₁ q₁ (j : ℝ) * mrLogScheduleUpper q₁ j *
      (∑ s ∈ mrScheduledSubblocks eta p₁ q₁ j, ∫ t in -T..T, E.indicator
        (fun t ↦ ‖F s t * logarithmicDirichletPolynomial (S s) (b s) t‖ ^ 2) t) ≤
      512 * Real.exp 13 * (1 + Real.pi) * (T / X + 1) /
        ((j : ℝ) ^ 2 * Real.exp (mrLogScheduleUpper q₁ (j - 1))) := by
  have hj1 : 1 ≤ j := by omega
  have hjprev : 1 ≤ j - 1 := by omega
  have hq : 1 ≤ q₁ := (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)).trans hqexp
  have hlogq : 1 ≤ Real.log q₁ := by
    have hh := Real.log_le_log (Real.exp_pos 1) hqexp
    rwa [Real.log_exp] at hh
  have hHcur := mrLogSchedule_resolution_one_le heta1 (by linarith) hlogq hbudget hj1
  have hHprev := mrLogSchedule_resolution_one_le heta1 (by linarith) hlogq hbudget hjprev
  have hQcur : 1 ≤ mrLogScheduleUpper q₁ j := hq.trans (mrLogScheduleUpper_ge hq hj1)
  have hQprev : 2 ≤ mrLogScheduleUpper q₁ (j - 1) :=
    (hp.trans hpq).trans (mrLogScheduleUpper_ge hq hjprev)
  have hPprev : 2 ≤ mrLogScheduleLower p₁ q₁ (j - 1) :=
    hp.trans (mrLogScheduleLower_ge (by linarith) hq hjprev)
  have hPcur : 2 ≤ mrLogScheduleLower p₁ q₁ j :=
    hp.trans (mrLogScheduleLower_ge (by linarith) hq hj1)
  have hblockgap := mrLogSchedule_block_gap heta1 hp hq hlogq hbudget hj
  have hcurPQ := mrLogScheduleLower_le_upper hq hpq hj1
  have hQmono : mrLogScheduleUpper q₁ (j - 1) ≤ mrLogScheduleUpper q₁ j := by linarith
  have hHmono : mrLogBlockResolution eta p₁ q₁ ((j - 1 : ℕ) : ℝ) ≤
      mrLogBlockResolution eta p₁ q₁ (j : ℝ) :=
    mrLogBlockResolution_mono (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le j 1)
  have hcurProd : 1 ≤ mrLogBlockResolution eta p₁ q₁ (j : ℝ) * mrLogScheduleUpper q₁ j := by
    have hh := mul_le_mul hHcur hQcur (by norm_num : (0 : ℝ) ≤ 1) (by linarith)
    simpa only [one_mul] using hh
  have hprevProd : 1 ≤ mrLogBlockResolution eta p₁ q₁ ((j - 1 : ℕ) : ℝ) *
      mrLogScheduleUpper q₁ (j - 1) := by
    have hh := mul_le_mul hHprev (show 1 ≤ mrLogScheduleUpper q₁ (j - 1) by linarith)
      (by norm_num : (0 : ℝ) ≤ 1) (by linarith)
    simpa only [one_mul] using hh
  have hprevParam (r : ℕ) (hr : r ∈ mrScheduledSubblocks eta p₁ q₁ (j - 1)) :=
    mrScheduledParameter_bounds heta1 hp hq hlogq hbudget hjprev hr
  have hcurParam (s : ℕ) (hs : s ∈ mrScheduledSubblocks eta p₁ q₁ j) :=
    mrScheduledParameter_bounds heta1 hp hq hlogq hbudget hj1 hs
  have halpha := mrThresholdExponent_bounds heta0.le (by linarith : eta ≤ 1 / 6)
    (by exact_mod_cast hjprev : (1 : ℝ) ≤ (j - 1 : ℕ))
  apply firstSmallBlock_enlarged_frequencyClass_energy_le
    (mrScheduledSubblocks eta p₁ q₁ j) (mrScheduledSubblocks eta p₁ q₁ (j - 1)) P S a b
    (mrScheduledParameter eta p₁ q₁ (j - 1)) (mrScheduledParameter eta p₁ q₁ j) F
    hP ha hb (by linarith : 0 < mrLogBlockResolution eta p₁ q₁ (j : ℝ))
    (by linarith : 0 < mrLogScheduleUpper q₁ j) (by exact_mod_cast hj1) hQprev hblockgap
    ?_ ?_ halpha.1 halpha.2
    (mrThresholdExponent_bounds heta0.le (by linarith) (by exact_mod_cast hj1)).2
    (mrSchedule_delta_pos heta0 hj1) (mrSchedule_delta_le_one heta1 hj1)
    ?_ (mrLogSchedule_threshold_gap heta0.le hj) ?_
    (mrLogSchedule_resolution_prefactor heta0 heta1 hp hq hpq hlogq hbudget hj)
    (mrLogSchedule_gap_separation hq hlogq hbudget hj) hPlo hPhi hX hSlo hShi hF hE hT hsmall hcover
  · intro r hr
    have hb := hprevParam r hr
    exact ⟨by linarith [hb.1], hb.2⟩
  · intro s hs
    exact (hcurParam s hs).1
  · intro s hs r hr
    have hvs : 1 ≤ mrScheduledParameter eta p₁ q₁ j s := by linarith [(hcurParam s hs).1]
    exact amplification_cost_le_of_block_range hPprev (hprevParam r hr).1 (by linarith : 1 ≤ mrScheduledParameter eta p₁ q₁ j s + 1)
      (add_le_add (hcurParam s hs).2 le_rfl)
      (mrLogSchedule_shifted_cost_separation heta0 hp hq hlogq hbudget hj)
  · exact mrLogBlock_covering_cost_le (by linarith) (by linarith) (by linarith) (by linarith)
      hHmono hQmono hcurProd hprevProd

end

end Erdos67b
