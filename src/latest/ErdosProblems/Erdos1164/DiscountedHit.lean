import ErdosProblems.Erdos1164.SelectedCost

/-! # A uniform contraction for discounted hitting costs -/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1164

open Erdos1165 Erdos1165.PlanarPotential

/-- A witness to the cost event precedes every visit to the target. -/
theorem beforePointVisits_le_at_hit {x y : Point} {k n : ℕ} {w : StepPath}
    (hw : w ∈ beforePointVisits x y k) (hn : trajectoryFrom x w n = y) :
    k ≤ originVisits (trajectoryFrom x w) n := by
  obtain ⟨j, hj, hno⟩ := hw
  have hjn : j ≤ n := by
    by_contra h
    exact hno n (by omega) hn
  exact hj.trans (originVisits_mono _ hjn)

private theorem measurable_originVisits_pair :
    Measurable (fun p : WalkPath × ℕ ↦ originVisits p.1 p.2) := by
  apply measurable_from_prod_countable_left (α := WalkPath) (β := ℕ) (γ := ℕ)
  intro n
  exact measurable_originVisits n

/-- Local time evaluated at a measurable natural-valued time is measurable. -/
theorem measurable_originVisits_at (x : Point) {τ : StepPath → ℕ} (hτ : Measurable τ) :
    Measurable fun w ↦ originVisits (trajectoryFrom x w) (τ w) :=
  measurable_originVisits_pair.comp ((measurable_trajectoryFrom x).prodMk hτ)

/-- Discounted origin visits at a successful target-hitting time; unsuccessful
paths carry zero weight. This applies in particular to capped first hits. -/
noncomputable def discountedHitAt (x : Point) (ell : ℕ) (τ : StepPath → ℕ)
    (A : Set StepPath) : StepPath → ℝ≥0∞ :=
  A.indicator (fun w ↦ ENNReal.ofReal
    (Real.exp (-(originVisits (trajectoryFrom x w) (τ w) : ℝ) / (ell : ℝ))))

theorem measurable_discountedHitAt (x : Point) (ell : ℕ) {τ : StepPath → ℕ}
    (hτ : Measurable τ) {A : Set StepPath} (hA : MeasurableSet A) :
    Measurable (discountedHitAt x ell τ A) := by
  apply Measurable.indicator _ hA
  apply ENNReal.measurable_ofReal.comp
  apply Real.measurable_exp.comp
  have hc : Measurable fun w ↦ (originVisits (trajectoryFrom x w) (τ w) : ℝ) :=
    (measurable_of_countable (fun k : ℕ ↦ (k : ℝ))).comp (measurable_originVisits_at x hτ)
  exact hc.neg.div_const _

private theorem discounted_contraction {A : Set StepPath} (hA : MeasurableSet A)
    (hprob : (1 / 256 : ℝ) ≤ fairSteps.real A) {f : StepPath → ℝ≥0∞}
    (hf : ∀ w, f w ≤ 1)
    (hfA : ∀ w ∈ A, f w ≤ ENNReal.ofReal (Real.exp (-1))) :
    (∫⁻ w, f w ∂fairSteps) ≤ ENNReal.ofReal targetCostDiscount := by
  have hpoint : f ≤ (A.indicator (fun _ ↦ ENNReal.ofReal (Real.exp (-1)))) +
      (Aᶜ.indicator (fun _ ↦ (1 : ℝ≥0∞))) := by
    intro w
    by_cases hw : w ∈ A
    · simpa only [Pi.add_apply, Set.indicator_of_mem hw,
        Set.indicator_of_notMem (show w ∉ Aᶜ from fun h ↦ h hw), add_zero] using hfA w hw
    · simpa only [Pi.add_apply, Set.indicator_of_notMem hw,
        Set.indicator_of_mem (show w ∈ Aᶜ from hw), zero_add] using hf w
  have hbound := lintegral_mono (μ := fairSteps) hpoint
  simp only [Pi.add_apply] at hbound
  rw [lintegral_add_left (measurable_const.indicator hA),
    lintegral_indicator_const hA, lintegral_indicator_const hA.compl, one_mul] at hbound
  apply hbound.trans
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_pos _).le,
    ENNReal.toReal_ofReal targetCostDiscount_pos.le]
  change Real.exp (-1) * fairSteps.real A + fairSteps.real Aᶜ ≤ targetCostDiscount
  rw [measureReal_compl hA]
  have hu : fairSteps.real (Set.univ : Set StepPath) = 1 := by simp [measureReal_def]
  rw [hu]
  have he : Real.exp (-1) ≤ 1 := (Real.exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0)).le
  have hmul := mul_le_mul_of_nonneg_left hprob (by linarith : 0 ≤ 1 - Real.exp (-1))
  unfold targetCostDiscount
  nlinarith

/-- Any successful hit at any natural-valued time has the same discounted
upper bound. The target and starting point obey the proved spatial hypotheses. -/
theorem selected_discounted_hit_bound {m : ℕ} (hm : LargeTargetScale m) (j : Fin m)
    {x : Point} (hx : x = 0 ∨ ∃ i : Fin m, i ≠ j ∧ x = separatedTarget m i)
    (τ : StepPath → ℕ) (A : Set StepPath)
    (hhit : ∀ w ∈ A, trajectoryFrom x w (τ w) = separatedTarget m j) :
    (∫⁻ w, discountedHitAt x (targetVisitCost m) τ A w ∂fairSteps) ≤
      ENNReal.ofReal targetCostDiscount := by
  have hell : 0 < (targetVisitCost m : ℝ) := by exact_mod_cast targetVisitCost_pos m
  apply discounted_contraction (measurableSet_beforePointVisits x (separatedTarget m j) _)
    (selected_cost_uniform hm j hx)
  · intro w
    by_cases hw : w ∈ A
    · rw [discountedHitAt, Set.indicator_of_mem hw]
      apply ENNReal.ofReal_le_one.mpr
      apply Real.exp_le_one_iff.mpr
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hell.le
    · rw [discountedHitAt, Set.indicator_of_notMem hw]
      exact zero_le
  · intro w hwcost
    by_cases hw : w ∈ A
    · rw [discountedHitAt, Set.indicator_of_mem hw]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hcost := beforePointVisits_le_at_hit hwcost (hhit w hw)
      have hcast : (targetVisitCost m : ℝ) ≤ (originVisits (trajectoryFrom x w) (τ w) : ℝ) :=
        by exact_mod_cast hcost
      apply (div_le_iff₀ hell).mpr
      linarith
    · rw [discountedHitAt, Set.indicator_of_notMem hw]
      exact zero_le

end Erdos1164
