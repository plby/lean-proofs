import ErdosProblems.Erdos421.MeanSquare
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Sampling a differentiable function at separated real points -/

namespace Erdos421

open MeasureTheory

/-- A unit-interval point evaluation is bounded by the integral and total variation. -/
theorem unit_interval_evaluation_le {f g : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : Continuous g) (a : ℝ) :
    f a ≤ (∫ t in a..a + 1, f t) + ∫ t in a..a + 1, |g t| := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x ↦ (hf x).continuousAt)
  have hfd : Differentiable ℝ f := fun x ↦ (hf x).differentiableAt
  have hpoint : ∀ t ∈ Set.Icc a (a + 1),
      f a ≤ f t + ∫ v in a..a + 1, |g v| := by
    intro t ht
    have hdiff : ‖f t - f a‖ ≤ ∫ v in a..t, |g v| :=
      norm_sub_le_integral_of_norm_deriv_le_of_le ht.1 hfc.continuousOn hfd.differentiableOn
        (Filter.Eventually.of_forall (fun v _ ↦ by rw [(hf v).deriv, Real.norm_eq_abs]))
        (hg.abs.intervalIntegrable a t)
    have hmono : (∫ v in a..t, |g v|) ≤ ∫ v in a..a + 1, |g v| :=
      intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
        (Filter.Eventually.of_forall (fun v ↦ abs_nonneg (g v)))
        (hg.abs.intervalIntegrable a (a + 1))
    have hlow : f a - f t ≤ ‖f t - f a‖ := by
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact le_abs_self _
    linarith
  have h := intervalIntegral.integral_mono_on (μ := volume) (show a ≤ a + 1 by linarith)
    (continuous_const.intervalIntegrable a (a + 1))
    ((hfc.add continuous_const).intervalIntegrable a (a + 1)) hpoint
  simp only [Pi.add_apply] at h
  rw [intervalIntegral.integral_add (hfc.intervalIntegrable a (a + 1))
    (continuous_const.intervalIntegrable a (a + 1))] at h
  simpa only [intervalIntegral.integral_const, add_sub_cancel_left, smul_eq_mul, one_mul] using h

theorem unit_intervals_disjoint {a b : ℝ} (h : 1 ≤ |a - b|) :
    Disjoint (Set.Ioc a (a + 1)) (Set.Ioc b (b + 1)) := by
  apply Set.disjoint_left.mpr
  intro x hax hbx
  rcases le_total a b with hab | hba
  · rw [abs_of_nonpos (sub_nonpos.mpr hab)] at h
    have := hax.2
    have := hbx.1
    linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr hba)] at h
    have := hbx.2
    have := hax.1
    linarith

theorem sum_unit_integrals_le (S : Finset ℕ) (t : ℕ → ℝ) {A B : ℝ}
    (hAB : A ≤ B) (ht : ∀ i ∈ S, A ≤ t i ∧ t i ≤ B)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |t i - t j|)
    {H : ℝ → ℝ} (hH : Continuous H) (hHpos : ∀ x, 0 ≤ H x) :
    (∑ i ∈ S, ∫ x in t i..t i + 1, H x) ≤ ∫ x in A..B + 1, H x := by
  have hdisj : Set.PairwiseDisjoint (↑S : Set ℕ) (fun i ↦ Set.Ioc (t i) (t i + 1)) :=
    fun i hi j hj hij ↦ unit_intervals_disjoint (hsep i hi j hj hij)
  have hsub : (⋃ i ∈ S, Set.Ioc (t i) (t i + 1)) ⊆ Set.Ioc A (B + 1) := by
    intro x hx
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp hx
    exact ⟨(ht i hi).1.trans_lt hx.1, hx.2.trans (by linarith [(ht i hi).2])⟩
  have hsum : (∑ i ∈ S, ∫ x in t i..t i + 1, H x) =
      ∫ x in ⋃ i ∈ S, Set.Ioc (t i) (t i + 1), H x := by
    rw [integral_biUnion_finset S (fun _ _ ↦ measurableSet_Ioc) hdisj
      (fun i _ ↦ (hH.intervalIntegrable (t i) (t i + 1)).1)]
    apply Finset.sum_congr rfl
    intro i _
    exact intervalIntegral.integral_of_le (by linarith)
  rw [hsum, intervalIntegral.integral_of_le (show A ≤ B + 1 by linarith)]
  exact setIntegral_mono_set (hH.intervalIntegrable A (B + 1)).1
    (Filter.Eventually.of_forall hHpos) hsub.eventuallyLE

/-- The basic sampling inequality underlying separated large-value estimates. -/
theorem separated_sampling_le (S : Finset ℕ) (t : ℕ → ℝ) {A B : ℝ}
    (hAB : A ≤ B) (ht : ∀ i ∈ S, A ≤ t i ∧ t i ≤ B)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |t i - t j|)
    {f g : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (g x) x) (hg : Continuous g)
    (hfpos : ∀ x, 0 ≤ f x) :
    (∑ i ∈ S, f (t i)) ≤ ∫ x in A..B + 1, (f x + |g x|) := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x ↦ (hf x).continuousAt)
  calc
    _ ≤ ∑ i ∈ S, ∫ x in t i..t i + 1, (f x + |g x|) := by
      apply Finset.sum_le_sum
      intro i _
      rw [intervalIntegral.integral_add
        (hfc.intervalIntegrable _ _) (hg.abs.intervalIntegrable _ _)]
      exact unit_interval_evaluation_le hf hg (t i)
    _ ≤ _ := sum_unit_integrals_le S t hAB ht hsep (hfc.add hg.abs)
      (fun x ↦ add_nonneg (hfpos x) (abs_nonneg _))

theorem separated_norm_square_sum_le (S : Finset ℕ) (t : ℕ → ℝ) {A B : ℝ}
    (hAB : A ≤ B) (ht : ∀ i ∈ S, A ≤ t i ∧ t i ≤ B)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |t i - t j|)
    {F F' : ℝ → ℂ} (hF : ∀ x, HasDerivAt F (F' x) x) (hF' : Continuous F') :
    (∑ i ∈ S, ‖F (t i)‖ ^ 2) ≤
      2 * (∫ x in A..B + 1, ‖F x‖ ^ 2) + ∫ x in A..B + 1, ‖F' x‖ ^ 2 := by
  let g : ℝ → ℝ := fun x ↦ 2 * inner ℝ (F x) (F' x)
  have hFc : Continuous F := continuous_iff_continuousAt.mpr (fun x ↦ (hF x).continuousAt)
  have hg : Continuous g := continuous_const.mul (hFc.inner hF')
  have hsq : ∀ x, HasDerivAt (fun y ↦ ‖F y‖ ^ 2) (g x) x :=
    fun x ↦ (hF x).norm_sq
  have hgBound : ∀ x, |g x| ≤ ‖F x‖ ^ 2 + ‖F' x‖ ^ 2 := by
    intro x
    have hi := abs_real_inner_le_norm (F x) (F' x)
    dsimp only [g]
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [sq_nonneg (‖F x‖ - ‖F' x‖)]
  have hA : A ≤ B + 1 := by linarith
  have hleft : IntervalIntegrable (fun x ↦ ‖F x‖ ^ 2 + |g x|) volume A (B + 1) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hfirst : IntervalIntegrable (fun x ↦ 2 * ‖F x‖ ^ 2) volume A (B + 1) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hsecond : IntervalIntegrable (fun x ↦ ‖F' x‖ ^ 2) volume A (B + 1) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hright : IntervalIntegrable (fun x ↦ 2 * ‖F x‖ ^ 2 + ‖F' x‖ ^ 2)
      volume A (B + 1) := by
    apply Continuous.intervalIntegrable
    fun_prop
  calc
    _ ≤ ∫ x in A..B + 1, (‖F x‖ ^ 2 + |g x|) :=
      separated_sampling_le S t hAB ht hsep hsq hg (fun x ↦ sq_nonneg _)
    _ ≤ ∫ x in A..B + 1, (2 * ‖F x‖ ^ 2 + ‖F' x‖ ^ 2) := by
      apply intervalIntegral.integral_mono_on hA hleft hright
      intro x _
      linarith [hgBound x]
    _ = _ := by
      rw [intervalIntegral.integral_add hfirst hsecond, intervalIntegral.integral_const_mul]

end Erdos421
