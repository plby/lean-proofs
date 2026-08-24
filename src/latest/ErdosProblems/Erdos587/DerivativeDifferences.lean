import ErdosProblems.Erdos587.FiniteDifferences
import ErdosProblems.Erdos587.SqrtPhase

/-! Transfer derivative bounds to unit forward differences by repeated mean-value arguments. -/

namespace Erdos587

noncomputable def realForwardDifference (f : ℝ → ℝ) (x : ℝ) : ℝ := f (x + 1) - f x

lemma phaseIncrement_sample (f : ℝ → ℝ) :
    phaseIncrement (fun n : ℕ => f n) = fun n : ℕ => realForwardDifference f n := by
  funext n
  simp only [phaseIncrement, realForwardDifference, Nat.cast_add, Nat.cast_one]

lemma hasDerivAt_realForwardDifference (f f' : ℝ → ℝ) (x : ℝ)
    (h₀ : HasDerivAt f (f' x) x) (h₁ : HasDerivAt f (f' (x + 1)) (x + 1)) :
    HasDerivAt (realForwardDifference f) (realForwardDifference f' x) x := by
  have hshift : HasDerivAt (fun y : ℝ => y + 1) 1 x := (hasDerivAt_id' x).add_const 1
  have hh := (h₁.comp x hshift).sub h₀
  change HasDerivAt (fun y : ℝ => f (y + 1) - f y) (f' (x + 1) - f' x) x
  simpa only [mul_one] using! hh

lemma realForwardDifference_bounds (f f' : ℝ → ℝ) (x : ℝ) {lo hi : ℝ}
    (hf : ∀ y ∈ Set.Icc x (x + 1), HasDerivAt f (f' y) y)
    (hbound : ∀ y ∈ Set.Icc x (x + 1), lo ≤ f' y ∧ f' y ≤ hi) :
    lo ≤ realForwardDifference f x ∧ realForwardDifference f x ≤ hi := by
  have hcont : ContinuousOn f (Set.Icc x (x + 1)) :=
    fun y hy => (hf y hy).continuousAt.continuousWithinAt
  obtain ⟨c, hc, heq⟩ := exists_hasDerivAt_eq_slope f f' (by linarith : x < x + 1) hcont
    (fun y hy => hf y ⟨hy.1.le, hy.2.le⟩)
  simp only [add_sub_cancel_left, div_one] at heq
  have hb := hbound c ⟨hc.1.le, hc.2.le⟩
  change lo ≤ f (x + 1) - f x ∧ f (x + 1) - f x ≤ hi
  rwa [heq] at hb

theorem realSecondDifference_bounds (f f' f'' : ℝ → ℝ) (x : ℝ) {lo hi : ℝ}
    (hf : ∀ y ∈ Set.Icc x (x + 2), HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Set.Icc x (x + 2), HasDerivAt f' (f'' y) y)
    (hbound : ∀ y ∈ Set.Icc x (x + 2), lo ≤ f'' y ∧ f'' y ≤ hi) :
    lo ≤ realForwardDifference (realForwardDifference f) x ∧
      realForwardDifference (realForwardDifference f) x ≤ hi := by
  apply realForwardDifference_bounds (realForwardDifference f) (realForwardDifference f') x
  · intro y hy
    exact hasDerivAt_realForwardDifference f f' y
      (hf y ⟨hy.1, by linarith [hy.2]⟩)
      (hf (y + 1) ⟨by linarith [hy.1], by linarith [hy.2]⟩)
  · intro y hy
    apply realForwardDifference_bounds f' f'' y
    · intro z hz
      exact hf' z ⟨by linarith [hz.1, hy.1], by linarith [hz.2, hy.2]⟩
    · intro z hz
      exact hbound z ⟨by linarith [hz.1, hy.1], by linarith [hz.2, hy.2]⟩

theorem realThirdDifference_bounds (f f' f'' f''' : ℝ → ℝ) (x : ℝ) {lo hi : ℝ}
    (hf : ∀ y ∈ Set.Icc x (x + 3), HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Set.Icc x (x + 3), HasDerivAt f' (f'' y) y)
    (hf'' : ∀ y ∈ Set.Icc x (x + 3), HasDerivAt f'' (f''' y) y)
    (hbound : ∀ y ∈ Set.Icc x (x + 3), lo ≤ f''' y ∧ f''' y ≤ hi) :
    lo ≤ realForwardDifference (realForwardDifference (realForwardDifference f)) x ∧
      realForwardDifference (realForwardDifference (realForwardDifference f)) x ≤ hi := by
  apply realSecondDifference_bounds (realForwardDifference f) (realForwardDifference f')
    (realForwardDifference f'') x
  · intro y hy
    exact hasDerivAt_realForwardDifference f f' y
      (hf y ⟨hy.1, by linarith [hy.2]⟩)
      (hf (y + 1) ⟨by linarith [hy.1], by linarith [hy.2]⟩)
  · intro y hy
    exact hasDerivAt_realForwardDifference f' f'' y
      (hf' y ⟨hy.1, by linarith [hy.2]⟩)
      (hf' (y + 1) ⟨by linarith [hy.1], by linarith [hy.2]⟩)
  · intro y hy
    apply realForwardDifference_bounds f'' f''' y
    · intro z hz
      exact hf'' z ⟨by linarith [hz.1, hy.1], by linarith [hz.2, hy.2]⟩
    · intro z hz
      exact hbound z ⟨by linarith [hz.1, hy.1], by linarith [hz.2, hy.2]⟩

theorem second_sample_difference_bounds (f f' f'' : ℝ → ℝ) (n : ℕ) {lo hi : ℝ}
    (hf : ∀ y ∈ Set.Icc (n : ℝ) (n + 2), HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Set.Icc (n : ℝ) (n + 2), HasDerivAt f' (f'' y) y)
    (hbound : ∀ y ∈ Set.Icc (n : ℝ) (n + 2), lo ≤ f'' y ∧ f'' y ≤ hi) :
    lo ≤ phaseIncrement (phaseIncrement (fun n : ℕ => f n)) n ∧
      phaseIncrement (phaseIncrement (fun n : ℕ => f n)) n ≤ hi := by
  rw [phaseIncrement_sample f, phaseIncrement_sample (realForwardDifference f)]
  exact realSecondDifference_bounds f f' f'' n hf hf' hbound

theorem third_sample_difference_bounds (f f' f'' f''' : ℝ → ℝ) (n : ℕ) {lo hi : ℝ}
    (hf : ∀ y ∈ Set.Icc (n : ℝ) (n + 3), HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Set.Icc (n : ℝ) (n + 3), HasDerivAt f' (f'' y) y)
    (hf'' : ∀ y ∈ Set.Icc (n : ℝ) (n + 3), HasDerivAt f'' (f''' y) y)
    (hbound : ∀ y ∈ Set.Icc (n : ℝ) (n + 3), lo ≤ f''' y ∧ f''' y ≤ hi) :
    lo ≤ phaseIncrement (phaseIncrement (phaseIncrement (fun n : ℕ => f n))) n ∧
      phaseIncrement (phaseIncrement (phaseIncrement (fun n : ℕ => f n))) n ≤ hi := by
  rw [phaseIncrement_sample f, phaseIncrement_sample (realForwardDifference f),
    phaseIncrement_sample (realForwardDifference (realForwardDifference f))]
  exact realThirdDifference_bounds f f' f'' f''' n hf hf' hf'' hbound

end Erdos587
