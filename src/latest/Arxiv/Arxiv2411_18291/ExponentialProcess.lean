import Arxiv.Arxiv2411_18291.ConditionalExponential
import Mathlib.Probability.Martingale.Basic

/-! # Exponential compensation for a finite adapted process -/

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The exponential of the sum after subtracting scaled conditional means. -/
def compensatedExp (ℱ : Filtration ℕ mΩ) (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (t g : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp (∑ i ∈ range n, (t * X i ω - g * P[X i | ℱ i] ω))

variable {ℱ : Filtration ℕ mΩ} {P : Measure Ω} [IsProbabilityMeasure P]
variable {X : ℕ → Ω → ℝ} {t g C : ℝ} {n : ℕ}

omit [IsProbabilityMeasure P] in
@[simp] theorem compensatedExp_zero : compensatedExp ℱ P X t g 0 = fun _ => 1 := by
  funext ω
  simp [compensatedExp]

omit [IsProbabilityMeasure P] in
theorem compensatedExp_succ (ω : Ω) :
    compensatedExp ℱ P X t g (n + 1) ω =
      compensatedExp ℱ P X t g n ω * Real.exp (t * X n ω - g * P[X n | ℱ n] ω) := by
  simp only [compensatedExp, sum_range_succ, Real.exp_add]

omit [IsProbabilityMeasure P] in
theorem compensatedExp_stronglyMeasurable
    (hX : ∀ i < n, StronglyMeasurable[ℱ (i + 1)] (X i)) :
    StronglyMeasurable[ℱ n] (compensatedExp ℱ P X t g n) := by
  apply Real.continuous_exp.comp_stronglyMeasurable
  have hs : StronglyMeasurable[ℱ n]
      (∑ i ∈ range n, fun ω => t * X i ω - g * P[X i | ℱ i] ω) := by
    apply Finset.stronglyMeasurable_sum
    intro i hi
    have hin : i < n := mem_range.mp hi
    exact (((hX i hin).mono (ℱ.mono (by omega))).const_mul t).sub
      ((stronglyMeasurable_condExp.mono (ℱ.mono (by omega : i ≤ n))).const_mul g)
  convert hs using 1
  funext ω
  simp only [Finset.sum_apply]

omit [IsProbabilityMeasure P] in
theorem compensatedExp_bound
    (hXC : ∀ i < n, ∀ᵐ ω ∂P, 0 ≤ X i ω ∧ X i ω ≤ C)
    (ht : 0 ≤ t) (hg : 0 ≤ g) :
    ∀ᵐ ω ∂P, ‖compensatedExp ℱ P X t g n ω‖ ≤ Real.exp (n * (t * C)) := by
  have hi : ∀ i, ∀ᵐ ω ∂P, i < n → t * X i ω - g * P[X i | ℱ i] ω ≤ t * C := by
    intro i
    by_cases hin : i < n
    · have hY : 0 ≤ᵐ[P] P[X i | ℱ i] :=
        condExp_nonneg ((hXC i hin).mono fun _ h => h.1)
      filter_upwards [hXC i hin, hY] with ω hx hy
      intro _
      exact (sub_le_self _ (mul_nonneg hg hy)).trans (mul_le_mul_of_nonneg_left hx.2 ht)
    · exact ae_of_all _ fun _ h => (hin h).elim
  filter_upwards [ae_all_iff.mpr hi] with ω hω
  simp only [compensatedExp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ ∑ _i ∈ range n, t * C := sum_le_sum (fun i hi => hω i (mem_range.mp hi))
    _ = _ := by simp [nsmul_eq_mul]

theorem compensatedExp_integrable
    (hX : ∀ i < n, StronglyMeasurable[ℱ (i + 1)] (X i))
    (hXC : ∀ i < n, ∀ᵐ ω ∂P, 0 ≤ X i ω ∧ X i ω ≤ C)
    (ht : 0 ≤ t) (hg : 0 ≤ g) : Integrable (compensatedExp ℱ P X t g n) P :=
  Integrable.of_bound ((compensatedExp_stronglyMeasurable hX).mono (ℱ.le n)).aestronglyMeasurable
    _ (compensatedExp_bound hXC ht hg)

/-- The compensated exponential has expectation at most one at every finite
time. This is proved by the conditional one-step estimate, not assumed. -/
theorem integral_compensatedExp_le (ht : 0 ≤ t) (htC : t * C < 2) (n : ℕ)
    (hX : ∀ i < n, StronglyMeasurable[ℱ (i + 1)] (X i))
    (hXC : ∀ i < n, ∀ᵐ ω ∂P, 0 ≤ X i ω ∧ X i ω ≤ C) :
    (∫ ω, compensatedExp ℱ P X t (2 * t / (2 - t * C)) n ω ∂P) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hXm : ∀ i < n, StronglyMeasurable[ℱ (i + 1)] (X i) :=
      fun i hi => hX i (by omega)
    have hXCm : ∀ i < n, ∀ᵐ ω ∂P, 0 ≤ X i ω ∧ X i ω ≤ C :=
      fun i hi => hXC i (by omega)
    have hg : 0 ≤ 2 * t / (2 - t * C) := by positivity
    calc
      _ = ∫ ω, compensatedExp ℱ P X t (2 * t / (2 - t * C)) n ω *
          Real.exp (t * X n ω - (2 * t / (2 - t * C)) * P[X n | ℱ n] ω) ∂P := by
        apply integral_congr_ae
        exact ae_of_all _ compensatedExp_succ
      _ ≤ ∫ ω, compensatedExp ℱ P X t (2 * t / (2 - t * C)) n ω ∂P :=
        integral_compensated_step (ℱ.le n) (compensatedExp_stronglyMeasurable hXm)
          (ae_of_all _ fun _ => (Real.exp_pos _).le)
          (compensatedExp_bound hXCm ht hg) ((hX n (by omega)).mono (ℱ.le (n + 1)))
          (hXC n (by omega)) ht htC
      _ ≤ 1 := ih hXm hXCm

end Arxiv2411_18291
