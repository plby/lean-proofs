import Arxiv.Arxiv2411_18291.ConditionalVarianceCompensation
import Mathlib.Probability.Martingale.Basic

/-! # The exponential supermartingale with second-moment compensation -/

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

def varianceCompensatedExp (ℱ : Filtration ℕ mΩ) (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (t g : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp (∑ i ∈ range n, (t * X i ω - g * P[fun ω => (X i ω) ^ 2 | ℱ i] ω))

variable {ℱ : Filtration ℕ mΩ} {P : Measure Ω} {X : ℕ → Ω → ℝ}
variable {t g b : ℝ} {n : ℕ}

@[simp] theorem varianceCompensatedExp_zero :
    varianceCompensatedExp ℱ P X t g 0 = fun _ => 1 := by
  funext ω
  simp [varianceCompensatedExp]

theorem varianceCompensatedExp_succ (ω : Ω) :
    varianceCompensatedExp ℱ P X t g (n + 1) ω =
      varianceCompensatedExp ℱ P X t g n ω *
        Real.exp (t * X n ω - g * P[fun ω => (X n ω) ^ 2 | ℱ n] ω) := by
  simp only [varianceCompensatedExp, sum_range_succ, Real.exp_add]

theorem varianceCompensatedExp_stronglyMeasurable
    (hX : ∀ i < n, StronglyMeasurable[ℱ (i + 1)] (X i)) :
    StronglyMeasurable[ℱ n] (varianceCompensatedExp ℱ P X t g n) := by
  apply Real.continuous_exp.comp_stronglyMeasurable
  have hs : StronglyMeasurable[ℱ n]
      (∑ i ∈ range n, fun ω => t * X i ω - g * P[fun ω => (X i ω) ^ 2 | ℱ i] ω) := by
    apply Finset.stronglyMeasurable_sum
    intro i hi
    have hin : i < n := mem_range.mp hi
    exact (((hX i hin).mono (ℱ.mono (by omega))).const_mul t).sub
      ((stronglyMeasurable_condExp.mono (ℱ.mono (by omega : i ≤ n))).const_mul g)
  convert hs using 1
  funext ω
  simp only [Finset.sum_apply]

theorem varianceCompensatedExp_bound
    (hXb : ∀ i < n, ∀ᵐ ω ∂P, |X i ω| ≤ b) (ht : 0 ≤ t) (hg : 0 ≤ g) :
    ∀ᵐ ω ∂P, ‖varianceCompensatedExp ℱ P X t g n ω‖ ≤ Real.exp (n * (t * b)) := by
  have hi : ∀ i, ∀ᵐ ω ∂P, i < n →
      t * X i ω - g * P[fun ω => (X i ω) ^ 2 | ℱ i] ω ≤ t * b := by
    intro i
    by_cases hin : i < n
    · have hQ : 0 ≤ᵐ[P] P[fun ω => (X i ω) ^ 2 | ℱ i] :=
        condExp_nonneg (ae_of_all _ fun ω => sq_nonneg (X i ω))
      filter_upwards [hXb i hin, hQ] with ω hx hq
      intro _
      exact (sub_le_self _ (mul_nonneg hg hq)).trans
        (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hx) ht)
    · exact ae_of_all _ fun _ h => (hin h).elim
  filter_upwards [ae_all_iff.mpr hi] with ω hω
  simp only [varianceCompensatedExp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ ∑ _i ∈ range n, t * b := sum_le_sum (fun i hi => hω i (mem_range.mp hi))
    _ = _ := by simp [nsmul_eq_mul]

variable [IsProbabilityMeasure P]

theorem varianceCompensatedExp_integrable
    (hX : ∀ i < n, StronglyMeasurable[ℱ (i + 1)] (X i))
    (hXb : ∀ i < n, ∀ᵐ ω ∂P, |X i ω| ≤ b) (ht : 0 ≤ t) (hg : 0 ≤ g) :
    Integrable (varianceCompensatedExp ℱ P X t g n) P :=
  Integrable.of_bound
    ((varianceCompensatedExp_stronglyMeasurable hX).mono (ℱ.le n)).aestronglyMeasurable
    _ (varianceCompensatedExp_bound hXb ht hg)

theorem varianceCompensatedExp_supermartingale (hb : 0 ≤ b)
    (hX : ∀ i, StronglyMeasurable[ℱ (i + 1)] (X i))
    (hXb : ∀ i, ∀ᵐ ω ∂P, |X i ω| ≤ b) (hmean : ∀ i, P[X i | ℱ i] ≤ᵐ[P] 0)
    (ht : 0 ≤ t) (htb : t * b < 2) :
    Supermartingale (varianceCompensatedExp ℱ P X t (t ^ 2 / (2 - t * b))) ℱ P := by
  have hg : 0 ≤ t ^ 2 / (2 - t * b) := by positivity
  apply supermartingale_nat
    (fun n => varianceCompensatedExp_stronglyMeasurable (fun i _ => hX i))
    (fun n => varianceCompensatedExp_integrable (fun i _ => hX i) (fun i _ => hXb i) ht hg)
  intro n
  have heq : varianceCompensatedExp ℱ P X t (t ^ 2 / (2 - t * b)) (n + 1) =
      fun ω => varianceCompensatedExp ℱ P X t (t ^ 2 / (2 - t * b)) n ω *
        Real.exp (t * X n ω -
          (t ^ 2 / (2 - t * b)) * P[fun ω => (X n ω) ^ 2 | ℱ n] ω) :=
    funext varianceCompensatedExp_succ
  rw [heq]
  exact condExp_variance_compensated_step (ℱ.le n) hb
    (varianceCompensatedExp_stronglyMeasurable (fun i _ => hX i))
    (ae_of_all _ fun _ => (Real.exp_pos _).le)
    (varianceCompensatedExp_bound (fun i _ => hXb i) ht hg)
    ((hX n).mono (ℱ.le (n + 1))) (hXb n) (hmean n) ht htb

end Arxiv2411_18291
