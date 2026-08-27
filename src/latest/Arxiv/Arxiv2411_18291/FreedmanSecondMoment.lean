import Arxiv.Arxiv2411_18291.VarianceExponentialProcess
import Arxiv.Arxiv2411_18291.SupermartingaleMaximal

/-!
# Freedman's inequality with a predictable second-moment budget

The exponential maximal inequality gives a bound uniform over a finite
time interval. The rational exponential estimate yields denominator
`2*v+a*b`, which is slightly stronger than the paper's denominator.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ}
variable {a b v t : ℝ}

theorem freedman_secondMoment_exponential_bound (hb : 0 ≤ b)
    (hX : ∀ i, StronglyMeasurable[ℱ (i + 1)] (X i))
    (hXb : ∀ i, ∀ᵐ ω ∂P, |X i ω| ≤ b) (hmean : ∀ i, P[X i | ℱ i] ≤ᵐ[P] 0)
    (ht : 0 ≤ t) (htb : t * b < 2) (n : ℕ) :
    P.real {ω | ∃ j ≤ n, a ≤ ∑ i ∈ range j, X i ω ∧
      (∑ i ∈ range j, P[fun ω => (X i ω) ^ 2 | ℱ i] ω) ≤ v} ≤
      Real.exp (-t * a + (t ^ 2 / (2 - t * b)) * v) := by
  let g := t ^ 2 / (2 - t * b)
  have hg : 0 ≤ g := by dsimp [g]; positivity
  let M := varianceCompensatedExp ℱ P X t g
  have hM : Supermartingale M ℱ P :=
    varianceCompensatedExp_supermartingale hb hX hXb hmean ht htb
  have hM0 : ∀ i, 0 ≤ᵐ[P] M i := fun _ => ae_of_all _ fun _ => (Real.exp_pos _).le
  have hsub : {ω | ∃ j ≤ n, a ≤ ∑ i ∈ range j, X i ω ∧
      (∑ i ∈ range j, P[fun ω => (X i ω) ^ 2 | ℱ i] ω) ≤ v} ⊆
      {ω | ∃ j ≤ n, Real.exp (t * a - g * v) ≤ M j ω} := by
    rintro ω ⟨j, hj, ha, hv⟩
    refine ⟨j, hj, Real.exp_le_exp.mpr ?_⟩
    rw [sum_sub_distrib, ← mul_sum, ← mul_sum]
    exact sub_le_sub (mul_le_mul_of_nonneg_left ha ht)
      (mul_le_mul_of_nonneg_left hv hg)
  calc
    _ ≤ P.real {ω | ∃ j ≤ n, Real.exp (t * a - g * v) ≤ M j ω} := measureReal_mono hsub
    _ ≤ (∫ ω, M 0 ω ∂P) / Real.exp (t * a - g * v) :=
      supermartingale_maximal_probability_le hM hM0 (Real.exp_pos _) n
    _ = Real.exp (-t * a + g * v) := by
      simp only [M, varianceCompensatedExp_zero, integral_const, probReal_univ, smul_eq_mul,
        one_mul, one_div, ← Real.exp_neg]
      congr 1
      ring

theorem freedman_secondMoment_bound (ha : 0 < a) (hb : 0 < b) (hv : 0 ≤ v)
    (hX : ∀ i, StronglyMeasurable[ℱ (i + 1)] (X i))
    (hXb : ∀ i, ∀ᵐ ω ∂P, |X i ω| ≤ b) (hmean : ∀ i, P[X i | ℱ i] ≤ᵐ[P] 0)
    (n : ℕ) :
    P.real {ω | ∃ j ≤ n, a ≤ ∑ i ∈ range j, X i ω ∧
      (∑ i ∈ range j, P[fun ω => (X i ω) ^ 2 | ℱ i] ω) ≤ v} ≤
      Real.exp (-(a ^ 2 / (2 * v + a * b))) := by
  obtain ⟨ht, _, htb, heq, _⟩ := variance_chernoff_parameters ha hb hv
  have h := freedman_secondMoment_exponential_bound (a := a) (v := v)
    hb.le hX hXb hmean ht.le htb n
  rw [heq] at h
  exact h

theorem freedman_secondMoment_paper_bound (ha : 0 < a) (hb : 0 < b) (hv : 0 ≤ v)
    (hX : ∀ i, StronglyMeasurable[ℱ (i + 1)] (X i))
    (hXb : ∀ i, ∀ᵐ ω ∂P, |X i ω| ≤ b) (hmean : ∀ i, P[X i | ℱ i] ≤ᵐ[P] 0)
    (n : ℕ) :
    P.real {ω | ∃ j ≤ n, a ≤ ∑ i ∈ range j, X i ω ∧
      (∑ i ∈ range j, P[fun ω => (X i ω) ^ 2 | ℱ i] ω) ≤ v} ≤
      Real.exp (-(a ^ 2 / (2 * (v + a * b)))) := by
  exact (freedman_secondMoment_bound ha hb hv hX hXb hmean n).trans
    (Real.exp_le_exp.mpr (variance_chernoff_parameters ha hb hv).2.2.2.2)

end Arxiv2411_18291
