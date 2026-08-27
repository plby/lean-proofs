import Arxiv.Arxiv2411_18291.IndependentConcentration

/-!
# An upper-tail bound using only an upper bound on the mean

Independent nonnegative summands bounded by `C` exceed twice an upper bound
`B` on their total expectation with probability at most `exp(-B/(3*C))`.
This form is useful when balancing group representatives, whose exact
expected degree varies with the face being tested.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable [IsProbabilityMeasure P] {X : ι → Ω → ℝ} {C B : ℝ}

theorem independent_nonnegative_upper_tail_of_mean_le (s : Finset ι) (hC : 0 < C)
    (hX : ∀ i, Measurable (X i)) (hInd : iIndepFun X P)
    (hXC : ∀ i ∈ s, ∀ᵐ ω ∂P, 0 ≤ X i ω ∧ X i ω ≤ C)
    (hB : (∫ ω, ∑ i ∈ s, X i ω ∂P) ≤ B) :
    P.real {ω | 2 * B < ∑ i ∈ s, X i ω} ≤ Real.exp (-(B / (3 * C))) := by
  let t := (1 : ℝ) / ((1 + 1) * C)
  let g := 2 * t / (2 - t * C)
  obtain ⟨ht, hg, htC, hpar⟩ := adaptive_chernoff_parameters hC (by norm_num : (0 : ℝ) < 1)
  change 0 < t at ht
  change 0 ≤ g at hg
  change t * C < 2 at htC
  change -t * (1 + 1) + g = -(1 ^ 2 / ((2 + 1) * C)) at hpar
  have hAbs (i) (hi : i ∈ s) : ∀ᵐ ω ∂P, |X i ω| ≤ C := by
    filter_upwards [hXC i hi] with ω hω
    simpa only [abs_of_nonneg hω.1] using hω.2
  have hXi (i) (hi : i ∈ s) : Integrable (X i) P :=
    Integrable.of_bound (hX i).aestronglyMeasurable C (hAbs i hi)
  have he (i) (hi : i ∈ s) : Integrable (fun ω => Real.exp (t * X i ω)) P :=
    integrable_exp_mul_of_abs_bound (hX i) (hAbs i hi) t
  have hlin (i) (hi : i ∈ s) :
      ∀ᵐ ω ∂P, Real.exp (t * X i ω) ≤ 1 + g * X i ω := by
    filter_upwards [hXC i hi] with ω hω
    exact exp_mul_le_linear hω.1 hω.2 ht.le htC
  have hmgf := independent_mgf_le_of_linear s hX hInd hXi he hlin
  have hmgfB : mgf (∑ i ∈ s, X i) P t ≤ Real.exp (g * B) :=
    hmgf.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hB hg))
  have hmark := measure_ge_le_exp_mul_mgf (2 * B) ht.le
    (hInd.integrable_exp_mul_sum hX he)
  calc
    _ ≤ P.real {ω | 2 * B ≤ (∑ i ∈ s, X i) ω} := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro ω hω
      change 2 * B < ∑ i ∈ s, X i ω at hω
      simpa only [Set.mem_ofPred_eq, Finset.sum_apply] using hω.le
    _ ≤ Real.exp (-t * (2 * B)) * mgf (∑ i ∈ s, X i) P t := hmark
    _ ≤ Real.exp (-t * (2 * B)) * Real.exp (g * B) :=
      mul_le_mul_of_nonneg_left hmgfB (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      calc
        -t * (2 * B) + g * B = B * (-t * (1 + 1) + g) := by ring
        _ = _ := by rw [hpar]; ring

end Arxiv2411_18291
