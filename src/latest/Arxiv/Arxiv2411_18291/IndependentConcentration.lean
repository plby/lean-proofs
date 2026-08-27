import Arxiv.Arxiv2411_18291.ExponentialBound
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Concentration for independent nonnegative bounded variables

The corrected form of Lemma 5.1(1): require `0 ≤ Xᵢ ≤ C`. The signed
statement is refuted in `ConcentrationCounterexample`; the user has authorized
this correction, with nonnegativity to be checked at each application.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

theorem exp_neg_le_quadratic {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  have hd (x : ℝ) : HasDerivAt
      (fun y : ℝ => 1 - y + y ^ 2 / 2 - Real.exp (-y))
      (-1 + x + Real.exp (-x)) x := by
    convert! (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).add
      (((hasDerivAt_id x).pow 2).div_const 2)).sub
      (((hasDerivAt_id x).neg).exp) using 1
    simp
  have hm := monotone_of_hasDerivAt_nonneg hd (fun y => by
    have h := Real.add_one_le_exp (-y)
    change (0 : ℝ) ≤ -1 + y + Real.exp (-y)
    linarith)
  have h := hm hx
  norm_num at h
  linarith

theorem exp_neg_mul_le_linear {x C t : ℝ} (hx : 0 ≤ x) (hxC : x ≤ C) (ht : 0 ≤ t) :
    Real.exp (-t * x) ≤ 1 + (-t + t ^ 2 * C / 2) * x := by
  have he := exp_neg_le_quadratic (mul_nonneg ht hx)
  have hs : x ^ 2 ≤ C * x := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg t)
  rw [← neg_mul] at he
  nlinarith

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable [IsProbabilityMeasure P] {X : Ω → ℝ} {C t g : ℝ}

theorem integrable_exp_mul_of_abs_bound (hX : Measurable X)
    (hXC : ∀ᵐ ω ∂P, |X ω| ≤ C) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * X ω)) P := by
  apply Integrable.of_bound ((hX.const_mul t).exp.aestronglyMeasurable) (Real.exp (|t| * C))
  filter_upwards [hXC] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    t * X ω ≤ |t * X ω| := le_abs_self _
    _ = |t| * |X ω| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hω (abs_nonneg _)

theorem mgf_le_exp_mean_of_linear (hX : Integrable X P)
    (he : Integrable (fun ω => Real.exp (t * X ω)) P)
    (hlin : ∀ᵐ ω ∂P, Real.exp (t * X ω) ≤ 1 + g * X ω) :
    mgf X P t ≤ Real.exp (g * ∫ ω, X ω ∂P) := by
  calc
    _ ≤ ∫ ω, 1 + g * X ω ∂P :=
      integral_mono_ae he ((integrable_const 1).add (hX.const_mul g)) hlin
    _ = 1 + g * ∫ ω, X ω ∂P := by
      rw [integral_add (integrable_const 1) (hX.const_mul g), integral_const_mul]
      simp
    _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp (g * ∫ ω, X ω ∂P)

theorem independent_mgf_le_of_linear {X : ι → Ω → ℝ} (s : Finset ι)
    (hX : ∀ i, Measurable (X i)) (hInd : iIndepFun X P)
    (hXi : ∀ i ∈ s, Integrable (X i) P)
    (he : ∀ i ∈ s, Integrable (fun ω => Real.exp (t * X i ω)) P)
    (hlin : ∀ i ∈ s, ∀ᵐ ω ∂P, Real.exp (t * X i ω) ≤ 1 + g * X i ω) :
    mgf (∑ i ∈ s, X i) P t ≤ Real.exp (g * ∫ ω, ∑ i ∈ s, X i ω ∂P) := by
  rw [hInd.mgf_sum hX]
  calc
    _ ≤ ∏ i ∈ s, Real.exp (g * ∫ ω, X i ω ∂P) := by
      apply prod_le_prod (fun _ _ => mgf_nonneg)
      intro i hi
      exact mgf_le_exp_mean_of_linear (hXi i hi) (he i hi) (hlin i hi)
    _ = Real.exp (∑ i ∈ s, g * ∫ ω, X i ω ∂P) := (Real.exp_sum _ _).symm
    _ = _ := by rw [← mul_sum, integral_finsetSum s hXi]

/-- Upper-tail concentration, with a stronger constant than Lemma 5.1(1). -/
theorem independent_nonnegative_upper_tail {X : ι → Ω → ℝ} {c μ : ℝ}
    (s : Finset ι) (hC : 0 < C) (hc : 0 < c)
    (hX : ∀ i, Measurable (X i)) (hInd : iIndepFun X P)
    (hXC : ∀ i ∈ s, ∀ᵐ ω ∂P, 0 ≤ X i ω ∧ X i ω ≤ C)
    (hμ : (∫ ω, ∑ i ∈ s, X i ω ∂P) = μ) :
    P.real {ω | (1 + c) * μ < ∑ i ∈ s, X i ω} ≤
      Real.exp (-(μ * c ^ 2 / ((2 + c) * C))) := by
  let t := c / ((1 + c) * C)
  let g := 2 * t / (2 - t * C)
  obtain ⟨ht, hg, htC, hpar⟩ := adaptive_chernoff_parameters hC hc
  change 0 < t at ht
  change 0 ≤ g at hg
  change t * C < 2 at htC
  change -t * (1 + c) + g = -(c ^ 2 / ((2 + c) * C)) at hpar
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
  rw [hμ] at hmgf
  have hmark := measure_ge_le_exp_mul_mgf ((1 + c) * μ) ht.le
    (hInd.integrable_exp_mul_sum hX he)
  calc
    _ ≤ P.real {ω | (1 + c) * μ ≤ (∑ i ∈ s, X i) ω} := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro ω hω
      change (1 + c) * μ < ∑ i ∈ s, X i ω at hω
      simpa only [Set.mem_ofPred_eq, Finset.sum_apply] using hω.le
    _ ≤ Real.exp (-t * ((1 + c) * μ)) * mgf (∑ i ∈ s, X i) P t := hmark
    _ ≤ Real.exp (-t * ((1 + c) * μ)) * Real.exp (g * μ) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      calc
        -t * ((1 + c) * μ) + g * μ = μ * (-t * (1 + c) + g) := by ring
        _ = _ := by rw [hpar]; ring

/-- Lower-tail concentration for independent nonnegative bounded variables. -/
theorem independent_nonnegative_lower_tail {X : ι → Ω → ℝ} {c μ : ℝ}
    (s : Finset ι) (hC : 0 < C) (hc : 0 ≤ c)
    (hX : ∀ i, Measurable (X i)) (hInd : iIndepFun X P)
    (hXC : ∀ i ∈ s, ∀ᵐ ω ∂P, 0 ≤ X i ω ∧ X i ω ≤ C)
    (hμ : (∫ ω, ∑ i ∈ s, X i ω ∂P) = μ) :
    P.real {ω | (∑ i ∈ s, X i ω) < (1 - c) * μ} ≤
      Real.exp (-(μ * c ^ 2 / (2 * C))) := by
  let t := c / C
  let g := -t + t ^ 2 * C / 2
  have ht : 0 ≤ t := div_nonneg hc hC.le
  have hAbs (i) (hi : i ∈ s) : ∀ᵐ ω ∂P, |X i ω| ≤ C := by
    filter_upwards [hXC i hi] with ω hω
    simpa only [abs_of_nonneg hω.1] using hω.2
  have hXi (i) (hi : i ∈ s) : Integrable (X i) P :=
    Integrable.of_bound (hX i).aestronglyMeasurable C (hAbs i hi)
  have he (i) (hi : i ∈ s) : Integrable (fun ω => Real.exp (-t * X i ω)) P :=
    integrable_exp_mul_of_abs_bound (hX i) (hAbs i hi) (-t)
  have hlin (i) (hi : i ∈ s) :
      ∀ᵐ ω ∂P, Real.exp (-t * X i ω) ≤ 1 + g * X i ω := by
    filter_upwards [hXC i hi] with ω hω
    exact exp_neg_mul_le_linear hω.1 hω.2 ht
  have hmgf := independent_mgf_le_of_linear s hX hInd hXi he hlin
  rw [hμ] at hmgf
  have hmark := measure_le_le_exp_mul_mgf ((1 - c) * μ) (neg_nonpos.mpr ht)
    (hInd.integrable_exp_mul_sum hX he)
  calc
    _ ≤ P.real {ω | (∑ i ∈ s, X i) ω ≤ (1 - c) * μ} := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro ω hω
      change (∑ i ∈ s, X i ω) < (1 - c) * μ at hω
      simpa only [Set.mem_ofPred_eq, Finset.sum_apply] using hω.le
    _ ≤ Real.exp (-(-t) * ((1 - c) * μ)) * mgf (∑ i ∈ s, X i) P (-t) := hmark
    _ ≤ Real.exp (-(-t) * ((1 - c) * μ)) * Real.exp (g * μ) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      dsimp only [t, g]
      field_simp
      ring

/-- Corrected Lemma 5.1(1). Nonnegativity is an additional hypothesis, not
an inferred consequence of the paper's bound on absolute values. -/
theorem pseudobin_part_one_nonneg {X : ι → Ω → ℝ} {c μ : ℝ}
    (s : Finset ι) (hC : 0 < C) (hc : 0 ≤ c)
    (hX : ∀ i, Measurable (X i)) (hInd : iIndepFun X P)
    (hXC : ∀ i ∈ s, ∀ᵐ ω ∂P, 0 ≤ X i ω ∧ X i ω ≤ C)
    (hμ : (∫ ω, ∑ i ∈ s, X i ω ∂P) = μ) :
    P.real {ω | |(∑ i ∈ s, X i ω) - μ| > c * μ} ≤
      2 * Real.exp (-(μ * c ^ 2 / (2 * (1 + 2 * c) * C))) := by
  obtain rfl | hcpos := hc.eq_or_lt
  · simpa using (measureReal_le_one (μ := P) (s :=
      {ω | |(∑ i ∈ s, X i ω) - μ| > (0 : ℝ) * μ})).trans
      (by norm_num : (1 : ℝ) ≤ 2)
  have hμ0 : 0 ≤ μ := by
    rw [← hμ]
    apply integral_nonneg_of_ae
    have hall : ∀ᵐ ω ∂P, ∀ i ∈ s, 0 ≤ X i ω :=
      (ae_ball_iff s.finite_toSet.countable).mpr
        (fun i hi => (hXC i hi).mono fun _ h => h.1)
    filter_upwards [hall] with ω hω
    exact sum_nonneg hω
  have hsub : {ω | |(∑ i ∈ s, X i ω) - μ| > c * μ} ⊆
      {ω | (1 + c) * μ < ∑ i ∈ s, X i ω} ∪
      {ω | (∑ i ∈ s, X i ω) < (1 - c) * μ} := by
    intro ω hω
    change c * μ < |(∑ i ∈ s, X i ω) - μ| at hω
    rcases lt_abs.mp hω with hω | hω
    · left
      change (1 + c) * μ < ∑ i ∈ s, X i ω
      linarith
    · right
      change (∑ i ∈ s, X i ω) < (1 - c) * μ
      linarith
  have hupper : -(μ * c ^ 2 / ((2 + c) * C)) ≤
      -(μ * c ^ 2 / (2 * (1 + 2 * c) * C)) := by
    apply neg_le_neg
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
  have hlower : -(μ * c ^ 2 / (2 * C)) ≤
      -(μ * c ^ 2 / (2 * (1 + 2 * c) * C)) := by
    apply neg_le_neg
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
  calc
    _ ≤ P.real ({ω | (1 + c) * μ < ∑ i ∈ s, X i ω} ∪
        {ω | (∑ i ∈ s, X i ω) < (1 - c) * μ}) := measureReal_mono hsub
    _ ≤ P.real {ω | (1 + c) * μ < ∑ i ∈ s, X i ω} +
        P.real {ω | (∑ i ∈ s, X i ω) < (1 - c) * μ} := measureReal_union_le _ _
    _ ≤ Real.exp (-(μ * c ^ 2 / ((2 + c) * C))) +
        Real.exp (-(μ * c ^ 2 / (2 * C))) :=
      add_le_add (independent_nonnegative_upper_tail s hC hcpos hX hInd hXC hμ)
        (independent_nonnegative_lower_tail s hC hc hX hInd hXC hμ)
    _ ≤ _ := by
      have hu := Real.exp_le_exp.mpr hupper
      have hl := Real.exp_le_exp.mpr hlower
      linarith

end Arxiv2411_18291
