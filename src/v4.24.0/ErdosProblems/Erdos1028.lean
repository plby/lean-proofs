/-

This is a Lean formalization of a solution to Erdős Problem 1028.
https://www.erdosproblems.com/forum/thread/1028

The original proof was found by: Paul Erdős & Joel Spencer

[Er63d] Erdős, P\'al, On combinatorial questions connected with a
theorem of {R}amsey and van der {W}aerden. Mat. Lapok (1963), 29--37.

[ErSp71] Erdős, P. and Spencer, J., Imbalances in
{$k$}-colorations. Networks (1971/72), 379--385.


A proof of ChatGPT's choice was auto-formalized by Aristotle (from
Harmonic).  The final theorem statement was written by Aristotle.


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/


/-
We have formalized the definition of H(n) and proved that H(n) = Θ(n^(3/2)).
This involved proving Hoeffding's inequality for Rademacher sums, a Paley-Zygmund consequence for the first absolute moment of Rademacher sums, and relating bilinear forms to rectangle sums and induced sums.
The main results are `thm_upper` giving the upper bound O(n^(3/2)) and `thm_lower` giving the lower bound Ω(n^(3/2)), combined in `erdos_1028`.
-/

import Mathlib

namespace Erdos1028

set_option linter.mathlibStandardSet false

open scoped Classical

set_option maxHeartbeats 0

open Nat Real ENNReal
open Finset Sym2
open MeasureTheory ProbabilityTheory
open BigOperators
open Matrix

/-
Define the induced sum S_f(X) as the sum of f({i,j}) for all distinct i,j in X.
-/
def inducedSum (n : ℕ) (f : Sym2 (Fin n) → ℤ) (X : Finset (Fin n)) : ℤ :=
  ∑ e ∈ X.sym2.filter (fun e => ¬e.IsDiag), f e

/-
Define H(n) as the minimum over all colorings of the maximum induced sum.
-/
def coloringToInt {n : ℕ} (c : Sym2 (Fin n) → Bool) (e : Sym2 (Fin n)) : ℤ :=
  if c e then 1 else -1

noncomputable def H (n : ℕ) : ℤ :=
  let colorings := (Finset.univ : Finset (Sym2 (Fin n) → Bool))
  let subsets := (Finset.univ : Finset (Finset (Fin n)))
  let max_induced (c : Sym2 (Fin n) → Bool) : ℤ :=
    subsets.image (fun X => abs (inducedSum n (coloringToInt c) X)) |>.max' (by
    -- The image of the function is nonempty because it contains the absolute value of the induced sum for each subset.
    simp [subsets])
  colorings.image max_induced |>.min' (by
  bound)

/-
Define a Rademacher random variable.
-/
def IsRademacher {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) : Prop :=
  Measurable X ∧ P {ω | X ω = 1} = (1 : ℝ≥0∞) / 2 ∧ P {ω | X ω = -1} = (1 : ℝ≥0∞) / 2

/-
The moment generating function of a Rademacher variable is bounded by $\exp(t^2/2)$.
-/
lemma rademacher_mgf_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (h_rad : IsRademacher P X) (t : ℝ) :
    ∫ ω, exp (t * X ω) ∂P ≤ exp (t^2 / 2) := by
  obtain ⟨ hX₁, hX₂, hX₃ ⟩ := h_rad;
  -- Since $X$ takes values $\pm 1$ with probability $1/2$, we can split the integral into two parts:
  have h_split : ∫ ω, Real.exp (t * X ω) ∂P = (∫ ω in {ω | X ω = 1}, Real.exp (t) ∂P) + (∫ ω in {ω | X ω = -1}, Real.exp (-t) ∂P) := by
    rw [ ← MeasureTheory.integral_indicator, ← MeasureTheory.integral_indicator ];
    · rw [ ← MeasureTheory.integral_add ];
      · have h_split : ∀ᵐ ω ∂P, X ω = 1 ∨ X ω = -1 := by
          have h_split : P {ω | X ω ≠ 1 ∧ X ω ≠ -1} = 0 := by
            have h_ae : P {ω | X ω = 1 ∨ X ω = -1} = 1 := by
              rw [ show { ω | X ω = 1 ∨ X ω = -1 } = { ω | X ω = 1 } ∪ { ω | X ω = -1 } by rfl, MeasureTheory.measure_union ];
              · rw [ hX₂, hX₃ ];
                rw [ ENNReal.div_add_div_same, ENNReal.div_eq_one_iff ] <;> norm_num;
              · exact Set.disjoint_left.mpr fun ω hω₁ hω₂ => by linarith [ Set.mem_setOf.mp hω₁, Set.mem_setOf.mp hω₂ ] ;
              · exact hX₁ ( MeasurableSingletonClass.measurableSet_singleton _ );
            have h_ae : P {ω | X ω ≠ 1 ∧ X ω ≠ -1} = P Set.univ - P {ω | X ω = 1 ∨ X ω = -1} := by
              rw [ ← MeasureTheory.measure_diff ];
              · exact congr_arg _ ( by ext; aesop );
              · exact Set.subset_univ _;
              · exact MeasurableSet.nullMeasurableSet ( by exact MeasurableSet.union ( hX₁ ( MeasurableSingletonClass.measurableSet_singleton _ ) ) ( hX₁ ( MeasurableSingletonClass.measurableSet_singleton _ ) ) );
              · exact ne_of_lt ( MeasureTheory.measure_lt_top _ _ );
            aesop;
          filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp h_split ] with ω hω using by contrapose! hω; tauto;
        refine' MeasureTheory.integral_congr_ae _;
        filter_upwards [ h_split ] with ω hω ; rcases hω with ( hω | hω ) <;> simp +decide [ hω ];
        · norm_num;
        · norm_num;
      · rw [ MeasureTheory.integrable_indicator_iff ];
        · norm_num;
        · exact hX₁ ( MeasurableSingletonClass.measurableSet_singleton _ );
      · rw [ MeasureTheory.integrable_indicator_iff ] <;> norm_num;
        exact measurableSet_eq_fun hX₁ measurable_const |> MeasurableSet.mem;
    · exact hX₁ ( MeasurableSingletonClass.measurableSet_singleton _ );
    · exact hX₁ ( MeasurableSingletonClass.measurableSet_singleton _ );
  simp_all +decide [ MeasureTheory.measureReal_def ];
  -- Using the inequality $\cosh(t) \leq \exp(t^2/2)$, we can conclude the proof.
  have h_cosh : Real.cosh t ≤ Real.exp (t^2 / 2) := by
    exact cosh_le_exp_half_sq t;
  convert h_cosh using 1 ; rw [ Real.cosh_eq ] ; ring

/-
The expectation of the product of exponentials of independent Rademacher variables is the product of their expectations.
-/
lemma expectation_prod_exp_rademacher {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {M : ℕ} (ξ : Fin M → Ω → ℝ)
    (h_indep : iIndepFun ξ P)
    (h_rad : ∀ i, IsRademacher P (ξ i))
    (t : ℝ) :
    ∫ ω, ∏ i, exp (t * ξ i ω) ∂P = ∏ i, ∫ ω, exp (t * ξ i ω) ∂P := by
  -- Since the Rademacher variables are independent, the exponential of each random variable is also independent.
  have h_exp_indep : ProbabilityTheory.iIndepFun (fun i => fun ω => Real.exp (t * ξ i ω)) P := by
    rw [ ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul ] at *;
    intro S sets hsets; convert h_indep S _ using 1;
    any_goals intro i hi; exact MeasurableSet.preimage ( hsets i hi ) ( show Measurable fun x => Real.exp ( t * x ) from Measurable.exp ( measurable_const.mul measurable_id' ) );
    · simp +decide [ Set.preimage ];
    · rfl;
  convert h_exp_indep.integral_prod_eq_prod_integral _;
  · (expose_names; exact Eq.symm (Fintype.prod_apply x fun c ω => rexp (t * ξ c ω)));
  · intro i;
    have := h_rad i;
    exact Real.continuous_exp.comp_aestronglyMeasurable ( this.1.const_mul t |> Measurable.aestronglyMeasurable )

/-
One-sided Hoeffding inequality for Rademacher sums.
-/
theorem hoeffding_rademacher_sum_one_sided {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {M : ℕ} (ξ : Fin M → Ω → ℝ)
    (h_indep : iIndepFun ξ P)
    (h_rad : ∀ i, IsRademacher P (ξ i))
    (t : ℝ) (ht : t ≥ 0) :
    P {ω | ∑ i, ξ i ω ≥ t} ≤ ENNReal.ofReal (Real.exp (- t^2 / (2 * M))) := by
  -- For any $\lambda > 0$, by Markov's inequality,
  have h_markov : ∀ lambda > 0, (P {ω | ∑ i, ξ i ω ≥ t}) ≤ ENNReal.ofReal (Real.exp (-lambda * t) * ∫ ω, Real.exp (lambda * ∑ i, ξ i ω) ∂P) := by
    intro lambda hlambda_pos
    have h_markov : (∫ ω in {ω | ∑ i, ξ i ω ≥ t}, 1 ∂P) ≤ (∫ ω, Real.exp (lambda * (∑ i, ξ i ω - t)) ∂P) := by
      rw [ MeasureTheory.integral_eq_lintegral_of_nonneg_ae ];
      · rw [ MeasureTheory.integral_eq_lintegral_of_nonneg_ae ];
        · rw [ ← MeasureTheory.lintegral_indicator ];
          · refine' ENNReal.toReal_mono _ _;
            · refine' ne_of_lt ( MeasureTheory.Integrable.lintegral_lt_top _ );
              -- Since $\xi_i$ are Rademacher variables, we have $|\xi_i| \leq 1$ almost surely.
              have h_abs : ∀ i, ∀ᵐ ω ∂P, |ξ i ω| ≤ 1 := by
                intro i
                have h_abs_i : ∀ᵐ ω ∂P, ξ i ω = 1 ∨ ξ i ω = -1 := by
                  have := h_rad i;
                  have h_abs_i : P {ω | ξ i ω ≠ 1 ∧ ξ i ω ≠ -1} = 0 := by
                    have h_abs : P {ω | ξ i ω = 1} + P {ω | ξ i ω = -1} = 1 := by
                      rw [ this.2.1, this.2.2 ];
                      rw [ ENNReal.div_add_div_same, ENNReal.div_eq_one_iff ] <;> norm_num;
                    have h_abs : P {ω | ξ i ω = 1 ∨ ξ i ω = -1} = 1 := by
                      rw [ ← h_abs, ← MeasureTheory.measure_union ];
                      · rfl;
                      · exact Set.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Set.mem_setOf.mp hx₁, Set.mem_setOf.mp hx₂ ] ;
                      · exact this.1 ( MeasurableSingletonClass.measurableSet_singleton _ );
                    have h_abs : P {ω | ξ i ω ≠ 1 ∧ ξ i ω ≠ -1} = P Set.univ - P {ω | ξ i ω = 1 ∨ ξ i ω = -1} := by
                      rw [ ← MeasureTheory.measure_diff ] <;> norm_num [ Set.compl_setOf ];
                      · exact congr_arg _ ( by ext; simp +decide [ not_or ] );
                      · exact MeasurableSet.nullMeasurableSet ( by exact MeasurableSet.union ( this.1 ( MeasurableSingletonClass.measurableSet_singleton _ ) ) ( this.1 ( MeasurableSingletonClass.measurableSet_singleton _ ) ) );
                    aesop;
                  filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp h_abs_i ] with ω hω using Classical.or_iff_not_imp_left.2 fun h => Classical.not_not.1 fun h' => hω ⟨ h, h' ⟩;
                filter_upwards [ h_abs_i ] with ω hω using by rcases hω with ( hω | hω ) <;> norm_num [ hω ] ;
              refine' MeasureTheory.Integrable.mono' _ _ _;
              refine' fun ω => Real.exp ( lambda * ( M + |t| ) );
              · norm_num;
              · refine' Measurable.aestronglyMeasurable _;
                have h_measurable : ∀ i, Measurable (ξ i) := by
                  exact fun i => ( h_rad i ).1;
                exact Measurable.exp ( Measurable.mul measurable_const ( Measurable.sub ( Finset.measurable_sum _ fun i _ => h_measurable i ) measurable_const ) );
              · filter_upwards [ MeasureTheory.ae_all_iff.2 h_abs ] with ω hω using by simpa using Real.exp_le_exp.2 ( mul_le_mul_of_nonneg_left ( show ∑ i, ξ i ω - t ≤ M + |t| by cases abs_cases t <;> linarith [ show ∑ i, ξ i ω ≤ M by exact le_trans ( Finset.sum_le_sum fun i _ => le_of_abs_le ( hω i ) ) ( by norm_num ) ] ) hlambda_pos.le ) ;
            · refine' MeasureTheory.lintegral_mono fun ω => _;
              rw [ Set.indicator_apply ] ; aesop;
          · have h_measurable : ∀ i, Measurable (ξ i) := by
              exact fun i => ( h_rad i ).1;
            exact measurableSet_le measurable_const ( Finset.measurable_sum _ fun i _ => h_measurable i );
        · exact Filter.Eventually.of_forall fun ω => Real.exp_nonneg _;
        · have h_measurable : ∀ i, MeasureTheory.AEStronglyMeasurable (ξ i) P := by
            exact fun i => ( h_rad i ).1.aestronglyMeasurable;
          fun_prop;
      · exact Filter.Eventually.of_forall fun ω => zero_le_one;
      · exact MeasureTheory.aestronglyMeasurable_const;
    rw [ ← MeasureTheory.integral_const_mul ];
    convert ENNReal.ofReal_le_ofReal h_markov using 1;
    · aesop;
    · exact congr_arg _ ( by congr; ext; rw [ ← Real.exp_add ] ; ring_nf );
  by_cases hM : M = 0 <;> simp_all +decide;
  · exact le_trans ( MeasureTheory.measure_mono ( Set.subset_univ _ ) ) ( by simp +decide );
  · -- Using independence and the Rademacher MGF bound:
    have h_exp_bound : ∀ lambda > 0, ∫ ω, Real.exp (lambda * ∑ i, ξ i ω) ∂P ≤ Real.exp (M * lambda^2 / 2) := by
      -- Using the independence of the Rademacher variables and the bound on their moment generating functions, we have:
      have h_prod_exp_bound : ∀ lambda > 0, ∫ ω, ∏ i, Real.exp (lambda * ξ i ω) ∂P ≤ ∏ i : Fin M, Real.exp (lambda^2 / 2) := by
        intro lambda hlambda_pos
        have h_prod_exp_bound : ∫ ω, ∏ i, Real.exp (lambda * ξ i ω) ∂P = ∏ i, ∫ ω, Real.exp (lambda * ξ i ω) ∂P := by
          exact expectation_prod_exp_rademacher ξ h_indep h_rad lambda;
        exact h_prod_exp_bound.symm ▸ Finset.prod_le_prod ( fun _ _ => MeasureTheory.integral_nonneg fun _ => Real.exp_nonneg _ ) fun _ _ => rademacher_mgf_bound ( h_rad _ ) _;
      simp_all +decide [ ← Real.exp_sum, mul_div_assoc, Finset.mul_sum _ _ _ ];
      simpa only [ ← Real.exp_nat_mul, mul_comm ] using h_prod_exp_bound;
    by_cases ht : t = 0 <;> simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
    · exact le_trans ( MeasureTheory.measure_mono ( Set.subset_univ _ ) ) ( by simp +decide );
    · refine' le_trans ( h_markov ( t / M ) ( by positivity ) ) ( ENNReal.ofReal_le_ofReal _ );
      convert mul_le_mul_of_nonneg_left ( h_exp_bound ( t / M ) ( by positivity ) ) ( Real.exp_nonneg _ ) using 1 ; ring_nf;
      rw [ ← Real.exp_add ] ; norm_num [ sq, mul_assoc, hM ] ; ring

/-
Hoeffding's inequality for Rademacher sums.
-/
theorem hoeffding_rademacher_sum {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {M : ℕ} (ξ : Fin M → Ω → ℝ)
    (h_indep : iIndepFun ξ P)
    (h_rad : ∀ i, IsRademacher P (ξ i))
    (t : ℝ) (ht : t ≥ 0) :
    P {ω | |∑ i, ξ i ω| ≥ t} ≤ 2 * ENNReal.ofReal (Real.exp (- t^2 / (2 * M))) := by
  -- The event $\{|\sum \xi_i| \ge t\}$ is the union of $\{\sum \xi_i \ge t\}$ and $\{\sum \xi_i \le -t\}$.
  have h_union : {ω : Ω | |∑ i, ξ i ω| ≥ t} = {ω : Ω | ∑ i, ξ i ω ≥ t} ∪ {ω : Ω | ∑ i, ξ i ω ≤ -t} := by
    norm_num [ Set.ext_iff, abs_eq_max_neg, max_le_iff ];
    exact fun x => or_congr Iff.rfl ⟨ fun h => by linarith, fun h => by linarith ⟩;
  rw [ h_union, two_mul ];
  refine' le_trans ( MeasureTheory.measure_union_le _ _ ) _;
  -- Since $\xi_i$ are independent Rademacher variables, $-\xi_i$ are also independent Rademacher variables.
  have h_neg_rad : ∀ i, IsRademacher P (fun ω => -ξ i ω) := by
    intro i;
    obtain ⟨ h₁, h₂, h₃ ⟩ := h_rad i;
    refine' ⟨ _, _, _ ⟩;
    · exact h₁.neg;
    · simp_all +decide [ neg_eq_iff_eq_neg ];
    · simpa using h₂;
  -- Applying the one-sided Hoeffding inequality to $-\xi_i$, we get $P(\sum (-\xi_i) \ge t) \le \exp(-t^2/(2M))$.
  have h_neg : P {ω : Ω | ∑ i, -ξ i ω ≥ t} ≤ ENNReal.ofReal (Real.exp (- t^2 / (2 * M))) := by
    convert hoeffding_rademacher_sum_one_sided ( fun i ω => -ξ i ω ) _ _ t ht using 1;
    · infer_instance;
    · rw [ ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul ] at *;
      intro S sets hsets; specialize h_indep S ( fun i hi => hsets i hi |> MeasurableSet.preimage <| measurable_neg ) ; simp_all +decide [ Set.preimage ] ;
    · exact h_neg_rad;
  simp_all +decide [ Finset.sum_neg_distrib, le_neg ];
  refine' add_le_add _ h_neg;
  convert hoeffding_rademacher_sum_one_sided ξ h_indep h_rad t ht using 1

/-
Define the uniform measure on the space of colorings.
-/
noncomputable def coloringMeasure (n : ℕ) : Measure (Sym2 (Fin n) → Bool) :=
  (PMF.uniformOfFintype (Sym2 (Fin n) → Bool)).toMeasure

instance (n : ℕ) : IsProbabilityMeasure (coloringMeasure n) :=
  PMF.toMeasure.isProbabilityMeasure _

/-
The uniform measure on colorings is equal to the product measure of uniform measures on edges.
-/
noncomputable def coloringProductMeasure (n : ℕ) : Measure (Sym2 (Fin n) → Bool) :=
  Measure.pi (fun _ => (PMF.uniformOfFintype Bool).toMeasure)

lemma coloring_measure_eq_product (n : ℕ) :
    coloringMeasure n = coloringProductMeasure n := by
  unfold coloringMeasure coloringProductMeasure;
  rw [ MeasureTheory.Measure.pi_eq ];
  simp +decide
  intro s; erw [ Finset.sum_congr rfl fun x hx => by rw [ Set.indicator_apply ] ] ; simp +decide [ Finset.prod_add ] ;
  -- By definition of product measure, we can rewrite the sum as a product of sums.
  have h_prod_sum : ∑ x : Sym2 (Fin n) → Bool, (if ∀ i, x i ∈ s i then (2 ^ Fintype.card (Sym2 (Fin n)))⁻¹ else 0) = ∏ i : Sym2 (Fin n), (∑ x : Bool, (if x ∈ s i then (2 : ℝ≥0∞)⁻¹ else 0)) := by
    have h_prod_sum : ∀ (f : Sym2 (Fin n) → Bool → ℝ≥0∞), (∑ x : Sym2 (Fin n) → Bool, ∏ i : Sym2 (Fin n), f i (x i)) = ∏ i : Sym2 (Fin n), (∑ x : Bool, f i x) := by
      exact fun f => Eq.symm (Fintype.prod_sum f);
    convert h_prod_sum _ using 2;
    split_ifs <;> simp_all +decide [ Finset.prod_ite ];
    rw [ ENNReal.inv_pow ];
  convert h_prod_sum using 1;
  simp +decide
  rw [ Finset.prod_add ];
  simp +decide [ Set.indicator ]

/-
The edge values are independent under the product measure.
-/
lemma coloring_product_measure_independent (n : ℕ) :
    let Ω := Sym2 (Fin n) → Bool
    let P := coloringProductMeasure n
    let ξ (e : Sym2 (Fin n)) (ω : Ω) : ℝ := if ω e then 1 else -1
    iIndepFun ξ P := by
  -- The projection maps are independent under the product measure.
  have h_indep : ProbabilityTheory.iIndepFun (fun e : Sym2 (Fin n) => (fun ω : Sym2 (Fin n) → Bool => ω e)) (Measure.pi (fun _ : Sym2 (Fin n) => (PMF.uniformOfFintype Bool).toMeasure)) := by
    refine' ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul.mpr _;
    intro S sets hsets;
    -- The measure of the intersection of these sets is equal to the product of the measures of the individual sets because the product measure is defined as the Cartesian product of the measures on each component.
    have h_prod_measure : ∀ (S : Finset (Sym2 (Fin n))) (sets : Sym2 (Fin n) → Set Bool), (∀ i ∈ S, MeasurableSet (sets i)) → (MeasureTheory.Measure.pi fun (x : Sym2 (Fin n)) => (PMF.uniformOfFintype Bool).toMeasure) (⋂ i ∈ S, (fun (ω : Sym2 (Fin n) → Bool) => ω i) ⁻¹' sets i) = ∏ i ∈ S, (PMF.uniformOfFintype Bool).toMeasure (sets i) := by
      intros S sets hsets;
      have h_prod_measure : ∀ (S : Finset (Sym2 (Fin n))) (sets : Sym2 (Fin n) → Set Bool), (∀ i ∈ S, MeasurableSet (sets i)) → (MeasureTheory.Measure.pi fun (x : Sym2 (Fin n)) => (PMF.uniformOfFintype Bool).toMeasure) (⋂ i ∈ S, (fun (ω : Sym2 (Fin n) → Bool) => ω i) ⁻¹' sets i) = ∏ i ∈ S, (PMF.uniformOfFintype Bool).toMeasure (sets i) := by
        intros S sets hsets;
        induction' S using Finset.induction with i S hiS ih;
        · simp +decide
        · simp_all +decide [ Finset.prod_insert hiS, Set.preimage ];
          rw [ ← ih ];
          rw [ show { x : Sym2 ( Fin n ) → Bool | x i ∈ sets i } ∩ ⋂ x ∈ S, { x_1 : Sym2 ( Fin n ) → Bool | x_1 x ∈ sets x } = ( Set.pi Set.univ fun j => if j = i then sets i else if j ∈ S then sets j else Set.univ ) from ?_ ];
          · rw [ show ( ⋂ i ∈ S, { x : Sym2 ( Fin n ) → Bool | x i ∈ sets i } ) = Set.pi Set.univ fun j => if j ∈ S then sets j else Set.univ from ?_ ];
            · rw [ MeasureTheory.Measure.pi_pi ];
              rw [ Finset.prod_eq_mul_prod_diff_singleton ( Finset.mem_univ i ) ];
              rw [ MeasureTheory.Measure.pi_pi ];
              rw [ Finset.prod_eq_prod_diff_singleton_mul <| Finset.mem_univ i ];
              simp +decide [ hiS ];
              rw [ ENNReal.mul_inv_cancel ] <;> norm_num;
              exact congrArg _ ( Finset.prod_congr rfl fun x hx => by aesop );
            · ext; simp [Set.mem_pi];
              exact ⟨ fun h i => by by_cases hi : i ∈ S <;> simp +decide [ hi, h ], fun h i hi => by simpa [ hi ] using h i ⟩;
          · ext; simp [Set.mem_pi];
            grind;
      exact h_prod_measure S sets hsets;
    convert h_prod_measure S sets hsets using 1;
    refine' Finset.prod_congr rfl fun i hi => _;
    convert h_prod_measure { i } ( fun _ => sets i ) ( by aesop ) using 1;
    · simp +decide [ Set.preimage ];
    · norm_num;
  rw [ ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul ] at *;
  intro S sets hsets; convert h_indep S ( show ∀ i ∈ S, MeasurableSet ( fun x : Bool => ( if x = Bool.true then 1 else -1 ) ∈ sets i ) from fun i hi => ?_ ) using 1;
  exact trivial

/-
The edge values are Rademacher variables under the product measure.
-/
lemma coloring_product_measure_rademacher (n : ℕ) (e : Sym2 (Fin n)) :
    let Ω := Sym2 (Fin n) → Bool
    let P := coloringProductMeasure n
    let ξ (e : Sym2 (Fin n)) (ω : Ω) : ℝ := if ω e then 1 else -1
    IsRademacher P (ξ e) := by
  -- Show that the measure of {ω | ξ e ω = 1} is 1/2.
  have h_measure1 : coloringProductMeasure n {ω : Sym2 (Fin n) → Bool | (if ω e then 1 else -1) = 1} = 1 / 2 := by
    norm_num +zetaDelta at *;
    erw [ show { ω : Sym2 ( Fin n ) → Bool | ω e = Bool.true } = ( Set.pi Set.univ fun i => if i = e then { Bool.true } else Set.univ ) from ?_ ];
    · -- Apply the fact that the measure of a product set is the product of the measures of the individual sets.
      have h_prod : (coloringProductMeasure n) (Set.pi Set.univ fun i => if i = e then { Bool.true } else Set.univ) = ∏ i : Sym2 (Fin n), (PMF.uniformOfFintype Bool).toMeasure (if i = e then { Bool.true } else Set.univ) := by
        erw [ MeasureTheory.Measure.pi_pi ];
      rw [ h_prod, Finset.prod_eq_mul_prod_diff_singleton <| Finset.mem_univ e ];
      norm_num +zetaDelta at *;
      rw [ Finset.prod_congr rfl fun x hx => by aesop ] ; norm_num;
      rw [ ← two_mul, ENNReal.mul_inv_cancel ] <;> norm_num;
    · grind;
  refine' ⟨ _, _, _ ⟩;
  · exact Measurable.ite ( measurableSet_eq_fun ( measurable_pi_apply e ) measurable_const ) measurable_const measurable_const;
  · grind;
  · convert congr_arg ( fun x : ENNReal => 1 - x ) h_measure1 using 1 <;> norm_num [ Set.setOf_eq_eq_singleton ];
    rw [ eq_comm, ENNReal.sub_eq_of_eq_add ];
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.subset_univ _ ) ) ( by simp +decide [ coloringProductMeasure ] ) );
    · rw [ ← MeasureTheory.measure_union ] <;> norm_num [ Set.setOf_or ];
      · rw [ show { ω : Sym2 ( Fin n ) → Bool | ω e = Bool.false } ∪ { ω : Sym2 ( Fin n ) → Bool | ω e = Bool.true } = Set.univ by ext ω; by_cases h : ω e <;> aesop ] ; norm_num [ coloringProductMeasure ];
      · exact Set.disjoint_left.mpr fun x hx₁ hx₂ => by aesop;
      · exact measurableSet_eq_fun ( measurable_pi_apply e ) measurable_const |> MeasurableSet.mem

/-
The probability that the induced sum of a subset X exceeds t is bounded by Hoeffding's inequality.
-/
lemma prob_induced_sum_ge (n : ℕ) (X : Finset (Fin n)) (t : ℝ) (ht : t ≥ 0) :
    (coloringMeasure n) {c | |inducedSum n (coloringToInt c) X| ≥ t} ≤ 2 * ENNReal.ofReal (Real.exp (- t^2 / (2 * (X.card.choose 2)))) := by
  have := @hoeffding_rademacher_sum ( Sym2 ( Fin n ) → Bool );
  obtain ⟨M, e⟩ : ∃ M : ℕ, ∃ e : Fin M → Sym2 (Fin n), Function.Injective e ∧ Finset.image e Finset.univ = X.sym2.filter (fun e => ¬e.IsDiag) := by
    have h_finite : ∃ M : ℕ, ∃ e : Fin M → Sym2 (Fin n), Function.Injective e ∧ Finset.image e Finset.univ = X.sym2.filter (fun e => ¬e.IsDiag) := by
      have h_finite : ∃ s : Finset (Sym2 (Fin n)), s = X.sym2.filter (fun e => ¬e.IsDiag) ∧ s.card = s.card := by
        exact ⟨ _, rfl, rfl ⟩
      obtain ⟨ s, hs₁, hs₂ ⟩ := h_finite;
      use s.card;
      have h_finite : Nonempty (Fin s.card ≃ s) := by
        exact ⟨ Fintype.equivOfCardEq <| by simp +decide ⟩;
      obtain ⟨ e ⟩ := h_finite;
      use fun i => e i |>.1;
      exact ⟨ fun i j hij => e.injective <| Subtype.ext hij, by ext x; exact ⟨ fun hx => by obtain ⟨ i, _, rfl ⟩ := Finset.mem_image.mp hx; exact hs₁ ▸ Subtype.mem _, fun hx => by obtain ⟨ i, hi ⟩ := e.surjective ⟨ x, hs₁ ▸ hx ⟩ ; exact Finset.mem_image.mpr ⟨ i, Finset.mem_univ _, hi ▸ rfl ⟩ ⟩ ⟩;
    exact h_finite;
  obtain ⟨ e, he₁, he₂ ⟩ := e;
  -- Apply the Hoeffding's inequality to the sum of the Rademacher variables corresponding to the edges in $X$.
  have h_hoeffding : (coloringMeasure n) {c : Sym2 (Fin n) → Bool | |∑ i : Fin M, (if c (e i) then 1 else -1 : ℝ)| ≥ t} ≤ 2 * ENNReal.ofReal (Real.exp (-t^2 / (2 * M))) := by
    convert this ( fun i ω => if ω ( e i ) then 1 else -1 ) _ _ t ht using 1;
    · infer_instance;
    · have h_indep : iIndepFun (fun i ω => if ω (e i) then 1 else -1 : Fin M → (Sym2 (Fin n) → Bool) → ℝ) (coloringProductMeasure n) := by
        have h_indep : iIndepFun (fun e ω => if ω e then 1 else -1 : Sym2 (Fin n) → (Sym2 (Fin n) → Bool) → ℝ) (coloringProductMeasure n) := by
          exact coloring_product_measure_independent n
        rw [ ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul ] at *;
        intro S sets hsets; specialize h_indep ( Finset.image e S ) ; simp_all +decide
        use fun i => if h : ∃ j, e j = i then sets ( Classical.choose h ) else Set.univ;
        convert h_indep _ using 1;
        · congr! 1;
          ext; simp +decide [ he₁.eq_iff ] ;
        · rw [ Finset.prod_image ];
          · refine' Finset.prod_congr rfl fun i hi => _;
            simp +decide [ he₁.eq_iff];
          · exact he₁.injOn;
        · simp +zetaDelta at *;
          intro i hi; specialize hsets i hi; convert hsets using 1;
          exact congr_arg _ ( he₁ <| by have := Classical.choose_spec ( show ∃ j, e j = e i from ⟨ i, rfl ⟩ ) ; aesop );
      convert h_indep using 1;
      exact coloring_measure_eq_product n;
    · intro i; convert coloring_product_measure_rademacher n ( e i ) using 1;
      exact coloring_measure_eq_product n;
  convert h_hoeffding using 1;
  · have h_sum_eq : ∀ c : Sym2 (Fin n) → Bool, ∑ x ∈ X.sym2.filter (fun e => ¬e.IsDiag), (if c x then 1 else -1 : ℝ) = ∑ i : Fin M, (if c (e i) then 1 else -1 : ℝ) := by
      intro c; rw [ ← he₂, Finset.sum_image <| by tauto ] ;
    unfold inducedSum coloringToInt; aesop;
  · have h_card : Finset.card (X.sym2.filter (fun e => ¬e.IsDiag)) = Nat.choose (Finset.card X) 2 := by
      have h_card : Finset.card (Finset.filter (fun e => ¬e.IsDiag) (Finset.sym2 X)) = Finset.card (Finset.powersetCard 2 X) := by
        refine' Finset.card_bij ( fun x hx => Finset.filter ( fun y => y ∈ x ) X ) _ _ _;
        · simp +contextual [ Finset.mem_powersetCard, Finset.subset_iff ];
          intro a ha₁ ha₂; rcases a with ⟨ x, y ⟩ ; simp_all +decide [ Sym2.IsDiag ] ;
          rw [ show { y_1 ∈ X | y_1 = x ∨ y_1 = y } = { x, y } by ext; aesop ] ; rw [ Finset.card_insert_of_notMem, Finset.card_singleton ] ; aesop;
        · simp +contextual [ Finset.ext_iff, Sym2.forall ];
          grind;
        · simp +decide [ Finset.mem_powersetCard, Finset.subset_iff ];
          intro b hb hb'; obtain ⟨ x, y, hxy ⟩ := Finset.card_eq_two.mp hb'; use Sym2.mk ( x, y ) ; aesop;
      rw [ h_card, Finset.card_powersetCard ];
    rw [ ← h_card, ← he₂, Finset.card_image_of_injective _ he₁, Finset.card_fin ]

/-
The binomial coefficient binom(|X|, 2) is bounded by n^2 / 2.
-/
lemma binom_card_le_sq_div_two (n : ℕ) (X : Finset (Fin n)) :
    (X.card.choose 2 : ℝ) ≤ (n : ℝ)^2 / 2 := by
  rw [ le_div_iff₀ ] <;> norm_cast ; norm_num [ Nat.choose_two_right ];
  exact le_trans ( Nat.div_mul_le_self _ _ ) ( by nlinarith [ Nat.sub_le ( Finset.card X ) 1, show Finset.card X ≤ n from le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ] )

/-
Bound for the exponent in Hoeffding's inequality.
-/
lemma exponent_bound (n : ℕ) (X : Finset (Fin n)) (C : ℝ) (hC : C > 0) (hn : n > 0) (hX : X.card.choose 2 > 0) :
    - (C * (n : ℝ) ^ (3 / 2 : ℝ)) ^ 2 / (2 * (X.card.choose 2 : ℝ)) ≤ - C ^ 2 * n := by
  rw [ div_le_iff₀ ] <;> ring_nf <;> norm_cast;
  · rw [ show ( n : ℝ ) ^ ( 3 / 2 : ℝ ) = n * Real.sqrt n by rw [ Real.sqrt_eq_rpow, ← Real.rpow_one_add' ] <;> norm_num ] ; ring_nf ; norm_num [ hC.le ];
    -- Apply the lemma `binom_card_le_sq_div_two`.
    have h_binom : (X.card.choose 2 : ℝ) ≤ (n : ℝ)^2 / 2 := by
      exact binom_card_le_sq_div_two n X;
    nlinarith [ show 0 ≤ C ^ 2 * n by positivity ];
  · positivity

/-
If a subset X has fewer than 2 elements, its induced sum is 0.
-/
lemma inducedSum_eq_zero_of_card_lt_two (n : ℕ) (f : Sym2 (Fin n) → ℤ) (X : Finset (Fin n)) (hX : X.card < 2) :
    inducedSum n f X = 0 := by
      unfold inducedSum;
      interval_cases _ : X.card <;> simp_all +decide [ Finset.sum_filter ];
      rw [ Finset.card_eq_one ] at * ; aesop

/-
Monotonicity of the bound 2 * exp(x).
-/
lemma ennreal_exp_bound_mono (a b : ℝ) (h : a ≤ b) :
    2 * ENNReal.ofReal (Real.exp a) ≤ 2 * ENNReal.ofReal (Real.exp b) := by
      gcongr

/-
n^2 is at least 2 * binom(k, 2) for k <= n.
-/
lemma sq_ge_choose_two_mul_two (n k : ℕ) (hk : k ≤ n) : (n : ℝ)^2 ≥ 2 * (k.choose 2 : ℝ) := by
  rcases k with ( _ | _ | k ) <;> simp_all +decide [ Nat.choose_two_right ];
  norm_cast ; nlinarith [ Nat.div_mul_cancel ( show 2 ∣ ( k + 1 + 1 ) * ( k + 1 ) from Nat.dvd_of_mod_eq_zero ( by norm_num [ Nat.add_mod, Nat.mod_two_of_bodd ] ) ) ]

/-
The exponent term is bounded by -C^2 * n.
-/
lemma exponent_bound_aux (n : ℕ) (X : Finset (Fin n)) (C : ℝ) (hC : C > 0) (hn : n > 0) (hX : X.card.choose 2 > 0) :
    - (C * (n : ℝ) ^ (3 / 2 : ℝ)) ^ 2 / (2 * (X.card.choose 2 : ℝ)) ≤ - C ^ 2 * n := by
      -- Apply the lemma exponent_bound to derive the inequality.
      apply exponent_bound n X C hC hn hX

/-
The probability that the induced sum of X exceeds C n^(3/2) is bounded by 2 exp(-C^2 n).
-/
lemma prob_induced_sum_le_uniform (n : ℕ) (X : Finset (Fin n)) (C : ℝ) (hC : C > 0) (hn : n ≥ 2) :
    (coloringMeasure n) {c | |inducedSum n (coloringToInt c) X| ≥ C * (n : ℝ)^(3/2 : ℝ)} ≤ 2 * ENNReal.ofReal (Real.exp (- C^2 * n)) := by
      by_cases hX : X.card.choose 2 > 0;
      · refine' le_trans ( prob_induced_sum_ge n X _ _ ) _;
        · positivity;
        · exact mul_le_mul_left' ( ENNReal.ofReal_le_ofReal <| Real.exp_le_exp.mpr <| by nlinarith [ exponent_bound n X C hC ( by linarith ) hX ] ) _;
      · -- Since the binomial coefficient is zero, X must have fewer than 2 elements. Therefore, the induced sum of X is zero.
        have h_induced_sum_zero : ∀ c : Sym2 (Fin n) → Bool, inducedSum n (coloringToInt c) X = 0 := by
          exact fun c => inducedSum_eq_zero_of_card_lt_two n ( coloringToInt c ) X ( by contrapose! hX; exact Nat.choose_pos ( by linarith ) );
        norm_num [ h_induced_sum_zero ];
        rw [ show { c : Sym2 ( Fin n ) → Bool | C * ( n : ℝ ) ^ ( 3 / 2 : ℝ ) ≤ 0 } = ∅ by rw [ Set.eq_empty_iff_forall_notMem ] ; rintro c ( hc : C * ( n : ℝ ) ^ ( 3 / 2 : ℝ ) ≤ 0 ) ; exact not_le_of_gt ( by positivity ) hc ] ; norm_num

/-
The sum of a constant over all subsets is 2^n times the constant.
-/
lemma sum_const_bound (n : ℕ) (K : ℝ≥0∞) :
    ∑ _ : Finset (Fin n), K = (2^n : ℝ≥0∞) * K := by
      norm_num +zetaDelta at *

/-
The sum of a function bounded by K over all subsets is bounded by 2^n * K.
-/
lemma sum_le_pow_two_mul (n : ℕ) (f : Finset (Fin n) → ℝ≥0∞) (K : ℝ≥0∞) (h : ∀ X, f X ≤ K) :
    ∑ X, f X ≤ (2^n : ℝ≥0∞) * K := by
      refine' le_trans ( Finset.sum_le_sum fun _ _ => h _ ) _;
      norm_num [ Finset.card_univ ]

/-
The probability that there exists a subset X with induced sum >= C n^(3/2) is bounded by 2^n * 2 * exp(-C^2 n).
-/
lemma prob_exists_induced_sum_ge (n : ℕ) (C : ℝ) (hC : C > 0) (hn : n ≥ 2) :
    (coloringMeasure n) {c | ∃ X : Finset (Fin n), |inducedSum n (coloringToInt c) X| ≥ C * (n : ℝ)^(3/2 : ℝ)} ≤
    (2^n : ℝ≥0∞) * (2 * ENNReal.ofReal (Real.exp (- C^2 * n))) := by
      -- Apply the union bound to the family of sets {c | |inducedSum n (coloringToInt c) X| ≥ C * n^(3/2)} over all subsets X.
      have h_union_bound : (coloringMeasure n) (⋃ X : Finset (Fin n), {c | |inducedSum n (coloringToInt c) X| ≥ C * (n : ℝ)^(3/2 : ℝ)}) ≤ ∑ X : Finset (Fin n), (coloringMeasure n) {c | |inducedSum n (coloringToInt c) X| ≥ C * (n : ℝ)^(3/2 : ℝ)} := by
        exact
          measure_iUnion_fintype_le (coloringMeasure n) fun i =>
            {c | ↑|inducedSum n (coloringToInt c) i| ≥ C * ↑n ^ (3 / 2)};
      simp_all +decide [ Set.setOf_exists ];
      refine le_trans h_union_bound ?_;
      exact le_trans ( Finset.sum_le_sum fun _ _ => show ( coloringMeasure n ) { c | C * ( n : ℝ ) ^ ( 3 / 2 : ℝ ) ≤ |↑ ( inducedSum n ( coloringToInt c ) _ )| } ≤ 2 * ENNReal.ofReal ( Real.exp ( - ( C ^ 2 * n ) ) ) from by simpa using prob_induced_sum_le_uniform n _ C hC hn ) ( by simp +decide [ Finset.card_univ ] )

/-
If the probability of a set of colorings is less than 1, then there exists a coloring not in that set.
-/
lemma prob_lt_one_implies_exists_good_coloring (n : ℕ) (P : Set (Sym2 (Fin n) → Bool)) :
    (coloringMeasure n) P < 1 → ∃ c, c ∉ P := by
      -- By definition of measure, if the measure of P is less than 1, then the measure of its complement is greater than 0.
      intro h
      have h_compl : (coloringMeasure n) Pᶜ > 0 := by
        have h_compl : (coloringMeasure n) Pᶜ = 1 - (coloringMeasure n) P := by
          have h_compl : (coloringMeasure n) (Set.univ \ P) = 1 - (coloringMeasure n) P := by
            rw [ MeasureTheory.measure_diff ] <;> norm_num;
            exact MeasurableSet.nullMeasurableSet ( by exact
              DiscreteMeasurableSpace.forall_measurableSet P );
          simpa [ Set.diff_eq ] using h_compl;
        exact h_compl.symm ▸ tsub_pos_of_lt h;
      contrapose! h_compl;
      rw [ show Pᶜ = ∅ by aesop ] ; norm_num

/-
For n >= 2 and C^2 > 2 log 2, the probability bound is strictly less than 1.
-/
lemma bound_lt_one_of_large_C (n : ℕ) (hn : n ≥ 2) (C : ℝ) (hC : C^2 > 2 * Real.log 2) :
    (2^n : ℝ≥0∞) * (2 * ENNReal.ofReal (Real.exp (- C^2 * n))) < 1 := by
      rw [ ← ENNReal.toReal_lt_toReal ] <;> norm_num [ ENNReal.toReal_mul, ENNReal.toReal_ofReal, Real.exp_pos ];
      · rw [ ENNReal.toReal_ofReal ( Real.exp_nonneg _ ) ] ; ring_nf;
        -- Simplifying the inequality.
        have h_simp : Real.exp (-(C ^ 2 * n)) * 2 ^ (n + 1) < 1 := by
          rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_mul ( by positivity ) ( by positivity ), Real.log_exp, Real.log_pow ] ; ring_nf ; norm_num;
          nlinarith [ Real.log_pos one_lt_two, show ( n : ℝ ) ≥ 2 by norm_cast ];
        convert h_simp using 1 ; ring;
      · norm_num [ ENNReal.mul_eq_top ]

/-
If there exists a coloring such that all induced sums are bounded by B, then H(n) <= B.
-/
lemma H_le_of_exists (n : ℕ) (B : ℝ) (h : ∃ c : Sym2 (Fin n) → Bool, ∀ X : Finset (Fin n), |(inducedSum n (coloringToInt c) X : ℝ)| ≤ B) :
    (H n : ℝ) ≤ B := by
      obtain ⟨ c, hc ⟩ := h;
      refine' le_trans _ ( show ( ⌊B⌋ : ℝ ) ≤ B by exact Int.floor_le _ );
      refine' mod_cast le_trans ( Finset.min'_le _ _ <| Finset.mem_image_of_mem _ <| Finset.mem_univ c ) _;
      simp_all +decide [ Finset.max' ];
      exact fun X => Int.le_floor.2 <| mod_cast hc X

/-
If C is large enough and positive, there exists a coloring such that all induced sums are strictly less than C * n^(3/2).
-/
lemma exists_good_coloring (n : ℕ) (hn : n ≥ 2) (C : ℝ) (hC_pos : C > 0) (hC_sq : C^2 > 2 * Real.log 2) :
    ∃ c : Sym2 (Fin n) → Bool, ∀ X : Finset (Fin n), |inducedSum n (coloringToInt c) X| < C * (n : ℝ)^(3/2 : ℝ) := by
      -- Let Bad be the set of colorings where there exists a subset X with induced sum ≥ C * n^(3/2).
      set Bad := {c : Sym2 (Fin n) → Bool | ∃ X : Finset (Fin n), |(inducedSum n (coloringToInt c) X : ℝ)| ≥ C * (n : ℝ)^(3/2 : ℝ)} with hBad_def;
      -- By the probabilistic method, since the probability of Bad is less than 1, there exists a coloring not in Bad.
      have h_exists_not_bad : (coloringMeasure n) Bad < 1 := by
        refine' lt_of_le_of_lt ( _ : _ ≤ _ ) ( bound_lt_one_of_large_C n hn C hC_sq );
        convert prob_exists_induced_sum_ge n C hC_pos hn using 1;
        norm_num +zetaDelta at *;
      have := prob_lt_one_implies_exists_good_coloring n Bad h_exists_not_bad; aesop;

/-
4 is greater than 2 * Real.log 2.
-/
lemma four_gt_two_mul_log_two : 4 > 2 * Real.log 2 := by
  have := Real.log_two_lt_d9 ; norm_num at * ; linarith

/-
The Paley-Zygmund inequality: for a non-negative random variable Z with finite second moment and $0 \le \theta < 1$,
$\mathbb{P}(Z \ge \theta \mathbb{E}Z) \ge (1-\theta)^2 \frac{(\mathbb{E}Z)^2}{\mathbb{E}Z^2}$.
-/
lemma paley_zygmund_inequality {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : Ω → ℝ} (hZ_nonneg : 0 ≤ Z) (hZ_int : Integrable Z P) (hZ_sq_int : Integrable (fun ω => (Z ω)^2) P)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ_lt_1 : θ < 1) :
    P {ω | Z ω ≥ θ * ∫ ω, Z ω ∂P} ≥ ENNReal.ofReal ((1 - θ)^2 * (∫ ω, Z ω ∂P)^2 / ∫ ω, (Z ω)^2 ∂P) := by
      -- Let $E = \mathbb{E}[Z]$. We have $Z = Z \mathbb{1}_{Z < \theta E} + Z \mathbb{1}_{Z \ge \theta E}$.
      set E : ℝ := ∫ ω, Z ω ∂P
      have h_split : E = ∫ ω, Z ω * (if Z ω < θ * E then 1 else 0) ∂P + ∫ ω, Z ω * (if Z ω ≥ θ * E then 1 else 0) ∂P := by
        rw [ ← MeasureTheory.integral_add ];
        · exact congr_arg _ ( funext fun ω => by split_ifs <;> linarith );
        · refine' hZ_int.norm.mono' _ _;
          · refine' hZ_int.1.mul _;
            have := hZ_int.aestronglyMeasurable.aemeasurable;
            exact Measurable.aestronglyMeasurable ( Measurable.ite ( measurableSet_Iio.preimage ( measurable_id' ) ) measurable_const measurable_const ) |> fun h => h.comp_aemeasurable this;
          · filter_upwards [ ] with ω using by split_ifs <;> simp +decide [ * ] ;
        · refine' hZ_int.norm.mono' _ _;
          · have := hZ_int.aestronglyMeasurable;
            exact this.mul ( Measurable.aestronglyMeasurable ( show Measurable fun x => if θ * E ≤ x then ( 1 : ℝ ) else 0 from Measurable.ite ( measurableSet_Ici ) measurable_const measurable_const ) |> fun h => h.comp_aemeasurable this.aemeasurable );
          · filter_upwards [ ] with ω using by split_ifs <;> simp +decide [ * ] ;
      -- The first term is bounded by $\theta E$.
      have h_first_term : ∫ ω, Z ω * (if Z ω < θ * E then 1 else 0) ∂P ≤ θ * E := by
        refine' le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _;
        refine' fun ω => θ * E;
        · exact Filter.Eventually.of_forall fun ω => mul_nonneg ( hZ_nonneg ω ) ( by positivity );
        · fun_prop;
        · filter_upwards [ ] with ω using by split_ifs <;> nlinarith [ hZ_nonneg ω, show 0 ≤ E by exact MeasureTheory.integral_nonneg hZ_nonneg ] ;
        · norm_num;
      -- By Cauchy-Schwarz, $(\mathbb{E}[Z \mathbb{1}_{Z \ge \theta E}])^2 \le \mathbb{E}[Z^2] \mathbb{P}(Z \ge \theta E)$.
      have h_cauchy_schwarz : (∫ ω, Z ω * (if Z ω ≥ θ * E then 1 else 0) ∂P) ^ 2 ≤ (∫ ω, Z ω ^ 2 ∂P) * (∫ ω, (if Z ω ≥ θ * E then 1 else 0) ∂P) := by
        have h_cauchy_schwarz : ∀ (f g : Ω → ℝ), MeasureTheory.Integrable (fun ω => f ω ^ 2) P → MeasureTheory.Integrable (fun ω => g ω ^ 2) P → MeasureTheory.Integrable (fun ω => f ω * g ω) P → (∫ ω, f ω * g ω ∂P) ^ 2 ≤ (∫ ω, f ω ^ 2 ∂P) * (∫ ω, g ω ^ 2 ∂P) := by
          intros f g hf hg hfg
          have h_cauchy_schwarz : (∫ ω, (f ω - (∫ ω, f ω * g ω ∂P) / (∫ ω, g ω ^ 2 ∂P) * g ω) ^ 2 ∂P) ≥ 0 := by
            exact MeasureTheory.integral_nonneg fun ω => sq_nonneg _;
          by_cases h : ∫ ω, g ω ^ 2 ∂P = 0 <;> simp +decide [ h, sub_sq, mul_pow ] at h_cauchy_schwarz ⊢;
          · rw [ MeasureTheory.integral_eq_zero_iff_of_nonneg ( fun _ => sq_nonneg _ ) ] at h;
            · exact MeasureTheory.integral_eq_zero_of_ae ( h.mono fun x hx => by simp +decide [ show g x = 0 by simpa using hx ] );
            · exact hg;
          · rw [ MeasureTheory.integral_add, MeasureTheory.integral_sub ] at h_cauchy_schwarz;
            · simp +decide [ div_eq_inv_mul, mul_assoc, mul_comm, mul_left_comm, MeasureTheory.integral_mul_const, ] at h_cauchy_schwarz ⊢;
              simp +decide [ ← mul_assoc, MeasureTheory.integral_mul_const ] at h_cauchy_schwarz ⊢ ; nlinarith [ inv_mul_cancel_left₀ h ( ∫ ω, f ω * g ω ∂P ), inv_mul_cancel₀ h, show 0 ≤ ∫ ω, f ω ^ 2 ∂P from MeasureTheory.integral_nonneg fun _ => sq_nonneg _, show 0 ≤ ∫ ω, g ω ^ 2 ∂P from MeasureTheory.integral_nonneg fun _ => sq_nonneg _ ] ;
            · exact hf;
            · convert hfg.mul_const ( 2 * ( ( ∫ ω, f ω * g ω ∂P ) / ∫ ω, g ω ^ 2 ∂P ) ) using 2 ; ring;
            · refine' MeasureTheory.Integrable.sub hf _;
              convert hfg.mul_const ( 2 * ( ( ∫ ω, f ω * g ω ∂P ) / ∫ ω, g ω ^ 2 ∂P ) ) using 2 ; ring;
            · exact hg.const_mul _;
        convert h_cauchy_schwarz ( fun ω => Z ω ) ( fun ω => if Z ω ≥ θ * E then 1 else 0 ) hZ_sq_int _ _ using 1;
        · exact congrArg _ ( by congr; ext; split_ifs <;> norm_num );
        · refine' MeasureTheory.Integrable.mono' _ _ _;
          refine' fun ω => 1;
          · norm_num;
          · simp +zetaDelta at *;
            have := hZ_int.aestronglyMeasurable;
            exact Measurable.aestronglyMeasurable ( Measurable.ite ( measurableSet_le measurable_const measurable_id' ) measurable_const measurable_const ) |> fun h => h.comp_aemeasurable this.aemeasurable;
          · exact Filter.Eventually.of_forall fun ω => by by_cases h : Z ω ≥ θ * E <;> norm_num [ h ] ;
        · refine' hZ_int.norm.mono' _ _;
          · refine' hZ_int.1.mul _;
            have := hZ_int.aestronglyMeasurable;
            exact Measurable.aestronglyMeasurable ( show Measurable fun x : ℝ => if x ≥ θ * E then ( 1 : ℝ ) else 0 from Measurable.ite ( measurableSet_Ici ) measurable_const measurable_const ) |> fun h => h.comp_aemeasurable this.aemeasurable;
          · filter_upwards [ ] with ω using by split_ifs <;> simp +decide [ * ] ;
      by_cases hE : E = 0 <;> simp +decide [ hE ] at *;
      -- Rearrange h_cauchy_schwarz to get the desired inequality.
      have h_rearrange : (∫ ω, (if θ * E ≤ Z ω then 1 else 0) ∂P) ≥ (1 - θ) ^ 2 * E ^ 2 / (∫ ω, Z ω ^ 2 ∂P) := by
        by_cases h : ∫ ω, Z ω ^ 2 ∂P = 0 <;> simp +decide [ h ] at h_cauchy_schwarz ⊢;
        · exact MeasureTheory.integral_nonneg fun _ => by positivity;
        · field_simp;
          refine' le_trans _ h_cauchy_schwarz;
          have h_rearrange : (∫ ω, if θ * E ≤ Z ω then Z ω else 0 ∂P) ≥ (1 - θ) * E := by
            linarith;
          convert pow_le_pow_left₀ ( mul_nonneg ( sub_nonneg.2 hθ_lt_1.le ) ( MeasureTheory.integral_nonneg hZ_nonneg ) ) h_rearrange 2 using 1 ; ring;
      refine' le_trans ( ENNReal.ofReal_le_ofReal h_rearrange ) _;
      rw [ MeasureTheory.integral_eq_lintegral_of_nonneg_ae ];
      · rw [ MeasureTheory.lintegral_congr_ae, MeasureTheory.lintegral_indicator₀ ];
        change ENNReal.ofReal ( ∫⁻ ω in { ω | θ * E ≤ Z ω }, 1 ∂P ).toReal ≤ P { ω | θ * E ≤ Z ω };
        · simp +decide [ ENNReal.ofReal ];
        · exact hZ_int.1.aemeasurable.nullMeasurable measurableSet_Ici;
        · filter_upwards [ ] with ω using by by_cases h : θ * E ≤ Z ω <;> simp +decide [ h ] ;
      · exact Filter.Eventually.of_forall fun ω => by positivity;
      · have := hZ_int.aestronglyMeasurable;
        exact Measurable.aestronglyMeasurable ( show Measurable fun x : ℝ => if θ * E ≤ x then ( 1 : ℝ ) else 0 from Measurable.ite ( measurableSet_Ici ) measurable_const measurable_const ) |> fun h => h.comp_aemeasurable this.aemeasurable

/-
For any real number x and natural number k <= 4, |x|^k <= 1 + |x|^4.
-/
lemma abs_pow_le_one_add_abs_pow_four (x : ℝ) (k : ℕ) (hk : k ≤ 4) :
    |x|^k ≤ 1 + |x|^4 := by
      interval_cases k <;> norm_num;
      · by_cases hx : |x| ≤ 1;
        · exact le_add_of_le_of_nonneg hx ( by positivity );
        · nlinarith [ sq_nonneg ( |x|^2 - 1 ) ];
      · cases abs_cases x <;> push_cast [ * ] <;> nlinarith [ sq_nonneg ( x^2 - 1 ) ];
      · nlinarith [ sq_nonneg ( |x|^2 - 1 ), abs_nonneg x ]

/-
If X is measurable and has a finite fourth moment, then its k-th moment is finite for all k <= 4.
-/
lemma integrable_pow_of_integrable_pow_four {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX_meas : AEStronglyMeasurable X P) (hX4 : Integrable (fun ω => (X ω)^4) P) (k : ℕ) (hk : k ≤ 4) :
    Integrable (fun ω => (X ω)^k) P := by
      interval_cases k <;> norm_num at *;
      · refine' MeasureTheory.Integrable.mono' _ _ _;
        exacts [ fun ω => 1 + |X ω ^ 4|, by exact MeasureTheory.Integrable.add ( MeasureTheory.integrable_const _ ) ( hX4.norm ), hX_meas, Filter.Eventually.of_forall fun ω => by simpa using abs_pow_le_one_add_abs_pow_four ( X ω ) 1 ( by norm_num ) ];
      · refine' MeasureTheory.Integrable.mono' _ _ _;
        exacts [ fun ω => X ω ^ 4 + 1, by exact MeasureTheory.Integrable.add hX4 ( MeasureTheory.integrable_const _ ), by exact hX_meas.pow 2, Filter.Eventually.of_forall fun ω => by simpa using by nlinarith [ sq_nonneg ( X ω ^ 2 - 1 ) ] ];
      · refine' MeasureTheory.Integrable.mono' _ _ _;
        exacts [ fun ω => X ω ^ 4 + 1, hX4.add ( MeasureTheory.integrable_const _ ), hX_meas.pow 3, Filter.Eventually.of_forall fun ω => abs_le.mpr ⟨ by nlinarith only [ sq_nonneg ( X ω ^ 2 - 1 ), sq_nonneg ( X ω ^ 2 ) ], by nlinarith only [ sq_nonneg ( X ω ^ 2 - 1 ), sq_nonneg ( X ω ^ 2 ) ] ⟩ ];
      · exact hX4

/-
If X and Y are independent, Y has mean 0, then E[X^3 Y] = 0.
-/
lemma expectation_pow_three_mul_eq_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X Y : Ω → ℝ}
    (h_indep : IndepFun X Y P)
    (hX_meas : AEStronglyMeasurable X P)
    (hY_meas : AEStronglyMeasurable Y P)
    (hY_mean_zero : ∫ ω, Y ω ∂P = 0) :
    ∫ ω, (X ω)^3 * Y ω ∂P = 0 := by
      have h_indep_X3Y : ∫ ω, X ω ^ 3 * Y ω ∂P = (∫ ω, X ω ^ 3 ∂P) * (∫ ω, Y ω ∂P) := by
        apply_rules [ IndepFun.integral_mul_eq_mul_integral ];
        · exact h_indep.comp ( measurable_id.pow_const 3 ) measurable_id;
        · exact hX_meas.pow 3;
      aesop

/-
If X and Y are independent, then E[X^2 Y^2] = E[X^2] E[Y^2].
-/
lemma expectation_sq_mul_sq_eq_mul_expectation_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X Y : Ω → ℝ}
    (h_indep : IndepFun X Y P)
    (hX_meas : AEStronglyMeasurable X P)
    (hY_meas : AEStronglyMeasurable Y P) :
    ∫ ω, (X ω)^2 * (Y ω)^2 ∂P = (∫ ω, (X ω)^2 ∂P) * (∫ ω, (Y ω)^2 ∂P) := by
      apply_rules [ ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral ];
      · exact h_indep.comp ( measurable_id'.pow_const 2 ) ( measurable_id'.pow_const 2 );
      · simpa only [ sq ] using hX_meas.mul hX_meas;
      · simpa only [ sq ] using hY_meas.mul hY_meas

/-
Properties of Rademacher variables: integrability and moments.
-/
lemma rademacher_props {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (h : IsRademacher P X) :
    Integrable X P ∧ (∫ ω, X ω ∂P = 0) ∧
    Integrable (fun ω => (X ω)^2) P ∧ (∫ ω, (X ω)^2 ∂P = 1) ∧
    Integrable (fun ω => (X ω)^4) P ∧ (∫ ω, (X ω)^4 ∂P = 1) := by
      -- Since X is Rademacher, we know that X^2 = 1 almost everywhere.
      have h_X_sq : ∀ᵐ ω ∂P, (X ω) ^ 2 = 1 := by
        have h_X_sq : ∀ᵐ ω ∂P, X ω = 1 ∨ X ω = -1 := by
          have := h.1;
          have h_X_values : P {ω | X ω ≠ 1 ∧ X ω ≠ -1} = 0 := by
            have := h.2.1; have := h.2.2; simp_all +decide [ Set.setOf_and ];
            rw [ show { a : Ω | ¬X a = 1 } ∩ { a : Ω | ¬X a = -1 } = ( { ω | X ω = 1 } ∪ { ω | X ω = -1 } )ᶜ by ext; aesop, MeasureTheory.measure_compl ] <;> norm_num [ * ];
            · rw [ MeasureTheory.measure_union ] <;> norm_num [ * ];
              · norm_num [ ENNReal.inv_two_add_inv_two ];
              · exact Set.disjoint_left.mpr fun ω hω₁ hω₂ => by linarith [ Set.mem_setOf.mp hω₁, Set.mem_setOf.mp hω₂ ];
              · exact measurableSet_eq_fun ‹_› measurable_const |> MeasurableSet.mem;
            · exact MeasurableSet.union ( measurableSet_eq_fun ‹_› measurable_const ) ( measurableSet_eq_fun ‹_› measurable_const );
          filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp h_X_values ] with ω hω using by contrapose! hω; tauto;
        filter_upwards [ h_X_sq ] with ω hω using by rcases hω with ( hω | hω ) <;> norm_num [ hω ] ;
      refine' ⟨ _, _, _, _, _ ⟩;
      · refine' MeasureTheory.Integrable.mono' _ _ _;
        exacts [ fun ω => 1, MeasureTheory.integrable_const _, h.1.aestronglyMeasurable, by filter_upwards [ h_X_sq ] with ω hω using abs_le.mpr ⟨ by nlinarith, by nlinarith ⟩ ];
      · have h_E_X : ∫ ω, X ω ∂P = ∫ ω in {ω | X ω = 1}, (1 : ℝ) ∂P - ∫ ω in {ω | X ω = -1}, (1 : ℝ) ∂P := by
          rw [ ← MeasureTheory.integral_indicator ( show MeasurableSet { ω | X ω = 1 } from by exact h.1 ( MeasurableSingletonClass.measurableSet_singleton _ ) ), ← MeasureTheory.integral_indicator ( show MeasurableSet { ω | X ω = -1 } from by exact h.1 ( MeasurableSingletonClass.measurableSet_singleton _ ) ) ];
          rw [ ← MeasureTheory.integral_sub ];
          · rw [ MeasureTheory.integral_congr_ae ];
            filter_upwards [ h_X_sq ] with ω hω using by norm_num [ Set.indicator ] ; rcases eq_or_eq_neg_of_sq_eq_sq ( X ω ) 1 ( by linarith ) with h | h <;> norm_num [ h ] ;
          · exact MeasureTheory.integrable_indicator_iff ( h.1 ( MeasurableSingletonClass.measurableSet_singleton 1 ) ) |>.2 ( MeasureTheory.integrable_const _ );
          · exact MeasureTheory.integrable_indicator_iff ( show MeasurableSet { ω | X ω = -1 } from measurableSet_eq_fun h.1 measurable_const ) |>.2 ( MeasureTheory.integrable_const _ );
        have := h.2.1;
        have := h.2.2; simp_all +decide [ MeasureTheory.measureReal_def ] ;
      · rw [ MeasureTheory.integrable_congr h_X_sq ] ; norm_num;
      · rw [ MeasureTheory.integral_congr_ae h_X_sq, MeasureTheory.integral_const ] ; norm_num;
      · rw [ MeasureTheory.integral_congr_ae ( h_X_sq.mono fun ω hω => by rw [ show X ω ^ 4 = ( X ω ^ 2 ) ^ 2 by ring, hω ] ) ] ; norm_num;
        rw [ MeasureTheory.integrable_congr ( h_X_sq.mono fun ω hω => by rw [ show X ω ^ 4 = ( X ω ^ 2 ) ^ 2 by ring, hω ] ) ] ; norm_num

/-
The second moment of a sum of independent Rademacher variables is equal to the number of variables.
-/
lemma second_moment_rademacher_sum {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {m : ℕ} (ξ : Fin m → Ω → ℝ)
    (h_indep : iIndepFun ξ P)
    (h_rad : ∀ i, IsRademacher P (ξ i)) :
    ∫ ω, (∑ i, ξ i ω)^2 ∂P = m := by
      -- Expand the square and use linearity of expectation.
      have h_expand : ∫ ω, (∑ i, ξ i ω) ^ 2 ∂P = ∑ i, ∑ j, ∫ ω, ξ i ω * ξ j ω ∂P := by
        simp +decide only [pow_two, Finset.sum_mul _ _ _, mul_sum];
        rw [ MeasureTheory.integral_finset_sum ];
        · refine' Finset.sum_congr rfl fun i _ => MeasureTheory.integral_finset_sum _ _;
          intro j _;
          have h_integrable : ∀ i, MeasureTheory.Integrable (fun ω => (ξ i ω)^2) P := by
            exact fun i => ( rademacher_props ( h_rad i ) ) |>.2.2.1;
          refine' MeasureTheory.Integrable.mono' ( h_integrable i |> fun hi => hi.add ( h_integrable j ) ) _ _;
          · have h_integrable : ∀ i, MeasureTheory.AEStronglyMeasurable (fun ω => ξ i ω) P := by
              intro i; specialize h_rad i; exact h_rad.1.aestronglyMeasurable;
            exact MeasureTheory.AEStronglyMeasurable.mul ( h_integrable i ) ( h_integrable j );
          · filter_upwards [ ] with ω using abs_le.mpr ⟨ by norm_num; nlinarith only, by norm_num; nlinarith only ⟩;
        · intro i _;
          refine' MeasureTheory.integrable_finset_sum _ _;
          intro j _;
          refine' MeasureTheory.Integrable.mono' _ _ _;
          exact fun ω => ( ξ i ω ) ^ 2 + ( ξ j ω ) ^ 2;
          · exact MeasureTheory.Integrable.add ( by exact ( rademacher_props ( h_rad i ) ) |>.2.2.1 ) ( by exact ( rademacher_props ( h_rad j ) ) |>.2.2.1 );
          · exact MeasureTheory.AEStronglyMeasurable.mul ( h_rad i |>.1.aestronglyMeasurable ) ( h_rad j |>.1.aestronglyMeasurable );
          · filter_upwards [ ] with ω using abs_le.mpr ⟨ by nlinarith only, by nlinarith only ⟩;
      -- Since ξ_i are independent and mean 0 (Rademacher), E[ξ_i ξ_j] = E[ξ_i]E[ξ_j] = 0 for i ≠ j.
      have h_cross_terms : ∀ i j : Fin m, i ≠ j → ∫ ω, ξ i ω * ξ j ω ∂P = 0 := by
        intro i j hij
        have h_zero : ∫ ω, ξ i ω * ξ j ω ∂P = (∫ ω, ξ i ω ∂P) * (∫ ω, ξ j ω ∂P) := by
          apply_rules [ ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral ];
          · exact h_indep.indepFun hij;
          · exact h_rad i |>.1.aestronglyMeasurable;
          · exact ( h_rad j ).1.aestronglyMeasurable
        have h_zero_i : ∫ ω, ξ i ω ∂P = 0 := by
          exact ( rademacher_props ( h_rad i ) ) |>.2.1
        have h_zero_j : ∫ ω, ξ j ω ∂P = 0 := by
          exact ( rademacher_props ( h_rad j ) ) |>.2.1
        rw [h_zero, h_zero_i, h_zero_j]
        simp [mul_zero];
      rw [ h_expand, Finset.sum_congr rfl fun i hi => Finset.sum_eq_single i ( by aesop ) ( by aesop ) ];
      simp +decide [ ← sq, rademacher_props ( h_rad _ ) ]

/-
Expectation of the fourth power of the sum of two independent variables, where the second has specific moments.
-/
lemma expectation_add_pow_four {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X Y : Ω → ℝ}
    (h_indep : IndepFun X Y P)
    (hX : AEStronglyMeasurable X P)
    (hY : AEStronglyMeasurable Y P)
    (hX4 : Integrable (fun ω => (X ω)^4) P)
    (hY4 : Integrable (fun ω => (Y ω)^4) P)
    (hY_mean : ∫ ω, Y ω ∂P = 0)
    (hY_sq_mean : ∫ ω, (Y ω)^2 ∂P = 1)
    (hY_cube_mean : ∫ ω, (Y ω)^3 ∂P = 0)
    (hY_four_mean : ∫ ω, (Y ω)^4 ∂P = 1) :
    ∫ ω, (X ω + Y ω)^4 ∂P = ∫ ω, (X ω)^4 ∂P + 6 * ∫ ω, (X ω)^2 ∂P + 1 := by
      -- By linearity of expectation and independence of $X$ and $Y$, we can expand and simplify the integral.
      have h_expand : ∫ ω, (X ω + Y ω)^4 ∂P = (∫ ω, X ω^4 ∂P) + 4 * (∫ ω, X ω^3 * Y ω ∂P) + 6 * (∫ ω, X ω^2 * Y ω^2 ∂P) + 4 * (∫ ω, X ω * Y ω^3 ∂P) + (∫ ω, Y ω^4 ∂P) := by
        rw [ ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_add, ← MeasureTheory.integral_add ];
        · rw [ ← MeasureTheory.integral_add, ← MeasureTheory.integral_add ] <;> ring_nf;
          · apply_rules [ MeasureTheory.Integrable.add, MeasureTheory.Integrable.mul_const, MeasureTheory.Integrable.const_mul ];
            · refine' MeasureTheory.Integrable.mono' _ _ _;
              refine' fun ω => X ω ^ 4 + Y ω ^ 4;
              · exact hX4.add hY4;
              · exact hX.mul ( hY.pow 3 );
              · filter_upwards [ ] with ω using abs_le.mpr ⟨ by nlinarith only [ sq_nonneg ( X ω ^ 2 - Y ω ^ 2 ), sq_nonneg ( X ω * Y ω ), sq_nonneg ( X ω ^ 2 ), sq_nonneg ( Y ω ^ 2 ) ], by nlinarith only [ sq_nonneg ( X ω ^ 2 - Y ω ^ 2 ), sq_nonneg ( X ω * Y ω ), sq_nonneg ( X ω ^ 2 ), sq_nonneg ( Y ω ^ 2 ) ] ⟩;
            · refine' MeasureTheory.Integrable.mono' _ _ _;
              exacts [ fun ω => X ω ^ 4 + Y ω ^ 4, by exact MeasureTheory.Integrable.add hX4 hY4, by exact hX.pow 2 |> AEStronglyMeasurable.mul <| hY.pow 2, Filter.Eventually.of_forall fun ω => abs_le.mpr ⟨ by nlinarith only [ sq_nonneg ( X ω ^ 2 - Y ω ^ 2 ) ], by nlinarith only [ sq_nonneg ( X ω ^ 2 - Y ω ^ 2 ) ] ⟩ ];
            · refine' MeasureTheory.Integrable.mono' _ _ _;
              exact fun ω => X ω ^ 4 + Y ω ^ 4;
              · exact hX4.add hY4;
              · exact MeasureTheory.AEStronglyMeasurable.mul ( hX.pow 3 ) hY;
              · filter_upwards [ ] with ω using abs_le.mpr ⟨ by nlinarith only [ sq_nonneg ( X ω ^ 2 - Y ω ^ 2 ), sq_nonneg ( X ω * Y ω - X ω ^ 2 ), sq_nonneg ( X ω * Y ω + X ω ^ 2 ) ], by nlinarith only [ sq_nonneg ( X ω ^ 2 - Y ω ^ 2 ), sq_nonneg ( X ω * Y ω - X ω ^ 2 ), sq_nonneg ( X ω * Y ω + X ω ^ 2 ) ] ⟩;
          · exact hY4;
          · apply_rules [ MeasureTheory.Integrable.add, MeasureTheory.Integrable.mul_const, hX4, hY4 ];
            · refine' MeasureTheory.Integrable.mono' _ _ _;
              exacts [ fun ω => X ω ^ 4 + Y ω ^ 4, by exact MeasureTheory.Integrable.add hX4 hY4, by exact hX.pow 2 |> AEStronglyMeasurable.mul <| hY.pow 2, Filter.Eventually.of_forall fun ω => abs_le.mpr ⟨ by nlinarith only [ sq_nonneg ( X ω ^ 2 - Y ω ^ 2 ) ], by nlinarith only [ sq_nonneg ( X ω ^ 2 - Y ω ^ 2 ) ] ⟩ ];
            · refine' MeasureTheory.Integrable.mono' _ _ _;
              exact fun ω => X ω ^ 4 + Y ω ^ 4;
              · exact hX4.add hY4;
              · exact MeasureTheory.AEStronglyMeasurable.mul ( hX.pow 3 ) hY;
              · filter_upwards [ ] with ω using abs_le.mpr ⟨ by nlinarith only [ sq_nonneg ( X ω ^ 2 - Y ω ^ 2 ), sq_nonneg ( X ω * Y ω - X ω ^ 2 ), sq_nonneg ( X ω * Y ω + X ω ^ 2 ) ], by nlinarith only [ sq_nonneg ( X ω ^ 2 - Y ω ^ 2 ), sq_nonneg ( X ω * Y ω - X ω ^ 2 ), sq_nonneg ( X ω * Y ω + X ω ^ 2 ) ] ⟩;
          · refine' MeasureTheory.Integrable.mul_const _ _;
            refine' MeasureTheory.Integrable.mono' _ _ _;
            refine' fun ω => X ω ^ 4 + Y ω ^ 4;
            · exact hX4.add hY4;
            · exact hX.mul ( hY.pow 3 );
            · filter_upwards [ ] with ω using abs_le.mpr ⟨ by nlinarith only [ sq_nonneg ( X ω ^ 2 - Y ω ^ 2 ), sq_nonneg ( X ω - Y ω ), sq_nonneg ( X ω + Y ω ) ], by nlinarith only [ sq_nonneg ( X ω ^ 2 - Y ω ^ 2 ), sq_nonneg ( X ω - Y ω ), sq_nonneg ( X ω + Y ω ) ] ⟩;
        · refine' hX4.add _;
          refine' MeasureTheory.Integrable.const_mul _ _;
          refine' MeasureTheory.Integrable.mono' _ _ _;
          exact fun ω => X ω ^ 4 + Y ω ^ 4;
          · exact hX4.add hY4;
          · exact MeasureTheory.AEStronglyMeasurable.mul ( hX.pow 3 ) hY;
          · filter_upwards [ ] with ω using abs_le.mpr ⟨ by nlinarith only [ sq_nonneg ( X ω ^ 2 - Y ω ^ 2 ), sq_nonneg ( X ω - Y ω ), sq_nonneg ( X ω + Y ω ) ], by nlinarith only [ sq_nonneg ( X ω ^ 2 - Y ω ^ 2 ), sq_nonneg ( X ω - Y ω ), sq_nonneg ( X ω + Y ω ) ] ⟩;
        · refine' MeasureTheory.Integrable.const_mul _ _;
          refine' MeasureTheory.Integrable.mono' _ _ _;
          refine' fun ω => X ω ^ 4 + Y ω ^ 4;
          · exact hX4.add hY4;
          · exact MeasureTheory.AEStronglyMeasurable.mul ( hX.pow 2 ) ( hY.pow 2 );
          · filter_upwards [ ] with ω using abs_le.mpr ⟨ by nlinarith only [ sq_nonneg ( X ω ^ 2 - Y ω ^ 2 ) ], by nlinarith only [ sq_nonneg ( X ω ^ 2 - Y ω ^ 2 ) ] ⟩;
        · exact hX4;
        · refine' MeasureTheory.Integrable.const_mul _ _;
          refine' MeasureTheory.Integrable.mono' _ _ _;
          exact fun ω => X ω ^ 4 + Y ω ^ 4;
          · exact hX4.add hY4;
          · exact MeasureTheory.AEStronglyMeasurable.mul ( hX.pow 3 ) hY;
          · filter_upwards [ ] with ω using abs_le.mpr ⟨ by nlinarith only [ sq_nonneg ( X ω ^ 2 - Y ω ^ 2 ), sq_nonneg ( X ω - Y ω ), sq_nonneg ( X ω + Y ω ) ], by nlinarith only [ sq_nonneg ( X ω ^ 2 - Y ω ^ 2 ), sq_nonneg ( X ω - Y ω ), sq_nonneg ( X ω + Y ω ) ] ⟩;
      have h_indep_terms : ∫ ω, X ω^3 * Y ω ∂P = 0 ∧ ∫ ω, X ω * Y ω^3 ∂P = 0 ∧ ∫ ω, X ω^2 * Y ω^2 ∂P = (∫ ω, X ω^2 ∂P) * (∫ ω, Y ω^2 ∂P) := by
        apply_rules [ And.intro, expectation_pow_three_mul_eq_zero, expectation_sq_mul_sq_eq_mul_expectation_sq ];
        have h_indep_prod : ∫ ω, X ω * Y ω ^ 3 ∂P = (∫ ω, X ω ∂P) * (∫ ω, Y ω ^ 3 ∂P) := by
          apply_rules [ ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral ];
          · exact h_indep.comp ( measurable_id' ) ( measurable_id'.pow_const 3 );
          · exact hY.pow 3;
        aesop;
      aesop

/-
The sum of a subset of independent variables is independent of a variable not in the subset.
-/
lemma indep_sum_of_not_mem {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ι : Type*} [DecidableEq ι]
    (ξ : ι → Ω → ℝ)
    (h_indep : iIndepFun ξ P)
    (h_meas : ∀ i, Measurable (ξ i))
    (s : Finset ι) (a : ι) (ha : a ∉ s) :
    IndepFun (∑ i ∈ s, ξ i) (ξ a) P := by
      have h_sum_ind : IndepFun (fun ω => ∑ i ∈ s, ξ i ω) (ξ a) P := by
        have h_sum_meas : ∀ (s : Finset ι), Measurable (fun ω => ∑ i ∈ s, ξ i ω) := by
          exact fun s => Finset.measurable_sum _ fun i _ => h_meas i
        have := h_indep.indepFun_finset s { a } ; simp_all +decide [ iIndepFun ] ;
        rw [ ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul ] at *;
        intro s_1 t hs_1 ht; specialize this ( ( fun f => ∑ i : s, f i ) ⁻¹' s_1 ) ( ( fun f => f ⟨ a, by simp +decide ⟩ ) ⁻¹' t ) ; simp_all +decide [ Set.preimage ] ;
        convert this _ _;
        · conv_lhs => rw [ ← Finset.sum_attach ] ;
        · conv_lhs => rw [ ← Finset.sum_attach ] ;
        · exact MeasurableSet.mem ( hs_1.preimage ( Finset.measurable_sum _ fun i _ => measurable_pi_apply i ) );
        · exact measurableSet_preimage ( measurable_pi_apply _ ) ht |> MeasurableSet.mem;
      convert h_sum_ind using 1;
      exact sum_fn s ξ

/-
The second moment of a sum of independent Rademacher variables over a Finset is equal to the cardinality of the Finset.
-/
lemma second_moment_rademacher_sum_finset {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ι : Type*} [DecidableEq ι]
    (ξ : ι → Ω → ℝ)
    (h_indep : iIndepFun ξ P)
    (h_rad : ∀ i, IsRademacher P (ξ i))
    (s : Finset ι) :
    ∫ ω, (∑ i ∈ s, ξ i ω)^2 ∂P = s.card := by
      -- Apply the lemma for the second moment of a sum of independent Rademacher variables over a Finset.
      have h_second_moment : ∫ ω, (∑ i ∈ s, ξ i ω)^2 ∂P = ∑ i ∈ s, ∫ ω, (ξ i ω)^2 ∂P := by
        -- Apply the independence of the Rademacher variables to split the integral.
        have h_split : ∫ ω, (∑ i ∈ s, ξ i ω) ^ 2 ∂P = ∑ i ∈ s, ∑ j ∈ s, ∫ ω, ξ i ω * ξ j ω ∂P := by
          simp +decide only [sq, Finset.mul_sum _ _ _, sum_mul];
          rw [ MeasureTheory.integral_finset_sum ];
          · rw [ Finset.sum_congr rfl fun i hi => MeasureTheory.integral_finset_sum _ _ ];
            · ac_rfl;
            · intro i hi j hj;
              field_simp;
              refine' MeasureTheory.Integrable.mono' _ _ _;
              refine' fun ω => ( ξ j ω ) ^ 2 + ( ξ i ω ) ^ 2;
              · exact MeasureTheory.Integrable.add ( by exact ( rademacher_props ( h_rad j ) ) |>.2.2.1 ) ( by exact ( rademacher_props ( h_rad i ) ) |>.2.2.1 );
              · exact MeasureTheory.AEStronglyMeasurable.mul ( h_rad j |>.1.aestronglyMeasurable ) ( h_rad i |>.1.aestronglyMeasurable );
              · filter_upwards [ ] with ω using abs_le.mpr ⟨ by nlinarith only, by nlinarith only ⟩;
          · intro i hi;
            refine' MeasureTheory.integrable_finset_sum _ fun j hj => _;
            refine' MeasureTheory.Integrable.mono' _ _ _;
            exact fun ω => ( ξ j ω ) ^ 2 + ( ξ i ω ) ^ 2;
            · exact MeasureTheory.Integrable.add ( by exact ( rademacher_props ( h_rad j ) ) |>.2.2.1 ) ( by exact ( rademacher_props ( h_rad i ) ) |>.2.2.1 );
            · exact MeasureTheory.AEStronglyMeasurable.mul ( h_rad j |>.1.aestronglyMeasurable ) ( h_rad i |>.1.aestronglyMeasurable );
            · filter_upwards [ ] with ω using abs_le.mpr ⟨ by nlinarith only, by nlinarith only ⟩;
        -- Since $\xi_i$ and $\xi_j$ are independent Rademacher variables, $\mathbb{E}[\xi_i \xi_j] = 0$ for $i \neq j$.
        have h_cross_terms : ∀ i j, i ≠ j → ∫ ω, ξ i ω * ξ j ω ∂P = 0 := by
          -- Since ξ i and ξ j are independent and each has expectation zero, the expectation of their product is zero.
          have h_indep_zero : ∀ i j, i ≠ j → ∫ ω, ξ i ω * ξ j ω ∂P = (∫ ω, ξ i ω ∂P) * (∫ ω, ξ j ω ∂P) := by
            intro i j hij;
            apply_rules [ ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral ];
            · exact h_indep.indepFun hij;
            · exact ( h_rad i ).1.aestronglyMeasurable;
            · exact h_rad j |>.1.aestronglyMeasurable;
          exact fun i j hij => h_indep_zero i j hij ▸ by simp +decide [ show ∫ ω, ξ i ω ∂P = 0 from ( rademacher_props ( h_rad i ) ) |>.2.1, show ∫ ω, ξ j ω ∂P = 0 from ( rademacher_props ( h_rad j ) ) |>.2.1 ] ;
        simp_all +decide [ sq ];
        exact Finset.sum_congr rfl fun i hi => by rw [ Finset.sum_eq_single i ] <;> aesop;
      have h_second_moment : ∀ i ∈ s, ∫ ω, (ξ i ω)^2 ∂P = 1 := by
        exact fun i hi => ( rademacher_props ( h_rad i ) ) |>.2.2.2.1;
      aesop

/-
The fourth moment of a sum of independent Rademacher variables over a Finset is 3*card^2 - 2*card.
-/
lemma fourth_moment_rademacher_sum_finset {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ι : Type*} [DecidableEq ι]
    (ξ : ι → Ω → ℝ)
    (h_indep : iIndepFun ξ P)
    (h_rad : ∀ i, IsRademacher P (ξ i))
    (s : Finset ι) :
    ∫ ω, (∑ i ∈ s, ξ i ω)^4 ∂P = 3 * (s.card : ℝ)^2 - 2 * (s.card : ℝ) := by
      induction' s using Finset.induction with a s ha ih generalizing P;
      · norm_num;
      · -- Apply the lemma about the fourth moment of the sum of independent variables.
        have h_sum_fourth_moment_step : ∫ ω, (∑ i ∈ insert a s, ξ i ω)^4 ∂P = ∫ ω, (∑ i ∈ s, ξ i ω)^4 ∂P + 6 * ∫ ω, (∑ i ∈ s, ξ i ω)^2 ∂P + 1 := by
          have h_sum_fourth_moment_step : ∫ ω, ((∑ i ∈ s, ξ i ω) + ξ a ω)^4 ∂P = ∫ ω, (∑ i ∈ s, ξ i ω)^4 ∂P + 6 * ∫ ω, (∑ i ∈ s, ξ i ω)^2 ∂P + 1 := by
            have h_exp : ∫ ω, (∑ i ∈ s, ξ i ω + ξ a ω)^4 ∂P = ∫ ω, (∑ i ∈ s, ξ i ω)^4 ∂P + 6 * ∫ ω, (∑ i ∈ s, ξ i ω)^2 ∂P + 1 := by
              have h_indep_X_Y : IndepFun (∑ i ∈ s, ξ i) (ξ a) P := by
                apply_rules [ indep_sum_of_not_mem ];
                exact fun i => ( h_rad i ).1
              have hX_meas : Measurable (∑ i ∈ s, ξ i) := by
                have h_meas : ∀ i, Measurable (ξ i) := by
                  intro i; specialize h_rad i; exact h_rad.1;
                fun_prop
              have hY_meas : Measurable (ξ a) := by
                exact h_rad a |>.1
              have hX4 : Integrable (fun ω => (∑ i ∈ s, ξ i ω)^4) P := by
                by_contra h_contra;
                have := @ih P;
                rw [ MeasureTheory.integral_undef h_contra ] at this;
                rcases s with ⟨ ⟨ l, hl ⟩ ⟩ <;> norm_num at *;
                exact absurd ( this h_indep h_rad ) ( by ring_nf; nlinarith )
              have hY4 : Integrable (fun ω => (ξ a ω)^4) P := by
                exact ( rademacher_props ( h_rad a ) ) |>.2.2.2.2.1
              have hY_mean : ∫ ω, ξ a ω ∂P = 0 := by
                exact rademacher_props ( h_rad a ) |>.2.1
              have hY_sq_mean : ∫ ω, (ξ a ω)^2 ∂P = 1 := by
                have := h_rad a;
                have := rademacher_props this; aesop;
              have hY_cube_mean : ∫ ω, (ξ a ω)^3 ∂P = 0 := by
                have := h_rad a;
                cases' this with h₁ h₂;
                have hY_cube_mean : ∫ ω, (ξ a ω)^3 ∂P = ∫ ω in {ω | ξ a ω = 1}, (ξ a ω)^3 ∂P + ∫ ω in {ω | ξ a ω = -1}, (ξ a ω)^3 ∂P := by
                  rw [ ← MeasureTheory.setIntegral_union ];
                  · rw [ MeasureTheory.Measure.restrict_eq_self_of_ae_mem ];
                    have := h_rad a;
                    have := this.1;
                    have hY_cube_mean : P {ω | ξ a ω ≠ 1 ∧ ξ a ω ≠ -1} = 0 := by
                      have hY_cube_mean : P {ω | ξ a ω ≠ 1 ∧ ξ a ω ≠ -1} ≤ P {ω | ξ a ω ≠ 1} - P {ω | ξ a ω = -1} := by
                        rw [ ← MeasureTheory.measure_diff ];
                        · exact MeasureTheory.measure_mono fun x hx => by aesop;
                        · exact fun x hx => by norm_num [ hx.out ] ;
                        · exact this ( MeasurableSingletonClass.measurableSet_singleton _ ) |> MeasurableSet.nullMeasurableSet;
                        · exact ne_of_lt ( MeasureTheory.measure_lt_top _ _ );
                      have hY_cube_mean : P {ω | ξ a ω ≠ 1} = 1 - P {ω | ξ a ω = 1} := by
                        rw [ show { ω | ξ a ω ≠ 1 } = ( Set.univ \ { ω | ξ a ω = 1 } ) by ext; simp +decide, MeasureTheory.measure_diff ] <;> norm_num;
                        exact this.nullMeasurable ( MeasurableSingletonClass.measurableSet_singleton _ );
                      aesop;
                    filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hY_cube_mean ] with ω hω using by contrapose! hω; aesop;
                  · exact Set.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ hx₁.symm, hx₂.symm ] ;
                  · exact h₁ ( MeasurableSingletonClass.measurableSet_singleton _ );
                  · refine' MeasureTheory.Integrable.integrableOn _;
                    refine' MeasureTheory.Integrable.mono' _ _ _;
                    use fun ω => ξ a ω ^ 4 + 1;
                    · exact hY4.add ( MeasureTheory.integrable_const _ );
                    · exact h₁.pow_const 3 |> Measurable.aestronglyMeasurable;
                    · filter_upwards [ ] with ω using abs_le.mpr ⟨ by nlinarith only [ sq_nonneg ( ξ a ω ^ 2 - 1 ), sq_nonneg ( ξ a ω + 1 ) ], by nlinarith only [ sq_nonneg ( ξ a ω ^ 2 - 1 ), sq_nonneg ( ξ a ω - 1 ) ] ⟩;
                  · refine' MeasureTheory.Integrable.mono' _ _ _;
                    use fun ω => ( ξ a ω ) ^ 4 + 1;
                    · exact MeasureTheory.Integrable.add ( hY4.integrableOn ) ( MeasureTheory.integrable_const _ );
                    · exact h₁.pow_const 3 |> Measurable.aestronglyMeasurable;
                    · filter_upwards [ MeasureTheory.ae_restrict_mem ( show MeasurableSet { ω | ξ a ω = -1 } from h₁ ( MeasurableSingletonClass.measurableSet_singleton _ ) ) ] with ω hω using by rw [ hω ] ; norm_num;
                rw [ hY_cube_mean, MeasureTheory.setIntegral_congr_fun ( show MeasurableSet { ω | ξ a ω = 1 } from h₁ ( MeasurableSingletonClass.measurableSet_singleton _ ) ) fun x hx => by aesop, MeasureTheory.setIntegral_congr_fun ( show MeasurableSet { ω | ξ a ω = -1 } from h₁ ( MeasurableSingletonClass.measurableSet_singleton _ ) ) fun x hx => by aesop ] ; norm_num [ h₂ ];
                norm_num [ MeasureTheory.measureReal_def, h₂ ]
              have hY_four_mean : ∫ ω, (ξ a ω)^4 ∂P = 1 := by
                have := h_rad a;
                have := rademacher_props this;
                exact this.2.2.2.2.2
              convert expectation_add_pow_four h_indep_X_Y _ _ _ _ _ _ _ using 1;
              all_goals norm_num [ hY_mean, hY_sq_mean, hY_cube_mean, hY_four_mean ];
              · exact hX_meas.aestronglyMeasurable;
              · exact hY_meas.aestronglyMeasurable;
              · exact hX4;
              · exact hY4;
            exact h_exp;
          grind;
        have := @second_moment_rademacher_sum_finset Ω _ P _ ι _ ξ h_indep h_rad s; simp_all +decide [ Finset.sum_insert ha ] ; ring;

/-
Lower bound on the first absolute moment of a Rademacher sum using Paley-Zygmund.
-/
lemma abs_rademacher_sum_lower_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ι : Type*} [DecidableEq ι]
    (ξ : ι → Ω → ℝ)
    (h_indep : iIndepFun ξ P)
    (h_rad : ∀ i, IsRademacher P (ξ i))
    (s : Finset ι) :
    ∫ ω, |∑ i ∈ s, ξ i ω| ∂P ≥ (1 / (12 * Real.sqrt 2)) * Real.sqrt s.card := by
      -- Apply the Paley-Zygmund inequality to $Y = U^2$ with $\theta = 1/2$.
      have h_paley_zygmund : P {ω | (∑ i ∈ s, ξ i ω)^2 ≥ (1 / 2) * (s.card : ℝ)} ≥ ENNReal.ofReal ((1 - (1 / 2))^2 * (s.card : ℝ)^2 / (3 * (s.card : ℝ)^2 - 2 * (s.card : ℝ))) := by
        -- Let $Y = U^2$. We need to show that $Y$ is non-negative and integrable.
        set Y : Ω → ℝ := fun ω => (∑ i ∈ s, ξ i ω)^2
        have hY_nonneg : 0 ≤ Y := by
          exact fun ω => sq_nonneg _
        have hY_int : Integrable Y P := by
          have hY_integrable : ∀ i ∈ s, Integrable (fun ω => (ξ i ω)^2) P := by
            exact fun i hi => ( h_rad i ) |>.1 |> fun h => by have := rademacher_props ( h_rad i ) ; aesop;
          have hY_integrable : ∀ i j : ι, i ∈ s → j ∈ s → Integrable (fun ω => ξ i ω * ξ j ω) P := by
            intro i j hi hj;
            refine' MeasureTheory.Integrable.mono' _ _ _;
            exact fun ω => ( ξ i ω ) ^ 2 + ( ξ j ω ) ^ 2;
            · exact MeasureTheory.Integrable.add ( hY_integrable i hi ) ( hY_integrable j hj );
            · have := h_rad i;
              have := this.1;
              exact this.aestronglyMeasurable.mul ( h_rad j |>.1.aestronglyMeasurable );
            · filter_upwards [ ] with ω using abs_le.mpr ⟨ by nlinarith only, by nlinarith only ⟩;
          simp +zetaDelta at *;
          simp +decide only [sq, Finset.sum_mul _ _ _, mul_sum];
          exact MeasureTheory.integrable_finset_sum _ fun i hi => MeasureTheory.integrable_finset_sum _ fun j hj => hY_integrable i j hi hj
        have hY_sq_int : Integrable (fun ω => Y ω^2) P := by
          have := fourth_moment_rademacher_sum_finset ξ h_indep h_rad s;
          simp +zetaDelta at *;
          norm_num [ ← pow_mul ] at *;
          exact ( by contrapose! this; rw [ MeasureTheory.integral_undef this ] ; nlinarith [ show ( s.card : ℝ ) ≥ 0 by positivity, show ( s.card : ℝ ) ≥ 1 by norm_cast; exact Nat.succ_le_of_lt ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ] );
        have h_paley_zygmund : P {ω | Y ω ≥ (1 / 2) * (∫ ω, Y ω ∂P)} ≥ ENNReal.ofReal ((1 - (1 / 2))^2 * (∫ ω, Y ω ∂P)^2 / (∫ ω, Y ω^2 ∂P)) := by
          apply paley_zygmund_inequality hY_nonneg hY_int hY_sq_int (1 / 2) (by norm_num) (by norm_num);
        convert h_paley_zygmund using 3;
        · rw [ show ∫ ω, Y ω ∂P = s.card from ?_ ];
          exact second_moment_rademacher_sum_finset ξ h_indep h_rad s;
        · rw [ show ∫ ω, Y ω ∂P = s.card from ?_ ];
          exact second_moment_rademacher_sum_finset ξ h_indep h_rad s;
        · convert fourth_moment_rademacher_sum_finset ξ h_indep h_rad s |> Eq.symm using 1;
          exact congr_arg _ ( funext fun ω => by ring );
      -- On the event $Y \ge m/2$, $|U| = \sqrt{Y} \ge \sqrt{m/2}$.
      have h_event : ∫ ω in {ω | (∑ i ∈ s, ξ i ω)^2 ≥ (1 / 2) * (s.card : ℝ)}, |∑ i ∈ s, ξ i ω| ∂P ≥ (1 / 12) * Real.sqrt ((s.card : ℝ) / 2) := by
        have h_event : ∫ ω in {ω | (∑ i ∈ s, ξ i ω)^2 ≥ (1 / 2) * (s.card : ℝ)}, |∑ i ∈ s, ξ i ω| ∂P ≥ ∫ ω in {ω | (∑ i ∈ s, ξ i ω)^2 ≥ (1 / 2) * (s.card : ℝ)}, Real.sqrt ((1 / 2) * (s.card : ℝ)) ∂P := by
          refine' MeasureTheory.setIntegral_mono_on _ _ _ _ <;> norm_num;
          · exact MeasureTheory.integrable_const _;
          · -- The sum of Rademacher variables is bounded, hence integrable.
            have h_sum_integrable : Integrable (fun ω => ∑ i ∈ s, ξ i ω) P := by
              refine' MeasureTheory.integrable_finset_sum _ fun i _ => _;
              exact ( h_rad i ).1 |> fun h => by have := rademacher_props ( h_rad i ) ; exact this.1;
            exact h_sum_integrable.abs.integrableOn;
          · have h_measurable : ∀ i, Measurable (ξ i) := by
              intro i; specialize h_rad i; exact h_rad.1;
            exact measurableSet_Ici.mem.comp ( Measurable.pow_const ( Finset.measurable_sum _ fun i _ => h_measurable i ) _ );
          · intro ω hω; rw [ ← Real.sqrt_inv, ← Real.sqrt_mul ( by positivity ) ] ; exact Real.sqrt_le_iff.mpr ⟨ by positivity, by simpa [ abs_mul ] using hω ⟩ ;
        refine' le_trans _ h_event;
        by_cases hs : s = ∅ <;> simp_all +decide;
        refine' le_trans _ ( mul_le_mul_of_nonneg_right ( show P.real { ω | 2⁻¹ * ↑ ( #s ) ≤ ( ∑ i ∈ s, ξ i ω ) ^ 2 } ≥ 1 / 12 by
                                                            refine' le_trans _ ( ENNReal.toReal_mono _ h_paley_zygmund );
                                                            · rw [ ENNReal.toReal_ofReal ] <;> norm_num;
                                                              · rw [ le_div_iff₀ ] <;> nlinarith only [ show ( s.card : ℝ ) ≥ 1 by exact_mod_cast Finset.card_pos.mpr ( Finset.nonempty_of_ne_empty hs ) ];
                                                              · exact div_nonneg ( by positivity ) ( sub_nonneg_of_le ( by nlinarith only [ show ( s.card : ℝ ) ≥ 1 by exact_mod_cast Finset.card_pos.mpr ( Finset.nonempty_of_ne_empty hs ) ] ) );
                                                            · exact MeasureTheory.measure_ne_top _ _ ) ( by positivity ) ) ; ring_nf ; norm_num;
      refine' le_trans _ ( h_event.trans ( MeasureTheory.setIntegral_le_integral _ _ ) );
      · norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
      · refine' MeasureTheory.Integrable.abs _;
        refine' MeasureTheory.integrable_finset_sum _ _;
        exact fun i _ => ( h_rad i ).1 |> fun h => by have := rademacher_props ( h_rad i ) ; aesop;
      · exact Filter.Eventually.of_forall fun ω => abs_nonneg _

/-
Identity relating the bilinear form x^T A y to sums over rectangles defined by the signs of x and y.
-/
lemma rectangle_identity {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ)
    (hx : ∀ i, x i = 1 ∨ x i = -1) (hy : ∀ j, y j = 1 ∨ y j = -1) :
    let S := {i | x i = 1}
    let T := {j | y j = 1}
    let R (P Q : Set (Fin n)) := ∑ i ∈ univ.filter (fun i => i ∈ P), ∑ j ∈ univ.filter (fun j => j ∈ Q), A i j
    ∑ i, ∑ j, x i * A i j * y j = R S T + R Sᶜ Tᶜ - R S Tᶜ - R Sᶜ T := by
      -- We can split the sum into four parts based on the signs of $x_i$ and $y_j$.
      have h_split : ∀ i j, x i * y j = (if x i = 1 then 1 else -1) * (if y j = 1 then 1 else -1) := by
        intro i j; rcases hx i with ha | ha <;> rcases hy j with hb | hb <;> norm_num [ ha, hb ] ;
      simp +decide [ Finset.sum_ite, Finset.filter_not, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_comm, mul_left_comm, h_split ];
      ring

/-
From a large rectangle sum to a large induced sum (diagonal sum).
-/
lemma rect_to_induced {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h_symm : A.IsSymm)
    (P Q : Finset (Fin n))
    (M : ℝ)
    (h_rect : |∑ i ∈ P, ∑ j ∈ Q, A i j| ≥ M) :
    ∃ X : Finset (Fin n), |∑ i ∈ X, ∑ j ∈ X, A i j| ≥ M / 48 := by
      revert h_rect;
      intro hM
      set A0 := P ∩ Q
      set B := P \ Q
      set C := Q \ P
      have h_sum : ∑ i ∈ P, ∑ j ∈ Q, A i j = ∑ i ∈ A0, ∑ j ∈ A0, A i j + ∑ i ∈ B, ∑ j ∈ A0, A i j + ∑ i ∈ A0, ∑ j ∈ C, A i j + ∑ i ∈ B, ∑ j ∈ C, A i j := by
        have h_expand : ∑ i ∈ P, ∑ j ∈ Q, A i j = ∑ i ∈ A0 ∪ B, ∑ j ∈ A0 ∪ C, A i j := by
          rw [ show A0 ∪ B = P by ext i; by_cases hi : i ∈ Q <;> aesop, show A0 ∪ C = Q by ext i; by_cases hi : i ∈ P <;> aesop ];
        rw [ h_expand, Finset.sum_union ];
        · rw [ Finset.sum_congr rfl fun i hi => Finset.sum_union <| Finset.disjoint_right.mpr fun j hj => by aesop, Finset.sum_congr rfl fun i hi => Finset.sum_union <| Finset.disjoint_right.mpr fun j hj => by aesop ] ; ring_nf;
          simpa only [ Finset.sum_add_distrib ] using by ring;
        · exact Finset.disjoint_left.mpr fun x => by aesop;
      -- Thus one of the terms is $\ge M/4$.
      have h_term : |∑ i ∈ A0, ∑ j ∈ A0, A i j| ≥ M / 4 ∨ |∑ i ∈ B, ∑ j ∈ A0, A i j| ≥ M / 4 ∨ |∑ i ∈ A0, ∑ j ∈ C, A i j| ≥ M / 4 ∨ |∑ i ∈ B, ∑ j ∈ C, A i j| ≥ M / 4 := by
        contrapose! hM; cases abs_cases ( ∑ i ∈ P, ∑ j ∈ Q, A i j ) <;> cases abs_cases ( ∑ i ∈ A0, ∑ j ∈ A0, A i j ) <;> cases abs_cases ( ∑ i ∈ B, ∑ j ∈ A0, A i j ) <;> cases abs_cases ( ∑ i ∈ A0, ∑ j ∈ C, A i j ) <;> cases abs_cases ( ∑ i ∈ B, ∑ j ∈ C, A i j ) <;> linarith;
      rcases h_term with h | h | h | h;
      · exact ⟨ A0, by linarith [ abs_nonneg ( ∑ i ∈ A0, ∑ j ∈ A0, A i j ) ] ⟩;
      · -- Let $U = B$ and $V = A0$. Since $B$ and $A0$ are disjoint, we have $R(U \cup V, U \cup V) = R(U, U) + R(V, V) + R(U, V) + R(V, U)$.
        set U := B
        set V := A0
        have h_union : ∑ i ∈ U ∪ V, ∑ j ∈ U ∪ V, A i j = ∑ i ∈ U, ∑ j ∈ U, A i j + ∑ i ∈ V, ∑ j ∈ V, A i j + ∑ i ∈ U, ∑ j ∈ V, A i j + ∑ i ∈ V, ∑ j ∈ U, A i j := by
          rw [ Finset.sum_union ];
          · rw [ Finset.sum_congr rfl fun i hi => Finset.sum_union <| Finset.disjoint_left.mpr fun j hj₁ hj₂ => by aesop, Finset.sum_congr rfl fun i hi => Finset.sum_union <| Finset.disjoint_left.mpr fun j hj₁ hj₂ => by aesop ] ; ring_nf;
            simpa only [ Finset.sum_add_distrib ] using by ring;
          · exact Finset.disjoint_left.mpr fun x => by aesop;
        -- Since $A$ is symmetric, $R(V, U) = R(U, V)$.
        have h_symm_union : ∑ i ∈ V, ∑ j ∈ U, A i j = ∑ i ∈ U, ∑ j ∈ V, A i j := by
          rw [ Finset.sum_comm ];
          exact Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => h_symm.apply _ _ ▸ rfl;
        contrapose! h;
        exact abs_lt.mpr ⟨ by linarith [ abs_lt.mp ( h ( U ∪ V ) ), abs_lt.mp ( h U ), abs_lt.mp ( h V ) ], by linarith [ abs_lt.mp ( h ( U ∪ V ) ), abs_lt.mp ( h U ), abs_lt.mp ( h V ) ] ⟩;
      · -- Let $U = A0$ and $V = C$. $U$ and $V$ are disjoint.
        set U := A0
        set V := C
        have h_disjoint : Disjoint U V := by
          exact Finset.disjoint_left.mpr fun x hxU hxV => Finset.mem_sdiff.mp hxV |>.2 <| Finset.mem_inter.mp hxU |>.1;
        -- Since $A$ is symmetric, $R(V, U) = R(U, V)$.
        have h_symm_UV : ∑ i ∈ V, ∑ j ∈ U, A i j = ∑ i ∈ U, ∑ j ∈ V, A i j := by
          exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => h_symm.apply i j ▸ rfl );
        -- Thus $2 |R(U, V)| \le |R(U \cup V, U \cup V)| + |R(U, U)| + |R(V, V)|$.
        have h_bound : 2 * |∑ i ∈ U, ∑ j ∈ V, A i j| ≤ |∑ i ∈ U ∪ V, ∑ j ∈ U ∪ V, A i j| + |∑ i ∈ U, ∑ j ∈ U, A i j| + |∑ i ∈ V, ∑ j ∈ V, A i j| := by
          have h_bound : ∑ i ∈ U ∪ V, ∑ j ∈ U ∪ V, A i j = ∑ i ∈ U, ∑ j ∈ U, A i j + ∑ i ∈ V, ∑ j ∈ V, A i j + ∑ i ∈ U, ∑ j ∈ V, A i j + ∑ i ∈ V, ∑ j ∈ U, A i j := by
            simp +decide [ Finset.sum_union h_disjoint, Finset.sum_add_distrib ] ; ring;
          cases abs_cases ( ∑ i ∈ U, ∑ j ∈ V, A i j ) <;> cases abs_cases ( ∑ i ∈ U ∪ V, ∑ j ∈ U ∪ V, A i j ) <;> cases abs_cases ( ∑ i ∈ U, ∑ j ∈ U, A i j ) <;> cases abs_cases ( ∑ i ∈ V, ∑ j ∈ V, A i j ) <;> linarith;
        contrapose! h_bound;
        linarith [ h_bound ( U ∪ V ), h_bound U, h_bound V, abs_nonneg ( ∑ i ∈ U, ∑ j ∈ V, A i j ) ];
      · -- Thus $\max(|R(U \cup V, U \cup V)|, |R(U, U)|, |R(V, V)|) \ge M/6$.
        have h_max : max (|∑ i ∈ B ∪ C, ∑ j ∈ B ∪ C, A i j|) (max (|∑ i ∈ B, ∑ j ∈ B, A i j|) (|∑ i ∈ C, ∑ j ∈ C, A i j|)) ≥ M / 6 := by
          have h_max : 2 * |∑ i ∈ B, ∑ j ∈ C, A i j| ≤ |∑ i ∈ B ∪ C, ∑ j ∈ B ∪ C, A i j| + |∑ i ∈ B, ∑ j ∈ B, A i j| + |∑ i ∈ C, ∑ j ∈ C, A i j| := by
            have h_max : ∑ i ∈ B ∪ C, ∑ j ∈ B ∪ C, A i j = ∑ i ∈ B, ∑ j ∈ B, A i j + ∑ i ∈ C, ∑ j ∈ C, A i j + 2 * ∑ i ∈ B, ∑ j ∈ C, A i j := by
              rw [ Finset.sum_union ];
              · rw [ Finset.sum_congr rfl fun i hi => Finset.sum_union <| Finset.disjoint_left.mpr fun j hj₁ hj₂ => by aesop, Finset.sum_congr rfl fun i hi => Finset.sum_union <| Finset.disjoint_left.mpr fun j hj₁ hj₂ => by aesop ] ; ring_nf;
                simp +decide [ Finset.sum_add_distrib, mul_two, add_comm, add_left_comm, Finset.sum_mul _ _ _ ];
                exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => h_symm.apply _ _ );
              · exact disjoint_sdiff_sdiff;
            cases abs_cases ( ∑ i ∈ B, ∑ j ∈ C, A i j ) <;> cases abs_cases ( ∑ i ∈ B ∪ C, ∑ j ∈ B ∪ C, A i j ) <;> cases abs_cases ( ∑ i ∈ B, ∑ j ∈ B, A i j ) <;> cases abs_cases ( ∑ i ∈ C, ∑ j ∈ C, A i j ) <;> linarith;
          cases max_cases |∑ i ∈ B ∪ C, ∑ j ∈ B ∪ C, A i j| ( max |∑ i ∈ B, ∑ j ∈ B, A i j| |∑ i ∈ C, ∑ j ∈ C, A i j| ) <;> cases max_cases |∑ i ∈ B, ∑ j ∈ B, A i j| |∑ i ∈ C, ∑ j ∈ C, A i j| <;> linarith;
        contrapose! h_max;
        exact lt_of_le_of_lt ( max_le_iff.mpr ⟨ le_of_lt ( h_max _ ), max_le_iff.mpr ⟨ le_of_lt ( h_max _ ), le_of_lt ( h_max _ ) ⟩ ⟩ ) ( by linarith [ abs_lt.mp ( h_max ( B ∪ C ) ), abs_lt.mp ( h_max B ), abs_lt.mp ( h_max C ) ] )

/-
The uniform measure on the space of vertex colorings (vectors in {-1, 1}^n).
-/
noncomputable def vertexMeasure (n : ℕ) : Measure (Fin n → Bool) :=
  Measure.pi (fun _ => (PMF.uniformOfFintype Bool).toMeasure)

instance (n : ℕ) : IsProbabilityMeasure (vertexMeasure n) := by
  rw [vertexMeasure]
  infer_instance

/-
The coordinate variables of the uniform measure on the hypercube are independent.
-/
lemma vertex_measure_indep (n : ℕ) :
    let Ω := Fin n → Bool
    let P := vertexMeasure n
    let ξ (i : Fin n) (ω : Ω) : ℝ := if ω i then 1 else -1
    iIndepFun ξ P := by
      refine' ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul.mpr _;
      -- By definition of product measure, we can write the measure of the intersection as the product of the measures of the individual sets.
      have h_prod_measure : ∀ (S : Finset (Fin n)) {sets : Fin n → Set Bool}, (∀ i ∈ S, MeasurableSet (sets i)) → (Measure.pi (fun _ => (PMF.uniformOfFintype Bool).toMeasure)) (⋂ i ∈ S, (fun ω => ω i) ⁻¹' sets i) = ∏ i ∈ S, (Measure.pi (fun _ => (PMF.uniformOfFintype Bool).toMeasure)) ((fun ω => ω i) ⁻¹' sets i) := by
        intro S sets hsets;
        have h_prod_measure : ∀ (S : Finset (Fin n)) {sets : Fin n → Set Bool}, (∀ i ∈ S, MeasurableSet (sets i)) → (Measure.pi (fun _ => (PMF.uniformOfFintype Bool).toMeasure)) (⋂ i ∈ S, (fun ω => ω i) ⁻¹' sets i) = ∏ i ∈ S, (PMF.uniformOfFintype Bool).toMeasure (sets i) := by
          intro S sets hsets;
          have h_prod_measure : ∀ (S : Finset (Fin n)) {sets : Fin n → Set Bool}, (∀ i ∈ S, MeasurableSet (sets i)) → (Measure.pi (fun _ => (PMF.uniformOfFintype Bool).toMeasure)) (⋂ i ∈ S, (fun ω => ω i) ⁻¹' sets i) = ∏ i ∈ S, (PMF.uniformOfFintype Bool).toMeasure (sets i) := by
            intro S sets hsets
            have h_prod_measure : (Measure.pi (fun _ => (PMF.uniformOfFintype Bool).toMeasure)) (⋂ i ∈ S, (fun ω => ω i) ⁻¹' sets i) = (Measure.pi (fun _ => (PMF.uniformOfFintype Bool).toMeasure)) (Set.pi Set.univ (fun i => if i ∈ S then sets i else Set.univ)) := by
              congr with ω ; simp +decide [ Set.mem_iInter, Set.mem_preimage ];
              exact ⟨ fun h i => by by_cases hi : i ∈ S <;> simp +decide [ hi, h ], fun h i hi => by simpa [ hi ] using h i ⟩
            rw [ h_prod_measure, MeasureTheory.Measure.pi_pi ];
            rw [ ← Finset.prod_subset ( Finset.subset_univ S ) ] ; aesop;
            simp +contextual [ PMF.uniformOfFintype ];
            norm_num [ ENNReal.mul_inv_cancel ];
          exact h_prod_measure S hsets;
        have h_prod_measure : ∀ (i : Fin n), (Measure.pi (fun _ => (PMF.uniformOfFintype Bool).toMeasure)) ((fun ω => ω i) ⁻¹' sets i) = (PMF.uniformOfFintype Bool).toMeasure (sets i) := by
          intro i;
          specialize @h_prod_measure { i } ; aesop;
        aesop;
      intro S sets hsets;
      convert h_prod_measure S ( fun i hi => show MeasurableSet ( { b : Bool | ( if b then 1 else -1 : ℝ ) ∈ sets i } ) from ?_ ) using 1;
      exact trivial

/-
The coordinate variables of the uniform measure on the hypercube are Rademacher variables.
-/
lemma vertex_measure_rademacher (n : ℕ) (i : Fin n) :
    let Ω := Fin n → Bool
    let P := vertexMeasure n
    let ξ (i : Fin n) (ω : Ω) : ℝ := if ω i then 1 else -1
    IsRademacher P (ξ i) := by
      refine' ⟨ _, _, _ ⟩;
      · exact Measurable.ite ( measurableSet_eq_fun ( measurable_pi_apply i ) measurable_const ) measurable_const measurable_const;
      · unfold vertexMeasure;
        -- The set {ω | ω i = true} is a cylinder set, so its measure is the product of the measures of the individual coordinates.
        have h_cylinder : (Measure.pi fun _ : Fin n => (PMF.uniformOfFintype Bool).toMeasure) {ω : Fin n → Bool | ω i = true} = (PMF.uniformOfFintype Bool).toMeasure {true} * ∏ j ∈ Finset.univ.erase i, (PMF.uniformOfFintype Bool).toMeasure Set.univ := by
          have h_cylinder : (Measure.pi fun _ : Fin n => (PMF.uniformOfFintype Bool).toMeasure) (Set.pi Set.univ (fun j => if j = i then {true} else Set.univ)) = (PMF.uniformOfFintype Bool).toMeasure {true} * ∏ j ∈ Finset.univ.erase i, (PMF.uniformOfFintype Bool).toMeasure Set.univ := by
            rw [ MeasureTheory.Measure.pi_pi ];
            rw [ Finset.prod_eq_mul_prod_diff_singleton <| Finset.mem_univ i ];
            rw [ Finset.sdiff_singleton_eq_erase ];
            exact congr_arg₂ _ ( by simp +decide ) ( Finset.prod_congr rfl fun j hj => by aesop );
          convert h_cylinder using 2;
          grind;
        convert h_cylinder using 1 ; norm_num [ PMF.uniformOfFintype ];
        norm_num [ PMF.uniformOfFintype ];
        erw [ ENNReal.mul_inv_cancel ] <;> norm_num;
      · erw [ show { ω : Fin n → Bool | ( if ω i = true then ( 1 : ℝ ) else -1 ) = -1 } = ( Set.pi Set.univ fun j => if j = i then { false } else Set.univ ) from ?_ ];
        · -- The measure of the product of sets where each set is either {false} or Set.univ is the product of their measures.
          have h_measure : (vertexMeasure n) (Set.pi Set.univ fun j => if j = i then {false} else Set.univ) = ∏ j, (if j = i then 1 / 2 else 1) := by
            convert Measure.pi_pi _ _;
            · split_ifs <;> simp +decide [ *, PMF.uniformOfFintype ];
              rw [ ENNReal.mul_inv_cancel ] <;> norm_cast;
            · exact fun i => sigmaFinite_of_locallyFinite;
          aesop;
        · grind

/-
The expected absolute value of a row sum of A with random signs is at least C * sqrt(n-1).
-/
lemma expectation_abs_row_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h_diag : ∀ i, A i i = 0)
    (h_vals : ∀ i j, i ≠ j → A i j = 1 ∨ A i j = -1)
    (j : Fin n) :
    let P := vertexMeasure n
    let ξ (i : Fin n) (ω : Fin n → Bool) : ℝ := if ω i then 1 else -1
    ∫ ω, |∑ i, A j i * ξ i ω| ∂P ≥ (1 / (12 * Real.sqrt 2)) * Real.sqrt (n - 1) := by
      -- Let's simplify the expression inside the absolute value further.
      suffices h_simp'''' : ∫ ω, |∑ i ∈ Finset.univ.erase j, A j i * (if ω i then 1 else -1)| ∂vertexMeasure n ≥ (1 / (12 * Real.sqrt 2)) * Real.sqrt (n - 1) by
        simp_all +decide
      have h_simp''' : ∫ ω, |∑ i ∈ Finset.univ.erase j, (if A j i = 1 then 1 else -1) * (if ω i then 1 else -1)| ∂vertexMeasure n ≥ (1 / (12 * Real.sqrt 2)) * Real.sqrt (n - 1) := by
        have h_simp''' : ∫ ω, |∑ i ∈ Finset.univ.erase j, (if A j i = 1 then 1 else -1) * (if ω i then 1 else -1)| ∂vertexMeasure n ≥ (1 / (12 * Real.sqrt 2)) * Real.sqrt (Finset.card (Finset.univ.erase j)) := by
          apply_rules [ abs_rademacher_sum_lower_bound ];
          · have h_indep : iIndepFun (fun i ω => if ω i then 1 else -1 : Fin n → (Fin n → Bool) → ℝ) (vertexMeasure n) := by
              exact vertex_measure_indep n;
            rw [ iIndepFun_iff_measure_inter_preimage_eq_mul ] at *;
            intro S sets hsets; specialize h_indep S ( fun i hi => ?_ ) ; simp_all +decide [ Set.preimage ] ;
            use fun i => ( fun x => ( if A j i = 1 then 1 else -1 ) * x ) ⁻¹' sets i;
            · exact measurable_const.mul measurable_id' ( hsets i hi );
            · convert h_indep using 3;
          · intro i;
            -- The function (if A j i = 1 then 1 else -1) * (if ω i then 1 else -1) is a Rademacher variable because it takes values 1 and -1 with equal probability.
            have h_rademacher : IsRademacher (vertexMeasure n) (fun ω => if ω i then 1 else -1) := by
              exact vertex_measure_rademacher n i;
            by_cases hi : A j i = 1 <;> simp_all +decide [ IsRademacher ];
            norm_num +zetaDelta at *;
            exact ⟨ Measurable.ite ( measurableSet_eq_fun ( measurable_pi_apply i ) measurable_const ) measurable_const measurable_const, h_rademacher.2.2, h_rademacher.2.1 ⟩;
        simpa [ Nat.cast_sub ( show 1 ≤ n from Fin.pos j ) ] using h_simp''';
      convert h_simp''' using 3;
      exact congr_arg _ ( Finset.sum_congr rfl fun i hi => by cases h_vals j i ( by aesop ) <;> aesop )

/-
Existence of vectors x and y such that x^T A y is large.
-/
lemma exists_large_bilinear {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h_symm : A.IsSymm)
    (h_diag : ∀ i, A i i = 0)
    (h_vals : ∀ i j, i ≠ j → A i j = 1 ∨ A i j = -1) :
    ∃ x y : Fin n → ℝ, (∀ i, x i = 1 ∨ x i = -1) ∧ (∀ j, y j = 1 ∨ y j = -1) ∧
    dotProduct x (mulVec A y) ≥ (1 / (12 * Real.sqrt 2)) * n * Real.sqrt (n - 1) := by
      -- By the properties of the expectation, we know that there exists an ω such that the sum of the absolute values of the row sums is at least the expected value.
      obtain ⟨ω, hω⟩ : ∃ ω : Fin n → Bool, ∑ j, |∑ i, A j i * (if ω i then 1 else -1)| ≥ (1 / (12 * Real.sqrt 2)) * n * Real.sqrt (n - 1) := by
        have h_expectation : ∫ ω : Fin n → Bool, ∑ j, |∑ i, A j i * (if ω i then 1 else -1)| ∂vertexMeasure n ≥ (1 / (12 * Real.sqrt 2)) * n * Real.sqrt (n - 1) := by
          have h_exp_ge : ∫ ω : Fin n → Bool, ∑ j : Fin n, |∑ i : Fin n, A j i * (if ω i then 1 else -1)| ∂vertexMeasure n = ∑ j : Fin n, ∫ ω : Fin n → Bool, |∑ i : Fin n, A j i * (if ω i then 1 else -1)| ∂vertexMeasure n := by
            rw [ MeasureTheory.integral_finset_sum ];
            aesop;
          rw [h_exp_ge];
          exact le_trans ( by norm_num; linarith ) ( Finset.sum_le_sum fun j _ => expectation_abs_row_sum A h_diag h_vals j );
        contrapose! h_expectation;
        have h_integral_lt : ∫ ω : Fin n → Bool, ∑ j, |∑ i, A j i * (if ω i then 1 else -1)| ∂vertexMeasure n < ∫ ω : Fin n → Bool, (1 / (12 * Real.sqrt 2)) * n * Real.sqrt (n - 1) ∂vertexMeasure n := by
          field_simp;
          apply lt_of_sub_pos;
          rw [ ← MeasureTheory.integral_sub ];
          · rw [ MeasureTheory.integral_pos_iff_support_of_nonneg_ae ];
            · simp_all +decide [ Function.support ];
              rw [ show { x : Fin n → Bool | ¬ ( n : ℝ ) * Real.sqrt ( n - 1 ) / ( 12 * Real.sqrt 2 ) - ∑ j : Fin n, |∑ i : Fin n, if x i = true then A j i else -A j i| = 0 } = Set.univ from Set.eq_univ_iff_forall.mpr fun x => ne_of_gt <| sub_pos.mpr <| by have := h_expectation x; ring_nf at *; linarith ] ; norm_num [ vertexMeasure ];
            · filter_upwards [ ] with x using sub_nonneg_of_le <| le_of_lt <| by simpa [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ] using h_expectation x;
            · exact Integrable.of_finite;
          · simp +zetaDelta at *;
          · aesop;
        aesop;
      refine' ⟨ fun i => if ω i then 1 else -1, fun j => if ∑ i, A j i * ( if ω i then 1 else -1 ) ≥ 0 then 1 else -1, _, _, _ ⟩ <;> norm_num;
      · exact fun j => le_or_gt _ _;
      · convert hω.le using 1;
        · ring;
        · simp +decide [ dotProduct, Matrix.mulVec, Finset.mul_sum _ _ _, mul_comm ];
          rw [ Finset.sum_comm ];
          refine' Finset.sum_congr rfl fun i hi => _;
          split_ifs <;> simp_all +decide [ abs_of_nonneg ];
          · exact Finset.sum_congr rfl fun j hj => by rw [ ← h_symm.apply ] ;
          · rw [ abs_of_neg ‹_› ];
            rw [ ← Finset.sum_neg_distrib ] ; congr ; ext j ; split_ifs <;> simp_all +decide [ Matrix.IsSymm, mul_comm ] ;
            · exact congr_fun ( congr_fun h_symm _ ) _;
            · exact congr_fun ( congr_fun h_symm i ) j

/-
From a bilinear form to a rectangle sum.
-/
lemma bilinear_to_rectangle {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ)
    (hx : ∀ i, x i = 1 ∨ x i = -1) (hy : ∀ j, y j = 1 ∨ y j = -1) :
    ∃ P Q : Finset (Fin n), |∑ i ∈ P, ∑ j ∈ Q, A i j| ≥ (1 / 4) * |dotProduct x (mulVec A y)| := by
      -- Let $S = \{i \mid x_i = 1\}$ and $T = \{j \mid y_j = 1\}$.
      set S : Finset (Fin n) := Finset.univ.filter (fun i => x i = 1)
      set T : Finset (Fin n) := Finset.univ.filter (fun j => y j = 1);
      -- By the rectangle_identity, we have $x^T A y = R(S, T) + R(S^c, T^c) - R(S, T^c) - R(S^c, T)$.
      have h_rect : dotProduct x (mulVec A y) = (∑ i ∈ S, ∑ j ∈ T, A i j) + (∑ i ∈ Sᶜ, ∑ j ∈ Tᶜ, A i j) - (∑ i ∈ S, ∑ j ∈ Tᶜ, A i j) - (∑ i ∈ Sᶜ, ∑ j ∈ T, A i j) := by
        have := @rectangle_identity n A x y hx hy;
        convert this using 1;
        · simp +decide [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc ];
        · simp +zetaDelta at *;
      contrapose! h_rect;
      have := h_rect S T; have := h_rect Sᶜ Tᶜ; have := h_rect S Tᶜ; have := h_rect Sᶜ T; norm_num [ abs_lt ] at *;
      cases abs_cases ( x ⬝ᵥ A *ᵥ y ) <;> linarith

/-
Lower bound on H(n).
-/
theorem thm_lower : ∃ c > 0, ∀ᶠ n in Filter.atTop, (H n : ℝ) ≥ c * (n : ℝ)^(3/2 : ℝ) := by
  use 1 / 4608 / 2;
  refine' ⟨ by norm_num, _ ⟩;
  -- By definition of $H$, we know that for any coloring $c$, the maximum induced sum is at least $\frac{1}{9216} n^{3/2}$.
  have h_lower_bound : ∀ n : ℕ, n ≥ 2 → ∀ c : Sym2 (Fin n) → Bool, ∃ X : Finset (Fin n), |(inducedSum n (coloringToInt c) X : ℝ)| ≥ (1 / 9216) * (n : ℝ) ^ (3 / 2 : ℝ) := by
    intro n hn c
    set A : Matrix (Fin n) (Fin n) ℝ := fun i j => if i = j then 0 else if c (Sym2.mk (i, j)) then 1 else -1
    have h_symm : A.IsSymm := by
      -- Since the coloring is symmetric, the matrix A is symmetric.
      ext i j; simp [A];
      cases eq_or_ne i j <;> simp +decide [ *, Sym2.eq_swap ];
      grind
    have h_diag : ∀ i, A i i = 0 := by
      aesop
    have h_vals : ∀ i j, i ≠ j → A i j = 1 ∨ A i j = -1 := by
      grind
    have h_exists : ∃ X : Finset (Fin n), |∑ i ∈ X, ∑ j ∈ X, A i j| ≥ (1 / 4608) * (n : ℝ) ^ (3 / 2 : ℝ) := by
      have h_exists : ∃ x y : Fin n → ℝ, (∀ i, x i = 1 ∨ x i = -1) ∧ (∀ j, y j = 1 ∨ y j = -1) ∧ dotProduct x (mulVec A y) ≥ (1 / (12 * Real.sqrt 2)) * (n : ℝ) * Real.sqrt (n - 1) := by
        exact exists_large_bilinear A h_symm h_diag h_vals;
      obtain ⟨ x, y, hx, hy, hxy ⟩ := h_exists
      obtain ⟨ P, Q, hPQ ⟩ := bilinear_to_rectangle A x y hx hy
      obtain ⟨ X, hX ⟩ := rect_to_induced A h_symm P Q ((1 / 4) * (1 / (12 * Real.sqrt 2)) * (n : ℝ) * Real.sqrt (n - 1)) (by
      cases abs_cases ( x ⬝ᵥ ( fun i j => if i = j then 0 else if c s(i, j) = true then 1 else -1 ) *ᵥ y ) <;> nlinarith [ show 0 ≤ ( Real.sqrt 2 ) ⁻¹ * ( 1 / 12 ) * ( n : ℝ ) * Real.sqrt ( n - 1 ) by positivity ]);
      refine' ⟨ X, hX.trans' _ ⟩;
      rw [ show ( n : ℝ ) ^ ( 3 / 2 : ℝ ) = n * Real.sqrt n by rw [ Real.sqrt_eq_rpow, ← Real.rpow_one_add' ] <;> norm_num ] ; ring_nf ; norm_num;
      rw [ ← Real.sqrt_div_self ] ; ring_nf ; norm_num;
      rw [ mul_assoc, ← Real.sqrt_mul ( by positivity ) ] ; exact mul_le_mul_of_nonneg_left ( Real.sqrt_le_sqrt <| by nlinarith only [ show ( n : ℝ ) ≥ 2 by norm_cast ] ) <| by positivity;
    -- By definition of $A$, we know that $\sum_{i,j \in X} A_{ij} = 2 \sum_{\{i,j\} \subseteq X} A_{ij}$.
    have h_sum_eq : ∀ X : Finset (Fin n), ∑ i ∈ X, ∑ j ∈ X, A i j = 2 * ∑ e ∈ X.sym2.filter (fun e => ¬e.IsDiag), (if c e then 1 else -1 : ℝ) := by
      intro X
      have h_sum_eq : ∑ i ∈ X, ∑ j ∈ X, A i j = ∑ i ∈ X, ∑ j ∈ X, (if i ≠ j then (if c (Sym2.mk (i, j)) then 1 else -1 : ℝ) else 0) := by
        exact Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => by aesop;
      have h_sum_eq : ∑ i ∈ X, ∑ j ∈ X, (if i ≠ j then (if c (Sym2.mk (i, j)) then 1 else -1 : ℝ) else 0) = ∑ i ∈ X, ∑ j ∈ X, (if i < j then (if c (Sym2.mk (i, j)) then 1 else -1 : ℝ) else 0) + ∑ i ∈ X, ∑ j ∈ X, (if i > j then (if c (Sym2.mk (i, j)) then 1 else -1 : ℝ) else 0) := by
        simp +decide only [← sum_add_distrib];
        refine' Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => _;
        grind;
      have h_sum_eq : ∑ i ∈ X, ∑ j ∈ X, (if i < j then (if c (Sym2.mk (i, j)) then 1 else -1 : ℝ) else 0) = ∑ e ∈ X.sym2.filter (fun e => ¬e.IsDiag), (if c e then 1 else -1 : ℝ) := by
        rw [ Finset.sum_sigma' ];
        rw [ ← Finset.sum_filter ];
        refine' Finset.sum_bij ( fun x hx => Sym2.mk ( x.1, x.2 ) ) _ _ _ _ <;> simp +decide;
        · exact fun a ha₁ ha₂ ha₃ => ⟨ ⟨ ha₁, ha₂ ⟩, ne_of_lt ha₃ ⟩;
        · grind;
        · rintro ⟨ a, b ⟩ hab h; cases lt_trichotomy a b <;> simp_all +decide
          · exact ⟨ a, b, ⟨ hab, by assumption ⟩, Or.inl ⟨ rfl, rfl ⟩ ⟩;
          · exact ⟨ b, a, ⟨ ⟨ hab.2, hab.1 ⟩, by assumption ⟩, Or.inr ⟨ rfl, rfl ⟩ ⟩;
      have h_sum_eq : ∑ i ∈ X, ∑ j ∈ X, (if i > j then (if c (Sym2.mk (i, j)) then 1 else -1 : ℝ) else 0) = ∑ e ∈ X.sym2.filter (fun e => ¬e.IsDiag), (if c e then 1 else -1 : ℝ) := by
        rw [ ← h_sum_eq ];
        rw [ Finset.sum_comm ];
        simp +decide [ Sym2.eq_swap ];
      linarith;
    obtain ⟨ X, hX ⟩ := h_exists; use X; simp_all +decide [ inducedSum ] ;
    convert mul_le_mul_of_nonneg_left hX ( show ( 0 : ℝ ) ≤ 1 / 2 by norm_num ) using 1 <;> norm_num [ coloringToInt ] ; ring;
    ring;
  -- Therefore, $H(n) \geq \frac{1}{9216} n^{3/2}$ for all $n \geq 2$.
  have h_H_lower_bound : ∀ n : ℕ, n ≥ 2 → (H n : ℝ) ≥ (1 / 9216) * (n : ℝ) ^ (3 / 2 : ℝ) := by
    intro n hn;
    -- By definition of $H$, there exists a coloring $c$ such that the maximum induced sum over all subsets $X$ is exactly $H(n)$.
    obtain ⟨c, hc⟩ : ∃ c : Sym2 (Fin n) → Bool, (Finset.image (fun X => abs (inducedSum n (coloringToInt c) X)) (Finset.univ : Finset (Finset (Fin n)))).max' (by
    exact ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_univ ∅ ) ⟩) = H n := by
      have := Finset.min'_mem ( Finset.image ( fun c : Sym2 ( Fin n ) → Bool => ( Finset.image ( fun X : Finset ( Fin n ) => |inducedSum n ( coloringToInt c ) X| ) Finset.univ |> Finset.max' <| by aesop ) ) Finset.univ ) ⟨ _, Finset.mem_image_of_mem _ <| Finset.mem_univ <| fun _ => Bool.true ⟩ ; aesop;
    generalize_proofs at *;
    obtain ⟨ X, hX ⟩ := h_lower_bound n hn c;
    exact hX.trans ( mod_cast hc ▸ Finset.le_max' ( Finset.image ( fun X => |inducedSum n ( coloringToInt c ) X| ) Finset.univ ) _ ( Finset.mem_image_of_mem _ ( Finset.mem_univ _ ) ) );
  filter_upwards [ Filter.eventually_ge_atTop 2 ] with n hn using le_trans ( by ring_nf; norm_num ) ( h_H_lower_bound n hn )

/-
Upper bound on H(n).
-/
theorem thm_upper : ∃ C > 0, ∀ n ≥ 2, (H n : ℝ) ≤ C * (n : ℝ)^(3/2 : ℝ) := by
  -- Choose $C=2$.
  use 2;
  norm_num;
  intro n hn
  obtain ⟨c, hc⟩ : ∃ c : Sym2 (Fin n) → Bool, ∀ X : Finset (Fin n), abs (inducedSum n (coloringToInt c) X) < 2 * (n : ℝ)^(3/2 : ℝ) := by
    exact Exists.elim ( exists_good_coloring n hn 2 ( by norm_num ) ( by norm_num; have := Real.log_two_lt_d9; norm_num1 at *; linarith ) ) fun c hc => ⟨ c, mod_cast hc ⟩;
  refine' le_trans ( H_le_of_exists n _ ⟨ c, fun X => le_of_lt ( mod_cast hc X ) ⟩ ) _;
  norm_num

/-
H(n) is Theta(n^(3/2)).
-/
open Filter

theorem erdos_1028 : ∃ c C : ℝ, 0 < c ∧ c < C ∧ ∀ᶠ n : ℕ in atTop, c * (n : ℝ)^(3/2 : ℝ) ≤ (H n : ℝ) ∧ (H n : ℝ) ≤ C * (n : ℝ)^(3/2 : ℝ) := by
  obtain ⟨ c, hc ⟩ := thm_lower;
  simp +zetaDelta at *;
  rcases hc with ⟨ hc₀, a, ha ⟩;
  obtain ⟨ C, hC₀, hC ⟩ := thm_upper;
  exact ⟨ c, hc₀, C + c, by linarith, Max.max a 2, fun n hn => ⟨ ha n ( le_trans ( le_max_left _ _ ) hn ), hC n ( le_trans ( le_max_right _ _ ) hn ) |> le_trans <| mul_le_mul_of_nonneg_right ( by linarith ) <| by positivity ⟩ ⟩

#print axioms erdos_1028
-- 'erdos_1028' depends on axioms: [propext, Classical.choice, Quot.sound]
