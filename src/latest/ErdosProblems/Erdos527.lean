/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 527.
https://www.erdosproblems.com/forum/thread/527

Informal authors:
- Marcus Michelen
- Mehtaab Sawhney

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos527.md
-/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib
import BoundedGaps.BombieriVinogradov.Analytic.AdditiveLargeSieve.ConsecutiveInterval
import ErdosProblems.Erdos615.Erdos615BrunnMinkowski
import ErdosProblems.Erdos88.Invariance

/-!
# Erdős Problem 527

This file uses the infinite product of fair Rademacher measures as the probability
space of sign sequences.  Ordinary series convergence is expressed using
`SummationFilter.conditional ℕ`, hence in the natural order of the coefficients.
-/

open scoped BigOperators ENNReal NNReal ProbabilityTheory Topology

namespace Erdos527

open Asymptotics Filter MeasureTheory ProbabilityTheory

/-- The parameter `1 / 2`, regarded as an element of the unit interval. -/
noncomputable def half : unitInterval := ⟨1 / 2, by norm_num⟩

/-- The fair Rademacher law on `ℝ`, with mass `1 / 2` at each of `1` and `-1`. -/
noncomputable def rademacherMeasure : Measure ℝ :=
  Ber((1 : ℝ), (-1 : ℝ), half)

instance : IsProbabilityMeasure rademacherMeasure := by
  unfold rademacherMeasure
  infer_instance

/-- The iid fair Rademacher product measure on real sequences. -/
noncomputable def rademacherProductMeasure : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ ↦ rademacherMeasure

instance : IsProbabilityMeasure rademacherProductMeasure := by
  unfold rademacherProductMeasure
  infer_instance

lemma rademacherMeasure_singleton_one :
    rademacherMeasure.real ({1} : Set ℝ) = (1 / 2 : ℝ) := by
  rw [rademacherMeasure, bernoulliMeasure_real_apply_of_mem_of_notMem half]
  · rfl
  · measurability
  · simp
  · norm_num

lemma rademacherMeasure_singleton_neg_one :
    rademacherMeasure.real ({-1} : Set ℝ) = (1 / 2 : ℝ) := by
  rw [rademacherMeasure, bernoulliMeasure_real_apply_of_notMem_of_mem half]
  · change 1 - (1 / 2 : ℝ) = 1 / 2
    norm_num
  · measurability
  · norm_num
  · simp

/-- A random variable with the Rademacher law is almost surely a sign. -/
lemma ae_rademacherMeasure :
    ∀ᵐ x ∂rademacherMeasure, x = 1 ∨ x = -1 := by
  rw [ae_iff]
  unfold rademacherMeasure
  simp [bernoulliMeasure_def]

/-- Every coordinate of almost every point in the product space is a sign. -/
lemma ae_rademacherProduct_signs :
    ∀ᵐ ε ∂rademacherProductMeasure, ∀ n, ε n = 1 ∨ ε n = -1 := by
  rw [ae_all_iff]
  intro n
  exact
    (measurePreserving_eval_infinitePi
      (fun _ : ℕ ↦ rademacherMeasure) n).quasiMeasurePreserving.ae
        ae_rademacherMeasure

/-- Each coordinate projection has the Rademacher law. -/
lemma rademacherProductMeasure_map_eval (n : ℕ) :
    rademacherProductMeasure.map (fun ε ↦ ε n) = rademacherMeasure := by
  unfold rademacherProductMeasure
  exact Measure.infinitePi_map_eval (fun _ : ℕ ↦ rademacherMeasure) n

/-- The Bernoulli presentation used for the infinite sign space agrees with the
finite uniform-Boolean presentation used by the Lindeberg API. -/
lemma rademacherMeasure_eq_invariance :
    rademacherMeasure = Erdos88.Invariance.rademacherMeasure := by
  classical
  ext s hs
  unfold rademacherMeasure Erdos88.Invariance.rademacherMeasure
  rw [ProbabilityTheory.bernoulliMeasure_apply half hs]
  rw [Measure.map_apply (measurable_of_finite _) hs]
  have hhalf : unitInterval.toNNReal half = (2 : ℝ≥0)⁻¹ := by
    apply NNReal.eq
    change (1 / 2 : ℝ) = (2 : ℝ)⁻¹
    norm_num
  have hsym : unitInterval.toNNReal (unitInterval.symm half) = (2 : ℝ≥0)⁻¹ := by
    apply NNReal.eq
    change (1 - 1 / 2 : ℝ) = (2 : ℝ)⁻¹
    norm_num
  by_cases h1 : (1 : ℝ) ∈ s <;> by_cases hm : (-1 : ℝ) ∈ s <;>
    simp [h1, hm, Erdos88.Invariance.rademacherSign,
      PMF.uniformOfFintype_apply, hhalf, hsym,
      ENNReal.inv_two_add_inv_two]

/-- The coordinate projections are mutually independent. -/
lemma iIndepFun_eval_rademacherProduct :
    iIndepFun (fun n : ℕ ↦ fun ε : ℕ → ℝ ↦ ε n) rademacherProductMeasure := by
  unfold rademacherProductMeasure
  exact iIndepFun_infinitePi (fun _ ↦ measurable_id)

/-! ## Finite-coordinate restrictions -/

/-- Restriction of a sign sequence to a finite coordinate set. -/
def restrictCoords (S : Finset ℕ) : (ℕ → ℝ) → (S → ℝ) := S.restrict

lemma measurable_restrictCoords (S : Finset ℕ) : Measurable (restrictCoords S) := by
  change Measurable (fun ε : ℕ → ℝ ↦ fun i : S ↦ ε (i : ℕ))
  exact measurable_pi_lambda _ (fun i : S ↦ measurable_pi_apply (i : ℕ))

/-- The restriction to a finite set has the corresponding finite product law. -/
lemma map_restrictCoords_rademacher (S : Finset ℕ) :
    rademacherProductMeasure.map (restrictCoords S) =
      Measure.pi (fun _ : S ↦ rademacherMeasure) := by
  change Measure.map S.restrict (Measure.infinitePi fun _ : ℕ ↦ rademacherMeasure) = _
  exact Measure.infinitePi_map_restrict
    (μ := fun _ : ℕ ↦ rademacherMeasure) (I := S)

/-- Events determined by disjoint finite blocks of signs are independent. -/
lemma indepFun_restrictCoords_of_disjoint {S T : Finset ℕ} (hST : Disjoint S T) :
    IndepFun (restrictCoords S) (restrictCoords T) rademacherProductMeasure := by
  change IndepFun (fun (a : ℕ → ℝ) (i : S) ↦ a (i : ℕ))
    (fun (a : ℕ → ℝ) (i : T) ↦ a (i : ℕ)) rademacherProductMeasure
  exact iIndepFun.indepFun_finset S T hST iIndepFun_eval_rademacherProduct
    (fun i ↦ measurable_pi_apply i)

/-! ## Finite-dimensional Rademacher concentration -/

/-- Increasing the variance proxy preserves the sub-Gaussian MGF bound. -/
lemma hasSubgaussianMGF_mono {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} {c d : ℝ≥0} (h : HasSubgaussianMGF X c μ)
    (hcd : c ≤ d) : HasSubgaussianMGF X d μ where
  integrable_exp_mul := h.integrable_exp_mul
  mgf_le t := by
    calc
      mgf X μ t ≤ Real.exp ((c : ℝ) * t ^ 2 / 2) := h.mgf_le t
      _ ≤ Real.exp ((d : ℝ) * t ^ 2 / 2) := by
        gcongr

/-- A fair Rademacher variable is sub-Gaussian with variance proxy one. -/
lemma rademacherMeasure_subgaussian :
    HasSubgaussianMGF (fun x : ℝ ↦ x) 1 rademacherMeasure := by
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (X := fun x : ℝ ↦ x) (a := -1) (b := 1) (μ := rademacherMeasure)
    (by fun_prop) (by
      rw [ae_iff]
      simp [rademacherMeasure, bernoulliMeasure_def])
    (by norm_num [rademacherMeasure, integral_bernoulliMeasure, half])
  norm_num at h ⊢
  exact h

/-- Each coordinate of the product space is sub-Gaussian with variance proxy one. -/
lemma rademacher_eval_subgaussian (i : ℕ) :
    HasSubgaussianMGF (fun ε : ℕ → ℝ ↦ ε i) 1 rademacherProductMeasure := by
  have h := HasSubgaussianMGF.of_map
    (X := fun x : ℝ ↦ x) (Y := fun ε : ℕ → ℝ ↦ ε i)
    (μ := rademacherProductMeasure) ((measurable_pi_apply i).aemeasurable) (by
      rw [rademacherProductMeasure_map_eval]
      exact rademacherMeasure_subgaussian)
  simpa [Function.comp_def] using h

/-- A finite real linear form in independent Rademacher signs is sub-Gaussian,
with variance proxy equal to the sum of the squared coefficients. -/
lemma rademacher_linear_subgaussian (c : ℕ → ℝ) (s : Finset ℕ) :
    HasSubgaussianMGF
      (fun ε : ℕ → ℝ ↦ ∑ i ∈ s, c i * ε i)
      (∑ i ∈ s, ⟨(c i) ^ 2, sq_nonneg (c i)⟩ * (1 : ℝ≥0))
      rademacherProductMeasure := by
  let X : ℕ → (ℕ → ℝ) → ℝ := fun i ε ↦ c i * ε i
  have h_indep : iIndepFun X rademacherProductMeasure := by
    simpa [X, Function.comp_def] using
      iIndepFun_eval_rademacherProduct.comp
        (fun i x ↦ c i * x) (fun _ ↦ by fun_prop)
  apply HasSubgaussianMGF.sum_of_iIndepFun h_indep
  intro i hi
  simpa only [X] using (rademacher_eval_subgaussian i).const_mul (c i)

/-- Two-sided Hoeffding bound for a finite real Rademacher linear form. -/
lemma rademacher_linear_abs_tail (c : ℕ → ℝ) (s : Finset ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    rademacherProductMeasure.real {ε | t ≤ |∑ i ∈ s, c i * ε i|} ≤
      2 * Real.exp
        (-t ^ 2 /
          (2 * ((↑(∑ i ∈ s,
            ⟨(c i) ^ 2, sq_nonneg (c i)⟩ * (1 : ℝ≥0))) : ℝ))) := by
  let Y : (ℕ → ℝ) → ℝ := fun ε ↦ ∑ i ∈ s, c i * ε i
  let v : ℝ≥0 := ∑ i ∈ s, ⟨(c i) ^ 2, sq_nonneg (c i)⟩ * (1 : ℝ≥0)
  have hsg : HasSubgaussianMGF Y v rademacherProductMeasure := by
    simpa only [Y, v] using rademacher_linear_subgaussian c s
  have hpos := hsg.measure_ge_le ht
  have hneg := hsg.neg.measure_ge_le ht
  have hset : {ε | t ≤ |Y ε|} = {ε | t ≤ Y ε} ∪ {ε | t ≤ -Y ε} := by
    ext ε
    simp only [Set.mem_ofPred_eq, Set.mem_union, le_abs]
  rw [hset]
  calc
    rademacherProductMeasure.real ({ε | t ≤ Y ε} ∪ {ε | t ≤ -Y ε})
        ≤ rademacherProductMeasure.real {ε | t ≤ Y ε} +
          rademacherProductMeasure.real {ε | t ≤ -Y ε} := measureReal_union_le _ _
    _ ≤ Real.exp (-t ^ 2 / (2 * (v : ℝ))) +
          Real.exp (-t ^ 2 / (2 * (v : ℝ))) := add_le_add hpos hneg
    _ = 2 * Real.exp (-t ^ 2 / (2 * (v : ℝ))) := by ring

/-- A two-sided Hoeffding bound after enlarging the variance proxy. -/
lemma rademacher_linear_abs_tail_of_le (c : ℕ → ℝ) (s : Finset ℕ) (v : ℝ≥0)
    (hv : (∑ i ∈ s, ⟨(c i) ^ 2, sq_nonneg (c i)⟩ * (1 : ℝ≥0)) ≤ v)
    {t : ℝ} (ht : 0 ≤ t) :
    rademacherProductMeasure.real {ε | t ≤ |∑ i ∈ s, c i * ε i|} ≤
      2 * Real.exp (-t ^ 2 / (2 * (v : ℝ))) := by
  let Y : (ℕ → ℝ) → ℝ := fun ε ↦ ∑ i ∈ s, c i * ε i
  have hsg : HasSubgaussianMGF Y v rademacherProductMeasure :=
    hasSubgaussianMGF_mono (by
      simpa only [Y] using rademacher_linear_subgaussian c s) hv
  have hpos := hsg.measure_ge_le ht
  have hneg := hsg.neg.measure_ge_le ht
  rw [show {ε | t ≤ |Y ε|} = {ε | t ≤ Y ε} ∪ {ε | t ≤ -Y ε} by
    ext ε
    simp only [Set.mem_ofPred_eq, Set.mem_union, le_abs]]
  calc
    rademacherProductMeasure.real ({ε | t ≤ Y ε} ∪ {ε | t ≤ -Y ε})
        ≤ rademacherProductMeasure.real {ε | t ≤ Y ε} +
          rademacherProductMeasure.real {ε | t ≤ -Y ε} := measureReal_union_le _ _
    _ ≤ Real.exp (-t ^ 2 / (2 * (v : ℝ))) +
          Real.exp (-t ^ 2 / (2 * (v : ℝ))) := add_le_add hpos hneg
    _ = 2 * Real.exp (-t ^ 2 / (2 * (v : ℝ))) := by ring

/-- Complex Hoeffding bound, obtained by applying the real estimate to the
real and imaginary parts and using `‖z‖ ≤ |z.re| + |z.im|`. -/
lemma rademacher_complex_tail (b : ℕ → ℂ) (s : Finset ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    rademacherProductMeasure.real
        {ε | t ≤ ‖∑ i ∈ s, (ε i : ℂ) * b i‖} ≤
      2 * Real.exp
          (-(t / 2) ^ 2 /
            (2 * ((↑(∑ i ∈ s,
              ⟨(b i).re ^ 2, sq_nonneg (b i).re⟩ * (1 : ℝ≥0))) : ℝ))) +
        2 * Real.exp
          (-(t / 2) ^ 2 /
            (2 * ((↑(∑ i ∈ s,
              ⟨(b i).im ^ 2, sq_nonneg (b i).im⟩ * (1 : ℝ≥0))) : ℝ))) := by
  let Z : (ℕ → ℝ) → ℂ := fun ε ↦ ∑ i ∈ s, (ε i : ℂ) * b i
  let A : Set (ℕ → ℝ) := {ε | t / 2 ≤ |(Z ε).re|}
  let B : Set (ℕ → ℝ) := {ε | t / 2 ≤ |(Z ε).im|}
  have hsubset : {ε | t ≤ ‖Z ε‖} ⊆ A ∪ B := by
    intro ε hε
    simp only [Set.mem_union, A, B, Set.mem_ofPred_eq]
    by_contra h
    push_neg at h
    change t ≤ ‖Z ε‖ at hε
    have hz := Complex.norm_le_abs_re_add_abs_im (Z ε)
    linarith
  have hre := rademacher_linear_abs_tail (fun i ↦ (b i).re) s
    (t := t / 2) (by linarith)
  have him := rademacher_linear_abs_tail (fun i ↦ (b i).im) s
    (t := t / 2) (by linarith)
  have hre' : rademacherProductMeasure.real A ≤
      2 * Real.exp
        (-(t / 2) ^ 2 /
          (2 * ((↑(∑ i ∈ s,
            ⟨(b i).re ^ 2, sq_nonneg (b i).re⟩ * (1 : ℝ≥0))) : ℝ))) := by
    simpa [A, Z, Complex.mul_re, mul_comm] using hre
  have him' : rademacherProductMeasure.real B ≤
      2 * Real.exp
        (-(t / 2) ^ 2 /
          (2 * ((↑(∑ i ∈ s,
            ⟨(b i).im ^ 2, sq_nonneg (b i).im⟩ * (1 : ℝ≥0))) : ℝ))) := by
    simpa [B, Z, Complex.mul_im, mul_comm] using him
  calc
    rademacherProductMeasure.real {ε | t ≤ ‖∑ i ∈ s, (ε i : ℂ) * b i‖}
        = rademacherProductMeasure.real {ε | t ≤ ‖Z ε‖} := by rfl
    _ ≤ rademacherProductMeasure.real (A ∪ B) := measureReal_mono hsubset
    _ ≤ rademacherProductMeasure.real A + rademacherProductMeasure.real B :=
      measureReal_union_le _ _
    _ ≤ _ := add_le_add hre' him'

/-- Total squared norm of the complex coefficients in a finite linear form. -/
noncomputable def complexEnergy (b : ℕ → ℂ) (s : Finset ℕ) : NNReal :=
  ∑ i ∈ s, (⟨‖b i‖ ^ 2, sq_nonneg ‖b i‖⟩ : NNReal)

lemma re_energy_le_complexEnergy (b : ℕ → ℂ) (s : Finset ℕ) :
    (∑ i ∈ s, ⟨(b i).re ^ 2, sq_nonneg (b i).re⟩ * (1 : NNReal)) ≤
      complexEnergy b s := by
  unfold complexEnergy
  apply Finset.sum_le_sum
  intro i hi
  let x : NNReal := ⟨(b i).re ^ 2, sq_nonneg _⟩
  let y : NNReal := ⟨‖b i‖ ^ 2, sq_nonneg _⟩
  have hxy0 : x ≤ y := NNReal.coe_le_coe.mp (by
    have h := Complex.re_sq_le_normSq (b i)
    rw [← Complex.sq_norm] at h
    have hx : (x : ℝ) = (b i).re ^ 2 := rfl
    have hy : (y : ℝ) = ‖b i‖ ^ 2 := rfl
    rw [hx, hy]
    simpa only [pow_two] using h)
  have hxy : x * 1 ≤ y := by simpa using hxy0
  exact hxy

lemma im_energy_le_complexEnergy (b : ℕ → ℂ) (s : Finset ℕ) :
    (∑ i ∈ s, ⟨(b i).im ^ 2, sq_nonneg (b i).im⟩ * (1 : NNReal)) ≤
      complexEnergy b s := by
  unfold complexEnergy
  apply Finset.sum_le_sum
  intro i hi
  let x : NNReal := ⟨(b i).im ^ 2, sq_nonneg _⟩
  let y : NNReal := ⟨‖b i‖ ^ 2, sq_nonneg _⟩
  have hxy0 : x ≤ y := NNReal.coe_le_coe.mp (by
    have h := Complex.im_sq_le_normSq (b i)
    rw [← Complex.sq_norm] at h
    have hx : (x : ℝ) = (b i).im ^ 2 := rfl
    have hy : (y : ℝ) = ‖b i‖ ^ 2 := rfl
    rw [hx, hy]
    simpa only [pow_two] using h)
  have hxy : x * 1 ≤ y := by simpa using hxy0
  exact hxy

/-- A common-variance complex Hoeffding bound.  In contrast to the coordinate
form above, this remains exponentially small when one coordinate variance is
zero. -/
lemma rademacher_complex_tail_commonVariance (b : ℕ → ℂ) (s : Finset ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    rademacherProductMeasure.real
        {ε | t ≤ ‖∑ i ∈ s, (ε i : ℂ) * b i‖} ≤
      4 * Real.exp (-(t / 2) ^ 2 / (2 * (complexEnergy b s : ℝ))) := by
  let Z : (ℕ → ℝ) → ℂ := fun ε ↦ ∑ i ∈ s, (ε i : ℂ) * b i
  let A : Set (ℕ → ℝ) := {ε | t / 2 ≤ |(Z ε).re|}
  let B : Set (ℕ → ℝ) := {ε | t / 2 ≤ |(Z ε).im|}
  have hsubset : {ε | t ≤ ‖Z ε‖} ⊆ A ∪ B := by
    intro ε hε
    simp only [Set.mem_union, A, B, Set.mem_ofPred_eq]
    by_contra h
    push Not at h
    change t ≤ ‖Z ε‖ at hε
    have hz := Complex.norm_le_abs_re_add_abs_im (Z ε)
    linarith
  have hre := rademacher_linear_abs_tail_of_le (fun i ↦ (b i).re) s
    (complexEnergy b s) (re_energy_le_complexEnergy b s)
    (t := t / 2) (by linarith)
  have him := rademacher_linear_abs_tail_of_le (fun i ↦ (b i).im) s
    (complexEnergy b s) (im_energy_le_complexEnergy b s)
    (t := t / 2) (by linarith)
  have hre' : rademacherProductMeasure.real A ≤
      2 * Real.exp (-(t / 2) ^ 2 / (2 * (complexEnergy b s : ℝ))) := by
    simpa [A, Z, mul_comm] using hre
  have him' : rademacherProductMeasure.real B ≤
      2 * Real.exp (-(t / 2) ^ 2 / (2 * (complexEnergy b s : ℝ))) := by
    simpa [B, Z, mul_comm] using him
  calc
    rademacherProductMeasure.real {ε | t ≤ ‖Z ε‖}
        ≤ rademacherProductMeasure.real (A ∪ B) := measureReal_mono hsubset
    _ ≤ rademacherProductMeasure.real A + rademacherProductMeasure.real B :=
      measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-(t / 2) ^ 2 / (2 * (complexEnergy b s : ℝ))) +
          2 * Real.exp (-(t / 2) ^ 2 / (2 * (complexEnergy b s : ℝ))) := by
      exact add_le_add hre' him'
    _ = 4 * Real.exp (-(t / 2) ^ 2 / (2 * (complexEnergy b s : ℝ))) := by ring

lemma rademacher_complex_tail_commonVariance_of_le (b : ℕ → ℂ) (s : Finset ℕ)
    (v : NNReal) (hv : complexEnergy b s ≤ v) {t : ℝ} (ht : 0 ≤ t) :
    rademacherProductMeasure.real
        {ε | t ≤ ‖∑ i ∈ s, (ε i : ℂ) * b i‖} ≤
      4 * Real.exp (-(t / 2) ^ 2 / (2 * (v : ℝ))) := by
  let Z : (ℕ → ℝ) → ℂ := fun ε ↦ ∑ i ∈ s, (ε i : ℂ) * b i
  let A : Set (ℕ → ℝ) := {ε | t / 2 ≤ |(Z ε).re|}
  let B : Set (ℕ → ℝ) := {ε | t / 2 ≤ |(Z ε).im|}
  have hsubset : {ε | t ≤ ‖Z ε‖} ⊆ A ∪ B := by
    intro ε hε
    simp only [Set.mem_union, A, B, Set.mem_ofPred_eq]
    by_contra h
    push Not at h
    change t ≤ ‖Z ε‖ at hε
    have hz := Complex.norm_le_abs_re_add_abs_im (Z ε)
    linarith
  have hre := rademacher_linear_abs_tail_of_le (fun i ↦ (b i).re) s v
    ((re_energy_le_complexEnergy b s).trans hv) (t := t / 2) (by linarith)
  have him := rademacher_linear_abs_tail_of_le (fun i ↦ (b i).im) s v
    ((im_energy_le_complexEnergy b s).trans hv) (t := t / 2) (by linarith)
  have hre' : rademacherProductMeasure.real A ≤
      2 * Real.exp (-(t / 2) ^ 2 / (2 * (v : ℝ))) := by
    simpa [A, Z, mul_comm] using hre
  have him' : rademacherProductMeasure.real B ≤
      2 * Real.exp (-(t / 2) ^ 2 / (2 * (v : ℝ))) := by
    simpa [B, Z, mul_comm] using him
  calc
    rademacherProductMeasure.real {ε | t ≤ ‖Z ε‖}
        ≤ rademacherProductMeasure.real (A ∪ B) := measureReal_mono hsubset
    _ ≤ rademacherProductMeasure.real A + rademacherProductMeasure.real B :=
      measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-(t / 2) ^ 2 / (2 * (v : ℝ))) +
          2 * Real.exp (-(t / 2) ^ 2 / (2 * (v : ℝ))) := add_le_add hre' him'
    _ = 4 * Real.exp (-(t / 2) ^ 2 / (2 * (v : ℝ))) := by ring

/-- Union bound for finitely many complex Rademacher linear forms. -/
lemma measureReal_exists_norm_rademacher_sum_le
    {J : Type*} [Fintype J] (b : J → ℕ → ℂ) (s : Finset ℕ) (v : NNReal)
    (hv : ∀ j, complexEnergy (b j) s ≤ v) {t : ℝ} (ht : 0 ≤ t) :
    rademacherProductMeasure.real
        {ε | ∃ j : J, t ≤ ‖∑ i ∈ s, (ε i : ℂ) * b j i‖} ≤
      Fintype.card J * (4 * Real.exp (-(t / 2) ^ 2 / (2 * (v : ℝ)))) := by
  have hset : ({ε : ℕ → ℝ | ∃ j : J,
      t ≤ ‖∑ i ∈ s, (ε i : ℂ) * b j i‖} : Set (ℕ → ℝ)) =
      ⋃ j : J, {ε : ℕ → ℝ | t ≤ ‖∑ i ∈ s, (ε i : ℂ) * b j i‖} := by
    ext ε
    simp
  rw [hset]
  calc
    rademacherProductMeasure.real
        (⋃ j : J, {ε | t ≤ ‖∑ i ∈ s, (ε i : ℂ) * b j i‖})
      ≤ ∑ j : J, rademacherProductMeasure.real
          {ε | t ≤ ‖∑ i ∈ s, (ε i : ℂ) * b j i‖} :=
        measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : J, 4 * Real.exp (-(t / 2) ^ 2 / (2 * (v : ℝ))) := by
      gcongr with j
      exact rademacher_complex_tail_commonVariance_of_le (b j) s v (hv j) ht
    _ = Fintype.card J *
        (4 * Real.exp (-(t / 2) ^ 2 / (2 * (v : ℝ)))) := by simp

/-- A real summable majorant for a sequence of failure probabilities is the
form of the first Borel--Cantelli lemma used below. -/
lemma ae_eventually_notMem_of_measureReal_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (E : ℕ → Set Ω) (p : ℕ → ℝ) (hp : Summable p)
    (hE : ∀ k, μ.real (E k) ≤ p k) :
    ∀ᵐ ω ∂μ, ∀ᶠ k : ℕ in atTop, ω ∉ E k := by
  apply ae_eventually_notMem
  apply ne_top_of_le_ne_top hp.tsum_ofReal_ne_top
  apply ENNReal.tsum_le_tsum
  intro k
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal (hE k)

/-! ## Unit-circle polynomial oscillation -/

/-- On the closed unit disk, the map `z ↦ z ^ n` is `n`-Lipschitz. -/
lemma norm_pow_sub_pow_le_nat_mul {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (n : ℕ) : ‖z ^ n - w ^ n‖ ≤ n * ‖z - w‖ := by
  rw [← (Commute.all z w).mul_geom_sum₂ n]
  calc
    ‖(z - w) * ∑ i ∈ Finset.range n, z ^ i * w ^ (n - 1 - i)‖
        ≤ ‖z - w‖ * ‖∑ i ∈ Finset.range n, z ^ i * w ^ (n - 1 - i)‖ := by
          rw [norm_mul]
    _ ≤ ‖z - w‖ * ∑ i ∈ Finset.range n, ‖z ^ i * w ^ (n - 1 - i)‖ := by
          gcongr
          exact norm_sum_le _ _
    _ ≤ ‖z - w‖ * ∑ _i ∈ Finset.range n, (1 : ℝ) := by
          gcongr with i hi
          rw [norm_mul, norm_pow, norm_pow]
          exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hz)
            (pow_nonneg (norm_nonneg _) _) (pow_le_one₀ (norm_nonneg _) hw)
    _ = n * ‖z - w‖ := by simp [mul_comm]

/-- A finite polynomial inherits the weighted coefficient Lipschitz bound. -/
lemma norm_sum_mul_pow_sub_le (c : ℕ → ℂ) (s : Finset ℕ) {z w : ℂ}
    (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖(∑ n ∈ s, c n * z ^ n) - ∑ n ∈ s, c n * w ^ n‖ ≤
      ‖z - w‖ * ∑ n ∈ s, ‖c n‖ * n := by
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ n ∈ s, (c n * z ^ n - c n * w ^ n)‖
        ≤ ∑ n ∈ s, ‖c n * z ^ n - c n * w ^ n‖ := norm_sum_le _ _
    _ = ∑ n ∈ s, ‖c n‖ * ‖z ^ n - w ^ n‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [← mul_sub, norm_mul]
    _ ≤ ∑ n ∈ s, ‖c n‖ * (n * ‖z - w‖) := by
      gcongr with n hn
      exact norm_pow_sub_pow_le_nat_mul hz hw n
    _ = ‖z - w‖ * ∑ n ∈ s, ‖c n‖ * n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring

/-- The `n`th term of the signed power series. -/
def seriesTerm (a ε : ℕ → ℝ) (z : ℂ) (n : ℕ) : ℂ :=
  ((ε n * a n : ℝ) : ℂ) * z ^ n

/-- Convergence, in the natural order, of the signed power series at `z`. -/
def SeriesConvergesAt (a ε : ℕ → ℝ) (z : ℂ) : Prop :=
  Summable (seriesTerm a ε z) (SummationFilter.conditional ℕ)

/-- The hypothesis `∑ n, |a n|² = +∞`, expressed by its natural partial sums. -/
def SquareSumDiverges (a : ℕ → ℝ) : Prop :=
  Tendsto (fun N ↦ ∑ n ∈ Finset.range N, |a n| ^ 2) atTop atTop

/-- The hypothesis `|a n| = o(1 / √n)`. -/
def DecaysFasterThanInvSqrt (a : ℕ → ℝ) : Prop :=
  (fun n : ℕ ↦ |a n|) =o[atTop]
    (fun n : ℕ ↦ (Real.sqrt (n : ℝ))⁻¹)

/-! ## Exact cyclic grids and refinement -/

namespace Grid

noncomputable def gridPoint (q : ℕ) [NeZero q] (j : ZMod q) : UnitAddCircle :=
  ZMod.toAddCircle j

lemma gridPoint_injective (q : ℕ) [NeZero q] :
    Function.Injective (gridPoint q) := ZMod.toAddCircle_injective q

lemma one_div_natCast_le_gridPoint_dist (q : ℕ) [NeZero q]
    (r s : ZMod q) (hrs : r ≠ s) :
    (1 : ℝ) / q ≤ dist (gridPoint q r) (gridPoint q s) := by
  have hu : r - s ≠ 0 := sub_ne_zero.mpr hrs
  have hval0 : 0 < (r - s).val := Nat.pos_of_ne_zero fun h ↦ by
    apply hu
    exact (ZMod.val_eq_zero (r - s)).mp h
  have hvalq : (r - s).val < q := ZMod.val_lt _
  have hmin : 1 ≤ min ((r - s).val % q) (q - (r - s).val % q) := by
    rw [Nat.mod_eq_of_lt hvalq]
    omega
  have hformula := AddCircle.norm_div_natCast (p := (1 : ℝ))
    (m := (r - s).val) (n := q)
  rw [dist_eq_norm]
  change (1 : ℝ) / q ≤ ‖ZMod.toAddCircle r - ZMod.toAddCircle s‖
  rw [← map_sub, ZMod.toAddCircle_apply]
  simp only [mul_one, one_mul] at hformula
  rw [hformula]
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  apply (div_le_div_iff_of_pos_right hq).2
  exact_mod_cast hmin

noncomputable def gridReal (q : ℕ) [NeZero q] (j : ZMod q) : ℝ :=
  j.val / q

def childIndex (q m : ℕ) [NeZero q] [NeZero m]
    (j : ZMod q) (r : Fin m) : ZMod (q * m) :=
  (j.val * m + r.val : ℕ)

lemma childIndex_val (q m : ℕ) [NeZero q] [NeZero m]
    (j : ZMod q) (r : Fin m) :
    (childIndex q m j r).val = j.val * m + r.val := by
  rw [childIndex, ZMod.val_natCast]
  apply Nat.mod_eq_of_lt
  calc
    j.val * m + r.val < j.val * m + m := Nat.add_lt_add_left r.isLt _
    _ = (j.val + 1) * m := by rw [Nat.add_mul, one_mul]
    _ ≤ q * m := Nat.mul_le_mul_right m (Nat.succ_le_of_lt j.val_lt)

lemma childIndex_injective (q m : ℕ) [NeZero q] [NeZero m] (j : ZMod q) :
    Function.Injective (childIndex q m j) := by
  intro r s hrs
  apply Fin.ext
  have := congrArg ZMod.val hrs
  rw [childIndex_val, childIndex_val] at this
  omega

lemma gridReal_child_sub_parent (q m : ℕ) [NeZero q] [NeZero m]
    (j : ZMod q) (r : Fin m) :
    gridReal (q * m) (childIndex q m j r) - gridReal q j =
      (r.val : ℝ) / (q * m) := by
  rw [gridReal, gridReal, childIndex_val]
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  push_cast
  field_simp
  ring

lemma abs_gridReal_child_sub_parent_le (q m : ℕ) [NeZero q] [NeZero m]
    (j : ZMod q) (r : Fin m) :
    |gridReal (q * m) (childIndex q m j r) - gridReal q j| ≤ (1 : ℝ) / q := by
  rw [gridReal_child_sub_parent, abs_of_nonneg (by positivity)]
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hm : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
  rw [div_le_div_iff₀ (mul_pos hq hm) hq]
  have hr : (r.val : ℝ) ≤ m := by exact_mod_cast (le_of_lt r.isLt)
  nlinarith

/-- The cyclic grid point obtained by rounding down a real representative. -/
noncomputable def nearestGridIndex (q : ℕ) [NeZero q] (x : ℝ) : ZMod q :=
  (⌊(q : ℝ) * x⌋ : ℤ)

lemma dist_coe_gridPoint_nearest_le (q : ℕ) [NeZero q] (x : ℝ) :
    dist (x : UnitAddCircle) (gridPoint q (nearestGridIndex q x)) ≤ (1 : ℝ) / q := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hfloor : ((⌊(q : ℝ) * x⌋ : ℤ) : ℝ) ≤ (q : ℝ) * x := Int.floor_le _
  have hfloor' : (q : ℝ) * x < ((⌊(q : ℝ) * x⌋ : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  rw [gridPoint, nearestGridIndex, ZMod.toAddCircle_intCast, dist_eq_norm,
    ← QuotientAddGroup.mk_sub]
  calc
    ‖(↑(x - ((⌊(q : ℝ) * x⌋ : ℤ) : ℝ) / q) : UnitAddCircle)‖
        ≤ ‖x - ((⌊(q : ℝ) * x⌋ : ℤ) : ℝ) / q‖ :=
          QuotientAddGroup.norm_mk_le_norm
    _ = x - ((⌊(q : ℝ) * x⌋ : ℤ) : ℝ) / q := by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      rw [sub_nonneg]
      apply (div_le_iff₀ hq).2
      nlinarith
    _ ≤ (1 : ℝ) / q := by
      apply (le_div_iff₀ hq).2
      field_simp
      rw [sub_le_iff_le_add]
      simpa [mul_comm, add_comm] using le_of_lt hfloor'

/-- Every point of the additive unit circle is within `1/q` of the regular
order-`q` grid. -/
lemma exists_gridPoint_dist_le (q : ℕ) [NeZero q] (x : UnitAddCircle) :
    ∃ j : ZMod q, dist x (gridPoint q j) ≤ (1 : ℝ) / q := by
  obtain ⟨y, rfl⟩ := Quotient.exists_rep x
  exact ⟨nearestGridIndex q y, dist_coe_gridPoint_nearest_le q y⟩

/-- The complex `q`th root of unity indexed by `j`. -/
noncomputable def complexGridPoint (q : ℕ) [NeZero q] (j : ZMod q) : ℂ :=
  ZMod.stdAddChar j

lemma norm_complexGridPoint (q : ℕ) [NeZero q] (j : ZMod q) :
    ‖complexGridPoint q j‖ = 1 := by
  rw [complexGridPoint, ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

lemma norm_exp_mul_I_sub_exp_mul_I_le {x y : ℝ} (hxy : |x - y| ≤ 1) :
    ‖Complex.exp (x * Complex.I) - Complex.exp (y * Complex.I)‖ ≤
      2 * |x - y| := by
  have heq : Complex.exp (x * Complex.I) =
      Complex.exp (y * Complex.I) * Complex.exp ((x - y) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [heq, show Complex.exp (y * Complex.I) * Complex.exp ((x - y) * Complex.I) -
      Complex.exp (y * Complex.I) =
      Complex.exp (y * Complex.I) * (Complex.exp ((x - y) * Complex.I) - 1) by ring,
    norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hd : ((x : ℂ) - (y : ℂ)) * Complex.I = ((x - y : ℝ) : ℂ) * Complex.I := by
    push_cast
    rfl
  rw [hd]
  have hnorm : ‖((x - y : ℝ) : ℂ) * Complex.I‖ = |x - y| := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
  have h := Complex.norm_exp_sub_one_le
    (x := ((x - y : ℝ) : ℂ) * Complex.I) (by rwa [hnorm])
  rwa [hnorm] at h

noncomputable def nearestComplexGridIndex (q : ℕ) [NeZero q] (z : ℂ) : ZMod q :=
  (⌊(q : ℝ) * (z.arg / (2 * Real.pi))⌋ : ℤ)

/-- The regular complex root grid is a quantitative net for the unit circle. -/
lemma exists_complexGridPoint_dist_le (q : ℕ) [NeZero q] (hq : 8 ≤ q)
    (z : ℂ) (hz : ‖z‖ = 1) :
    ∃ j : ZMod q, ‖z - complexGridPoint q j‖ ≤ 4 * Real.pi / q := by
  let x : ℝ := z.arg / (2 * Real.pi)
  let m : ℤ := ⌊(q : ℝ) * x⌋
  let j : ZMod q := (m : ZMod q)
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 8) hq)
  have htwopi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hfloor : (m : ℝ) ≤ (q : ℝ) * x := Int.floor_le _
  have hfloor' : (q : ℝ) * x < (m : ℝ) + 1 := Int.lt_floor_add_one _
  have hd0 : 0 ≤ z.arg - 2 * Real.pi * (m : ℝ) / q := by
    rw [sub_nonneg]
    apply (div_le_iff₀ hqpos).2
    have h := mul_le_mul_of_nonneg_left hfloor (le_of_lt htwopi)
    dsimp [x] at h
    field_simp at h
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hdlt : z.arg - 2 * Real.pi * (m : ℝ) / q < 2 * Real.pi / q := by
    rw [sub_lt_iff_lt_add]
    have h := mul_lt_mul_of_pos_left hfloor' htwopi
    dsimp [x] at h
    field_simp at h ⊢
    nlinarith
  have hratio : 2 * Real.pi / (q : ℝ) ≤ 1 := by
    apply (div_le_one hqpos).2
    have hp : Real.pi < 4 := Real.pi_lt_four
    exact (by exact_mod_cast hq : (8 : ℝ) ≤ q) |>.trans' (by linarith)
  have hdabs : |z.arg - 2 * Real.pi * (m : ℝ) / q| ≤ 1 := by
    rw [abs_of_nonneg hd0]
    exact (le_of_lt hdlt).trans hratio
  refine ⟨j, ?_⟩
  have hzexp : Complex.exp (z.arg * Complex.I) = z := by
    simpa [hz] using Complex.norm_mul_exp_arg_mul_I z
  have hjexp : complexGridPoint q j =
      Complex.exp ((2 * Real.pi * (m : ℝ) / q) * Complex.I) := by
    rw [complexGridPoint]
    change ZMod.stdAddChar (m : ZMod q) = _
    rw [ZMod.stdAddChar_coe]
    push_cast
    congr 1
    ring
  rw [← hzexp, hjexp]
  push_cast
  calc
    ‖Complex.exp (z.arg * Complex.I) -
        Complex.exp ((2 * Real.pi * (m : ℝ) / q) * Complex.I)‖
      ≤ 2 * |z.arg - 2 * Real.pi * (m : ℝ) / q| := by
        convert norm_exp_mul_I_sub_exp_mul_I_le hdabs using 1 <;> push_cast <;> ring
    _ ≤ 2 * (2 * Real.pi / q) := by
      rw [abs_of_nonneg hd0]
      exact mul_le_mul_of_nonneg_left (le_of_lt hdlt) (by norm_num)
    _ = 4 * Real.pi / q := by ring

end Grid

/-! ## Uniform control from finite root grids -/

def signedPolynomial (a ε : ℕ → ℝ) (s : Finset ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ s, ((ε n * a n : ℝ) : ℂ) * z ^ n

noncomputable def realSquareEnergy (a : ℕ → ℝ) (s : Finset ℕ) : NNReal :=
  Real.toNNReal (∑ n ∈ s, |a n| ^ 2)

lemma complexEnergy_root_eq (a : ℕ → ℝ) (s : Finset ℕ)
    (q : ℕ) [NeZero q] (j : ZMod q) :
    complexEnergy
      (fun n ↦ (a n : ℂ) * Grid.complexGridPoint q j ^ n) s =
      realSquareEnergy a s := by
  apply NNReal.eq
  rw [show realSquareEnergy a s =
      Real.toNNReal (∑ n ∈ s, |a n| ^ 2) from rfl,
    Real.coe_toNNReal _ (Finset.sum_nonneg fun n _ ↦ sq_nonneg |a n|)]
  let e : ℕ → NNReal := fun n ↦
    ⟨‖(a n : ℂ) * Grid.complexGridPoint q j ^ n‖ ^ 2, sq_nonneg _⟩
  have he : complexEnergy
      (fun n ↦ (a n : ℂ) * Grid.complexGridPoint q j ^ n) s =
      ∑ n ∈ s, e n := rfl
  rw [he, NNReal.coe_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp [e, norm_mul, norm_pow, Grid.norm_complexGridPoint, Complex.norm_real,
    Real.norm_eq_abs]
  rfl

noncomputable def gridPolynomialFailure (a : ℕ → ℝ) (s : Finset ℕ)
    (q : ℕ) [NeZero q] (t : ℝ) : Set (ℕ → ℝ) :=
  {ε | ∃ j : ZMod q, t ≤ ‖signedPolynomial a ε s (Grid.complexGridPoint q j)‖}

lemma measureReal_gridPolynomialFailure_le (a : ℕ → ℝ) (s : Finset ℕ)
    (q : ℕ) [NeZero q] (v : NNReal) (hv : realSquareEnergy a s ≤ v)
    {t : ℝ} (ht : 0 ≤ t) :
    rademacherProductMeasure.real (gridPolynomialFailure a s q t) ≤
      q * (4 * Real.exp (-(t / 2) ^ 2 / (2 * (v : ℝ)))) := by
  have h := measureReal_exists_norm_rademacher_sum_le
    (J := ZMod q)
    (fun j n ↦ (a n : ℂ) * Grid.complexGridPoint q j ^ n) s v
    (fun j ↦ (complexEnergy_root_eq a s q j).trans_le hv) ht
  simpa [gridPolynomialFailure, signedPolynomial, mul_assoc] using h

lemma norm_signedPolynomial_sub_le (a ε : ℕ → ℝ) (s : Finset ℕ)
    {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (hε : ∀ n ∈ s, |ε n| ≤ 1) :
    ‖signedPolynomial a ε s z - signedPolynomial a ε s w‖ ≤
      ‖z - w‖ * ∑ n ∈ s, |a n| * n := by
  calc
    ‖signedPolynomial a ε s z - signedPolynomial a ε s w‖
      ≤ ‖z - w‖ * ∑ n ∈ s, ‖((ε n * a n : ℝ) : ℂ)‖ * n :=
        norm_sum_mul_pow_sub_le (fun n ↦ ((ε n * a n : ℝ) : ℂ)) s hz hw
    _ ≤ ‖z - w‖ * ∑ n ∈ s, |a n| * n := by
      gcongr with n hn
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (hε n hn) (abs_nonneg (a n))

lemma norm_signedPolynomial_lt_of_not_gridPolynomialFailure
    (a ε : ℕ → ℝ) (s : Finset ℕ) (q : ℕ) [NeZero q]
    (hq : 8 ≤ q) {t : ℝ}
    (hmesh : (4 * Real.pi / q) * (∑ n ∈ s, |a n| * n) ≤ t / 2)
    (hε : ∀ n ∈ s, |ε n| ≤ 1)
    (hnot : ε ∉ gridPolynomialFailure a s q (t / 2))
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖signedPolynomial a ε s z‖ < t := by
  obtain ⟨j, hj⟩ := Grid.exists_complexGridPoint_dist_le q hq z hz
  have hgrid : ‖signedPolynomial a ε s (Grid.complexGridPoint q j)‖ < t / 2 := by
    by_contra h
    apply hnot
    exact ⟨j, le_of_not_gt h⟩
  have hosc : ‖signedPolynomial a ε s z -
      signedPolynomial a ε s (Grid.complexGridPoint q j)‖ ≤ t / 2 := by
    calc
      ‖signedPolynomial a ε s z -
          signedPolynomial a ε s (Grid.complexGridPoint q j)‖
        ≤ ‖z - Grid.complexGridPoint q j‖ *
            ∑ n ∈ s, |a n| * n :=
          norm_signedPolynomial_sub_le a ε s hz.le
            (Grid.norm_complexGridPoint q j).le hε
      _ ≤ (4 * Real.pi / q) * ∑ n ∈ s, |a n| * n := by gcongr
      _ ≤ t / 2 := hmesh
  calc
    ‖signedPolynomial a ε s z‖ =
        ‖(signedPolynomial a ε s z -
          signedPolynomial a ε s (Grid.complexGridPoint q j)) +
          signedPolynomial a ε s (Grid.complexGridPoint q j)‖ := by ring_nf
    _ ≤ ‖signedPolynomial a ε s z -
          signedPolynomial a ε s (Grid.complexGridPoint q j)‖ +
        ‖signedPolynomial a ε s (Grid.complexGridPoint q j)‖ := norm_add_le _ _
    _ < t := by linarith

/-! ## Explicit block scales -/

/-- The rapidly growing deterministic scale used to separate the random blocks. -/
def scale (N0 k : ℕ) : ℕ := N0 * 2 ^ (k ^ 3)

/-- The exponent gained in passing from the `k`th scale to the next scale. -/
def stepExponent (k : ℕ) : ℕ := 3 * k ^ 2 + 3 * k + 1

@[simp] lemma scale_zero (N0 : ℕ) : scale N0 0 = N0 := by
  simp [scale]

lemma cube_succ (k : ℕ) : (k + 1) ^ 3 = k ^ 3 + stepExponent k := by
  simp only [stepExponent]
  ring

lemma stepExponent_pos (k : ℕ) : 0 < stepExponent k := by
  simp [stepExponent]

lemma one_le_stepExponent (k : ℕ) : 1 ≤ stepExponent k :=
  stepExponent_pos k

/-- Exact multiplicative recursion for the block scales. -/
lemma scale_succ (N0 k : ℕ) :
    scale N0 (k + 1) = scale N0 k * 2 ^ stepExponent k := by
  simp only [scale, cube_succ, pow_add]
  ac_rfl

lemma scale_pos {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) : 0 < scale N0 k := by
  simp only [scale]
  positivity

lemma scale_ne_zero {N0 : ℕ} (hN0 : N0 ≠ 0) (k : ℕ) : scale N0 k ≠ 0 := by
  exact (scale_pos (Nat.pos_iff_ne_zero.mpr hN0) k).ne'

/-- Exact successor ratio when the initial scale is positive. -/
lemma scale_succ_div_scale {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) :
    scale N0 (k + 1) / scale N0 k = 2 ^ stepExponent k := by
  rw [scale_succ]
  simpa only [mul_comm] using Nat.mul_div_left (2 ^ stepExponent k) (scale_pos hN0 k)

/-- Exact factor between scales separated by an arbitrary gap. -/
lemma scale_add (N0 k j : ℕ) :
    scale N0 (k + j) = scale N0 k * 2 ^ ((k + j) ^ 3 - k ^ 3) := by
  have hcube : k ^ 3 ≤ (k + j) ^ 3 :=
    Nat.pow_le_pow_left (Nat.le_add_right k j) 3
  have hp : 2 ^ ((k + j) ^ 3) = 2 ^ (k ^ 3) * 2 ^ ((k + j) ^ 3 - k ^ 3) := by
    calc
      2 ^ ((k + j) ^ 3) = 2 ^ (((k + j) ^ 3 - k ^ 3) + k ^ 3) := by
        exact congrArg (fun n : ℕ => 2 ^ n) (Nat.sub_add_cancel hcube).symm
      _ = 2 ^ (k ^ 3) * 2 ^ ((k + j) ^ 3 - k ^ 3) := by
        simp only [pow_add, mul_comm]
  simp only [scale]
  rw [hp]
  ac_rfl

lemma scale_add_div_scale {N0 : ℕ} (hN0 : 0 < N0) (k j : ℕ) :
    scale N0 (k + j) / scale N0 k = 2 ^ ((k + j) ^ 3 - k ^ 3) := by
  rw [scale_add]
  simpa only [mul_comm] using
    Nat.mul_div_left (2 ^ ((k + j) ^ 3 - k ^ 3)) (scale_pos hN0 k)

lemma two_le_stepFactor (k : ℕ) : 2 ≤ 2 ^ stepExponent k := by
  simpa only [pow_one] using
    Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) (one_le_stepExponent k)

lemma one_le_stepFactor (k : ℕ) : 1 ≤ 2 ^ stepExponent k := by
  exact (by omega : 1 ≤ 2).trans (two_le_stepFactor k)

lemma le_stepExponent (k : ℕ) : k ≤ stepExponent k := by
  simp only [stepExponent]
  omega

lemma square_le_stepExponent (k : ℕ) : k ^ 2 ≤ stepExponent k := by
  simp only [stepExponent]
  omega

lemma two_pow_square_le_stepFactor (k : ℕ) :
    2 ^ (k ^ 2) ≤ 2 ^ stepExponent k :=
  Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) (square_le_stepExponent k)

lemma stepExponent_tendsto_atTop : Tendsto stepExponent atTop atTop := by
  refine tendsto_atTop.2 fun C => ?_
  filter_upwards [eventually_ge_atTop C] with k hk
  exact hk.trans (le_stepExponent k)

lemma stepFactor_tendsto_atTop :
    Tendsto (fun k : ℕ => 2 ^ stepExponent k) atTop atTop :=
  (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2)).comp
    stepExponent_tendsto_atTop

lemma eventually_le_stepFactor (C : ℕ) :
    ∀ᶠ k in atTop, C ≤ 2 ^ stepExponent k :=
  stepFactor_tendsto_atTop.eventually_ge_atTop C

lemma eventually_le_scale_succ_div_scale {N0 : ℕ} (hN0 : 0 < N0) (C : ℕ) :
    ∀ᶠ k in atTop, C ≤ scale N0 (k + 1) / scale N0 k := by
  filter_upwards [eventually_le_stepFactor C] with k hk
  simpa only [scale_succ_div_scale hN0 k] using hk

lemma scale_le_scale_succ (N0 k : ℕ) : scale N0 k ≤ scale N0 (k + 1) := by
  rw [scale_succ]
  exact Nat.le_mul_of_pos_right _ (by positivity)

/-- The scales are monotone even when the initial scale is zero. -/
lemma scale_monotone (N0 : ℕ) : Monotone (scale N0) :=
  monotone_nat_of_le_succ (scale_le_scale_succ N0)

/-- Every step multiplies the preceding scale by at least two. -/
lemma two_mul_scale_le_scale_succ (N0 k : ℕ) :
    2 * scale N0 k ≤ scale N0 (k + 1) := by
  rw [scale_succ, mul_comm 2]
  exact Nat.mul_le_mul_left _ (two_le_stepFactor k)

/-- Iterating the factor-two lower bound gives geometric separation over any gap. -/
lemma scale_mul_two_pow_le_scale_add (N0 k j : ℕ) :
    scale N0 k * 2 ^ j ≤ scale N0 (k + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
      calc
        scale N0 k * 2 ^ (j + 1) = (scale N0 k * 2 ^ j) * 2 := by
          simp only [pow_succ, mul_assoc]
        _ ≤ scale N0 (k + j) * 2 := Nat.mul_le_mul_right 2 ih
        _ = 2 * scale N0 (k + j) := by ac_rfl
        _ ≤ scale N0 ((k + j) + 1) := two_mul_scale_le_scale_succ N0 (k + j)
        _ = scale N0 (k + (j + 1)) := by simp only [Nat.add_assoc]

/-- In particular, the scale dominates the geometric sequence with base two. -/
lemma base_mul_two_pow_le_scale (N0 k : ℕ) :
    N0 * 2 ^ k ≤ scale N0 k := by
  simpa using scale_mul_two_pow_le_scale_add N0 0 k

lemma two_pow_le_scale {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) :
    2 ^ k ≤ scale N0 k := by
  calc
    2 ^ k ≤ N0 * 2 ^ k := Nat.le_mul_of_pos_left _ hN0
    _ ≤ scale N0 k := base_mul_two_pow_le_scale N0 k

lemma scale_lt_scale_succ {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) :
    scale N0 k < scale N0 (k + 1) := by
  have hp := scale_pos hN0 k
  have hdouble := two_mul_scale_le_scale_succ N0 k
  omega

/-- With a positive initial scale, the scale sequence is strictly increasing. -/
lemma scale_strictMono {N0 : ℕ} (hN0 : 0 < N0) : StrictMono (scale N0) :=
  strictMono_nat_of_lt_succ (scale_lt_scale_succ hN0)

lemma scale_injective {N0 : ℕ} (hN0 : 0 < N0) : Function.Injective (scale N0) :=
  (scale_strictMono hN0).injective

/-- A positive scale tends to infinity. -/
lemma scale_tendsto_atTop {N0 : ℕ} (hN0 : 0 < N0) :
    Tendsto (scale N0) atTop atTop :=
  (scale_strictMono hN0).tendsto_atTop

/-- Every fixed natural bound is eventually below the scale. -/
lemma eventually_le_scale {N0 : ℕ} (hN0 : 0 < N0) (C : ℕ) :
    ∀ᶠ k in atTop, C ≤ scale N0 k :=
  (scale_tendsto_atTop hN0).eventually_ge_atTop C

lemma base_le_scale (N0 k : ℕ) : N0 ≤ scale N0 k := by
  simp only [scale]
  exact Nat.le_mul_of_pos_right _ (by positivity)

lemma pow_cube_le_scale {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) :
    2 ^ (k ^ 3) ≤ scale N0 k := by
  simp only [scale]
  exact Nat.le_mul_of_pos_left _ hN0

/-! The following real-power estimates package the scale arithmetic needed for
the later probabilistic summability arguments. -/

/-- A fixed polynomial loss is swallowed by a thirtieth power of the next-step
scale factor. The explicit cutoff is useful when choosing a first block. -/
lemma polynomial_le_stepFactor_rpow (d k : ℕ) (hk : 10 * d ≤ k) :
    (k : ℝ) ^ d ≤ ((2 ^ stepExponent k : ℕ) : ℝ) ^ (1 / 30 : ℝ) := by
  have hkpow : k ≤ 2 ^ k := Nat.lt_two_pow_self.le
  have hpolyNat : k ^ d ≤ 2 ^ (k * d) := by
    calc
      k ^ d ≤ (2 ^ k) ^ d := Nat.pow_le_pow_left hkpow d
      _ = 2 ^ (k * d) := by rw [pow_mul]
  have hexpNat : 30 * (k * d) ≤ stepExponent k := by
    calc
      30 * (k * d) = 3 * k * (10 * d) := by ring
      _ ≤ 3 * k * k := Nat.mul_le_mul_left (3 * k) hk
      _ = 3 * k ^ 2 := by ring
      _ ≤ stepExponent k := by simp only [stepExponent]; omega
  have hexpReal : (k * d : ℕ) ≤ (stepExponent k : ℕ) / (30 : ℝ) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 30)).2
    have hcast : ((30 * (k * d) : ℕ) : ℝ) ≤ (stepExponent k : ℝ) := by
      exact_mod_cast hexpNat
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_comm] using hcast
  calc
    (k : ℝ) ^ d ≤ ((2 ^ (k * d) : ℕ) : ℝ) := by exact_mod_cast hpolyNat
    _ = (2 : ℝ) ^ (k * d : ℕ) := by norm_num
    _ = (2 : ℝ) ^ ((k * d : ℕ) : ℝ) := by rw [Real.rpow_natCast]
    _ ≤ (2 : ℝ) ^ ((stepExponent k : ℕ) / (30 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexpReal
    _ = (((2 ^ stepExponent k : ℕ) : ℝ)) ^ (1 / 30 : ℝ) := by
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]
      rw [div_eq_mul_inv]
      convert Real.rpow_natCast_mul (by positivity : (0 : ℝ) ≤ 2)
        (stepExponent k) (1 / 30 : ℝ) using 1
      all_goals norm_num

lemma eventually_polynomial_le_stepFactor_rpow (d : ℕ) :
    ∀ᶠ k : ℕ in atTop,
      (k : ℝ) ^ d ≤ ((2 ^ stepExponent k : ℕ) : ℝ) ^ (1 / 30 : ℝ) := by
  filter_upwards [eventually_ge_atTop (10 * d)] with k hk
  exact polynomial_le_stepFactor_rpow d k hk

/-- A negative real power of the cubic-exponential scale is bounded by a
geometric sequence. -/
lemma rpow_scale_le_geometric {N0 : ℕ} (hN0 : 0 < N0) {c : ℝ}
    (hc : 0 ≤ c) (k : ℕ) :
    ((scale N0 k : ℕ) : ℝ) ^ (-c) ≤ ((2 : ℝ) ^ (-c)) ^ k := by
  have hscale : (2 : ℝ) ^ k ≤ ((scale N0 k : ℕ) : ℝ) := by
    exact_mod_cast two_pow_le_scale hN0 k
  calc
    ((scale N0 k : ℕ) : ℝ) ^ (-c) ≤ ((2 : ℝ) ^ k) ^ (-c) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hscale (neg_nonpos.mpr hc)
    _ = (2 : ℝ) ^ ((k : ℝ) * (-c)) := by
      rw [Real.rpow_natCast_mul (by positivity : (0 : ℝ) ≤ 2)]
    _ = (2 : ℝ) ^ ((-c) * (k : ℝ)) := by rw [mul_comm]
    _ = ((2 : ℝ) ^ (-c)) ^ k := by
      rw [Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ 2)]

/-- Every fixed negative real power of the scale is summable. -/
lemma summable_scale_rpow_neg {N0 : ℕ} (hN0 : 0 < N0) {c : ℝ} (hc : 0 < c) :
    Summable (fun k : ℕ ↦ ((scale N0 k : ℕ) : ℝ) ^ (-c)) := by
  apply Summable.of_nonneg_of_le
  · intro k
    positivity
  · exact rpow_scale_le_geometric hN0 hc.le
  · apply summable_geometric_of_lt_one
    · exact (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le
    · exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hc)

/-- In particular, failure probabilities bounded by `Nₖ⁻¹/³⁰` are summable. -/
lemma summable_scale_rpow_neg_thirtieth {N0 : ℕ} (hN0 : 0 < N0) :
    Summable (fun k : ℕ ↦ ((scale N0 k : ℕ) : ℝ) ^ (-(1 / 30 : ℝ))) := by
  exact summable_scale_rpow_neg hN0 (by norm_num)

/-- A real sequence tending to zero is eventually smaller in absolute value
than any prescribed positive tolerance. -/
lemma eventually_abs_lt_of_tendsto_zero {δ : ℕ → ℝ}
    (hδ : Tendsto δ atTop (nhds 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, |δ k| < ε := by
  have hlo : ∀ᶠ k : ℕ in atTop, -ε < δ k :=
    (tendsto_order.1 hδ).1 (-ε) (by linarith)
  have hhi : ∀ᶠ k : ℕ in atTop, δ k < ε :=
    (tendsto_order.1 hδ).2 ε hε
  filter_upwards [hlo, hhi] with k hklo hkhi
  exact (abs_lt).2 ⟨hklo, hkhi⟩

lemma eventually_le_of_tendsto_zero {δ : ℕ → ℝ}
    (hδ : Tendsto δ atTop (nhds 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, δ k ≤ ε := by
  filter_upwards [eventually_abs_lt_of_tendsto_zero hδ hε] with k hk
  exact (le_abs_self (δ k)).trans hk.le

namespace Grid

/-- Number of the earliest children retained when the refinement factor is `m`
and the desired angular gain is `d`. -/
def nearChildCount (m d : ℕ) : ℕ := m / d

/-- The `r`th retained child of `j`; retained offsets form the initial segment
`[0,m/d)`. -/
def nearChildIndex (q m d : ℕ) [NeZero q] [NeZero m]
    (j : ZMod q) (r : Fin (nearChildCount m d)) : ZMod (q * m) :=
  childIndex q m j
    ⟨r.val, lt_of_lt_of_le r.isLt (Nat.div_le_self m d)⟩

lemma childIndex_pair_injective (q m : ℕ) [NeZero q] [NeZero m] :
    Function.Injective
      (fun p : ZMod q × Fin m ↦ childIndex q m p.1 p.2) := by
  rintro ⟨j, r⟩ ⟨j', r'⟩ h
  have hv := congrArg ZMod.val h
  rw [childIndex_val, childIndex_val] at hv
  have hm : 0 < m := NeZero.pos m
  have hj : j.val = j'.val := by
    have hv' := congrArg (fun n : ℕ ↦ n / m) hv
    have hl : (j.val * m + r.val) / m = j.val := by
      rw [Nat.mul_comm j.val m, Nat.mul_add_div hm,
        Nat.div_eq_of_lt r.isLt, Nat.add_zero]
    have hrhs : (j'.val * m + r'.val) / m = j'.val := by
      rw [Nat.mul_comm j'.val m, Nat.mul_add_div hm,
        Nat.div_eq_of_lt r'.isLt, Nat.add_zero]
    rwa [hl, hrhs] at hv'
  have hr : r.val = r'.val := by
    rw [hj] at hv
    exact Nat.add_left_cancel hv
  have hj' : j = j' := ZMod.val_injective _ hj
  have hr' : r = r' := Fin.ext hr
  simp [hj', hr']

lemma nearChildIndex_pair_injective (q m d : ℕ) [NeZero q] [NeZero m] :
    Function.Injective
      (fun p : ZMod q × Fin (nearChildCount m d) ↦
        nearChildIndex q m d p.1 p.2) := by
  rintro ⟨j, r⟩ ⟨j', r'⟩ h
  let er : Fin m := ⟨r.val, lt_of_lt_of_le r.isLt (Nat.div_le_self m d)⟩
  let er' : Fin m := ⟨r'.val, lt_of_lt_of_le r'.isLt (Nat.div_le_self m d)⟩
  have he : childIndex q m j er = childIndex q m j' er' := by
    exact h
  have h' := childIndex_pair_injective q m
    (show (fun p : ZMod q × Fin m ↦ childIndex q m p.1 p.2) (j, er) =
      (fun p : ZMod q × Fin m ↦ childIndex q m p.1 p.2) (j', er') by exact he)
  have hj : j = j' := congrArg (fun p : ZMod q × Fin m ↦ p.1) h'
  have her : er = er' := congrArg (fun p : ZMod q × Fin m ↦ p.2) h'
  exact Prod.ext hj (Fin.ext (congrArg (fun x : Fin m ↦ x.val) her))

lemma nearChildIndex_injective (q m d : ℕ) [NeZero q] [NeZero m]
    (j : ZMod q) :
    Function.Injective (nearChildIndex q m d j) := by
  intro r r' h
  have hp := nearChildIndex_pair_injective q m d
    (show nearChildIndex q m d (j, r).1 (j, r).2 =
      nearChildIndex q m d (j, r').1 (j, r').2 by exact h)
  exact congrArg Prod.snd hp

/-- Retained child indices in the refined grid. -/
def nearChildren (q m d : ℕ) [NeZero q] [NeZero m]
    (j : ZMod q) : Finset (ZMod (q * m)) :=
  Finset.univ.image (nearChildIndex q m d j)

lemma mem_nearChildren_iff (q m d : ℕ) [NeZero q] [NeZero m]
    (j : ZMod q) (s : ZMod (q * m)) :
    s ∈ nearChildren q m d j ↔
      ∃ r : Fin (nearChildCount m d), nearChildIndex q m d j r = s := by
  simp [nearChildren]

@[simp] lemma card_nearChildren (q m d : ℕ) [NeZero q] [NeZero m]
    (j : ZMod q) :
    (nearChildren q m d j).card = nearChildCount m d := by
  rw [nearChildren,
    Finset.card_image_of_injective _ (nearChildIndex_injective q m d j)]
  simp

lemma nearChildren_disjoint (q m d : ℕ) [NeZero q] [NeZero m]
    {j j' : ZMod q} (hjj' : j ≠ j') :
    Disjoint (nearChildren q m d j) (nearChildren q m d j') := by
  rw [Finset.disjoint_left]
  intro s hs hs'
  rw [mem_nearChildren_iff] at hs hs'
  obtain ⟨r, rfl⟩ := hs
  obtain ⟨r', hr'⟩ := hs'
  have hp := nearChildIndex_pair_injective q m d
    (show nearChildIndex q m d (j, r).1 (j, r).2 =
      nearChildIndex q m d (j', r').1 (j', r').2 by exact hr'.symm)
  exact hjj' (congrArg Prod.fst hp)

lemma gridReal_nearChild_sub_parent (q m d : ℕ) [NeZero q] [NeZero m]
    (j : ZMod q) (r : Fin (nearChildCount m d)) :
    gridReal (q * m) (nearChildIndex q m d j r) - gridReal q j =
      (r.val : ℝ) / (q * m) := by
  exact gridReal_child_sub_parent q m j _

lemma abs_gridReal_nearChild_sub_parent_le (q m d : ℕ)
    [NeZero q] [NeZero m] (hd : 0 < d)
    (j : ZMod q) (r : Fin (nearChildCount m d)) :
    |gridReal (q * m) (nearChildIndex q m d j r) - gridReal q j| ≤
      (1 : ℝ) / (q * d) := by
  rw [gridReal_nearChild_sub_parent, abs_of_nonneg (by positivity)]
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hm : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hrd : r.val * d < m := by
    have hmul : (m / d) * d ≤ m := Nat.div_mul_le_self m d
    exact (Nat.mul_lt_mul_of_pos_right r.isLt hd).trans_le hmul
  rw [div_le_div_iff₀ (mul_pos hq hm) (mul_pos hq hdR)]
  have hnat : q * (r.val * d) ≤ q * m :=
    Nat.mul_le_mul_left q (le_of_lt hrd)
  have hreal : (q : ℝ) * ((r.val : ℝ) * d) ≤ (q : ℝ) * m := by
    exact_mod_cast hnat
  nlinarith [hreal]

lemma complexGridPoint_injective (q : ℕ) [NeZero q] :
    Function.Injective (complexGridPoint q) := by
  intro x y h
  apply ZMod.injective_stdAddChar
  simpa only [complexGridPoint] using h

lemma complexGridPoint_eq_exp_gridReal (q : ℕ) [NeZero q] (j : ZMod q) :
    complexGridPoint q j =
      Complex.exp ((2 * Real.pi * gridReal q j) * Complex.I) := by
  rw [complexGridPoint, ZMod.stdAddChar_apply, ZMod.toCircle_apply, gridReal]
  push_cast
  congr 1
  ring

lemma norm_exp_real_mul_I_sub_exp_real_mul_I_le (x y : ℝ) :
    ‖Complex.exp (x * Complex.I) - Complex.exp (y * Complex.I)‖ ≤ |x - y| := by
  have heq : Complex.exp (x * Complex.I) =
      Complex.exp (y * Complex.I) * Complex.exp ((x - y) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [heq, show Complex.exp (y * Complex.I) * Complex.exp ((x - y) * Complex.I) -
      Complex.exp (y * Complex.I) =
      Complex.exp (y * Complex.I) * (Complex.exp ((x - y) * Complex.I) - 1) by ring,
    norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hd : ((x : ℂ) - (y : ℂ)) = ((x - y : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hd, mul_comm ((x - y : ℝ) : ℂ) Complex.I,
    Complex.norm_exp_I_mul_ofReal_sub_one]
  calc
    ‖2 * Real.sin ((x - y) / 2)‖ = 2 * |Real.sin ((x - y) / 2)| := by
      rw [Real.norm_eq_abs, abs_mul]
      norm_num
    _ ≤ 2 * |(x - y) / 2| :=
      mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
    _ = |x - y| := by
      rw [abs_div]
      norm_num
      ring

lemma norm_complexGridPoint_nearChild_sub_parent_le (q m d : ℕ)
    [NeZero q] [NeZero m] (hd : 0 < d)
    (j : ZMod q) (r : Fin (nearChildCount m d)) :
    ‖complexGridPoint (q * m) (nearChildIndex q m d j r) -
        complexGridPoint q j‖ ≤
      2 * Real.pi / (q * d) := by
  rw [complexGridPoint_eq_exp_gridReal, complexGridPoint_eq_exp_gridReal]
  let x : ℝ := 2 * Real.pi *
    gridReal (q * m) (nearChildIndex q m d j r)
  let y : ℝ := 2 * Real.pi * gridReal q j
  have hnorm := norm_exp_real_mul_I_sub_exp_real_mul_I_le x y
  dsimp only [x, y] at hnorm
  push_cast at hnorm
  calc
    ‖Complex.exp ((2 * Real.pi *
          gridReal (q * m) (nearChildIndex q m d j r)) * Complex.I) -
        Complex.exp ((2 * Real.pi * gridReal q j) * Complex.I)‖
        ≤ |2 * Real.pi * gridReal (q * m) (nearChildIndex q m d j r) -
            2 * Real.pi * gridReal q j| :=
          hnorm
    _ = 2 * Real.pi *
        |gridReal (q * m) (nearChildIndex q m d j r) - gridReal q j| := by
          rw [← mul_sub, abs_mul, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
    _ ≤ 2 * Real.pi * ((1 : ℝ) / (q * d)) := by
          exact mul_le_mul_of_nonneg_left
            (abs_gridReal_nearChild_sub_parent_le q m d hd j r)
            (mul_nonneg (by norm_num) Real.pi_pos.le)
    _ = 2 * Real.pi / (q * d) := by ring

/-- The retained children, now represented as actual complex roots of unity. -/
noncomputable def nearChildRoots (q m d : ℕ) [NeZero q] [NeZero m]
    (j : ZMod q) : Finset ℂ :=
  (nearChildren q m d j).image (complexGridPoint (q * m))

@[simp] lemma card_nearChildRoots (q m d : ℕ) [NeZero q] [NeZero m]
    (j : ZMod q) :
    (nearChildRoots q m d j).card = nearChildCount m d := by
  rw [nearChildRoots,
    Finset.card_image_of_injective _ (complexGridPoint_injective (q * m)),
    card_nearChildren]

lemma nearChildRoots_disjoint (q m d : ℕ) [NeZero q] [NeZero m]
    {j j' : ZMod q} (hjj' : j ≠ j') :
    Disjoint (nearChildRoots q m d j) (nearChildRoots q m d j') := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  simp only [nearChildRoots, Finset.mem_image] at hz hz'
  obtain ⟨s, hs, rfl⟩ := hz
  obtain ⟨s', hs', hroot⟩ := hz'
  have hss' : s = s' := complexGridPoint_injective (q * m) hroot.symm
  subst s'
  exact Finset.disjoint_left.mp (nearChildren_disjoint q m d hjj') hs hs'

lemma retained_children_phase_separated (q m d : ℕ) [NeZero q] [NeZero m]
    {j j' : ZMod q} {r r' : Fin (nearChildCount m d)}
    (hpair : (j, r) ≠ (j', r')) :
    (1 : ℝ) / (q * m) ≤
      dist (gridPoint (q * m) (nearChildIndex q m d j r))
        (gridPoint (q * m) (nearChildIndex q m d j' r')) := by
  simpa only [Nat.cast_mul] using
    one_div_natCast_le_gridPoint_dist (q * m)
      (nearChildIndex q m d j r) (nearChildIndex q m d j' r')
      (fun h ↦ hpair (nearChildIndex_pair_injective q m d h))

/-! A concrete polynomially narrow family and nested complex thickenings. -/

def branchChildDenom (k : ℕ) : ℕ := (k + 2) ^ 20

def branchRadiusDenom (k : ℕ) : ℕ := (k + 2) ^ 10

noncomputable def branchRootRadius (q k : ℕ) : ℝ :=
  4 * Real.pi / ((q : ℝ) * (branchRadiusDenom k : ℝ))

lemma branchChildDenom_pos (k : ℕ) : 0 < branchChildDenom k := by
  exact pow_pos (by omega) _

lemma branchRadiusDenom_pos (k : ℕ) : 0 < branchRadiusDenom k := by
  exact pow_pos (by omega) _

lemma card_nearChildRoots_branch (q m k : ℕ) [NeZero q] [NeZero m]
    (j : ZMod q) :
    (nearChildRoots q m (branchChildDenom k) j).card =
      m / (k + 2) ^ 20 := by
  simp [branchChildDenom, nearChildCount]

lemma norm_nearChildRoot_sub_parent_branch_le (q m k : ℕ)
    [NeZero q] [NeZero m] (j : ZMod q)
    (r : Fin (nearChildCount m (branchChildDenom k))) :
    ‖complexGridPoint (q * m)
          (nearChildIndex q m (branchChildDenom k) j r) -
        complexGridPoint q j‖ ≤
      2 * Real.pi /
        ((q : ℝ) * ((k + 2 : ℕ) : ℝ) ^ 20) := by
  have h := norm_complexGridPoint_nearChild_sub_parent_le
    q m (branchChildDenom k) (branchChildDenom_pos k) j r
  simpa only [branchChildDenom, Nat.cast_mul, Nat.cast_pow, Nat.cast_add,
    Nat.cast_ofNat] using h

lemma branch_radius_arithmetic (q m A B : ℝ)
    (hq : 0 < q) (hm : 2 ≤ m) (hA : 2 ≤ A) (hAB : A ≤ B) :
    2 * Real.pi / (q * A ^ 2) + 4 * Real.pi / (q * m * B) ≤
      4 * Real.pi / (q * A) := by
  have hpi : 0 ≤ 2 * Real.pi :=
    mul_nonneg (by norm_num) Real.pi_pos.le
  have hpi4 : 0 ≤ 4 * Real.pi :=
    mul_nonneg (by norm_num) Real.pi_pos.le
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hBpos : 0 < B := hApos.trans_le hAB
  have hmpos : 0 < m := lt_of_lt_of_le (by norm_num) hm
  have hAA : A ≤ A ^ 2 := by
    calc
      A ≤ 2 * A := by nlinarith
      _ ≤ A * A := mul_le_mul_of_nonneg_right hA hApos.le
      _ = A ^ 2 := by ring
  have hden1 : q * A ≤ q * A ^ 2 :=
    mul_le_mul_of_nonneg_left hAA hq.le
  have hfirst : 2 * Real.pi / (q * A ^ 2) ≤ 2 * Real.pi / (q * A) :=
    div_le_div_of_nonneg_left hpi (mul_pos hq hApos) hden1
  have htwoAB : 2 * A ≤ m * B := by
    calc
      2 * A ≤ 2 * B := by nlinarith
      _ ≤ m * B := by
        exact mul_le_mul_of_nonneg_right hm hBpos.le
  have hden2 : q * (2 * A) ≤ q * (m * B) :=
    mul_le_mul_of_nonneg_left htwoAB hq.le
  have hsecond' : 4 * Real.pi / (q * (m * B)) ≤
      4 * Real.pi / (q * (2 * A)) :=
    div_le_div_of_nonneg_left hpi4 (mul_pos hq (mul_pos (by norm_num) hApos)) hden2
  have hsecond : 4 * Real.pi / (q * m * B) ≤ 2 * Real.pi / (q * A) := by
    calc
      4 * Real.pi / (q * m * B) = 4 * Real.pi / (q * (m * B)) := by ring
      _ ≤ 4 * Real.pi / (q * (2 * A)) := hsecond'
      _ = 2 * Real.pi / (q * A) := by
        field_simp
        <;> ring
  calc
    2 * Real.pi / (q * A ^ 2) + 4 * Real.pi / (q * m * B) ≤
        2 * Real.pi / (q * A) + 2 * Real.pi / (q * A) :=
      add_le_add hfirst hsecond
    _ = 4 * Real.pi / (q * A) := by ring

lemma norm_nearChildRoot_sub_parent_add_radius_le (q m k : ℕ)
    [NeZero q] [NeZero m] (hm : 2 ≤ m) (j : ZMod q)
    (r : Fin (nearChildCount m (branchChildDenom k))) :
    ‖complexGridPoint (q * m)
          (nearChildIndex q m (branchChildDenom k) j r) -
        complexGridPoint q j‖ + branchRootRadius (q * m) (k + 1) ≤
      branchRootRadius q k := by
  have hc := norm_nearChildRoot_sub_parent_branch_le q m k j r
  let A : ℝ := ((k + 2 : ℕ) : ℝ) ^ 10
  let B : ℝ := ((k + 3 : ℕ) : ℝ) ^ 10
  have hA : 2 ≤ A := by
    dsimp [A]
    calc
      (2 : ℝ) ≤ 2 ^ 10 := by norm_num
      _ ≤ (((k + 2 : ℕ) : ℝ)) ^ 10 := by
        gcongr
        exact_mod_cast (show 2 ≤ k + 2 by omega)
  have hAB : A ≤ B := by
    dsimp [A, B]
    gcongr
    norm_num
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have harith := branch_radius_arithmetic (q : ℝ) (m : ℝ) A B hq hmR hA hAB
  have hpow : ((k + 2 : ℕ) : ℝ) ^ 20 = A ^ 2 := by
    dsimp [A]
    ring
  rw [hpow] at hc
  calc
    ‖complexGridPoint (q * m)
          (nearChildIndex q m (branchChildDenom k) j r) -
        complexGridPoint q j‖ + branchRootRadius (q * m) (k + 1) ≤
        2 * Real.pi / ((q : ℝ) * A ^ 2) +
          branchRootRadius (q * m) (k + 1) := add_le_add hc (le_refl _)
    _ ≤ branchRootRadius q k := by
      dsimp only [branchRootRadius, branchRadiusDenom]
      push_cast
      norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_mul, A, B,
        add_assoc, mul_assoc] at harith ⊢
      simpa only [one_add_one_eq_two, Nat.reduceAdd] using harith

lemma closedBall_nearChildRoot_subset_parent (q m k : ℕ)
    [NeZero q] [NeZero m] (hm : 2 ≤ m) (j : ZMod q)
    (r : Fin (nearChildCount m (branchChildDenom k))) :
    Metric.closedBall
        (complexGridPoint (q * m)
          (nearChildIndex q m (branchChildDenom k) j r))
        (branchRootRadius (q * m) (k + 1)) ⊆
      Metric.closedBall (complexGridPoint q j) (branchRootRadius q k) := by
  intro z hz
  rw [Metric.mem_closedBall] at hz ⊢
  calc
    dist z (complexGridPoint q j) ≤
        dist z (complexGridPoint (q * m)
          (nearChildIndex q m (branchChildDenom k) j r)) +
        dist (complexGridPoint (q * m)
          (nearChildIndex q m (branchChildDenom k) j r))
          (complexGridPoint q j) := dist_triangle _ _ _
    _ ≤ branchRootRadius (q * m) (k + 1) +
        ‖complexGridPoint (q * m)
          (nearChildIndex q m (branchChildDenom k) j r) -
          complexGridPoint q j‖ := by
      exact add_le_add hz (by rw [dist_eq_norm])
    _ = ‖complexGridPoint (q * m)
          (nearChildIndex q m (branchChildDenom k) j r) -
          complexGridPoint q j‖ + branchRootRadius (q * m) (k + 1) := by
      ring
    _ ≤ branchRootRadius q k :=
      norm_nearChildRoot_sub_parent_add_radius_le q m k hm j r

/-- Scale-specialized retained child roots.  Their order `scale N0 k *
2^(stepExponent k)` is definitionally the right-hand side of `scale_succ`. -/
noncomputable def scaleBranchChildRoots (N0 k : ℕ) [NeZero N0]
    (j : ZMod (scale N0 k)) : Finset ℂ := by
  letI : NeZero (scale N0 k) := ⟨scale_ne_zero (NeZero.ne N0) k⟩
  exact nearChildRoots (scale N0 k) (2 ^ stepExponent k)
    (branchChildDenom k) j

@[simp] lemma card_scaleBranchChildRoots (N0 k : ℕ) [NeZero N0]
    (j : ZMod (scale N0 k)) :
    (scaleBranchChildRoots N0 k j).card =
      2 ^ stepExponent k / (k + 2) ^ 20 := by
  letI : NeZero (scale N0 k) := ⟨scale_ne_zero (NeZero.ne N0) k⟩
  simp [scaleBranchChildRoots, nearChildCount, branchChildDenom]

lemma scale_refinement_factor_two_le (k : ℕ) :
    2 ≤ 2 ^ stepExponent k := by
  calc
    2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ stepExponent k :=
      Nat.pow_le_pow_right (by norm_num) (one_le_stepExponent k)

lemma add_two_le_two_pow {k : ℕ} (hk : 3 ≤ k) : k + 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      rw [Nat.pow_succ]
      have hone : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      omega

lemma branchChildDenom_le_scale_refinement {k : ℕ} (hk : 4 ≤ k) :
    branchChildDenom k ≤ 2 ^ stepExponent k := by
  by_cases hk6 : 6 ≤ k
  · have hbase : k + 2 ≤ 2 ^ k := add_two_le_two_pow (by omega)
    have hpow := Nat.pow_le_pow_left hbase 20
    have hexp : k * 20 ≤ stepExponent k := by
      simp only [stepExponent]
      nlinarith [sq_nonneg (k : ℝ)]
    calc
      branchChildDenom k = (k + 2) ^ 20 := rfl
      _ ≤ (2 ^ k) ^ 20 := hpow
      _ = 2 ^ (k * 20) := by rw [← pow_mul]
      _ ≤ 2 ^ stepExponent k :=
        Nat.pow_le_pow_right (by norm_num) hexp
  · interval_cases k <;> norm_num [branchChildDenom, stepExponent] at hk ⊢

lemma one_le_card_scaleBranchChildRoots {N0 k : ℕ} [NeZero N0]
    (hk : 4 ≤ k) (j : ZMod (scale N0 k)) :
    1 ≤ (scaleBranchChildRoots N0 k j).card := by
  rw [card_scaleBranchChildRoots]
  exact Nat.div_pos (branchChildDenom_le_scale_refinement hk)
    (branchChildDenom_pos k)

lemma scaleBranchChild_closedBall_subset_parent (N0 k : ℕ) [NeZero N0]
    [NeZero (scale N0 k)]
    (j : ZMod (scale N0 k))
    (r : Fin (nearChildCount (2 ^ stepExponent k) (branchChildDenom k))) :
    Metric.closedBall
        (complexGridPoint (scale N0 k * 2 ^ stepExponent k)
          (nearChildIndex (scale N0 k) (2 ^ stepExponent k)
            (branchChildDenom k) j r))
        (branchRootRadius (scale N0 k * 2 ^ stepExponent k) (k + 1)) ⊆
      Metric.closedBall (complexGridPoint (scale N0 k) j)
        (branchRootRadius (scale N0 k) k) := by
  exact closedBall_nearChildRoot_subset_parent
    (scale N0 k) (2 ^ stepExponent k) k
      (scale_refinement_factor_two_le k) j r

/-- All complex roots of unity in the order-`q` grid. -/
noncomputable def complexRootGrid (q : ℕ) [NeZero q] : Finset ℂ :=
  Finset.univ.image (complexGridPoint q)

@[simp] lemma card_complexRootGrid (q : ℕ) [NeZero q] :
    (complexRootGrid q).card = q := by
  rw [complexRootGrid,
    Finset.card_image_of_injective _ (complexGridPoint_injective q)]
  simp

/-- Parent indices whose roots belong to the prescribed finite phase set. -/
noncomputable def parentIndices (q : ℕ) [NeZero q] (A : Finset ℂ) :
    Finset (ZMod q) :=
  Finset.univ.filter (fun p ↦ complexGridPoint q p ∈ A)

lemma mem_parentIndices_iff (q : ℕ) [NeZero q] (A : Finset ℂ)
    (p : ZMod q) :
    p ∈ parentIndices q A ↔ complexGridPoint q p ∈ A := by
  simp [parentIndices]

lemma image_parentIndices_eq (q : ℕ) [NeZero q] {A : Finset ℂ}
    (hA : A ⊆ complexRootGrid q) :
    (parentIndices q A).image (complexGridPoint q) = A := by
  ext z
  simp only [Finset.mem_image, mem_parentIndices_iff]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp
  · intro hz
    have hzgrid := hA hz
    rw [complexRootGrid, Finset.mem_image] at hzgrid
    obtain ⟨p, -, rfl⟩ := hzgrid
    exact ⟨p, hz, rfl⟩

lemma card_parentIndices (q : ℕ) [NeZero q] {A : Finset ℂ}
    (hA : A ⊆ complexRootGrid q) :
    (parentIndices q A).card = A.card := by
  calc
    (parentIndices q A).card =
        ((parentIndices q A).image (complexGridPoint q)).card := by
      symm
      exact Finset.card_image_of_injective _ (complexGridPoint_injective q)
    _ = A.card := congrArg Finset.card (image_parentIndices_eq q hA)

/-- The union of the retained child-root families over all parents represented
in `A`. -/
noncomputable def childRootUnion (q m d : ℕ) [NeZero q] [NeZero m]
    (A : Finset ℂ) : Finset ℂ :=
  (parentIndices q A).biUnion (nearChildRoots q m d)

lemma mem_childRootUnion_iff (q m d : ℕ) [NeZero q] [NeZero m]
    (A : Finset ℂ) (z : ℂ) :
    z ∈ childRootUnion q m d A ↔
      ∃ p : ZMod q, complexGridPoint q p ∈ A ∧
        z ∈ nearChildRoots q m d p := by
  simp [childRootUnion, mem_parentIndices_iff]

lemma nearChildRoots_subset_complexRootGrid (q m d : ℕ)
    [NeZero q] [NeZero m] (p : ZMod q) :
    nearChildRoots q m d p ⊆ complexRootGrid (q * m) := by
  intro z hz
  rw [nearChildRoots, Finset.mem_image] at hz
  obtain ⟨s, hs, rfl⟩ := hz
  exact Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩

lemma childRootUnion_subset_complexRootGrid (q m d : ℕ)
    [NeZero q] [NeZero m] (A : Finset ℂ) :
    childRootUnion q m d A ⊆ complexRootGrid (q * m) := by
  rw [childRootUnion, Finset.biUnion_subset_iff_forall_subset]
  intro p hp
  exact nearChildRoots_subset_complexRootGrid q m d p

lemma childRootUnion_pairwiseDisjoint (q m d : ℕ) [NeZero q] [NeZero m]
    (A : Finset ℂ) :
    ((parentIndices q A : Finset (ZMod q)) : Set (ZMod q)).PairwiseDisjoint
      (nearChildRoots q m d) := by
  intro p hp p' hp' hpp'
  exact nearChildRoots_disjoint q m d hpp'

lemma card_childRootUnion (q m d : ℕ) [NeZero q] [NeZero m]
    {A : Finset ℂ} (hA : A ⊆ complexRootGrid q) :
    (childRootUnion q m d A).card = A.card * (m / d) := by
  rw [childRootUnion,
    Finset.card_biUnion (childRootUnion_pairwiseDisjoint q m d A)]
  simp only [card_nearChildRoots, nearChildCount]
  rw [Finset.sum_const, card_parentIndices q hA, nsmul_eq_mul]
  simp

lemma exists_parent_of_mem_childRootUnion (q m d : ℕ)
    [NeZero q] [NeZero m] {A : Finset ℂ} {z : ℂ}
    (hz : z ∈ childRootUnion q m d A) :
    ∃ p : ZMod q, complexGridPoint q p ∈ A ∧
      z ∈ nearChildRoots q m d p :=
  (mem_childRootUnion_iff q m d A z).mp hz

lemma exists_parent_index_of_mem_nearChildRoots (q m d : ℕ)
    [NeZero q] [NeZero m] {p : ZMod q} {z : ℂ}
    (hz : z ∈ nearChildRoots q m d p) :
    ∃ r : Fin (nearChildCount m d),
      z = complexGridPoint (q * m) (nearChildIndex q m d p r) := by
  rw [nearChildRoots, Finset.mem_image] at hz
  obtain ⟨s, hs, rfl⟩ := hz
  rw [mem_nearChildren_iff] at hs
  obtain ⟨r, rfl⟩ := hs
  exact ⟨r, rfl⟩

lemma exists_parent_with_nesting_of_mem_childRootUnion (q m k : ℕ)
    [NeZero q] [NeZero m] (hm : 2 ≤ m) {A : Finset ℂ} {z : ℂ}
    (hz : z ∈ childRootUnion q m (branchChildDenom k) A) :
    ∃ p : ZMod q, complexGridPoint q p ∈ A ∧
      ‖z - complexGridPoint q p‖ + branchRootRadius (q * m) (k + 1) ≤
        branchRootRadius q k ∧
      Metric.closedBall z (branchRootRadius (q * m) (k + 1)) ⊆
        Metric.closedBall (complexGridPoint q p) (branchRootRadius q k) := by
  obtain ⟨p, hpA, hzp⟩ := exists_parent_of_mem_childRootUnion q m _ hz
  obtain ⟨r, rfl⟩ := exists_parent_index_of_mem_nearChildRoots q m _ hzp
  refine ⟨p, hpA, norm_nearChildRoot_sub_parent_add_radius_le q m k hm p r, ?_⟩
  exact closedBall_nearChildRoot_subset_parent q m k hm p r

/-! Scale specialization. -/

noncomputable def scaleChildRootUnion (N0 k : ℕ) [NeZero N0]
    (A : Finset ℂ) : Finset ℂ := by
  letI : NeZero (scale N0 k) := ⟨scale_ne_zero (NeZero.ne N0) k⟩
  exact childRootUnion (scale N0 k) (2 ^ stepExponent k)
    (branchChildDenom k) A

lemma scaleChildRootUnion_subset_grid (N0 k : ℕ) [NeZero N0]
    [NeZero (scale N0 k)]
    (A : Finset ℂ) :
    scaleChildRootUnion N0 k A ⊆
      complexRootGrid (scale N0 k * 2 ^ stepExponent k) := by
  letI : NeZero (scale N0 k) := ⟨scale_ne_zero (NeZero.ne N0) k⟩
  exact childRootUnion_subset_complexRootGrid _ _ _ A

lemma card_scaleChildRootUnion (N0 k : ℕ) [NeZero N0]
    [NeZero (scale N0 k)]
    {A : Finset ℂ} (hA : A ⊆ complexRootGrid (scale N0 k)) :
    (scaleChildRootUnion N0 k A).card =
      A.card * (2 ^ stepExponent k / (k + 2) ^ 20) := by
  letI : NeZero (scale N0 k) := ⟨scale_ne_zero (NeZero.ne N0) k⟩
  simpa only [scaleChildRootUnion, branchChildDenom] using
    card_childRootUnion (scale N0 k) (2 ^ stepExponent k)
      (branchChildDenom k) hA

lemma exists_scale_parent_with_nesting_of_mem (N0 k : ℕ) [NeZero N0]
    [NeZero (scale N0 k)]
    {A : Finset ℂ} {z : ℂ} (hz : z ∈ scaleChildRootUnion N0 k A) :
    ∃ p : ZMod (scale N0 k), complexGridPoint (scale N0 k) p ∈ A ∧
      ‖z - complexGridPoint (scale N0 k) p‖ +
          branchRootRadius (scale N0 k * 2 ^ stepExponent k) (k + 1) ≤
        branchRootRadius (scale N0 k) k ∧
      Metric.closedBall z
          (branchRootRadius (scale N0 k * 2 ^ stepExponent k) (k + 1)) ⊆
        Metric.closedBall (complexGridPoint (scale N0 k) p)
          (branchRootRadius (scale N0 k) k) := by
  letI : NeZero (scale N0 k) := ⟨scale_ne_zero (NeZero.ne N0) k⟩
  exact exists_parent_with_nesting_of_mem_childRootUnion
    (scale N0 k) (2 ^ stepExponent k) k
      (scale_refinement_factor_two_le k) hz


end Grid

/-! ## Exact fine blocks inside a scale -/

/-- Number of equal fine blocks inside each dyadic epoch at scale `k`. -/
def fineParts (k : ℕ) : ℕ := 2 ^ k

/-- Length of a fine block in dyadic epoch `t` of scale `k`. -/
def fineBlockLength (N0 k t : ℕ) : ℕ := N0 * 2 ^ (k ^ 3 + t - k)

/-- Endpoint `j` in dyadic epoch `t`; blocks use consecutive endpoints. -/
def fineEndpoint (N0 k t j : ℕ) : ℕ :=
  fineBlockLength N0 k t * (fineParts k + j)

lemma k_le_cube (k : ℕ) : k ≤ k ^ 3 := by
  exact Nat.le_pow (by omega)

lemma fineBlockLength_mul_parts (N0 k t : ℕ) :
    fineBlockLength N0 k t * fineParts k = N0 * 2 ^ (k ^ 3 + t) := by
  rw [fineBlockLength, fineParts]
  have hle : k ≤ k ^ 3 + t := (k_le_cube k).trans (Nat.le_add_right _ _)
  rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

lemma fineEndpoint_zero (N0 k t : ℕ) :
    fineEndpoint N0 k t 0 = N0 * 2 ^ (k ^ 3 + t) := by
  simp only [fineEndpoint, add_zero]
  exact fineBlockLength_mul_parts N0 k t

lemma fineEndpoint_scale (N0 k : ℕ) :
    fineEndpoint N0 k 0 0 = scale N0 k := by
  rw [fineEndpoint_zero, scale]
  simp

lemma fineEndpoint_succ (N0 k t j : ℕ) :
    fineEndpoint N0 k t (j + 1) =
      fineEndpoint N0 k t j + fineBlockLength N0 k t := by
  simp only [fineEndpoint]
  ring

lemma fineEndpoint_epoch_end (N0 k t : ℕ) :
    fineEndpoint N0 k t (fineParts k) = fineEndpoint N0 k (t + 1) 0 := by
  calc
    fineEndpoint N0 k t (fineParts k) =
        2 * (fineBlockLength N0 k t * fineParts k) := by
          simp only [fineEndpoint]
          ring
    _ = 2 * (N0 * 2 ^ (k ^ 3 + t)) := by
          rw [fineBlockLength_mul_parts]
    _ = N0 * 2 ^ (k ^ 3 + (t + 1)) := by
          rw [show k ^ 3 + (t + 1) = (k ^ 3 + t) + 1 by omega, pow_succ]
          ring
    _ = fineEndpoint N0 k (t + 1) 0 := (fineEndpoint_zero _ _ _).symm

lemma fineEndpoint_last (N0 k : ℕ) :
    fineEndpoint N0 k (stepExponent k - 1) (fineParts k) = scale N0 (k + 1) := by
  rw [fineEndpoint_epoch_end, fineEndpoint_zero, scale, cube_succ]
  have hs : 0 < stepExponent k := stepExponent_pos k
  rw [Nat.sub_add_cancel hs]

/-- The fine block indexed by `(t,j)`. -/
def fineBlock (N0 k t j : ℕ) : Finset ℕ :=
  Finset.Ico (fineEndpoint N0 k t j) (fineEndpoint N0 k t (j + 1))

lemma card_fineBlock (N0 k t j : ℕ) :
    (fineBlock N0 k t j).card = fineBlockLength N0 k t := by
  rw [fineBlock, Nat.card_Ico, fineEndpoint_succ]
  omega

lemma mem_fineBlock_iff {N0 k t j n : ℕ} :
    n ∈ fineBlock N0 k t j ↔
      fineEndpoint N0 k t j ≤ n ∧
        n < fineEndpoint N0 k t j + fineBlockLength N0 k t := by
  simp only [fineBlock, Finset.mem_Ico, fineEndpoint_succ]

lemma fineEndpoint_mono_j (N0 k t : ℕ) : Monotone (fineEndpoint N0 k t) := by
  intro i j hij
  simp only [fineEndpoint]
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_left hij _)

lemma fineBlock_start_ge_epoch (N0 k t j : ℕ) :
    N0 * 2 ^ (k ^ 3 + t) ≤ fineEndpoint N0 k t j := by
  rw [← fineEndpoint_zero]
  exact fineEndpoint_mono_j N0 k t (Nat.zero_le j)

lemma fineBlockLength_mul_parts_eq_epoch (N0 k t : ℕ) :
    fineBlockLength N0 k t * 2 ^ k = N0 * 2 ^ (k ^ 3 + t) := by
  simpa only [fineParts] using fineBlockLength_mul_parts N0 k t

lemma sq_abs_le_div_of_scaled_le {a : ℕ → ℝ} {δ : ℝ} {N n : ℕ}
    (hN : 0 < N) (hNn : N ≤ n) (hδ : 0 ≤ δ)
    (hscaled : Real.sqrt (n : ℝ) * |a n| ≤ δ) :
    |a n| ^ 2 ≤ δ ^ 2 / N := by
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hsqrt : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn0
  have hx0 : 0 ≤ Real.sqrt (n : ℝ) * |a n| :=
    mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  have hsq : (Real.sqrt (n : ℝ) * |a n|) ^ 2 ≤ δ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hscaled) (add_nonneg hδ hx0)]
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast hNn
  have hmain : (N : ℝ) * |a n| ^ 2 ≤ δ ^ 2 := by
    calc
      (N : ℝ) * |a n| ^ 2 ≤ (n : ℝ) * |a n| ^ 2 := by
        gcongr
      _ = (Real.sqrt (n : ℝ) * |a n|) ^ 2 := by rw [mul_pow, hsqrt]
      _ ≤ δ ^ 2 := hsq
  exact (le_div_iff₀ (by exact_mod_cast hN)).2 (by simpa [mul_comm] using hmain)

/-- Every fine block has square energy at most `δ² / 2^k`. -/
lemma sum_sq_fineBlock_le (a : ℕ → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    {N0 k t j : ℕ} (hN0 : 0 < N0)
    (hscaled : ∀ n ∈ fineBlock N0 k t j,
      Real.sqrt (n : ℝ) * |a n| ≤ δ) :
    (∑ n ∈ fineBlock N0 k t j, |a n| ^ 2) ≤ δ ^ 2 / 2 ^ k := by
  let B := N0 * 2 ^ (k ^ 3 + t)
  have hB : 0 < B := by simp only [B]; positivity
  have hterm : ∀ n ∈ fineBlock N0 k t j, |a n| ^ 2 ≤ δ ^ 2 / B := by
    intro n hn
    exact sq_abs_le_div_of_scaled_le hB
      ((fineBlock_start_ge_epoch N0 k t j).trans (mem_fineBlock_iff.mp hn).1)
      hδ (hscaled n hn)
  calc
    (∑ n ∈ fineBlock N0 k t j, |a n| ^ 2)
        ≤ ∑ _n ∈ fineBlock N0 k t j, δ ^ 2 / B := by
          gcongr with n hn
          exact hterm n hn
    _ = (fineBlockLength N0 k t : ℝ) * (δ ^ 2 / B) := by
          rw [Finset.sum_const, nsmul_eq_mul, card_fineBlock]
    _ = δ ^ 2 / 2 ^ k := by
          have hlen : 0 < fineBlockLength N0 k t := by
            simp only [fineBlockLength]
            positivity
          have heq : (fineBlockLength N0 k t : ℝ) * (2 ^ k : ℝ) = B := by
            exact_mod_cast fineBlockLength_mul_parts_eq_epoch N0 k t
          field_simp
          nlinarith

lemma abs_le_div_sqrt_of_scaled_le {a : ℕ → ℝ} {δ : ℝ} {N n : ℕ}
    (hN : 0 < N) (hNn : N ≤ n)
    (hscaled : Real.sqrt (n : ℝ) * |a n| ≤ δ) :
    |a n| ≤ δ / Real.sqrt (N : ℝ) := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hsqrtN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNreal
  have hroot : Real.sqrt (N : ℝ) ≤ Real.sqrt (n : ℝ) := by
    exact Real.sqrt_le_sqrt (by exact_mod_cast hNn)
  apply (le_div_iff₀ hsqrtN).2
  simpa [mul_comm] using
    (mul_le_mul_of_nonneg_right hroot (abs_nonneg _)).trans hscaled

/-- The cube mass of a fine block has the extra inverse-square-root gain used
in the Lindeberg replacement. -/
lemma sum_abs_cube_fineBlock_le (a : ℕ → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    {N0 k t j : ℕ} (hN0 : 0 < N0)
    (hscaled : ∀ n ∈ fineBlock N0 k t j,
      Real.sqrt (n : ℝ) * |a n| ≤ δ) :
    (∑ n ∈ fineBlock N0 k t j, |a n| ^ 3) ≤
      (δ / Real.sqrt (N0 * 2 ^ (k ^ 3 + t) : ℕ)) * (δ ^ 2 / 2 ^ k) := by
  let B := N0 * 2 ^ (k ^ 3 + t)
  have hB : 0 < B := by simp only [B]; positivity
  calc
    (∑ n ∈ fineBlock N0 k t j, |a n| ^ 3)
        = ∑ n ∈ fineBlock N0 k t j, |a n| * |a n| ^ 2 := by
          apply Finset.sum_congr rfl
          intro n hn
          ring
    _ ≤ ∑ n ∈ fineBlock N0 k t j, (δ / Real.sqrt (B : ℝ)) * |a n| ^ 2 := by
          gcongr with n hn
          exact abs_le_div_sqrt_of_scaled_le hB
            ((fineBlock_start_ge_epoch N0 k t j).trans (mem_fineBlock_iff.mp hn).1)
            (hscaled n hn)
    _ = (δ / Real.sqrt (B : ℝ)) *
          ∑ n ∈ fineBlock N0 k t j, |a n| ^ 2 := by
          rw [Finset.mul_sum]
    _ ≤ (δ / Real.sqrt (B : ℝ)) * (δ ^ 2 / 2 ^ k) := by
          exact mul_le_mul_of_nonneg_left
            (sum_sq_fineBlock_le a hδ hN0 hscaled)
            (div_nonneg hδ (Real.sqrt_nonneg _))

/-- Telescoping a consecutive equal-length partition of a natural interval. -/
lemma sum_range_sum_Ico_arith {R : Type*} [AddCommMonoid R]
    (f : ℕ → R) (A d m : ℕ) :
    (∑ j ∈ Finset.range m,
      ∑ n ∈ Finset.Ico (A + j * d) (A + (j + 1) * d), f n) =
      ∑ n ∈ Finset.Ico A (A + m * d), f n := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      exact Finset.sum_Ico_consecutive f (Nat.le_add_right _ _)
        (Nat.add_le_add_left (Nat.mul_le_mul_right d (Nat.le_succ m)) A)

/-- The fine blocks in one dyadic epoch telescope to the entire epoch. -/
lemma sum_fineBlocks_epoch (f : ℕ → ℝ) (N0 k t : ℕ) :
    (∑ j ∈ Finset.range (fineParts k), ∑ n ∈ fineBlock N0 k t j, f n) =
      ∑ n ∈ Finset.Ico (fineEndpoint N0 k t 0)
        (fineEndpoint N0 k t (fineParts k)), f n := by
  have hblock (j : ℕ) : fineBlock N0 k t j =
      Finset.Ico (fineEndpoint N0 k t 0 + j * fineBlockLength N0 k t)
        (fineEndpoint N0 k t 0 + (j + 1) * fineBlockLength N0 k t) := by
    rw [fineBlock]
    congr 2 <;> simp only [fineEndpoint] <;> ring
  simp_rw [hblock]
  have hend : fineEndpoint N0 k t (fineParts k) =
      fineEndpoint N0 k t 0 + fineParts k * fineBlockLength N0 k t := by
    simp only [fineEndpoint]
    ring
  rw [hend]
  exact sum_range_sum_Ico_arith f _ _ _

/-- The dyadic epochs telescope to the entire cubic-exponential scale. -/
lemma sum_fineEpochs_scale (f : ℕ → ℝ) (N0 k : ℕ) :
    (∑ t ∈ Finset.range (stepExponent k),
      ∑ n ∈ Finset.Ico (fineEndpoint N0 k t 0)
        (fineEndpoint N0 k t (fineParts k)), f n) =
      ∑ n ∈ Finset.Ico (scale N0 k) (scale N0 (k + 1)), f n := by
  have htel : ∀ q : ℕ,
      (∑ t ∈ Finset.range q,
        ∑ n ∈ Finset.Ico (fineEndpoint N0 k t 0)
          (fineEndpoint N0 k t (fineParts k)), f n) =
        ∑ n ∈ Finset.Ico (fineEndpoint N0 k 0 0)
          (fineEndpoint N0 k q 0), f n := by
    intro q
    induction q with
    | zero => simp
    | succ q ihq =>
        rw [Finset.sum_range_succ, ihq, fineEndpoint_epoch_end]
        exact Finset.sum_Ico_consecutive f
          (by rw [fineEndpoint_zero, fineEndpoint_zero]
              apply Nat.mul_le_mul_left N0
              apply Nat.pow_le_pow_right (by omega)
              omega)
          (by rw [fineEndpoint_zero, fineEndpoint_zero]
              apply Nat.mul_le_mul_left N0
              apply Nat.pow_le_pow_right (by omega)
              omega)
  rw [htel, fineEndpoint_scale]
  have hp := stepExponent_pos k
  have hend : fineEndpoint N0 k (stepExponent k) 0 = scale N0 (k + 1) := by
    rw [← Nat.sub_add_cancel hp, ← fineEndpoint_epoch_end, fineEndpoint_last]
  rw [hend]

/-- The complete square-energy clock on scale `k` is at most
`(3k²+3k+1) δ²`.  This is the variance input to the Gaussian tube estimate. -/
theorem sum_sq_scale_le (a : ℕ → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    {N0 k : ℕ} (hN0 : 0 < N0)
    (hscaled : ∀ n ∈ Finset.Ico (scale N0 k) (scale N0 (k + 1)),
      Real.sqrt (n : ℝ) * |a n| ≤ δ) :
    (∑ n ∈ Finset.Ico (scale N0 k) (scale N0 (k + 1)), |a n| ^ 2) ≤
      stepExponent k * δ ^ 2 := by
  rw [← sum_fineEpochs_scale (fun n ↦ |a n| ^ 2) N0 k]
  calc
    _ = ∑ t ∈ Finset.range (stepExponent k),
        ∑ j ∈ Finset.range (fineParts k),
          ∑ n ∈ fineBlock N0 k t j, |a n| ^ 2 := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [sum_fineBlocks_epoch]
    _ ≤ ∑ _t ∈ Finset.range (stepExponent k), δ ^ 2 := by
      gcongr with t ht
      calc
        (∑ j ∈ Finset.range (fineParts k),
            ∑ n ∈ fineBlock N0 k t j, |a n| ^ 2)
            ≤ ∑ _j ∈ Finset.range (fineParts k), δ ^ 2 / 2 ^ k := by
              gcongr with j hj
              apply sum_sq_fineBlock_le a hδ hN0
              intro n hn
              apply hscaled n
              rw [Finset.mem_Ico]
              constructor
              · have hnstart := (mem_fineBlock_iff.mp hn).1
                have hscaleEpoch : scale N0 k ≤ N0 * 2 ^ (k ^ 3 + t) := by
                  rw [scale]
                  exact Nat.mul_le_mul_left N0
                    (Nat.pow_le_pow_right (by omega) (Nat.le_add_right _ _))
                exact hscaleEpoch.trans
                  ((fineBlock_start_ge_epoch N0 k t j).trans hnstart)
              · have htlt : t < stepExponent k := Finset.mem_range.mp ht
                have hnlt := (mem_fineBlock_iff.mp hn).2
                have hjlt : j < fineParts k := Finset.mem_range.mp hj
                have hend : fineEndpoint N0 k t j + fineBlockLength N0 k t ≤
                    fineEndpoint N0 k t (fineParts k) := by
                  rw [← fineEndpoint_succ]
                  exact fineEndpoint_mono_j N0 k t (by omega)
                exact hnlt.trans_le (hend.trans (by
                  rw [fineEndpoint_epoch_end, fineEndpoint_zero, scale]
                  simp only [cube_succ]
                  apply Nat.mul_le_mul_left N0
                  apply Nat.pow_le_pow_right (by omega)
                  omega))
        _ = δ ^ 2 := by
          simp only [fineParts, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          have hpow : (0 : ℝ) < 2 ^ k := by positivity
          field_simp [ne_of_gt hpow]
          norm_num only [Nat.cast_pow, Nat.cast_ofNat]
          exact mul_comm (2 ^ k : ℝ) (δ ^ 2)
    _ = stepExponent k * δ ^ 2 := by simp

/-! ## A flat equal-block partition of one scale -/

/-- The common length of the equal blocks partitioning
`[scale N0 k, scale N0 (k+1))`. -/
def uniformBlockLength (N0 k : ℕ) : ℕ := N0 * 2 ^ (k ^ 3 - k)

/-- Number of equal blocks on scale `k`.  Although exponential in `k`, this is
`scale N0 k` to a quantity tending to zero, which is the only counting property
needed in the probabilistic estimates. -/
def uniformBlockCount (k : ℕ) : ℕ := 2 ^ k * (2 ^ stepExponent k - 1)

/-- The `r`th endpoint of the flat equal-block partition. -/
def uniformEndpoint (N0 k r : ℕ) : ℕ :=
  scale N0 k + r * uniformBlockLength N0 k

/-- The `r`th flat block on scale `k`. -/
def uniformBlock (N0 k r : ℕ) : Finset ℕ :=
  Finset.Ico (uniformEndpoint N0 k r) (uniformEndpoint N0 k (r + 1))

/-- The prefix ending at the `l`th index of a flat block. -/
def uniformPrefix (N0 k r l : ℕ) : Finset ℕ :=
  Finset.Ico (uniformEndpoint N0 k r) (uniformEndpoint N0 k r + l + 1)

lemma uniformBlockLength_pos {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) :
    0 < uniformBlockLength N0 k := by
  simp only [uniformBlockLength]
  positivity

lemma uniformBlockCount_pos (k : ℕ) : 0 < uniformBlockCount k := by
  unfold uniformBlockCount
  exact Nat.mul_pos (by positivity) (Nat.sub_pos_of_lt (two_le_stepFactor k))

lemma uniformBlockLength_mul_parts (N0 k : ℕ) :
    uniformBlockLength N0 k * 2 ^ k = scale N0 k := by
  have hlen : uniformBlockLength N0 k = fineBlockLength N0 k 0 := by
    simp only [uniformBlockLength, fineBlockLength, add_zero]
  rw [hlen]
  simpa only [scale, add_zero] using fineBlockLength_mul_parts_eq_epoch N0 k 0

lemma uniformEndpoint_zero (N0 k : ℕ) :
    uniformEndpoint N0 k 0 = scale N0 k := by
  simp only [uniformEndpoint, zero_mul, add_zero]

lemma uniformEndpoint_succ (N0 k r : ℕ) :
    uniformEndpoint N0 k (r + 1) =
      uniformEndpoint N0 k r + uniformBlockLength N0 k := by
  simp only [uniformEndpoint, Nat.add_mul, one_mul, add_assoc]

lemma uniformEndpoint_last (N0 k : ℕ) :
    uniformEndpoint N0 k (uniformBlockCount k) = scale N0 (k + 1) := by
  rw [uniformEndpoint, uniformBlockCount, scale_succ]
  calc
    scale N0 k + (2 ^ k * (2 ^ stepExponent k - 1)) * uniformBlockLength N0 k
        = scale N0 k +
            (uniformBlockLength N0 k * 2 ^ k) * (2 ^ stepExponent k - 1) := by
              ac_rfl
    _ = scale N0 k + scale N0 k * (2 ^ stepExponent k - 1) := by
          rw [uniformBlockLength_mul_parts]
    _ = scale N0 k * (1 + (2 ^ stepExponent k - 1)) := by
          rw [Nat.mul_add, Nat.mul_one]
    _ = scale N0 k * 2 ^ stepExponent k := by
          rw [Nat.add_sub_of_le (one_le_stepFactor k)]

lemma scale_gap_eq_uniformBlockCount_mul_length (N0 k : ℕ) :
    scale N0 (k + 1) - scale N0 k =
      uniformBlockCount k * uniformBlockLength N0 k := by
  have hlast := uniformEndpoint_last N0 k
  simp only [uniformEndpoint] at hlast
  omega

/-- The flat-block number containing an offset into a scale. -/
def uniformBlockOfOffset {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (i : Fin (scale N0 (k + 1) - scale N0 k)) : Fin (uniformBlockCount k) :=
  ⟨i.val / uniformBlockLength N0 k, by
    rw [Nat.div_lt_iff_lt_mul (uniformBlockLength_pos hN0 k)]
    rw [← scale_gap_eq_uniformBlockCount_mul_length]
    exact i.isLt⟩

lemma uniformBlockOfOffset_val {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (i : Fin (scale N0 (k + 1) - scale N0 k)) :
    (uniformBlockOfOffset hN0 k i).val = i.val / uniformBlockLength N0 k := rfl

lemma card_uniformBlock (N0 k r : ℕ) :
    (uniformBlock N0 k r).card = uniformBlockLength N0 k := by
  rw [uniformBlock, Nat.card_Ico, uniformEndpoint_succ]
  omega

lemma uniformPrefix_subset_uniformBlock {N0 k r l : ℕ}
    (hl : l < uniformBlockLength N0 k) :
    uniformPrefix N0 k r l ⊆ uniformBlock N0 k r := by
  intro n hn
  rw [uniformPrefix, Finset.mem_Ico] at hn
  rw [uniformBlock, Finset.mem_Ico, uniformEndpoint_succ]
  omega

lemma mem_uniformBlock_iff {N0 k r n : ℕ} :
    n ∈ uniformBlock N0 k r ↔
      uniformEndpoint N0 k r ≤ n ∧
        n < uniformEndpoint N0 k r + uniformBlockLength N0 k := by
  simp only [uniformBlock, Finset.mem_Ico, uniformEndpoint_succ]

lemma uniformEndpoint_mono (N0 k : ℕ) : Monotone (uniformEndpoint N0 k) := by
  intro r s hrs
  simp only [uniformEndpoint]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hrs) _

lemma uniformBlock_start_ge_scale (N0 k r : ℕ) :
    scale N0 k ≤ uniformEndpoint N0 k r := by
  simp only [uniformEndpoint, le_add_iff_nonneg_right, zero_le]

/-- Every flat block has square energy at most `δ² / 2^k` under the scale
envelope `√n |a n| ≤ δ`. -/
lemma sum_sq_uniformBlock_le (a : ℕ → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    {N0 : ℕ} (hN0 : 0 < N0) {k r : ℕ}
    (hscaled : ∀ n ∈ uniformBlock N0 k r,
      Real.sqrt (n : ℝ) * |a n| ≤ δ) :
    (∑ n ∈ uniformBlock N0 k r, |a n| ^ 2) ≤ δ ^ 2 / 2 ^ k := by
  let B := scale N0 k
  have hB : 0 < B := scale_pos hN0 k
  have hterm : ∀ n ∈ uniformBlock N0 k r, |a n| ^ 2 ≤ δ ^ 2 / B := by
    intro n hn
    exact sq_abs_le_div_of_scaled_le hB
      ((uniformBlock_start_ge_scale N0 k r).trans (mem_uniformBlock_iff.mp hn).1)
      hδ (hscaled n hn)
  calc
    (∑ n ∈ uniformBlock N0 k r, |a n| ^ 2)
        ≤ ∑ _n ∈ uniformBlock N0 k r, δ ^ 2 / B := by
          exact Finset.sum_le_sum fun n hn ↦ hterm n hn
    _ = (uniformBlockLength N0 k : ℝ) * (δ ^ 2 / B) := by
          rw [Finset.sum_const, nsmul_eq_mul, card_uniformBlock]
    _ = δ ^ 2 / 2 ^ k := by
          have hlen : 0 < uniformBlockLength N0 k := by
            simp only [uniformBlockLength]
            positivity
          have heq : (uniformBlockLength N0 k : ℝ) * (2 ^ k : ℝ) = B := by
            exact_mod_cast uniformBlockLength_mul_parts N0 k
          field_simp
          nlinarith

/-- The fourth-moment replacement error on a flat block has two extra powers
of the coefficient envelope. -/
lemma sum_abs_four_uniformBlock_le (a : ℕ → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    {N0 : ℕ} (hN0 : 0 < N0) {k r : ℕ}
    (hscaled : ∀ n ∈ uniformBlock N0 k r,
      Real.sqrt (n : ℝ) * |a n| ≤ δ) :
    (∑ n ∈ uniformBlock N0 k r, |a n| ^ 4) ≤
      (δ ^ 2 / scale N0 k) * (δ ^ 2 / 2 ^ k) := by
  have hB : 0 < scale N0 k := scale_pos hN0 k
  have hmax : ∀ n ∈ uniformBlock N0 k r,
      |a n| ^ 2 ≤ δ ^ 2 / scale N0 k := by
    intro n hn
    exact sq_abs_le_div_of_scaled_le hB
      ((uniformBlock_start_ge_scale N0 k r).trans (mem_uniformBlock_iff.mp hn).1)
      hδ (hscaled n hn)
  calc
    (∑ n ∈ uniformBlock N0 k r, |a n| ^ 4)
        = ∑ n ∈ uniformBlock N0 k r, |a n| ^ 2 * |a n| ^ 2 := by
          apply Finset.sum_congr rfl
          intro n hn
          ring
    _ ≤ ∑ n ∈ uniformBlock N0 k r,
          (δ ^ 2 / scale N0 k) * |a n| ^ 2 := by
          gcongr with n hn
          exact hmax n hn
    _ = (δ ^ 2 / scale N0 k) *
          ∑ n ∈ uniformBlock N0 k r, |a n| ^ 2 := by
          rw [Finset.mul_sum]
    _ ≤ (δ ^ 2 / scale N0 k) * (δ ^ 2 / 2 ^ k) := by
          exact mul_le_mul_of_nonneg_left
            (sum_sq_uniformBlock_le a hδ hN0 hscaled)
            (div_nonneg (sq_nonneg _) (by positivity))

/-- The `NNReal` energy form used by the concentration estimates inherits the
flat-block square-energy bound. -/
lemma realSquareEnergy_uniformBlock_le (a : ℕ → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    {N0 : ℕ} (hN0 : 0 < N0) {k r : ℕ}
    (hscaled : ∀ n ∈ uniformBlock N0 k r,
      Real.sqrt (n : ℝ) * |a n| ≤ δ) :
    realSquareEnergy a (uniformBlock N0 k r) ≤
      ⟨δ ^ 2 / 2 ^ k, div_nonneg (sq_nonneg _) (by positivity)⟩ := by
  apply NNReal.coe_le_coe.mp
  rw [realSquareEnergy,
    Real.coe_toNNReal _ (Finset.sum_nonneg fun n _ ↦ sq_nonneg |a n|)]
  change (∑ n ∈ uniformBlock N0 k r, |a n| ^ 2) ≤ δ ^ 2 / 2 ^ k
  exact sum_sq_uniformBlock_le a hδ hN0 hscaled

lemma realSquareEnergy_uniformPrefix_le (a : ℕ → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    {N0 : ℕ} (hN0 : 0 < N0) {k r l : ℕ}
    (hl : l < uniformBlockLength N0 k)
    (hscaled : ∀ n ∈ uniformBlock N0 k r,
      Real.sqrt (n : ℝ) * |a n| ≤ δ) :
    realSquareEnergy a (uniformPrefix N0 k r l) ≤
      ⟨δ ^ 2 / 2 ^ k, div_nonneg (sq_nonneg _) (by positivity)⟩ := by
  apply NNReal.coe_le_coe.mp
  rw [realSquareEnergy,
    Real.coe_toNNReal _ (Finset.sum_nonneg fun n _ ↦ sq_nonneg |a n|)]
  change (∑ n ∈ uniformPrefix N0 k r l, |a n| ^ 2) ≤ δ ^ 2 / 2 ^ k
  exact (Finset.sum_le_sum_of_subset_of_nonneg
    (uniformPrefix_subset_uniformBlock hl) (fun n _ _ ↦ sq_nonneg |a n|)).trans
      (sum_sq_uniformBlock_le a hδ hN0 hscaled)

lemma mem_uniformPrefix_lt_scale_succ {N0 k : ℕ}
    {r : Fin (uniformBlockCount k)} {l : Fin (uniformBlockLength N0 k)}
    {n : ℕ} (hn : n ∈ uniformPrefix N0 k r l) :
    n < scale N0 (k + 1) := by
  have hnblock := uniformPrefix_subset_uniformBlock l.isLt hn
  have hnend := (mem_uniformBlock_iff.mp hnblock).2
  have hr : r.val + 1 ≤ uniformBlockCount k := by omega
  have hmono := uniformEndpoint_mono N0 k hr
  rw [uniformEndpoint_last] at hmono
  rw [← uniformEndpoint_succ] at hnend
  exact hnend.trans_le hmono

/-- A crude deterministic derivative bound sufficient for the very fine
phase grid used below. -/
lemma sum_abs_mul_index_uniformPrefix_le_scale_sq
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) {k : ℕ}
    (r : Fin (uniformBlockCount k))
    (l : Fin (uniformBlockLength N0 k))
    (hscaled : ∀ n ∈ uniformBlock N0 k r,
      Real.sqrt (n : ℝ) * |a n| ≤ 1) :
    (∑ n ∈ uniformPrefix N0 k r l, |a n| * n) ≤
      (scale N0 (k + 1) : ℝ) ^ 2 := by
  let S := scale N0 (k + 1)
  have hscale1 : 1 ≤ scale N0 k := (scale_pos hN0 k)
  have hsqrt1 : 1 ≤ Real.sqrt (scale N0 k : ℝ) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hscale1
  have hsqrtpos : 0 < Real.sqrt (scale N0 k : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast scale_pos hN0 k)
  have hterm : ∀ n ∈ uniformPrefix N0 k r l, |a n| * (n : ℝ) ≤ S := by
    intro n hn
    have hnblock := uniformPrefix_subset_uniformBlock l.isLt hn
    have habs : |a n| ≤ 1 := by
      exact (abs_le_div_sqrt_of_scaled_le (scale_pos hN0 k)
        ((uniformBlock_start_ge_scale N0 k r).trans
          (mem_uniformBlock_iff.mp hnblock).1)
        (hscaled n hnblock)).trans ((div_le_one hsqrtpos).2 hsqrt1)
    have hnS : (n : ℝ) ≤ S := by
      exact_mod_cast (mem_uniformPrefix_lt_scale_succ hn).le
    exact (mul_le_mul habs hnS (by positivity) (by norm_num)).trans_eq
      (one_mul (S : ℝ))
  have hsubset : uniformPrefix N0 k r l ⊆ Finset.range S := by
    intro n hn
    exact Finset.mem_range.mpr (mem_uniformPrefix_lt_scale_succ hn)
  have hcard : ((uniformPrefix N0 k r l).card : ℝ) ≤ S := by
    have hcardNat : (uniformPrefix N0 k r l).card ≤ S := by
      simpa using Finset.card_le_card hsubset
    exact_mod_cast hcardNat
  calc
    (∑ n ∈ uniformPrefix N0 k r l, |a n| * n)
      ≤ ∑ _n ∈ uniformPrefix N0 k r l, (S : ℝ) := by
        exact Finset.sum_le_sum fun n hn ↦ hterm n hn
    _ = (uniformPrefix N0 k r l).card * (S : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (S : ℝ) * S := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (scale N0 (k + 1) : ℝ) ^ 2 := by simp only [S, pow_two]

/-- Failure of the desired oscillation bound at some prefix of some flat
block, detected on a finite root grid. -/
noncomputable def flatPrefixGridFailure (a : ℕ → ℝ) (N0 k q : ℕ)
    [NeZero q] (t : ℝ) : Set (ℕ → ℝ) :=
  ⋃ r : Fin (uniformBlockCount k), ⋃ l : Fin (uniformBlockLength N0 k),
    gridPolynomialFailure a (uniformPrefix N0 k r l) q t

lemma measureReal_flatPrefixGridFailure_le
    (a : ℕ → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    {N0 : ℕ} (hN0 : 0 < N0) (k q : ℕ) [NeZero q]
    (hscaled : ∀ (r : Fin (uniformBlockCount k)) n,
      n ∈ uniformBlock N0 k r → Real.sqrt (n : ℝ) * |a n| ≤ δ)
    {t : ℝ} (ht : 0 ≤ t) :
    rademacherProductMeasure.real (flatPrefixGridFailure a N0 k q t) ≤
      uniformBlockCount k * uniformBlockLength N0 k *
        (q * (4 * Real.exp (-(t / 2) ^ 2 /
          (2 * (δ ^ 2 / 2 ^ k))))) := by
  unfold flatPrefixGridFailure
  calc
    rademacherProductMeasure.real
        (⋃ r : Fin (uniformBlockCount k), ⋃ l : Fin (uniformBlockLength N0 k),
          gridPolynomialFailure a (uniformPrefix N0 k r l) q t)
      ≤ ∑ r : Fin (uniformBlockCount k),
          rademacherProductMeasure.real
            (⋃ l : Fin (uniformBlockLength N0 k),
              gridPolynomialFailure a (uniformPrefix N0 k r l) q t) :=
        measureReal_iUnion_fintype_le _
    _ ≤ ∑ r : Fin (uniformBlockCount k),
          ∑ l : Fin (uniformBlockLength N0 k),
            rademacherProductMeasure.real
              (gridPolynomialFailure a (uniformPrefix N0 k r l) q t) := by
      gcongr with r
      exact measureReal_iUnion_fintype_le _
    _ ≤ ∑ _r : Fin (uniformBlockCount k),
          ∑ _l : Fin (uniformBlockLength N0 k),
            q * (4 * Real.exp (-(t / 2) ^ 2 /
              (2 * (δ ^ 2 / 2 ^ k)))) := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro l hl
      have hv := realSquareEnergy_uniformPrefix_le a hδ hN0 l.isLt
        (hscaled r)
      convert measureReal_gridPolynomialFailure_le a (uniformPrefix N0 k r l) q
        ⟨δ ^ 2 / 2 ^ k, div_nonneg (sq_nonneg _) (by positivity)⟩ hv ht using 1
      · rfl
      · rfl
    _ = uniformBlockCount k * uniformBlockLength N0 k *
        (q * (4 * Real.exp (-(t / 2) ^ 2 /
          (2 * (δ ^ 2 / 2 ^ k))))) := by
      simp [mul_assoc]

lemma flatPrefix_uniform_bound_of_not_failure
    (a ε : ℕ → ℝ) {N0 k q : ℕ} [NeZero q] (hq : 8 ≤ q) {t : ℝ}
    (hmesh : ∀ (r : Fin (uniformBlockCount k))
      (l : Fin (uniformBlockLength N0 k)),
      (4 * Real.pi / q) *
        (∑ n ∈ uniformPrefix N0 k r l, |a n| * n) ≤ t / 2)
    (hε : ∀ n, |ε n| ≤ 1)
    (hnot : ε ∉ flatPrefixGridFailure a N0 k q (t / 2)) :
    ∀ (r : Fin (uniformBlockCount k)) (l : Fin (uniformBlockLength N0 k))
      (z : ℂ), ‖z‖ = 1 →
      ‖signedPolynomial a ε (uniformPrefix N0 k r l) z‖ < t := by
  intro r l z hz
  apply norm_signedPolynomial_lt_of_not_gridPolynomialFailure
    a ε (uniformPrefix N0 k r l) q hq (hmesh r l)
  · intro n hn
    exact hε n
  · intro hfail
    apply hnot
    simp only [flatPrefixGridFailure, Set.mem_iUnion]
    exact ⟨r, l, hfail⟩
  · exact hz

/-! ## Coefficient tail envelopes -/

/-- The scale-invariant size `√n |a n|` of the `n`th coefficient. -/
noncomputable def scaledAbs (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (n : ℝ) * |a n|

/-- The little-oh assumption makes the scale-invariant coefficient sizes tend to zero. -/
theorem scaledAbs_tendsto_zero
    (a : ℕ → ℝ) (h : DecaysFasterThanInvSqrt a) :
    Tendsto (scaledAbs a) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hevent : ∀ᶠ n : ℕ in atTop, scaledAbs a n ≤ ε / 2 := by
    filter_upwards [h.bound (half_pos hε), eventually_gt_atTop (0 : ℕ)] with n hn hn0
    have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn0)
    have habs : |a n| ≤ (ε / 2) * (Real.sqrt (n : ℝ))⁻¹ := by
      simpa only [Real.norm_eq_abs, abs_abs, abs_inv,
        abs_of_nonneg (Real.sqrt_nonneg _)] using hn
    calc
      scaledAbs a n ≤
          Real.sqrt (n : ℝ) * ((ε / 2) * (Real.sqrt (n : ℝ))⁻¹) :=
        mul_le_mul_of_nonneg_left habs (le_of_lt hsqrt)
      _ = ε / 2 := by field_simp
  rcases eventually_atTop.1 hevent with ⟨n₀, hn₀⟩
  refine ⟨n₀, fun n hn ↦ ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg]
  · exact (hn₀ n hn).trans_lt (half_lt_self hε)
  · exact mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)

/-- Values of `√n |a n|` at and beyond the `k`th cutoff. -/
def tailValues (a : ℕ → ℝ) (N : ℕ → ℕ) (k : ℕ) : Set ℝ :=
  {x | ∃ n : ℕ, N k ≤ n ∧ x = scaledAbs a n}

/-- The supremum of the scale-invariant coefficient sizes beyond the `k`th cutoff. -/
noncomputable def tailEnvelope (a : ℕ → ℝ) (N : ℕ → ℕ) (k : ℕ) : ℝ :=
  sSup (tailValues a N k)

theorem tailValues_nonempty (a : ℕ → ℝ) (N : ℕ → ℕ) (k : ℕ) :
    (tailValues a N k).Nonempty := by
  exact ⟨scaledAbs a (N k), N k, le_rfl, rfl⟩

theorem tailValues_bddAbove
    (a : ℕ → ℝ) (h : DecaysFasterThanInvSqrt a)
    (N : ℕ → ℕ) (k : ℕ) :
    BddAbove (tailValues a N k) := by
  refine (scaledAbs_tendsto_zero a h).bddAbove_range.mono ?_
  intro x hx
  rcases hx with ⟨n, hn, rfl⟩
  exact Set.mem_range_self n

/-- Every coefficient beyond a cutoff is bounded by the corresponding tail envelope. -/
theorem scaledAbs_le_tailEnvelope
    (a : ℕ → ℝ) (h : DecaysFasterThanInvSqrt a)
    (N : ℕ → ℕ) {k n : ℕ} (hn : N k ≤ n) :
    scaledAbs a n ≤ tailEnvelope a N k := by
  exact le_csSup (tailValues_bddAbove a h N k) ⟨n, hn, rfl⟩

theorem tailEnvelope_nonneg
    (a : ℕ → ℝ) (h : DecaysFasterThanInvSqrt a)
    (N : ℕ → ℕ) (k : ℕ) :
    0 ≤ tailEnvelope a N k := by
  exact (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)).trans
    (scaledAbs_le_tailEnvelope a h N (k := k) (n := N k) le_rfl)

/-- Tail envelopes decrease when their cutoff sequence increases. -/
theorem tailEnvelope_antitone
    (a : ℕ → ℝ) (h : DecaysFasterThanInvSqrt a)
    {N : ℕ → ℕ} (hN : Monotone N) :
    Antitone (tailEnvelope a N) := by
  intro k l hkl
  apply csSup_le (tailValues_nonempty a N l)
  intro x hx
  rcases hx with ⟨n, hln, rfl⟩
  exact scaledAbs_le_tailEnvelope a h N (le_trans (hN hkl) hln)

/-- Along any cutoff sequence tending to infinity, the tail envelope tends to zero. -/
theorem tailEnvelope_tendsto_zero
    (a : ℕ → ℝ) (h : DecaysFasterThanInvSqrt a)
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) :
    Tendsto (tailEnvelope a N) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hevent : ∀ᶠ n : ℕ in atTop, scaledAbs a n ≤ ε / 2 := by
    have ht := scaledAbs_tendsto_zero a h
    rcases Metric.tendsto_atTop.1 ht (ε / 2) (half_pos hε) with ⟨n₀, hn₀⟩
    filter_upwards [eventually_ge_atTop n₀] with n hn
    have hdist := hn₀ n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg] at hdist
    · exact hdist.le
    · exact mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  rcases eventually_atTop.1 hevent with ⟨n₀, hn₀⟩
  have hN_event : ∀ᶠ k : ℕ in atTop, n₀ ≤ N k := hN.eventually (eventually_ge_atTop n₀)
  rcases eventually_atTop.1 hN_event with ⟨k₀, hk₀⟩
  refine ⟨k₀, fun k hk ↦ ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (tailEnvelope_nonneg a h N k)]
  apply lt_of_le_of_lt _ (half_lt_self hε)
  apply csSup_le (tailValues_nonempty a N k)
  intro x hx
  rcases hx with ⟨n, hkn, rfl⟩
  exact hn₀ n (le_trans (hk₀ k hk) hkn)

/-- The envelope used on the explicit cubic scales.  The deterministic floor
`1 / √(k+1)` is harmless asymptotically and ensures that polynomial losses in
the Gaussian small-ball estimate can be absorbed into its exponential term. -/
noncomputable def coefficientEnvelope (a : ℕ → ℝ) (N0 k : ℕ) : ℝ :=
  max (Real.sqrt ((k + 1 : ℕ) : ℝ))⁻¹ (tailEnvelope a (scale N0) k)

lemma coefficientEnvelope_nonneg
    (a : ℕ → ℝ) (h : DecaysFasterThanInvSqrt a) (N0 k : ℕ) :
    0 ≤ coefficientEnvelope a N0 k := by
  exact le_max_of_le_right (tailEnvelope_nonneg a h (scale N0) k)

lemma inv_sqrt_succ_le_coefficientEnvelope (a : ℕ → ℝ) (N0 k : ℕ) :
    (Real.sqrt ((k + 1 : ℕ) : ℝ))⁻¹ ≤ coefficientEnvelope a N0 k :=
  le_max_left _ _

/-- Every coefficient in and after the `k`th scale obeys the explicit
coefficient envelope. -/
lemma scaledAbs_le_coefficientEnvelope
    (a : ℕ → ℝ) (h : DecaysFasterThanInvSqrt a) {N0 k n : ℕ}
    (hn : scale N0 k ≤ n) :
    scaledAbs a n ≤ coefficientEnvelope a N0 k := by
  exact (scaledAbs_le_tailEnvelope a h (scale N0) hn).trans (le_max_right _ _)

theorem coefficientEnvelope_tendsto_zero
    (a : ℕ → ℝ) (h : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) :
    Tendsto (coefficientEnvelope a N0) atTop (nhds 0) := by
  have hsucc : Tendsto (fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hfloor : Tendsto (fun k : ℕ ↦ (Real.sqrt ((k + 1 : ℕ) : ℝ))⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hsucc)
  have htail : Tendsto (tailEnvelope a (scale N0)) atTop (nhds 0) :=
    tailEnvelope_tendsto_zero a h (scale_tendsto_atTop hN0)
  change Tendsto
    (fun k : ℕ ↦ max (Real.sqrt ((k + 1 : ℕ) : ℝ))⁻¹
      (tailEnvelope a (scale N0) k)) atTop (nhds 0)
  simpa only [max_self] using hfloor.max htail

/-! ## Summable uniform-prefix exceptional events -/

/-- A deliberately very fine phase grid.  Its sixteenth-power size makes
the deterministic interpolation error negligible, while its logarithm is
still only polynomial in the scale parameter. -/
def prefixPhaseGridSize (N0 k : ℕ) : ℕ := scale N0 (k + 1) ^ 16

/-- The local oscillation tolerance.  The constant leaves enough room for
the phase-grid union bound and for replacing a grid estimate by a circle
estimate. -/
noncomputable def prefixTolerance (N0 k : ℕ) : ℝ :=
  Real.sqrt
    (2048 * Real.log (scale N0 (k + 1) : ℝ) / (2 : ℝ) ^ k)

lemma one_lt_scale_succ {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) :
    1 < scale N0 (k + 1) := by
  have htwo : 2 ≤ 2 ^ (k + 1) := by
    simpa only [pow_one] using
      Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) (by omega : 1 ≤ k + 1)
  exact lt_of_lt_of_le (by omega) (htwo.trans (two_pow_le_scale hN0 (k + 1)))

lemma prefixPhaseGridSize_pos {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) :
    0 < prefixPhaseGridSize N0 k := by
  unfold prefixPhaseGridSize
  exact pow_pos (scale_pos hN0 (k + 1)) _

noncomputable instance prefixPhaseGridSize_neZero
    (N0 k : ℕ) [NeZero N0] : NeZero (prefixPhaseGridSize N0 k) := by
  refine ⟨(prefixPhaseGridSize_pos ?_ k).ne'⟩
  exact Nat.pos_of_ne_zero (NeZero.ne N0)

lemma prefixTolerance_pos {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) :
    0 < prefixTolerance N0 k := by
  unfold prefixTolerance
  apply Real.sqrt_pos.2
  exact div_pos (mul_pos (by norm_num)
    (Real.log_pos (by exact_mod_cast one_lt_scale_succ hN0 k))) (by positivity)

lemma prefixTolerance_sq {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) :
    prefixTolerance N0 k ^ 2 =
      2048 * Real.log (scale N0 (k + 1) : ℝ) / (2 : ℝ) ^ k := by
  unfold prefixTolerance
  exact Real.sq_sqrt (le_of_lt (div_pos (mul_pos (by norm_num)
    (Real.log_pos (by exact_mod_cast one_lt_scale_succ hN0 k))) (by positivity)))

lemma log_scale_eq {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) :
    Real.log (scale N0 k : ℝ) =
      Real.log (N0 : ℝ) + (k : ℝ) ^ 3 * Real.log 2 := by
  rw [scale, Nat.cast_mul, Nat.cast_pow, Real.log_mul, Real.log_pow]
  · norm_cast
  · exact_mod_cast hN0.ne'
  · positivity

lemma log_scale_succ_div_pow_tendsto_zero {N0 : ℕ} (hN0 : 0 < N0) :
    Tendsto (fun k : ℕ ↦
      Real.log (scale N0 (k + 1) : ℝ) / (2 : ℝ) ^ k)
      atTop (𝓝 0) := by
  have hpoly : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 3 / (2 : ℝ) ^ n)
      atTop (𝓝 0) := tendsto_pow_const_div_const_pow_of_one_lt 3 (by norm_num)
  have hpolyShift : Tendsto (fun k : ℕ ↦
      ((k + 1 : ℕ) : ℝ) ^ 3 / (2 : ℝ) ^ (k + 1)) atTop (𝓝 0) :=
    hpoly.comp (tendsto_add_atTop_nat 1)
  have hpoly' : Tendsto (fun k : ℕ ↦
      ((k + 1 : ℕ) : ℝ) ^ 3 / (2 : ℝ) ^ k) atTop (𝓝 0) := by
    convert hpolyShift.const_mul 2 using 1
    · ext k
      rw [show (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ k * 2 by rw [pow_succ]]
      field_simp
    · norm_num
  have hconst : Tendsto (fun k : ℕ ↦
      Real.log (N0 : ℝ) / (2 : ℝ) ^ k) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 : ℝ) / 2 < 1)).const_mul (Real.log (N0 : ℝ))
  have hsum := hconst.add (hpoly'.const_mul (Real.log 2))
  simpa only [zero_add, mul_zero] using hsum.congr' (Filter.Eventually.of_forall fun k ↦ by
    rw [log_scale_eq hN0]
    ring)

lemma prefixTolerance_tendsto_zero {N0 : ℕ} (hN0 : 0 < N0) :
    Tendsto (prefixTolerance N0) atTop (𝓝 0) := by
  have harg : Tendsto (fun k : ℕ ↦
      2048 * Real.log (scale N0 (k + 1) : ℝ) / (2 : ℝ) ^ k)
      atTop (𝓝 0) := by
    simpa [mul_div_assoc] using
      (log_scale_succ_div_pow_tendsto_zero hN0).const_mul 2048
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp harg
  change Tendsto (fun k : ℕ ↦ Real.sqrt
    (2048 * Real.log (scale N0 (k + 1) : ℝ) / (2 : ℝ) ^ k)) atTop (𝓝 0)
  rw [Real.sqrt_zero] at hsqrt
  exact hsqrt.congr' (Filter.Eventually.of_forall fun _ ↦ rfl)

lemma inv_scale_succ_le_prefixTolerance {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) :
    (scale N0 (k + 1) : ℝ)⁻¹ ≤ prefixTolerance N0 k := by
  let S : ℝ := scale N0 (k + 1)
  have hS : 0 < S := by
    change (0 : ℝ) < (scale N0 (k + 1) : ℝ)
    exact_mod_cast scale_pos hN0 (k + 1)
  have hS2 : 2 ≤ S := by
    have htwoNat : 2 ≤ 2 ^ (k + 1) := by
      simpa only [pow_one] using Nat.pow_le_pow_right
        (by norm_num : 0 < (2 : ℕ)) (by omega : 1 ≤ k + 1)
    have hNat : 2 ≤ scale N0 (k + 1) :=
      htwoNat.trans (two_pow_le_scale hN0 (k + 1))
    dsimp only [S]
    exact_mod_cast hNat
  have hpowS : (2 : ℝ) ^ k ≤ S := by
    have hNat := (two_pow_le_scale hN0 k).trans
      (scale_monotone N0 (by omega : k ≤ k + 1))
    dsimp only [S]
    exact_mod_cast hNat
  have hlog : (1 / 2 : ℝ) ≤ Real.log S := by
    have hlogmono : Real.log 2 ≤ Real.log S := Real.log_le_log (by norm_num) hS2
    have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    exact hhalf.trans hlogmono
  have hlog0 : 0 ≤ Real.log S := (by norm_num : (0 : ℝ) ≤ 1 / 2).trans hlog
  rw [← sq_le_sq₀ (inv_nonneg.mpr hS.le) (prefixTolerance_pos hN0 k).le,
    prefixTolerance_sq hN0 k]
  field_simp
  nlinarith [mul_nonneg hS.le hS.le, mul_nonneg hlog0 hS.le]

/-- At the chosen tolerance, Hoeffding beats the sixteenth-power phase grid
by a fixed negative power of the next scale. -/
lemma measureReal_flatPrefixGridFailure_envelope_le
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} [NeZero N0] (hN0 : 0 < N0) (k : ℕ)
    (henv : coefficientEnvelope a N0 k ≤ 1) :
    rademacherProductMeasure.real
        (flatPrefixGridFailure a N0 k (prefixPhaseGridSize N0 k)
          (prefixTolerance N0 k / 2)) ≤
      4 * (scale N0 (k + 1) : ℝ) ^ (-(47 : ℝ)) := by
  let δ := coefficientEnvelope a N0 k
  let S : ℝ := scale N0 (k + 1)
  have hδ0 : 0 < δ := by
    exact lt_of_lt_of_le (inv_pos.mpr (Real.sqrt_pos.2 (by positivity)))
      (inv_sqrt_succ_le_coefficientEnvelope a N0 k)
  have hδnonneg : 0 ≤ δ := hδ0.le
  have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ0
  have hδsqone : δ ^ 2 ≤ 1 := by nlinarith [sq_nonneg (1 - δ)]
  have hS : 0 < S := by
    change (0 : ℝ) < (scale N0 (k + 1) : ℝ)
    exact_mod_cast scale_pos hN0 (k + 1)
  have hlogS : 0 < Real.log S := by
    apply Real.log_pos
    change (1 : ℝ) < (scale N0 (k + 1) : ℝ)
    exact_mod_cast one_lt_scale_succ hN0 k
  have hscaled : ∀ (r : Fin (uniformBlockCount k)) n,
      n ∈ uniformBlock N0 k r → scaledAbs a n ≤ δ := by
    intro r n hn
    exact scaledAbs_le_coefficientEnvelope a hsmall
      ((uniformBlock_start_ge_scale N0 k r).trans (mem_uniformBlock_iff.mp hn).1)
  have hraw := measureReal_flatPrefixGridFailure_le a hδnonneg hN0 k
    (prefixPhaseGridSize N0 k) hscaled
    (div_nonneg (prefixTolerance_pos hN0 k).le (by norm_num : (0 : ℝ) ≤ 2))
  have hexponent : 64 * Real.log S ≤
      ((prefixTolerance N0 k / 2) / 2) ^ 2 /
        (2 * (δ ^ 2 / 2 ^ k)) := by
    have ht := prefixTolerance_sq hN0 k
    change 64 * Real.log S ≤
      ((prefixTolerance N0 k / 2) / 2) ^ 2 /
        (2 * (δ ^ 2 / (2 : ℝ) ^ k))
    rw [div_pow, div_pow, ht]
    field_simp
    nlinarith [mul_nonneg hlogS.le (sub_nonneg.mpr hδsqone)]
  have hexp : Real.exp
      (-((prefixTolerance N0 k / 2) / 2) ^ 2 /
        (2 * (δ ^ 2 / 2 ^ k))) ≤ S ^ (-(64 : ℝ)) := by
    rw [Real.rpow_def_of_pos hS]
    apply Real.exp_le_exp.mpr
    calc
      -((prefixTolerance N0 k / 2) / 2) ^ 2 /
          (2 * (δ ^ 2 / 2 ^ k)) =
          -(((prefixTolerance N0 k / 2) / 2) ^ 2 /
            (2 * (δ ^ 2 / 2 ^ k))) := by ring
      _ ≤ -(64 * Real.log S) := neg_le_neg hexponent
      _ = Real.log S * -64 := by ring
  calc
    rademacherProductMeasure.real
        (flatPrefixGridFailure a N0 k (prefixPhaseGridSize N0 k)
          (prefixTolerance N0 k / 2))
      ≤ uniformBlockCount k * uniformBlockLength N0 k *
          (prefixPhaseGridSize N0 k *
            (4 * Real.exp
              (-((prefixTolerance N0 k / 2) / 2) ^ 2 /
                (2 * (δ ^ 2 / 2 ^ k))))) := hraw
    _ ≤ uniformBlockCount k * uniformBlockLength N0 k *
          (prefixPhaseGridSize N0 k * (4 * S ^ (-(64 : ℝ)))) := by
      gcongr
    _ ≤ 4 * S ^ (-(47 : ℝ)) := by
      have hgap : (uniformBlockCount k * uniformBlockLength N0 k : ℝ) ≤ S := by
        dsimp only [S]
        norm_cast
        rw [← scale_gap_eq_uniformBlockCount_mul_length]
        omega
      have hq : (prefixPhaseGridSize N0 k : ℝ) = S ^ 16 := by
        simp only [prefixPhaseGridSize, S]
        norm_cast
      rw [hq]
      calc
        (uniformBlockCount k : ℝ) * uniformBlockLength N0 k *
            (S ^ 16 * (4 * S ^ (-(64 : ℝ))))
          ≤ S * (S ^ 16 * (4 * S ^ (-(64 : ℝ)))) := by gcongr
        _ = 4 * S ^ (-(47 : ℝ)) := by
          rw [Real.rpow_neg hS.le, Real.rpow_neg hS.le]
          norm_num [Real.rpow_natCast]
          field_simp

/-- A summable pointwise majorant which also covers the finitely many early
scales where the coefficient envelope has not yet dropped below one. -/
noncomputable def prefixFailureBound (a : ℕ → ℝ) (N0 k : ℕ) : ℝ :=
  if coefficientEnvelope a N0 k ≤ 1 then
    4 * (scale N0 (k + 1) : ℝ) ^ (-(47 : ℝ))
  else 1

lemma summable_prefixFailureBound
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) :
    Summable (prefixFailureBound a N0) := by
  have hbase : Summable
      (fun k : ℕ ↦ 4 * (scale N0 (k + 1) : ℝ) ^ (-(47 : ℝ))) := by
    have h := summable_scale_rpow_neg (N0 := N0) hN0 (c := 47) (by norm_num)
    exact (h.comp_injective (fun _ _ hxy ↦ Nat.add_right_cancel hxy)).mul_left 4
  apply hbase.congr_atTop
  filter_upwards [eventually_le_of_tendsto_zero
    (coefficientEnvelope_tendsto_zero a hsmall hN0) (by norm_num : (0 : ℝ) < 1)]
    with k hk
  simp [prefixFailureBound, hk]

/-- Almost surely, every sufficiently late flat block has every partial sum
small simultaneously at all points of the phase grid. -/
theorem ae_eventually_not_flatPrefixGridFailure
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} [NeZero N0] (hN0 : 0 < N0) :
    ∀ᵐ ε ∂rademacherProductMeasure, ∀ᶠ k : ℕ in atTop,
      ε ∉ flatPrefixGridFailure a N0 k (prefixPhaseGridSize N0 k)
        (prefixTolerance N0 k / 2) := by
  apply ae_eventually_notMem_of_measureReal_le
    (fun k ↦ flatPrefixGridFailure a N0 k (prefixPhaseGridSize N0 k)
      (prefixTolerance N0 k / 2))
    (prefixFailureBound a N0)
    (summable_prefixFailureBound a hsmall hN0)
  intro k
  by_cases hk : coefficientEnvelope a N0 k ≤ 1
  · simpa [prefixFailureBound, hk] using
      measureReal_flatPrefixGridFailure_envelope_le a hsmall hN0 k hk
  · simpa [prefixFailureBound, hk] using
      (measureReal_le_one (μ := rademacherProductMeasure)
        (flatPrefixGridFailure a N0 k (prefixPhaseGridSize N0 k)
          (prefixTolerance N0 k / 2)))

lemma prefix_phase_mesh_error_le
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} [NeZero N0] (hN0 : 0 < N0) (k : ℕ)
    (henv : coefficientEnvelope a N0 k ≤ 1)
    (r : Fin (uniformBlockCount k))
    (l : Fin (uniformBlockLength N0 k)) :
    (4 * Real.pi / prefixPhaseGridSize N0 k) *
        (∑ n ∈ uniformPrefix N0 k r l, |a n| * n) ≤
      prefixTolerance N0 k / 2 := by
  let S : ℝ := scale N0 (k + 1)
  have hS : 0 < S := by
    change (0 : ℝ) < (scale N0 (k + 1) : ℝ)
    exact_mod_cast scale_pos hN0 (k + 1)
  have hS2 : 2 ≤ S := by
    have hNat : 2 ≤ scale N0 (k + 1) := by
      have htwo : 2 ≤ 2 ^ (k + 1) := by
        simpa only [pow_one] using Nat.pow_le_pow_right
          (by norm_num : 0 < (2 : ℕ)) (by omega : 1 ≤ k + 1)
      exact htwo.trans (two_pow_le_scale hN0 (k + 1))
    dsimp only [S]
    exact_mod_cast hNat
  have hscaled : ∀ n ∈ uniformBlock N0 k r,
      Real.sqrt (n : ℝ) * |a n| ≤ 1 := by
    intro n hn
    exact (scaledAbs_le_coefficientEnvelope a hsmall
      ((uniformBlock_start_ge_scale N0 k r).trans
        (mem_uniformBlock_iff.mp hn).1)).trans henv
  have hsum := sum_abs_mul_index_uniformPrefix_le_scale_sq
    a hN0 r l hscaled
  have hq : (prefixPhaseGridSize N0 k : ℝ) = S ^ 16 := by
    simp only [prefixPhaseGridSize, S]
    norm_cast
  have hpow5 : (32 : ℝ) ≤ S ^ 5 := by
    calc
      (32 : ℝ) = 2 ^ 5 := by norm_num
      _ ≤ S ^ 5 := pow_le_pow_left₀ (by norm_num) hS2 5
  have hpow13 : (32 : ℝ) ≤ S ^ 13 :=
    hpow5.trans (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ S) (by norm_num))
  calc
    (4 * Real.pi / prefixPhaseGridSize N0 k) *
        (∑ n ∈ uniformPrefix N0 k r l, |a n| * n)
      ≤ (4 * Real.pi / prefixPhaseGridSize N0 k) * S ^ 2 := by
        exact mul_le_mul_of_nonneg_left hsum (div_nonneg (by positivity) (by positivity))
    _ = 4 * Real.pi / S ^ 14 := by
      rw [hq]
      field_simp
    _ ≤ 16 / S ^ 14 := by
      gcongr
      linarith [Real.pi_le_four]
    _ ≤ S⁻¹ / 2 := by
      rw [inv_eq_one_div, div_div]
      apply (div_le_div_iff₀ (pow_pos hS 14)
        (mul_pos hS (by norm_num : (0 : ℝ) < 2))).2
      have hmul := mul_le_mul_of_nonneg_left hpow13 hS.le
      rw [show S ^ 14 = S * S ^ 13 by ring]
      nlinarith
    _ ≤ prefixTolerance N0 k / 2 := by
      gcongr
      exact inv_scale_succ_le_prefixTolerance hN0 k

/-- Combining the summable grid exceptions with deterministic interpolation,
all sufficiently late flat-block prefixes are uniformly small on the whole
unit circle, almost surely. -/
theorem ae_eventually_flatPrefix_uniform_bound
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} [NeZero N0] (hN0 : 0 < N0) :
    ∀ᵐ ε ∂rademacherProductMeasure, ∀ᶠ k : ℕ in atTop,
      ∀ (r : Fin (uniformBlockCount k))
        (l : Fin (uniformBlockLength N0 k)) (z : ℂ), ‖z‖ = 1 →
        ‖signedPolynomial a ε (uniformPrefix N0 k r l) z‖ <
          prefixTolerance N0 k := by
  filter_upwards [ae_eventually_not_flatPrefixGridFailure a hsmall hN0,
    ae_rademacherProduct_signs] with ε hnot hsigns
  have henv : ∀ᶠ k : ℕ in atTop, coefficientEnvelope a N0 k ≤ 1 :=
    eventually_le_of_tendsto_zero
      (coefficientEnvelope_tendsto_zero a hsmall hN0) (by norm_num)
  filter_upwards [hnot, henv] with k hknot hkenv
  have hq8 : 8 ≤ prefixPhaseGridSize N0 k := by
    have hs2 : 2 ≤ scale N0 (k + 1) := by
      have htwo : 2 ≤ 2 ^ (k + 1) := by
        simpa only [pow_one] using Nat.pow_le_pow_right
          (by norm_num : 0 < (2 : ℕ)) (by omega : 1 ≤ k + 1)
      exact htwo.trans (two_pow_le_scale hN0 (k + 1))
    unfold prefixPhaseGridSize
    calc
      8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ 16 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
      _ ≤ scale N0 (k + 1) ^ 16 := Nat.pow_le_pow_left hs2 16
  exact flatPrefix_uniform_bound_of_not_failure a ε
    (N0 := N0) (k := k) (q := prefixPhaseGridSize N0 k)
    (t := prefixTolerance N0 k) hq8
    (fun r l ↦ prefix_phase_mesh_error_le a hsmall hN0 k hkenv r l)
    (fun n ↦ by rcases hsigns n with h | h <;> simp [h]) hknot

namespace DerivativeEvents

/-- The coefficient sequence of the angular derivative. -/
def derivativeCoefficient (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * a n

/-- The signed angular-derivative polynomial on a finite set of indices. -/
def signedDerivativePolynomial (a ε : ℕ → ℝ) (s : Finset ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ s, (((ε n * (n : ℝ) * a n : ℝ) : ℂ) * z ^ n)

lemma signedPolynomial_derivativeCoefficient
    (a ε : ℕ → ℝ) (s : Finset ℕ) (z : ℂ) :
    signedPolynomial (derivativeCoefficient a) ε s z =
      signedDerivativePolynomial a ε s z := by
  apply Finset.sum_congr rfl
  intro n hn
  simp only [derivativeCoefficient]
  push_cast
  ring

/-- The cumulative prefix from the start of scale `k` to endpoint `l`. -/
def scalePrefix (N0 k l : ℕ) : Finset ℕ :=
  Finset.Ico (scale N0 k) l

/-- The target derivative size on the `k`th whole scale. -/
noncomputable def derivativeThreshold (N0 k : ℕ) : ℝ :=
  (scale N0 (k + 1) : ℝ) * Real.log (scale N0 (k + 1) : ℝ)

lemma derivativeThreshold_pos {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) :
    0 < derivativeThreshold N0 k := by
  exact mul_pos (by exact_mod_cast scale_pos hN0 (k + 1))
    (Real.log_pos (by exact_mod_cast one_lt_scale_succ hN0 k))

lemma scalePrefix_subset_range_succ {N0 k l : ℕ}
    (hl : l ≤ scale N0 (k + 1)) :
    scalePrefix N0 k l ⊆ Finset.range (scale N0 (k + 1)) := by
  intro n hn
  exact Finset.mem_range.mpr ((Finset.mem_Ico.mp hn).2.trans_le hl)

lemma card_scalePrefix_le_scale_succ {N0 k l : ℕ}
    (hl : l ≤ scale N0 (k + 1)) :
    (scalePrefix N0 k l).card ≤ scale N0 (k + 1) := by
  exact (Finset.card_le_card (scalePrefix_subset_range_succ hl)).trans_eq
    (Finset.card_range _)

/-- Under the coefficient envelope bound, each squared derivative coefficient
in a whole-scale prefix is at most the next scale. -/
lemma derivativeCoefficient_sq_le_scale_succ
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) {k l n : ℕ}
    (henv : coefficientEnvelope a N0 k ≤ 1)
    (hn : n ∈ scalePrefix N0 k l)
    (hl : l ≤ scale N0 (k + 1)) :
    |derivativeCoefficient a n| ^ 2 ≤ (scale N0 (k + 1) : ℝ) := by
  have hnIco := Finset.mem_Ico.mp hn
  have hscaled : scaledAbs a n ≤ 1 :=
    (scaledAbs_le_coefficientEnvelope a hsmall hnIco.1).trans henv
  have hscaled0 : 0 ≤ scaledAbs a n :=
    mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  have hscaledSq : scaledAbs a n ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (scaledAbs a n - 1)]
  have hnS : (n : ℝ) ≤ scale N0 (k + 1) := by
    exact_mod_cast hnIco.2.le.trans hl
  have hsqrtSq : Real.sqrt (n : ℝ) ^ 2 = n :=
    Real.sq_sqrt (Nat.cast_nonneg n)
  calc
    |derivativeCoefficient a n| ^ 2 =
        (n : ℝ) * scaledAbs a n ^ 2 := by
      rw [derivativeCoefficient, scaledAbs, abs_mul,
        abs_of_nonneg (Nat.cast_nonneg n)]
      calc
        ((n : ℝ) * |a n|) ^ 2 =
            (n : ℝ) * (Real.sqrt (n : ℝ) ^ 2 * |a n| ^ 2) := by
          rw [hsqrtSq]
          ring
        _ = (n : ℝ) * (Real.sqrt (n : ℝ) * |a n|) ^ 2 := by
          rw [mul_pow]
    _ ≤ (n : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hscaledSq (Nat.cast_nonneg n)
    _ ≤ (scale N0 (k + 1) : ℝ) := by simpa using hnS

/-- The full cumulative derivative prefix has square energy at most `S²`. -/
lemma realSquareEnergy_derivative_scalePrefix_le
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) {k l : ℕ}
    (henv : coefficientEnvelope a N0 k ≤ 1)
    (hl : l ≤ scale N0 (k + 1)) :
    realSquareEnergy (derivativeCoefficient a) (scalePrefix N0 k l) ≤
      ⟨(scale N0 (k + 1) : ℝ) ^ 2, sq_nonneg _⟩ := by
  apply NNReal.coe_le_coe.mp
  rw [realSquareEnergy,
    Real.coe_toNNReal _ (Finset.sum_nonneg fun n _ ↦ sq_nonneg
      |derivativeCoefficient a n|)]
  change (∑ n ∈ scalePrefix N0 k l, |derivativeCoefficient a n| ^ 2) ≤
    (scale N0 (k + 1) : ℝ) ^ 2
  let S : ℝ := scale N0 (k + 1)
  have hcard : ((scalePrefix N0 k l).card : ℝ) ≤ S := by
    dsimp only [S]
    exact_mod_cast card_scalePrefix_le_scale_succ hl
  calc
    (∑ n ∈ scalePrefix N0 k l, |derivativeCoefficient a n| ^ 2)
      ≤ ∑ _n ∈ scalePrefix N0 k l, S := by
        exact Finset.sum_le_sum fun n hn ↦
          derivativeCoefficient_sq_le_scale_succ a hsmall hN0 henv hn hl
    _ = (scalePrefix N0 k l).card * S := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ S * S := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (scale N0 (k + 1) : ℝ) ^ 2 := by simp only [S, pow_two]

/-- Failure at one of all `S+1` possible cumulative endpoints, detected on
the finite root grid. -/
noncomputable def derivativeGridFailure (a : ℕ → ℝ) (N0 k : ℕ)
    [NeZero N0] : Set (ℕ → ℝ) :=
  ⋃ l : Fin (scale N0 (k + 1) + 1),
    gridPolynomialFailure (derivativeCoefficient a)
      (scalePrefix N0 k l.val) (prefixPhaseGridSize N0 k)
      (derivativeThreshold N0 k / 2)

/-- Once `log S` is large enough, Hoeffding beats both the `S+1` cumulative
endpoints and the sixteenth-power phase grid. -/
lemma measureReal_derivativeGridFailure_le
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} [NeZero N0] (hN0 : 0 < N0) (k : ℕ)
    (henv : coefficientEnvelope a N0 k ≤ 1)
    (hk : (2080 : ℝ) ≤ Real.log (scale N0 (k + 1) : ℝ)) :
    rademacherProductMeasure.real (derivativeGridFailure a N0 k) ≤
      4 * (scale N0 (k + 1) : ℝ) ^ (-(47 : ℝ)) := by
  let S : ℝ := scale N0 (k + 1)
  have hS : 0 < S := by
    change (0 : ℝ) < (scale N0 (k + 1) : ℝ)
    exact_mod_cast scale_pos hN0 (k + 1)
  have hS2 : 2 ≤ S := by
    have htwo : 2 ≤ 2 ^ (k + 1) := by
      simpa only [pow_one] using Nat.pow_le_pow_right
        (by norm_num : 0 < (2 : ℕ)) (by omega : 1 ≤ k + 1)
    dsimp only [S]
    exact_mod_cast htwo.trans (two_pow_le_scale hN0 (k + 1))
  have hlogS : 0 < Real.log S := Real.log_pos (lt_of_lt_of_le (by norm_num) hS2)
  have hmeasure : ∀ l : Fin (scale N0 (k + 1) + 1),
      rademacherProductMeasure.real
        (gridPolynomialFailure (derivativeCoefficient a)
          (scalePrefix N0 k l.val) (prefixPhaseGridSize N0 k)
          (derivativeThreshold N0 k / 2)) ≤
        prefixPhaseGridSize N0 k *
          (4 * Real.exp
            (-((derivativeThreshold N0 k / 2) / 2) ^ 2 /
              (2 * S ^ 2))) := by
    intro l
    have hl : l.val ≤ scale N0 (k + 1) := by omega
    have hv := realSquareEnergy_derivative_scalePrefix_le
      a hsmall hN0 henv hl
    have h := measureReal_gridPolynomialFailure_le
      (derivativeCoefficient a) (scalePrefix N0 k l.val)
      (prefixPhaseGridSize N0 k)
      ⟨S ^ 2, sq_nonneg S⟩ hv
      (t := derivativeThreshold N0 k / 2)
      (div_nonneg (derivativeThreshold_pos hN0 k).le (by norm_num))
    change rademacherProductMeasure.real
        (gridPolynomialFailure (derivativeCoefficient a)
          (scalePrefix N0 k l.val) (prefixPhaseGridSize N0 k)
          (derivativeThreshold N0 k / 2)) ≤
      prefixPhaseGridSize N0 k *
        (4 * Real.exp
          (-((derivativeThreshold N0 k / 2) / 2) ^ 2 /
            (2 * S ^ 2))) at h
    exact h
  have hexponent : 65 * Real.log S ≤
      ((derivativeThreshold N0 k / 2) / 2) ^ 2 / (2 * S ^ 2) := by
    rw [derivativeThreshold]
    change 65 * Real.log S ≤
      (((S * Real.log S) / 2) / 2) ^ 2 / (2 * S ^ 2)
    field_simp
    have hprod : 0 ≤ (Real.log S - 2080) * Real.log S :=
      mul_nonneg (sub_nonneg.mpr (by simpa only [S] using hk)) hlogS.le
    nlinarith
  have hexp : Real.exp
      (-((derivativeThreshold N0 k / 2) / 2) ^ 2 / (2 * S ^ 2)) ≤
      S ^ (-(65 : ℝ)) := by
    rw [Real.rpow_def_of_pos hS]
    apply Real.exp_le_exp.mpr
    calc
      -((derivativeThreshold N0 k / 2) / 2) ^ 2 / (2 * S ^ 2) =
          -(((derivativeThreshold N0 k / 2) / 2) ^ 2 / (2 * S ^ 2)) := by ring
      _ ≤ -(65 * Real.log S) := neg_le_neg hexponent
      _ = Real.log S * -65 := by ring
  unfold derivativeGridFailure
  calc
    rademacherProductMeasure.real
        (⋃ l : Fin (scale N0 (k + 1) + 1),
          gridPolynomialFailure (derivativeCoefficient a)
            (scalePrefix N0 k l.val) (prefixPhaseGridSize N0 k)
            (derivativeThreshold N0 k / 2))
      ≤ ∑ l : Fin (scale N0 (k + 1) + 1),
          rademacherProductMeasure.real
            (gridPolynomialFailure (derivativeCoefficient a)
              (scalePrefix N0 k l.val) (prefixPhaseGridSize N0 k)
              (derivativeThreshold N0 k / 2)) :=
        measureReal_iUnion_fintype_le _
    _ ≤ ∑ _l : Fin (scale N0 (k + 1) + 1),
          prefixPhaseGridSize N0 k *
            (4 * Real.exp
              (-((derivativeThreshold N0 k / 2) / 2) ^ 2 /
                (2 * S ^ 2))) := by
      gcongr with l
      exact hmeasure l
    _ = (scale N0 (k + 1) + 1) *
          (prefixPhaseGridSize N0 k *
            (4 * Real.exp
              (-((derivativeThreshold N0 k / 2) / 2) ^ 2 /
                (2 * S ^ 2)))) := by simp
    _ ≤ (2 * S) * (S ^ 16 * (4 * S ^ (-(65 : ℝ)))) := by
      have hcard : (scale N0 (k + 1) + 1 : ℝ) ≤ 2 * S := by
        push_cast
        dsimp only [S]
        nlinarith
      have hq : (prefixPhaseGridSize N0 k : ℝ) = S ^ 16 := by
        simp only [prefixPhaseGridSize, S]
        norm_cast
      rw [hq]
      gcongr
    _ ≤ 4 * S ^ (-(47 : ℝ)) := by
      rw [Real.rpow_neg hS.le, Real.rpow_neg hS.le]
      norm_num [Real.rpow_natCast]
      field_simp
      nlinarith

/-- A summable majorant, equal to one on the finitely many early or
large-envelope scales. -/
noncomputable def derivativeFailureBound (a : ℕ → ℝ) (N0 k : ℕ) : ℝ :=
  if coefficientEnvelope a N0 k ≤ 1 ∧
      (2080 : ℝ) ≤ Real.log (scale N0 (k + 1) : ℝ) then
    4 * (scale N0 (k + 1) : ℝ) ^ (-(47 : ℝ))
  else 1

lemma log_scale_succ_tendsto_atTop {N0 : ℕ} (hN0 : 0 < N0) :
    Tendsto (fun k : ℕ ↦ Real.log (scale N0 (k + 1) : ℝ)) atTop atTop := by
  exact Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp
      ((scale_tendsto_atTop hN0).comp (tendsto_add_atTop_nat 1)))

lemma eventually_derivative_log_large {N0 : ℕ} (hN0 : 0 < N0) :
    ∀ᶠ k : ℕ in atTop,
      (2080 : ℝ) ≤ Real.log (scale N0 (k + 1) : ℝ) :=
  (log_scale_succ_tendsto_atTop hN0).eventually_ge_atTop 2080

lemma summable_derivativeFailureBound
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) :
    Summable (derivativeFailureBound a N0) := by
  have hbase : Summable
      (fun k : ℕ ↦ 4 * (scale N0 (k + 1) : ℝ) ^ (-(47 : ℝ))) := by
    have h := summable_scale_rpow_neg (N0 := N0) hN0 (c := 47) (by norm_num)
    exact (h.comp_injective (fun _ _ hxy ↦ Nat.add_right_cancel hxy)).mul_left 4
  apply hbase.congr_atTop
  filter_upwards [eventually_le_of_tendsto_zero
      (coefficientEnvelope_tendsto_zero a hsmall hN0)
      (by norm_num : (0 : ℝ) < 1),
    eventually_derivative_log_large hN0] with k henv hk
  simp [derivativeFailureBound, henv, hk]

/-- Almost surely, every sufficiently late whole-scale cumulative derivative
prefix is below half the target threshold on the finite root grid. -/
theorem ae_eventually_not_derivativeGridFailure
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} [NeZero N0] (hN0 : 0 < N0) :
    ∀ᵐ ε ∂rademacherProductMeasure, ∀ᶠ k : ℕ in atTop,
      ε ∉ derivativeGridFailure a N0 k := by
  apply ae_eventually_notMem_of_measureReal_le
    (fun k ↦ derivativeGridFailure a N0 k) (derivativeFailureBound a N0)
    (summable_derivativeFailureBound a hsmall hN0)
  intro k
  by_cases hk : coefficientEnvelope a N0 k ≤ 1 ∧
      (2080 : ℝ) ≤ Real.log (scale N0 (k + 1) : ℝ)
  · simpa [derivativeFailureBound, hk] using
      measureReal_derivativeGridFailure_le a hsmall hN0 k hk.1 hk.2
  · simpa [derivativeFailureBound, hk] using
      (measureReal_le_one rademacherProductMeasure
        (derivativeGridFailure a N0 k))

/-- A deterministic second-derivative/Lipschitz budget for every cumulative
prefix in the whole scale. -/
lemma sum_abs_derivative_mul_index_scalePrefix_le_scale_cube
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) {k l : ℕ}
    (henv : coefficientEnvelope a N0 k ≤ 1)
    (hl : l ≤ scale N0 (k + 1)) :
    (∑ n ∈ scalePrefix N0 k l, |derivativeCoefficient a n| * n) ≤
      (scale N0 (k + 1) : ℝ) ^ 3 := by
  let S : ℝ := scale N0 (k + 1)
  have hscale1 : 1 ≤ scale N0 k := scale_pos hN0 k
  have hsqrt1 : 1 ≤ Real.sqrt (scale N0 k : ℝ) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hscale1
  have hsqrtpos : 0 < Real.sqrt (scale N0 k : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast scale_pos hN0 k)
  have hterm : ∀ n ∈ scalePrefix N0 k l,
      |derivativeCoefficient a n| * (n : ℝ) ≤ S ^ 2 := by
    intro n hn
    have hnIco := Finset.mem_Ico.mp hn
    have hscaled : scaledAbs a n ≤ 1 :=
      (scaledAbs_le_coefficientEnvelope a hsmall hnIco.1).trans henv
    have habs : |a n| ≤ 1 := by
      exact (abs_le_div_sqrt_of_scaled_le (scale_pos hN0 k) hnIco.1 hscaled).trans
        ((div_le_one hsqrtpos).2 hsqrt1)
    have hnS : (n : ℝ) ≤ S := by
      change (n : ℝ) ≤ (scale N0 (k + 1) : ℝ)
      exact_mod_cast hnIco.2.le.trans hl
    rw [derivativeCoefficient, abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
    calc
      (n : ℝ) * |a n| * n ≤ (n : ℝ) * 1 * n := by gcongr
      _ ≤ S * S := by
        simpa only [mul_one] using mul_self_le_mul_self (Nat.cast_nonneg n) hnS
      _ = S ^ 2 := by ring
  have hcard : ((scalePrefix N0 k l).card : ℝ) ≤ S := by
    dsimp only [S]
    exact_mod_cast card_scalePrefix_le_scale_succ hl
  calc
    (∑ n ∈ scalePrefix N0 k l, |derivativeCoefficient a n| * n)
      ≤ ∑ _n ∈ scalePrefix N0 k l, S ^ 2 := by
        exact Finset.sum_le_sum fun n hn ↦ hterm n hn
    _ = (scalePrefix N0 k l).card * S ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ S * S ^ 2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg S)
    _ = (scale N0 (k + 1) : ℝ) ^ 3 := by simp only [S]; ring

lemma derivative_phase_mesh_error_le
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} [NeZero N0] (hN0 : 0 < N0) (k l : ℕ)
    (henv : coefficientEnvelope a N0 k ≤ 1)
    (hl : l ≤ scale N0 (k + 1)) :
    (4 * Real.pi / prefixPhaseGridSize N0 k) *
        (∑ n ∈ scalePrefix N0 k l, |derivativeCoefficient a n| * n) ≤
      derivativeThreshold N0 k / 2 := by
  let S : ℝ := scale N0 (k + 1)
  have hS : 0 < S := by
    change (0 : ℝ) < (scale N0 (k + 1) : ℝ)
    exact_mod_cast scale_pos hN0 (k + 1)
  have hS2 : 2 ≤ S := by
    have htwo : 2 ≤ 2 ^ (k + 1) := by
      simpa only [pow_one] using Nat.pow_le_pow_right
        (by norm_num : 0 < (2 : ℕ)) (by omega : 1 ≤ k + 1)
    dsimp only [S]
    exact_mod_cast htwo.trans (two_pow_le_scale hN0 (k + 1))
  have hlogHalf : (1 / 2 : ℝ) ≤ Real.log S := by
    have hm : Real.log 2 ≤ Real.log S := Real.log_le_log (by norm_num) hS2
    nlinarith [Real.log_two_gt_d9]
  have hsum := sum_abs_derivative_mul_index_scalePrefix_le_scale_cube
    a hsmall hN0 henv hl
  have hq : (prefixPhaseGridSize N0 k : ℝ) = S ^ 16 := by
    simp only [prefixPhaseGridSize, S]
    norm_cast
  calc
    (4 * Real.pi / prefixPhaseGridSize N0 k) *
        (∑ n ∈ scalePrefix N0 k l, |derivativeCoefficient a n| * n)
      ≤ (4 * Real.pi / prefixPhaseGridSize N0 k) * S ^ 3 := by
        exact mul_le_mul_of_nonneg_left hsum
          (div_nonneg (by positivity) (by positivity))
    _ = 4 * Real.pi / S ^ 13 := by rw [hq]; field_simp
    _ ≤ 16 / S ^ 13 := by
      gcongr
      linarith [Real.pi_le_four]
    _ ≤ S / 4 := by
      apply (div_le_iff₀ (pow_pos hS 13)).2
      have hp : (64 : ℝ) ≤ S ^ 14 := by
        calc
          (64 : ℝ) = 2 ^ 6 := by norm_num
          _ ≤ S ^ 6 := pow_le_pow_left₀ (by norm_num) hS2 6
          _ ≤ S ^ 14 := pow_le_pow_right₀ (by linarith) (by norm_num)
      calc
        (16 : ℝ) ≤ S ^ 14 / 4 := by nlinarith
        _ = S / 4 * S ^ 13 := by ring
    _ ≤ derivativeThreshold N0 k / 2 := by
      rw [derivativeThreshold]
      change S / 4 ≤ S * Real.log S / 2
      nlinarith

/-- Almost surely, every sufficiently late cumulative derivative prefix from
`scale k` to any endpoint through `scale (k+1)` is uniformly bounded by
`S log S` on the whole unit circle. -/
theorem ae_eventually_derivativeScalePrefix_uniform_bound
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} [NeZero N0] (hN0 : 0 < N0) :
    ∀ᵐ ε ∂rademacherProductMeasure, ∀ᶠ k : ℕ in atTop,
      ∀ l : ℕ, scale N0 k ≤ l → l ≤ scale N0 (k + 1) →
        ∀ z : ℂ, ‖z‖ = 1 →
          ‖signedDerivativePolynomial a ε (scalePrefix N0 k l) z‖ <
            derivativeThreshold N0 k := by
  filter_upwards [ae_eventually_not_derivativeGridFailure a hsmall hN0,
    ae_rademacherProduct_signs] with ε hnot hsigns
  have henv : ∀ᶠ k : ℕ in atTop, coefficientEnvelope a N0 k ≤ 1 :=
    eventually_le_of_tendsto_zero
      (coefficientEnvelope_tendsto_zero a hsmall hN0) (by norm_num)
  filter_upwards [hnot, henv] with k hknot hkenv
  have hq8 : 8 ≤ prefixPhaseGridSize N0 k := by
    have hs2 : 2 ≤ scale N0 (k + 1) := by
      have htwo : 2 ≤ 2 ^ (k + 1) := by
        simpa only [pow_one] using Nat.pow_le_pow_right
          (by norm_num : 0 < (2 : ℕ)) (by omega : 1 ≤ k + 1)
      exact htwo.trans (two_pow_le_scale hN0 (k + 1))
    unfold prefixPhaseGridSize
    calc
      8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ 16 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
      _ ≤ scale N0 (k + 1) ^ 16 := Nat.pow_le_pow_left hs2 16
  intro l hlower hl z hz
  rw [← signedPolynomial_derivativeCoefficient]
  apply norm_signedPolynomial_lt_of_not_gridPolynomialFailure
    (derivativeCoefficient a) ε (scalePrefix N0 k l)
      (prefixPhaseGridSize N0 k) hq8
      (derivative_phase_mesh_error_le a hsmall hN0 k l hkenv hl)
      (fun n hn ↦ by rcases hsigns n with h | h <;> simp [h])
  · intro hfail
    apply hknot
    unfold derivativeGridFailure
    simp only [Set.mem_iUnion]
    exact ⟨⟨l, by omega⟩, hfail⟩
  · exact hz

open Complex

/-- A finite complex polynomial, used to parameterize the restriction of a
signed block polynomial to a circular arc. -/
def finitePolynomial (c : ℕ → ℂ) (s : Finset ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ s, c n * z ^ n

/-- The angular derivative `z P'(z)` of `finitePolynomial`. -/
def finiteAngularDerivative (c : ℕ → ℂ) (s : Finset ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ s, (n : ℂ) * c n * z ^ n

lemma hasDerivAt_finitePolynomial_circlePath
    (c : ℕ → ℂ) (s : Finset ℕ) (w : ℂ) (t : ℝ) :
    HasDerivAt
      (fun x : ℝ ↦ finitePolynomial c s (w * Complex.exp ((x : ℂ) * I)))
      (I * finiteAngularDerivative c s (w * Complex.exp ((t : ℂ) * I))) t := by
  let e : ℂ → ℂ := fun x ↦ w * Complex.exp (x * I)
  have he : HasDerivAt e (e (t : ℂ) * I) (t : ℂ) := by
    simpa only [e, Function.comp_apply, id_eq, one_mul, mul_assoc] using
      ((Complex.hasDerivAt_exp ((t : ℂ) * I)).comp (t : ℂ)
        ((hasDerivAt_id (t : ℂ)).mul_const I) |>.const_mul w)
  have hterm : ∀ n : ℕ,
      HasDerivAt (fun x : ℂ ↦ c n * (e x) ^ n)
        (I * ((n : ℂ) * c n * (e (t : ℂ)) ^ n)) (t : ℂ) := by
    intro n
    cases n with
    | zero => simpa using hasDerivAt_const (x := (t : ℂ)) (c 0)
    | succ n =>
      apply ((he.pow (n + 1)).const_mul (c (n + 1))).congr_deriv
      simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, pow_succ]
      ring
  have hsum : HasDerivAt
      (fun x : ℂ ↦ finitePolynomial c s (e x))
      (I * finiteAngularDerivative c s (e (t : ℂ))) (t : ℂ) := by
    simpa only [finitePolynomial, finiteAngularDerivative, Finset.mul_sum] using
      HasDerivAt.fun_sum (u := s) (fun n _hn ↦ hterm n)
  simpa only [e] using hsum.comp_ofReal

/-- A uniform bound for the angular derivative on the unit circle gives a
Lipschitz bound for the polynomial in chordal distance. -/
lemma norm_finitePolynomial_sub_le_pi_div_two
    (c : ℕ → ℂ) (s : Finset ℕ) (B : ℝ) {z w : ℂ}
    (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    (hder : ∀ u : ℂ, ‖u‖ = 1 → ‖finiteAngularDerivative c s u‖ ≤ B) :
    ‖finitePolynomial c s z - finitePolynomial c s w‖ ≤
      (Real.pi / 2) * B * ‖z - w‖ := by
  let θ : ℝ := (z / w).arg
  let f : ℝ → ℂ := fun t ↦
    finitePolynomial c s (w * Complex.exp ((t : ℂ) * I))
  let f' : ℝ → ℂ := fun t ↦
    I * finiteAngularDerivative c s (w * Complex.exp ((t : ℂ) * I))
  have hB : 0 ≤ B :=
    (norm_nonneg (finiteAngularDerivative c s 1)).trans (hder 1 norm_one)
  have hpathNorm : ∀ t : ℝ,
      ‖w * Complex.exp ((t : ℂ) * I)‖ = 1 := by
    intro t
    rw [norm_mul, hw, one_mul, Complex.norm_exp]
    simp
  have hf : ∀ t ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt f (f' t) Set.univ t := by
    intro t _ht
    exact (hasDerivAt_finitePolynomial_circlePath c s w t).hasDerivWithinAt
  have hf' : ∀ t ∈ (Set.univ : Set ℝ), ‖f' t‖ ≤ B := by
    intro t _ht
    dsimp only [f']
    simpa only [norm_mul, norm_I, one_mul] using
      hder (w * Complex.exp ((t : ℂ) * I)) (hpathNorm t)
  have hmv : ‖f θ - f 0‖ ≤ B * ‖θ - 0‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hf hf' convex_univ
      (Set.mem_univ 0) (Set.mem_univ θ)
  have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (by rw [hw]; norm_num)
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; norm_num)
  have hquotNorm : ‖z / w‖ = 1 := by rw [norm_div, hz, hw, div_one]
  have hexp : Complex.exp ((θ : ℂ) * I) = z / w := by
    have hpolar := Complex.norm_mul_exp_arg_mul_I (z / w)
    simpa only [θ, hquotNorm, ofReal_one, one_mul] using hpolar
  have hend : w * Complex.exp ((θ : ℂ) * I) = z := by
    rw [hexp]
    field_simp
  have hzero : w * Complex.exp (((0 : ℝ) : ℂ) * I) = w := by simp
  have hangle : |θ| = InnerProductGeometry.angle z w := by
    rw [Complex.angle_eq_abs_arg hz0 hw0]
  calc
    ‖finitePolynomial c s z - finitePolynomial c s w‖ = ‖f θ - f 0‖ := by
      rw [show f θ = finitePolynomial c s z by simp only [f, hend],
        show f 0 = finitePolynomial c s w by simp only [f, hzero]]
    _ ≤ B * |θ| := by simpa only [Real.norm_eq_abs, sub_zero] using hmv
    _ = B * InnerProductGeometry.angle z w := by rw [hangle]
    _ ≤ B * ((Real.pi / 2) * ‖z - w‖) := by
      gcongr
      exact Complex.angle_le_mul_norm_sub hz hw
    _ = (Real.pi / 2) * B * ‖z - w‖ := by ring

lemma finitePolynomial_signed_eq
    (a ε : ℕ → ℝ) (s : Finset ℕ) (z : ℂ) :
    finitePolynomial (fun n ↦ ((ε n * a n : ℝ) : ℂ)) s z =
      signedPolynomial a ε s z := rfl

lemma finiteAngularDerivative_signed_eq
    (a ε : ℕ → ℝ) (s : Finset ℕ) (z : ℂ) :
    finiteAngularDerivative (fun n ↦ ((ε n * a n : ℝ) : ℂ)) s z =
      signedDerivativePolynomial a ε s z := by
  unfold finiteAngularDerivative signedDerivativePolynomial
  apply Finset.sum_congr rfl
  intro n hn
  push_cast
  ring

/-- A uniform angular-derivative bound transports the signed polynomial
between two unit-circle points with the sharp arc/chord constant `π / 2`. -/
lemma norm_signedPolynomial_sub_le_pi_div_two
    (a ε : ℕ → ℝ) (s : Finset ℕ) (B : ℝ) {z w : ℂ}
    (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    (hder : ∀ u : ℂ, ‖u‖ = 1 →
      ‖signedDerivativePolynomial a ε s u‖ ≤ B) :
    ‖signedPolynomial a ε s z - signedPolynomial a ε s w‖ ≤
      (Real.pi / 2) * B * ‖z - w‖ := by
  rw [← finitePolynomial_signed_eq a ε s z,
    ← finitePolynomial_signed_eq a ε s w]
  apply norm_finitePolynomial_sub_le_pi_div_two
      (fun n ↦ ((ε n * a n : ℝ) : ℂ)) s B hz hw
  intro u hu
  rw [finiteAngularDerivative_signed_eq]
  exact hder u hu

/-- The phase-transport loss from the derivative threshold across one branch
root thickening. -/
noncomputable def transportError (N0 k : ℕ) : ℝ :=
  (Real.pi / 2) * derivativeThreshold N0 k *
    Grid.branchRootRadius (scale N0 (k + 1)) (k + 1)

lemma transportError_eq {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) :
    transportError N0 k =
      2 * Real.pi ^ 2 * Real.log (scale N0 (k + 1) : ℝ) /
        (((k + 3 : ℕ) : ℝ) ^ 10) := by
  have hS : (scale N0 (k + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (scale_pos hN0 (k + 1)).ne'
  unfold transportError derivativeThreshold Grid.branchRootRadius
    Grid.branchRadiusDenom
  push_cast
  field_simp
  ring

lemma transportError_mul_succ_sq_tendsto_zero
    {N0 : ℕ} (hN0 : 0 < N0) :
    Tendsto (fun k : ℕ ↦
      transportError N0 k * (((k + 1 : ℕ) : ℝ) ^ 2))
      atTop (nhds 0) := by
  let x : ℕ → ℝ := fun k ↦ ((k + 1 : ℕ) : ℝ)
  let g : ℕ → ℝ := fun k ↦
    2 * Real.pi ^ 2 *
      (|Real.log (N0 : ℝ)| * (x k ^ 2 / x k ^ 10) +
        Real.log 2 * (x k ^ 5 / x k ^ 10))
  have hx : Tendsto x atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun k : ℕ ↦ x k ^ 2 / x k ^ 10)
      atTop (nhds 0) :=
    (tendsto_pow_div_pow_atTop_zero (𝕜 := ℝ) (by omega : 2 < 10)).comp hx
  have h5 : Tendsto (fun k : ℕ ↦ x k ^ 5 / x k ^ 10)
      atTop (nhds 0) :=
    (tendsto_pow_div_pow_atTop_zero (𝕜 := ℝ) (by omega : 5 < 10)).comp hx
  have hg : Tendsto g atTop (nhds 0) := by
    have hsum :=
      (h2.const_mul |Real.log (N0 : ℝ)|).add
        (h5.const_mul (Real.log 2))
    have hmul := hsum.const_mul (2 * Real.pi ^ 2)
    simpa only [g, mul_zero, add_zero] using hmul
  apply squeeze_zero' (g := g)
  · filter_upwards with k
    have hr : 0 ≤ Grid.branchRootRadius
        (scale N0 (k + 1)) (k + 1) := by
      unfold Grid.branchRootRadius Grid.branchRadiusDenom
      positivity
    unfold transportError
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (div_nonneg Real.pi_pos.le (by norm_num))
          (derivativeThreshold_pos hN0 k).le) hr)
      (sq_nonneg _)
  · filter_upwards with k
    let X : ℝ := x k
    let Y : ℝ := ((k + 3 : ℕ) : ℝ)
    have hX : 0 < X := by positivity
    have hXY : X ≤ Y := by
      dsimp only [X, Y, x]
      norm_num
    have hden : X ^ 10 ≤ Y ^ 10 := pow_le_pow_left₀ hX.le hXY 10
    have hlog2 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
    have hnum : 0 ≤
        |Real.log (N0 : ℝ)| * X ^ 2 + Real.log 2 * X ^ 5 := by positivity
    rw [transportError_eq hN0, log_scale_eq hN0]
    change
      (2 * Real.pi ^ 2 *
        (Real.log (N0 : ℝ) + X ^ 3 * Real.log 2) / Y ^ 10) * X ^ 2 ≤
        g k
    calc
      (2 * Real.pi ^ 2 *
          (Real.log (N0 : ℝ) + X ^ 3 * Real.log 2) / Y ^ 10) * X ^ 2 =
          2 * Real.pi ^ 2 *
            ((Real.log (N0 : ℝ) * X ^ 2 + Real.log 2 * X ^ 5) / Y ^ 10) := by
              ring
      _ ≤ 2 * Real.pi ^ 2 *
            ((|Real.log (N0 : ℝ)| * X ^ 2 + Real.log 2 * X ^ 5) / Y ^ 10) := by
          gcongr
          exact le_abs_self _
      _ ≤ 2 * Real.pi ^ 2 *
            ((|Real.log (N0 : ℝ)| * X ^ 2 + Real.log 2 * X ^ 5) / X ^ 10) := by
          gcongr
      _ = g k := by
          dsimp only [g, X, x]
          ring
  · exact hg

lemma eventually_transportError_le_inv_two_succ_sq
    {N0 : ℕ} (hN0 : 0 < N0) :
    ∀ᶠ k : ℕ in atTop,
      transportError N0 k ≤
        1 / (2 * (((k + 1 : ℕ) : ℝ) ^ 2)) := by
  have hsmall : ∀ᶠ k : ℕ in atTop,
      transportError N0 k * (((k + 1 : ℕ) : ℝ) ^ 2) < 1 / 2 :=
    (transportError_mul_succ_sq_tendsto_zero hN0).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hsmall] with k hk
  have hx : 0 < (((k + 1 : ℕ) : ℝ) ^ 2) := by positivity
  apply (le_div_iff₀ (mul_pos (by norm_num) hx)).2
  nlinarith

lemma inv_two_succ_sq_le_sqrt_coefficientEnvelope_div_two
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    (N0 k : ℕ) :
    1 / (2 * (((k + 1 : ℕ) : ℝ) ^ 2)) ≤
      Real.sqrt (coefficientEnvelope a N0 k) / 2 := by
  let X : ℝ := ((k + 1 : ℕ) : ℝ)
  have hX : 1 ≤ X := by
    dsimp only [X]
    exact_mod_cast (by omega : 1 ≤ k + 1)
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hsqrtXpos : 0 < Real.sqrt X := Real.sqrt_pos.2 hXpos
  have hX2 : X ≤ X ^ 2 := by nlinarith
  have hX4 : X ^ 2 ≤ X ^ 4 := by
    have := mul_self_le_mul_self ((by norm_num : (0 : ℝ) ≤ 1).trans hX) hX2
    nlinarith
  have hsqrt_le_X : Real.sqrt X ≤ X := by
    rw [Real.sqrt_le_iff]
    exact ⟨((by norm_num : (0 : ℝ) ≤ 1).trans hX), hX2⟩
  have hsqrt_le_X4 : Real.sqrt X ≤ X ^ 4 :=
    hsqrt_le_X.trans (hX2.trans hX4)
  have hinv : 1 / X ^ 4 ≤ (Real.sqrt X)⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le hsqrtXpos hsqrt_le_X4
  have hfloor : (Real.sqrt X)⁻¹ ≤ coefficientEnvelope a N0 k := by
    simpa only [X] using inv_sqrt_succ_le_coefficientEnvelope a N0 k
  have hsq : (1 / X ^ 2) ^ 2 ≤ coefficientEnvelope a N0 k := by
    calc
      (1 / X ^ 2) ^ 2 = 1 / X ^ 4 := by ring
      _ ≤ (Real.sqrt X)⁻¹ := hinv
      _ ≤ coefficientEnvelope a N0 k := hfloor
  have hroot : 1 / X ^ 2 ≤ Real.sqrt (coefficientEnvelope a N0 k) := by
    rw [Real.le_sqrt (by positivity) (coefficientEnvelope_nonneg a hsmall N0 k)]
    exact hsq
  change 1 / (2 * X ^ 2) ≤ Real.sqrt (coefficientEnvelope a N0 k) / 2
  calc
    1 / (2 * X ^ 2) = (1 / X ^ 2) / 2 := by ring
    _ ≤ Real.sqrt (coefficientEnvelope a N0 k) / 2 :=
      div_le_div_of_nonneg_right hroot (by norm_num)

lemma eventually_transportError_le_sqrt_coefficientEnvelope_div_two
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) :
    ∀ᶠ k : ℕ in atTop,
      transportError N0 k ≤
        Real.sqrt (coefficientEnvelope a N0 k) / 2 := by
  filter_upwards [eventually_transportError_le_inv_two_succ_sq hN0] with k hk
  exact hk.trans
    (inv_two_succ_sq_le_sqrt_coefficientEnvelope_div_two a hsmall N0 k)

end DerivativeEvents

namespace FailureMeasurability

lemma measurable_signedPolynomial
    (a : ℕ → ℝ) (s : Finset ℕ) (z : ℂ) :
    Measurable (fun ε : ℕ → ℝ ↦ signedPolynomial a ε s z) := by
  unfold signedPolynomial
  fun_prop

lemma measurableSet_gridPolynomialFailure
    (a : ℕ → ℝ) (s : Finset ℕ) (q : ℕ) [NeZero q] (t : ℝ) :
    MeasurableSet (gridPolynomialFailure a s q t) := by
  unfold gridPolynomialFailure
  rw [show ({ε : ℕ → ℝ | ∃ j : ZMod q,
      t ≤ ‖signedPolynomial a ε s (Grid.complexGridPoint q j)‖} :
      Set (ℕ → ℝ)) =
      ⋃ j : ZMod q,
        {ε | t ≤ ‖signedPolynomial a ε s (Grid.complexGridPoint q j)‖} by
    ext ε
    simp]
  apply MeasurableSet.iUnion
  intro j
  exact measurableSet_le measurable_const
    (measurable_signedPolynomial a s (Grid.complexGridPoint q j)).norm

lemma measurableSet_flatPrefixGridFailure
    (a : ℕ → ℝ) (N0 k q : ℕ) [NeZero q] (t : ℝ) :
    MeasurableSet (flatPrefixGridFailure a N0 k q t) := by
  unfold flatPrefixGridFailure
  apply MeasurableSet.iUnion
  intro r
  apply MeasurableSet.iUnion
  intro l
  exact measurableSet_gridPolynomialFailure _ _ _ _

lemma measurableSet_derivativeGridFailure
    (a : ℕ → ℝ) (N0 k : ℕ) [NeZero N0] :
    MeasurableSet (DerivativeEvents.derivativeGridFailure a N0 k) := by
  unfold DerivativeEvents.derivativeGridFailure
  apply MeasurableSet.iUnion
  intro l
  exact measurableSet_gridPolynomialFailure _ _ _ _

/-- The union of the ordinary-prefix and derivative-prefix exceptional events
at scale `k`. -/
noncomputable def combinedGridFailure
    (a : ℕ → ℝ) (N0 k : ℕ) [NeZero N0] : Set (ℕ → ℝ) :=
  flatPrefixGridFailure a N0 k (prefixPhaseGridSize N0 k)
      (prefixTolerance N0 k / 2) ∪
    DerivativeEvents.derivativeGridFailure a N0 k

lemma measurableSet_combinedGridFailure
    (a : ℕ → ℝ) (N0 k : ℕ) [NeZero N0] :
    MeasurableSet (combinedGridFailure a N0 k) := by
  exact (measurableSet_flatPrefixGridFailure _ _ _ _ _).union
    (measurableSet_derivativeGridFailure _ _ _)

/-- The sum of the two real-valued summable failure majorants. -/
noncomputable def combinedFailureBound (a : ℕ → ℝ) (N0 k : ℕ) : ℝ :=
  prefixFailureBound a N0 k + DerivativeEvents.derivativeFailureBound a N0 k

lemma prefixFailureBound_nonneg (a : ℕ → ℝ) (N0 k : ℕ) :
    0 ≤ prefixFailureBound a N0 k := by
  unfold prefixFailureBound
  split <;> positivity

lemma derivativeFailureBound_nonneg (a : ℕ → ℝ) (N0 k : ℕ) :
    0 ≤ DerivativeEvents.derivativeFailureBound a N0 k := by
  unfold DerivativeEvents.derivativeFailureBound
  split <;> positivity

lemma combinedFailureBound_nonneg (a : ℕ → ℝ) (N0 k : ℕ) :
    0 ≤ combinedFailureBound a N0 k :=
  add_nonneg (prefixFailureBound_nonneg a N0 k)
    (derivativeFailureBound_nonneg a N0 k)

lemma summable_combinedFailureBound
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) :
    Summable (combinedFailureBound a N0) := by
  exact (summable_prefixFailureBound a hsmall hN0).add
    (DerivativeEvents.summable_derivativeFailureBound a hsmall hN0)

lemma measureReal_combinedGridFailure_le
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} [NeZero N0] (hN0 : 0 < N0) (k : ℕ)
    (henv : coefficientEnvelope a N0 k ≤ 1)
    (hlog : (2080 : ℝ) ≤ Real.log (scale N0 (k + 1) : ℝ)) :
    rademacherProductMeasure.real (combinedGridFailure a N0 k) ≤
      combinedFailureBound a N0 k := by
  have hp := measureReal_flatPrefixGridFailure_envelope_le
    a hsmall hN0 k henv
  have hd := DerivativeEvents.measureReal_derivativeGridFailure_le
    a hsmall hN0 k henv hlog
  have hp' : rademacherProductMeasure.real
      (flatPrefixGridFailure a N0 k (prefixPhaseGridSize N0 k)
        (prefixTolerance N0 k / 2)) ≤ prefixFailureBound a N0 k := by
    simpa [prefixFailureBound, henv] using hp
  have hd' : rademacherProductMeasure.real
      (DerivativeEvents.derivativeGridFailure a N0 k) ≤
        DerivativeEvents.derivativeFailureBound a N0 k := by
    simpa [DerivativeEvents.derivativeFailureBound, henv, hlog] using hd
  calc
    rademacherProductMeasure.real (combinedGridFailure a N0 k)
      ≤ rademacherProductMeasure.real
          (flatPrefixGridFailure a N0 k (prefixPhaseGridSize N0 k)
            (prefixTolerance N0 k / 2)) +
        rademacherProductMeasure.real
          (DerivativeEvents.derivativeGridFailure a N0 k) := by
        exact measureReal_union_le _ _
    _ ≤ prefixFailureBound a N0 k +
        DerivativeEvents.derivativeFailureBound a N0 k := add_le_add hp' hd'
    _ = combinedFailureBound a N0 k := rfl

/-- ENNReal form of the combined failure estimate. -/
lemma measure_combinedGridFailure_le_ofReal
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} [NeZero N0] (hN0 : 0 < N0) (k : ℕ)
    (henv : coefficientEnvelope a N0 k ≤ 1)
    (hlog : (2080 : ℝ) ≤ Real.log (scale N0 (k + 1) : ℝ)) :
    rademacherProductMeasure (combinedGridFailure a N0 k) ≤
      ENNReal.ofReal (prefixFailureBound a N0 k +
        DerivativeEvents.derivativeFailureBound a N0 k) := by
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal
    (measureReal_combinedGridFailure_le a hsmall hN0 k henv hlog)

lemma combinedFailureBound_tendsto_zero
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) :
    Tendsto (combinedFailureBound a N0) atTop (𝓝 0) :=
  (summable_combinedFailureBound a hsmall hN0).tendsto_atTop_zero

lemma ofReal_combinedFailureBound_tendsto_zero
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) :
    Tendsto (fun k ↦ ENNReal.ofReal (combinedFailureBound a N0 k))
      atTop (𝓝 0) := by
  simpa only [ENNReal.ofReal_zero] using
    ENNReal.tendsto_ofReal (combinedFailureBound_tendsto_zero a hsmall hN0)

/-- The actual shifted infinite ENNReal tail of the two failure majorants
tends to zero. -/
lemma ofReal_combinedFailureTail_tendsto_zero
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) :
    Tendsto (fun k ↦ ∑' j : ℕ,
        ENNReal.ofReal (combinedFailureBound a N0 (j + k)))
      atTop (𝓝 0) := by
  exact ENNReal.tendsto_sum_nat_add
    (fun k ↦ ENNReal.ofReal (combinedFailureBound a N0 k))
    (summable_combinedFailureBound a hsmall hN0).tsum_ofReal_ne_top

end FailureMeasurability

/-! ## Ordered convergence and finite modifications -/

/-- Conditional `HasSum` on `ℕ` is precisely convergence of the usual
range partial sums. -/
theorem hasSum_conditional_iff_tendsto_sum_range
    {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (f : ℕ → E) (s : E) :
    HasSum f s (SummationFilter.conditional ℕ) ↔
      Tendsto (fun N ↦ ∑ n ∈ Finset.range N, f n) atTop (𝓝 s) := by
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
    Filter.tendsto_map'_iff]
  rfl

/-- Conditional `Summable` on `ℕ` is ordinary natural-order convergence. -/
theorem summable_conditional_iff_exists_tendsto_sum_range
    {E : Type*} [AddCommMonoid E] [TopologicalSpace E] (f : ℕ → E) :
    Summable f (SummationFilter.conditional ℕ) ↔
      ∃ s, Tendsto (fun N ↦ ∑ n ∈ Finset.range N, f n) atTop (𝓝 s) := by
  simp only [Summable, hasSum_conditional_iff_tendsto_sum_range]

/-- Summability along any supported summation filter is unchanged by a finite
modification of the summands. -/
theorem summable_congr_cofinite_filter
    {ι E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    {L : SummationFilter ι} [L.HasSupport] {f g : ι → E}
    (hfg : f =ᶠ[cofinite] g) : Summable f L ↔ Summable g L := by
  have hfin : {i | f i ≠ g i}.Finite := Filter.eventually_cofinite.mp hfg
  have hgf : g =ᶠ[cofinite] f := hfg.symm
  have hfin' : {i | g i ≠ f i}.Finite := Filter.eventually_cofinite.mp hgf
  have hsub_fg : Function.HasFiniteSupport (fun i ↦ g i - f i) := by
    refine hfin'.subset ?_
    intro i hi
    exact sub_ne_zero.mp hi
  have hsub_gf : Function.HasFiniteSupport (fun i ↦ f i - g i) := by
    refine hfin.subset ?_
    intro i hi
    exact sub_ne_zero.mp hi
  constructor
  · intro hf
    have hd : Summable (fun i ↦ g i - f i) L :=
      summable_of_hasFiniteSupport hsub_fg
    exact (hf.add hd).congr (fun i ↦ by abel)
  · intro hg
    have hd : Summable (fun i ↦ f i - g i) L :=
      summable_of_hasFiniteSupport hsub_gf
    exact (hg.add hd).congr (fun i ↦ by abel)

/-- Ordinary ordered series convergence on `ℕ` is unchanged by changing only
finitely many terms. -/
theorem summable_conditional_congr_atTop
    {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    {f g : ℕ → E} (hfg : f =ᶠ[atTop] g) :
    Summable f (.conditional ℕ) ↔ Summable g (.conditional ℕ) := by
  apply summable_congr_cofinite_filter
  simpa only [Nat.cofinite_eq_atTop] using hfg

/-- A finite modification of the coefficient sequence does not affect
convergence at a fixed sign sequence and point. -/
theorem seriesConvergesAt_iff_of_eventuallyEq
    {a b ε : ℕ → ℝ} {z : ℂ} (hab : a =ᶠ[atTop] b) :
    SeriesConvergesAt a ε z ↔ SeriesConvergesAt b ε z := by
  apply summable_conditional_congr_atTop
  filter_upwards [hab] with n hn
  simp [seriesTerm, hn]

/-- Consequently, the event that some unit-circle point is a convergence
point is unchanged by a finite modification of the coefficients. -/
theorem exists_unit_seriesConvergesAt_iff_of_eventuallyEq
    {a b ε : ℕ → ℝ} (hab : a =ᶠ[atTop] b) :
    (∃ z : ℂ, ‖z‖ = 1 ∧ SeriesConvergesAt a ε z) ↔
      ∃ z : ℂ, ‖z‖ = 1 ∧ SeriesConvergesAt b ε z := by
  constructor <;> rintro ⟨z, hz, hsum⟩
  · exact ⟨z, hz, (seriesConvergesAt_iff_of_eventuallyEq hab).mp hsum⟩
  · exact ⟨z, hz, (seriesConvergesAt_iff_of_eventuallyEq hab).mpr hsum⟩

/-- The corresponding almost-everywhere assertion transfers across a finite
coefficient modification. -/
theorem ae_exists_unit_seriesConvergesAt_iff_of_eventuallyEq
    {a b : ℕ → ℝ} (hab : a =ᶠ[atTop] b) (μ : Measure (ℕ → ℝ)) :
    (∀ᵐ ε ∂μ, ∃ z : ℂ, ‖z‖ = 1 ∧ SeriesConvergesAt a ε z) ↔
      ∀ᵐ ε ∂μ, ∃ z : ℂ, ‖z‖ = 1 ∧ SeriesConvergesAt b ε z := by
  constructor
  · intro h
    filter_upwards [h] with ε hε
    exact (exists_unit_seriesConvergesAt_iff_of_eventuallyEq hab).mp hε
  · intro h
    filter_upwards [h] with ε hε
    exact (exists_unit_seriesConvergesAt_iff_of_eventuallyEq hab).mpr hε

/-! ## Second-moment branching and survival -/

section Branching

open Set

/-- A relative second-moment estimate immediately gives a relative variance estimate. -/
lemma variance_le_of_secondMoment_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} (hY : MemLp Y 2 μ) {δ : ℝ}
    (hsecond : μ[Y ^ 2] ≤ (1 + δ) * μ[Y] ^ 2) :
    Var[Y; μ] ≤ δ * μ[Y] ^ 2 := by
  rw [variance_eq_sub hY]
  linarith

/-- Chebyshev's inequality in the one-sided form used for a branching count. -/
lemma measure_lt_expectation_sub_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {Y : Ω → ℝ} (hY : MemLp Y 2 μ) {c v : ℝ} (hc : 0 < c)
    (hvar : Var[Y; μ] ≤ v) :
    μ {ω | Y ω < μ[Y] - c} ≤ ENNReal.ofReal (v / c ^ 2) := by
  calc
    μ {ω | Y ω < μ[Y] - c} ≤ μ {ω | c ≤ |Y ω - μ[Y]|} := by
      apply measure_mono
      intro ω hω
      simp only [mem_setOf_eq] at hω ⊢
      rw [abs_of_nonpos (by linarith)]
      linarith
    _ ≤ ENNReal.ofReal (Var[Y; μ] / c ^ 2) :=
      meas_ge_le_variance_div_sq hY hc
    _ ≤ ENNReal.ofReal (v / c ^ 2) := by
      apply ENNReal.ofReal_le_ofReal
      exact div_le_div_of_nonneg_right hvar (sq_nonneg c)

/-- If a count has variance at most `δ` times the square of its mean, then it is
at least half its mean except on a set of measure at most `4 * δ`. -/
lemma measure_lt_half_expectation_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} (hY : MemLp Y 2 μ) {δ : ℝ} (_hδ : 0 ≤ δ)
    (hmean : 0 < μ[Y]) (hvar : Var[Y; μ] ≤ δ * μ[Y] ^ 2) :
    μ {ω | Y ω < μ[Y] / 2} ≤ ENNReal.ofReal (4 * δ) := by
  have hc : 0 < μ[Y] / 2 := by positivity
  have h := measure_lt_expectation_sub_le μ hY hc hvar
  have hset : {ω | Y ω < μ[Y] - μ[Y] / 2} = {ω | Y ω < μ[Y] / 2} := by
    congr with ω
    ring_nf
  rw [hset] at h
  refine h.trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hm : μ[Y] ≠ 0 := ne_of_gt hmean
  field_simp
  nlinarith [sq_pos_of_pos hmean]

/-- The direct passage from the relative second-moment estimate to the
half-expectation failure estimate used at each generation. -/
lemma measure_lt_half_expectation_le_of_secondMoment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {Y : Ω → ℝ} (hY : MemLp Y 2 μ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hmean : 0 < μ[Y])
    (hsecond : μ[Y ^ 2] ≤ (1 + δ) * μ[Y] ^ 2) :
    μ {ω | Y ω < μ[Y] / 2} ≤ ENNReal.ofReal (4 * δ) :=
  measure_lt_half_expectation_le μ hY hδ hmean
    (variance_le_of_secondMoment_le μ hY hsecond)

/-- Countable union bound for failures from generation `K` onward. -/
lemma measure_exists_failure_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (failure : ℕ → Set Ω)
    (_hfailure : ∀ k, MeasurableSet (failure k)) (K : ℕ) :
    μ {ω | ∃ k ≥ K, ω ∈ failure k} ≤ ∑' j : ℕ, μ (failure (K + j)) := by
  have hset : {ω | ∃ k ≥ K, ω ∈ failure k} = ⋃ j : ℕ, failure (K + j) := by
    ext ω
    simp only [mem_setOf_eq, mem_iUnion]
    constructor
    · rintro ⟨k, hk, hω⟩
      exact ⟨k - K, by simpa [Nat.add_sub_of_le hk] using hω⟩
    · rintro ⟨j, hω⟩
      exact ⟨K + j, Nat.le_add_right K j, hω⟩
  rw [hset]
  exact measure_iUnion_le fun j ↦ failure (K + j)

/-- A summable generation-by-generation failure estimate gives a quantitative
survival bound for all later generations at once. -/
lemma measure_all_generations_good_ge {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (good : ℕ → Set Ω) (hgood : ∀ k, MeasurableSet (good k)) (K : ℕ) {η : ℝ≥0∞}
    (htail : (∑' j : ℕ, μ ((good (K + j))ᶜ)) ≤ η) :
    1 - η ≤ μ {ω | ∀ k ≥ K, ω ∈ good k} := by
  have hbad := measure_exists_failure_le μ (fun k ↦ (good k)ᶜ)
    (fun k ↦ (hgood k).compl) K
  have hcompl : {ω | ∃ k ≥ K, ω ∈ (good k)ᶜ} =
      ({ω | ∀ k ≥ K, ω ∈ good k})ᶜ := by
    ext ω
    simp
  rw [hcompl, measure_compl (by measurability) (measure_ne_top μ _)] at hbad
  rw [measure_univ] at hbad
  rw [tsub_le_iff_right] at hbad
  rw [tsub_le_iff_right]
  have htail' : (∑' j : ℕ, μ ((good (K + j))ᶜ)) +
      μ {ω | ∀ k ≥ K, ω ∈ good k} ≤ η + μ {ω | ∀ k ≥ K, ω ∈ good k} := by
    gcongr
  simpa [add_comm] using hbad.trans htail'

/-- If an event has probability at least `1 - 1/(n+1)` for every `n`, then it
has probability one. -/
lemma measure_eq_one_of_one_sub_inv_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {event : Set Ω} (_hevent : MeasurableSet event)
    (h : ∀ n : ℕ, 1 - (n + 1 : ℝ≥0∞)⁻¹ ≤ μ event) : μ event = 1 := by
  apply le_antisymm
  · simpa using measure_mono (μ := μ) (subset_univ event)
  · have hinv : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) atTop (nhds 0) :=
      ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
    have hlim : Tendsto (fun n : ℕ ↦ 1 - ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) atTop (nhds 1) := by
      have hraw := (ENNReal.tendsto_sub (Or.inl ENNReal.one_ne_top)).comp
        (tendsto_const_nhds.prodMk_nhds hinv)
      change Tendsto (fun n : ℕ ↦ 1 - ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) atTop
        (nhds (1 - 0)) at hraw
      simpa using hraw
    apply le_of_tendsto hlim
    filter_upwards [] with n
    simpa using h n

/-- The nested nonempty compact intersection step that extracts a limiting
phase from surviving generations. -/
lemma nonempty_iInter_of_nested_compact {X : Type*} [TopologicalSpace X]
    (K : ℕ → Set X) (hnested : ∀ n, K (n + 1) ⊆ K n)
    (hne : ∀ n, (K n).Nonempty) (hcompact : IsCompact (K 0))
    (hclosed : ∀ n, IsClosed (K n)) :
    (⋂ n, K n).Nonempty :=
  hcompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    K hnested hne hclosed

/-- A point in the nested compact intersection belongs to every generation. -/
lemma exists_mem_all_of_nested_compact {X : Type*} [TopologicalSpace X]
    (K : ℕ → Set X) (hnested : ∀ n, K (n + 1) ⊆ K n)
    (hne : ∀ n, (K n).Nonempty) (hcompact : IsCompact (K 0))
    (hclosed : ∀ n, IsClosed (K n)) :
    ∃ x, ∀ n, x ∈ K n := by
  simpa only [nonempty_iInter, mem_iInter] using
    nonempty_iInter_of_nested_compact K hnested hne hcompact hclosed

end Branching

namespace Anderson

open Set Real MeasureTheory
open scoped ENNReal Pointwise Topology

/-!
A finite-dimensional Anderson translation inequality, derived directly from
the finite-dimensional Prékopa--Leindler theorem already formalized for
Erdős 615.  The density is allowed to take the value `∞`; no normalization
or finiteness assumption is needed.
-/

theorem lintegral_indicator_linear_preimage_sub_le_centered
    {n m : ℕ}
    (p : (Fin n → ℝ) → ℝ≥0∞)
    (hp : Measurable p)
    (hp_even : ∀ x, p (-x) = p x)
    (hp_midpoint_logConcave : ∀ x y,
      p ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) ≥
        p x ^ (1 / 2 : ℝ) * p y ^ (1 / 2 : ℝ))
    (L : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (hL : Measurable L)
    (K : Set (Fin m → ℝ))
    (hK : MeasurableSet K)
    (hK_convex : Convex ℝ K)
    (hK_symmetric : ∀ z, -z ∈ K ↔ z ∈ K)
    (t : Fin m → ℝ) :
    (∫⁻ x, ({x | L x - t ∈ K} : Set (Fin n → ℝ)).indicator p x) ≤
      ∫⁻ x, ({x | L x ∈ K} : Set (Fin n → ℝ)).indicator p x := by
  let A : Set (Fin n → ℝ) := {x | L x - t ∈ K}
  let B : Set (Fin n → ℝ) := {x | L x + t ∈ K}
  let C : Set (Fin n → ℝ) := {x | L x ∈ K}
  have hA : MeasurableSet A := hK.preimage (hL.sub measurable_const)
  have hB : MeasurableSet B := hK.preimage (hL.add measurable_const)
  have hC : MeasurableSet C := hK.preimage hL
  have hB_neg_A : ∀ x, B.indicator p (-x) = A.indicator p x := by
    intro x
    have hmem : -x ∈ B ↔ x ∈ A := by
      change L (-x) + t ∈ K ↔ L x - t ∈ K
      rw [map_neg]
      have hs := hK_symmetric (L x - t)
      simpa only [Pi.neg_apply, Pi.sub_apply, Pi.add_apply, sub_eq_add_neg,
        neg_add_rev, neg_neg, add_comm] using hs
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.mpr hx), hp_even]
    · rw [Set.indicator_of_notMem hx,
        Set.indicator_of_notMem (fun h ↦ hx (hmem.mp h))]
  have hIntBA : (∫⁻ x, B.indicator p x) = ∫⁻ x, A.indicator p x := by
    have hneg :=
      (Measure.measurePreserving_neg (volume : Measure (Fin n → ℝ))).lintegral_comp
        (hp.indicator hB)
    rw [lintegral_congr hB_neg_A] at hneg
    exact hneg.symm
  have hPL := Erdos615.BrunnMinkowski.prekopa_leindler_fin
    (C.indicator p) (A.indicator p) (B.indicator p)
    (hp.indicator hC) (hp.indicator hA) (hp.indicator hB)
    (1 / 2 : ℝ) (1 / 2 : ℝ) (by positivity) (by positivity) (by norm_num) ?_
  · rw [hIntBA] at hPL
    have hsquare :
        (∫⁻ x, A.indicator p x) ^ (1 / 2 : ℝ) *
            (∫⁻ x, A.indicator p x) ^ (1 / 2 : ℝ) =
          ∫⁻ x, A.indicator p x := by
      calc
        _ = (∫⁻ x, A.indicator p x) ^ ((1 / 2 : ℝ) + (1 / 2 : ℝ)) :=
          (ENNReal.rpow_add_of_nonneg (1 / 2 : ℝ) (1 / 2 : ℝ)
            (by norm_num) (by norm_num)).symm
        _ = ∫⁻ x, A.indicator p x := by norm_num
    rw [hsquare] at hPL
    exact hPL
  · intro x y
    by_cases hx : x ∈ A
    · by_cases hy : y ∈ B
      · have hc : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ∈ C := by
          change L ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) ∈ K
          rw [map_add, map_smul, map_smul]
          change L x - t ∈ K at hx
          change L y + t ∈ K at hy
          have hk := hK_convex hx hy (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
            (by norm_num) (by norm_num) (by norm_num)
          convert hk using 1 <;> ext i <;> simp [sub_eq_add_neg] <;> ring
        rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy,
          Set.indicator_of_mem hc]
        exact hp_midpoint_logConcave x y
      · simp only [Set.indicator_of_notMem hy]
        simp
    · simp only [Set.indicator_of_notMem hx]
      simp

/-- Measure form of the preceding density inequality. -/
theorem withDensity_linear_preimage_sub_le_centered
    {n m : ℕ}
    (p : (Fin n → ℝ) → ℝ≥0∞)
    (hp : Measurable p)
    (hp_even : ∀ x, p (-x) = p x)
    (hp_midpoint_logConcave : ∀ x y,
      p ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) ≥
        p x ^ (1 / 2 : ℝ) * p y ^ (1 / 2 : ℝ))
    (L : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (hL : Measurable L)
    (K : Set (Fin m → ℝ))
    (hK : MeasurableSet K)
    (hK_convex : Convex ℝ K)
    (hK_symmetric : ∀ z, -z ∈ K ↔ z ∈ K)
    (t : Fin m → ℝ) :
    (volume.withDensity p) {x | L x - t ∈ K} ≤
      (volume.withDensity p) {x | L x ∈ K} := by
  have hA : MeasurableSet {x : Fin n → ℝ | L x - t ∈ K} :=
    hK.preimage (hL.sub measurable_const)
  have hC : MeasurableSet {x : Fin n → ℝ | L x ∈ K} := hK.preimage hL
  rw [withDensity_apply _ hA, withDensity_apply _ hC,
    ← lintegral_indicator hA, ← lintegral_indicator hC]
  exact lintegral_indicator_linear_preimage_sub_le_centered p hp hp_even
    hp_midpoint_logConcave L hL K hK hK_convex hK_symmetric t

open ProbabilityTheory

lemma gaussianPDF_zero_one_even (x : ℝ) :
    gaussianPDF 0 1 (-x) = gaussianPDF 0 1 x := by
  simp [gaussianPDF, gaussianPDFReal, neg_sq]

lemma gaussianPDF_zero_one_midpoint_logConcave (x y : ℝ) :
    gaussianPDF 0 1 ((x + y) / 2) ≥
      gaussianPDF 0 1 x ^ (1 / 2 : ℝ) *
        gaussianPDF 0 1 y ^ (1 / 2 : ℝ) := by
  apply (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) gaussianPDF_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) gaussianPDF_ne_top))
    gaussianPDF_ne_top).mp
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, toReal_gaussianPDF]
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity)]
  simp only [← Real.exp_mul]
  have hsqrt : 0 < √(2 * π) := Real.sqrt_pos.2 (mul_pos two_pos Real.pi_pos)
  rw [Real.inv_rpow hsqrt.le]
  have hpow : √(2 * π) ^ (1 / 2 : ℝ) * √(2 * π) ^ (1 / 2 : ℝ) = √(2 * π) := by
    rw [← Real.rpow_add hsqrt]
    norm_num
  have hinv : (√(2 * π) ^ (1 / 2 : ℝ))⁻¹ *
      (√(2 * π) ^ (1 / 2 : ℝ))⁻¹ = (√(2 * π))⁻¹ := by
    rw [← mul_inv, hpow]
  calc
    _ = ((√(2 * π) ^ (1 / 2 : ℝ))⁻¹ *
          (√(2 * π) ^ (1 / 2 : ℝ))⁻¹) *
        (rexp (-x ^ 2 / 2 * (1 / 2)) * rexp (-y ^ 2 / 2 * (1 / 2))) := by ac_rfl
    _ = (√(2 * π))⁻¹ *
        rexp (-x ^ 2 / 2 * (1 / 2) + -y ^ 2 / 2 * (1 / 2)) := by
      rw [hinv, Real.exp_add]
    _ ≤ (√(2 * π))⁻¹ * rexp (-((x + y) / 2) ^ 2 / 2) := by
      gcongr
      nlinarith [sq_nonneg (x - y)]

/-- Lebesgue density of `n` independent standard real Gaussians. -/
noncomputable def standardGaussianProductDensity (n : ℕ) (x : Fin n → ℝ) : ℝ≥0∞ :=
  ∏ i, gaussianPDF 0 1 (x i)

lemma measurable_standardGaussianProductDensity (n : ℕ) :
    Measurable (standardGaussianProductDensity n) := by
  unfold standardGaussianProductDensity
  exact Finset.measurable_fun_prod _ fun i _ ↦
    (measurable_gaussianPDF 0 1).comp (measurable_pi_apply i)

lemma standardGaussianProductDensity_even (n : ℕ) (x : Fin n → ℝ) :
    standardGaussianProductDensity n (-x) = standardGaussianProductDensity n x := by
  unfold standardGaussianProductDensity
  apply Finset.prod_congr rfl
  intro i _
  simpa using gaussianPDF_zero_one_even (x i)

lemma standardGaussianProductDensity_midpoint_logConcave
    (n : ℕ) (x y : Fin n → ℝ) :
    standardGaussianProductDensity n
        ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) ≥
      standardGaussianProductDensity n x ^ (1 / 2 : ℝ) *
        standardGaussianProductDensity n y ^ (1 / 2 : ℝ) := by
  unfold standardGaussianProductDensity
  calc
    (∏ i, gaussianPDF 0 1 (x i)) ^ (1 / 2 : ℝ) *
          (∏ i, gaussianPDF 0 1 (y i)) ^ (1 / 2 : ℝ)
        = (∏ i, gaussianPDF 0 1 (x i) ^ (1 / 2 : ℝ)) *
          ∏ i, gaussianPDF 0 1 (y i) ^ (1 / 2 : ℝ) := by
            rw [ENNReal.prod_rpow_of_nonneg (by norm_num),
              ENNReal.prod_rpow_of_nonneg (by norm_num)]
    _ = ∏ i, (gaussianPDF 0 1 (x i) ^ (1 / 2 : ℝ) *
          gaussianPDF 0 1 (y i) ^ (1 / 2 : ℝ)) := by
            rw [Finset.prod_mul_distrib]
    _ ≤ ∏ i, gaussianPDF 0 1
          (((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) i) := by
            apply Finset.prod_le_prod
            · intro i _
              exact bot_le
            · intro i _
              rw [show (((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) i) =
                  (x i + y i) / 2 by simp; ring]
              exact gaussianPDF_zero_one_midpoint_logConcave (x i) (y i)

/-- Tonelli for a finite product of one-coordinate nonnegative functions. -/
lemma lintegral_fin_product_volume_eq_prod : ∀ (n : ℕ)
    (f : Fin n → ℝ → ℝ≥0∞),
    (∀ i, Measurable (f i)) →
    (∫⁻ x : Fin n → ℝ, ∏ i, f i (x i)) = ∏ i, ∫⁻ y, f i y
  | 0, f, hf => by
      simp only [Finset.univ_eq_empty, Finset.prod_empty]
      rw [lintegral_const, volume_pi, Measure.pi_empty_univ, one_mul]
  | n + 1, f, hf => by
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0
      let g : ℝ × (Fin n → ℝ) → ℝ≥0∞ := fun z ↦
        f 0 z.1 * ∏ j, f (Fin.succ j) (z.2 j)
      have hg0 : Measurable (fun z : ℝ × (Fin n → ℝ) ↦ f 0 z.1) :=
        (hf 0).comp measurable_fst
      have hgtail : Measurable (fun z : ℝ × (Fin n → ℝ) ↦
          ∏ j, f (Fin.succ j) (z.2 j)) :=
        Finset.measurable_fun_prod _ fun j _ ↦
          (hf (Fin.succ j)).comp ((measurable_pi_apply j).comp measurable_snd)
      have hg : Measurable g := hg0.mul hgtail
      have he := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0
      calc
        (∫⁻ x : Fin (n + 1) → ℝ, ∏ i, f i (x i))
            = ∫⁻ x : Fin (n + 1) → ℝ, g (e x) := by
                apply lintegral_congr
                intro x
                simp [g, e, Fin.prod_univ_succ, Fin.tail]
        _ = ∫⁻ z : ℝ × (Fin n → ℝ), g z :=
          he.lintegral_comp_emb e.measurableEmbedding g
        _ = (∫⁻ y, f 0 y) *
              ∫⁻ x : Fin n → ℝ, ∏ j, f (Fin.succ j) (x j) := by
                exact lintegral_prod_mul (hf 0).aemeasurable
                  (Finset.measurable_fun_prod _ fun j _ ↦
                    (hf (Fin.succ j)).comp (measurable_pi_apply j)).aemeasurable
        _ = (∫⁻ y, f 0 y) * ∏ j, ∫⁻ y, f (Fin.succ j) y := by
              rw [lintegral_fin_product_volume_eq_prod n (fun j ↦ f (Fin.succ j))
                (fun j ↦ hf (Fin.succ j))]
        _ = ∏ i, ∫⁻ y, f i y := by rw [Fin.prod_univ_succ]

lemma indicator_pi_standardGaussianProductDensity
    {n : ℕ} (s : Fin n → Set ℝ) (x : Fin n → ℝ) :
    (Set.pi Set.univ s).indicator (standardGaussianProductDensity n) x =
      ∏ i, (s i).indicator (gaussianPDF 0 1) (x i) := by
  by_cases hx : x ∈ Set.pi Set.univ s
  · rw [Set.indicator_of_mem hx]
    unfold standardGaussianProductDensity
    apply Finset.prod_congr rfl
    intro i _
    rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
  · rw [Set.indicator_of_notMem hx]
    rw [Set.mem_pi] at hx
    simp only [Set.mem_univ, forall_const] at hx
    push Not at hx
    obtain ⟨i, hi⟩ := hx
    apply Eq.symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact Set.indicator_of_notMem hi _

/-- The preceding product density is exactly the standard finite product Gaussian law. -/
theorem gaussianProductMeasure_eq_withDensity (n : ℕ) :
    (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) =
      volume.withDensity (standardGaussianProductDensity n) := by
  apply Measure.pi_eq
  intro s hs
  have hpi : MeasurableSet (Set.pi Set.univ s) :=
    MeasurableSet.pi Set.countable_univ fun i _ ↦ hs i
  rw [withDensity_apply _ hpi, ← lintegral_indicator hpi]
  rw [lintegral_congr (indicator_pi_standardGaussianProductDensity s)]
  rw [lintegral_fin_product_volume_eq_prod n
    (fun i ↦ (s i).indicator (gaussianPDF 0 1))
    (fun i ↦ (measurable_gaussianPDF 0 1).indicator (hs i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [lintegral_indicator (hs i)]
  exact (gaussianReal_apply 0 (by norm_num : (1 : NNReal) ≠ 0) (s i)).symm

/-- Anderson's inequality for the standard finite product Gaussian density. -/
theorem standardGaussianProduct_withDensity_linear_preimage_sub_le_centered
    {n m : ℕ}
    (L : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (hL : Measurable L)
    (K : Set (Fin m → ℝ))
    (hK : MeasurableSet K)
    (hK_convex : Convex ℝ K)
    (hK_symmetric : ∀ z, -z ∈ K ↔ z ∈ K)
    (t : Fin m → ℝ) :
    (volume.withDensity (standardGaussianProductDensity n)) {x | L x - t ∈ K} ≤
      (volume.withDensity (standardGaussianProductDensity n)) {x | L x ∈ K} := by
  exact withDensity_linear_preimage_sub_le_centered
    (standardGaussianProductDensity n) (measurable_standardGaussianProductDensity n)
    (standardGaussianProductDensity_even n)
    (standardGaussianProductDensity_midpoint_logConcave n)
    L hL K hK hK_convex hK_symmetric t

/-- Anderson's inequality for the standard finite product Gaussian law. -/
theorem gaussianProductMeasure_linear_preimage_sub_le_centered
    {n m : ℕ}
    (L : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (hL : Measurable L)
    (K : Set (Fin m → ℝ))
    (hK : MeasurableSet K)
    (hK_convex : Convex ℝ K)
    (hK_symmetric : ∀ z, -z ∈ K ↔ z ∈ K)
    (t : Fin m → ℝ) :
    (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) {x | L x - t ∈ K} ≤
      (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) {x | L x ∈ K} := by
  rw [gaussianProductMeasure_eq_withDensity n]
  exact standardGaussianProduct_withDensity_linear_preimage_sub_le_centered
    L hL K hK hK_convex hK_symmetric t

/-- Convolution form of Anderson's inequality.  Adding any independent
finite standard-Gaussian linear image cannot increase the mass of a measurable
centrally symmetric convex set.  This formulation directly compares the
original complex Gaussian walk with its circularized version. -/
theorem gaussianProductMeasure_add_linear_preimage_le_centered
    {n p m : ℕ}
    (L : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (hL : Measurable L)
    (R : (Fin p → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (hR : Measurable R)
    (K : Set (Fin m → ℝ))
    (hK : MeasurableSet K)
    (hK_convex : Convex ℝ K)
    (hK_symmetric : ∀ z, -z ∈ K ↔ z ∈ K) :
    ((Measure.pi fun _ : Fin n ↦ gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin p ↦ gaussianReal 0 1))
        {q | L q.1 + R q.2 ∈ K} ≤
      (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) {x | L x ∈ K} := by
  let μ : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n ↦ gaussianReal 0 1
  let ν : Measure (Fin p → ℝ) := Measure.pi fun _ : Fin p ↦ gaussianReal 0 1
  let A : Set ((Fin n → ℝ) × (Fin p → ℝ)) := {q | L q.1 + R q.2 ∈ K}
  have hA : MeasurableSet A := hK.preimage
    ((hL.comp measurable_fst).add (hR.comp measurable_snd))
  rw [show (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) = μ from rfl,
    show (Measure.pi fun _ : Fin p ↦ gaussianReal 0 1) = ν from rfl,
    show {q | L q.1 + R q.2 ∈ K} = A from rfl,
    Measure.prod_apply_symm hA]
  calc
    (∫⁻ y, μ ((fun x => (x, y)) ⁻¹' A) ∂ν)
        ≤ ∫⁻ _y, μ {x | L x ∈ K} ∂ν := by
      apply lintegral_mono
      intro y
      dsimp only
      have hsec : ((fun x => (x, y)) ⁻¹' A) = {x | L x - (-R y) ∈ K} := by
        ext x
        simp only [A, Set.mem_preimage, Set.mem_ofPred_eq]
        abel_nf
      rw [hsec]
      exact gaussianProductMeasure_linear_preimage_sub_le_centered
        L hL K hK hK_convex hK_symmetric (-R y)
    _ = μ {x | L x ∈ K} := by simp [ν]

end Anderson


namespace LindebergC4

/-- The linear combination of a finite family of vectors with real coefficients. -/
noncomputable def linearCombination {n d : ℕ}
    (v : Fin n → Fin d → ℝ) (x : Fin n → ℝ) : Fin d → ℝ :=
  fun j ↦ ∑ i, x i * v i j

lemma measurable_linearCombination {n d : ℕ} (v : Fin n → Fin d → ℝ) :
    Measurable (linearCombination v) := by
  refine measurable_pi_lambda _ fun j ↦ ?_
  exact Finset.measurable_sum Finset.univ fun i _ ↦
    (measurable_pi_apply i).mul measurable_const

/-- Hypotheses on a bounded test function needed for finite-dimensional
Lindeberg replacement.  `lineTest i a` controls the fourth derivative of
the restriction of `F` to the affine line through `a` in direction `v i`.
The number `M i` is allowed to depend on the direction. -/
structure IsBoundedC4OnLines {n d : ℕ} (F : (Fin d → ℝ) → ℝ)
    (v : Fin n → Fin d → ℝ) (M : Fin n → ℝ) : Prop where
  measurable : Measurable F
  bounded : ∃ B : ℝ, ∀ x, |F x| ≤ B
  lineTest : ∀ i a,
    Erdos88.Invariance.IsBoundedC4Test (fun z : ℝ ↦ F (a + z • v i)) (M i)

lemma IsBoundedC4OnLines.integrable_comp {n d : ℕ}
    {F : (Fin d → ℝ) → ℝ} {v : Fin n → Fin d → ℝ}
    {M : Fin n → ℝ} (hF : IsBoundedC4OnLines F v M)
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega) [IsFiniteMeasure P]
    (f : Omega → Fin d → ℝ) (hf : Measurable f) :
    Integrable (fun w ↦ F (f w)) P := by
  obtain ⟨B, hB⟩ := hF.bounded
  refine Integrable.mono' (integrable_const B) ?_ ?_
  · exact (hF.measurable.comp hf).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun w ↦ hB _

lemma linearCombination_piFinSuccAbove {n d : ℕ}
    (v : Fin (n + 1) → Fin d → ℝ) (t : Fin (n + 1))
    (z : ℝ) (y : Fin n → ℝ) :
    linearCombination v
        ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) t).symm (z, y)) =
      linearCombination (fun j ↦ v (t.succAbove j)) y + z • v t := by
  funext k
  rw [linearCombination, Fin.sum_univ_succAbove (fun i ↦
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) t).symm (z, y)) i *
      v i k) t]
  simp [linearCombination, add_comm]

/-- One coordinate of a vector-valued finite sum can be replaced by a
standard Gaussian at cost `M t / 6`. -/
theorem hybrid_step_linearCombination {n d : ℕ}
    (F : (Fin d → ℝ) → ℝ) (v : Fin (n + 1) → Fin d → ℝ)
    (M : Fin (n + 1) → ℝ) (hF : IsBoundedC4OnLines F v M)
    (t : Fin (n + 1)) :
    |∫ x, F (linearCombination v x) ∂Erdos88.Invariance.hybridMeasure (n + 1) t.val -
        ∫ x, F (linearCombination v x)
          ∂Erdos88.Invariance.hybridMeasure (n + 1) (t.val + 1)| ≤
      M t / 6 := by
  let split := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) t
  let base : (Fin n → ℝ) → (Fin d → ℝ) :=
    fun y ↦ linearCombination (fun j ↦ v (t.succAbove j)) y
  let g : ℝ × (Fin n → ℝ) → ℝ := fun p ↦ F (base p.2 + p.1 • v t)
  let Fr : (Fin n → ℝ) → ℝ := fun y ↦
    ∫ z, F (base y + z • v t) ∂Erdos88.Invariance.rademacherMeasure
  let Fg : (Fin n → ℝ) → ℝ := fun y ↦
    ∫ z, F (base y + z • v t) ∂Erdos88.Invariance.standardGaussian
  have hcomp : (fun x ↦ F (linearCombination v x)) = g ∘ split := by
    funext x
    change F (linearCombination v x) = F (base (split x).2 + (split x).1 • v t)
    congr 1
    calc
      linearCombination v x = linearCombination v (split.symm (split x)) := by
        rw [split.symm_apply_apply]
      _ = base (split x).2 + (split x).1 • v t := by
        exact linearCombination_piFinSuccAbove v t (split x).1 (split x).2
  have hfullRad : Integrable (fun x ↦ F (linearCombination v x))
      (Erdos88.Invariance.hybridMeasure (n + 1) t.val) :=
    hF.integrable_comp _ _ (measurable_linearCombination v)
  have hfullGauss : Integrable (fun x ↦ F (linearCombination v x))
      (Erdos88.Invariance.hybridMeasure (n + 1) (t.val + 1)) :=
    hF.integrable_comp _ _ (measurable_linearCombination v)
  have hpairRad : Integrable g
      (Erdos88.Invariance.rademacherMeasure.prod
        (Erdos88.Invariance.hybridMeasure n t.val)) := by
    apply ((Erdos88.Invariance.hybridMeasure_split_rademacher t).integrable_comp_emb
      split.measurableEmbedding).mp
    rw [← hcomp]
    exact hfullRad
  have hpairGauss : Integrable g
      (Erdos88.Invariance.standardGaussian.prod
        (Erdos88.Invariance.hybridMeasure n t.val)) := by
    apply ((Erdos88.Invariance.hybridMeasure_split_gaussian t).integrable_comp_emb
      split.measurableEmbedding).mp
    rw [← hcomp]
    exact hfullGauss
  have hrad : (∫ x, F (linearCombination v x)
      ∂Erdos88.Invariance.hybridMeasure (n + 1) t.val) =
      ∫ y, Fr y ∂Erdos88.Invariance.hybridMeasure n t.val := by
    calc
      (∫ x, F (linearCombination v x)
          ∂Erdos88.Invariance.hybridMeasure (n + 1) t.val) =
          ∫ x, g (split x) ∂Erdos88.Invariance.hybridMeasure (n + 1) t.val := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun x ↦ congrFun hcomp x
      _ = ∫ p, g p ∂Erdos88.Invariance.rademacherMeasure.prod
          (Erdos88.Invariance.hybridMeasure n t.val) :=
        (Erdos88.Invariance.hybridMeasure_split_rademacher t).integral_comp' g
      _ = ∫ y, Fr y ∂Erdos88.Invariance.hybridMeasure n t.val := by
        simpa [g, Fr] using integral_prod_symm g hpairRad
  have hgauss :
      (∫ x, F (linearCombination v x)
          ∂Erdos88.Invariance.hybridMeasure (n + 1) (t.val + 1)) =
        ∫ y, Fg y ∂Erdos88.Invariance.hybridMeasure n t.val := by
    calc
      (∫ x, F (linearCombination v x)
          ∂Erdos88.Invariance.hybridMeasure (n + 1) (t.val + 1)) =
          ∫ x, g (split x)
            ∂Erdos88.Invariance.hybridMeasure (n + 1) (t.val + 1) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun x ↦ congrFun hcomp x
      _ = ∫ p, g p ∂Erdos88.Invariance.standardGaussian.prod
          (Erdos88.Invariance.hybridMeasure n t.val) :=
        (Erdos88.Invariance.hybridMeasure_split_gaussian t).integral_comp' g
      _ = ∫ y, Fg y ∂Erdos88.Invariance.hybridMeasure n t.val := by
        simpa [g, Fg] using integral_prod_symm g hpairGauss
  have hFr : Integrable Fr (Erdos88.Invariance.hybridMeasure n t.val) := by
    simpa [g, Fr] using hpairRad.integral_prod_right
  have hFg : Integrable Fg (Erdos88.Invariance.hybridMeasure n t.val) := by
    simpa [g, Fg] using hpairGauss.integral_prod_right
  have hnonneg : 0 ≤ M t := (hF.lineTest t 0).fourth_nonneg
  rw [hrad, hgauss, ← integral_sub hFr hFg]
  calc
    |∫ y, Fr y - Fg y ∂Erdos88.Invariance.hybridMeasure n t.val| ≤
        ∫ y, |Fr y - Fg y| ∂Erdos88.Invariance.hybridMeasure n t.val :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _y, M t / 6 ∂Erdos88.Invariance.hybridMeasure n t.val := by
      apply integral_mono (hFr.sub hFg).abs (integrable_const _)
      intro y
      have hrep := Erdos88.Invariance.affine_rademacher_gaussian_replacement
        (hF.lineTest t (base y)) 0 1
      simpa [Fr, Fg] using hrep
    _ = M t / 6 := by simp

/-- Finite-dimensional C⁴ Lindeberg replacement for a bounded test of a
linear combination.  No differentiability of `F` away from the finitely many
increment directions is needed. -/
theorem linearCombination_rademacher_gaussian_replacement {n d : ℕ}
    (F : (Fin d → ℝ) → ℝ) (v : Fin n → Fin d → ℝ)
    (M : Fin n → ℝ) (hF : IsBoundedC4OnLines F v M) :
    |∫ x, F (linearCombination v x)
          ∂Erdos88.Invariance.rademacherProductMeasure n -
        ∫ x, F (linearCombination v x)
          ∂Erdos88.Invariance.gaussianProductMeasure n| ≤
      ∑ i, M i / 6 := by
  cases n with
  | zero =>
      rw [← Erdos88.Invariance.hybridMeasure_zero 0,
        ← Erdos88.Invariance.hybridMeasure_eq_gaussian 0 0 (by norm_num)]
      simp
  | succ n =>
      rw [← Erdos88.Invariance.hybridMeasure_zero (n + 1),
        ← Erdos88.Invariance.hybridMeasure_eq_gaussian (n + 1) (n + 1) le_rfl]
      let G : ℕ → ℝ := fun t ↦
        ∫ x, F (linearCombination v x) ∂Erdos88.Invariance.hybridMeasure (n + 1) t
      calc
        |G 0 - G (n + 1)| ≤
            ∑ i : Fin (n + 1), |G i.val - G (i.val + 1)| :=
          Erdos88.Invariance.telescoping_abs G (n + 1)
        _ ≤ ∑ i : Fin (n + 1), M i / 6 := by
          apply Finset.sum_le_sum
          intro i _
          simpa [G] using hybrid_step_linearCombination F v M hF i

/-- The same estimate with the fourth-derivative budget presented as a
function of the increment vector itself. -/
theorem linearCombination_rademacher_gaussian_replacement_direction {n d : ℕ}
    (F : (Fin d → ℝ) → ℝ) (v : Fin n → Fin d → ℝ)
    (M : (Fin d → ℝ) → ℝ)
    (hF : IsBoundedC4OnLines F v (fun i ↦ M (v i))) :
    |∫ x, F (linearCombination v x)
          ∂Erdos88.Invariance.rademacherProductMeasure n -
        ∫ x, F (linearCombination v x)
          ∂Erdos88.Invariance.gaussianProductMeasure n| ≤
      ∑ i, M (v i) / 6 :=
  linearCombination_rademacher_gaussian_replacement F v (fun i ↦ M (v i)) hF

end LindebergC4

/-! ## Smooth C⁴ cutoffs for Lindeberg test functions -/

namespace SmoothCutoffC4

noncomputable section

open scoped BigOperators Topology
open Set Function

/-! A fixed radial `C^∞` cutoff on the real normed space `ℂ`. -/

/-- The Mathlib bump with inner radius `1` and outer radius `2`. -/
def cutoffBump : ContDiffBump (0 : ℂ) :=
  ⟨1, 2, by norm_num, by norm_num⟩

/-- A smooth cutoff which is one on the closed unit disk and zero off the open disk of radius 2. -/
def cutoff (z : ℂ) : ℝ := cutoffBump z

theorem cutoff_contDiff : ContDiff ℝ (⊤ : ℕ∞) cutoff := cutoffBump.contDiff

theorem cutoff_nonneg (z : ℂ) : 0 ≤ cutoff z := cutoffBump.nonneg

theorem cutoff_le_one (z : ℂ) : cutoff z ≤ 1 := cutoffBump.le_one

theorem norm_cutoff_le_one (z : ℂ) : ‖cutoff z‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg z)]
  exact cutoff_le_one z

theorem cutoff_eq_one {z : ℂ} (hz : ‖z‖ ≤ 1) : cutoff z = 1 := by
  apply cutoffBump.one_of_mem_closedBall
  simpa [Metric.mem_closedBall, cutoffBump] using hz

theorem cutoff_eq_zero {z : ℂ} (hz : 2 ≤ ‖z‖) : cutoff z = 0 := by
  apply cutoffBump.zero_of_le_dist
  simpa [Complex.dist_eq, cutoffBump] using hz

/-! Uniform bounds for the first four real Fréchet derivatives of the fixed cutoff. -/

theorem exists_cutoff_deriv_bound (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ z : ℂ, ‖iteratedFDeriv ℝ m cutoff z‖ ≤ C := by
  have hcont : Continuous (iteratedFDeriv ℝ m cutoff) :=
    cutoff_contDiff.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)
  have hsupp : HasCompactSupport (iteratedFDeriv ℝ m cutoff) :=
    cutoffBump.hasCompactSupport.iteratedFDeriv m
  obtain ⟨C, hC⟩ := hsupp.exists_bound_of_continuous hcont
  refine ⟨max 1 C, le_max_left _ _, fun z ↦ (hC z).trans (le_max_right _ _)⟩

/-- A nonnegative, at-least-one global bound for the `m`-th derivative of `cutoff`. -/
def cutoffDerivBound (m : ℕ) : ℝ := Classical.choose (exists_cutoff_deriv_bound m)

theorem one_le_cutoffDerivBound (m : ℕ) : 1 ≤ cutoffDerivBound m :=
  (Classical.choose_spec (exists_cutoff_deriv_bound m)).1

theorem norm_iteratedFDeriv_cutoff_le (m : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ m cutoff z‖ ≤ cutoffDerivBound m :=
  (Classical.choose_spec (exists_cutoff_deriv_bound m)).2 z

/-- A single constant controlling every derivative of order at most four. -/
def cutoffC4 : ℝ := ∑ m ∈ Finset.range 5, cutoffDerivBound m

theorem one_le_cutoffC4 : 1 ≤ cutoffC4 := by
  calc
    1 ≤ cutoffDerivBound 0 := one_le_cutoffDerivBound 0
    _ ≤ ∑ m ∈ Finset.range 5, cutoffDerivBound m := by
      apply Finset.single_le_sum
      · intro i hi
        exact le_trans (by norm_num) (one_le_cutoffDerivBound i)
      · simp

theorem cutoffC4_nonneg : 0 ≤ cutoffC4 := zero_le_one.trans one_le_cutoffC4

theorem norm_iteratedFDeriv_cutoff_le_C4 {m : ℕ} (hm : m ≤ 4) (z : ℂ) :
    ‖iteratedFDeriv ℝ m cutoff z‖ ≤ cutoffC4 := by
  exact (norm_iteratedFDeriv_cutoff_le m z).trans <| by
    apply Finset.single_le_sum
    · intro i hi
      exact le_trans (by norm_num) (one_le_cutoffDerivBound i)
    · simpa using Nat.lt_succ_iff.mpr hm

/-! Scaling by arbitrary continuous real-linear maps. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cutoff_comp_contDiff (L : E →L[ℝ] ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (cutoff ∘ L) :=
  cutoff_contDiff.comp_continuousLinearMap

/-- Exact scaling estimate.  The order-zero case uses `|cutoff| ≤ 1`; consequently finite
products do not pay one cutoff constant for every undifferentiated factor. -/
theorem norm_iteratedFDeriv_cutoff_comp_le (L : E →L[ℝ] ℂ) (x : E) {m : ℕ} (hm : m ≤ 4) :
    ‖iteratedFDeriv ℝ m (cutoff ∘ L) x‖ ≤ (cutoffC4 * ‖L‖) ^ m := by
  cases m with
  | zero =>
      simpa [norm_iteratedFDeriv_zero, Function.comp_apply] using norm_cutoff_le_one (L x)
  | succ m =>
      rw [L.iteratedFDeriv_comp_right cutoff_contDiff x (WithTop.coe_le_coe.mpr le_top)]
      calc
        ‖(iteratedFDeriv ℝ (m + 1) cutoff (L x)).compContinuousLinearMap (fun _ ↦ L)‖
            ≤ ‖iteratedFDeriv ℝ (m + 1) cutoff (L x)‖ *
                ∏ _ : Fin (m + 1), ‖L‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
        _ = ‖iteratedFDeriv ℝ (m + 1) cutoff (L x)‖ * ‖L‖ ^ (m + 1) := by simp
        _ ≤ cutoffC4 * ‖L‖ ^ (m + 1) := by
          gcongr
          exact norm_iteratedFDeriv_cutoff_le_C4 hm (L x)
        _ ≤ cutoffC4 ^ (m + 1) * ‖L‖ ^ (m + 1) := by
          gcongr
          exact le_self_pow₀ one_le_cutoffC4 (Nat.succ_ne_zero m)
        _ = (cutoffC4 * ‖L‖) ^ (m + 1) := by rw [mul_pow]

/-! A multinomial `C^4` bound for products of linearly composed cutoffs. -/

variable {ι : Type*} [DecidableEq ι]

/-- The finite product of cutoff tests associated to real-linear forms. -/
def cutoffProduct (u : Finset ι) (L : ι → E →L[ℝ] ℂ) (x : E) : ℝ :=
  ∏ j ∈ u, cutoff (L j x)

theorem cutoffProduct_contDiff (u : Finset ι) (L : ι → E →L[ℝ] ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (cutoffProduct u L) := by
  unfold cutoffProduct
  exact contDiff_prod fun i _ ↦ cutoff_comp_contDiff (L i)

private theorem map_prod_eq_prod_pow_count {u : Finset ι} {n : ℕ}
    (p : u.sym n) (a : ι → ℝ) :
    (p.1.val.map a).prod = ∏ j ∈ u, a j ^ p.1.val.count j := by
  rw [Finset.prod_multiset_map_count]
  apply Finset.prod_subset
  · intro j hj
    exact Finset.mem_sym_iff.mp p.2 j (Multiset.mem_toFinset.mp hj)
  · intro j hju hjp
    rw [Multiset.count_eq_zero.mpr]
    · simp
    · simpa only [Multiset.mem_toFinset] using hjp

/-- The clean product bound used in fourth-order Lindeberg replacement.  It is polynomial in
the number and norms of the linear tests: for every `n ≤ 4`,
`‖D^n ∏ H(L_j x)‖ ≤ (C₄ ∑ ‖L_j‖)^n`. -/
theorem norm_iteratedFDeriv_cutoffProduct_le (u : Finset ι) (L : ι → E →L[ℝ] ℂ)
    (x : E) {n : ℕ} (hn : n ≤ 4) :
    ‖iteratedFDeriv ℝ n (cutoffProduct u L) x‖ ≤
      (cutoffC4 * ∑ j ∈ u, ‖L j‖) ^ n := by
  unfold cutoffProduct
  calc
    ‖iteratedFDeriv ℝ n (fun x ↦ ∏ j ∈ u, cutoff (L j x)) x‖
        ≤ ∑ p ∈ u.sym n, (p : Multiset ι).countPerms *
            ∏ j ∈ u,
              ‖iteratedFDeriv ℝ ((p : Multiset ι).count j) (cutoff ∘ L j) x‖ := by
      simpa [cutoffProduct, Function.comp_apply] using
        (norm_iteratedFDeriv_prod_le
          (u := u) (f := fun j ↦ cutoff ∘ L j)
          (fun j _ ↦ cutoff_comp_contDiff (L j)) (x := x) (n := n)
          (WithTop.coe_le_coe.mpr le_top))
    _ ≤ ∑ p ∈ u.sym n, (p : Multiset ι).countPerms *
            ∏ j ∈ u, (cutoffC4 * ‖L j‖) ^ ((p : Multiset ι).count j) := by
      gcongr with p hp j hj
      apply norm_iteratedFDeriv_cutoff_comp_le
      exact (Multiset.count_le_card j p.1).trans (by simpa using hn)
    _ = (∑ j ∈ u, cutoffC4 * ‖L j‖) ^ n := by
      rw [Finset.sum_pow]
      apply Finset.sum_congr rfl
      intro p hp
      congr 1
      exact (map_prod_eq_prod_pow_count ⟨p, hp⟩ (fun j ↦ cutoffC4 * ‖L j‖)).symm
    _ = (cutoffC4 * ∑ j ∈ u, ‖L j‖) ^ n := by
      congr 1
      rw [Finset.mul_sum]

/-! Concrete linear forms for the endpoint and all prefix constraints. -/

variable [Fintype ι]

/-- Sum a finite collection of coordinates, as a continuous real-linear map. -/
def coordinateSum (s : Finset ι) : (ι → ℂ) →L[ℝ] ℂ :=
  ∑ j ∈ s, ContinuousLinearMap.proj j

@[simp] theorem coordinateSum_apply (s : Finset ι) (w : ι → ℂ) :
    coordinateSum s w = ∑ j ∈ s, w j := by
  simp [coordinateSum]

theorem norm_coordinateSum_le (s : Finset ι) : ‖coordinateSum s‖ ≤ s.card := by
  unfold coordinateSum
  calc
    ‖∑ j ∈ s, ContinuousLinearMap.proj j‖
        ≤ ∑ j ∈ s, ‖ContinuousLinearMap.proj j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ s, (1 : ℝ) := by
      gcongr with j hj
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro w
      simpa using norm_le_pi_norm w j
    _ = s.card := by simp

/-- The total-sum test followed by multiplication by a real scale. -/
def scaledCoordinateSum (c : ℝ) (s : Finset ι) : (ι → ℂ) →L[ℝ] ℂ :=
  c • coordinateSum s

@[simp] theorem scaledCoordinateSum_apply (c : ℝ) (s : Finset ι) (w : ι → ℂ) :
    scaledCoordinateSum c s w = c • ∑ j ∈ s, w j := by
  simp [scaledCoordinateSum]

theorem norm_scaledCoordinateSum_le (c : ℝ) (s : Finset ι) :
    ‖scaledCoordinateSum c s‖ ≤ |c| * s.card := by
  calc
    ‖scaledCoordinateSum c s‖ ≤ ‖c‖ * ‖coordinateSum s‖ := by
      exact norm_smul_le c (coordinateSum s)
    _ = |c| * ‖coordinateSum s‖ := by rw [Real.norm_eq_abs]
    _ ≤ |c| * s.card := mul_le_mul_of_nonneg_left (norm_coordinateSum_le s) (abs_nonneg c)

/-- Index the endpoint constraint by `none` and the `j`-th prefix constraint by `some j`. -/
def endpointPrefixForms (l : ℕ) (endpointScale prefixScale : ℝ) :
    Option (Fin l) → (Fin l → ℂ) →L[ℝ] ℂ
  | none => scaledCoordinateSum endpointScale Finset.univ
  | some j => scaledCoordinateSum prefixScale (Finset.Iic j)

/-- The exact cutoff used for a total-sum constraint and all successive prefix constraints. -/
def endpointPrefixCutoff (l : ℕ) (endpointScale prefixScale : ℝ) (w : Fin l → ℂ) : ℝ :=
  cutoffProduct Finset.univ (endpointPrefixForms l endpointScale prefixScale) w

theorem endpointPrefixCutoff_eq (l : ℕ) (endpointScale prefixScale : ℝ) (w : Fin l → ℂ) :
    endpointPrefixCutoff l endpointScale prefixScale w =
      cutoff (endpointScale • ∑ r : Fin l, w r) *
        ∏ j : Fin l, cutoff (prefixScale • ∑ r ∈ Finset.Iic j, w r) := by
  simp [endpointPrefixCutoff, cutoffProduct, endpointPrefixForms]

theorem endpointPrefixCutoff_nonneg (l : ℕ) (endpointScale prefixScale : ℝ)
    (w : Fin l → ℂ) :
    0 ≤ endpointPrefixCutoff l endpointScale prefixScale w := by
  unfold endpointPrefixCutoff cutoffProduct
  exact Finset.prod_nonneg fun _ _ ↦ cutoff_nonneg _

theorem endpointPrefixCutoff_le_one (l : ℕ) (endpointScale prefixScale : ℝ)
    (w : Fin l → ℂ) :
    endpointPrefixCutoff l endpointScale prefixScale w ≤ 1 := by
  unfold endpointPrefixCutoff cutoffProduct
  exact Finset.prod_le_one (fun _ _ ↦ cutoff_nonneg _) (fun _ _ ↦ cutoff_le_one _)

theorem endpointPrefixCutoff_eq_one_of_bounds (l : ℕ)
    (endpointScale prefixScale : ℝ) (w : Fin l → ℂ)
    (hend : ‖endpointScale • ∑ r : Fin l, w r‖ ≤ 1)
    (hprefix : ∀ j : Fin l,
      ‖prefixScale • ∑ r ∈ Finset.Iic j, w r‖ ≤ 1) :
    endpointPrefixCutoff l endpointScale prefixScale w = 1 := by
  rw [endpointPrefixCutoff_eq, cutoff_eq_one hend]
  simp only [one_mul]
  apply Finset.prod_eq_one
  intro j hj
  exact cutoff_eq_one (hprefix j)

theorem endpoint_norm_lt_two_of_endpointPrefixCutoff_ne_zero (l : ℕ)
    (endpointScale prefixScale : ℝ) (w : Fin l → ℂ)
    (hG : endpointPrefixCutoff l endpointScale prefixScale w ≠ 0) :
    ‖endpointScale • ∑ r : Fin l, w r‖ < 2 := by
  by_contra h
  have hz := cutoff_eq_zero (z := endpointScale • ∑ r : Fin l, w r) (not_lt.mp h)
  apply hG
  rw [endpointPrefixCutoff_eq, hz, zero_mul]

theorem prefix_norm_lt_two_of_endpointPrefixCutoff_ne_zero (l : ℕ)
    (endpointScale prefixScale : ℝ) (w : Fin l → ℂ)
    (hG : endpointPrefixCutoff l endpointScale prefixScale w ≠ 0)
    (j : Fin l) :
    ‖prefixScale • ∑ r ∈ Finset.Iic j, w r‖ < 2 := by
  by_contra h
  have hz := cutoff_eq_zero
    (z := prefixScale • ∑ r ∈ Finset.Iic j, w r) (not_lt.mp h)
  apply hG
  rw [endpointPrefixCutoff_eq]
  apply mul_eq_zero_of_right
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  exact hz

theorem endpointPrefixCutoff_contDiff (l : ℕ) (endpointScale prefixScale : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (endpointPrefixCutoff l endpointScale prefixScale) :=
  cutoffProduct_contDiff _ _

/-- A deliberately coarse but polynomial operator budget for the endpoint and all prefix forms. -/
theorem sum_norm_endpointPrefixForms_le (l : ℕ) (endpointScale prefixScale : ℝ) :
    (∑ j : Option (Fin l), ‖endpointPrefixForms l endpointScale prefixScale j‖) ≤
      ((l + 1 : ℕ) : ℝ) * (|endpointScale| + |prefixScale|) * l := by
  apply (Finset.sum_le_sum fun j _ ↦ ?_).trans_eq
      (show (∑ _j : Option (Fin l),
          (|endpointScale| + |prefixScale|) * (l : ℝ)) =
          ((l + 1 : ℕ) : ℝ) * (|endpointScale| + |prefixScale|) * l by
        simp [mul_assoc])
  cases j with
  | none =>
      apply (norm_scaledCoordinateSum_le endpointScale Finset.univ).trans
      have hcard : ((Finset.univ : Finset (Fin l)).card : ℝ) = l := by simp
      rw [hcard]
      gcongr
      exact le_add_of_nonneg_right (abs_nonneg prefixScale)
  | some j =>
      apply (norm_scaledCoordinateSum_le prefixScale (Finset.Iic j)).trans
      calc
        |prefixScale| * ((Finset.Iic j).card : ℝ)
            ≤ |prefixScale| * l := by
          gcongr
          have hcard : (Finset.Iic j).card ≤ l := by
            simpa using Finset.card_le_card (Finset.subset_univ (Finset.Iic j))
          exact_mod_cast hcard
        _ ≤ (|endpointScale| + |prefixScale|) * l := by
          gcongr
          exact le_add_of_nonneg_left (abs_nonneg endpointScale)

/-- Direct `C^4` bound for the concrete total/prefix test.  Taking
`endpointScale = k^2` and `prefixScale = δ^{-1/2}` gives the test function used in the proof. -/
theorem norm_iteratedFDeriv_endpointPrefixCutoff_le (l : ℕ)
    (endpointScale prefixScale : ℝ) (w : Fin l → ℂ) {n : ℕ} (hn : n ≤ 4) :
    ‖iteratedFDeriv ℝ n (endpointPrefixCutoff l endpointScale prefixScale) w‖ ≤
      (cutoffC4 *
        ∑ j : Option (Fin l), ‖endpointPrefixForms l endpointScale prefixScale j‖) ^ n := by
  unfold endpointPrefixCutoff
  exact norm_iteratedFDeriv_cutoffProduct_le
    (u := (Finset.univ : Finset (Option (Fin l))))
    (endpointPrefixForms l endpointScale prefixScale) w hn

/-- Fully explicit polynomial form of the preceding derivative estimate. -/
theorem norm_iteratedFDeriv_endpointPrefixCutoff_le_explicit (l : ℕ)
    (endpointScale prefixScale : ℝ) (w : Fin l → ℂ) {n : ℕ} (hn : n ≤ 4) :
    ‖iteratedFDeriv ℝ n (endpointPrefixCutoff l endpointScale prefixScale) w‖ ≤
      (cutoffC4 * (((l + 1 : ℕ) : ℝ) *
        (|endpointScale| + |prefixScale|) * l)) ^ n := by
  apply (norm_iteratedFDeriv_endpointPrefixCutoff_le l endpointScale prefixScale w hn).trans
  apply pow_le_pow_left₀
  · exact mul_nonneg cutoffC4_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
  · exact mul_le_mul_of_nonneg_left
      (sum_norm_endpointPrefixForms_le l endpointScale prefixScale) cutoffC4_nonneg

end

end SmoothCutoffC4


/-! ## Large-sieve correlation count -/

namespace CorrelationCount

noncomputable section

open BoundedGaps.Maynard

/-- The two real coordinates of a complex number. -/
def coord : Bool → ℂ → ℝ
  | false, z => z.re
  | true, z => z.im

@[simp] lemma coord_false (z : ℂ) : coord false z = z.re := rfl
@[simp] lemma coord_true (z : ℂ) : coord true z = z.im := rfl

lemma abs_coord_le_norm (q : Bool) (z : ℂ) : |coord q z| ≤ ‖z‖ := by
  cases q <;> simp only [coord_false, coord_true]
  · exact Complex.abs_re_le_norm z
  · exact Complex.abs_im_le_norm z

lemma coord_sum {J : Type*} (q : Bool) (s : Finset J) (f : J → ℂ) :
    coord q (∑ j ∈ s, f j) = ∑ j ∈ s, coord q (f j) := by
  cases q <;> simp [coord]

lemma coord_real_mul (q : Bool) (r : ℝ) (z : ℂ) :
    coord q ((r : ℂ) * z) = r * coord q z := by
  cases q <;> simp [coord]

/-- The value `a_n e(n x)` whose two coordinates form the covariance vectors. -/
def phaseValue (a : ℕ → ℂ) (n : ℕ) (x : UnitAddCircle) : ℂ :=
  a n * unitAddCircleAddChar (n • x)

/-- A real-coordinate covariance on the interval `m < n ≤ m + M`. -/
def blockCovariance (a : ℕ → ℂ) (m M : ℕ) (x y : UnitAddCircle)
    (p q : Bool) : ℝ :=
  ∑ n ∈ Finset.Ioc m (m + M), coord p (phaseValue a n x) * coord q (phaseValue a n y)

/-- The Fourier sum which simultaneously controls either output coordinate `q`. -/
def covarianceFourier (a : ℕ → ℂ) (m M : ℕ) (x y : UnitAddCircle)
    (p : Bool) : ℂ :=
  ∑ n ∈ Finset.Ioc m (m + M),
    ((coord p (phaseValue a n x) : ℝ) : ℂ) * a n * unitAddCircleAddChar (n • y)

lemma coord_covarianceFourier (a : ℕ → ℂ) (m M : ℕ) (x y : UnitAddCircle)
    (p q : Bool) :
    coord q (covarianceFourier a m M x y p) = blockCovariance a m M x y p q := by
  rw [covarianceFourier, blockCovariance, coord_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [mul_assoc, coord_real_mul]
  rfl

lemma abs_blockCovariance_le_norm_fourier
    (a : ℕ → ℂ) (m M : ℕ) (x y : UnitAddCircle) (p q : Bool) :
    |blockCovariance a m M x y p q| ≤ ‖covarianceFourier a m M x y p‖ := by
  rw [← coord_covarianceFourier]
  exact abs_coord_le_norm q _

lemma norm_coord_phaseValue_le (a : ℕ → ℂ) (n : ℕ) (x : UnitAddCircle) (p : Bool) :
    ‖((coord p (phaseValue a n x) : ℝ) : ℂ)‖ ≤ ‖a n‖ := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  refine (abs_coord_le_norm p _).trans ?_
  rw [phaseValue, norm_mul, show ‖unitAddCircleAddChar (n • x)‖ = 1 by
    change ‖((AddCircle.toCircle (n • x) : Circle) : ℂ)‖ = 1
    exact Circle.norm_coe _]
  simp

lemma covarianceCoefficient_sq_le
    (a : ℕ → ℂ) (N n : ℕ) (x : UnitAddCircle) (p : Bool)
    (ha : ‖a n‖ ^ 2 ≤ (N : ℝ)⁻¹) :
    ‖((coord p (phaseValue a n x) : ℝ) : ℂ) * a n‖ ^ 2 ≤ ((N : ℝ)⁻¹) ^ 2 := by
  have hc := norm_coord_phaseValue_le a n x p
  have hc2 : ‖((coord p (phaseValue a n x) : ℝ) : ℂ)‖ ^ 2 ≤ ‖a n‖ ^ 2 := by
    nlinarith [norm_nonneg ((coord p (phaseValue a n x) : ℝ) : ℂ), norm_nonneg (a n)]
  rw [norm_mul]
  calc
    (‖((coord p (phaseValue a n x) : ℝ) : ℂ)‖ * ‖a n‖) ^ 2 =
        ‖((coord p (phaseValue a n x) : ℝ) : ℂ)‖ ^ 2 * ‖a n‖ ^ 2 := by ring
    _ ≤ ‖a n‖ ^ 2 * (N : ℝ)⁻¹ :=
      mul_le_mul hc2 ha (sq_nonneg _) (sq_nonneg _)
    _ ≤ (N : ℝ)⁻¹ * (N : ℝ)⁻¹ := by
      exact mul_le_mul_of_nonneg_right ha (inv_nonneg.mpr (Nat.cast_nonneg N))
    _ = ((N : ℝ)⁻¹) ^ 2 := by ring

lemma covarianceCoefficient_energy_le
    (a : ℕ → ℂ) (m M N : ℕ) (x : UnitAddCircle) (p : Bool)
    (ha : ∀ n ∈ Finset.Ioc m (m + M), ‖a n‖ ^ 2 ≤ (N : ℝ)⁻¹) :
    (∑ n ∈ Finset.Ioc m (m + M),
      ‖((coord p (phaseValue a n x) : ℝ) : ℂ) * a n‖ ^ 2) ≤
      (M : ℝ) * ((N : ℝ)⁻¹) ^ 2 := by
  calc
    (∑ n ∈ Finset.Ioc m (m + M),
      ‖((coord p (phaseValue a n x) : ℝ) : ℂ) * a n‖ ^ 2) ≤
        ∑ n ∈ Finset.Ioc m (m + M), ((N : ℝ)⁻¹) ^ 2 := by
          exact Finset.sum_le_sum fun n hn => covarianceCoefficient_sq_le a N n x p (ha n hn)
    _ = (M : ℝ) * ((N : ℝ)⁻¹) ^ 2 := by
      rw [Finset.sum_const, Nat.card_Ioc]
      simp

lemma sum_norm_sq_covarianceFourier_le
    {I : Type*} [Fintype I] [DecidableEq I]
    (a : ℕ → ℂ) (m M N : ℕ) (x : UnitAddCircle) (y : I → UnitAddCircle)
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ r s, r ≠ s → δ ≤ dist (y r) (y s))
    (ha : ∀ n ∈ Finset.Ioc m (m + M), ‖a n‖ ^ 2 ≤ (N : ℝ)⁻¹) (p : Bool) :
    (∑ r, ‖covarianceFourier a m M x (y r) p‖ ^ 2) ≤
      ((M : ℝ) + δ⁻¹) * (M : ℝ) * ((N : ℝ)⁻¹) ^ 2 := by
  have hls := sum_norm_sq_unitAddCircleAddChar_Ioc_le y hδ hsep m M
    (fun n => ((coord p (phaseValue a n x) : ℝ) : ℂ) * a n)
  calc
    (∑ r, ‖covarianceFourier a m M x (y r) p‖ ^ 2) ≤
        ((M : ℝ) + δ⁻¹) *
          ∑ n ∈ Finset.Ioc m (m + M),
            ‖((coord p (phaseValue a n x) : ℝ) : ℂ) * a n‖ ^ 2 := by
              simpa only [covarianceFourier] using hls
    _ ≤ ((M : ℝ) + δ⁻¹) * ((M : ℝ) * ((N : ℝ)⁻¹) ^ 2) := by
      gcongr
      exact covarianceCoefficient_energy_le a m M N x p ha
    _ = ((M : ℝ) + δ⁻¹) * (M : ℝ) * ((N : ℝ)⁻¹) ^ 2 := by ring

/-- At least one of the four real/imaginary coordinate covariances is large. -/
def IsCorrelated (a : ℕ → ℂ) (m M : ℕ) (x y : UnitAddCircle) (ρ : ℝ) : Prop :=
  ∃ p q : Bool, ρ ≤ |blockCovariance a m M x y p q|

/-- Indices in a finite phase family which are correlated with the fixed phase `x`. -/
noncomputable def correlatedIndices {I : Type*} [Fintype I]
    (a : ℕ → ℂ) (m M : ℕ) (x : UnitAddCircle) (y : I → UnitAddCircle) (ρ : ℝ) :
    Finset I := by
  classical
  exact Finset.univ.filter fun r => IsCorrelated a m M x (y r) ρ

@[simp] lemma mem_correlatedIndices {I : Type*} [Fintype I] [DecidableEq I]
    (a : ℕ → ℂ) (m M : ℕ) (x : UnitAddCircle) (y : I → UnitAddCircle) (ρ : ℝ)
    (r : I) :
    r ∈ correlatedIndices a m M x y ρ ↔ IsCorrelated a m M x (y r) ρ := by
  classical
  simp [correlatedIndices]

lemma rho_sq_le_sum_fourier_of_correlated
    (a : ℕ → ℂ) (m M : ℕ) (x y : UnitAddCircle) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : IsCorrelated a m M x y ρ) :
    ρ ^ 2 ≤ ∑ p : Bool, ∑ _q : Bool, ‖covarianceFourier a m M x y p‖ ^ 2 := by
  rcases h with ⟨p, q, hpq⟩
  have hn := hpq.trans (abs_blockCovariance_le_norm_fourier a m M x y p q)
  have hs : ρ ^ 2 ≤ ‖covarianceFourier a m M x y p‖ ^ 2 := by
    nlinarith [norm_nonneg (covarianceFourier a m M x y p)]
  cases p <;> simp only [Fintype.sum_bool]
  · nlinarith [sq_nonneg ‖covarianceFourier a m M x y true‖,
      sq_nonneg ‖covarianceFourier a m M x y false‖]
  · nlinarith [sq_nonneg ‖covarianceFourier a m M x y true‖,
      sq_nonneg ‖covarianceFourier a m M x y false‖]

lemma sum_four_coordinate_fourier_le
    {I : Type*} [Fintype I] [DecidableEq I]
    (a : ℕ → ℂ) (m M N : ℕ) (x : UnitAddCircle) (y : I → UnitAddCircle)
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ r s, r ≠ s → δ ≤ dist (y r) (y s))
    (ha : ∀ n ∈ Finset.Ioc m (m + M), ‖a n‖ ^ 2 ≤ (N : ℝ)⁻¹) :
    (∑ r, ∑ p : Bool, ∑ _q : Bool, ‖covarianceFourier a m M x (y r) p‖ ^ 2) ≤
      4 * (((M : ℝ) + δ⁻¹) * (M : ℝ) * ((N : ℝ)⁻¹) ^ 2) := by
  have ht := sum_norm_sq_covarianceFourier_le a m M N x y hδ hsep ha true
  have hf := sum_norm_sq_covarianceFourier_le a m M N x y hδ hsep ha false
  simp only [Fintype.sum_bool, Finset.sum_add_distrib]
  linarith

/-- Application-specific large-sieve count.  This bounds the union of all four choices of
real/imaginary coordinate in the two covariance vectors.  The harmless constant `4` is kept
explicit. -/
theorem card_correlatedIndices_le
    {I : Type*} [Fintype I] [DecidableEq I]
    (a : ℕ → ℂ) (m M N : ℕ) (_hMN : M ≤ N)
    (x : UnitAddCircle) (y : I → UnitAddCircle)
    {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ)
    (hsep : ∀ r s, r ≠ s → δ ≤ dist (y r) (y s))
    (ha : ∀ n ∈ Finset.Ioc m (m + M), ‖a n‖ ^ 2 ≤ (N : ℝ)⁻¹) :
    ((correlatedIndices a m M x y ρ).card : ℝ) ≤
      4 * (ρ⁻¹) ^ 2 * ((M : ℝ) + δ⁻¹) * (M : ℝ) * ((N : ℝ)⁻¹) ^ 2 := by
  let B : ℝ := ((M : ℝ) + δ⁻¹) * (M : ℝ) * ((N : ℝ)⁻¹) ^ 2
  have hpoint : ∀ r ∈ correlatedIndices a m M x y ρ,
      ρ ^ 2 ≤ ∑ p : Bool, ∑ _q : Bool, ‖covarianceFourier a m M x (y r) p‖ ^ 2 := by
    intro r hr
    exact rho_sq_le_sum_fourier_of_correlated a m M x (y r) hρ.le
      ((mem_correlatedIndices a m M x y ρ r).mp hr)
  have hscaled :
      ρ ^ 2 * ((correlatedIndices a m M x y ρ).card : ℝ) ≤ 4 * B := by
    calc
      ρ ^ 2 * ((correlatedIndices a m M x y ρ).card : ℝ) =
          ∑ r ∈ correlatedIndices a m M x y ρ, ρ ^ 2 := by simp [mul_comm]
      _ ≤ ∑ r ∈ correlatedIndices a m M x y ρ,
          ∑ p : Bool, ∑ _q : Bool, ‖covarianceFourier a m M x (y r) p‖ ^ 2 := by
            exact Finset.sum_le_sum hpoint
      _ ≤ ∑ r, ∑ p : Bool, ∑ _q : Bool,
          ‖covarianceFourier a m M x (y r) p‖ ^ 2 := by
            apply Finset.sum_le_univ_sum_of_nonneg
            intro r
            positivity
      _ ≤ 4 * B := by
        exact sum_four_coordinate_fourier_le a m M N x y hδ hsep ha
  have hρne : ρ ≠ 0 := ne_of_gt hρ
  calc
    ((correlatedIndices a m M x y ρ).card : ℝ) =
        (ρ⁻¹) ^ 2 * (ρ ^ 2 * ((correlatedIndices a m M x y ρ).card : ℝ)) := by
          field_simp
    _ ≤ (ρ⁻¹) ^ 2 * (4 * B) :=
      mul_le_mul_of_nonneg_left hscaled (sq_nonneg _)
    _ = 4 * (ρ⁻¹) ^ 2 * ((M : ℝ) + δ⁻¹) * (M : ℝ) * ((N : ℝ)⁻¹) ^ 2 := by
      dsimp only [B]
      ring

end

end CorrelationCount


namespace CutoffLindebergBridge

open SmoothCutoffC4

noncomputable section

/-- The fourth-derivative budget of the endpoint/prefix cutoff in a complex
increment direction. -/
def endpointPrefixDirectionBudget (l : ℕ) (endpointScale prefixScale : ℝ)
    (v : Fin l → ℂ) : ℝ :=
  (cutoffC4 *
    (∑ j : Option (Fin l),
      ‖endpointPrefixForms l endpointScale prefixScale j‖) * ‖v‖) ^ 4

theorem endpointPrefixDirectionBudget_nonneg (l : ℕ)
    (endpointScale prefixScale : ℝ) (v : Fin l → ℂ) :
    0 ≤ endpointPrefixDirectionBudget l endpointScale prefixScale v := by
  exact Even.pow_nonneg (by norm_num) _

/-- Restricting the endpoint/prefix cutoff to an affine line gives exactly
the one-dimensional bounded `C⁴` test required by Lindeberg replacement. -/
theorem endpointPrefixCutoff_isBoundedC4Test_line (l : ℕ)
    (endpointScale prefixScale : ℝ) (a v : Fin l → ℂ) :
    Erdos88.Invariance.IsBoundedC4Test
      (fun z : ℝ ↦ endpointPrefixCutoff l endpointScale prefixScale (a + z • v))
      (endpointPrefixDirectionBudget l endpointScale prefixScale v) := by
  let F : (Fin l → ℂ) → ℝ :=
    endpointPrefixCutoff l endpointScale prefixScale
  let L : ℝ →L[ℝ] (Fin l → ℂ) :=
    ContinuousLinearMap.toSpanSingleton ℝ v
  have hF : ContDiff ℝ (⊤ : ℕ∞) F :=
    endpointPrefixCutoff_contDiff l endpointScale prefixScale
  have hshift : ContDiff ℝ (⊤ : ℕ∞) (fun w ↦ F (a + w)) := by
    exact hF.comp (contDiff_const.add contDiff_id)
  refine {
    contDiff := ?_
    bounded := ⟨1, ?_⟩
    fourth_nonneg := endpointPrefixDirectionBudget_nonneg l endpointScale prefixScale v
    fourth_bound := ?_
  }
  · have hline : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ ↦ a + z • v) := by
      fun_prop
    exact (hF.comp hline).of_le (WithTop.coe_le_coe.mpr le_top)
  · intro z
    rw [abs_of_nonneg (endpointPrefixCutoff_nonneg l endpointScale prefixScale _)]
    exact endpointPrefixCutoff_le_one l endpointScale prefixScale _
  · intro z
    rw [← Real.norm_eq_abs, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hfun :
        (fun z : ℝ ↦ F (a + z • v)) = (fun w ↦ F (a + w)) ∘ L := by
      funext t
      rfl
    rw [hfun, L.iteratedFDeriv_comp_right hshift z (WithTop.coe_le_coe.mpr le_top)]
    calc
      ‖(iteratedFDeriv ℝ 4 (fun w ↦ F (a + w)) (L z)).compContinuousLinearMap
          (fun _ ↦ L)‖ ≤
          ‖iteratedFDeriv ℝ 4 (fun w ↦ F (a + w)) (L z)‖ *
            ∏ _ : Fin 4, ‖L‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ = ‖iteratedFDeriv ℝ 4 F (a + L z)‖ * ‖v‖ ^ 4 := by
        rw [iteratedFDeriv_comp_add_left]
        simp [L]
      _ ≤
          (cutoffC4 *
            (∑ j : Option (Fin l),
              ‖endpointPrefixForms l endpointScale prefixScale j‖)) ^ 4 * ‖v‖ ^ 4 := by
        gcongr
        exact norm_iteratedFDeriv_endpointPrefixCutoff_le
          l endpointScale prefixScale (a + L z) (by norm_num)
      _ = endpointPrefixDirectionBudget l endpointScale prefixScale v := by
        rw [endpointPrefixDirectionBudget, mul_pow]
        ring

namespace NormedLindeberg

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [MeasurableAdd₂ E]

/-- A finite linear combination in an arbitrary real normed space. -/
def linearCombination {n : ℕ} (v : Fin n → E) (x : Fin n → ℝ) : E :=
  ∑ i, x i • v i

theorem measurable_linearCombination {n : ℕ} (v : Fin n → E) :
    Measurable (linearCombination v) := by
  unfold linearCombination
  apply Finset.measurable_sum
  intro i hi
  by_cases hvi : v i = 0
  · simp [hvi]
  · exact (_root_.measurable_smul_const hvi).2 (measurable_pi_apply i)

/-- Boundedness and uniform fourth-derivative control along each of a finite
family of directions in a real normed space. -/
structure IsBoundedC4OnLines {n : ℕ} (F : E → ℝ) (v : Fin n → E)
    (M : Fin n → ℝ) : Prop where
  measurable : Measurable F
  bounded : ∃ B : ℝ, ∀ x, |F x| ≤ B
  lineTest : ∀ i a,
    Erdos88.Invariance.IsBoundedC4Test (fun z : ℝ ↦ F (a + z • v i)) (M i)

theorem IsBoundedC4OnLines.integrable_comp {n : ℕ}
    {F : E → ℝ} {v : Fin n → E} {M : Fin n → ℝ}
    (hF : IsBoundedC4OnLines F v M)
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega) [IsFiniteMeasure P]
    (f : Omega → E) (hf : Measurable f) : Integrable (fun w ↦ F (f w)) P := by
  obtain ⟨B, hB⟩ := hF.bounded
  refine Integrable.mono' (integrable_const B) ?_ ?_
  · exact (hF.measurable.comp hf).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun w ↦ hB _

theorem linearCombination_piFinSuccAbove {n : ℕ}
    (v : Fin (n + 1) → E) (t : Fin (n + 1)) (z : ℝ) (y : Fin n → ℝ) :
    linearCombination v
        ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) t).symm (z, y)) =
      linearCombination (fun j ↦ v (t.succAbove j)) y + z • v t := by
  rw [linearCombination, Fin.sum_univ_succAbove (fun i ↦
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) t).symm (z, y)) i •
      v i) t]
  simp [linearCombination, add_comm]

/-- One step of normed-space Lindeberg replacement. -/
theorem hybrid_step {n : ℕ} (F : E → ℝ) (v : Fin (n + 1) → E)
    (M : Fin (n + 1) → ℝ) (hF : IsBoundedC4OnLines F v M)
    (t : Fin (n + 1)) :
    |∫ x, F (linearCombination v x)
          ∂Erdos88.Invariance.hybridMeasure (n + 1) t.val -
        ∫ x, F (linearCombination v x)
          ∂Erdos88.Invariance.hybridMeasure (n + 1) (t.val + 1)| ≤
      M t / 6 := by
  let split := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) t
  let base : (Fin n → ℝ) → E :=
    fun y ↦ linearCombination (fun j ↦ v (t.succAbove j)) y
  let g : ℝ × (Fin n → ℝ) → ℝ := fun p ↦ F (base p.2 + p.1 • v t)
  let Fr : (Fin n → ℝ) → ℝ := fun y ↦
    ∫ z, F (base y + z • v t) ∂Erdos88.Invariance.rademacherMeasure
  let Fg : (Fin n → ℝ) → ℝ := fun y ↦
    ∫ z, F (base y + z • v t) ∂Erdos88.Invariance.standardGaussian
  have hcomp : (fun x ↦ F (linearCombination v x)) = g ∘ split := by
    funext x
    change F (linearCombination v x) = F (base (split x).2 + (split x).1 • v t)
    congr 1
    calc
      linearCombination v x = linearCombination v (split.symm (split x)) := by
        rw [split.symm_apply_apply]
      _ = base (split x).2 + (split x).1 • v t := by
        exact linearCombination_piFinSuccAbove v t (split x).1 (split x).2
  have hfullRad : Integrable (fun x ↦ F (linearCombination v x))
      (Erdos88.Invariance.hybridMeasure (n + 1) t.val) :=
    hF.integrable_comp _ _ (measurable_linearCombination v)
  have hfullGauss : Integrable (fun x ↦ F (linearCombination v x))
      (Erdos88.Invariance.hybridMeasure (n + 1) (t.val + 1)) :=
    hF.integrable_comp _ _ (measurable_linearCombination v)
  have hpairRad : Integrable g
      (Erdos88.Invariance.rademacherMeasure.prod
        (Erdos88.Invariance.hybridMeasure n t.val)) := by
    apply ((Erdos88.Invariance.hybridMeasure_split_rademacher t).integrable_comp_emb
      split.measurableEmbedding).mp
    rw [← hcomp]
    exact hfullRad
  have hpairGauss : Integrable g
      (Erdos88.Invariance.standardGaussian.prod
        (Erdos88.Invariance.hybridMeasure n t.val)) := by
    apply ((Erdos88.Invariance.hybridMeasure_split_gaussian t).integrable_comp_emb
      split.measurableEmbedding).mp
    rw [← hcomp]
    exact hfullGauss
  have hrad :
      (∫ x, F (linearCombination v x)
          ∂Erdos88.Invariance.hybridMeasure (n + 1) t.val) =
        ∫ y, Fr y ∂Erdos88.Invariance.hybridMeasure n t.val := by
    calc
      (∫ x, F (linearCombination v x)
          ∂Erdos88.Invariance.hybridMeasure (n + 1) t.val) =
          ∫ x, g (split x) ∂Erdos88.Invariance.hybridMeasure (n + 1) t.val := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun x ↦ congrFun hcomp x
      _ = ∫ p, g p ∂Erdos88.Invariance.rademacherMeasure.prod
          (Erdos88.Invariance.hybridMeasure n t.val) :=
        (Erdos88.Invariance.hybridMeasure_split_rademacher t).integral_comp' g
      _ = ∫ y, Fr y ∂Erdos88.Invariance.hybridMeasure n t.val := by
        simpa [g, Fr] using integral_prod_symm g hpairRad
  have hgauss :
      (∫ x, F (linearCombination v x)
          ∂Erdos88.Invariance.hybridMeasure (n + 1) (t.val + 1)) =
        ∫ y, Fg y ∂Erdos88.Invariance.hybridMeasure n t.val := by
    calc
      (∫ x, F (linearCombination v x)
          ∂Erdos88.Invariance.hybridMeasure (n + 1) (t.val + 1)) =
          ∫ x, g (split x)
            ∂Erdos88.Invariance.hybridMeasure (n + 1) (t.val + 1) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun x ↦ congrFun hcomp x
      _ = ∫ p, g p ∂Erdos88.Invariance.standardGaussian.prod
          (Erdos88.Invariance.hybridMeasure n t.val) :=
        (Erdos88.Invariance.hybridMeasure_split_gaussian t).integral_comp' g
      _ = ∫ y, Fg y ∂Erdos88.Invariance.hybridMeasure n t.val := by
        simpa [g, Fg] using integral_prod_symm g hpairGauss
  have hFr : Integrable Fr (Erdos88.Invariance.hybridMeasure n t.val) := by
    simpa [g, Fr] using hpairRad.integral_prod_right
  have hFg : Integrable Fg (Erdos88.Invariance.hybridMeasure n t.val) := by
    simpa [g, Fg] using hpairGauss.integral_prod_right
  rw [hrad, hgauss, ← integral_sub hFr hFg]
  calc
    |∫ y, Fr y - Fg y ∂Erdos88.Invariance.hybridMeasure n t.val| ≤
        ∫ y, |Fr y - Fg y| ∂Erdos88.Invariance.hybridMeasure n t.val :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _y, M t / 6 ∂Erdos88.Invariance.hybridMeasure n t.val := by
      apply integral_mono (hFr.sub hFg).abs (integrable_const _)
      intro y
      have hrep := Erdos88.Invariance.affine_rademacher_gaussian_replacement
        (hF.lineTest t (base y)) 0 1
      simpa [Fr, Fg] using hrep
    _ = M t / 6 := by simp

/-- Normed-space finite-dimensional C⁴ Lindeberg replacement. -/
theorem rademacher_gaussian_replacement {n : ℕ}
    (F : E → ℝ) (v : Fin n → E) (M : Fin n → ℝ)
    (hF : IsBoundedC4OnLines F v M) :
    |∫ x, F (linearCombination v x)
          ∂Erdos88.Invariance.rademacherProductMeasure n -
        ∫ x, F (linearCombination v x)
          ∂Erdos88.Invariance.gaussianProductMeasure n| ≤
      ∑ i, M i / 6 := by
  cases n with
  | zero =>
      rw [← Erdos88.Invariance.hybridMeasure_zero 0,
        ← Erdos88.Invariance.hybridMeasure_eq_gaussian 0 0 (by norm_num)]
      simp
  | succ n =>
      rw [← Erdos88.Invariance.hybridMeasure_zero (n + 1),
        ← Erdos88.Invariance.hybridMeasure_eq_gaussian (n + 1) (n + 1) le_rfl]
      let G : ℕ → ℝ := fun t ↦
        ∫ x, F (linearCombination v x)
          ∂Erdos88.Invariance.hybridMeasure (n + 1) t
      calc
        |G 0 - G (n + 1)| ≤
            ∑ i : Fin (n + 1), |G i.val - G (i.val + 1)| :=
          Erdos88.Invariance.telescoping_abs G (n + 1)
        _ ≤ ∑ i : Fin (n + 1), M i / 6 := by
          apply Finset.sum_le_sum
          intro i _
          simpa [G] using hybrid_step F v M hF i

end NormedLindeberg

/-- The endpoint/prefix cutoff satisfies the normed-output line hypotheses
for any finite family of complex increment vectors. -/
theorem endpointPrefixCutoff_isBoundedC4OnLines (n l : ℕ)
    (endpointScale prefixScale : ℝ) (v : Fin n → Fin l → ℂ) :
    NormedLindeberg.IsBoundedC4OnLines
      (endpointPrefixCutoff l endpointScale prefixScale) v
      (fun i ↦ endpointPrefixDirectionBudget l endpointScale prefixScale (v i)) := by
  refine {
    measurable :=
      (endpointPrefixCutoff_contDiff l endpointScale prefixScale).continuous.measurable
    bounded := ⟨1, ?_⟩
    lineTest := ?_
  }
  · intro w
    rw [abs_of_nonneg (endpointPrefixCutoff_nonneg l endpointScale prefixScale w)]
    exact endpointPrefixCutoff_le_one l endpointScale prefixScale w
  · intro i a
    exact endpointPrefixCutoff_isBoundedC4Test_line l endpointScale prefixScale a (v i)

/-- Rademacher-to-Gaussian comparison for the smooth endpoint/prefix event
of a family of complex increment vectors. -/
theorem endpointPrefixCutoff_rademacher_gaussian_replacement (n l : ℕ)
    (endpointScale prefixScale : ℝ) (v : Fin n → Fin l → ℂ) :
    |∫ x, endpointPrefixCutoff l endpointScale prefixScale
          (NormedLindeberg.linearCombination v x)
          ∂Erdos88.Invariance.rademacherProductMeasure n -
        ∫ x, endpointPrefixCutoff l endpointScale prefixScale
          (NormedLindeberg.linearCombination v x)
          ∂Erdos88.Invariance.gaussianProductMeasure n| ≤
      ∑ i, endpointPrefixDirectionBudget l endpointScale prefixScale (v i) / 6 := by
  exact NormedLindeberg.rademacher_gaussian_replacement
    (endpointPrefixCutoff l endpointScale prefixScale) v
    (fun i ↦ endpointPrefixDirectionBudget l endpointScale prefixScale (v i))
    (endpointPrefixCutoff_isBoundedC4OnLines n l endpointScale prefixScale v)

end

end CutoffLindebergBridge

/-! ## Flat-block increment vectors for Lindeberg replacement -/

namespace FlatVectorAPI

noncomputable section

open CutoffLindebergBridge SmoothCutoffC4

/-- The natural-number coefficient represented by an offset into scale `k`. -/
def scaleCoefficient (N0 k : ℕ)
    (i : Fin (scale N0 (k + 1) - scale N0 k)) : ℕ :=
  scale N0 k + i

/-- Restrict a natural-number scalar sequence to the coefficient offsets in one scale. -/
def scaleRestriction (x : ℕ → ℝ) (N0 k : ℕ) :
    Fin (scale N0 (k + 1) - scale N0 k) → ℝ :=
  fun i => x (scaleCoefficient N0 k i)

/-- The coefficient-indexed direction whose only nonzero coordinate is the flat block
containing the coefficient.  Thus a linear combination of these directions is the vector
of flat-block increments. -/
def flatDirection (a : ℕ → ℝ) (z : ℂ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (i : Fin (scale N0 (k + 1) - scale N0 k)) :
    Fin (uniformBlockCount k) → ℂ :=
  fun r => if uniformBlockOfOffset hN0 k i = r then
    (a (scaleCoefficient N0 k i) : ℂ) * z ^ scaleCoefficient N0 k i else 0

@[simp] lemma flatDirection_apply_own (a : ℕ → ℝ) (z : ℂ) {N0 : ℕ}
    (hN0 : 0 < N0) (k : ℕ)
    (i : Fin (scale N0 (k + 1) - scale N0 k)) :
    flatDirection a z hN0 k i (uniformBlockOfOffset hN0 k i) =
      (a (scaleCoefficient N0 k i) : ℂ) * z ^ scaleCoefficient N0 k i := by
  simp [flatDirection]

lemma norm_flatDirection (a : ℕ → ℝ) {z : ℂ} (hz : ‖z‖ = 1) {N0 : ℕ}
    (hN0 : 0 < N0) (k : ℕ)
    (i : Fin (scale N0 (k + 1) - scale N0 k)) :
    ‖flatDirection a z hN0 k i‖ = |a (scaleCoefficient N0 k i)| := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (abs_nonneg _)]
    intro r
    by_cases hir : uniformBlockOfOffset hN0 k i = r
    · simp [flatDirection, hir, norm_pow, hz, Complex.norm_real, Real.norm_eq_abs]
    · simp [flatDirection, hir, abs_nonneg]
  · have h := norm_le_pi_norm (flatDirection a z hN0 k i)
        (uniformBlockOfOffset hN0 k i)
    simpa [norm_mul, norm_pow, hz, Complex.norm_real, Real.norm_eq_abs] using h

lemma linearCombination_flatDirection_apply (a : ℕ → ℝ) (z : ℂ) {N0 : ℕ}
    (hN0 : 0 < N0) (k : ℕ)
    (x : Fin (scale N0 (k + 1) - scale N0 k) → ℝ)
    (r : Fin (uniformBlockCount k)) :
    NormedLindeberg.linearCombination (flatDirection a z hN0 k) x r =
      ∑ i with uniformBlockOfOffset hN0 k i = r,
        ((x i * a (scaleCoefficient N0 k i) : ℝ) : ℂ) *
          z ^ scaleCoefficient N0 k i := by
  rw [Finset.sum_filter]
  simp [NormedLindeberg.linearCombination, flatDirection, Finset.sum_apply,
    Pi.smul_apply, mul_assoc]

/-- Summing all flat-block increments recovers the full coefficient sum on the scale. -/
lemma sum_linearCombination_flatDirection (a : ℕ → ℝ) (z : ℂ) {N0 : ℕ}
    (hN0 : 0 < N0) (k : ℕ)
    (x : Fin (scale N0 (k + 1) - scale N0 k) → ℝ) :
    (∑ r, NormedLindeberg.linearCombination (flatDirection a z hN0 k) x r) =
      ∑ i, ((x i * a (scaleCoefficient N0 k i) : ℝ) : ℂ) *
        z ^ scaleCoefficient N0 k i := by
  simp [NormedLindeberg.linearCombination, flatDirection, Finset.sum_apply,
    Pi.smul_apply, Finset.sum_comm, mul_assoc]

/-- Natural-number form of the endpoint identity: summing the block-increment vector gives
the signed polynomial on the whole scale interval. -/
lemma sum_linearCombination_flatDirection_scaleRestriction
    (a x : ℕ → ℝ) (z : ℂ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) :
    (∑ r, NormedLindeberg.linearCombination (flatDirection a z hN0 k)
      (scaleRestriction x N0 k) r) =
      signedPolynomial a x
        (Finset.Ico (scale N0 k) (scale N0 (k + 1))) z := by
  rw [sum_linearCombination_flatDirection]
  rw [signedPolynomial]
  rw [Finset.sum_Ico_eq_sum_range]
  unfold scaleRestriction scaleCoefficient
  rw [Fin.sum_univ_eq_sum_range
    (fun i => ((x (scale N0 k + i) * a (scale N0 k + i) : ℝ) : ℂ) *
      z ^ (scale N0 k + i))
    (scale N0 (k + 1) - scale N0 k)]

/-- The prefix of flat-block increments selects exactly the coefficients whose block number
does not exceed the prefix endpoint. -/
lemma sum_Iic_linearCombination_flatDirection (a : ℕ → ℝ) (z : ℂ) {N0 : ℕ}
    (hN0 : 0 < N0) (k : ℕ)
    (x : Fin (scale N0 (k + 1) - scale N0 k) → ℝ)
    (j : Fin (uniformBlockCount k)) :
    (∑ r ∈ Finset.Iic j,
        NormedLindeberg.linearCombination (flatDirection a z hN0 k) x r) =
      ∑ i with uniformBlockOfOffset hN0 k i ≤ j,
        ((x i * a (scaleCoefficient N0 k i) : ℝ) : ℂ) *
          z ^ scaleCoefficient N0 k i := by
  classical
  simp only [NormedLindeberg.linearCombination, Finset.sum_apply, Pi.smul_apply]
  rw [Finset.sum_comm]
  rw [Finset.sum_filter]
  simp [flatDirection, Finset.mem_Iic, mul_assoc]

lemma uniformBlockOfOffset_le_iff {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (i : Fin (scale N0 (k + 1) - scale N0 k))
    (j : Fin (uniformBlockCount k)) :
    uniformBlockOfOffset hN0 k i ≤ j ↔
      scaleCoefficient N0 k i < uniformEndpoint N0 k (j + 1) := by
  have hlen : 0 < uniformBlockLength N0 k := uniformBlockLength_pos hN0 k
  rw [show uniformBlockOfOffset hN0 k i ≤ j ↔
      i.val / uniformBlockLength N0 k < j.val + 1 by
    simp only [Fin.le_iff_val_le_val, uniformBlockOfOffset_val]
    omega]
  rw [Nat.div_lt_iff_lt_mul hlen]
  simp only [scaleCoefficient, uniformEndpoint]
  omega

/-- Natural-number form of the prefix identity. -/
lemma sum_Iic_linearCombination_flatDirection_scaleRestriction
    (a x : ℕ → ℝ) (z : ℂ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (j : Fin (uniformBlockCount k)) :
    (∑ r ∈ Finset.Iic j,
      NormedLindeberg.linearCombination (flatDirection a z hN0 k)
        (scaleRestriction x N0 k) r) =
      signedPolynomial a x
        (Finset.Ico (scale N0 k) (uniformEndpoint N0 k (j + 1))) z := by
  rw [sum_Iic_linearCombination_flatDirection]
  rw [signedPolynomial, Finset.sum_Ico_eq_sum_range]
  unfold scaleRestriction scaleCoefficient
  rw [Finset.sum_filter]
  let gap := scale N0 (k + 1) - scale N0 k
  let F : ℕ → ℂ := fun i =>
    ((x (scale N0 k + i) * a (scale N0 k + i) : ℝ) : ℂ) *
      z ^ (scale N0 k + i)
  let G : ℕ → ℂ := fun i => if hi : i < gap then
    if uniformBlockOfOffset hN0 k (⟨i, hi⟩ : Fin gap) ≤ j then F i else 0 else 0
  have hfin :
      (∑ i : Fin gap,
        if uniformBlockOfOffset hN0 k i ≤ j then F i.val else 0) =
        ∑ i ∈ Finset.range gap, G i := by
    rw [← Fin.sum_univ_eq_sum_range G gap]
    apply Finset.sum_congr rfl
    intro i hi
    simp [G]
  change (∑ i : Fin gap,
      if uniformBlockOfOffset hN0 k i ≤ j then F i.val else 0) = _
  rw [hfin]
  have hG : (∑ i ∈ Finset.range gap, G i) =
      ∑ i ∈ Finset.range gap,
        if i / uniformBlockLength N0 k ≤ j.val then F i else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [G, uniformBlockOfOffset, Fin.le_iff_val_le_val, Finset.mem_range.mp hi]
  rw [hG]
  have hend_le : uniformEndpoint N0 k (j.val + 1) ≤ scale N0 (k + 1) := by
    apply (uniformEndpoint_mono N0 k (show j.val + 1 ≤ uniformBlockCount k by omega)).trans_eq
    exact uniformEndpoint_last N0 k
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  have hscale : scale N0 k ≤ uniformEndpoint N0 k (j.val + 1) :=
    uniformBlock_start_ge_scale N0 k (j.val + 1)
  constructor
  · rintro ⟨hi, hij⟩
    have hlen : 0 < uniformBlockLength N0 k := uniformBlockLength_pos hN0 k
    have hij' : i < (j.val + 1) * uniformBlockLength N0 k :=
      (Nat.div_lt_iff_lt_mul hlen).mp (by omega)
    simp only [uniformEndpoint]
    omega
  · intro hi
    have hirange : i < scale N0 (k + 1) - scale N0 k := by
      simp only [uniformEndpoint] at hi hend_le
      omega
    refine ⟨hirange, ?_⟩
    have hlen : 0 < uniformBlockLength N0 k := uniformBlockLength_pos hN0 k
    apply Nat.lt_succ_iff.mp
    rw [Nat.div_lt_iff_lt_mul hlen]
    simpa only [uniformEndpoint, Nat.add_sub_cancel_left] using hi

/-- The sup norm of each one-coordinate direction loses no mass, so its `p`-moment
is exactly the coefficient `p`-moment on the scale. -/
lemma sum_norm_flatDirection_pow (a : ℕ → ℝ) {z : ℂ} (hz : ‖z‖ = 1)
    {N0 : ℕ} (hN0 : 0 < N0) (k p : ℕ) :
    (∑ i, ‖flatDirection a z hN0 k i‖ ^ p) =
      ∑ n ∈ Finset.Ico (scale N0 k) (scale N0 (k + 1)), |a n| ^ p := by
  simp_rw [norm_flatDirection a hz hN0 k]
  unfold scaleCoefficient
  rw [Fin.sum_univ_eq_sum_range
    (fun n => |a (scale N0 k + n)| ^ p)
    (scale N0 (k + 1) - scale N0 k)]
  exact (Finset.sum_Ico_eq_sum_range (fun n => |a n| ^ p)
    (scale N0 k) (scale N0 (k + 1))).symm

lemma sum_norm_sq_flatDirection (a : ℕ → ℝ) {z : ℂ} (hz : ‖z‖ = 1)
    {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) :
    (∑ i, ‖flatDirection a z hN0 k i‖ ^ 2) =
      ∑ n ∈ Finset.Ico (scale N0 k) (scale N0 (k + 1)), |a n| ^ 2 := by
  exact sum_norm_flatDirection_pow a hz hN0 k 2

lemma sum_norm_four_flatDirection (a : ℕ → ℝ) {z : ℂ} (hz : ‖z‖ = 1)
    {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) :
    (∑ i, ‖flatDirection a z hN0 k i‖ ^ 4) =
      ∑ n ∈ Finset.Ico (scale N0 k) (scale N0 (k + 1)), |a n| ^ 4 := by
  exact sum_norm_flatDirection_pow a hz hN0 k 4

lemma sum_norm_cube_flatDirection (a : ℕ → ℝ) {z : ℂ} (hz : ‖z‖ = 1)
    {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) :
    (∑ i, ‖flatDirection a z hN0 k i‖ ^ 3) =
      ∑ n ∈ Finset.Ico (scale N0 k) (scale N0 (k + 1)), |a n| ^ 3 := by
  exact sum_norm_flatDirection_pow a hz hN0 k 3

/-- The square energy on one scale is at most the envelope squared times a harmonic sum. -/
lemma sum_sq_scale_le_harmonic (a : ℕ → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (hscaled : ∀ n ∈ Finset.Ico (scale N0 k) (scale N0 (k + 1)),
      Real.sqrt (n : ℝ) * |a n| ≤ δ) :
    (∑ n ∈ Finset.Ico (scale N0 k) (scale N0 (k + 1)), |a n| ^ 2) ≤
      δ ^ 2 * (harmonic (scale N0 (k + 1)) : ℝ) := by
  let s := Finset.Ico (scale N0 k) (scale N0 (k + 1))
  let t := Finset.Icc 1 (scale N0 (k + 1))
  have hsub : s ⊆ t := by
    intro n hn
    simp only [s, t, Finset.mem_Ico, Finset.mem_Icc] at hn ⊢
    exact ⟨(scale_pos hN0 k).trans_le hn.1, hn.2.le⟩
  calc
    (∑ n ∈ s, |a n| ^ 2) ≤ ∑ n ∈ s, δ ^ 2 * (n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : 0 < n := (scale_pos hN0 k).trans_le
        ((Finset.mem_Ico.mp hn).1)
      have h := sq_abs_le_div_of_scaled_le (a := a) (δ := δ)
        hnpos le_rfl hδ (hscaled n hn)
      simpa [div_eq_mul_inv] using h
    _ ≤ ∑ n ∈ t, δ ^ 2 * (n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro n hnt hns
      positivity
    _ = δ ^ 2 * (harmonic (scale N0 (k + 1)) : ℝ) := by
      simp only [t, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
        Rat.cast_natCast]
      rw [Finset.mul_sum]

/-- Logarithmic form of the total square-energy estimate. -/
lemma sum_sq_scale_le_log (a : ℕ → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (hscaled : ∀ n ∈ Finset.Ico (scale N0 k) (scale N0 (k + 1)),
      Real.sqrt (n : ℝ) * |a n| ≤ δ) :
    (∑ n ∈ Finset.Ico (scale N0 k) (scale N0 (k + 1)), |a n| ^ 2) ≤
      δ ^ 2 * (1 + Real.log (scale N0 (k + 1))) := by
  exact (sum_sq_scale_le_harmonic a hδ hN0 k hscaled).trans
    (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log _) (sq_nonneg _))

lemma sum_abs_four_scale_le_log (a : ℕ → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (hscaled : ∀ n ∈ Finset.Ico (scale N0 k) (scale N0 (k + 1)),
      Real.sqrt (n : ℝ) * |a n| ≤ δ) :
    (∑ n ∈ Finset.Ico (scale N0 k) (scale N0 (k + 1)), |a n| ^ 4) ≤
      (δ ^ 2 / scale N0 k) *
        (δ ^ 2 * (1 + Real.log (scale N0 (k + 1)))) := by
  have hscale : 0 < scale N0 k := scale_pos hN0 k
  calc
    (∑ n ∈ Finset.Ico (scale N0 k) (scale N0 (k + 1)), |a n| ^ 4) =
        ∑ n ∈ Finset.Ico (scale N0 k) (scale N0 (k + 1)),
          |a n| ^ 2 * |a n| ^ 2 := by
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ ≤ ∑ n ∈ Finset.Ico (scale N0 k) (scale N0 (k + 1)),
          (δ ^ 2 / scale N0 k) * |a n| ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      gcongr
      exact sq_abs_le_div_of_scaled_le hscale (Finset.mem_Ico.mp hn).1 hδ
        (hscaled n hn)
    _ = (δ ^ 2 / scale N0 k) *
          ∑ n ∈ Finset.Ico (scale N0 k) (scale N0 (k + 1)), |a n| ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ (δ ^ 2 / scale N0 k) *
          (δ ^ 2 * (1 + Real.log (scale N0 (k + 1)))) := by
      exact mul_le_mul_of_nonneg_left (sum_sq_scale_le_log a hδ hN0 k hscaled)
        (div_nonneg (sq_nonneg _) (by positivity))

lemma sum_abs_cube_scale_le_log (a : ℕ → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (hscaled : ∀ n ∈ Finset.Ico (scale N0 k) (scale N0 (k + 1)),
      Real.sqrt (n : ℝ) * |a n| ≤ δ) :
    (∑ n ∈ Finset.Ico (scale N0 k) (scale N0 (k + 1)), |a n| ^ 3) ≤
      (δ / Real.sqrt (scale N0 k : ℝ)) *
        (δ ^ 2 * (1 + Real.log (scale N0 (k + 1)))) := by
  have hscale : 0 < scale N0 k := scale_pos hN0 k
  calc
    (∑ n ∈ Finset.Ico (scale N0 k) (scale N0 (k + 1)), |a n| ^ 3) =
        ∑ n ∈ Finset.Ico (scale N0 k) (scale N0 (k + 1)),
          |a n| * |a n| ^ 2 := by
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ ≤ ∑ n ∈ Finset.Ico (scale N0 k) (scale N0 (k + 1)),
          (δ / Real.sqrt (scale N0 k : ℝ)) * |a n| ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      gcongr
      exact abs_le_div_sqrt_of_scaled_le hscale (Finset.mem_Ico.mp hn).1
        (hscaled n hn)
    _ = (δ / Real.sqrt (scale N0 k : ℝ)) *
          ∑ n ∈ Finset.Ico (scale N0 k) (scale N0 (k + 1)), |a n| ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ (δ / Real.sqrt (scale N0 k : ℝ)) *
          (δ ^ 2 * (1 + Real.log (scale N0 (k + 1)))) := by
      exact mul_le_mul_of_nonneg_left (sum_sq_scale_le_log a hδ hN0 k hscaled)
        (div_nonneg hδ (Real.sqrt_nonneg _))

/-- Total variance of the flat direction family. -/
lemma sum_norm_sq_flatDirection_le_log (a : ℕ → ℝ) {z : ℂ} (hz : ‖z‖ = 1)
    {δ : ℝ} (hδ : 0 ≤ δ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (hscaled : ∀ n ∈ Finset.Ico (scale N0 k) (scale N0 (k + 1)),
      Real.sqrt (n : ℝ) * |a n| ≤ δ) :
    (∑ i, ‖flatDirection a z hN0 k i‖ ^ 2) ≤
      δ ^ 2 * (1 + Real.log (scale N0 (k + 1))) := by
  rw [sum_norm_sq_flatDirection a hz hN0 k]
  exact sum_sq_scale_le_log a hδ hN0 k hscaled

lemma sum_norm_four_flatDirection_le_log (a : ℕ → ℝ) {z : ℂ} (hz : ‖z‖ = 1)
    {δ : ℝ} (hδ : 0 ≤ δ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (hscaled : ∀ n ∈ Finset.Ico (scale N0 k) (scale N0 (k + 1)),
      Real.sqrt (n : ℝ) * |a n| ≤ δ) :
    (∑ i, ‖flatDirection a z hN0 k i‖ ^ 4) ≤
      (δ ^ 2 / scale N0 k) *
        (δ ^ 2 * (1 + Real.log (scale N0 (k + 1)))) := by
  rw [sum_norm_four_flatDirection a hz hN0 k]
  exact sum_abs_four_scale_le_log a hδ hN0 k hscaled

lemma sum_norm_cube_flatDirection_le_log (a : ℕ → ℝ) {z : ℂ} (hz : ‖z‖ = 1)
    {δ : ℝ} (hδ : 0 ≤ δ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (hscaled : ∀ n ∈ Finset.Ico (scale N0 k) (scale N0 (k + 1)),
      Real.sqrt (n : ℝ) * |a n| ≤ δ) :
    (∑ i, ‖flatDirection a z hN0 k i‖ ^ 3) ≤
      (δ / Real.sqrt (scale N0 k : ℝ)) *
        (δ ^ 2 * (1 + Real.log (scale N0 (k + 1)))) := by
  rw [sum_norm_cube_flatDirection a hz hN0 k]
  exact sum_abs_cube_scale_le_log a hδ hN0 k hscaled

/-- A generic summation form of the explicit fourth-derivative direction budget. -/
lemma sum_endpointPrefixDirectionBudget_le (n l : ℕ)
    (endpointScale prefixScale : ℝ) (v : Fin n → Fin l → ℂ) :
    (∑ i, endpointPrefixDirectionBudget l endpointScale prefixScale (v i)) ≤
      (cutoffC4 * (((l + 1 : ℕ) : ℝ) *
        (|endpointScale| + |prefixScale|) * l)) ^ 4 *
          ∑ i, ‖v i‖ ^ 4 := by
  calc
    (∑ i, endpointPrefixDirectionBudget l endpointScale prefixScale (v i)) ≤
        ∑ i, (cutoffC4 * (((l + 1 : ℕ) : ℝ) *
          (|endpointScale| + |prefixScale|) * l) * ‖v i‖) ^ 4 := by
      apply Finset.sum_le_sum
      intro i hi
      unfold endpointPrefixDirectionBudget
      apply pow_le_pow_left₀
      · exact mul_nonneg
          (mul_nonneg cutoffC4_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _))
          (norm_nonneg _)
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (sum_norm_endpointPrefixForms_le l endpointScale prefixScale)
            cutoffC4_nonneg)
          (norm_nonneg _)
    _ = (cutoffC4 * (((l + 1 : ℕ) : ℝ) *
          (|endpointScale| + |prefixScale|) * l)) ^ 4 *
            ∑ i, ‖v i‖ ^ 4 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [mul_pow]

/-- The complete fourth-order Lindeberg budget for the flat-block increment family. -/
lemma sum_flatDirection_budget_le_log (a : ℕ → ℝ) {z : ℂ} (hz : ‖z‖ = 1)
    {δ : ℝ} (hδ : 0 ≤ δ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (endpointScale prefixScale : ℝ)
    (hscaled : ∀ n ∈ Finset.Ico (scale N0 k) (scale N0 (k + 1)),
      Real.sqrt (n : ℝ) * |a n| ≤ δ) :
    (∑ i, endpointPrefixDirectionBudget (uniformBlockCount k)
      endpointScale prefixScale (flatDirection a z hN0 k i)) ≤
      (cutoffC4 * ((((uniformBlockCount k + 1 : ℕ) : ℝ)) *
        (|endpointScale| + |prefixScale|) * uniformBlockCount k)) ^ 4 *
        ((δ ^ 2 / scale N0 k) *
          (δ ^ 2 * (1 + Real.log (scale N0 (k + 1))))) := by
  exact (sum_endpointPrefixDirectionBudget_le
      (scale N0 (k + 1) - scale N0 k) (uniformBlockCount k)
      endpointScale prefixScale (flatDirection a z hN0 k)).trans
    (mul_le_mul_of_nonneg_left
      (sum_norm_four_flatDirection_le_log a hz hδ hN0 k hscaled)
      (Even.pow_nonneg (by norm_num) _))

/-! ### Exact finite-scale coordinate law -/

lemma scaleCoefficient_injective (N0 k : ℕ) :
    Function.Injective (scaleCoefficient N0 k) := by
  intro i j hij
  apply Fin.ext
  exact Nat.add_left_cancel hij

lemma measurable_scaleRestriction (N0 k : ℕ) :
    Measurable (fun x : ℕ → ℝ ↦ scaleRestriction x N0 k) := by
  exact measurable_pi_lambda _ fun i ↦ measurable_pi_apply (scaleCoefficient N0 k i)

/-- Restricting the infinite sign sequence to one scale gives exactly the finite
Rademacher product law used by the Lindeberg replacement theorem. -/
theorem map_scaleRestriction_rademacher (N0 k : ℕ) :
    rademacherProductMeasure.map (fun x ↦ scaleRestriction x N0 k) =
      Erdos88.Invariance.rademacherProductMeasure
        (scale N0 (k + 1) - scale N0 k) := by
  let n := scale N0 (k + 1) - scale N0 k
  have hind : iIndepFun
      (fun i : Fin n ↦ fun x : ℕ → ℝ ↦ x (scaleCoefficient N0 k i))
      rademacherProductMeasure :=
    iIndepFun_eval_rademacherProduct.precomp
      (scaleCoefficient_injective N0 k)
  have hmap := hind.map_fun_eq_infinitePi_map
    (fun i : Fin n ↦ measurable_pi_apply (scaleCoefficient N0 k i))
  change rademacherProductMeasure.map
      (fun x : ℕ → ℝ ↦ fun i : Fin n ↦ x (scaleCoefficient N0 k i)) = _
  rw [hmap]
  simp_rw [rademacherProductMeasure_map_eval]
  rw [Measure.infinitePi_eq_pi]
  unfold Erdos88.Invariance.rademacherProductMeasure
  rw [rademacherMeasure_eq_invariance]

/-- Event probabilities on one scale transfer exactly to the finite product law. -/
theorem measure_preimage_scaleRestriction_rademacher (N0 k : ℕ)
    {s : Set (Fin (scale N0 (k + 1) - scale N0 k) → ℝ)}
    (hs : MeasurableSet s) :
    rademacherProductMeasure ((fun x ↦ scaleRestriction x N0 k) ⁻¹' s) =
      Erdos88.Invariance.rademacherProductMeasure
        (scale N0 (k + 1) - scale N0 k) s := by
  rw [← map_scaleRestriction_rademacher N0 k]
  exact (Measure.map_apply (measurable_scaleRestriction N0 k) hs).symm

theorem measureReal_preimage_scaleRestriction_rademacher (N0 k : ℕ)
    {s : Set (Fin (scale N0 (k + 1) - scale N0 k) → ℝ)}
    (hs : MeasurableSet s) :
    rademacherProductMeasure.real ((fun x ↦ scaleRestriction x N0 k) ⁻¹' s) =
      (Erdos88.Invariance.rademacherProductMeasure
        (scale N0 (k + 1) - scale N0 k)).real s := by
  exact congrArg ENNReal.toReal
    (measure_preimage_scaleRestriction_rademacher N0 k hs)

/-- The set of natural-number coordinates belonging to one scale. -/
def scaleCoordinateSet (N0 k : ℕ) : Finset ℕ :=
  Finset.Ico (scale N0 k) (scale N0 (k + 1))

def scaleCoordinateSubtype (N0 k : ℕ)
    (i : Fin (scale N0 (k + 1) - scale N0 k)) : scaleCoordinateSet N0 k :=
  ⟨scaleCoefficient N0 k i, by
    simp only [scaleCoordinateSet, Finset.mem_Ico, scaleCoefficient]
    constructor
    · omega
    · have hmono := scale_le_scale_succ N0 k
      omega⟩

def scaleSubtypeRestriction (N0 k : ℕ)
    (x : scaleCoordinateSet N0 k → ℝ) :
    Fin (scale N0 (k + 1) - scale N0 k) → ℝ :=
  fun i ↦ x (scaleCoordinateSubtype N0 k i)

lemma measurable_scaleSubtypeRestriction (N0 k : ℕ) :
    Measurable (scaleSubtypeRestriction N0 k) := by
  exact measurable_pi_lambda _ fun i ↦ measurable_pi_apply (scaleCoordinateSubtype N0 k i)

lemma disjoint_scaleCoordinateSet {N0 k l : ℕ} (_hN0 : 0 < N0) (hkl : k ≠ l) :
    Disjoint (scaleCoordinateSet N0 k) (scaleCoordinateSet N0 l) := by
  rw [Finset.disjoint_left]
  intro n hnk hnl
  simp only [scaleCoordinateSet, Finset.mem_Ico] at hnk hnl
  rcases lt_or_gt_of_ne hkl with h | h
  · have hstep : k + 1 ≤ l := by omega
    have hscale : scale N0 (k + 1) ≤ scale N0 l := scale_monotone N0 hstep
    omega
  · have hstep : l + 1 ≤ k := by omega
    have hscale : scale N0 (l + 1) ≤ scale N0 k := scale_monotone N0 hstep
    omega

/-- Distinct scale restrictions are independent because they use disjoint coordinate
intervals of the infinite product space. -/
theorem indepFun_scaleRestriction_of_ne {N0 k l : ℕ} (hN0 : 0 < N0)
    (hkl : k ≠ l) :
    IndepFun (fun x : ℕ → ℝ ↦ scaleRestriction x N0 k)
      (fun x : ℕ → ℝ ↦ scaleRestriction x N0 l)
      rademacherProductMeasure := by
  have hbase : IndepFun
      (fun (x : ℕ → ℝ) (i : scaleCoordinateSet N0 k) ↦ x (i : ℕ))
      (fun (x : ℕ → ℝ) (i : scaleCoordinateSet N0 l) ↦ x (i : ℕ))
      rademacherProductMeasure :=
    iIndepFun_eval_rademacherProduct.indepFun_finset
      (scaleCoordinateSet N0 k) (scaleCoordinateSet N0 l)
      (disjoint_scaleCoordinateSet hN0 hkl)
      (fun i ↦ measurable_pi_apply i)
  have hcomp := hbase.comp
    (measurable_scaleSubtypeRestriction N0 k)
    (measurable_scaleSubtypeRestriction N0 l)
  have hkfun :
      scaleSubtypeRestriction N0 k ∘
          (fun (x : ℕ → ℝ) (i : scaleCoordinateSet N0 k) ↦ x (i : ℕ)) =
        fun x : ℕ → ℝ ↦ scaleRestriction x N0 k := by
    rfl
  have hlfun :
      scaleSubtypeRestriction N0 l ∘
          (fun (x : ℕ → ℝ) (i : scaleCoordinateSet N0 l) ↦ x (i : ℕ)) =
        fun x : ℕ → ℝ ↦ scaleRestriction x N0 l := by
    rfl
  rwa [hkfun, hlfun] at hcomp

/-- Integration of a measurable finite-scale statistic transfers exactly to the finite
Rademacher product law. -/
theorem integral_scaleRestriction_rademacher {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] (N0 k : ℕ)
    (f : (Fin (scale N0 (k + 1) - scale N0 k) → ℝ) → G)
    (hf : AEStronglyMeasurable f
      (Erdos88.Invariance.rademacherProductMeasure
        (scale N0 (k + 1) - scale N0 k))) :
    ∫ x, f (scaleRestriction x N0 k) ∂rademacherProductMeasure =
      ∫ y, f y ∂Erdos88.Invariance.rademacherProductMeasure
        (scale N0 (k + 1) - scale N0 k) := by
  have hmap := map_scaleRestriction_rademacher N0 k
  have hf' : AEStronglyMeasurable f
      (rademacherProductMeasure.map (fun x ↦ scaleRestriction x N0 k)) := by
    rw [hmap]
    exact hf
  have hint := integral_map (measurable_scaleRestriction N0 k).aemeasurable hf'
  rw [hmap] at hint
  exact hint.symm

end

end FlatVectorAPI

/-! ## One-point Lindeberg comparison on the flat partition -/

namespace OnePointLindeberg

open SmoothCutoffC4 CutoffLindebergBridge

noncomputable section

/-- The natural-number index represented by an offset into the `k`th scale. -/
def flatScaleIndex (N0 k : ℕ)
    (i : Fin (scale N0 (k + 1) - scale N0 k)) : ℕ :=
  scale N0 k + i

/-- The deterministic complex coefficient at phase `z` represented by an
offset into the `k`th scale. -/
def flatPhaseCoefficient (a : ℕ → ℝ) (N0 k : ℕ) (z : ℂ)
    (i : Fin (scale N0 (k + 1) - scale N0 k)) : ℂ :=
  (a (flatScaleIndex N0 k i) : ℂ) * z ^ flatScaleIndex N0 k i

/-- One coefficient, viewed as a vector of flat-block increments.  It is
supported in precisely the flat block containing that coefficient. -/
def flatBlockIncrementDirection (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0)
    (k : ℕ) (z : ℂ)
    (i : Fin (scale N0 (k + 1) - scale N0 k)) :
    Fin (uniformBlockCount k) → ℂ :=
  fun r ↦ if r = uniformBlockOfOffset hN0 k i then
    flatPhaseCoefficient a N0 k z i else 0

@[simp] lemma flatBlockIncrementDirection_apply_self
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) (z : ℂ)
    (i : Fin (scale N0 (k + 1) - scale N0 k)) :
    flatBlockIncrementDirection a hN0 k z i (uniformBlockOfOffset hN0 k i) =
      flatPhaseCoefficient a N0 k z i := by
  simp [flatBlockIncrementDirection]

lemma norm_flatPhaseCoefficient_le (a : ℕ → ℝ) (N0 k : ℕ) (z : ℂ)
    (hz : ‖z‖ = 1) (i : Fin (scale N0 (k + 1) - scale N0 k)) :
    ‖flatPhaseCoefficient a N0 k z i‖ ≤ |a (flatScaleIndex N0 k i)| := by
  simp [flatPhaseCoefficient, norm_pow, hz, Real.norm_eq_abs]

lemma norm_flatBlockIncrementDirection_le
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) (z : ℂ)
    (hz : ‖z‖ = 1) (i : Fin (scale N0 (k + 1) - scale N0 k)) :
    ‖flatBlockIncrementDirection a hN0 k z i‖ ≤
      |a (flatScaleIndex N0 k i)| := by
  rw [pi_norm_le_iff_of_nonneg (abs_nonneg _)]
  intro r
  by_cases hr : r = uniformBlockOfOffset hN0 k i
  · simp [flatBlockIncrementDirection, hr, norm_flatPhaseCoefficient_le a N0 k z hz i]
  · simp [flatBlockIncrementDirection, hr]

/-- The polynomial operator factor in the concrete endpoint/prefix cutoff. -/
def flatCutoffOperatorBudget (k : ℕ) (endpointScale prefixScale : ℝ) : ℝ :=
  cutoffC4 *
    (((uniformBlockCount k + 1 : ℕ) : ℝ) *
      (|endpointScale| + |prefixScale|) * uniformBlockCount k)

lemma flatCutoffOperatorBudget_nonneg (k : ℕ)
    (endpointScale prefixScale : ℝ) :
    0 ≤ flatCutoffOperatorBudget k endpointScale prefixScale := by
  unfold flatCutoffOperatorBudget
  exact mul_nonneg cutoffC4_nonneg
    (mul_nonneg
      (mul_nonneg (by positivity) (add_nonneg (abs_nonneg _) (abs_nonneg _)))
      (by positivity))

lemma flat_directionBudget_le
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) (z : ℂ)
    (hz : ‖z‖ = 1) (endpointScale prefixScale : ℝ)
    (i : Fin (scale N0 (k + 1) - scale N0 k)) :
    endpointPrefixDirectionBudget (uniformBlockCount k) endpointScale prefixScale
        (flatBlockIncrementDirection a hN0 k z i) ≤
      (flatCutoffOperatorBudget k endpointScale prefixScale *
        |a (flatScaleIndex N0 k i)|) ^ 4 := by
  unfold endpointPrefixDirectionBudget flatCutoffOperatorBudget
  apply pow_le_pow_left₀
    (mul_nonneg
      (mul_nonneg cutoffC4_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _))
      (norm_nonneg _)) (by
    calc
      (cutoffC4 *
          ∑ j, ‖endpointPrefixForms (uniformBlockCount k)
            endpointScale prefixScale j‖) *
          ‖flatBlockIncrementDirection a hN0 k z i‖ =
        cutoffC4 *
          ((∑ j, ‖endpointPrefixForms (uniformBlockCount k)
              endpointScale prefixScale j‖) *
            ‖flatBlockIncrementDirection a hN0 k z i‖) := by ring
      _ ≤ cutoffC4 *
          ((((uniformBlockCount k + 1 : ℕ) : ℝ) *
              (|endpointScale| + |prefixScale|) * uniformBlockCount k) *
            |a (flatScaleIndex N0 k i)|) := by
        apply mul_le_mul_of_nonneg_left _ cutoffC4_nonneg
        exact mul_le_mul
          (sum_norm_endpointPrefixForms_le
            (uniformBlockCount k) endpointScale prefixScale)
          (norm_flatBlockIncrementDirection_le a hN0 k z hz i)
          (norm_nonneg _) (by positivity)
      _ = (cutoffC4 *
          (((uniformBlockCount k + 1 : ℕ) : ℝ) *
            (|endpointScale| + |prefixScale|) * uniformBlockCount k)) *
          |a (flatScaleIndex N0 k i)| := by ring) 4

lemma flatScaleIndex_ge (N0 k : ℕ)
    (i : Fin (scale N0 (k + 1) - scale N0 k)) :
    scale N0 k ≤ flatScaleIndex N0 k i := by
  simp [flatScaleIndex]

lemma flatScaleIndex_mem_uniformBlock
    {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (i : Fin (scale N0 (k + 1) - scale N0 k)) :
    flatScaleIndex N0 k i ∈
      uniformBlock N0 k (uniformBlockOfOffset hN0 k i) := by
  rw [mem_uniformBlock_iff]
  simp only [uniformEndpoint, uniformBlockOfOffset_val, flatScaleIndex]
  have hlen := uniformBlockLength_pos hN0 k
  have hlo := Nat.div_mul_le_self i.val (uniformBlockLength N0 k)
  have hhi := Nat.lt_mul_div_succ i.val hlen
  have hhi' : i.val <
      (i.val / uniformBlockLength N0 k + 1) * uniformBlockLength N0 k := by
    simpa [Nat.mul_comm] using hhi
  rw [Nat.add_mul, one_mul] at hhi'
  omega

lemma flat_linearCombination_apply
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) (z : ℂ)
    (x : Fin (scale N0 (k + 1) - scale N0 k) → ℝ)
    (r : Fin (uniformBlockCount k)) :
    CutoffLindebergBridge.NormedLindeberg.linearCombination
        (flatBlockIncrementDirection a hN0 k z) x r =
      ∑ i with uniformBlockOfOffset hN0 k i = r,
        x i • flatPhaseCoefficient a N0 k z i := by
  simp only [CutoffLindebergBridge.NormedLindeberg.linearCombination,
    Finset.sum_apply, Pi.smul_apply, flatBlockIncrementDirection]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : uniformBlockOfOffset hN0 k i = r
  · simp [hi]
  · have hir : r ≠ uniformBlockOfOffset hN0 k i := by
      exact fun h ↦ hi h.symm
    simp [hi, hir]

lemma sum_abs_four_flatScale_le
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) :
    (∑ i : Fin (scale N0 (k + 1) - scale N0 k),
        |a (flatScaleIndex N0 k i)| ^ 4) ≤
      (scale N0 (k + 1) - scale N0 k : ℕ) *
        ((coefficientEnvelope a N0 k) ^ 2 / scale N0 k) ^ 2 := by
  have hδ := coefficientEnvelope_nonneg a hsmall N0 k
  have hS : 0 < scale N0 k := scale_pos hN0 k
  calc
    (∑ i : Fin (scale N0 (k + 1) - scale N0 k),
        |a (flatScaleIndex N0 k i)| ^ 4) ≤
      ∑ _i : Fin (scale N0 (k + 1) - scale N0 k),
        ((coefficientEnvelope a N0 k) ^ 2 / scale N0 k) ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          have hs := sq_abs_le_div_of_scaled_le hS
            (flatScaleIndex_ge N0 k i) hδ
            (scaledAbs_le_coefficientEnvelope a hsmall (flatScaleIndex_ge N0 k i))
          rw [show |a (flatScaleIndex N0 k i)| ^ 4 =
              (|a (flatScaleIndex N0 k i)| ^ 2) ^ 2 by ring]
          exact pow_le_pow_left₀ (sq_nonneg _) hs 2
    _ = (scale N0 (k + 1) - scale N0 k : ℕ) *
        ((coefficientEnvelope a N0 k) ^ 2 / scale N0 k) ^ 2 := by
          simp

/-- The same fourth-power estimate in the flat-block form: the fourth mass
of each block is bounded by `(delta^2 / N_k) (delta^2 / 2^k)`, and there are
`uniformBlockCount k` blocks. -/
lemma sum_abs_four_flatScale_le_uniformBlockCount
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) :
    (∑ i : Fin (scale N0 (k + 1) - scale N0 k),
        |a (flatScaleIndex N0 k i)| ^ 4) ≤
      uniformBlockCount k *
        (((coefficientEnvelope a N0 k) ^ 2 / scale N0 k) *
          ((coefficientEnvelope a N0 k) ^ 2 / 2 ^ k)) := by
  apply (sum_abs_four_flatScale_le a hsmall hN0 k).trans_eq
  rw [scale_gap_eq_uniformBlockCount_mul_length]
  push_cast
  have hS : (0 : ℝ) < scale N0 k := by exact_mod_cast scale_pos hN0 k
  have htwo : (0 : ℝ) < 2 ^ k := by positivity
  have hlen : ((uniformBlockLength N0 k : ℕ) : ℝ) * (2 : ℝ) ^ k =
      scale N0 k := by
    exact_mod_cast uniformBlockLength_mul_parts N0 k
  field_simp
  calc
    (uniformBlockCount k : ℝ) * uniformBlockLength N0 k *
          coefficientEnvelope a N0 k ^ 4 * 2 ^ k =
        (uniformBlockCount k : ℝ) * coefficientEnvelope a N0 k ^ 4 *
          ((uniformBlockLength N0 k : ℝ) * 2 ^ k) := by ring
    _ = (uniformBlockCount k : ℝ) * coefficientEnvelope a N0 k ^ 4 *
          scale N0 k := by rw [hlen]

/-- An explicit upper bound for the total one-point fourth-order replacement
error on scale `k`. -/
def flatOnePointLindebergError (a : ℕ → ℝ) (N0 k : ℕ)
    (endpointScale prefixScale : ℝ) : ℝ :=
  (flatCutoffOperatorBudget k endpointScale prefixScale) ^ 4 *
      ((scale N0 (k + 1) - scale N0 k : ℕ) *
        ((coefficientEnvelope a N0 k) ^ 2 / scale N0 k) ^ 2) / 6

lemma sum_flat_directionBudget_div_le_error
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) (z : ℂ) (hz : ‖z‖ = 1)
    (endpointScale prefixScale : ℝ) :
    (∑ i : Fin (scale N0 (k + 1) - scale N0 k),
        endpointPrefixDirectionBudget (uniformBlockCount k) endpointScale prefixScale
          (flatBlockIncrementDirection a hN0 k z i) / 6) ≤
      flatOnePointLindebergError a N0 k endpointScale prefixScale := by
  rw [← Finset.sum_div]
  unfold flatOnePointLindebergError
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    (∑ i : Fin (scale N0 (k + 1) - scale N0 k),
        endpointPrefixDirectionBudget (uniformBlockCount k) endpointScale prefixScale
          (flatBlockIncrementDirection a hN0 k z i)) ≤
      ∑ i : Fin (scale N0 (k + 1) - scale N0 k),
        (flatCutoffOperatorBudget k endpointScale prefixScale) ^ 4 *
          |a (flatScaleIndex N0 k i)| ^ 4 := by
            apply Finset.sum_le_sum
            intro i _
            simpa [mul_pow] using
              flat_directionBudget_le a hN0 k z hz endpointScale prefixScale i
    _ = (flatCutoffOperatorBudget k endpointScale prefixScale) ^ 4 *
        ∑ i : Fin (scale N0 (k + 1) - scale N0 k),
          |a (flatScaleIndex N0 k i)| ^ 4 := by
            rw [Finset.mul_sum]
    _ ≤ (flatCutoffOperatorBudget k endpointScale prefixScale) ^ 4 *
        ((scale N0 (k + 1) - scale N0 k : ℕ) *
          ((coefficientEnvelope a N0 k) ^ 2 / scale N0 k) ^ 2) := by
            exact mul_le_mul_of_nonneg_left
              (sum_abs_four_flatScale_le a hsmall hN0 k) (by positivity)

/-- The concrete one-point Rademacher cutoff expectation is at least its
Gaussian analogue minus the explicit fourth-order replacement error. -/
theorem flat_rademacher_expectation_ge_gaussian_sub_error
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) (z : ℂ) (hz : ‖z‖ = 1)
    (endpointScale prefixScale : ℝ) :
    (∫ x, endpointPrefixCutoff (uniformBlockCount k) endpointScale prefixScale
          (CutoffLindebergBridge.NormedLindeberg.linearCombination
            (flatBlockIncrementDirection a hN0 k z) x)
          ∂Erdos88.Invariance.gaussianProductMeasure
            (scale N0 (k + 1) - scale N0 k)) -
        flatOnePointLindebergError a N0 k endpointScale prefixScale ≤
      ∫ x, endpointPrefixCutoff (uniformBlockCount k) endpointScale prefixScale
          (CutoffLindebergBridge.NormedLindeberg.linearCombination
            (flatBlockIncrementDirection a hN0 k z) x)
          ∂Erdos88.Invariance.rademacherProductMeasure
            (scale N0 (k + 1) - scale N0 k) := by
  have hreplacement := endpointPrefixCutoff_rademacher_gaussian_replacement
    (scale N0 (k + 1) - scale N0 k) (uniformBlockCount k)
    endpointScale prefixScale (flatBlockIncrementDirection a hN0 k z)
  have hbudget := sum_flat_directionBudget_div_le_error
    a hsmall hN0 k z hz endpointScale prefixScale
  have habs := hreplacement.trans hbudget
  have hneg : -flatOnePointLindebergError a N0 k endpointScale prefixScale ≤
      (∫ x, endpointPrefixCutoff (uniformBlockCount k) endpointScale prefixScale
          (CutoffLindebergBridge.NormedLindeberg.linearCombination
            (flatBlockIncrementDirection a hN0 k z) x)
          ∂Erdos88.Invariance.rademacherProductMeasure
            (scale N0 (k + 1) - scale N0 k)) -
        ∫ x, endpointPrefixCutoff (uniformBlockCount k) endpointScale prefixScale
          (CutoffLindebergBridge.NormedLindeberg.linearCombination
            (flatBlockIncrementDirection a hN0 k z) x)
          ∂Erdos88.Invariance.gaussianProductMeasure
            (scale N0 (k + 1) - scale N0 k) :=
    (neg_le_neg habs).trans (neg_abs_le _)
  linarith

/-- A supplied Gaussian lower bound survives replacement whenever the
replacement error is at most half that bound. -/
theorem half_lower_bound_flat_rademacher_expectation
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) (z : ℂ) (hz : ‖z‖ = 1)
    (endpointScale prefixScale p : ℝ)
    (hgaussian : p ≤
      ∫ x, endpointPrefixCutoff (uniformBlockCount k) endpointScale prefixScale
          (CutoffLindebergBridge.NormedLindeberg.linearCombination
            (flatBlockIncrementDirection a hN0 k z) x)
          ∂Erdos88.Invariance.gaussianProductMeasure
            (scale N0 (k + 1) - scale N0 k))
    (herror : flatOnePointLindebergError a N0 k endpointScale prefixScale ≤ p / 2) :
    p / 2 ≤
      ∫ x, endpointPrefixCutoff (uniformBlockCount k) endpointScale prefixScale
          (CutoffLindebergBridge.NormedLindeberg.linearCombination
            (flatBlockIncrementDirection a hN0 k z) x)
          ∂Erdos88.Invariance.rademacherProductMeasure
            (scale N0 (k + 1) - scale N0 k) := by
  have hcompare := flat_rademacher_expectation_ge_gaussian_sub_error
    a hsmall hN0 k z hz endpointScale prefixScale
  linarith

end

end OnePointLindeberg

/-! ## Gaussian circularization -/

namespace GaussianCircularization

open scoped ENNReal NNReal ComplexConjugate

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- A finite family of independent standard real Gaussian random variables. -/
structure IndependentStandardGaussians {J : Type*} [Finite J] (u : J → Ω → ℝ)
    (P : Measure Ω) : Prop where
  law : ∀ j, HasLaw (u j) (gaussianReal 0 1) P
  indep : iIndepFun u P

namespace IndependentStandardGaussians

variable {J : Type*} [Finite J] {u : J → Ω → ℝ}

lemma hasGaussianLaw (h : IndependentStandardGaussians u P) (j : J) :
    HasGaussianLaw (u j) P :=
  (h.law j).hasGaussianLaw

lemma jointlyGaussian (h : IndependentStandardGaussians u P) :
    HasGaussianLaw (fun ω j ↦ u j ω) P :=
  h.indep.hasGaussianLaw h.hasGaussianLaw

lemma memLp_two (h : IndependentStandardGaussians u P) (j : J) : MemLp (u j) 2 P :=
  (h.hasGaussianLaw j).memLp_two

lemma integral_eq_zero (h : IndependentStandardGaussians u P) (j : J) :
    ∫ ω, u j ω ∂P = 0 := by
  rw [(h.law j).integral_eq]
  exact integral_id_gaussianReal

lemma variance_eq_one (h : IndependentStandardGaussians u P) (j : J) :
    Var[u j; P] = 1 := by
  rw [(h.law j).variance_eq]
  exact variance_fun_id_gaussianReal

lemma covariance_eq_ite [DecidableEq J] (h : IndependentStandardGaussians u P) (i j : J) :
    cov[u i, u j; P] = if i = j then 1 else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, covariance_self (h.hasGaussianLaw i).aemeasurable,
      h.variance_eq_one]
  · rw [if_neg hij]
    exact (h.indep.indepFun hij).covariance_eq_zero
      (h.memLp_two i) (h.memLp_two j)

end IndependentStandardGaussians

section LinearImages

variable {J K : Type*} [Fintype J] [Fintype K]

/-- `HasGaussianLaw` on Euclidean space with the topology and algebra structures supplied by its
normed-space instance.  This explicit wrapper avoids the non-definitional equality between the two
canonical topologies and algebra structures on `PiLp`. -/
def HasEuclideanGaussianLaw {K : Type*} [Fintype K]
    (X : Ω → EuclideanSpace ℝ K) (P : Measure Ω) : Prop :=
  @HasGaussianLaw Ω (EuclideanSpace ℝ K) _
    (@UniformSpace.toTopologicalSpace _ (@PseudoMetricSpace.toUniformSpace _ inferInstance))
    (PiLp.normedAddCommGroup 2 (fun _ : K ↦ ℝ)).toAddCommMonoid
    (PiLp.normedSpace 2 ℝ (fun _ : K ↦ ℝ)).toModule
    (WithLp.measurableSpace 2 ((i : K) → (fun _ : K ↦ ℝ) i)) X P

/-- The vector whose `k`th coordinate is the linear combination with coefficient row `A k`. -/
def linearPath (A : K → J → ℝ) (u : J → Ω → ℝ) (ω : Ω) : EuclideanSpace ℝ K :=
  WithLp.toLp 2 (fun k ↦ ∑ j, A k j * u j ω)

/-- The finite-dimensional linear map underlying `linearPath`. -/
def linearPathLinearMap (A : K → J → ℝ) : (J → ℝ) →ₗ[ℝ] EuclideanSpace ℝ K where
  toFun x := WithLp.toLp 2 (fun k ↦ ∑ j, A k j * x j)
  map_add' x y := by
    ext k
    change (∑ j, A k j * (x j + y j)) = (∑ j, A k j * x j) + ∑ j, A k j * y j
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  map_smul' r x := by
    ext k
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    change (∑ j, A k j * (r * x j)) = r * ∑ j, A k j * x j
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- Every such finite-dimensional linear map is continuous. -/
def linearPathCLM (A : K → J → ℝ) : (J → ℝ) →L[ℝ] EuclideanSpace ℝ K :=
  ⟨linearPathLinearMap A, (linearPathLinearMap A).continuous_of_finiteDimensional⟩

@[simp] lemma linearPathCLM_apply (A : K → J → ℝ) (x : J → ℝ) (k : K) :
    linearPathCLM A x k = ∑ j, A k j * x j := rfl

lemma hasGaussianLaw_linearPath {u : J → Ω → ℝ}
    (hu : IndependentStandardGaussians u P) (A : K → J → ℝ) :
    HasEuclideanGaussianLaw (linearPath A u) P := by
  unfold HasEuclideanGaussianLaw
  apply (hu.jointlyGaussian.map_fun (linearPathCLM A)).congr
  exact Filter.Eventually.of_forall fun ω ↦ by
    ext k
    rfl

lemma integral_linearPath {u : J → Ω → ℝ}
    (hu : IndependentStandardGaussians u P) (A : K → J → ℝ) (k : K) :
    ∫ ω, linearPath A u ω k ∂P = 0 := by
  letI := hu.indep.isProbabilityMeasure
  rw [show (fun ω ↦ linearPath A u ω k) = fun ω ↦ ∑ j, A k j * u j ω by rfl]
  rw [integral_finsetSum _ (fun j _ ↦ (hu.hasGaussianLaw j).integrable.const_mul (A k j))]
  simp [integral_const_mul, hu.integral_eq_zero]

lemma covariance_linearPath {u : J → Ω → ℝ}
    (hu : IndependentStandardGaussians u P) (A B : K → J → ℝ) (s t : K) :
    cov[(fun ω ↦ linearPath A u ω s), (fun ω ↦ linearPath B u ω t); P]
      = ∑ j, A s j * B t j := by
  letI := hu.indep.isProbabilityMeasure
  change cov[(fun ω ↦ ∑ j, A s j * u j ω), (fun ω ↦ ∑ j, B t j * u j ω); P]
      = _
  rw [covariance_fun_sum_fun_sum]
  · classical
    simp_rw [covariance_const_mul_left, covariance_const_mul_right,
      hu.covariance_eq_ite]
    simp only [mul_ite, mul_one, mul_zero]
    simp
  · exact fun j ↦ (hu.memLp_two j).const_mul _
  · exact fun j ↦ (hu.memLp_two j).const_mul _

end LinearImages

section CircularPaths

variable {n : ℕ}

/-- The two independent real Gaussian families, viewed as one family. -/
def doubledFamily (g h : Fin n → Ω → ℝ) : Fin n ⊕ Fin n → Ω → ℝ :=
  Sum.elim g h

/-- Real coefficient row of the circularized complex prefix at time `t`. -/
def realRow (c : Fin n → ℂ) (t : Fin (n + 1)) : Fin n ⊕ Fin n → ℝ
  | Sum.inl i => if i.val < t.val then (c i).re else 0
  | Sum.inr i => if i.val < t.val then -(c i).im else 0

/-- Imaginary coefficient row of the circularized complex prefix at time `t`. -/
def imagRow (c : Fin n → ℂ) (t : Fin (n + 1)) : Fin n ⊕ Fin n → ℝ
  | Sum.inl i => if i.val < t.val then (c i).im else 0
  | Sum.inr i => if i.val < t.val then (c i).re else 0

/-- The full real-part prefix path. -/
def realPath (c : Fin n → ℂ) (g h : Fin n → Ω → ℝ) :
    Ω → EuclideanSpace ℝ (Fin (n + 1)) :=
  linearPath (realRow c) (doubledFamily g h)

/-- The full imaginary-part prefix path. -/
def imagPath (c : Fin n → ℂ) (g h : Fin n → Ω → ℝ) :
    Ω → EuclideanSpace ℝ (Fin (n + 1)) :=
  linearPath (imagRow c) (doubledFamily g h)

/-- The circularized complex Gaussian prefix path. -/
def complexPath (c : Fin n → ℂ) (g h : Fin n → Ω → ℝ)
    (ω : Ω) (t : Fin (n + 1)) : ℂ :=
  ∑ i with i.val < t.val,
    ((g i ω : ℂ) * c i + (h i ω : ℂ) * Complex.I * c i)

lemma complexPath_re (c : Fin n → ℂ) (g h : Fin n → Ω → ℝ) (ω : Ω)
    (t : Fin (n + 1)) :
    (complexPath c g h ω t).re = realPath c g h ω t := by
  classical
  simp [complexPath, realPath, linearPath, realRow, doubledFamily,
    Fintype.sum_sum_type, apply_ite, Finset.sum_ite]
  rw [Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    ring
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring

lemma complexPath_im (c : Fin n → ℂ) (g h : Fin n → Ω → ℝ) (ω : Ω)
    (t : Fin (n + 1)) :
    (complexPath c g h ω t).im = imagPath c g h ω t := by
  classical
  simp [complexPath, imagPath, linearPath, imagRow, doubledFamily,
    Fintype.sum_sum_type, apply_ite, Finset.sum_ite]
  rw [Finset.sum_add_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring

/-- The real and imaginary coefficient rows have zero dot product, at arbitrary prefix times. -/
lemma realRow_dot_imagRow (c : Fin n → ℂ) (s t : Fin (n + 1)) :
    ∑ j : Fin n ⊕ Fin n, realRow c s j * imagRow c t j = 0 := by
  classical
  rw [Fintype.sum_sum_type]
  simp only [realRow, imagRow]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i _
  split_ifs <;> ring

/-- The two coefficient systems have the same Gram matrix. -/
lemma realRow_dot_realRow_eq_imagRow (c : Fin n → ℂ) (s t : Fin (n + 1)) :
    (∑ j : Fin n ⊕ Fin n, realRow c s j * realRow c t j) =
      ∑ j : Fin n ⊕ Fin n, imagRow c s j * imagRow c t j := by
  classical
  simp only [Fintype.sum_sum_type, realRow, imagRow]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> ring

/-- Both real/imaginary path vectors, concatenated into one Euclidean vector. -/
def bothRow (c : Fin n → ℂ) (p : Bool × Fin (n + 1)) : Fin n ⊕ Fin n → ℝ :=
  if p.1 then imagRow c p.2 else realRow c p.2

def bothPath (c : Fin n → ℂ) (g h : Fin n → Ω → ℝ) :
    Ω → EuclideanSpace ℝ (Bool × Fin (n + 1)) :=
  linearPath (bothRow c) (doubledFamily g h)

/-- The full real/imaginary path vector is jointly centered Gaussian. -/
lemma bothPath_hasGaussianLaw (c : Fin n → ℂ) (g h : Fin n → Ω → ℝ)
    (hu : IndependentStandardGaussians (doubledFamily g h) P) :
    HasEuclideanGaussianLaw (bothPath c g h) P :=
  hasGaussianLaw_linearPath hu (bothRow c)

lemma integral_realPath (c : Fin n → ℂ) (g h : Fin n → Ω → ℝ)
    (hu : IndependentStandardGaussians (doubledFamily g h) P) (t : Fin (n + 1)) :
    ∫ ω, realPath c g h ω t ∂P = 0 :=
  integral_linearPath hu (realRow c) t

lemma integral_imagPath (c : Fin n → ℂ) (g h : Fin n → Ω → ℝ)
    (hu : IndependentStandardGaussians (doubledFamily g h) P) (t : Fin (n + 1)) :
    ∫ ω, imagPath c g h ω t ∂P = 0 :=
  integral_linearPath hu (imagRow c) t

/-- All real/imaginary cross-covariances vanish. -/
lemma covariance_realPath_imagPath (c : Fin n → ℂ) (g h : Fin n → Ω → ℝ)
    (hu : IndependentStandardGaussians (doubledFamily g h) P) (s t : Fin (n + 1)) :
    cov[(fun ω ↦ realPath c g h ω s), (fun ω ↦ imagPath c g h ω t); P] = 0 := by
  unfold realPath imagPath
  rw [covariance_linearPath hu (realRow c) (imagRow c) s t,
    realRow_dot_imagRow]

/-- The real and imaginary path vectors have identical covariance matrices. -/
lemma covariance_realPath_eq_imagPath (c : Fin n → ℂ) (g h : Fin n → Ω → ℝ)
    (hu : IndependentStandardGaussians (doubledFamily g h) P) (s t : Fin (n + 1)) :
    cov[(fun ω ↦ realPath c g h ω s), (fun ω ↦ realPath c g h ω t); P] =
      cov[(fun ω ↦ imagPath c g h ω s), (fun ω ↦ imagPath c g h ω t); P] := by
  unfold realPath imagPath
  rw [covariance_linearPath hu (realRow c) (realRow c) s t,
    covariance_linearPath hu (imagRow c) (imagRow c) s t,
    realRow_dot_realRow_eq_imagRow]

/-- The real and imaginary full path vectors have exactly the same probability law. -/
lemma map_realPath_eq_map_imagPath (c : Fin n → ℂ) (g h : Fin n → Ω → ℝ)
    (hu : IndependentStandardGaussians (doubledFamily g h) P) :
    Measure.map (realPath c g h) P = Measure.map (imagPath c g h) P := by
  have hR := hasGaussianLaw_linearPath hu (realRow c)
  have hI := hasGaussianLaw_linearPath hu (imagRow c)
  unfold HasEuclideanGaussianLaw at hR hI
  change Measure.map (linearPath (realRow c) (doubledFamily g h)) P =
    Measure.map (linearPath (imagRow c) (doubledFamily g h)) P
  letI := hu.indep.isProbabilityMeasure
  letI : IsGaussian (Measure.map (linearPath (realRow c) (doubledFamily g h)) P) :=
    hR.isGaussian_map
  letI : IsGaussian (Measure.map (linearPath (imagRow c) (doubledFamily g h)) P) :=
    hI.isGaussian_map
  apply IsGaussian.ext
  · rw [integral_map hR.aemeasurable IsGaussian.integrable_id.aestronglyMeasurable,
      integral_map hI.aemeasurable IsGaussian.integrable_id.aestronglyMeasurable]
    ext t
    simp only [id_eq]
    rw [eval_integral_piLp
        (fun s ↦ (hR.memLp_two.eval_piLp s).integrable (by norm_num)) t,
      eval_integral_piLp
        (fun s ↦ (hI.memLp_two.eval_piLp s).integrable (by norm_num)) t]
    exact (integral_linearPath hu (realRow c) t).trans
      (integral_linearPath hu (imagRow c) t).symm
  · ext x y
    unfold linearPath
    have hmR (t : Fin (n + 1)) :
        MemLp (fun ω ↦ ∑ j, realRow c t j * doubledFamily g h j ω) 2 P :=
      memLp_finsetSum Finset.univ fun j _ ↦ (hu.memLp_two j).const_mul _
    have hmI (t : Fin (n + 1)) :
        MemLp (fun ω ↦ ∑ j, imagRow c t j * doubledFamily g h j ω) 2 P :=
      memLp_finsetSum Finset.univ fun j _ ↦ (hu.memLp_two j).const_mul _
    rw [covarianceBilin_apply_pi hmR, covarianceBilin_apply_pi hmI]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    have hc := covariance_realPath_eq_imagPath c g h hu s t
    unfold realPath imagPath linearPath at hc
    exact congrArg (fun z ↦ x s * y t * z) hc

lemma aemeasurable_realPath (c : Fin n → ℂ) (g h : Fin n → Ω → ℝ)
    (hu : IndependentStandardGaussians (doubledFamily g h) P) :
    AEMeasurable (realPath c g h) P := by
  have hR := hasGaussianLaw_linearPath hu (realRow c)
  unfold HasEuclideanGaussianLaw at hR
  exact hR.aemeasurable

lemma aemeasurable_imagPath (c : Fin n → ℂ) (g h : Fin n → Ω → ℝ)
    (hu : IndependentStandardGaussians (doubledFamily g h) P) :
    AEMeasurable (imagPath c g h) P := by
  have hI := hasGaussianLaw_linearPath hu (imagRow c)
  unfold HasEuclideanGaussianLaw at hI
  exact hI.aemeasurable

/-- A linear map that displays the two paths as a Boolean-indexed family of ordinary coordinate
functions.  It is used solely to apply Mathlib's covariance-implies-independence theorem. -/
def pathFamilyLinearMap (c : Fin n → ℂ) :
    ((Fin n ⊕ Fin n) → ℝ) →ₗ[ℝ] (Bool → Fin (n + 1) → ℝ) where
  toFun x b t := ∑ j, (if b then imagRow c t j else realRow c t j) * x j
  map_add' x y := by
    ext b t
    simp_rw [Pi.add_apply, mul_add]
    exact Finset.sum_add_distrib
  map_smul' r x := by
    ext b t
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

def pathFamilyCLM (c : Fin n → ℂ) :
    ((Fin n ⊕ Fin n) → ℝ) →L[ℝ] (Bool → Fin (n + 1) → ℝ) :=
  ⟨pathFamilyLinearMap c, (pathFamilyLinearMap c).continuous_of_finiteDimensional⟩

/-- The entire real path vector and entire imaginary path vector are independent. -/
lemma indepFun_realPath_imagPath (c : Fin n → ℂ) (g h : Fin n → Ω → ℝ)
    (hu : IndependentStandardGaussians (doubledFamily g h) P) :
    IndepFun (realPath c g h) (imagPath c g h) P := by
  let X : Bool → Fin (n + 1) → Ω → ℝ := fun b t ω ↦
    if b then imagPath c g h ω t else realPath c g h ω t
  have hX : HasGaussianLaw (fun ω b t ↦ X b t ω) P := by
    apply (hu.jointlyGaussian.map_fun (pathFamilyCLM c)).congr
    exact Filter.Eventually.of_forall fun ω ↦ by
      ext b t
      cases b <;> rfl
  have h_indep : iIndepFun (fun b ω t ↦ X b t ω) P :=
    hX.iIndepFun_of_covariance_eval fun b₁ b₂ hb t₁ t₂ ↦ by
      cases b₁ <;> cases b₂
      · exact (hb rfl).elim
      · exact covariance_realPath_imagPath c g h hu t₁ t₂
      · rw [covariance_comm]
        exact covariance_realPath_imagPath c g h hu t₂ t₁
      · exact (hb rfl).elim
  have h_plain : IndepFun
      (fun ω t ↦ realPath c g h ω t) (fun ω t ↦ imagPath c g h ω t) P := by
    simpa [X] using h_indep.indepFun (show false ≠ true by decide)
  simpa [Function.comp_def] using h_plain.comp
    (WithLp.measurable_toLp 2 (Fin (n + 1) → ℝ))
    (WithLp.measurable_toLp 2 (Fin (n + 1) → ℝ))

end CircularPaths

section EventFactorization

variable {n : ℕ}

/-- A scalar path tube together with a measurable endpoint constraint. -/
def pathEndpointSet (R : ℝ) (S : Set ℝ) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  {x | (∀ t, ‖x t‖ ≤ R) ∧ x (Fin.last n) ∈ S}

lemma measurableSet_pathEndpointSet (R : ℝ) {S : Set ℝ} (hS : MeasurableSet S) :
    MeasurableSet (pathEndpointSet (n := n) R S) := by
  have hpath : MeasurableSet {x : EuclideanSpace ℝ (Fin (n + 1)) | ∀ t, ‖x t‖ ≤ R} := by
    rw [show {x : EuclideanSpace ℝ (Fin (n + 1)) | ∀ t, ‖x t‖ ≤ R} =
        ⋂ t, {x | ‖x t‖ ≤ R} by ext x; simp]
    exact MeasurableSet.iInter fun t ↦
      measurableSet_le ((PiLp.continuous_apply 2 (fun _ : Fin (n + 1) ↦ ℝ) t).measurable.norm)
        measurable_const
  exact hpath.inter (hS.preimage
    (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n)).measurable)

/-- Independence factors every measurable rectangular path event. -/
lemma measure_realPath_mem_inter_imagPath_mem
    (c : Fin n → ℂ) (g h : Fin n → Ω → ℝ)
    (hu : IndependentStandardGaussians (doubledFamily g h) P)
    (A B : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    P ({ω | realPath c g h ω ∈ A} ∩ {ω | imagPath c g h ω ∈ B}) =
      P {ω | realPath c g h ω ∈ A} * P {ω | imagPath c g h ω ∈ B} := by
  simpa only [Set.preimage, Set.mem_ofPred_eq] using
    (indepFun_realPath_imagPath c g h hu).measure_inter_preimage_eq_mul A B hA hB

/-- Because the two path vectors have the same law, applying the same measurable path+endpoint
event to both coordinates gives the square of the corresponding scalar probability. -/
lemma measure_same_path_event_eq_sq
    (c : Fin n → ℂ) (g h : Fin n → Ω → ℝ)
    (hu : IndependentStandardGaussians (doubledFamily g h) P)
    (A : Set (EuclideanSpace ℝ (Fin (n + 1)))) (hA : MeasurableSet A) :
    P ({ω | realPath c g h ω ∈ A} ∩ {ω | imagPath c g h ω ∈ A}) =
      P {ω | realPath c g h ω ∈ A} ^ 2 := by
  rw [measure_realPath_mem_inter_imagPath_mem c g h hu A A hA hA, pow_two]
  congr 1
  calc
    P {ω | imagPath c g h ω ∈ A} = (Measure.map (imagPath c g h) P) A :=
      (Measure.map_apply_of_aemeasurable (aemeasurable_imagPath c g h hu) hA).symm
    _ = (Measure.map (realPath c g h) P) A := by
      rw [map_realPath_eq_map_imagPath c g h hu]
    _ = P {ω | realPath c g h ω ∈ A} :=
      Measure.map_apply_of_aemeasurable (aemeasurable_realPath c g h hu) hA

/-- The rectangular circularized path-tube plus endpoint event is the square of its scalar
counterpart. -/
lemma measure_pathEndpoint_event_eq_sq
    (c : Fin n → ℂ) (g h : Fin n → Ω → ℝ)
    (hu : IndependentStandardGaussians (doubledFamily g h) P)
    (R : ℝ) (S : Set ℝ) (hS : MeasurableSet S) :
    P ({ω | realPath c g h ω ∈ pathEndpointSet R S} ∩
        {ω | imagPath c g h ω ∈ pathEndpointSet R S}) =
      P {ω | realPath c g h ω ∈ pathEndpointSet R S} ^ 2 :=
  measure_same_path_event_eq_sq c g h hu (pathEndpointSet R S)
    (measurableSet_pathEndpointSet R hS)

end EventFactorization

end GaussianCircularization


namespace GaussianTubeGlue

noncomputable section

def pathDim (n : ℕ) : ℕ := (n + 1) + (n + 1)

def pathIndexEquiv (n : ℕ) : Fin (n + 1) ⊕ Fin (n + 1) ≃ Fin (pathDim n) :=
  finSumFinEquiv

def encodedPathCoordLM (n : ℕ) (t : Fin (n + 1)) :
    (Fin (pathDim n) → ℝ) →ₗ[ℝ] ℂ where
  toFun z := ⟨z (pathIndexEquiv n (Sum.inl t)), z (pathIndexEquiv n (Sum.inr t))⟩
  map_add' x y := by apply Complex.ext <;> simp
  map_smul' r x := by apply Complex.ext <;> simp

def encodedPathCoordCLM (n : ℕ) (t : Fin (n + 1)) :
    (Fin (pathDim n) → ℝ) →L[ℝ] ℂ :=
  ⟨encodedPathCoordLM n t, (encodedPathCoordLM n t).continuous_of_finiteDimensional⟩

def encodedTubeSet (n : ℕ) (R r : ℝ) : Set (Fin (pathDim n) → ℝ) :=
  {z | (∀ t, ‖encodedPathCoordLM n t z‖ ≤ R) ∧
    ‖encodedPathCoordLM n (Fin.last n) z‖ ≤ r}

lemma measurableSet_encodedTubeSet (n : ℕ) (R r : ℝ) :
    MeasurableSet (encodedTubeSet n R r) := by
  have hp : MeasurableSet {z : Fin (pathDim n) → ℝ |
      ∀ t, ‖encodedPathCoordLM n t z‖ ≤ R} := by
    rw [show {z : Fin (pathDim n) → ℝ |
        ∀ t, ‖encodedPathCoordLM n t z‖ ≤ R} =
        ⋂ t, {z | ‖encodedPathCoordLM n t z‖ ≤ R} by ext z; simp]
    exact MeasurableSet.iInter fun t => measurableSet_le
      ((encodedPathCoordCLM n t).measurable.norm) measurable_const
  exact hp.inter (measurableSet_le
    ((encodedPathCoordCLM n (Fin.last n)).measurable.norm) measurable_const)

lemma convex_encodedTubeSet (n : ℕ) (R r : ℝ) :
    Convex ℝ (encodedTubeSet n R r) := by
  have hp : Convex ℝ {z : Fin (pathDim n) → ℝ |
      ∀ t, ‖encodedPathCoordLM n t z‖ ≤ R} := by
    rw [show {z : Fin (pathDim n) → ℝ |
        ∀ t, ‖encodedPathCoordLM n t z‖ ≤ R} =
        ⋂ t, (encodedPathCoordLM n t) ⁻¹' Metric.closedBall 0 R by
      ext z
      simp [Metric.mem_closedBall]]
    exact convex_iInter fun t =>
      (convex_closedBall (0 : ℂ) R).linear_preimage (encodedPathCoordLM n t)
  have he : Convex ℝ {z : Fin (pathDim n) → ℝ |
      ‖encodedPathCoordLM n (Fin.last n) z‖ ≤ r} := by
    rw [show {z : Fin (pathDim n) → ℝ |
        ‖encodedPathCoordLM n (Fin.last n) z‖ ≤ r} =
        (encodedPathCoordLM n (Fin.last n)) ⁻¹' Metric.closedBall 0 r by
      ext z
      simp [Metric.mem_closedBall]]
    exact (convex_closedBall (0 : ℂ) r).linear_preimage
      (encodedPathCoordLM n (Fin.last n))
  exact hp.inter he

lemma neg_mem_encodedTubeSet_iff (n : ℕ) (R r : ℝ) (z : Fin (pathDim n) → ℝ) :
    -z ∈ encodedTubeSet n R r ↔ z ∈ encodedTubeSet n R r := by
  simp only [encodedTubeSet, Set.mem_setOf_eq, map_neg, norm_neg]

def originalEncodedPathLM {n : ℕ} (c : Fin n → ℂ) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin (pathDim n) → ℝ) where
  toFun x q :=
    match (pathIndexEquiv n).symm q with
    | Sum.inl t => ∑ i with i.val < t.val, x i * (c i).re
    | Sum.inr t => ∑ i with i.val < t.val, x i * (c i).im
  map_add' x y := by
    ext q
    generalize hq : (pathIndexEquiv n).symm q = s
    cases s with
    | inl t =>
        simp [hq, add_mul, Finset.sum_add_distrib]
    | inr t =>
        simp [hq, add_mul, Finset.sum_add_distrib]
  map_smul' a x := by
    ext q
    generalize hq : (pathIndexEquiv n).symm q = s
    cases s with
    | inl t =>
        simp only [hq, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
    | inr t =>
        simp only [hq, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring

def originalEncodedPathCLM {n : ℕ} (c : Fin n → ℂ) :
    (Fin n → ℝ) →L[ℝ] (Fin (pathDim n) → ℝ) :=
  ⟨originalEncodedPathLM c, (originalEncodedPathLM c).continuous_of_finiteDimensional⟩

lemma encodedPathCoord_originalEncodedPathLM {n : ℕ} (c : Fin n → ℂ)
    (x : Fin n → ℝ) (t : Fin (n + 1)) :
    encodedPathCoordLM n t (originalEncodedPathLM c x) =
      ∑ i with i.val < t.val, (x i : ℂ) * c i := by
  apply Complex.ext
  · change originalEncodedPathLM c x (pathIndexEquiv n (Sum.inl t)) = _
    unfold originalEncodedPathLM
    change (match (pathIndexEquiv n).symm (pathIndexEquiv n (Sum.inl t)) with
      | Sum.inl s => _
      | Sum.inr s => _) = _
    rw [show (pathIndexEquiv n).symm (pathIndexEquiv n (Sum.inl t)) = Sum.inl t
      from (pathIndexEquiv n).symm_apply_apply _]
    simp [Complex.mul_re]
  · change originalEncodedPathLM c x (pathIndexEquiv n (Sum.inr t)) = _
    unfold originalEncodedPathLM
    change (match (pathIndexEquiv n).symm (pathIndexEquiv n (Sum.inr t)) with
      | Sum.inl s => _
      | Sum.inr s => _) = _
    rw [show (pathIndexEquiv n).symm (pathIndexEquiv n (Sum.inr t)) = Sum.inr t
      from (pathIndexEquiv n).symm_apply_apply _]
    simp [Complex.mul_im]

def standardGaussianProduct (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ : Fin n => gaussianReal 0 1

instance (n : ℕ) : IsProbabilityMeasure (standardGaussianProduct n) := by
  unfold standardGaussianProduct
  infer_instance

def canonicalOriginalEvent {n : ℕ} (c : Fin n → ℂ) (R r : ℝ) :
    Set (Fin n → ℝ) :=
  {x | originalEncodedPathLM c x ∈ encodedTubeSet n R r}

def canonicalCircularEvent {n : ℕ} (c : Fin n → ℂ) (R r : ℝ) :
    Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {xy | originalEncodedPathLM c xy.1 +
      originalEncodedPathLM (fun i => Complex.I * c i) xy.2 ∈ encodedTubeSet n R r}

lemma measurableSet_canonicalOriginalEvent {n : ℕ} (c : Fin n → ℂ) (R r : ℝ) :
    MeasurableSet (canonicalOriginalEvent c R r) :=
  (measurableSet_encodedTubeSet n R r).preimage (originalEncodedPathCLM c).measurable

lemma measurableSet_canonicalCircularEvent {n : ℕ} (c : Fin n → ℂ) (R r : ℝ) :
    MeasurableSet (canonicalCircularEvent c R r) := by
  exact (measurableSet_encodedTubeSet n R r).preimage
    (((originalEncodedPathCLM c).measurable.comp measurable_fst).add
      ((originalEncodedPathCLM (fun i => Complex.I * c i)).measurable.comp measurable_snd))

theorem canonical_circularEvent_le_originalEvent {n : ℕ} (c : Fin n → ℂ)
    (R r : ℝ) :
    (standardGaussianProduct n).prod (standardGaussianProduct n)
        (canonicalCircularEvent c R r) ≤
      standardGaussianProduct n (canonicalOriginalEvent c R r) := by
  rw [Measure.prod_apply_symm (measurableSet_canonicalCircularEvent c R r)]
  calc
    (∫⁻ y, standardGaussianProduct n
        ((fun x => (x, y)) ⁻¹' canonicalCircularEvent c R r)
        ∂standardGaussianProduct n) ≤
      ∫⁻ _y, standardGaussianProduct n (canonicalOriginalEvent c R r)
        ∂standardGaussianProduct n := by
      apply lintegral_mono
      intro y
      have hA := Anderson.gaussianProductMeasure_linear_preimage_sub_le_centered
        (originalEncodedPathLM c) (originalEncodedPathCLM c).measurable
        (encodedTubeSet n R r) (measurableSet_encodedTubeSet n R r)
        (convex_encodedTubeSet n R r) (neg_mem_encodedTubeSet_iff n R r)
        (-(originalEncodedPathLM (fun i => Complex.I * c i) y))
      change standardGaussianProduct n
          {x | originalEncodedPathLM c x -
            (-(originalEncodedPathLM (fun i => Complex.I * c i) y)) ∈
              encodedTubeSet n R r} ≤
            standardGaussianProduct n
              {x | originalEncodedPathLM c x ∈ encodedTubeSet n R r} at hA
      simpa only [canonicalCircularEvent, canonicalOriginalEvent, Set.preimage_setOf_eq,
        sub_neg_eq_add] using hA
    _ = standardGaussianProduct n (canonicalOriginalEvent c R r) := by simp

def originalComplexPath {Ω : Type*} {n : ℕ} (c : Fin n → ℂ)
    (g : Fin n → Ω → ℝ) (ω : Ω) (t : Fin (n + 1)) : ℂ :=
  ∑ i with i.val < t.val, (g i ω : ℂ) * c i

def complexTubeEvent {Ω : Type*} {n : ℕ} (c : Fin n → ℂ)
    (g : Fin n → Ω → ℝ) (R r : ℝ) : Set Ω :=
  {ω | (∀ t, ‖originalComplexPath c g ω t‖ ≤ R) ∧
    ‖originalComplexPath c g ω (Fin.last n)‖ ≤ r}

def circularComplexTubeEvent {Ω : Type*} {n : ℕ} (c : Fin n → ℂ)
    (g h : Fin n → Ω → ℝ) (R r : ℝ) : Set Ω :=
  {ω | (∀ t, ‖GaussianCircularization.complexPath c g h ω t‖ ≤ R) ∧
    ‖GaussianCircularization.complexPath c g h ω (Fin.last n)‖ ≤ r}

lemma encodedPathCoord_original_g {Ω : Type*} {n : ℕ} (c : Fin n → ℂ)
    (g : Fin n → Ω → ℝ) (ω : Ω) (t : Fin (n + 1)) :
    encodedPathCoordLM n t (originalEncodedPathLM c (fun i => g i ω)) =
      originalComplexPath c g ω t := by
  exact encodedPathCoord_originalEncodedPathLM c (fun i => g i ω) t

lemma encodedPathCoord_circular {Ω : Type*} {n : ℕ} (c : Fin n → ℂ)
    (g h : Fin n → Ω → ℝ) (ω : Ω) (t : Fin (n + 1)) :
    encodedPathCoordLM n t
        (originalEncodedPathLM c (fun i => g i ω) +
          originalEncodedPathLM (fun i => Complex.I * c i) (fun i => h i ω)) =
      GaussianCircularization.complexPath c g h ω t := by
  rw [map_add, encodedPathCoord_originalEncodedPathLM,
    encodedPathCoord_originalEncodedPathLM]
  classical
  simp only [GaussianCircularization.complexPath, Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma complexTubeEvent_eq_preimage {Ω : Type*} {n : ℕ} (c : Fin n → ℂ)
    (g : Fin n → Ω → ℝ) (R r : ℝ) :
    complexTubeEvent c g R r =
      (fun ω i => g i ω) ⁻¹' canonicalOriginalEvent c R r := by
  ext ω
  simp only [complexTubeEvent, canonicalOriginalEvent, encodedTubeSet,
    Set.mem_setOf_eq, Set.mem_preimage]
  simp_rw [encodedPathCoord_original_g]

lemma circularComplexTubeEvent_eq_preimage {Ω : Type*} {n : ℕ} (c : Fin n → ℂ)
    (g h : Fin n → Ω → ℝ) (R r : ℝ) :
    circularComplexTubeEvent c g h R r =
      (fun ω => (fun i => g i ω, fun i => h i ω)) ⁻¹'
        canonicalCircularEvent c R r := by
  ext ω
  simp only [circularComplexTubeEvent, canonicalCircularEvent, encodedTubeSet,
    Set.mem_setOf_eq, Set.mem_preimage]
  simp_rw [encodedPathCoord_circular]

theorem circularComplexTubeEvent_le_originalComplexTubeEvent
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    (c : Fin n → ℂ) (g h : Fin n → Ω → ℝ)
    (hu : GaussianCircularization.IndependentStandardGaussians
      (GaussianCircularization.doubledFamily g h) P)
    (R r : ℝ) :
    P (circularComplexTubeEvent c g h R r) ≤ P (complexTubeEvent c g R r) := by
  letI : IsProbabilityMeasure P := hu.indep.isProbabilityMeasure
  let G : Ω → Fin n → ℝ := fun ω i => g i ω
  let H : Ω → Fin n → ℝ := fun ω i => h i ω
  have hGind : iIndepFun g P :=
    by
      simpa [GaussianCircularization.doubledFamily] using
        (ProbabilityTheory.iIndepFun.precomp (f :=
          GaussianCircularization.doubledFamily g h) Sum.inl_injective hu.indep)
  have hHind : iIndepFun h P :=
    by
      simpa [GaussianCircularization.doubledFamily] using
        (ProbabilityTheory.iIndepFun.precomp (f :=
          GaussianCircularization.doubledFamily g h) Sum.inr_injective hu.indep)
  have hGlaw : HasLaw G (standardGaussianProduct n) P := by
    exact iIndepFun.hasLaw_pi (fun i => hu.law (Sum.inl i)) hGind
  have hHlaw : HasLaw H (standardGaussianProduct n) P := by
    exact iIndepFun.hasLaw_pi (fun i => hu.law (Sum.inr i)) hHind
  let projG : ((Fin n ⊕ Fin n) → ℝ) →L[ℝ] (Fin n → ℝ) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Sum.inl i)
  let projH : ((Fin n ⊕ Fin n) → ℝ) →L[ℝ] (Fin n → ℝ) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Sum.inr i)
  have hpairGaussian : HasGaussianLaw (fun ω => (G ω, H ω)) P := by
    have hm := hu.jointlyGaussian.map_fun (projG.prod projH)
    apply hm.congr
    exact Filter.Eventually.of_forall fun ω => by
      ext i <;> rfl
  have hGH : IndepFun G H P := by
    apply hpairGaussian.indepFun_of_covariance_eval
    intro i j
    simpa [G, H, GaussianCircularization.doubledFamily] using
      hu.covariance_eq_ite (Sum.inl i) (Sum.inr j)
  have hpairMap : Measure.map (fun ω => (G ω, H ω)) P =
      (standardGaussianProduct n).prod (standardGaussianProduct n) := by
    rw [hGH.map_prod_eq_prod_map_map hGlaw.aemeasurable hHlaw.aemeasurable,
      hGlaw.map_eq, hHlaw.map_eq]
  rw [circularComplexTubeEvent_eq_preimage c g h R r,
    complexTubeEvent_eq_preimage c g R r]
  calc
    P ((fun ω => (G ω, H ω)) ⁻¹' canonicalCircularEvent c R r) =
        Measure.map (fun ω => (G ω, H ω)) P (canonicalCircularEvent c R r) :=
      (Measure.map_apply_of_aemeasurable
        (hGlaw.aemeasurable.prodMk hHlaw.aemeasurable)
        (measurableSet_canonicalCircularEvent c R r)).symm
    _ = (standardGaussianProduct n).prod (standardGaussianProduct n)
        (canonicalCircularEvent c R r) := by rw [hpairMap]
    _ ≤ standardGaussianProduct n (canonicalOriginalEvent c R r) :=
      canonical_circularEvent_le_originalEvent c R r
    _ = Measure.map G P (canonicalOriginalEvent c R r) := by rw [hGlaw.map_eq]
    _ = P (G ⁻¹' canonicalOriginalEvent c R r) :=
      Measure.map_apply_of_aemeasurable hGlaw.aemeasurable
        (measurableSet_canonicalOriginalEvent c R r)

theorem original_complex_tube_lower_sq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    (c : Fin n → ℂ) (g h : Fin n → Ω → ℝ)
    (hu : GaussianCircularization.IndependentStandardGaussians
      (GaussianCircularization.doubledFamily g h) P)
    (R r : ℝ) :
    P {ω | GaussianCircularization.realPath c g h ω ∈
        GaussianCircularization.pathEndpointSet R (Set.Icc (-r) r)} ^ 2 ≤
      P (complexTubeEvent c g (2 * R) (2 * r)) := by
  rw [← GaussianCircularization.measure_pathEndpoint_event_eq_sq c g h hu R
    (Set.Icc (-r) r) measurableSet_Icc]
  apply le_trans (measure_mono ?_)
    (circularComplexTubeEvent_le_originalComplexTubeEvent c g h hu (2 * R) (2 * r))
  intro ω hω
  rcases hω with ⟨hRe, hIm⟩
  change (∀ t, ‖GaussianCircularization.realPath c g h ω t‖ ≤ R) ∧
      GaussianCircularization.realPath c g h ω (Fin.last n) ∈ Set.Icc (-r) r at hRe
  change (∀ t, ‖GaussianCircularization.imagPath c g h ω t‖ ≤ R) ∧
      GaussianCircularization.imagPath c g h ω (Fin.last n) ∈ Set.Icc (-r) r at hIm
  change (∀ t, ‖GaussianCircularization.complexPath c g h ω t‖ ≤ 2 * R) ∧
    ‖GaussianCircularization.complexPath c g h ω (Fin.last n)‖ ≤ 2 * r
  constructor
  · intro t
    calc
      ‖GaussianCircularization.complexPath c g h ω t‖ ≤
          |(GaussianCircularization.complexPath c g h ω t).re| +
            |(GaussianCircularization.complexPath c g h ω t).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = ‖GaussianCircularization.realPath c g h ω t‖ +
          ‖GaussianCircularization.imagPath c g h ω t‖ := by
        rw [GaussianCircularization.complexPath_re,
          GaussianCircularization.complexPath_im]
        simp only [Real.norm_eq_abs]
      _ ≤ R + R := add_le_add (hRe.1 t) (hIm.1 t)
      _ = 2 * R := by ring
  · calc
      ‖GaussianCircularization.complexPath c g h ω (Fin.last n)‖ ≤
          |(GaussianCircularization.complexPath c g h ω (Fin.last n)).re| +
            |(GaussianCircularization.complexPath c g h ω (Fin.last n)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = |GaussianCircularization.realPath c g h ω (Fin.last n)| +
          |GaussianCircularization.imagPath c g h ω (Fin.last n)| := by
        rw [GaussianCircularization.complexPath_re,
          GaussianCircularization.complexPath_im]
      _ ≤ r + r := add_le_add (abs_le.mpr hRe.2) (abs_le.mpr hIm.2)
      _ = 2 * r := by ring

end

end GaussianTubeGlue

/-! ## Gaussian tube-to-cutoff bridge -/

namespace GaussianCutoffBridge

noncomputable section

open SmoothCutoffC4 CutoffLindebergBridge

lemma flatBlockIncrementDirection_eq_flatDirection
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) (z : ℂ) :
    OnePointLindeberg.flatBlockIncrementDirection a hN0 k z =
      FlatVectorAPI.flatDirection a z hN0 k := by
  funext i r
  by_cases hir : uniformBlockOfOffset hN0 k i = r
  · simp [OnePointLindeberg.flatBlockIncrementDirection,
      FlatVectorAPI.flatDirection, hir, OnePointLindeberg.flatPhaseCoefficient,
      OnePointLindeberg.flatScaleIndex, FlatVectorAPI.scaleCoefficient]
  · have hri : r ≠ uniformBlockOfOffset hN0 k i :=
      fun h ↦ hir h.symm
    simp [OnePointLindeberg.flatBlockIncrementDirection,
      FlatVectorAPI.flatDirection, hir, hri]

lemma endpoint_flat_linearCombination_eq_originalComplexPath
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) (z : ℂ)
    (x : Fin (scale N0 (k + 1) - scale N0 k) → ℝ) :
    (∑ r, CutoffLindebergBridge.NormedLindeberg.linearCombination
        (OnePointLindeberg.flatBlockIncrementDirection a hN0 k z) x r) =
      GaussianTubeGlue.originalComplexPath
        (OnePointLindeberg.flatPhaseCoefficient a N0 k z) (fun i x ↦ x i) x
        (Fin.last (scale N0 (k + 1) - scale N0 k)) := by
  rw [flatBlockIncrementDirection_eq_flatDirection]
  rw [FlatVectorAPI.sum_linearCombination_flatDirection]
  simp [GaussianTubeGlue.originalComplexPath, Fin.last,
    OnePointLindeberg.flatPhaseCoefficient, OnePointLindeberg.flatScaleIndex,
    FlatVectorAPI.scaleCoefficient, mul_assoc]

lemma prefix_flat_linearCombination_eq_originalComplexPath
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) (z : ℂ)
    (x : Fin (scale N0 (k + 1) - scale N0 k) → ℝ)
    (j : Fin (uniformBlockCount k)) :
    let t : Fin (scale N0 (k + 1) - scale N0 k + 1) :=
      ⟨(j.val + 1) * uniformBlockLength N0 k, by
        rw [scale_gap_eq_uniformBlockCount_mul_length]
        have hj : j.val + 1 ≤ uniformBlockCount k := by omega
        exact Nat.lt_succ_iff.mpr
          (Nat.mul_le_mul_right (uniformBlockLength N0 k) hj)⟩
    (∑ r ∈ Finset.Iic j,
        CutoffLindebergBridge.NormedLindeberg.linearCombination
          (OnePointLindeberg.flatBlockIncrementDirection a hN0 k z) x r) =
      GaussianTubeGlue.originalComplexPath
        (OnePointLindeberg.flatPhaseCoefficient a N0 k z) (fun i x ↦ x i) x t := by
  dsimp only
  rw [flatBlockIncrementDirection_eq_flatDirection]
  rw [FlatVectorAPI.sum_Iic_linearCombination_flatDirection]
  simp only [GaussianTubeGlue.originalComplexPath]
  apply Finset.sum_congr
  · ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [Fin.le_iff_val_le_val, uniformBlockOfOffset_val]
    have hlen : 0 < uniformBlockLength N0 k := uniformBlockLength_pos hN0 k
    rw [show i.val / uniformBlockLength N0 k ≤ j.val ↔
        i.val / uniformBlockLength N0 k < j.val + 1 by omega]
    exact Nat.div_lt_iff_lt_mul hlen
  · intro i hi
    simp only [OnePointLindeberg.flatPhaseCoefficient,
      OnePointLindeberg.flatScaleIndex, FlatVectorAPI.scaleCoefficient]
    push_cast
    ring

/-- Every coefficient-prefix tube of radii `R,r` lies in the plateau-one set of the
endpoint/prefix cutoff, after reciprocal rescaling by any parameters whose absolute values
send the respective radii into the unit disk. -/
theorem canonicalOriginalEvent_subset_flat_cutoff_eq_one
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) (z : ℂ)
    (endpointScale prefixScale R r : ℝ)
    (hend : |endpointScale| * r ≤ 1)
    (hprefix : |prefixScale| * R ≤ 1) :
    GaussianTubeGlue.canonicalOriginalEvent
        (OnePointLindeberg.flatPhaseCoefficient a N0 k z) R r ⊆
      {x | endpointPrefixCutoff (uniformBlockCount k) endpointScale prefixScale
          (CutoffLindebergBridge.NormedLindeberg.linearCombination
            (OnePointLindeberg.flatBlockIncrementDirection a hN0 k z) x) = 1} := by
  intro x hx
  have hxtube :
      (∀ t, ‖GaussianTubeGlue.originalComplexPath
        (OnePointLindeberg.flatPhaseCoefficient a N0 k z) (fun i x ↦ x i) x t‖ ≤ R) ∧
      ‖GaussianTubeGlue.originalComplexPath
        (OnePointLindeberg.flatPhaseCoefficient a N0 k z) (fun i x ↦ x i) x
        (Fin.last (scale N0 (k + 1) - scale N0 k))‖ ≤ r := by
    simpa only [GaussianTubeGlue.canonicalOriginalEvent,
      GaussianTubeGlue.encodedTubeSet, Set.mem_ofPred_eq,
      GaussianTubeGlue.encodedPathCoord_originalEncodedPathLM,
      GaussianTubeGlue.originalComplexPath] using hx
  apply endpointPrefixCutoff_eq_one_of_bounds
  · rw [endpoint_flat_linearCombination_eq_originalComplexPath]
    rw [norm_smul]
    change |endpointScale| *
      ‖GaussianTubeGlue.originalComplexPath
        (OnePointLindeberg.flatPhaseCoefficient a N0 k z) (fun i x ↦ x i) x
        (Fin.last (scale N0 (k + 1) - scale N0 k))‖ ≤ 1
    exact (mul_le_mul_of_nonneg_left hxtube.2 (abs_nonneg endpointScale)).trans hend
  · intro j
    rw [prefix_flat_linearCombination_eq_originalComplexPath]
    rw [norm_smul]
    change |prefixScale| *
      ‖GaussianTubeGlue.originalComplexPath
        (OnePointLindeberg.flatPhaseCoefficient a N0 k z) (fun i x ↦ x i) x
        ⟨(j.val + 1) * uniformBlockLength N0 k, _⟩‖ ≤ 1
    exact (mul_le_mul_of_nonneg_left (hxtube.1 _) (abs_nonneg prefixScale)).trans hprefix

lemma flat_gaussian_cutoff_integrable
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) (z : ℂ)
    (endpointScale prefixScale : ℝ) :
    Integrable (fun x ↦
      endpointPrefixCutoff (uniformBlockCount k) endpointScale prefixScale
        (CutoffLindebergBridge.NormedLindeberg.linearCombination
          (OnePointLindeberg.flatBlockIncrementDirection a hN0 k z) x))
      (Erdos88.Invariance.gaussianProductMeasure
        (scale N0 (k + 1) - scale N0 k)) := by
  let f := fun x ↦
    endpointPrefixCutoff (uniformBlockCount k) endpointScale prefixScale
      (CutoffLindebergBridge.NormedLindeberg.linearCombination
        (OnePointLindeberg.flatBlockIncrementDirection a hN0 k z) x)
  have hfmeas : Measurable f :=
    (endpointPrefixCutoff_contDiff (uniformBlockCount k) endpointScale prefixScale).continuous.measurable.comp
      (CutoffLindebergBridge.NormedLindeberg.measurable_linearCombination _)
  refine Integrable.mono' (integrable_const (1 : ℝ)) hfmeas.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (endpointPrefixCutoff_nonneg (uniformBlockCount k) endpointScale prefixScale _)]
    exact endpointPrefixCutoff_le_one (uniformBlockCount k) endpointScale prefixScale _

/-- The real mass of the canonical Gaussian coefficient-prefix tube is a lower bound for
the Gaussian endpoint/prefix cutoff integral. -/
theorem measureReal_canonicalOriginalEvent_le_flat_gaussian_integral
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) (z : ℂ)
    (endpointScale prefixScale R r : ℝ)
    (hend : |endpointScale| * r ≤ 1)
    (hprefix : |prefixScale| * R ≤ 1) :
    (GaussianTubeGlue.standardGaussianProduct
      (scale N0 (k + 1) - scale N0 k)).real
        (GaussianTubeGlue.canonicalOriginalEvent
          (OnePointLindeberg.flatPhaseCoefficient a N0 k z) R r) ≤
      ∫ x, endpointPrefixCutoff (uniformBlockCount k) endpointScale prefixScale
          (CutoffLindebergBridge.NormedLindeberg.linearCombination
            (OnePointLindeberg.flatBlockIncrementDirection a hN0 k z) x)
        ∂Erdos88.Invariance.gaussianProductMeasure
          (scale N0 (k + 1) - scale N0 k) := by
  let n := scale N0 (k + 1) - scale N0 k
  let A : Set (Fin n → ℝ) := GaussianTubeGlue.canonicalOriginalEvent
    (OnePointLindeberg.flatPhaseCoefficient a N0 k z) R r
  let f : (Fin n → ℝ) → ℝ := fun x ↦
    endpointPrefixCutoff (uniformBlockCount k) endpointScale prefixScale
      (CutoffLindebergBridge.NormedLindeberg.linearCombination
        (OnePointLindeberg.flatBlockIncrementDirection a hN0 k z) x)
  have hA : MeasurableSet A :=
    GaussianTubeGlue.measurableSet_canonicalOriginalEvent _ _ _
  have hsub := canonicalOriginalEvent_subset_flat_cutoff_eq_one
    a hN0 k z endpointScale prefixScale R r hend hprefix
  have hpoint : ∀ x, A.indicator (fun _ ↦ (1 : ℝ)) x ≤ f x := by
    intro x
    by_cases hx : x ∈ A
    · simp only [Set.indicator_of_mem hx]
      exact le_of_eq (hsub hx).symm
    · simp only [Set.indicator_of_notMem hx]
      exact endpointPrefixCutoff_nonneg _ _ _ _
  have hfind : Integrable f (Erdos88.Invariance.gaussianProductMeasure n) :=
    flat_gaussian_cutoff_integrable a hN0 k z endpointScale prefixScale
  have hAint : Integrable (A.indicator fun _ ↦ (1 : ℝ))
      (Erdos88.Invariance.gaussianProductMeasure n) :=
    (integrable_const (1 : ℝ)).indicator hA
  change (GaussianTubeGlue.standardGaussianProduct n).real A ≤ ∫ x, f x
    ∂Erdos88.Invariance.gaussianProductMeasure n
  rw [show GaussianTubeGlue.standardGaussianProduct n =
      Erdos88.Invariance.gaussianProductMeasure n by rfl]
  rw [← MeasureTheory.integral_indicator_one hA]
  exact integral_mono hAint hfind hpoint

/-- An `ENNReal` lower bound for the canonical Gaussian tube becomes the corresponding
`toReal` lower bound for the real Gaussian cutoff expectation. -/
theorem ennreal_tube_lower_le_flat_gaussian_integral
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) (z : ℂ)
    (endpointScale prefixScale R r : ℝ) (p : ℝ≥0∞)
    (hend : |endpointScale| * r ≤ 1)
    (hprefix : |prefixScale| * R ≤ 1)
    (hp : p ≤ GaussianTubeGlue.standardGaussianProduct
      (scale N0 (k + 1) - scale N0 k)
        (GaussianTubeGlue.canonicalOriginalEvent
          (OnePointLindeberg.flatPhaseCoefficient a N0 k z) R r)) :
    p.toReal ≤
      ∫ x, endpointPrefixCutoff (uniformBlockCount k) endpointScale prefixScale
          (CutoffLindebergBridge.NormedLindeberg.linearCombination
            (OnePointLindeberg.flatBlockIncrementDirection a hN0 k z) x)
        ∂Erdos88.Invariance.gaussianProductMeasure
          (scale N0 (k + 1) - scale N0 k) := by
  apply le_trans ?_ (measureReal_canonicalOriginalEvent_le_flat_gaussian_integral
    a hN0 k z endpointScale prefixScale R r hend hprefix)
  exact ENNReal.toReal_mono (measure_ne_top _ _) hp

/-- Law-transport form of `ennreal_tube_lower_le_flat_gaussian_integral`: the tube may be
proved on any probability space carrying a vector with the canonical standard Gaussian
product law. -/
theorem ennreal_complexTube_lower_le_flat_gaussian_integral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) (z : ℂ)
    (g : Fin (scale N0 (k + 1) - scale N0 k) → Ω → ℝ)
    (hg : HasLaw (fun ω i ↦ g i ω)
      (GaussianTubeGlue.standardGaussianProduct
        (scale N0 (k + 1) - scale N0 k)) P)
    (endpointScale prefixScale R r : ℝ) (p : ℝ≥0∞)
    (hend : |endpointScale| * r ≤ 1)
    (hprefix : |prefixScale| * R ≤ 1)
    (hp : p ≤ P (GaussianTubeGlue.complexTubeEvent
      (OnePointLindeberg.flatPhaseCoefficient a N0 k z) g R r)) :
    p.toReal ≤
      ∫ x, endpointPrefixCutoff (uniformBlockCount k) endpointScale prefixScale
          (CutoffLindebergBridge.NormedLindeberg.linearCombination
            (OnePointLindeberg.flatBlockIncrementDirection a hN0 k z) x)
        ∂Erdos88.Invariance.gaussianProductMeasure
          (scale N0 (k + 1) - scale N0 k) := by
  let n := scale N0 (k + 1) - scale N0 k
  let c : Fin n → ℂ := OnePointLindeberg.flatPhaseCoefficient a N0 k z
  let G : Ω → Fin n → ℝ := fun ω i ↦ g i ω
  let A : Set (Fin n → ℝ) := GaussianTubeGlue.canonicalOriginalEvent c R r
  have hA : MeasurableSet A :=
    GaussianTubeGlue.measurableSet_canonicalOriginalEvent _ _ _
  have hevent : P (GaussianTubeGlue.complexTubeEvent c g R r) =
      GaussianTubeGlue.standardGaussianProduct n A := by
    rw [GaussianTubeGlue.complexTubeEvent_eq_preimage]
    calc
      P (G ⁻¹' A) = Measure.map G P A :=
        (Measure.map_apply_of_aemeasurable hg.aemeasurable hA).symm
      _ = GaussianTubeGlue.standardGaussianProduct n A := by rw [hg.map_eq]
  apply ennreal_tube_lower_le_flat_gaussian_integral
    a hN0 k z endpointScale prefixScale R r p hend hprefix
  rw [← hevent]
  exact hp

end

end GaussianCutoffBridge

/-! ## Deterministic block convergence -/

/--
An abstract block criterion for convergence of a series in its natural order.

`cut k` is the left endpoint of block `k`, and `block n` selects a block whose
left endpoint is used to approximate the partial sum ending at `n`. The first
two hypotheses say that the partial sums at the cut points have summably small
successive increments. The last three hypotheses say that the chosen block
indices tend to infinity and that the remainder from the relevant cut point to
an arbitrary endpoint tends uniformly to zero.
-/
theorem summable_conditional_of_block_approx
    {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (f : ℕ → E) (cut block : ℕ → ℕ) (whole edge : ℕ → ℝ)
    (hwhole : ∀ k,
      dist (∑ n ∈ Finset.range (cut k), f n)
        (∑ n ∈ Finset.range (cut (k + 1)), f n) ≤ whole k)
    (hwhole_sum : Summable whole (SummationFilter.unconditional ℕ))
    (hblock : Tendsto block atTop atTop)
    (hedge_zero : Tendsto edge atTop (nhds 0))
    (hedge : ∀ n,
      ‖(∑ j ∈ Finset.range n, f j) -
          (∑ j ∈ Finset.range (cut (block n)), f j)‖ ≤ edge (block n)) :
    Summable f (SummationFilter.conditional ℕ) := by
  let partialSum : ℕ → E := fun n ↦ ∑ j ∈ Finset.range n, f j
  let atCut : ℕ → E := fun k ↦ partialSum (cut k)
  have hcut_cauchy : CauchySeq atCut := by
    apply cauchySeq_of_dist_le_of_summable whole
    · intro k
      simpa [atCut, partialSum, Nat.succ_eq_add_one] using hwhole k
    · exact hwhole_sum
  obtain ⟨limit, hcut_limit⟩ := cauchySeq_tendsto_of_complete hcut_cauchy
  have hcut_block_limit : Tendsto (fun n ↦ atCut (block n)) atTop (nhds limit) :=
    hcut_limit.comp hblock
  have hedge_comp_zero : Tendsto (fun n ↦ edge (block n)) atTop (nhds 0) :=
    hedge_zero.comp hblock
  have hremainder_zero :
      Tendsto (fun n ↦ partialSum n - atCut (block n)) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg _)
      (Eventually.of_forall ?_) hedge_comp_zero
    intro n
    simpa [partialSum, atCut] using hedge n
  have hpartial_limit : Tendsto partialSum atTop (nhds limit) := by
    have hadd := hremainder_zero.add hcut_block_limit
    simpa only [sub_add_cancel, zero_add] using hadd
  refine ⟨limit, ?_⟩
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff]
  change Tendsto (fun n ↦ ∑ j ∈ Finset.range n, f j) atTop (nhds limit)
  simpa only [partialSum] using hpartial_limit

/--
A block-interval form of `summable_conditional_of_block_approx`. Successive
cut points delimit complete blocks, while `block n` chooses the block containing
the endpoint `n` (only its left-endpoint property is needed). Thus the two norm
bounds are exactly bounds on complete blocks and on terminal pieces.
-/
theorem summable_conditional_of_block_bounds
    {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (f : ℕ → E) (cut block : ℕ → ℕ) (whole edge : ℕ → ℝ)
    (hcut : ∀ k, cut k ≤ cut (k + 1))
    (hwhole : ∀ k,
      ‖∑ n ∈ Finset.Ico (cut k) (cut (k + 1)), f n‖ ≤ whole k)
    (hwhole_sum : Summable whole (SummationFilter.unconditional ℕ))
    (hblock : Tendsto block atTop atTop)
    (hedge_zero : Tendsto edge atTop (nhds 0))
    (hleft : ∀ n, cut (block n) ≤ n)
    (hedge : ∀ n,
      ‖∑ j ∈ Finset.Ico (cut (block n)) n, f j‖ ≤ edge (block n)) :
    Summable f (SummationFilter.conditional ℕ) := by
  apply summable_conditional_of_block_approx f cut block whole edge
  · intro k
    rw [dist_eq_norm, ← norm_neg, neg_sub,
      ← Finset.sum_Ico_eq_sub _ (hcut k)]
    exact hwhole k
  · exact hwhole_sum
  · exact hblock
  · exact hedge_zero
  · intro n
    rw [← Finset.sum_Ico_eq_sub _ (hleft n)]
    exact hedge n

/-! ## Deterministic compactness and alive-grid convergence -/

section DeterministicAliveGlue

open Set

/-- The unit-circle points captured by one of the finitely many surviving phase
centres, with a prescribed closed thickening. -/
def thickenedFinitePhaseSet (phase : ℕ → Finset ℂ) (radius : ℕ → ℝ)
    (k : ℕ) : Set ℂ :=
  {z | ‖z‖ = 1 ∧ ∃ w ∈ phase k, dist z w ≤ radius k}

lemma thickenedFinitePhaseSet_eq (phase : ℕ → Finset ℂ) (radius : ℕ → ℝ)
    (k : ℕ) :
    thickenedFinitePhaseSet phase radius k =
      Metric.sphere (0 : ℂ) 1 ∩
        ⋃ w ∈ phase k, Metric.closedBall w (radius k) := by
  ext z
  simp only [thickenedFinitePhaseSet, mem_ofPred_eq, mem_inter_iff,
    Metric.mem_sphere, dist_zero_right, mem_iUnion, Metric.mem_closedBall]
  constructor
  · rintro ⟨hz, w, hw, hzw⟩
    exact ⟨hz, w, hw, by simpa [dist_comm] using hzw⟩
  · rintro ⟨hz, w, hw, hwz⟩
    exact ⟨hz, w, hw, by simpa [dist_comm] using hwz⟩

lemma isClosed_thickenedFinitePhaseSet (phase : ℕ → Finset ℂ)
    (radius : ℕ → ℝ) (k : ℕ) :
    IsClosed (thickenedFinitePhaseSet phase radius k) := by
  rw [thickenedFinitePhaseSet_eq]
  exact Metric.isClosed_sphere.inter
    (isClosed_biUnion_finset fun _ _ ↦ Metric.isClosed_closedBall)

lemma isCompact_thickenedFinitePhaseSet (phase : ℕ → Finset ℂ)
    (radius : ℕ → ℝ) (k : ℕ) :
    IsCompact (thickenedFinitePhaseSet phase radius k) := by
  rw [thickenedFinitePhaseSet_eq]
  exact (isCompact_sphere (0 : ℂ) 1).inter_right
    (isClosed_biUnion_finset fun _ _ ↦ Metric.isClosed_closedBall)

/-- Nested nonempty finite thickenings have a common unit-circle point. -/
theorem exists_unit_mem_all_thickenedFinitePhaseSet
    (phase : ℕ → Finset ℂ) (radius : ℕ → ℝ)
    (hnested : ∀ k,
      thickenedFinitePhaseSet phase radius (k + 1) ⊆
        thickenedFinitePhaseSet phase radius k)
    (hne : ∀ k, (thickenedFinitePhaseSet phase radius k).Nonempty) :
    ∃ z : ℂ, ‖z‖ = 1 ∧
      ∀ k, z ∈ thickenedFinitePhaseSet phase radius k := by
  obtain ⟨z, hz⟩ := exists_mem_all_of_nested_compact
    (thickenedFinitePhaseSet phase radius) hnested hne
    (isCompact_thickenedFinitePhaseSet phase radius 0)
    (isClosed_thickenedFinitePhaseSet phase radius)
  exact ⟨z, (hz 0).1, hz⟩

/-- Cut points with an initial finite block followed by the cubic scales. -/
def aliveCut (N0 : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => scale N0 k

lemma aliveCut_succ_le (N0 k : ℕ) : aliveCut N0 k ≤ aliveCut N0 (k + 1) := by
  cases k with
  | zero => simp [aliveCut]
  | succ k => simpa [aliveCut] using scale_le_scale_succ N0 k

lemma aliveCut_monotone (N0 : ℕ) : Monotone (aliveCut N0) :=
  monotone_nat_of_le_succ (aliveCut_succ_le N0)

lemma index_le_aliveCut {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) :
    k ≤ aliveCut N0 k := by
  cases k with
  | zero => simp [aliveCut]
  | succ k =>
      simp only [aliveCut]
      exact (Nat.add_one_le_iff.mpr Nat.lt_two_pow_self).trans
        (two_pow_le_scale hN0 k)

/-- The last cut point not exceeding `n`.  The search bound `n+1` is harmless,
since a positive initial scale makes the `k`th cut at least `k`. -/
noncomputable def aliveBlock (N0 n : ℕ) : ℕ :=
  Nat.findGreatest (fun k ↦ aliveCut N0 k ≤ n) (n + 1)

lemma aliveCut_aliveBlock_le (N0 n : ℕ) :
    aliveCut N0 (aliveBlock N0 n) ≤ n := by
  unfold aliveBlock
  apply Nat.findGreatest_spec (P := fun k ↦ aliveCut N0 k ≤ n)
      (m := 0) (Nat.zero_le _)
  change 0 ≤ n
  exact Nat.zero_le n

lemma aliveBlock_le {N0 : ℕ} (hN0 : 0 < N0) (n : ℕ) :
    aliveBlock N0 n ≤ n := by
  exact (index_le_aliveCut hN0 _).trans (aliveCut_aliveBlock_le N0 n)

lemma lt_aliveCut_aliveBlock_succ {N0 : ℕ} (hN0 : 0 < N0) (n : ℕ) :
    n < aliveCut N0 (aliveBlock N0 n + 1) := by
  by_contra h
  have hnext : aliveCut N0 (aliveBlock N0 n + 1) ≤ n := le_of_not_gt h
  exact (Nat.findGreatest_is_greatest
    (show aliveBlock N0 n < aliveBlock N0 n + 1 by omega)
    (show aliveBlock N0 n + 1 ≤ n + 1 by
      exact Nat.add_le_add_right (aliveBlock_le hN0 n) 1)) hnext

lemma aliveBlock_tendsto_atTop {N0 : ℕ} (hN0 : 0 < N0) :
    Tendsto (aliveBlock N0) atTop atTop := by
  refine tendsto_atTop.2 fun K ↦ ?_
  filter_upwards [eventually_ge_atTop (aliveCut N0 K)] with n hn
  exact Nat.le_findGreatest
    ((index_le_aliveCut hN0 K).trans hn |>.trans (Nat.le_add_right n 1)) hn

/-- The deterministic last step of the alive-grid construction.

The finite phase sets enter only through their nested closed thickenings.  The
first estimate controls complete scale increments.  The second controls the
walk at every flat-block endpoint.  The third is the uniform oscillation inside
one flat block.  `block n` merely records which interval between consecutive
`aliveCut`s contains `n`; this formulation deliberately separates compactness
from the elementary choice of a generalized inverse of the cut sequence. -/
theorem exists_unit_summable_conditional_of_nested_alive_flat
    (f : ℂ → ℕ → ℂ)
    (phase : ℕ → Finset ℂ) (radius δ tol : ℕ → ℝ)
    {N0 : ℕ} (hN0 : 0 < N0)
    (hnested : ∀ k,
      thickenedFinitePhaseSet phase radius (k + 1) ⊆
        thickenedFinitePhaseSet phase radius k)
    (hne : ∀ k, (thickenedFinitePhaseSet phase radius k).Nonempty)
    (hδ0 : Tendsto δ atTop (nhds 0))
    (htol0 : Tendsto tol atTop (nhds 0))
    (htol_nonneg : ∀ k, 0 ≤ tol k)
    (block : ℕ → ℕ)
    (hblock : Tendsto block atTop atTop)
    (hleft : ∀ n, aliveCut N0 (block n) ≤ n)
    (hright : ∀ n, n < aliveCut N0 (block n + 1))
    (hwhole : ∀ k z,
      z ∈ thickenedFinitePhaseSet phase radius k →
      ‖∑ n ∈ Finset.Ico (scale N0 k) (scale N0 (k + 1)), f z n‖ ≤
        1 / ((k + 1 : ℕ) : ℝ) ^ 2)
    (hflatPrefix : ∀ k z,
      z ∈ thickenedFinitePhaseSet phase radius k →
      ∀ r ≤ uniformBlockCount k,
        ‖∑ n ∈ Finset.Ico (scale N0 k) (uniformEndpoint N0 k r), f z n‖ ≤
          Real.sqrt (δ k))
    (hintra : ∀ k z, ‖z‖ = 1 →
      ∀ r < uniformBlockCount k, ∀ l < uniformBlockLength N0 k,
        ‖∑ n ∈ uniformPrefix N0 k r l, f z n‖ ≤ tol k) :
    ∃ z : ℂ, ‖z‖ = 1 ∧
      Summable (f z) (SummationFilter.conditional ℕ) := by
  obtain ⟨z, hzunit, hzmem⟩ :=
    exists_unit_mem_all_thickenedFinitePhaseSet phase radius hnested hne
  let initial : ℝ := ∑ n ∈ Finset.range N0, ‖f z n‖
  let whole : ℕ → ℝ
    | 0 => initial
    | k + 1 => 1 / ((k + 1 : ℕ) : ℝ) ^ 2
  let edge : ℕ → ℝ
    | 0 => initial
    | k + 1 => Real.sqrt (δ k) + tol k
  have hwholeSummable : Summable whole (SummationFilter.unconditional ℕ) := by
    have hp : Summable (fun k : ℕ ↦ 1 / (k : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have hu := hp.update 0 initial
    apply hu.congr
    intro k
    cases k <;> simp [whole, Function.update]
  have hedgeZero : Tendsto edge atTop (nhds 0) := by
    apply (Filter.tendsto_add_atTop_iff_nat (f := edge) 1).mp
    have hsqrt : Tendsto (fun k ↦ Real.sqrt (δ k)) atTop (nhds 0) := by
      have h := hδ0.sqrt
      rw [Real.sqrt_zero] at h
      exact h
    have hadd := hsqrt.add htol0
    simpa [edge] using hadd
  refine ⟨z, hzunit, summable_conditional_of_block_bounds
    (f z) (aliveCut N0) block whole edge
    (aliveCut_succ_le N0) ?_ hwholeSummable hblock hedgeZero hleft ?_⟩
  · intro k
    cases k with
    | zero =>
        calc
          ‖∑ n ∈ Finset.Ico (aliveCut N0 0) (aliveCut N0 (0 + 1)), f z n‖
              ≤ ∑ n ∈ Finset.Ico 0 N0, ‖f z n‖ := by
                simpa [aliveCut] using norm_sum_le (Finset.Ico 0 N0) (f z)
          _ = whole 0 := by simp [whole, initial]
    | succ k =>
        simpa [aliveCut, whole] using hwhole k z (hzmem k)
  · intro n
    generalize hb : block n = b
    cases b with
    | zero =>
        have hnN0 : n < N0 := by
          simpa [hb, aliveCut] using hright n
        calc
          ‖∑ j ∈ Finset.Ico (aliveCut N0 0) n, f z j‖
              ≤ ∑ j ∈ Finset.Ico 0 n, ‖f z j‖ := by
                simpa [hb, aliveCut] using norm_sum_le (Finset.Ico 0 n) (f z)
          _ ≤ ∑ j ∈ Finset.range N0, ‖f z j‖ := by
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · intro j hj
                  simp only [Finset.mem_Ico] at hj
                  simp only [Finset.mem_range]
                  omega
                · intro j _ _
                  exact norm_nonneg _
          _ = edge 0 := by simp [edge, initial]
    | succ k =>
        have hnleft : scale N0 k ≤ n := by
          simpa [hb, aliveCut] using hleft n
        have hnright : n < scale N0 (k + 1) := by
          simpa [hb, aliveCut] using hright n
        let off := n - scale N0 k
        let len := uniformBlockLength N0 k
        let r := off / len
        let rem := off % len
        have hlen : 0 < len := uniformBlockLength_pos hN0 k
        have hoff : off < uniformBlockCount k * len := by
          rw [← scale_gap_eq_uniformBlockCount_mul_length]
          dsimp only [off]
          omega
        have hr : r < uniformBlockCount k := by
          rw [Nat.div_lt_iff_lt_mul hlen]
          simpa [r] using hoff
        have hrem : rem < len := by
          exact Nat.mod_lt _ hlen
        have hn_decomp : n = uniformEndpoint N0 k r + rem := by
          calc
            n = scale N0 k + off := (Nat.add_sub_of_le hnleft).symm
            _ = scale N0 k + (len * r + rem) := by
              rw [Nat.div_add_mod off len]
            _ = uniformEndpoint N0 k r + rem := by
              simp [uniformEndpoint, len, Nat.mul_comm, Nat.add_assoc]
        have hscale_endpoint : scale N0 k ≤ uniformEndpoint N0 k r :=
          uniformBlock_start_ge_scale N0 k r
        have hendpoint_n : uniformEndpoint N0 k r ≤ n := by
          omega
        have hfirst :
            ‖∑ j ∈ Finset.Ico (scale N0 k) (uniformEndpoint N0 k r), f z j‖ ≤
              Real.sqrt (δ k) :=
          hflatPrefix k z (hzmem k) r hr.le
        have hlast :
            ‖∑ j ∈ Finset.Ico (uniformEndpoint N0 k r) n, f z j‖ ≤ tol k := by
          by_cases hrem0 : rem = 0
          · rw [hn_decomp, hrem0]
            simpa using htol_nonneg k
          · have hl : rem - 1 < uniformBlockLength N0 k := by
              dsimp only [len] at hrem
              omega
            have hset : Finset.Ico (uniformEndpoint N0 k r) n =
                uniformPrefix N0 k r (rem - 1) := by
              ext j
              simp only [Finset.mem_Ico, uniformPrefix]
              omega
            rw [hset]
            exact hintra k z hzunit r hr (rem - 1) hl
        calc
          ‖∑ j ∈ Finset.Ico (aliveCut N0 (k + 1)) n, f z j‖ =
              ‖(∑ j ∈ Finset.Ico (scale N0 k) (uniformEndpoint N0 k r), f z j) +
                ∑ j ∈ Finset.Ico (uniformEndpoint N0 k r) n, f z j‖ := by
                  simp only [aliveCut]
                  rw [Finset.sum_Ico_consecutive _ hscale_endpoint hendpoint_n]
          _ ≤ ‖∑ j ∈ Finset.Ico (scale N0 k) (uniformEndpoint N0 k r), f z j‖ +
                ‖∑ j ∈ Finset.Ico (uniformEndpoint N0 k r) n, f z j‖ :=
              norm_add_le _ _
          _ ≤ Real.sqrt (δ k) + tol k := add_le_add hfirst hlast
          _ = edge (k + 1) := by simp [edge]

/-- The same deterministic glue with the canonical generalized inverse of the
cut sequence supplied automatically. -/
theorem exists_unit_summable_conditional_of_nested_alive_flat'
    (f : ℂ → ℕ → ℂ)
    (phase : ℕ → Finset ℂ) (radius δ tol : ℕ → ℝ)
    {N0 : ℕ} (hN0 : 0 < N0)
    (hnested : ∀ k,
      thickenedFinitePhaseSet phase radius (k + 1) ⊆
        thickenedFinitePhaseSet phase radius k)
    (hne : ∀ k, (thickenedFinitePhaseSet phase radius k).Nonempty)
    (hδ0 : Tendsto δ atTop (nhds 0))
    (htol0 : Tendsto tol atTop (nhds 0))
    (htol_nonneg : ∀ k, 0 ≤ tol k)
    (hwhole : ∀ k z,
      z ∈ thickenedFinitePhaseSet phase radius k →
      ‖∑ n ∈ Finset.Ico (scale N0 k) (scale N0 (k + 1)), f z n‖ ≤
        1 / ((k + 1 : ℕ) : ℝ) ^ 2)
    (hflatPrefix : ∀ k z,
      z ∈ thickenedFinitePhaseSet phase radius k →
      ∀ r ≤ uniformBlockCount k,
        ‖∑ n ∈ Finset.Ico (scale N0 k) (uniformEndpoint N0 k r), f z n‖ ≤
          Real.sqrt (δ k))
    (hintra : ∀ k z, ‖z‖ = 1 →
      ∀ r < uniformBlockCount k, ∀ l < uniformBlockLength N0 k,
        ‖∑ n ∈ uniformPrefix N0 k r l, f z n‖ ≤ tol k) :
    ∃ z : ℂ, ‖z‖ = 1 ∧
      Summable (f z) (SummationFilter.conditional ℕ) := by
  exact exists_unit_summable_conditional_of_nested_alive_flat
    f phase radius δ tol hN0 hnested hne hδ0 htol0 htol_nonneg
    (aliveBlock N0) (aliveBlock_tendsto_atTop hN0)
    (aliveCut_aliveBlock_le N0)
    (lt_aliveCut_aliveBlock_succ hN0)
    hwhole hflatPrefix hintra

end DeterministicAliveGlue

/-! ## Reset-indexed deterministic alive-grid convergence -/

section ResetAliveGlue

/-- Delete the finite initial segment strictly below `M`. -/
def truncateBelow {E : Type*} [Zero E] (M : ℕ) (u : ℕ → E) (n : ℕ) : E :=
  if M ≤ n then u n else 0

lemma sum_Ico_truncateBelow_eq_of_le
    {E : Type*} [AddCommMonoid E] (u : ℕ → E) {M lo hi : ℕ} (hMlo : M ≤ lo) :
    (∑ n ∈ Finset.Ico lo hi, truncateBelow M u n) =
      ∑ n ∈ Finset.Ico lo hi, u n := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [truncateBelow, if_pos (hMlo.trans (Finset.mem_Ico.mp hn).1)]

lemma sum_Ico_truncateBelow_eq_zero
    {E : Type*} [AddCommMonoid E] (u : ℕ → E) {M lo hi : ℕ} (hhi : hi ≤ M) :
    (∑ n ∈ Finset.Ico lo hi, truncateBelow M u n) = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  rw [truncateBelow, if_neg]
  intro hMn
  have hnhi := (Finset.mem_Ico.mp hn).2
  omega

/-- Reset cut sequence: first `0`, then the cubic scales beginning at `start`. -/
def resetAliveCut (N0 start : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => scale N0 (start + t)

lemma resetAliveCut_succ_le (N0 start t : ℕ) :
    resetAliveCut N0 start t ≤ resetAliveCut N0 start (t + 1) := by
  cases t with
  | zero => simp [resetAliveCut]
  | succ t =>
      simpa [resetAliveCut, Nat.add_assoc] using scale_le_scale_succ N0 (start + t)

lemma index_le_resetAliveCut {N0 : ℕ} (hN0 : 0 < N0) (start t : ℕ) :
    t ≤ resetAliveCut N0 start t := by
  cases t with
  | zero => simp [resetAliveCut]
  | succ t =>
      simp only [resetAliveCut]
      have ht : t + 1 ≤ start + t + 1 := by omega
      exact ht.trans ((Nat.add_one_le_iff.mpr Nat.lt_two_pow_self).trans
        (two_pow_le_scale hN0 (start + t)))

/-- Canonical generalized inverse of the reset cut sequence. -/
noncomputable def resetAliveBlock (N0 start n : ℕ) : ℕ :=
  Nat.findGreatest (fun t ↦ resetAliveCut N0 start t ≤ n) (n + 1)

lemma resetAliveCut_resetAliveBlock_le (N0 start n : ℕ) :
    resetAliveCut N0 start (resetAliveBlock N0 start n) ≤ n := by
  unfold resetAliveBlock
  apply Nat.findGreatest_spec
      (P := fun t ↦ resetAliveCut N0 start t ≤ n) (m := 0) (Nat.zero_le _)
  change 0 ≤ n
  exact Nat.zero_le n

lemma resetAliveBlock_le {N0 : ℕ} (hN0 : 0 < N0) (start n : ℕ) :
    resetAliveBlock N0 start n ≤ n := by
  exact (index_le_resetAliveCut hN0 start _).trans
    (resetAliveCut_resetAliveBlock_le N0 start n)

lemma lt_resetAliveCut_resetAliveBlock_succ {N0 : ℕ} (hN0 : 0 < N0)
    (start n : ℕ) :
    n < resetAliveCut N0 start (resetAliveBlock N0 start n + 1) := by
  by_contra h
  have hnext : resetAliveCut N0 start (resetAliveBlock N0 start n + 1) ≤ n :=
    le_of_not_gt h
  exact (Nat.findGreatest_is_greatest
    (show resetAliveBlock N0 start n < resetAliveBlock N0 start n + 1 by omega)
    (show resetAliveBlock N0 start n + 1 ≤ n + 1 by
      exact Nat.add_le_add_right (resetAliveBlock_le hN0 start n) 1)) hnext

lemma resetAliveBlock_tendsto_atTop {N0 : ℕ} (hN0 : 0 < N0) (start : ℕ) :
    Tendsto (resetAliveBlock N0 start) atTop atTop := by
  refine tendsto_atTop.2 fun T ↦ ?_
  filter_upwards [eventually_ge_atTop (resetAliveCut N0 start T)] with n hn
  exact Nat.le_findGreatest
    ((index_le_resetAliveCut hN0 start T).trans hn |>.trans (Nat.le_add_right n 1)) hn

/-- Reset-indexed deterministic alive-grid glue.

The phase family begins at the chosen absolute generation `start`; no dummy
phase sets are required at earlier generations.  The original series is
recovered from the truncated one by finite-modification invariance. -/
theorem exists_unit_summable_conditional_of_reset_nested_alive_flat
    (f : ℂ → ℕ → ℂ)
    (phase : ℕ → Finset ℂ) (radius δ tol : ℕ → ℝ)
    {N0 : ℕ} (hN0 : 0 < N0) (start : ℕ)
    (hnested : ∀ t,
      thickenedFinitePhaseSet phase radius (t + 1) ⊆
        thickenedFinitePhaseSet phase radius t)
    (hne : ∀ t, (thickenedFinitePhaseSet phase radius t).Nonempty)
    (hδ0 : Tendsto (fun t ↦ δ (start + t)) atTop (nhds 0))
    (htol0 : Tendsto (fun t ↦ tol (start + t)) atTop (nhds 0))
    (htol_nonneg : ∀ k, 0 ≤ tol k)
    (hwhole : ∀ t z,
      z ∈ thickenedFinitePhaseSet phase radius t →
      ‖∑ n ∈ Finset.Ico (scale N0 (start + t)) (scale N0 (start + t + 1)),
          f z n‖ ≤ 1 / ((start + t + 1 : ℕ) : ℝ) ^ 2)
    (hflatPrefix : ∀ t z,
      z ∈ thickenedFinitePhaseSet phase radius t →
      ∀ r ≤ uniformBlockCount (start + t),
        ‖∑ n ∈ Finset.Ico (scale N0 (start + t))
            (uniformEndpoint N0 (start + t) r), f z n‖ ≤
          Real.sqrt (δ (start + t)))
    (hintra : ∀ t z, ‖z‖ = 1 →
      ∀ r < uniformBlockCount (start + t),
        ∀ l < uniformBlockLength N0 (start + t),
          ‖∑ n ∈ uniformPrefix N0 (start + t) r l, f z n‖ ≤
            tol (start + t)) :
    ∃ z : ℂ, ‖z‖ = 1 ∧
      Summable (f z) (SummationFilter.conditional ℕ) := by
  obtain ⟨z, hzunit, hzmem⟩ :=
    exists_unit_mem_all_thickenedFinitePhaseSet phase radius hnested hne
  let M := scale N0 start
  let g : ℕ → ℂ := truncateBelow M (f z)
  let whole : ℕ → ℝ
    | 0 => 0
    | t + 1 => 1 / ((start + t + 1 : ℕ) : ℝ) ^ 2
  let edge : ℕ → ℝ
    | 0 => 0
    | t + 1 => Real.sqrt (δ (start + t)) + tol (start + t)
  have hwholeSummable : Summable whole (SummationFilter.unconditional ℕ) := by
    have hp : Summable (fun k : ℕ ↦ 1 / (k : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have htail : Summable
        (fun t : ℕ ↦ 1 / ((start + t + 1 : ℕ) : ℝ) ^ 2) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (summable_nat_add_iff (start + 1)).mpr hp
    apply (summable_nat_add_iff 1).mp
    simpa [whole] using htail
  have hedgeZero : Tendsto edge atTop (nhds 0) := by
    apply (Filter.tendsto_add_atTop_iff_nat (f := edge) 1).mp
    have hsqrt : Tendsto (fun t ↦ Real.sqrt (δ (start + t))) atTop (nhds 0) := by
      have h := hδ0.sqrt
      rw [Real.sqrt_zero] at h
      exact h
    simpa [edge] using hsqrt.add htol0
  have hsumg : Summable g (SummationFilter.conditional ℕ) := by
    refine summable_conditional_of_block_bounds g (resetAliveCut N0 start)
      (resetAliveBlock N0 start) whole edge (resetAliveCut_succ_le N0 start)
      ?_ hwholeSummable (resetAliveBlock_tendsto_atTop hN0 start) hedgeZero
      (resetAliveCut_resetAliveBlock_le N0 start) ?_
    · intro b
      cases b with
      | zero =>
          have hzero : (∑ n ∈ Finset.Ico 0 M, g n) = 0 := by
            exact sum_Ico_truncateBelow_eq_zero (f z) (le_refl M)
          simpa [resetAliveCut, whole, g, M] using congrArg norm hzero
      | succ t =>
          have hMscale : M ≤ scale N0 (start + t) := by
            dsimp only [M]
            exact scale_monotone N0 (Nat.le_add_right start t)
          have hsum :
              (∑ n ∈ Finset.Ico (scale N0 (start + t))
                  (scale N0 (start + t + 1)), g n) =
                ∑ n ∈ Finset.Ico (scale N0 (start + t))
                  (scale N0 (start + t + 1)), f z n := by
            simpa [g] using sum_Ico_truncateBelow_eq_of_le (f z) hMscale
          simp only [resetAliveCut, whole]
          rw [show start + (t + 1) = start + t + 1 by omega]
          rw [hsum]
          simpa [Nat.add_assoc] using hwhole t z (hzmem t)
    · intro n
      generalize hb : resetAliveBlock N0 start n = b
      cases b with
      | zero =>
          have hnM : n < M := by
            simpa [hb, resetAliveCut, M] using
              lt_resetAliveCut_resetAliveBlock_succ hN0 start n
          have hzero : (∑ j ∈ Finset.Ico 0 n, g j) = 0 := by
            exact sum_Ico_truncateBelow_eq_zero (f z) hnM.le
          simpa [resetAliveCut, edge, g, M] using congrArg norm hzero
      | succ t =>
          let k := start + t
          have hnleft : scale N0 k ≤ n := by
            simpa [hb, resetAliveCut, k] using
              resetAliveCut_resetAliveBlock_le N0 start n
          have hnright : n < scale N0 (k + 1) := by
            simpa [hb, resetAliveCut, k, Nat.add_assoc] using
              lt_resetAliveCut_resetAliveBlock_succ hN0 start n
          have hMscale : M ≤ scale N0 k := by
            dsimp only [M, k]
            exact scale_monotone N0 (Nat.le_add_right start t)
          let off := n - scale N0 k
          let len := uniformBlockLength N0 k
          let r := off / len
          let rem := off % len
          have hlen : 0 < len := uniformBlockLength_pos hN0 k
          have hoff : off < uniformBlockCount k * len := by
            rw [← scale_gap_eq_uniformBlockCount_mul_length]
            dsimp only [off]
            omega
          have hr : r < uniformBlockCount k := by
            rw [Nat.div_lt_iff_lt_mul hlen]
            simpa [r] using hoff
          have hrem : rem < len := Nat.mod_lt _ hlen
          have hn_decomp : n = uniformEndpoint N0 k r + rem := by
            calc
              n = scale N0 k + off := (Nat.add_sub_of_le hnleft).symm
              _ = scale N0 k + (len * r + rem) := by
                rw [Nat.div_add_mod off len]
              _ = uniformEndpoint N0 k r + rem := by
                simp [uniformEndpoint, len, Nat.mul_comm, Nat.add_assoc]
          have hscale_endpoint : scale N0 k ≤ uniformEndpoint N0 k r :=
            uniformBlock_start_ge_scale N0 k r
          have hendpoint_n : uniformEndpoint N0 k r ≤ n := by omega
          have hfirst :
              ‖∑ j ∈ Finset.Ico (scale N0 k) (uniformEndpoint N0 k r), g j‖ ≤
                Real.sqrt (δ k) := by
            rw [sum_Ico_truncateBelow_eq_of_le (f z) hMscale]
            exact hflatPrefix t z (hzmem t) r hr.le
          have hlast :
              ‖∑ j ∈ Finset.Ico (uniformEndpoint N0 k r) n, g j‖ ≤
                tol k := by
            rw [sum_Ico_truncateBelow_eq_of_le (f z)
              (hMscale.trans hscale_endpoint)]
            by_cases hrem0 : rem = 0
            · rw [hn_decomp, hrem0]
              simpa using htol_nonneg k
            · have hl : rem - 1 < uniformBlockLength N0 k := by
                dsimp only [len] at hrem
                omega
              have hset : Finset.Ico (uniformEndpoint N0 k r) n =
                  uniformPrefix N0 k r (rem - 1) := by
                ext j
                simp only [Finset.mem_Ico, uniformPrefix]
                omega
              rw [hset]
              exact hintra t z hzunit r hr (rem - 1) hl
          calc
            ‖∑ j ∈ Finset.Ico (resetAliveCut N0 start (t + 1)) n, g j‖ =
                ‖(∑ j ∈ Finset.Ico (scale N0 k) (uniformEndpoint N0 k r), g j) +
                  ∑ j ∈ Finset.Ico (uniformEndpoint N0 k r) n, g j‖ := by
                    simp only [resetAliveCut, k]
                    rw [Finset.sum_Ico_consecutive _ hscale_endpoint hendpoint_n]
            _ ≤ ‖∑ j ∈ Finset.Ico (scale N0 k) (uniformEndpoint N0 k r), g j‖ +
                  ‖∑ j ∈ Finset.Ico (uniformEndpoint N0 k r) n, g j‖ :=
                norm_add_le _ _
            _ ≤ Real.sqrt (δ k) + tol k := add_le_add hfirst hlast
            _ = edge (t + 1) := by simp [edge, k]
  have heq : g =ᶠ[atTop] f z := by
    filter_upwards [eventually_ge_atTop M] with n hn
    simp [g, truncateBelow, hn]
  exact ⟨z, hzunit, (summable_conditional_congr_atTop heq).mp hsumg⟩

end ResetAliveGlue

namespace ScalarGaussianPath


/-- On a centered Gaussian density, every point of an interval centered at `c`
has density at least the density at distance `|c| + h` from the origin. -/
lemma gaussianPDFReal_lower_on_Icc (v : ℝ≥0) (hv : v ≠ 0) (c h x : ℝ)
    (hh : 0 ≤ h) (hx : x ∈ Set.Icc (c - h) (c + h)) :
    ProbabilityTheory.gaussianPDFReal 0 v (|c| + h) ≤
      ProbabilityTheory.gaussianPDFReal 0 v x := by
  have hvpos : 0 < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have habs : |x| ≤ |c| + h := by
    rcases hx with ⟨hxlo, hxhi⟩
    rw [abs_le]
    constructor <;> nlinarith [le_abs_self c, neg_abs_le c]
  have hsquare : x ^ 2 ≤ (|c| + h) ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg (by positivity : 0 ≤ |c| + h)] using habs
  unfold ProbabilityTheory.gaussianPDFReal
  simp only [NNReal.coe_eq_zero, hv, if_false, sub_zero]
  gcongr

/-- A directly usable lower bound for the mass of a finite interval under a
nondegenerate centered real Gaussian.  The deliberately un-simplified density
factor is convenient in the finite-walk iteration. -/
theorem gaussianReal_Icc_lower (v : ℝ≥0) (hv : v ≠ 0) (c h : ℝ) (hh : 0 ≤ h) :
    ENNReal.ofReal ((2 * h) * ProbabilityTheory.gaussianPDFReal 0 v (|c| + h)) ≤
      ProbabilityTheory.gaussianReal 0 v (Set.Icc (c - h) (c + h)) := by
  rw [ProbabilityTheory.gaussianReal_apply_eq_integral 0 hv]
  apply ENNReal.ofReal_le_ofReal
  calc
    (2 * h) * ProbabilityTheory.gaussianPDFReal 0 v (|c| + h) =
        ∫ _ in Set.Icc (c - h) (c + h),
          ProbabilityTheory.gaussianPDFReal 0 v (|c| + h) ∂volume := by
          rw [setIntegral_const]
          have hd : 0 ≤ (c + h) - (c - h) := by linarith
          simp only [measureReal_def, Real.volume_Icc,
            ENNReal.toReal_ofReal hd, smul_eq_mul]
          ring
    _ ≤ ∫ x in Set.Icc (c - h) (c + h),
        ProbabilityTheory.gaussianPDFReal 0 v x ∂volume := by
      apply setIntegral_mono_on
      · exact integrableOn_const (μ := volume) (by
          rw [Real.volume_Icc]
          exact ENNReal.ofReal_ne_top)
      · exact (ProbabilityTheory.integrable_gaussianPDFReal 0 v).integrableOn
      · exact measurableSet_Icc
      · intro x hx
        exact gaussianPDFReal_lower_on_Icc v hv c h x hh hx

/-- Uniform density bound used for a variance-regular macroblock.  The large
constant `256` is intentional: it makes all estimates elementary and leaves
ample room in the eventual walk iteration. -/
lemma gaussianPDFReal_macroblock_lower (v : ℝ≥0) (c h u : ℝ)
    (hu : 0 < u) (hh : 0 ≤ h) (hhu : h ≤ u) (hc : |c| ≤ u)
    (hvlo : u ^ 2 / 128 ≤ (v : ℝ)) (hvhi : (v : ℝ) ≤ u ^ 2) :
    Real.exp (-256) / (4 * u) ≤
      ProbabilityTheory.gaussianPDFReal 0 v (|c| + h) := by
  have hvpos : 0 < (v : ℝ) := by
    have : 0 < u ^ 2 / 128 := by positivity
    exact this.trans_le hvlo
  have hv : v ≠ 0 := by exact_mod_cast ne_of_gt hvpos
  have hxnonneg : 0 ≤ |c| + h := by positivity
  have hx : |c| + h ≤ 2 * u := by linarith
  have hxsq : (|c| + h) ^ 2 ≤ 4 * u ^ 2 := by nlinarith
  have hquot : (|c| + h) ^ 2 / (2 * (v : ℝ)) ≤ 256 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (v : ℝ))).2
    nlinarith
  have hexp : Real.exp (-256) ≤
      Real.exp (-((|c| + h) ^ 2 / (2 * (v : ℝ)))) := by
    exact Real.exp_le_exp.mpr (by linarith)
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi * (v : ℝ)) := by positivity
  have hsqrt_sq : (Real.sqrt (2 * Real.pi * (v : ℝ))) ^ 2 =
      2 * Real.pi * (v : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  have hsqrt_le : Real.sqrt (2 * Real.pi * (v : ℝ)) ≤ 4 * u := by
    nlinarith [Real.pi_lt_four, Real.pi_pos, NNReal.coe_nonneg v]
  have hpref : 1 / (4 * u) ≤ 1 / Real.sqrt (2 * Real.pi * (v : ℝ)) := by
    exact one_div_le_one_div_of_le (by positivity) hsqrt_le
  rw [ProbabilityTheory.gaussianPDFReal]
  simp only [NNReal.coe_eq_zero, hv, if_false, sub_zero]
  calc
    Real.exp (-256) / (4 * u) = (1 / (4 * u)) * Real.exp (-256) := by ring
    _ ≤ (1 / Real.sqrt (2 * Real.pi * (v : ℝ))) *
        Real.exp (-256) := by gcongr
    _ ≤ (1 / Real.sqrt (2 * Real.pi * (v : ℝ))) *
        Real.exp (-((|c| + h) ^ 2 / (2 * (v : ℝ)))) := by gcongr
    _ = _ := by ring

/-- Consequently a variance-regular macroblock has a reset probability bounded
below by a universal constant times `h / u`. -/
theorem gaussianReal_Icc_macroblock_lower (v : ℝ≥0) (c h u : ℝ)
    (hu : 0 < u) (hh : 0 ≤ h) (hhu : h ≤ u) (hc : |c| ≤ u)
    (hvlo : u ^ 2 / 128 ≤ (v : ℝ)) (hvhi : (v : ℝ) ≤ u ^ 2) :
    ENNReal.ofReal ((h / (2 * u)) * Real.exp (-256)) ≤
      ProbabilityTheory.gaussianReal 0 v (Set.Icc (c - h) (c + h)) := by
  have hvpos : 0 < (v : ℝ) := by
    have : 0 < u ^ 2 / 128 := by positivity
    exact this.trans_le hvlo
  have hv : v ≠ 0 := by exact_mod_cast ne_of_gt hvpos
  refine le_trans ?_ (gaussianReal_Icc_lower v hv c h hh)
  apply ENNReal.ofReal_le_ofReal
  have hdens := gaussianPDFReal_macroblock_lower v c h u hu hh hhu hc hvlo hvhi
  calc
    h / (2 * u) * Real.exp (-256) =
        (2 * h) * (Real.exp (-256) / (4 * u)) := by field_simp; ring
    _ ≤ (2 * h) * ProbabilityTheory.gaussianPDFReal 0 v (|c| + h) := by
      gcongr

/-- Gaussian bridge independence in the exact abstract form needed by a
macroblock argument.  If `cov(S,Y)=v` and `cov(Y,Y)=V`, then subtracting the
linear regression `(v/V)Y` from `S` makes it independent of the endpoint `Y`.
For partial sums of independent centered Gaussians, `v` is the prefix variance
and `V` is the block variance. -/
theorem gaussian_bridge_indep_endpoint
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {S Y : Ω → ℝ}
    (hSY : ProbabilityTheory.HasGaussianLaw (fun ω ↦ (S ω, Y ω)) P)
    (v V : ℝ) (hV : V ≠ 0)
    (hcov : ProbabilityTheory.covariance S Y P = v)
    (hYY : ProbabilityTheory.covariance Y Y P = V) :
    ProbabilityTheory.IndepFun (fun ω ↦ S ω - (v / V) * Y ω) Y P := by
  let c : ℝ := v / V
  let fst : ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  let snd : ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  let T : ℝ × ℝ →L[ℝ] ℝ × ℝ := (fst - c • snd).prod snd
  have hpair : ProbabilityTheory.HasGaussianLaw
      (fun ω ↦ (S ω - c * Y ω, Y ω)) P := by
    have hm := hSY.map_fun T
    simpa [T, fst, snd] using hm
  apply hpair.indepFun_of_covariance_eq_zero
  letI : IsProbabilityMeasure P := hSY.isProbabilityMeasure
  have hS2 : MemLp S 2 P := hSY.fst.memLp_two
  have hY2 : MemLp Y 2 P := hSY.snd.memLp_two
  have hcY2 : MemLp (c • Y) 2 P := hY2.const_smul c
  have hfun : (fun ω ↦ S ω - c * Y ω) = S - c • Y := by
    funext ω
    simp [Pi.smul_apply]
  rw [hfun, ProbabilityTheory.covariance_sub_left hS2 hcY2 hY2,
    ProbabilityTheory.covariance_smul_left, hcov, hYY]
  dsimp [c]
  field_simp
  ring

/-- A finite Gaussian vector is independent of a scalar Gaussian coordinate as
soon as every coordinate covariance vanishes.  This packages Mathlib's
vector-vector criterion with a one-coordinate target and is the form used for
the whole bridge path. -/
theorem gaussian_vector_indep_scalar_of_covariance_zero
    {Ω ι : Type*} [MeasurableSpace Ω] [Finite ι] {P : Measure Ω}
    {B : Ω → ι → ℝ} {Y : Ω → ℝ}
    (hBY : ProbabilityTheory.HasGaussianLaw (fun ω ↦ (B ω, Y ω)) P)
    (hcov : ∀ i, ProbabilityTheory.covariance (fun ω ↦ B ω i) Y P = 0) :
    ProbabilityTheory.IndepFun B Y P := by
  letI := Fintype.ofFinite ι
  let fst : (ι → ℝ) × ℝ →L[ℝ] (ι → ℝ) :=
    ContinuousLinearMap.fst ℝ (ι → ℝ) ℝ
  let snd : (ι → ℝ) × ℝ →L[ℝ] ℝ :=
    ContinuousLinearMap.snd ℝ (ι → ℝ) ℝ
  let T : (ι → ℝ) × ℝ →L[ℝ] (ι → ℝ) × (Fin 1 → ℝ) :=
    fst.prod (ContinuousLinearMap.pi fun _ : Fin 1 ↦ snd)
  have hvec : ProbabilityTheory.HasGaussianLaw
      (fun ω ↦ (B ω, fun _ : Fin 1 ↦ Y ω)) P := by
    have hm := hBY.map_fun T
    simpa [T, fst, snd] using hm
  have hindvec : ProbabilityTheory.IndepFun B
      (fun (ω : Ω) (_ : Fin 1) ↦ Y ω) P := by
    apply hvec.indepFun_of_covariance_eval
    intro i j
    simpa using hcov i
  have hc := hindvec.comp measurable_id (measurable_pi_apply (0 : Fin 1))
  simpa [Function.comp_def] using hc

/-- The complete finite Gaussian bridge is independent of its endpoint.  This
is the vector form needed to factor a path-tube event from the small endpoint
event. -/
theorem gaussian_bridge_process_indep_endpoint
    {Ω ι : Type*} [MeasurableSpace Ω] [Finite ι] {P : Measure Ω}
    {S : Ω → ι → ℝ} {Y : Ω → ℝ} (v : ι → ℝ) (V : ℝ) (hV : V ≠ 0)
    (hSY : ProbabilityTheory.HasGaussianLaw (fun ω ↦ (S ω, Y ω)) P)
    (hcov : ∀ i, ProbabilityTheory.covariance (fun ω ↦ S ω i) Y P = v i)
    (hYY : ProbabilityTheory.covariance Y Y P = V) :
    ProbabilityTheory.IndepFun
      (fun ω i ↦ S ω i - (v i / V) * Y ω) Y P := by
  letI := Fintype.ofFinite ι
  let fst : (ι → ℝ) × ℝ →L[ℝ] (ι → ℝ) :=
    ContinuousLinearMap.fst ℝ (ι → ℝ) ℝ
  let snd : (ι → ℝ) × ℝ →L[ℝ] ℝ :=
    ContinuousLinearMap.snd ℝ (ι → ℝ) ℝ
  let bridge : (ι → ℝ) × ℝ →L[ℝ] (ι → ℝ) :=
    ContinuousLinearMap.pi fun i ↦
      (ContinuousLinearMap.proj i).comp fst - (v i / V) • snd
  let T : (ι → ℝ) × ℝ →L[ℝ] (ι → ℝ) × ℝ := bridge.prod snd
  have hpair : ProbabilityTheory.HasGaussianLaw
      (fun ω ↦ (fun i ↦ S ω i - (v i / V) * Y ω, Y ω)) P := by
    have hm := hSY.map_fun T
    simpa [T, bridge, fst, snd] using hm
  apply gaussian_vector_indep_scalar_of_covariance_zero hpair
  intro i
  let c : ℝ := v i / V
  letI : IsProbabilityMeasure P := hSY.isProbabilityMeasure
  have hSi2 : MemLp (fun ω ↦ S ω i) 2 P := hSY.fst.eval i |>.memLp_two
  have hY2 : MemLp Y 2 P := hSY.snd.memLp_two
  have hcY2 : MemLp (c • Y) 2 P := hY2.const_smul c
  have hfun : (fun ω ↦ S ω i - c * Y ω) = (fun ω ↦ S ω i) - c • Y := by
    funext ω
    simp [Pi.smul_apply]
  rw [show (fun ω ↦ S ω i - (v i / V) * Y ω) =
      (fun ω ↦ S ω i - c * Y ω) by rfl,
    hfun, ProbabilityTheory.covariance_sub_left hSi2 hcY2 hY2,
    ProbabilityTheory.covariance_smul_left, hcov i, hYY]
  dsimp [c]
  field_simp
  ring

/-- Multiplicative lower bound for two events generated by independent random
variables.  This is used to combine a bridge-tube probability with the endpoint
interval bound. -/
theorem indepFun_measure_inter_preimage_lower
    {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    {P : Measure Ω} {X : Ω → A} {Y : Ω → B}
    (hXY : ProbabilityTheory.IndepFun X Y P)
    {s : Set A} {t : Set B} (hs : MeasurableSet s) (ht : MeasurableSet t)
    {a b : ℝ≥0∞} (ha : a ≤ P (X ⁻¹' s)) (hb : b ≤ P (Y ⁻¹' t)) :
    a * b ≤ P (X ⁻¹' s ∩ Y ⁻¹' t) := by
  rw [hXY.measure_inter_preimage_eq_mul s t hs ht]
  exact (mul_le_mul' ha hb)

/-- One Markov-style reset step obtained solely from independence.  If the
next independent increment has probability at least `p` of sending every
current state in `A` into `D`, then adjoining that increment costs at most the
factor `p`.  This is the Fubini lemma needed to iterate Gaussian block resets. -/
theorem indepFun_add_reset_lower
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {X Y : Ω → ℝ} (hXY : ProbabilityTheory.IndepFun X Y P)
    (hX : Measurable X) (hY : Measurable Y)
    {A D : Set ℝ} (hA : MeasurableSet A) (hD : MeasurableSet D)
    (p : ℝ≥0∞)
    (hreset : ∀ x ∈ A, p ≤ (P.map Y) {y | x + y ∈ D}) :
    p * P (X ⁻¹' A) ≤
      P {ω | X ω ∈ A ∧ X ω + Y ω ∈ D} := by
  let s : Set (ℝ × ℝ) := {z | z.1 ∈ A ∧ z.1 + z.2 ∈ D}
  have hs : MeasurableSet s :=
    (hA.preimage measurable_fst).inter
      (hD.preimage (measurable_fst.add measurable_snd))
  have hpair : P.map (fun ω ↦ (X ω, Y ω)) = (P.map X).prod (P.map Y) :=
    hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable
  change p * P (X ⁻¹' A) ≤ P ((fun ω ↦ (X ω, Y ω)) ⁻¹' s)
  rw [← Measure.map_apply (hX.prodMk hY) hs, hpair, Measure.prod_apply hs,
    ← Measure.map_apply hX hA]
  calc
    p * (P.map X) A = ∫⁻ _ in A, p ∂(P.map X) :=
      (setLIntegral_const A p).symm
    _ ≤ ∫⁻ x in A, (P.map Y) (Prod.mk x ⁻¹' s) ∂(P.map X) := by
      apply setLIntegral_mono (measurable_measure_prodMk_left hs)
      intro x hx
      simpa only [s, Set.mem_setOf_eq, hx, true_and, Set.preimage_setOf_eq] using
        hreset x hx
    _ ≤ ∫⁻ x, (P.map Y) (Prod.mk x ⁻¹' s) ∂(P.map X) :=
      setLIntegral_le_lintegral A _

/-- General transition form of `indepFun_add_reset_lower`, allowing the new
independent block to carry its complete path as well as its endpoint. -/
theorem indepFun_transition_lower
    {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    {P : Measure Ω} [IsFiniteMeasure P] {X : Ω → A} {Y : Ω → B}
    (hXY : ProbabilityTheory.IndepFun X Y P)
    (hX : Measurable X) (hY : Measurable Y)
    {s : Set A} {t : Set (A × B)} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (p : ℝ≥0∞)
    (hstep : ∀ x ∈ s, p ≤ (P.map Y) (Prod.mk x ⁻¹' t)) :
    p * P (X ⁻¹' s) ≤
      P (X ⁻¹' s ∩ (fun ω ↦ (X ω, Y ω)) ⁻¹' t) := by
  let u : Set (A × B) := (s ×ˢ Set.univ) ∩ t
  have hu : MeasurableSet u := (hs.prod MeasurableSet.univ).inter ht
  have hpair : P.map (fun ω ↦ (X ω, Y ω)) = (P.map X).prod (P.map Y) :=
    hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable
  have hevent : X ⁻¹' s ∩ (fun ω ↦ (X ω, Y ω)) ⁻¹' t =
      (fun ω ↦ (X ω, Y ω)) ⁻¹' u := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, u, Set.mem_prod, Set.mem_univ,
      and_true]
  rw [hevent, ← Measure.map_apply (hX.prodMk hY) hu, hpair,
    Measure.prod_apply hu, ← Measure.map_apply hX hs]
  calc
    p * (P.map X) s = ∫⁻ _ in s, p ∂(P.map X) :=
      (setLIntegral_const s p).symm
    _ ≤ ∫⁻ x in s, (P.map Y) (Prod.mk x ⁻¹' u) ∂(P.map X) := by
      apply setLIntegral_mono (measurable_measure_prodMk_left hu)
      intro x hx
      have hpre : Prod.mk x ⁻¹' u = Prod.mk x ⁻¹' t := by
        ext y
        simp only [Set.mem_preimage, u, Set.mem_inter_iff, Set.mem_prod,
          Set.mem_univ, and_true, hx, true_and]
      rw [hpre]
      exact hstep x hx
    _ ≤ ∫⁻ x, (P.map Y) (Prod.mk x ⁻¹' u) ∂(P.map X) :=
      setLIntegral_le_lintegral s _

/-- A variance-regular centered Gaussian increment resets any state in the
core interval `[-u/4,u/4]` back into that interval with a uniform probability. -/
theorem gaussian_independent_increment_core_reset_lower
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {X Y : Ω → ℝ} (hXY : ProbabilityTheory.IndepFun X Y P)
    (hX : Measurable X) (hY : Measurable Y)
    (v : ℝ≥0) (hYlaw : ProbabilityTheory.HasLaw Y
      (ProbabilityTheory.gaussianReal 0 v) P)
    (u : ℝ) (hu : 0 < u)
    (hvlo : u ^ 2 / 128 ≤ (v : ℝ)) (hvhi : (v : ℝ) ≤ u ^ 2 / 32) :
    ENNReal.ofReal ((1 / 8 : ℝ) * Real.exp (-256)) *
        P (X ⁻¹' Set.Icc (-u / 4) (u / 4)) ≤
      P {ω | X ω ∈ Set.Icc (-u / 4) (u / 4) ∧
        X ω + Y ω ∈ Set.Icc (-u / 4) (u / 4)} := by
  apply indepFun_add_reset_lower hXY hX hY measurableSet_Icc measurableSet_Icc
  intro x hx
  rw [hYlaw.map_eq]
  have hxabs : |x| ≤ u / 4 := by
    rcases hx with ⟨hxlo, hxhi⟩
    rw [abs_le]
    constructor <;> linarith
  have hset : {y : ℝ | x + y ∈ Set.Icc (-u / 4) (u / 4)} =
      Set.Icc (-x - u / 4) (-x + u / 4) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor <;> rintro ⟨hlo, hhi⟩ <;> constructor <;> linarith
  rw [hset]
  have hmacro := gaussianReal_Icc_macroblock_lower v (-x) (u / 4) u hu
    (by positivity) (by linarith)
    (by simpa only [abs_neg] using hxabs.trans (by linarith))
    hvlo (hvhi.trans (by nlinarith [sq_nonneg u]))
  convert hmacro using 1 <;> field_simp <;> ring

/-- The final reset can target a smaller endpoint interval `[-r,r]`; its cost
is linear in `r/u`, uniformly over the previous core state. -/
theorem gaussian_independent_increment_final_reset_lower
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {X Y : Ω → ℝ} (hXY : ProbabilityTheory.IndepFun X Y P)
    (hX : Measurable X) (hY : Measurable Y)
    (v : ℝ≥0) (hYlaw : ProbabilityTheory.HasLaw Y
      (ProbabilityTheory.gaussianReal 0 v) P)
    (u r : ℝ) (hu : 0 < u) (hr : 0 ≤ r) (hru : r ≤ u)
    (hvlo : u ^ 2 / 128 ≤ (v : ℝ)) (hvhi : (v : ℝ) ≤ u ^ 2 / 32) :
    ENNReal.ofReal ((r / (2 * u)) * Real.exp (-256)) *
        P (X ⁻¹' Set.Icc (-u / 4) (u / 4)) ≤
      P {ω | X ω ∈ Set.Icc (-u / 4) (u / 4) ∧
        X ω + Y ω ∈ Set.Icc (-r) r} := by
  apply indepFun_add_reset_lower hXY hX hY measurableSet_Icc measurableSet_Icc
  intro x hx
  rw [hYlaw.map_eq]
  have hxabs : |x| ≤ u / 4 := by
    rcases hx with ⟨hxlo, hxhi⟩
    rw [abs_le]
    constructor <;> linarith
  have hset : {y : ℝ | x + y ∈ Set.Icc (-r) r} =
      Set.Icc (-x - r) (-x + r) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor <;> rintro ⟨hlo, hhi⟩ <;> constructor <;> linarith
  rw [hset]
  exact gaussianReal_Icc_macroblock_lower v (-x) r u hu hr hru
    (by simpa only [abs_neg] using hxabs.trans (by linarith)) hvlo
    (hvhi.trans (by nlinarith [sq_nonneg u]))

/-- The numerical cost of one complete Gaussian macroblock is at least
`exp (-260)`.  Constants are deliberately rounded down for iteration. -/
lemma gaussian_macroblock_constant_lower :
    ENNReal.ofReal (Real.exp (-260)) ≤
      (1 / 2 : ℝ≥0∞) *
        ENNReal.ofReal ((1 / 8 : ℝ) * Real.exp (-256)) := by
  have heone : (2 : ℝ) ≤ Real.exp 1 := by
    nlinarith [Real.add_one_le_exp 1]
  have hfour : (16 : ℝ) ≤ Real.exp 4 := by
    calc
      (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) heone 4
      _ = Real.exp 4 := by
        rw [← Real.exp_nat_mul]
        norm_num
  have hnegfour : Real.exp (-4) ≤ (1 / 16 : ℝ) := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) hfour
  have hreal : Real.exp (-260) ≤
      (1 / 2 : ℝ) * ((1 / 8 : ℝ) * Real.exp (-256)) := by
    rw [show (-260 : ℝ) = -4 + -256 by norm_num, Real.exp_add]
    calc
      Real.exp (-4) * Real.exp (-256) ≤
          (1 / 16 : ℝ) * Real.exp (-256) := by gcongr
      _ = (1 / 2 : ℝ) * ((1 / 8 : ℝ) * Real.exp (-256)) := by ring
  have hof := ENNReal.ofReal_le_ofReal hreal
  have hhalf : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) := by
    symm
    simpa using (ENNReal.ofReal_div_of_pos (x := (1 : ℝ)) (y := 2) (by norm_num))
  rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (1 / 2 : ℝ)), ← hhalf] at hof
  exact hof

/-- Iteration of a uniform one-step probability lower bound. -/
theorem iterated_event_measure_lower
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (E : ℕ → Set Ω) (p : ℝ≥0∞) (hzero : E 0 = Set.univ)
    (hstep : ∀ k, p * P (E k) ≤ P (E (k + 1))) :
    ∀ m, p ^ m ≤ P (E m) := by
  intro m
  induction m with
  | zero =>
      simp only [pow_zero, hzero, measure_univ]
      exact le_rfl
  | succ m ih =>
      calc
        p ^ (m + 1) = p * p ^ m := by rw [pow_succ', mul_comm]
        _ ≤ p * P (E m) := mul_le_mul' le_rfl ih
        _ ≤ P (E (m + 1)) := hstep m

/-- Converting a macroblock count bounded by `1 + 128 V/u²` into the coarse
explicit exponential appearing in the finite Gaussian-walk bound. -/
lemma gaussian_block_count_exponential_lower (m : ℕ) (V u : ℝ)
    (hm : (m : ℝ) ≤ 1 + 128 * (V / u ^ 2)) :
    ENNReal.ofReal (Real.exp (-33280 * (1 + V / u ^ 2))) ≤
      ENNReal.ofReal (Real.exp (-260)) ^ m := by
  rw [← ENNReal.ofReal_pow (Real.exp_nonneg _), ← Real.exp_nat_mul]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  nlinarith

/-- The final-block path-and-endpoint factor is bounded below by the clean
linear prefactor `(r/u) * exp (-260)`. -/
lemma gaussian_final_macroblock_constant_lower (u r : ℝ)
    (hu : 0 < u) (hr : 0 ≤ r) :
    ENNReal.ofReal ((r / u) * Real.exp (-260)) ≤
      (1 / 2 : ℝ≥0∞) *
        ENNReal.ofReal ((r / (2 * u)) * Real.exp (-256)) := by
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by
    nlinarith [Real.add_one_le_exp 4]
  have hnegfour : Real.exp (-4) ≤ (1 / 4 : ℝ) := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) hfour
  have hreal : (r / u) * Real.exp (-260) ≤
      (1 / 2 : ℝ) * ((r / (2 * u)) * Real.exp (-256)) := by
    rw [show (-260 : ℝ) = -4 + -256 by norm_num, Real.exp_add]
    have hru : 0 ≤ r / u := div_nonneg hr hu.le
    calc
      (r / u) * (Real.exp (-4) * Real.exp (-256)) ≤
          (r / u) * ((1 / 4 : ℝ) * Real.exp (-256)) := by gcongr
      _ = (1 / 2 : ℝ) * ((r / (2 * u)) * Real.exp (-256)) := by ring
  have hof := ENNReal.ofReal_le_ofReal hreal
  have hhalf : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) := by
    symm
    simpa using (ENNReal.ofReal_div_of_pos (x := (1 : ℝ)) (y := 2) (by norm_num))
  rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (1 / 2 : ℝ)), ← hhalf] at hof
  exact hof

/-- Abstract finite Gaussian-walk iteration.  Once the variance-regular
macroblocks supply the one-step core and final reset estimates, this packages
them into the requested `r/u * exp (-C(1+V/u²))` lower bound with `C=33280`. -/
theorem gaussian_iterated_path_endpoint_lower
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (E : ℕ → Set Ω) (target : Set Ω) (m : ℕ) (V u r : ℝ)
    (hu : 0 < u) (hr : 0 ≤ r)
    (hcount : ((m + 1 : ℕ) : ℝ) ≤ 1 + 128 * (V / u ^ 2))
    (hzero : E 0 = Set.univ)
    (hstep : ∀ k,
      ((1 / 2 : ℝ≥0∞) *
          ENNReal.ofReal ((1 / 8 : ℝ) * Real.exp (-256))) * P (E k) ≤
        P (E (k + 1)))
    (hfinal : ((1 / 2 : ℝ≥0∞) *
        ENNReal.ofReal ((r / (2 * u)) * Real.exp (-256))) * P (E m) ≤
      P target) :
    ENNReal.ofReal ((r / u) *
        Real.exp (-33280 * (1 + V / u ^ 2))) ≤ P target := by
  let q : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-260))
  have hstepq : ∀ k, q * P (E k) ≤ P (E (k + 1)) := by
    intro k
    exact (mul_le_mul' gaussian_macroblock_constant_lower le_rfl).trans (hstep k)
  have hiter : q ^ m ≤ P (E m) :=
    iterated_event_measure_lower E q hzero hstepq m
  have hqcount : ENNReal.ofReal
      (Real.exp (-33280 * (1 + V / u ^ 2))) ≤ q ^ (m + 1) := by
    exact gaussian_block_count_exponential_lower (m + 1) V u hcount
  have hfinalconst : ENNReal.ofReal ((r / u) * Real.exp (-260)) ≤
      (1 / 2 : ℝ≥0∞) *
        ENNReal.ofReal ((r / (2 * u)) * Real.exp (-256)) :=
    gaussian_final_macroblock_constant_lower u r hu hr
  have hru : 0 ≤ r / u := div_nonneg hr hu.le
  rw [ENNReal.ofReal_mul hru]
  calc
    ENNReal.ofReal (r / u) *
        ENNReal.ofReal (Real.exp (-33280 * (1 + V / u ^ 2))) ≤
      ENNReal.ofReal (r / u) * q ^ (m + 1) :=
        mul_le_mul' le_rfl hqcount
    _ = (ENNReal.ofReal (r / u) * q) * q ^ m := by
      rw [pow_succ]
      ac_rfl
    _ = ENNReal.ofReal ((r / u) * Real.exp (-260)) * q ^ m := by
      rw [ENNReal.ofReal_mul hru]
    _ ≤ ((1 / 2 : ℝ≥0∞) *
          ENNReal.ofReal ((r / (2 * u)) * Real.exp (-256))) * P (E m) :=
      mul_le_mul' hfinalconst hiter
    _ ≤ P target := hfinal

/-- A fixed-block reset estimate once a bridge-tube event of probability at
least one half has been established.  In the block argument the preceding
Doob estimate supplies that one-half bound, while Gaussian bridge independence
supplies `hBY`. -/
theorem gaussian_bridge_endpoint_inter_lower
    {Ω ι : Type*} [MeasurableSpace Ω] [MeasurableSpace ι] {P : Measure Ω}
    {B : Ω → ι} {Y : Ω → ℝ} (v : ℝ≥0) (c h u : ℝ)
    (hBY : ProbabilityTheory.IndepFun B Y P)
    (hYlaw : ProbabilityTheory.HasLaw Y
      (ProbabilityTheory.gaussianReal 0 v) P)
    {tube : Set ι} (htube : MeasurableSet tube)
    (htube_mass : (1 / 2 : ℝ≥0∞) ≤ P (B ⁻¹' tube))
    (hu : 0 < u) (hh : 0 ≤ h) (hhu : h ≤ u) (hc : |c| ≤ u)
    (hvlo : u ^ 2 / 128 ≤ (v : ℝ)) (hvhi : (v : ℝ) ≤ u ^ 2) :
    (1 / 2 : ℝ≥0∞) *
        ENNReal.ofReal ((h / (2 * u)) * Real.exp (-256)) ≤
      P (B ⁻¹' tube ∩ Y ⁻¹' Set.Icc (c - h) (c + h)) := by
  apply indepFun_measure_inter_preimage_lower hBY htube measurableSet_Icc htube_mass
  calc
    ENNReal.ofReal ((h / (2 * u)) * Real.exp (-256)) ≤
        ProbabilityTheory.gaussianReal 0 v (Set.Icc (c - h) (c + h)) :=
      gaussianReal_Icc_macroblock_lower v c h u hu hh hhu hc hvlo hvhi
    _ = P (Y ⁻¹' Set.Icc (c - h) (c + h)) := by
      rw [← hYlaw.map_eq,
        Measure.map_apply_of_aemeasurable hYlaw.aemeasurable measurableSet_Icc]

/-- A small real-probability bad event gives an `ENNReal` lower bound for any
event containing its complement.  This is the final measure-theoretic glue in
the bridge-tube estimate. -/
theorem half_le_measure_of_compl_subset
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {bad good : Set Ω} (hbad_meas : MeasurableSet bad)
    (hbad : P.real bad ≤ 1 / 2) (hsub : badᶜ ⊆ good) :
    (1 / 2 : ℝ≥0∞) ≤ P good := by
  have hcompl : 1 / 2 ≤ P.real badᶜ := by
    rw [measureReal_compl hbad_meas, probReal_univ]
    linarith
  have hgood : 1 / 2 ≤ P.real good := hcompl.trans (measureReal_mono hsub)
  rw [← ofReal_measureReal]
  have hhalf : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) := by
    symm
    simpa using (ENNReal.ofReal_div_of_pos (x := (1 : ℝ)) (y := 2) (by norm_num))
  rw [hhalf]
  exact ENNReal.ofReal_le_ofReal hgood

/-- Deterministic bridge containment: if the original path and its endpoint
are both at most `u/4`, and every regression coefficient lies in `[0,1]`, then
the whole bridge is at most `u/2`. -/
lemma bridge_tube_of_path_and_endpoint_small
    {ι : Type*} {S : ι → ℝ} {Y u : ℝ} {q : ι → ℝ}
    (hu : 0 ≤ u) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (hS : ∀ i, |S i| ≤ u / 4) (hY : |Y| ≤ u / 4) :
    ∀ i, |S i - q i * Y| ≤ u / 2 := by
  intro i
  calc
    |S i - q i * Y| ≤ |S i| + |q i * Y| := abs_sub _ _
    _ = |S i| + q i * |Y| := by rw [abs_mul, abs_of_nonneg (hq0 i)]
    _ ≤ u / 4 + 1 * (u / 4) := by
      gcongr
      · exact hS i
      · exact hq1 i
    _ = u / 2 := by ring

/-- A convenient finite-horizon form of Doob's maximal inequality.  It is
stated for an arbitrary nonnegative submartingale because in the application
`f j = S_j^2`; proving that square process is a submartingale is independent
of the probability estimate below. -/
theorem doob_finite_maximal_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝒢 : MeasureTheory.Filtration ℕ ‹MeasurableSpace Ω›}
    {f : ℕ → Ω → ℝ} [IsFiniteMeasure P]
    (hsub : MeasureTheory.Submartingale f 𝒢 P) (hnonneg : 0 ≤ f)
    (n : ℕ) (u V : ℝ) (hu : 0 ≤ u)
    (hterminal : ∫ ω, f n ω ∂P ≤ V) :
    ENNReal.ofReal (u ^ 2) *
        P {ω | u ^ 2 ≤ (Finset.range (n + 1)).sup'
          Finset.nonempty_range_add_one (fun k ↦ f k ω)} ≤ ENNReal.ofReal V := by
  let ε : ℝ≥0 := ⟨u ^ 2, sq_nonneg u⟩
  let A : Set Ω := {ω | u ^ 2 ≤ (Finset.range (n + 1)).sup'
    Finset.nonempty_range_add_one (fun k ↦ f k ω)}
  have hmax := MeasureTheory.maximal_ineq hsub hnonneg (ε := ε) n
  have hfn_nonneg : 0 ≤ f n := hnonneg n
  have hrestrict : ∫ ω in A, f n ω ∂P ≤ ∫ ω, f n ω ∂P := by
    exact MeasureTheory.setIntegral_le_integral
      (hsub.integrable n) (Filter.Eventually.of_forall fun ω ↦ hfn_nonneg ω)
  have hA : ∫ ω in A, f n ω ∂P ≤ V := hrestrict.trans hterminal
  have hof : ENNReal.ofReal (∫ ω in A, f n ω ∂P) ≤ ENNReal.ofReal V :=
    ENNReal.ofReal_le_ofReal hA
  change ENNReal.ofReal (u ^ 2) * P A ≤ ENNReal.ofReal V
  have hε : (ε : ℝ≥0∞) = ENNReal.ofReal (u ^ 2) := by
    rw [ENNReal.coe_nnreal_eq]
    rfl
  rw [← hε]
  exact hmax.trans hof

/-- Squaring a real `L²` martingale gives a nonnegative submartingale.  This is
the exact input needed by `doob_finite_maximal_bound`. -/
theorem martingale_sq_submartingale
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝒢 : MeasureTheory.Filtration ℕ ‹MeasurableSpace Ω›}
    {S : ℕ → Ω → ℝ} [IsFiniteMeasure P]
    (hS : MeasureTheory.Martingale S 𝒢 P)
    (hL2 : ∀ j, MemLp (S j) 2 P) :
    MeasureTheory.Submartingale (fun j ω ↦ (S j ω) ^ 2) 𝒢 P := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    have hmul := (hS.stronglyMeasurable j).mul (hS.stronglyMeasurable j)
    have heq : S j * S j = (fun ω ↦ (S j ω) ^ 2) := by
      funext ω
      simp [pow_two]
    rw [heq] at hmul
    exact hmul
  · intro i j hij
    have hjensen :=
      (show Even (2 : ℕ) by norm_num).convexOn_pow.map_condExp_le_univ
        (𝒢.le i) (continuous_pow 2).lowerSemicontinuous
        (hS.integrable j) (hL2 j).integrable_sq
    have hcomp : ((fun x : ℝ ↦ x ^ 2) ∘ S j) = (fun ω ↦ (S j ω) ^ 2) := rfl
    rw [hcomp] at hjensen
    filter_upwards [hS.condExp_ae_eq hij, hjensen] with ω hmart hjens
    simpa only [Function.comp_apply, hmart] using hjens
  · intro j
    exact (hL2 j).integrable_sq

/-- L² maximal inequality for a finite real martingale, expressed directly in
terms of the squared partial sums. -/
theorem martingale_finite_sq_maximal_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝒢 : MeasureTheory.Filtration ℕ ‹MeasurableSpace Ω›}
    {S : ℕ → Ω → ℝ} [IsFiniteMeasure P]
    (hS : MeasureTheory.Martingale S 𝒢 P)
    (hL2 : ∀ j, MemLp (S j) 2 P)
    (n : ℕ) (u V : ℝ) (hu : 0 ≤ u)
    (hterminal : ∫ ω, (S n ω) ^ 2 ∂P ≤ V) :
    ENNReal.ofReal (u ^ 2) *
        P {ω | u ^ 2 ≤ (Finset.range (n + 1)).sup'
          Finset.nonempty_range_add_one (fun k ↦ (S k ω) ^ 2)} ≤
      ENNReal.ofReal V := by
  exact doob_finite_maximal_bound
    (martingale_sq_submartingale hS hL2) (fun _ _ ↦ sq_nonneg _)
    n u V hu hterminal

/-- Real-valued version of the preceding L² maximal inequality. -/
theorem martingale_finite_sq_maximal_bound_real
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝒢 : MeasureTheory.Filtration ℕ ‹MeasurableSpace Ω›}
    {S : ℕ → Ω → ℝ} [IsFiniteMeasure P]
    (hS : MeasureTheory.Martingale S 𝒢 P)
    (hL2 : ∀ j, MemLp (S j) 2 P)
    (n : ℕ) (u V : ℝ) (hu : 0 < u) (hV : 0 ≤ V)
    (hterminal : ∫ ω, (S n ω) ^ 2 ∂P ≤ V) :
    P.real {ω | u ^ 2 ≤ (Finset.range (n + 1)).sup'
          Finset.nonempty_range_add_one (fun k ↦ (S k ω) ^ 2)} ≤
      V / u ^ 2 := by
  have h := martingale_finite_sq_maximal_bound hS hL2 n u V hu.le hterminal
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg u),
    ENNReal.toReal_ofReal hV] at ht
  change u ^ 2 * P.real {ω | u ^ 2 ≤ (Finset.range (n + 1)).sup'
      Finset.nonempty_range_add_one (fun k ↦ (S k ω) ^ 2)} ≤ V at ht
  apply (le_div_iff₀ (sq_pos_of_pos hu)).2
  simpa only [mul_comm] using ht

/-- If the terminal second moment of a real martingale is at most `u²/32`,
then every deterministic regression bridge with coefficients in `[0,1]`
stays in the tube of radius `u/2` with probability at least one half.  This is
the fixed-small-variance bridge input used for Gaussian macroblocks. -/
theorem martingale_bridge_tube_mass_ge_half
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝒢 : MeasureTheory.Filtration ℕ ‹MeasurableSpace Ω›}
    {S : ℕ → Ω → ℝ} [IsProbabilityMeasure P]
    (hS : MeasureTheory.Martingale S 𝒢 P)
    (hL2 : ∀ j, MemLp (S j) 2 P)
    (n : ℕ) (q : Fin (n + 1) → ℝ) (u V : ℝ)
    (hu : 0 < u) (hV : 0 ≤ V) (hVsmall : V ≤ u ^ 2 / 32)
    (hterminal : ∫ ω, (S n ω) ^ 2 ∂P ≤ V)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) :
    (1 / 2 : ℝ≥0∞) ≤ P {ω | ∀ i : Fin (n + 1),
      |S i.1 ω - q i * S n ω| ≤ u / 2} := by
  let bad : Set Ω := {ω | (u / 4) ^ 2 ≤
    (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k ↦ (S k ω) ^ 2)}
  have hbad_meas : MeasurableSet bad := by
    exact measurableSet_le measurable_const
      (Finset.measurable_range_sup'' fun k _ ↦
        ((hS.stronglyMeasurable k).measurable.le (𝒢.le k)).pow_const 2)
  apply half_le_measure_of_compl_subset hbad_meas
  · calc
      P.real bad ≤ V / (u / 4) ^ 2 :=
        martingale_finite_sq_maximal_bound_real hS hL2 n (u / 4) V
          (by positivity) hV hterminal
      _ ≤ 1 / 2 := by
        apply (div_le_iff₀ (by positivity : 0 < (u / 4) ^ 2)).2
        nlinarith [sq_nonneg u]
  · intro ω hω
    have hsup : (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k ↦ (S k ω) ^ 2) < (u / 4) ^ 2 := by
      exact lt_of_not_ge hω
    have hpath : ∀ i : Fin (n + 1), |S i.1 ω| ≤ u / 4 := by
      intro i
      have hi : i.1 ∈ Finset.range (n + 1) := Finset.mem_range.mpr i.2
      have hle := Finset.le_sup' (fun k ↦ (S k ω) ^ 2) hi
      have hsq : (S i.1 ω) ^ 2 < (u / 4) ^ 2 := hle.trans_lt hsup
      have habs : |S i.1 ω| < |u / 4| := sq_lt_sq.mp hsq
      exact le_of_lt (by simpa [abs_of_pos (by positivity : 0 < u / 4)] using habs)
    have hend : |S n ω| ≤ u / 4 :=
      hpath ⟨n, Nat.lt_succ_self n⟩
    exact bridge_tube_of_path_and_endpoint_small hu.le hq0 hq1 hpath hend

/-- A coordinatewise closed tube is measurable in a finite real product. -/
lemma measurableSet_pi_abs_le {ι : Type*} [Finite ι] (r : ℝ) :
    MeasurableSet {x : ι → ℝ | ∀ i, |x i| ≤ r} := by
  letI := Fintype.ofFinite ι
  rw [show {x : ι → ℝ | ∀ i, |x i| ≤ r} =
      ⋂ i, {x | |x i| ≤ r} by ext x; simp]
  exact MeasurableSet.iInter fun i ↦ by
    exact measurableSet_le (measurable_pi_apply i).abs measurable_const

/-- A complete scalar Gaussian macroblock reset estimate.  For a centered
Gaussian martingale whose block variance lies between `u²/128` and `u²/32`,
the path remains in radius `u` and the endpoint lands in a prescribed interval
of radius `h` around any `c` with `|c| ≤ u/4`, with an explicit universal
lower bound. -/
theorem gaussian_martingale_path_endpoint_lower
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝒢 : MeasureTheory.Filtration ℕ ‹MeasurableSpace Ω›}
    {S : ℕ → Ω → ℝ} [IsProbabilityMeasure P]
    (hS : MeasureTheory.Martingale S 𝒢 P)
    (hL2 : ∀ j, MemLp (S j) 2 P)
    (n : ℕ) (v : ℝ≥0) (prefixVar : Fin (n + 1) → ℝ)
    (hjoint : ProbabilityTheory.HasGaussianLaw
      (fun ω ↦ (fun i : Fin (n + 1) ↦ S i.1 ω, S n ω)) P)
    (hcov : ∀ i, ProbabilityTheory.covariance (fun ω ↦ S i.1 ω) (S n) P =
      prefixVar i)
    (hYY : ProbabilityTheory.covariance (S n) (S n) P = (v : ℝ))
    (hYlaw : ProbabilityTheory.HasLaw (S n)
      (ProbabilityTheory.gaussianReal 0 v) P)
    (hq0 : ∀ i, 0 ≤ prefixVar i / (v : ℝ))
    (hq1 : ∀ i, prefixVar i / (v : ℝ) ≤ 1)
    (u c h : ℝ) (hu : 0 < u) (hh : 0 ≤ h) (hhu : h ≤ u / 4)
    (hc : |c| ≤ u / 4)
    (hvlo : u ^ 2 / 128 ≤ (v : ℝ)) (hvhi : (v : ℝ) ≤ u ^ 2 / 32)
    (hterminal : ∫ ω, (S n ω) ^ 2 ∂P ≤ (v : ℝ)) :
    (1 / 2 : ℝ≥0∞) *
        ENNReal.ofReal ((h / (2 * u)) * Real.exp (-256)) ≤
      P {ω | (∀ i : Fin (n + 1), |S i.1 ω| ≤ u) ∧
        S n ω ∈ Set.Icc (c - h) (c + h)} := by
  let q : Fin (n + 1) → ℝ := fun i ↦ prefixVar i / (v : ℝ)
  let B : Ω → Fin (n + 1) → ℝ := fun ω i ↦ S i.1 ω - q i * S n ω
  let tube : Set (Fin (n + 1) → ℝ) :=
    {x | ∀ i, |x i| ≤ u / 2}
  have hvpos : 0 < (v : ℝ) := by
    have : 0 < u ^ 2 / 128 := by positivity
    exact this.trans_le hvlo
  have hvne : (v : ℝ) ≠ 0 := ne_of_gt hvpos
  have hBindep : ProbabilityTheory.IndepFun B (S n) P := by
    exact gaussian_bridge_process_indep_endpoint prefixVar (v : ℝ) hvne
      hjoint hcov hYY
  have htube_meas : MeasurableSet tube := by
    exact measurableSet_pi_abs_le (u / 2)
  have htube_mass : (1 / 2 : ℝ≥0∞) ≤ P (B ⁻¹' tube) := by
    simpa only [B, tube, Set.preimage_setOf_eq] using
      martingale_bridge_tube_mass_ge_half hS hL2 n q u (v : ℝ) hu
        (NNReal.coe_nonneg v) hvhi hterminal
        (by simpa only [q] using hq0) (by simpa only [q] using hq1)
  have hinter := gaussian_bridge_endpoint_inter_lower v c h u hBindep hYlaw
    htube_meas htube_mass hu hh (by linarith) (by linarith) hvlo
    (hvhi.trans (by nlinarith [sq_nonneg u]))
  refine hinter.trans (measure_mono ?_)
  rintro ω ⟨hBtube, hYinterval⟩
  have hYabs : |S n ω| ≤ u / 2 := by
    have hcenter : |S n ω| ≤ |c| + h := by
      rcases hYinterval with ⟨hlo, hhi⟩
      rw [abs_le]
      constructor <;> nlinarith [le_abs_self c, neg_abs_le c]
    linarith
  refine ⟨?_, hYinterval⟩
  intro i
  have hBabs : |B ω i| ≤ u / 2 := hBtube i
  calc
    |S i.1 ω| = |B ω i + q i * S n ω| := by
      congr 1
      simp only [B]
      ring
    _ ≤ |B ω i| + |q i * S n ω| := abs_add_le _ _
    _ = |B ω i| + q i * |S n ω| := by
      rw [abs_mul, abs_of_nonneg (hq0 i)]
    _ ≤ u / 2 + 1 * (u / 2) := by
      apply add_le_add hBabs
      exact mul_le_mul (hq1 i) hYabs (abs_nonneg _) (by norm_num)
    _ = u := by ring

/-- One fully path-aware adaptive reset step.  A measurable past state in the
core interval is independent of a variance-regular Gaussian martingale block;
the block keeps every translated partial sum within `5u/4` and returns its
translated endpoint to the core at the same universal macroblock cost. -/
theorem gaussian_martingale_adaptive_core_step_lower
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝒢 : MeasureTheory.Filtration ℕ ‹MeasurableSpace Ω›}
    {S : ℕ → Ω → ℝ} {X : Ω → A} {state : A → ℝ}
    (hX : Measurable X) (hstate : Measurable state)
    (hS : MeasureTheory.Martingale S 𝒢 P)
    (hL2 : ∀ j, MemLp (S j) 2 P)
    (n : ℕ) (v : ℝ≥0) (prefixVar : Fin (n + 1) → ℝ)
    (hjoint : ProbabilityTheory.HasGaussianLaw
      (fun ω ↦ (fun i : Fin (n + 1) ↦ S i.1 ω, S n ω)) P)
    (hcov : ∀ i, ProbabilityTheory.covariance (fun ω ↦ S i.1 ω) (S n) P =
      prefixVar i)
    (hYY : ProbabilityTheory.covariance (S n) (S n) P = (v : ℝ))
    (hYlaw : ProbabilityTheory.HasLaw (S n)
      (ProbabilityTheory.gaussianReal 0 v) P)
    (hq0 : ∀ i, 0 ≤ prefixVar i / (v : ℝ))
    (hq1 : ∀ i, prefixVar i / (v : ℝ) ≤ 1)
    (u : ℝ) (hu : 0 < u)
    (hvlo : u ^ 2 / 128 ≤ (v : ℝ)) (hvhi : (v : ℝ) ≤ u ^ 2 / 32)
    (hterminal : ∫ ω, (S n ω) ^ 2 ∂P ≤ (v : ℝ))
    {pastGood : Set A} (hpast_meas : MeasurableSet pastGood)
    (hpast_core : ∀ x ∈ pastGood, |state x| ≤ u / 4)
    (hindep : ProbabilityTheory.IndepFun X
      (fun (ω : Ω) (i : Fin (n + 1)) ↦ S i.1 ω) P) :
    ((1 / 2 : ℝ≥0∞) *
        ENNReal.ofReal ((1 / 8 : ℝ) * Real.exp (-256))) *
        P (X ⁻¹' pastGood) ≤
      P (X ⁻¹' pastGood ∩ {ω |
        (∀ i : Fin (n + 1), |state (X ω) + S i.1 ω| ≤ 5 * u / 4) ∧
        state (X ω) + S n ω ∈ Set.Icc (-u / 4) (u / 4)}) := by
  let W : Ω → Fin (n + 1) → ℝ := fun ω i ↦ S i.1 ω
  let transition : Set (A × (Fin (n + 1) → ℝ)) := {z |
    (∀ i, |state z.1 + z.2 i| ≤ 5 * u / 4) ∧
      state z.1 + z.2 ⟨n, Nat.lt_succ_self n⟩ ∈ Set.Icc (-u / 4) (u / 4)}
  have hW : Measurable W := measurable_pi_iff.mpr fun i ↦
    (hS.stronglyMeasurable i.1).measurable.le (𝒢.le i.1)
  have htransition : MeasurableSet transition := by
    have hpath : MeasurableSet {z : A × (Fin (n + 1) → ℝ) |
        ∀ i, |state z.1 + z.2 i| ≤ 5 * u / 4} := by
      rw [show {z : A × (Fin (n + 1) → ℝ) |
          ∀ i, |state z.1 + z.2 i| ≤ 5 * u / 4} =
          ⋂ i, {z | |state z.1 + z.2 i| ≤ 5 * u / 4} by ext z; simp]
      exact MeasurableSet.iInter fun i ↦ measurableSet_le
        ((hstate.comp measurable_fst).add
          ((measurable_pi_apply i).comp measurable_snd) |>.abs) measurable_const
    exact hpath.inter (measurableSet_Icc.preimage
      ((hstate.comp measurable_fst).add
        ((measurable_pi_apply (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))).comp
          measurable_snd)))
  apply indepFun_transition_lower hindep hX hW hpast_meas htransition
  intro x hx
  have hxcore := hpast_core x hx
  have hblock := gaussian_martingale_path_endpoint_lower hS hL2 n v prefixVar
    hjoint hcov hYY hYlaw hq0 hq1 u (-state x) (u / 4) hu
    (by positivity) (by linarith) (by simpa only [abs_neg] using hxcore)
    hvlo hvhi hterminal
  have hp_eq : ENNReal.ofReal ((u / 4 / (2 * u)) * Real.exp (-256)) =
      ENNReal.ofReal ((1 / 8 : ℝ) * Real.exp (-256)) := by
    congr 1
    field_simp
    ring
  rw [hp_eq] at hblock
  refine hblock.trans ?_
  rw [Measure.map_apply hW (measurable_prodMk_left htransition)]
  apply measure_mono
  rintro ω ⟨hpath, hend⟩
  constructor
  · intro i
    calc
      |state x + S i.1 ω| ≤ |state x| + |S i.1 ω| := abs_add_le _ _
      _ ≤ u / 4 + u := add_le_add hxcore (hpath i)
      _ = 5 * u / 4 := by ring
  · rcases hend with ⟨hendlo, hendhi⟩
    constructor <;> linarith

/-- Partial sums through time `n` (inclusive).  The inclusive convention aligns
the process with Mathlib's natural filtration, which contains coordinate `n`
at time `n`. -/
noncomputable def partialSum (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), X k ω

/-- Partial sums of independent centered integrable variables form a
martingale for their natural filtration. -/
theorem iIndepFun_martingale_partialSum
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ}
    (hXmeas : ∀ k, StronglyMeasurable (X k))
    (hXindep : ProbabilityTheory.iIndepFun X P)
    (hXint : ∀ k, Integrable (X k) P)
    (hXmean : ∀ k, ∫ ω, X k ω ∂P = 0) :
    MeasureTheory.Martingale (partialSum X)
      (MeasureTheory.Filtration.natural X hXmeas) P := by
  let 𝒢 := MeasureTheory.Filtration.natural X hXmeas
  letI : IsProbabilityMeasure P := hXindep.isProbabilityMeasure
  have hnat : MeasureTheory.StronglyAdapted 𝒢 X :=
    MeasureTheory.Filtration.stronglyAdapted_natural hXmeas
  constructor
  · intro n
    have hs : StronglyMeasurable[𝒢 n] (∑ k ∈ Finset.range (n + 1), X k) := by
      apply Finset.stronglyMeasurable_sum
      intro k hk
      apply (hnat k).mono
      apply 𝒢.mono
      have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      exact hk'
    have heq : (∑ k ∈ Finset.range (n + 1), X k) = partialSum X n := by
      funext ω
      simp only [partialSum, Finset.sum_apply]
    rw [heq] at hs
    exact hs
  · intro i j hij
    have hleft : partialSum X j = ∑ k ∈ Finset.range (j + 1), X k := by
      funext ω
      simp only [partialSum, Finset.sum_apply]
    have hright : partialSum X i = ∑ k ∈ Finset.range (i + 1), X k := by
      funext ω
      simp only [partialSum, Finset.sum_apply]
    rw [hleft, hright]
    have hsum := MeasureTheory.condExp_finsetSum
      (μ := P) (s := Finset.range (j + 1))
      (fun k _ ↦ hXint k) (𝒢 i)
    refine hsum.trans ?_
    have hterms : ∀ k ∈ Finset.range (j + 1),
        P[X k | 𝒢 i] =ᵐ[P] if k ≤ i then X k else 0 := by
      intro k hk
      by_cases hki : k ≤ i
      · simp only [hki, if_true]
        exact Filter.EventuallyEq.of_eq <|
          MeasureTheory.condExp_of_stronglyMeasurable
            (𝒢.le i) ((hnat k).mono (𝒢.mono hki)) (hXint k)
      · have hik : i < k := Nat.lt_of_not_ge hki
        have hind := hXindep.condExp_natural_ae_eq_of_lt hXmeas hik
        simp only [hki, if_false]
        filter_upwards [hind] with ω hω
        rw [hω, hXmean k]
        rfl
    refine (eventuallyEq_sum hterms).trans ?_
    filter_upwards with ω
    simp only [Finset.sum_apply, ite_apply, Pi.zero_apply]
    rw [← Finset.sum_filter]
    have hrange : (Finset.range (j + 1)).filter (fun k ↦ k ≤ i) =
        Finset.range (i + 1) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [hrange]

/-- Maximal inequality specialized to partial sums of independent centered
`L²` variables.  The only remaining model-specific input is the terminal
second-moment estimate. -/
theorem iIndepFun_partialSum_sq_maximal_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ}
    (hXmeas : ∀ k, StronglyMeasurable (X k))
    (hXindep : ProbabilityTheory.iIndepFun X P)
    (hX2 : ∀ k, MemLp (X k) 2 P)
    (hXmean : ∀ k, ∫ ω, X k ω ∂P = 0)
    (n : ℕ) (u V : ℝ) (hu : 0 ≤ u)
    (hterminal : ∫ ω, (partialSum X n ω) ^ 2 ∂P ≤ V) :
    ENNReal.ofReal (u ^ 2) *
        P {ω | u ^ 2 ≤ (Finset.range (n + 1)).sup'
          Finset.nonempty_range_add_one (fun k ↦ (partialSum X k ω) ^ 2)} ≤
      ENNReal.ofReal V := by
  letI : IsProbabilityMeasure P := hXindep.isProbabilityMeasure
  have hM := iIndepFun_martingale_partialSum hXmeas hXindep
    (fun k ↦ (hX2 k).integrable one_le_two) hXmean
  have hS2 : ∀ j, MemLp (partialSum X j) 2 P := by
    intro j
    change MemLp (fun ω ↦ ∑ k ∈ Finset.range (j + 1), X k ω) 2 P
    exact memLp_finsetSum (Finset.range (j + 1)) (fun k _ ↦ hX2 k)
  exact martingale_finite_sq_maximal_bound hM hS2 n u V hu hterminal


end ScalarGaussianPath

end Erdos527

namespace Erdos527
namespace GaussianDecoupling

open scoped ENNReal NNReal Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Finset

noncomputable def innerFamilyCLM {H ι : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Fintype ι] (c : ι → H) : H →L[ℝ] EuclideanSpace ℝ ι :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i ↦ (innerSL ℝ) (c i))

@[simp] lemma innerFamilyCLM_apply {H ι : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Fintype ι] (c : ι → H) (x : H) (i : ι) :
    innerFamilyCLM c x i = inner ℝ (c i) x := by
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma map_innerFamilyCLM_stdGaussian_eq_of_gram_eq
    {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    [Fintype ι] [DecidableEq ι] (c d : ι → H)
    (hgram : ∀ i j, inner ℝ (c i) (c j) = inner ℝ (d i) (d j)) :
    (stdGaussian H).map (innerFamilyCLM c) =
      (stdGaussian H).map (innerFamilyCLM d) := by
  apply IsGaussian.ext
  · rw [integral_map (by fun_prop) (by fun_prop),
      integral_map (by fun_prop) (by fun_prop)]
    simp only [id_eq]
    rw [(innerFamilyCLM c).integral_comp_id_comm IsGaussian.integrable_id,
      (innerFamilyCLM d).integral_comp_id_comm IsGaussian.integrable_id,
      integral_id_stdGaussian]
    simp
  rw [← ContinuousLinearMap.toBilinForm_inj]
  refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun ι ℝ).toBasis fun i j ↦ ?_
  simp only [ContinuousLinearMap.toBilinForm_apply]
  rw [covarianceBilin_map IsGaussian.memLp_two_id,
    covarianceBilin_map IsGaussian.memLp_two_id,
    covarianceBilin_stdGaussian]
  have hadj (e : ι → H) (k : ι) :
      ContinuousLinearMap.adjoint (innerFamilyCLM e)
          ((EuclideanSpace.basisFun ι ℝ).toBasis k) = e k := by
    apply ext_inner_right ℝ
    intro x
    rw [ContinuousLinearMap.adjoint_inner_left]
    simp [innerFamilyCLM_apply, PiLp.inner_apply]
  rw [hadj c i, hadj c j, hadj d i, hadj d j]
  exact hgram i j

lemma integral_abs_inner_stdGaussian_le_norm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] (c : H) :
    ∫ x : H, |inner ℝ c x| ∂(stdGaussian H) ≤ ‖c‖ := by
  by_cases hc : c = 0
  · simp [hc]
  let L : StrongDual ℝ H := (innerSL ℝ) c
  have hL : ‖L‖ = ‖c‖ := by simp [L]
  have hX : MemLp (fun x : H ↦ L x) 2 (stdGaussian H) :=
    IsGaussian.memLp_dual (stdGaussian H) L 2 (by norm_num)
  have hsq : ∫ x : H, (L x) ^ 2 ∂(stdGaussian H) = ‖c‖ ^ 2 := by
    have hv := variance_dual_stdGaussian L
    rw [variance_eq_integral hX.aemeasurable,
      integral_strongDual_stdGaussian] at hv
    simpa [hL] using hv
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hmaj (x : H) :
      |L x| ≤ (((L x) ^ 2 / ‖c‖) + ‖c‖) / 2 := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2)).2
    have heq : (L x) ^ 2 / ‖c‖ + ‖c‖ =
        ((L x) ^ 2 + ‖c‖ ^ 2) / ‖c‖ := by
      field_simp
    rw [heq, le_div_iff₀ hcpos]
    nlinarith [sq_nonneg (|L x| - ‖c‖), sq_abs (L x)]
  have hLint : Integrable (fun x : H ↦ L x) (stdGaussian H) :=
    hX.integrable (by norm_num)
  have hright : Integrable
      (fun x : H ↦ (((L x) ^ 2 / ‖c‖) + ‖c‖) / 2)
      (stdGaussian H) := by
    exact ((hX.integrable_sq.div_const _).add (integrable_const _)).div_const _
  calc
    (∫ x : H, |inner ℝ c x| ∂(stdGaussian H)) =
        ∫ x : H, |L x| ∂(stdGaussian H) := by rfl
    _ ≤ ∫ x : H, (((L x) ^ 2 / ‖c‖) + ‖c‖) / 2 ∂(stdGaussian H) :=
      integral_mono hLint.abs hright hmaj
    _ = ‖c‖ := by
      rw [integral_div, integral_add, integral_div, hsq, integral_const]
      simp only [probReal_univ, one_smul]
      · field_simp
        norm_num
      · exact hX.integrable_sq.div_const _
      · exact integrable_const _

lemma euclidean_norm_le_sum_abs {ι : Type*} [Fintype ι]
    (x : EuclideanSpace ℝ ι) : ‖x‖ ≤ ∑ i, |x i| := by
  have hsum : 0 ≤ ∑ i, |x i| := sum_nonneg fun _ _ ↦ abs_nonneg _
  rw [← sq_le_sq₀ (norm_nonneg x) hsum, EuclideanSpace.real_norm_sq_eq]
  simpa [sq_abs] using
    (sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
      (f := fun i ↦ |x i|) (fun _ _ ↦ abs_nonneg _))

lemma integral_norm_innerFamilyCLM_le_sum_norm
    {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    [Fintype ι] (c : ι → H) :
    ∫ x : H, ‖innerFamilyCLM c x‖ ∂(stdGaussian H) ≤ ∑ i, ‖c i‖ := by
  have hcoord (i : ι) : Integrable (fun x : H ↦ |inner ℝ (c i) x|)
      (stdGaussian H) := by
    exact (IsGaussian.integrable_dual (stdGaussian H) ((innerSL ℝ) (c i))).abs
  calc
    (∫ x : H, ‖innerFamilyCLM c x‖ ∂(stdGaussian H)) ≤
        ∫ x : H, ∑ i, |inner ℝ (c i) x| ∂(stdGaussian H) := by
      apply integral_mono
      · exact ((innerFamilyCLM c).integrable_comp IsGaussian.integrable_id).norm
      · exact integrable_finsetSum _ fun i _ ↦ hcoord i
      · intro x
        simpa [innerFamilyCLM_apply] using euclidean_norm_le_sum_abs (innerFamilyCLM c x)
    _ = ∑ i, ∫ x : H, |inner ℝ (c i) x| ∂(stdGaussian H) := by
      exact integral_finsetSum _ fun i _ ↦ hcoord i
    _ ≤ ∑ i, ‖c i‖ := sum_le_sum fun i _ ↦ integral_abs_inner_stdGaussian_le_norm (c i)

lemma integrable_lipschitz_comp_innerFamilyCLM
    {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    [Fintype ι] (c : ι → H) {K : ℝ≥0}
    (f : EuclideanSpace ℝ ι → ℝ) (hf : LipschitzWith K f) :
    Integrable (fun x : H ↦ f (innerFamilyCLM c x)) (stdGaussian H) := by
  have hL : Integrable (fun x : H ↦ ‖innerFamilyCLM c x‖) (stdGaussian H) :=
    ((innerFamilyCLM c).integrable_comp IsGaussian.integrable_id).norm
  apply Integrable.mono'
      ((integrable_const (|f 0|)).add (hL.const_mul (K : ℝ)))
      (hf.continuous.comp (innerFamilyCLM c).continuous).aestronglyMeasurable
  filter_upwards with x
  calc
    ‖f (innerFamilyCLM c x)‖ ≤ ‖f (innerFamilyCLM c x) - f 0‖ + ‖f 0‖ := by
      simpa using norm_add_le (f (innerFamilyCLM c x) - f 0) (f 0)
    _ ≤ (K : ℝ) * ‖innerFamilyCLM c x‖ + ‖f 0‖ := by
      gcongr
      simpa using hf.norm_sub_le (innerFamilyCLM c x) 0
    _ = |f 0| + (K : ℝ) * ‖innerFamilyCLM c x‖ := by
      rw [Real.norm_eq_abs]
      ring

theorem integral_lipschitz_innerFamilyCLM_sub_le
    {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    [Fintype ι] (c d : ι → H) {K : ℝ≥0}
    (f : EuclideanSpace ℝ ι → ℝ) (hf : LipschitzWith K f) :
    |(∫ x : H, f (innerFamilyCLM c x) ∂(stdGaussian H)) -
        ∫ x : H, f (innerFamilyCLM d x) ∂(stdGaussian H)| ≤
      (K : ℝ) * ∑ i, ‖c i - d i‖ := by
  let e : ι → H := fun i ↦ c i - d i
  have hc := integrable_lipschitz_comp_innerFamilyCLM c f hf
  have hd := integrable_lipschitz_comp_innerFamilyCLM d f hf
  have heint : Integrable (fun x : H ↦ ‖innerFamilyCLM e x‖) (stdGaussian H) :=
    ((innerFamilyCLM e).integrable_comp IsGaussian.integrable_id).norm
  rw [← integral_sub hc hd]
  calc
    |∫ x : H, (f (innerFamilyCLM c x) - f (innerFamilyCLM d x))
        ∂(stdGaussian H)| ≤
        ∫ x : H, |f (innerFamilyCLM c x) - f (innerFamilyCLM d x)|
          ∂(stdGaussian H) := abs_integral_le_integral_abs
    _ ≤ ∫ x : H, (K : ℝ) * ‖innerFamilyCLM e x‖ ∂(stdGaussian H) := by
      apply integral_mono (hc.sub hd).abs (heint.const_mul _)
      intro x
      calc
        |f (innerFamilyCLM c x) - f (innerFamilyCLM d x)| =
            ‖f (innerFamilyCLM c x) - f (innerFamilyCLM d x)‖ := by simp
        _ ≤ (K : ℝ) * ‖innerFamilyCLM c x - innerFamilyCLM d x‖ :=
          hf.norm_sub_le _ _
        _ = (K : ℝ) * ‖innerFamilyCLM e x‖ := by
          congr 2
          ext i
          simp [e, innerFamilyCLM_apply, inner_sub_left]
    _ = (K : ℝ) * ∫ x : H, ‖innerFamilyCLM e x‖ ∂(stdGaussian H) := by
      rw [integral_const_mul]
    _ ≤ (K : ℝ) * ∑ i, ‖e i‖ := by
      gcongr
      exact integral_norm_innerFamilyCLM_le_sum_norm e
    _ = (K : ℝ) * ∑ i, ‖c i - d i‖ := by rfl

noncomputable def pairL2 {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (x y : H) : PiLp 2 (fun _ : Fin 2 ↦ H) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ H)).symm ![x, y]

@[simp] lemma pairL2_apply_zero {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (x y : H) : pairL2 x y 0 = x := rfl

@[simp] lemma pairL2_apply_one {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (x y : H) : pairL2 x y 1 = y := rfl

lemma pairL2_add (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x₀ x₁ y₀ y₁ : H) :
    pairL2 (x₀ + y₀) (x₁ + y₁) = pairL2 x₀ x₁ + pairL2 y₀ y₁ := by
  ext i
  fin_cases i <;> simp

lemma pairL2_sub (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x₀ x₁ y₀ y₁ : H) :
    pairL2 (x₀ - y₀) (x₁ - y₁) = pairL2 x₀ x₁ - pairL2 y₀ y₁ := by
  ext i
  fin_cases i <;> simp

@[simp] lemma pairL2_sub_pairL2 (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x₀ x₁ y₀ y₁ : H) :
    pairL2 x₀ x₁ - pairL2 y₀ y₁ = pairL2 (x₀ - y₀) (x₁ - y₁) :=
  (pairL2_sub H x₀ x₁ y₀ y₁).symm

@[simp] lemma inner_pairL2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x₀ x₁ y₀ y₁ : H) :
    inner ℝ (pairL2 x₀ x₁) (pairL2 y₀ y₁) = inner ℝ x₀ y₀ + inner ℝ x₁ y₁ := by
  rw [PiLp.inner_apply]
  simp [Fin.sum_univ_two]

@[simp] lemma norm_pairL2_zero_right {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (x : H) : ‖pairL2 x 0‖ = ‖x‖ := by
  rw [PiLp.norm_eq_of_L2]
  simp [Fin.sum_univ_two, Real.sqrt_sq (norm_nonneg x)]

@[simp] lemma norm_pairL2_zero_left {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (x : H) : ‖pairL2 0 x‖ = ‖x‖ := by
  rw [PiLp.norm_eq_of_L2]
  simp [Fin.sum_univ_two, Real.sqrt_sq (norm_nonneg x)]

lemma norm_pairL2_le_sum_norm {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (x y : H) : ‖pairL2 x y‖ ≤ ‖x‖ + ‖y‖ := by
  calc
    ‖pairL2 x y‖ = ‖pairL2 x 0 + pairL2 0 y‖ := by
      rw [← pairL2_add]
      simp
    _ ≤ ‖pairL2 x 0‖ + ‖pairL2 0 y‖ := norm_add_le _ _
    _ = ‖x‖ + ‖y‖ := by
      rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
      simp only [Fin.sum_univ_two, pairL2_apply_zero, pairL2_apply_one, norm_zero]
      norm_num

/-- A reusable finite Gaussian projection coupling.  The vectors `yr₀,yr₁`
are the components of the second complex form in the retained two-dimensional
subspace; `y₀-yr₀,y₁-yr₁` are required to be orthogonal to the retained first
form.  The three Gram identities say that this is an orthogonal decomposition
of the second form. -/
theorem gaussian_projection_coupling
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    (x₀ x₁ xt₀ xt₁ y₀ y₁ yr₀ yr₁ : H)
    (hcross00 : inner ℝ xt₀ (y₀ - yr₀) = 0)
    (hcross01 : inner ℝ xt₀ (y₁ - yr₁) = 0)
    (hcross10 : inner ℝ xt₁ (y₀ - yr₀) = 0)
    (hcross11 : inner ℝ xt₁ (y₁ - yr₁) = 0)
    (hgram00 : inner ℝ (y₀ - yr₀) (y₀ - yr₀) + inner ℝ yr₀ yr₀ = inner ℝ y₀ y₀)
    (hgram01 : inner ℝ (y₀ - yr₀) (y₁ - yr₁) + inner ℝ yr₀ yr₁ = inner ℝ y₀ y₁)
    (hgram11 : inner ℝ (y₁ - yr₁) (y₁ - yr₁) + inner ℝ yr₁ yr₁ = inner ℝ y₁ y₁)
    {K : ℝ≥0} (f : EuclideanSpace ℝ (Fin 4) → ℝ) (hf : LipschitzWith K f) :
    abs ((∫ z : PiLp 2 (fun _ : Fin 2 ↦ H),
          f (innerFamilyCLM
            (![pairL2 x₀ 0, pairL2 x₁ 0, pairL2 y₀ 0, pairL2 y₁ 0] :
              Fin 4 → PiLp 2 (fun _ : Fin 2 ↦ H)) z)
            ∂(stdGaussian (PiLp 2 (fun _ : Fin 2 ↦ H)))) -
        ∫ z : PiLp 2 (fun _ : Fin 2 ↦ H),
          f (innerFamilyCLM
            (![pairL2 x₀ 0, pairL2 x₁ 0, pairL2 0 y₀, pairL2 0 y₁] :
              Fin 4 → PiLp 2 (fun _ : Fin 2 ↦ H)) z)
            ∂(stdGaussian (PiLp 2 (fun _ : Fin 2 ↦ H)))) ≤
      2 * (K : ℝ) *
        (‖x₀ - xt₀‖ + ‖x₁ - xt₁‖ + ‖yr₀‖ + ‖yr₁‖) := by
  let H2 := PiLp 2 (fun _ : Fin 2 ↦ H)
  -- Families on the common standard Gaussian space `H₂`.
  let C0 : Fin 4 → H2 := ![pairL2 x₀ 0, pairL2 x₁ 0, pairL2 y₀ 0, pairL2 y₁ 0]
  let C1 : Fin 4 → H2 := ![pairL2 xt₀ 0, pairL2 xt₁ 0, pairL2 y₀ 0, pairL2 y₁ 0]
  let C2 : Fin 4 → H2 :=
    ![pairL2 xt₀ 0, pairL2 xt₁ 0, pairL2 (y₀ - yr₀) yr₀, pairL2 (y₁ - yr₁) yr₁]
  let C3 : Fin 4 → H2 := ![pairL2 xt₀ 0, pairL2 xt₁ 0, pairL2 0 y₀, pairL2 0 y₁]
  let C4 : Fin 4 → H2 := ![pairL2 x₀ 0, pairL2 x₁ 0, pairL2 0 y₀, pairL2 0 y₁]
  have hgram : ∀ i j, inner ℝ (C2 i) (C2 j) = inner ℝ (C3 i) (C3 j) := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp only [C2, C3]
    all_goals rw [PiLp.inner_apply, PiLp.inner_apply]
    all_goals simp [Fin.sum_univ_two, hcross00, hcross01, hcross10, hcross11,
        hgram00, hgram01, hgram11, real_inner_comm]
    all_goals first
      | simpa [real_inner_self_eq_norm_sq] using hgram00
      | simpa [real_inner_self_eq_norm_sq] using hgram11
  have hmap : (stdGaussian H2).map (innerFamilyCLM C2) =
      (stdGaussian H2).map (innerFamilyCLM C3) :=
    map_innerFamilyCLM_stdGaussian_eq_of_gram_eq C2 C3 hgram
  have h23 :
      (∫ z : H2, f (innerFamilyCLM C2 z) ∂(stdGaussian H2)) =
        ∫ z : H2, f (innerFamilyCLM C3 z) ∂(stdGaussian H2) := by
    calc
      _ = ∫ y, f y ∂((stdGaussian H2).map (innerFamilyCLM C2)) :=
        (integral_map (by fun_prop) (hf.continuous.aestronglyMeasurable)).symm
      _ = ∫ y, f y ∂((stdGaussian H2).map (innerFamilyCLM C3)) := by rw [hmap]
      _ = _ := integral_map (by fun_prop) (hf.continuous.aestronglyMeasurable)
  have h01 := integral_lipschitz_innerFamilyCLM_sub_le C0 C1 f hf
  have h12 := integral_lipschitz_innerFamilyCLM_sub_le C1 C2 f hf
  have h34 := integral_lipschitz_innerFamilyCLM_sub_le C3 C4 f hf
  have hs01 : ∑ i, ‖C0 i - C1 i‖ ≤ ‖x₀ - xt₀‖ + ‖x₁ - xt₁‖ := by
    calc
      _ ≤ ∑ i, (![‖x₀ - xt₀‖, ‖x₁ - xt₁‖, 0, 0] : Fin 4 → ℝ) i := by
        apply sum_le_sum
        intro i _
        fin_cases i <;> simp [C0, C1, pairL2_sub_pairL2]
        all_goals rw [pairL2_sub_pairL2]
        all_goals simp only [sub_self]
        all_goals exact (norm_pairL2_zero_right _).le
      _ = _ := by simp [Fin.sum_univ_four]
  have hs12 : ∑ i, ‖C1 i - C2 i‖ ≤ 2 * (‖yr₀‖ + ‖yr₁‖) := by
    have h0 : ‖pairL2 y₀ 0 - pairL2 (y₀ - yr₀) yr₀‖ ≤ 2 * ‖yr₀‖ := by
      rw [pairL2_sub_pairL2]
      have := norm_pairL2_le_sum_norm yr₀ (-yr₀)
      have ht : ‖pairL2 yr₀ (-yr₀)‖ ≤ 2 * ‖yr₀‖ := by
        simpa only [norm_neg, two_mul] using this
      simpa [sub_sub, sub_eq_add_neg] using ht
    have h1 : ‖pairL2 y₁ 0 - pairL2 (y₁ - yr₁) yr₁‖ ≤ 2 * ‖yr₁‖ := by
      rw [pairL2_sub_pairL2]
      have := norm_pairL2_le_sum_norm yr₁ (-yr₁)
      have ht : ‖pairL2 yr₁ (-yr₁)‖ ≤ 2 * ‖yr₁‖ := by
        simpa only [norm_neg, two_mul] using this
      simpa [sub_sub, sub_eq_add_neg] using ht
    calc
      _ ≤ ∑ i, (![0, 0, 2 * ‖yr₀‖, 2 * ‖yr₁‖] : Fin 4 → ℝ) i := by
        apply sum_le_sum
        intro i _
        fin_cases i <;> simp [C1, C2, h0, h1]
      _ = _ := by simp [Fin.sum_univ_four]; ring
  have hs34 : ∑ i, ‖C3 i - C4 i‖ ≤ ‖x₀ - xt₀‖ + ‖x₁ - xt₁‖ := by
    calc
      _ ≤ ∑ i, (![‖x₀ - xt₀‖, ‖x₁ - xt₁‖, 0, 0] : Fin 4 → ℝ) i := by
        apply sum_le_sum
        intro i _
        fin_cases i <;> simp [C3, C4, pairL2_sub_pairL2, norm_sub_rev]
        all_goals rw [pairL2_sub_pairL2]
        all_goals simp only [sub_self]
        all_goals simpa only [norm_sub_rev] using (norm_pairL2_zero_right _).le
      _ = _ := by simp [Fin.sum_univ_four]
  change |(∫ z, f (innerFamilyCLM C0 z) ∂stdGaussian H2) -
      ∫ z, f (innerFamilyCLM C4 z) ∂stdGaussian H2| ≤ _
  calc
    |(∫ z, f (innerFamilyCLM C0 z) ∂stdGaussian H2) -
        ∫ z, f (innerFamilyCLM C4 z) ∂stdGaussian H2| ≤
      |(∫ z, f (innerFamilyCLM C0 z) ∂stdGaussian H2) -
        ∫ z, f (innerFamilyCLM C1 z) ∂stdGaussian H2| +
      |(∫ z, f (innerFamilyCLM C1 z) ∂stdGaussian H2) -
        ∫ z, f (innerFamilyCLM C2 z) ∂stdGaussian H2| +
      |(∫ z, f (innerFamilyCLM C3 z) ∂stdGaussian H2) -
        ∫ z, f (innerFamilyCLM C4 z) ∂stdGaussian H2| := by
      rw [h23]
      exact (abs_sub_le _
        (∫ z, f (innerFamilyCLM C3 z) ∂stdGaussian H2) _).trans
        (add_le_add
          (abs_sub_le
            (∫ z, f (innerFamilyCLM C0 z) ∂stdGaussian H2)
            (∫ z, f (innerFamilyCLM C1 z) ∂stdGaussian H2)
            (∫ z, f (innerFamilyCLM C3 z) ∂stdGaussian H2)) (le_refl _))
    _ ≤ (K : ℝ) * (‖x₀ - xt₀‖ + ‖x₁ - xt₁‖) +
        (K : ℝ) * (2 * (‖yr₀‖ + ‖yr₁‖)) +
        (K : ℝ) * (‖x₀ - xt₀‖ + ‖x₁ - xt₁‖) := by
      exact add_le_add (add_le_add
        (h01.trans (mul_le_mul_of_nonneg_left hs01 (NNReal.coe_nonneg K)))
        (h12.trans (mul_le_mul_of_nonneg_left hs12 (NNReal.coe_nonneg K))))
        (h34.trans (mul_le_mul_of_nonneg_left hs34 (NNReal.coe_nonneg K)))
    _ = 2 * (K : ℝ) *
        (‖x₀ - xt₀‖ + ‖x₁ - xt₁‖ + ‖yr₀‖ + ‖yr₁‖) := by ring

noncomputable def orthoProj1 {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (e y : H) : H := inner ℝ e y • e

lemma inner_sub_orthoProj1_eq_zero {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {e : H} (he : ‖e‖ = 1) (y : H) :
    inner ℝ e (y - orthoProj1 e y) = 0 := by
  rw [inner_sub_right, orthoProj1, inner_smul_right, real_inner_self_eq_norm_sq, he]
  norm_num

lemma orthoProj1_gram {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {e : H} (he : ‖e‖ = 1) (y z : H) :
    inner ℝ (y - orthoProj1 e y) (z - orthoProj1 e z) +
      inner ℝ (orthoProj1 e y) (orthoProj1 e z) = inner ℝ y z := by
  simp only [orthoProj1, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, real_inner_self_eq_norm_sq, he]
  norm_num
  rw [real_inner_comm y e]
  ring

lemma norm_orthoProj1 {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {e : H} (he : ‖e‖ = 1) (y : H) :
    ‖orthoProj1 e y‖ = |inner ℝ e y| := by
  simp [orthoProj1, norm_smul, he]

/-- Rank-one specialization of the projection coupling. -/
theorem gaussian_rankOne_projection_coupling
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    (x₀ x₁ y₀ y₁ e : H) (he : ‖e‖ = 1) (s₀ s₁ : ℝ)
    (hx₀ : x₀ = s₀ • e) (hx₁ : x₁ = s₁ • e)
    {K : ℝ≥0} (f : EuclideanSpace ℝ (Fin 4) → ℝ) (hf : LipschitzWith K f) :
    abs ((∫ z : PiLp 2 (fun _ : Fin 2 ↦ H),
          f (innerFamilyCLM
            (![pairL2 x₀ 0, pairL2 x₁ 0, pairL2 y₀ 0, pairL2 y₁ 0] :
              Fin 4 → PiLp 2 (fun _ : Fin 2 ↦ H)) z)
            ∂(stdGaussian (PiLp 2 (fun _ : Fin 2 ↦ H)))) -
        ∫ z : PiLp 2 (fun _ : Fin 2 ↦ H),
          f (innerFamilyCLM
            (![pairL2 x₀ 0, pairL2 x₁ 0, pairL2 0 y₀, pairL2 0 y₁] :
              Fin 4 → PiLp 2 (fun _ : Fin 2 ↦ H)) z)
            ∂(stdGaussian (PiLp 2 (fun _ : Fin 2 ↦ H)))) ≤
      2 * (K : ℝ) * (|inner ℝ e y₀| + |inner ℝ e y₁|) := by
  have hcross (s : ℝ) (y : H) :
      inner ℝ (s • e) (y - orthoProj1 e y) = 0 := by
    rw [inner_smul_left, inner_sub_orthoProj1_eq_zero he, mul_zero]
  simpa [hx₀, hx₁, norm_orthoProj1 he] using
    gaussian_projection_coupling x₀ x₁ x₀ x₁ y₀ y₁
      (orthoProj1 e y₀) (orthoProj1 e y₁)
      (by simpa [hx₀] using hcross s₀ y₀)
      (by simpa [hx₀] using hcross s₀ y₁)
      (by simpa [hx₁] using hcross s₁ y₀)
      (by simpa [hx₁] using hcross s₁ y₁)
      (orthoProj1_gram he y₀ y₀)
      (orthoProj1_gram he y₀ y₁)
      (orthoProj1_gram he y₁ y₁) f hf

noncomputable def orthoProj2 {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (e₀ e₁ y : H) : H :=
  orthoProj1 e₀ y + orthoProj1 e₁ y

lemma inner_sub_orthoProj2_eq_zero_left {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {e₀ e₁ : H} (he₀ : ‖e₀‖ = 1)
    (horth : inner ℝ e₀ e₁ = 0) (y : H) :
    inner ℝ e₀ (y - orthoProj2 e₀ e₁ y) = 0 := by
  simp [orthoProj2, inner_sub_right, inner_add_right, orthoProj1,
    inner_smul_right, real_inner_self_eq_norm_sq, he₀, horth]

lemma inner_sub_orthoProj2_eq_zero_right {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {e₀ e₁ : H} (he₁ : ‖e₁‖ = 1)
    (horth : inner ℝ e₀ e₁ = 0) (y : H) :
    inner ℝ e₁ (y - orthoProj2 e₀ e₁ y) = 0 := by
  have horth' : inner ℝ e₁ e₀ = 0 := by simpa [real_inner_comm] using horth
  simp [orthoProj2, inner_sub_right, inner_add_right, orthoProj1,
    inner_smul_right, real_inner_self_eq_norm_sq, he₁, horth']

lemma orthoProj2_gram {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {e₀ e₁ : H} (he₀ : ‖e₀‖ = 1) (he₁ : ‖e₁‖ = 1)
    (horth : inner ℝ e₀ e₁ = 0) (y z : H) :
    inner ℝ (y - orthoProj2 e₀ e₁ y) (z - orthoProj2 e₀ e₁ z) +
      inner ℝ (orthoProj2 e₀ e₁ y) (orthoProj2 e₀ e₁ z) = inner ℝ y z := by
  have horth' : inner ℝ e₁ e₀ = 0 := by simpa [real_inner_comm] using horth
  simp only [orthoProj2, orthoProj1, inner_sub_left, inner_sub_right,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    real_inner_self_eq_norm_sq, he₀, he₁, horth, horth']
  norm_num
  rw [real_inner_comm y e₀, real_inner_comm y e₁]
  ring

lemma norm_orthoProj2_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {e₀ e₁ : H} (he₀ : ‖e₀‖ = 1) (he₁ : ‖e₁‖ = 1)
    (y : H) :
    ‖orthoProj2 e₀ e₁ y‖ ≤ |inner ℝ e₀ y| + |inner ℝ e₁ y| := by
  exact (norm_add_le _ _).trans_eq (by rw [norm_orthoProj1 he₀, norm_orthoProj1 he₁])

/-- Rank-two specialization.  This is the nondegenerate branch of the
cutoff Gram--Schmidt coupling. -/
theorem gaussian_rankTwo_projection_coupling
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    (x₀ x₁ y₀ y₁ e₀ e₁ : H) (he₀ : ‖e₀‖ = 1) (he₁ : ‖e₁‖ = 1)
    (horth : inner ℝ e₀ e₁ = 0) (s₀₀ s₀₁ s₁₀ s₁₁ : ℝ)
    (hx₀ : x₀ = s₀₀ • e₀ + s₀₁ • e₁) (hx₁ : x₁ = s₁₀ • e₀ + s₁₁ • e₁)
    {K : ℝ≥0} (f : EuclideanSpace ℝ (Fin 4) → ℝ) (hf : LipschitzWith K f) :
    abs ((∫ z : PiLp 2 (fun _ : Fin 2 ↦ H),
          f (innerFamilyCLM
            (![pairL2 x₀ 0, pairL2 x₁ 0, pairL2 y₀ 0, pairL2 y₁ 0] :
              Fin 4 → PiLp 2 (fun _ : Fin 2 ↦ H)) z)
            ∂(stdGaussian (PiLp 2 (fun _ : Fin 2 ↦ H)))) -
        ∫ z : PiLp 2 (fun _ : Fin 2 ↦ H),
          f (innerFamilyCLM
            (![pairL2 x₀ 0, pairL2 x₁ 0, pairL2 0 y₀, pairL2 0 y₁] :
              Fin 4 → PiLp 2 (fun _ : Fin 2 ↦ H)) z)
            ∂(stdGaussian (PiLp 2 (fun _ : Fin 2 ↦ H)))) ≤
      2 * (K : ℝ) *
        (|inner ℝ e₀ y₀| + |inner ℝ e₁ y₀| +
          (|inner ℝ e₀ y₁| + |inner ℝ e₁ y₁|)) := by
  have hcross (a b : ℝ) (y : H) :
      inner ℝ (a • e₀ + b • e₁) (y - orthoProj2 e₀ e₁ y) = 0 := by
    rw [inner_add_left, inner_smul_left, inner_smul_left,
      inner_sub_orthoProj2_eq_zero_left he₀ horth,
      inner_sub_orthoProj2_eq_zero_right he₁ horth]
    ring
  have hmain := gaussian_projection_coupling x₀ x₁ x₀ x₁ y₀ y₁
      (orthoProj2 e₀ e₁ y₀) (orthoProj2 e₀ e₁ y₁)
      (by simpa [hx₀] using hcross s₀₀ s₀₁ y₀)
      (by simpa [hx₀] using hcross s₀₀ s₀₁ y₁)
      (by simpa [hx₁] using hcross s₁₀ s₁₁ y₀)
      (by simpa [hx₁] using hcross s₁₀ s₁₁ y₁)
      (orthoProj2_gram he₀ he₁ horth y₀ y₀)
      (orthoProj2_gram he₀ he₁ horth y₀ y₁)
      (orthoProj2_gram he₀ he₁ horth y₁ y₁) f hf
  simp only [sub_self, norm_zero, zero_add] at hmain
  exact hmain.trans (mul_le_mul_of_nonneg_left
    (add_le_add (norm_orthoProj2_le he₀ he₁ y₀) (norm_orthoProj2_le he₀ he₁ y₁))
    (mul_nonneg (by norm_num) (NNReal.coe_nonneg K)))

noncomputable def unitVec {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (x : H) : H := ‖x‖⁻¹ • x

lemma norm_unitVec {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {x : H} (hx : x ≠ 0) : ‖unitVec x‖ = 1 := by
  simp [unitVec, norm_smul, abs_inv, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

lemma norm_smul_unitVec {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {x : H} (hx : x ≠ 0) : ‖x‖ • unitVec x = x := by
  rw [unitVec, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

lemma abs_inner_unitVec_le_div {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {x y : H} {δ m : ℝ} (hδ : 0 < δ)
    (hx : δ ≤ ‖x‖) (hxy : |inner ℝ x y| ≤ m) :
    |inner ℝ (unitVec x) y| ≤ m / δ := by
  have hxpos : 0 < ‖x‖ := hδ.trans_le hx
  rw [unitVec, inner_smul_left, abs_mul]
  simp only [map_inv₀, star_trivial, abs_inv, abs_norm]
  rw [inv_mul_eq_div]
  rw [show |(starRingEnd ℝ) ‖x‖| = ‖x‖ by simp]
  exact (div_le_div_iff₀ hxpos hδ).2
    ((mul_le_mul_of_nonneg_left hx (abs_nonneg (inner ℝ x y))).trans
      (mul_le_mul_of_nonneg_right hxy (le_of_lt hxpos)))


lemma abs_inner_unitVec_le_sq {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {x y : H} {δ : ℝ} (hδ : 0 < δ)
    (hx : δ ≤ ‖x‖) (hxy : |inner ℝ x y| ≤ δ ^ 3) :
    |inner ℝ (unitVec x) y| ≤ δ ^ 2 := by
  calc
    |inner ℝ (unitVec x) y| ≤ δ ^ 3 / δ :=
      abs_inner_unitVec_le_div hδ hx hxy
    _ = δ ^ 2 := by field_simp

lemma abs_inner_sub_orthoProj1_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (e x y : H) :
    |inner ℝ (x - orthoProj1 e x) y| ≤
      |inner ℝ x y| + |inner ℝ e x| * |inner ℝ e y| := by
  rw [inner_sub_left, orthoProj1, inner_smul_left]
  rw [show (starRingEnd ℝ) (inner ℝ e x) = inner ℝ e x by simp]
  simpa only [abs_mul] using
    (abs_sub (G := ℝ) (inner ℝ x y) (inner ℝ e x * inner ℝ e y))

noncomputable def gaussianPairDiscrepancy
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    (x₀ x₁ y₀ y₁ : H) (f : EuclideanSpace ℝ (Fin 4) → ℝ) : ℝ :=
  abs ((∫ z : PiLp 2 (fun _ : Fin 2 ↦ H),
        f (innerFamilyCLM
          (![pairL2 x₀ 0, pairL2 x₁ 0, pairL2 y₀ 0, pairL2 y₁ 0] :
            Fin 4 → PiLp 2 (fun _ : Fin 2 ↦ H)) z)
          ∂(stdGaussian (PiLp 2 (fun _ : Fin 2 ↦ H)))) -
      ∫ z : PiLp 2 (fun _ : Fin 2 ↦ H),
        f (innerFamilyCLM
          (![pairL2 x₀ 0, pairL2 x₁ 0, pairL2 0 y₀, pairL2 0 y₁] :
            Fin 4 → PiLp 2 (fun _ : Fin 2 ↦ H)) z)
          ∂(stdGaussian (PiLp 2 (fun _ : Fin 2 ↦ H))))

lemma gaussianPairDiscrepancy_le_of_both_small
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    (x₀ x₁ y₀ y₁ : H) {δ : ℝ} (hx₀ : ‖x₀‖ ≤ δ) (hx₁ : ‖x₁‖ ≤ δ)
    {K : ℝ≥0} (f : EuclideanSpace ℝ (Fin 4) → ℝ) (hf : LipschitzWith K f) :
    gaussianPairDiscrepancy x₀ x₁ y₀ y₁ f ≤ 4 * (K : ℝ) * δ := by
  have hmain := gaussian_projection_coupling x₀ x₁ 0 0 y₀ y₁ 0 0
    (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) f hf
  simp only [sub_zero, norm_zero, add_zero] at hmain
  rw [gaussianPairDiscrepancy]
  exact hmain.trans (by
      have hK : 0 ≤ (K : ℝ) := NNReal.coe_nonneg K
      nlinarith [norm_nonneg x₀, norm_nonneg x₁])

lemma gaussianPairDiscrepancy_le_of_first_small
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    (x₀ x₁ y₀ y₁ : H) {δ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hx₀ : ‖x₀‖ ≤ δ) (hx₁ : δ ≤ ‖x₁‖)
    (hxy₀ : |inner ℝ x₁ y₀| ≤ δ ^ 3)
    (hxy₁ : |inner ℝ x₁ y₁| ≤ δ ^ 3)
    {K : ℝ≥0} (f : EuclideanSpace ℝ (Fin 4) → ℝ) (hf : LipschitzWith K f) :
    gaussianPairDiscrepancy x₀ x₁ y₀ y₁ f ≤ 6 * (K : ℝ) * δ := by
  have hx₁ne : x₁ ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (hδ.trans_le hx₁))
  let e := unitVec x₁
  have he : ‖e‖ = 1 := norm_unitVec hx₁ne
  have hcross (y : H) : inner ℝ x₁ (y - orthoProj1 e y) = 0 := by
    rw [← norm_smul_unitVec hx₁ne, inner_smul_left,
      inner_sub_orthoProj1_eq_zero he, mul_zero]
  have hp₀ : ‖orthoProj1 e y₀‖ ≤ δ := by
    rw [norm_orthoProj1 he]
    exact (abs_inner_unitVec_le_sq hδ hx₁ hxy₀).trans (by nlinarith [sq_nonneg δ])
  have hp₁ : ‖orthoProj1 e y₁‖ ≤ δ := by
    rw [norm_orthoProj1 he]
    exact (abs_inner_unitVec_le_sq hδ hx₁ hxy₁).trans (by nlinarith [sq_nonneg δ])
  have hmain := gaussian_projection_coupling x₀ x₁ 0 x₁ y₀ y₁
    (orthoProj1 e y₀) (orthoProj1 e y₁)
    (by simp) (by simp) (hcross y₀) (hcross y₁)
    (orthoProj1_gram he y₀ y₀) (orthoProj1_gram he y₀ y₁)
    (orthoProj1_gram he y₁ y₁) f hf
  simp only [sub_zero, sub_self, norm_zero, zero_add] at hmain
  rw [gaussianPairDiscrepancy]
  exact hmain.trans (by
    have hK : 0 ≤ (K : ℝ) := NNReal.coe_nonneg K
    nlinarith [norm_nonneg x₀, norm_nonneg (orthoProj1 e y₀),
      norm_nonneg (orthoProj1 e y₁)])

lemma gaussianPairDiscrepancy_le_of_rankOne_residual
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    (x₀ x₁ y₀ y₁ : H) {δ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hx₀ : δ ≤ ‖x₀‖)
    (hw : ‖x₁ - orthoProj1 (unitVec x₀) x₁‖ ≤ δ)
    (hxy₀ : |inner ℝ x₀ y₀| ≤ δ ^ 3)
    (hxy₁ : |inner ℝ x₀ y₁| ≤ δ ^ 3)
    {K : ℝ≥0} (f : EuclideanSpace ℝ (Fin 4) → ℝ) (hf : LipschitzWith K f) :
    gaussianPairDiscrepancy x₀ x₁ y₀ y₁ f ≤ 6 * (K : ℝ) * δ := by
  have hx₀ne : x₀ ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (hδ.trans_le hx₀))
  let e := unitVec x₀
  have he : ‖e‖ = 1 := norm_unitVec hx₀ne
  have hcross₀ (y : H) : inner ℝ x₀ (y - orthoProj1 e y) = 0 := by
    rw [← norm_smul_unitVec hx₀ne, inner_smul_left,
      inner_sub_orthoProj1_eq_zero he, mul_zero]
  have hcross₁ (y : H) :
      inner ℝ (orthoProj1 e x₁) (y - orthoProj1 e y) = 0 := by
    rw [orthoProj1, inner_smul_left, inner_sub_orthoProj1_eq_zero he, mul_zero]
  have hp₀ : ‖orthoProj1 e y₀‖ ≤ δ := by
    rw [norm_orthoProj1 he]
    exact (abs_inner_unitVec_le_sq hδ hx₀ hxy₀).trans (by nlinarith [sq_nonneg δ])
  have hp₁ : ‖orthoProj1 e y₁‖ ≤ δ := by
    rw [norm_orthoProj1 he]
    exact (abs_inner_unitVec_le_sq hδ hx₀ hxy₁).trans (by nlinarith [sq_nonneg δ])
  have hmain := gaussian_projection_coupling x₀ x₁ x₀ (orthoProj1 e x₁) y₀ y₁
    (orthoProj1 e y₀) (orthoProj1 e y₁)
    (hcross₀ y₀) (hcross₀ y₁) (hcross₁ y₀) (hcross₁ y₁)
    (orthoProj1_gram he y₀ y₀) (orthoProj1_gram he y₀ y₁)
    (orthoProj1_gram he y₁ y₁) f hf
  simp only [sub_self, norm_zero, zero_add] at hmain
  rw [gaussianPairDiscrepancy]
  exact hmain.trans (by
    have hK : 0 ≤ (K : ℝ) := NNReal.coe_nonneg K
    nlinarith [norm_nonneg (x₁ - orthoProj1 e x₁),
      norm_nonneg (orthoProj1 e y₀), norm_nonneg (orthoProj1 e y₁)])

lemma gaussianPairDiscrepancy_le_of_rankTwo_residual
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    (x₀ x₁ y₀ y₁ : H) {δ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hx₀ : δ ≤ ‖x₀‖) (hx₁one : ‖x₁‖ ≤ 1)
    (hw : δ ≤ ‖x₁ - orthoProj1 (unitVec x₀) x₁‖)
    (hxy₀₀ : |inner ℝ x₀ y₀| ≤ δ ^ 3)
    (hxy₀₁ : |inner ℝ x₀ y₁| ≤ δ ^ 3)
    (hxy₁₀ : |inner ℝ x₁ y₀| ≤ δ ^ 3)
    (hxy₁₁ : |inner ℝ x₁ y₁| ≤ δ ^ 3)
    {K : ℝ≥0} (f : EuclideanSpace ℝ (Fin 4) → ℝ) (hf : LipschitzWith K f) :
    gaussianPairDiscrepancy x₀ x₁ y₀ y₁ f ≤ 12 * (K : ℝ) * δ := by
  have hx₀ne : x₀ ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (hδ.trans_le hx₀))
  let e₀ := unitVec x₀
  let w := x₁ - orthoProj1 e₀ x₁
  have hw' : δ ≤ ‖w‖ := hw
  have hwne : w ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (hδ.trans_le hw'))
  let e₁ := unitVec w
  have he₀ : ‖e₀‖ = 1 := norm_unitVec hx₀ne
  have he₁ : ‖e₁‖ = 1 := norm_unitVec hwne
  have horth : inner ℝ e₀ e₁ = 0 := by
    dsimp only [e₁]
    rw [unitVec, inner_smul_right, inner_sub_orthoProj1_eq_zero he₀, mul_zero]
  have hxrepr₀ : x₀ = ‖x₀‖ • e₀ + (0 : ℝ) • e₁ := by
    rw [zero_smul, add_zero, norm_smul_unitVec hx₀ne]
  have hxrepr₁ : x₁ = inner ℝ e₀ x₁ • e₀ + ‖w‖ • e₁ := by
    rw [norm_smul_unitVec hwne]
    simp only [w, orthoProj1]
    abel
  have he₀x₁ : |inner ℝ e₀ x₁| ≤ 1 := by
    calc
      |inner ℝ e₀ x₁| ≤ ‖e₀‖ * ‖x₁‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 := by rw [he₀, one_mul]; exact hx₁one
  have he₀y₀ : |inner ℝ e₀ y₀| ≤ δ ^ 2 :=
    abs_inner_unitVec_le_sq hδ hx₀ hxy₀₀
  have he₀y₁ : |inner ℝ e₀ y₁| ≤ δ ^ 2 :=
    abs_inner_unitVec_le_sq hδ hx₀ hxy₀₁
  have hwy₀ : |inner ℝ w y₀| ≤ δ ^ 3 + δ ^ 2 := by
    exact (abs_inner_sub_orthoProj1_le e₀ x₁ y₀).trans
      (add_le_add hxy₁₀
        (calc
          |inner ℝ e₀ x₁| * |inner ℝ e₀ y₀| ≤ 1 * δ ^ 2 :=
            mul_le_mul he₀x₁ he₀y₀ (abs_nonneg _) (by norm_num)
          _ = δ ^ 2 := one_mul _))
  have hwy₁ : |inner ℝ w y₁| ≤ δ ^ 3 + δ ^ 2 := by
    exact (abs_inner_sub_orthoProj1_le e₀ x₁ y₁).trans
      (add_le_add hxy₁₁
        (calc
          |inner ℝ e₀ x₁| * |inner ℝ e₀ y₁| ≤ 1 * δ ^ 2 :=
            mul_le_mul he₀x₁ he₀y₁ (abs_nonneg _) (by norm_num)
          _ = δ ^ 2 := one_mul _))
  have he₁y₀ : |inner ℝ e₁ y₀| ≤ 2 * δ := by
    calc
      |inner ℝ e₁ y₀| ≤ (δ ^ 3 + δ ^ 2) / δ :=
        abs_inner_unitVec_le_div hδ hw' hwy₀
      _ = δ ^ 2 + δ := by field_simp
      _ ≤ 2 * δ := by nlinarith [sq_nonneg δ]
  have he₁y₁ : |inner ℝ e₁ y₁| ≤ 2 * δ := by
    calc
      |inner ℝ e₁ y₁| ≤ (δ ^ 3 + δ ^ 2) / δ :=
        abs_inner_unitVec_le_div hδ hw' hwy₁
      _ = δ ^ 2 + δ := by field_simp
      _ ≤ 2 * δ := by nlinarith [sq_nonneg δ]
  have hmain := gaussian_rankTwo_projection_coupling x₀ x₁ y₀ y₁ e₀ e₁
    he₀ he₁ horth ‖x₀‖ 0 (inner ℝ e₀ x₁) ‖w‖ hxrepr₀ hxrepr₁ f hf
  rw [gaussianPairDiscrepancy]
  have hsum : |inner ℝ e₀ y₀| + |inner ℝ e₁ y₀| +
      (|inner ℝ e₀ y₁| + |inner ℝ e₁ y₁|) ≤ 6 * δ := by
    nlinarith [sq_nonneg δ]
  calc
    _ ≤ 2 * (K : ℝ) * (6 * δ) := hmain.trans
      (mul_le_mul_of_nonneg_left hsum
        (mul_nonneg (by norm_num) (NNReal.coe_nonneg K)))
    _ = 12 * (K : ℝ) * δ := by ring

/-- Cutoff Gram--Schmidt decoupling.  The four hypotheses are precisely the
four real coordinate cross-covariances of two complex Gaussian linear forms.
The proof includes the zero-, rank-one-, and rank-two branches. -/
theorem gaussianPairDiscrepancy_le_cutoff
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    (x₀ x₁ y₀ y₁ : H) {δ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hx₁one : ‖x₁‖ ≤ 1)
    (hxy₀₀ : |inner ℝ x₀ y₀| ≤ δ ^ 3)
    (hxy₀₁ : |inner ℝ x₀ y₁| ≤ δ ^ 3)
    (hxy₁₀ : |inner ℝ x₁ y₀| ≤ δ ^ 3)
    (hxy₁₁ : |inner ℝ x₁ y₁| ≤ δ ^ 3)
    {K : ℝ≥0} (f : EuclideanSpace ℝ (Fin 4) → ℝ) (hf : LipschitzWith K f) :
    gaussianPairDiscrepancy x₀ x₁ y₀ y₁ f ≤ 12 * (K : ℝ) * δ := by
  have hKδ : 0 ≤ (K : ℝ) * δ :=
    mul_nonneg (NNReal.coe_nonneg K) (le_of_lt hδ)
  by_cases hx₀small : ‖x₀‖ ≤ δ
  · by_cases hx₁small : ‖x₁‖ ≤ δ
    · exact (gaussianPairDiscrepancy_le_of_both_small x₀ x₁ y₀ y₁
        hx₀small hx₁small f hf).trans (by nlinarith)
    · have hx₁large : δ ≤ ‖x₁‖ := le_of_lt (lt_of_not_ge hx₁small)
      exact (gaussianPairDiscrepancy_le_of_first_small x₀ x₁ y₀ y₁
        hδ hδone hx₀small hx₁large hxy₁₀ hxy₁₁ f hf).trans (by nlinarith)
  · have hx₀large : δ ≤ ‖x₀‖ := le_of_lt (lt_of_not_ge hx₀small)
    by_cases hwsmall : ‖x₁ - orthoProj1 (unitVec x₀) x₁‖ ≤ δ
    · exact (gaussianPairDiscrepancy_le_of_rankOne_residual x₀ x₁ y₀ y₁
        hδ hδone hx₀large hwsmall hxy₀₀ hxy₀₁ f hf).trans (by nlinarith)
    · have hwlarge : δ ≤ ‖x₁ - orthoProj1 (unitVec x₀) x₁‖ :=
        le_of_lt (lt_of_not_ge hwsmall)
      exact gaussianPairDiscrepancy_le_of_rankTwo_residual x₀ x₁ y₀ y₁
        hδ hδone hx₀large hx₁one hwlarge hxy₀₀ hxy₀₁ hxy₁₀ hxy₁₁ f hf

/-- Finite-dimensional Gaussian decoupling with the `m^(1/4)` loss used in
Michelen--Sawhney's decoupling lemma.  No nondegeneracy is assumed. -/
theorem gaussianPairDiscrepancy_le_rpow_quarter
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    (x₀ x₁ y₀ y₁ : H) {m : ℝ} (hm : 0 ≤ m) (hmone : m ≤ 1)
    (hx₁one : ‖x₁‖ ≤ 1)
    (hxy₀₀ : |inner ℝ x₀ y₀| ≤ m)
    (hxy₀₁ : |inner ℝ x₀ y₁| ≤ m)
    (hxy₁₀ : |inner ℝ x₁ y₀| ≤ m)
    (hxy₁₁ : |inner ℝ x₁ y₁| ≤ m)
    {K : ℝ≥0} (f : EuclideanSpace ℝ (Fin 4) → ℝ) (hf : LipschitzWith K f) :
    gaussianPairDiscrepancy x₀ x₁ y₀ y₁ f ≤
      12 * (K : ℝ) * m ^ (1 / 4 : ℝ) := by
  by_cases hmzero : m = 0
  · subst m
    have hc00 : inner ℝ x₀ y₀ = 0 :=
      abs_eq_zero.mp (le_antisymm hxy₀₀ (abs_nonneg _))
    have hc01 : inner ℝ x₀ y₁ = 0 :=
      abs_eq_zero.mp (le_antisymm hxy₀₁ (abs_nonneg _))
    have hc10 : inner ℝ x₁ y₀ = 0 :=
      abs_eq_zero.mp (le_antisymm hxy₁₀ (abs_nonneg _))
    have hc11 : inner ℝ x₁ y₁ = 0 :=
      abs_eq_zero.mp (le_antisymm hxy₁₁ (abs_nonneg _))
    have hmain := gaussian_projection_coupling x₀ x₁ x₀ x₁ y₀ y₁ 0 0
      (by simpa using hc00) (by simpa using hc01)
      (by simpa using hc10) (by simpa using hc11)
      (by simp) (by simp) (by simp) f hf
    simpa [gaussianPairDiscrepancy] using hmain
  · have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hmzero)
    let δ : ℝ := m ^ (1 / 4 : ℝ)
    have hδ : 0 < δ := Real.rpow_pos_of_pos hmpos _
    have hδone : δ ≤ 1 := by
      calc
        δ ≤ 1 ^ (1 / 4 : ℝ) := by
          exact Real.rpow_le_rpow hm hmone (by norm_num)
        _ = 1 := Real.one_rpow _
    have hδfour : δ ^ 4 = m := by
      dsimp only [δ]
      convert Real.rpow_inv_natCast_pow hm (by norm_num : (4 : ℕ) ≠ 0) using 1 <;>
        norm_num
    have hmδcube : m ≤ δ ^ 3 := by
      rw [← hδfour]
      nlinarith [sq_nonneg δ, mul_nonneg (sq_nonneg δ) (le_of_lt hδ)]
    simpa only [δ] using gaussianPairDiscrepancy_le_cutoff x₀ x₁ y₀ y₁
      hδ hδone hx₁one (hxy₀₀.trans hmδcube) (hxy₀₁.trans hmδcube)
      (hxy₁₀.trans hmδcube) (hxy₁₁.trans hmδcube) f hf


end GaussianDecoupling
namespace PairFactorization

open scoped BigOperators ENNReal NNReal Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Finset
open SmoothCutoffC4 CutoffLindebergBridge

noncomputable section

abbrev PairIncrementSpace (l : ℕ) := Fin 2 → Fin l → ℂ

/-- The endpoint/prefix forms for two phases, on their product space. -/
def pairEndpointPrefixForms (l : ℕ) (endpointScale prefixScale : ℝ) :
    (Fin 2 × Option (Fin l)) → PairIncrementSpace l →L[ℝ] ℂ :=
  fun q ↦ (endpointPrefixForms l endpointScale prefixScale q.2).comp
    (ContinuousLinearMap.proj q.1)

/-- The product of the two endpoint/prefix cutoffs, represented as one cutoff product. -/
def pairEndpointPrefixCutoff (l : ℕ) (endpointScale prefixScale : ℝ)
    (w : PairIncrementSpace l) : ℝ :=
  cutoffProduct Finset.univ (pairEndpointPrefixForms l endpointScale prefixScale) w

lemma pairEndpointPrefixCutoff_eq (l : ℕ) (endpointScale prefixScale : ℝ)
    (w : PairIncrementSpace l) :
    pairEndpointPrefixCutoff l endpointScale prefixScale w =
      endpointPrefixCutoff l endpointScale prefixScale (w 0) *
        endpointPrefixCutoff l endpointScale prefixScale (w 1) := by
  simp only [pairEndpointPrefixCutoff, pairEndpointPrefixForms,
    endpointPrefixCutoff, cutoffProduct, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]
  rw [Fintype.prod_prod_type]
  rw [Fin.prod_univ_two]

/-- Explicit fourth-derivative budget for replacing one common sign in both phases. -/
def pairEndpointPrefixDirectionBudget (l : ℕ) (endpointScale prefixScale : ℝ)
    (v : PairIncrementSpace l) : ℝ :=
  (cutoffC4 *
    (∑ q : Fin 2 × Option (Fin l),
      ‖pairEndpointPrefixForms l endpointScale prefixScale q‖) * ‖v‖) ^ 4

lemma pairEndpointPrefixDirectionBudget_nonneg (l : ℕ)
    (endpointScale prefixScale : ℝ) (v : PairIncrementSpace l) :
    0 ≤ pairEndpointPrefixDirectionBudget l endpointScale prefixScale v := by
  exact Even.pow_nonneg (by norm_num) _

lemma pairEndpointPrefixCutoff_contDiff (l : ℕ)
    (endpointScale prefixScale : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (pairEndpointPrefixCutoff l endpointScale prefixScale) := by
  exact cutoffProduct_contDiff _ _

lemma pairEndpointPrefixCutoff_nonneg (l : ℕ) (endpointScale prefixScale : ℝ)
    (w : PairIncrementSpace l) :
    0 ≤ pairEndpointPrefixCutoff l endpointScale prefixScale w := by
  unfold pairEndpointPrefixCutoff cutoffProduct
  exact Finset.prod_nonneg fun _ _ ↦ cutoff_nonneg _

lemma pairEndpointPrefixCutoff_le_one (l : ℕ) (endpointScale prefixScale : ℝ)
    (w : PairIncrementSpace l) :
    pairEndpointPrefixCutoff l endpointScale prefixScale w ≤ 1 := by
  unfold pairEndpointPrefixCutoff cutoffProduct
  exact Finset.prod_le_one (fun _ _ ↦ cutoff_nonneg _) (fun _ _ ↦ cutoff_le_one _)

/-- The joint two-phase cutoff restricted to any affine replacement line is an
explicit bounded `C⁴` test. -/
theorem pairEndpointPrefixCutoff_isBoundedC4Test_line (l : ℕ)
    (endpointScale prefixScale : ℝ) (a v : PairIncrementSpace l) :
    Erdos88.Invariance.IsBoundedC4Test
      (fun z : ℝ ↦ pairEndpointPrefixCutoff l endpointScale prefixScale (a + z • v))
      (pairEndpointPrefixDirectionBudget l endpointScale prefixScale v) := by
  let F : PairIncrementSpace l → ℝ :=
    pairEndpointPrefixCutoff l endpointScale prefixScale
  let L : ℝ →L[ℝ] PairIncrementSpace l :=
    ContinuousLinearMap.toSpanSingleton ℝ v
  have hF : ContDiff ℝ (⊤ : ℕ∞) F :=
    pairEndpointPrefixCutoff_contDiff l endpointScale prefixScale
  have hshift : ContDiff ℝ (⊤ : ℕ∞) (fun w ↦ F (a + w)) := by
    exact hF.comp (contDiff_const.add contDiff_id)
  refine {
    contDiff := ?_
    bounded := ⟨1, ?_⟩
    fourth_nonneg := pairEndpointPrefixDirectionBudget_nonneg
      l endpointScale prefixScale v
    fourth_bound := ?_
  }
  · have hline : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ ↦ a + z • v) := by
      fun_prop
    exact (hF.comp hline).of_le (WithTop.coe_le_coe.mpr le_top)
  · intro z
    rw [abs_of_nonneg (pairEndpointPrefixCutoff_nonneg l endpointScale prefixScale _)]
    exact pairEndpointPrefixCutoff_le_one l endpointScale prefixScale _
  · intro z
    rw [← Real.norm_eq_abs, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hfun :
        (fun z : ℝ ↦ F (a + z • v)) = (fun w ↦ F (a + w)) ∘ L := by
      funext t
      rfl
    rw [hfun, L.iteratedFDeriv_comp_right hshift z (WithTop.coe_le_coe.mpr le_top)]
    calc
      ‖(iteratedFDeriv ℝ 4 (fun w ↦ F (a + w)) (L z)).compContinuousLinearMap
          (fun _ ↦ L)‖ ≤
          ‖iteratedFDeriv ℝ 4 (fun w ↦ F (a + w)) (L z)‖ *
            ∏ _ : Fin 4, ‖L‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ = ‖iteratedFDeriv ℝ 4 F (a + L z)‖ * ‖v‖ ^ 4 := by
        rw [iteratedFDeriv_comp_add_left]
        simp [L]
      _ ≤
          (cutoffC4 *
            (∑ q : Fin 2 × Option (Fin l),
              ‖pairEndpointPrefixForms l endpointScale prefixScale q‖)) ^ 4 * ‖v‖ ^ 4 := by
        gcongr
        unfold F pairEndpointPrefixCutoff
        exact norm_iteratedFDeriv_cutoffProduct_le
          (u := (Finset.univ : Finset (Fin 2 × Option (Fin l))))
          (pairEndpointPrefixForms l endpointScale prefixScale) (a + L z) (by norm_num)
      _ = pairEndpointPrefixDirectionBudget l endpointScale prefixScale v := by
        rw [pairEndpointPrefixDirectionBudget, mul_pow]
        ring

/-- The joint cutoff satisfies the normed-output Lindeberg hypotheses. -/
theorem pairEndpointPrefixCutoff_isBoundedC4OnLines (n l : ℕ)
    (endpointScale prefixScale : ℝ) (v : Fin n → PairIncrementSpace l) :
    CutoffLindebergBridge.NormedLindeberg.IsBoundedC4OnLines
      (pairEndpointPrefixCutoff l endpointScale prefixScale) v
      (fun i ↦ pairEndpointPrefixDirectionBudget l endpointScale prefixScale (v i)) := by
  refine {
    measurable :=
      (pairEndpointPrefixCutoff_contDiff l endpointScale prefixScale).continuous.measurable
    bounded := ⟨1, ?_⟩
    lineTest := ?_
  }
  · intro w
    rw [abs_of_nonneg (pairEndpointPrefixCutoff_nonneg l endpointScale prefixScale w)]
    exact pairEndpointPrefixCutoff_le_one l endpointScale prefixScale w
  · intro i a
    exact pairEndpointPrefixCutoff_isBoundedC4Test_line
      l endpointScale prefixScale a (v i)

/-- Joint Rademacher-to-Gaussian comparison for two endpoint/prefix cutoffs
driven by the same signs. -/
theorem pairEndpointPrefixCutoff_rademacher_gaussian_replacement (n l : ℕ)
    (endpointScale prefixScale : ℝ) (v : Fin n → PairIncrementSpace l) :
    |∫ x, pairEndpointPrefixCutoff l endpointScale prefixScale
          (CutoffLindebergBridge.NormedLindeberg.linearCombination v x)
          ∂Erdos88.Invariance.rademacherProductMeasure n -
        ∫ x, pairEndpointPrefixCutoff l endpointScale prefixScale
          (CutoffLindebergBridge.NormedLindeberg.linearCombination v x)
          ∂Erdos88.Invariance.gaussianProductMeasure n| ≤
      ∑ i, pairEndpointPrefixDirectionBudget l endpointScale prefixScale (v i) / 6 := by
  exact CutoffLindebergBridge.NormedLindeberg.rademacher_gaussian_replacement
    (pairEndpointPrefixCutoff l endpointScale prefixScale) v
    (fun i ↦ pairEndpointPrefixDirectionBudget l endpointScale prefixScale (v i))
    (pairEndpointPrefixCutoff_isBoundedC4OnLines n l endpointScale prefixScale v)

def phaseRademacherExpectation {n l : ℕ} (endpointScale prefixScale : ℝ)
    (v : Fin n → Fin l → ℂ) : ℝ :=
  ∫ x, endpointPrefixCutoff l endpointScale prefixScale
      (CutoffLindebergBridge.NormedLindeberg.linearCombination v x)
    ∂Erdos88.Invariance.rademacherProductMeasure n

def phaseGaussianExpectation {n l : ℕ} (endpointScale prefixScale : ℝ)
    (v : Fin n → Fin l → ℂ) : ℝ :=
  ∫ x, endpointPrefixCutoff l endpointScale prefixScale
      (CutoffLindebergBridge.NormedLindeberg.linearCombination v x)
    ∂Erdos88.Invariance.gaussianProductMeasure n

def pairRademacherExpectation {n l : ℕ} (endpointScale prefixScale : ℝ)
    (v : Fin n → PairIncrementSpace l) : ℝ :=
  ∫ x, pairEndpointPrefixCutoff l endpointScale prefixScale
      (CutoffLindebergBridge.NormedLindeberg.linearCombination v x)
    ∂Erdos88.Invariance.rademacherProductMeasure n

def pairGaussianExpectation {n l : ℕ} (endpointScale prefixScale : ℝ)
    (v : Fin n → PairIncrementSpace l) : ℝ :=
  ∫ x, pairEndpointPrefixCutoff l endpointScale prefixScale
      (CutoffLindebergBridge.NormedLindeberg.linearCombination v x)
    ∂Erdos88.Invariance.gaussianProductMeasure n

@[simp] lemma pair_linearCombination_apply {n l : ℕ}
    (v : Fin n → PairIncrementSpace l) (x : Fin n → ℝ) (q : Fin 2) :
    CutoffLindebergBridge.NormedLindeberg.linearCombination v x q =
      CutoffLindebergBridge.NormedLindeberg.linearCombination (fun i ↦ v i q) x := by
  simp [CutoffLindebergBridge.NormedLindeberg.linearCombination]

lemma pair_cutoff_linearCombination_eq {n l : ℕ}
    (endpointScale prefixScale : ℝ) (v : Fin n → PairIncrementSpace l)
    (x : Fin n → ℝ) :
    pairEndpointPrefixCutoff l endpointScale prefixScale
        (CutoffLindebergBridge.NormedLindeberg.linearCombination v x) =
      endpointPrefixCutoff l endpointScale prefixScale
          (CutoffLindebergBridge.NormedLindeberg.linearCombination (fun i ↦ v i 0) x) *
        endpointPrefixCutoff l endpointScale prefixScale
          (CutoffLindebergBridge.NormedLindeberg.linearCombination (fun i ↦ v i 1) x) := by
  rw [pairEndpointPrefixCutoff_eq]
  simp only [pair_linearCombination_apply]

lemma pairRademacherExpectation_eq_integral_mul {n l : ℕ}
    (endpointScale prefixScale : ℝ) (v : Fin n → PairIncrementSpace l) :
    pairRademacherExpectation endpointScale prefixScale v =
      ∫ x,
        endpointPrefixCutoff l endpointScale prefixScale
            (CutoffLindebergBridge.NormedLindeberg.linearCombination (fun i ↦ v i 0) x) *
          endpointPrefixCutoff l endpointScale prefixScale
            (CutoffLindebergBridge.NormedLindeberg.linearCombination (fun i ↦ v i 1) x)
        ∂Erdos88.Invariance.rademacherProductMeasure n := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦
    pair_cutoff_linearCombination_eq endpointScale prefixScale v x

lemma pairGaussianExpectation_eq_integral_mul {n l : ℕ}
    (endpointScale prefixScale : ℝ) (v : Fin n → PairIncrementSpace l) :
    pairGaussianExpectation endpointScale prefixScale v =
      ∫ x,
        endpointPrefixCutoff l endpointScale prefixScale
            (CutoffLindebergBridge.NormedLindeberg.linearCombination (fun i ↦ v i 0) x) *
          endpointPrefixCutoff l endpointScale prefixScale
            (CutoffLindebergBridge.NormedLindeberg.linearCombination (fun i ↦ v i 1) x)
        ∂Erdos88.Invariance.gaussianProductMeasure n := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦
    pair_cutoff_linearCombination_eq endpointScale prefixScale v x

lemma phase_expectation_mem_unit {n l : ℕ} (endpointScale prefixScale : ℝ)
    (v : Fin n → Fin l → ℂ)
    (P : Measure (Fin n → ℝ)) [IsProbabilityMeasure P] :
    0 ≤ ∫ x, endpointPrefixCutoff l endpointScale prefixScale
        (CutoffLindebergBridge.NormedLindeberg.linearCombination v x) ∂P ∧
      (∫ x, endpointPrefixCutoff l endpointScale prefixScale
        (CutoffLindebergBridge.NormedLindeberg.linearCombination v x) ∂P) ≤ 1 := by
  let f : (Fin n → ℝ) → ℝ := fun x ↦
    endpointPrefixCutoff l endpointScale prefixScale
      (CutoffLindebergBridge.NormedLindeberg.linearCombination v x)
  have hfmeas : Measurable f :=
    (endpointPrefixCutoff_contDiff l endpointScale prefixScale).continuous.measurable.comp
      (CutoffLindebergBridge.NormedLindeberg.measurable_linearCombination v)
  have hfint : Integrable f P := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hfmeas.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (endpointPrefixCutoff_nonneg l endpointScale prefixScale _)]
      exact endpointPrefixCutoff_le_one l endpointScale prefixScale _
  constructor
  · exact integral_nonneg fun x ↦ endpointPrefixCutoff_nonneg
      l endpointScale prefixScale _
  · calc
      ∫ x, f x ∂P ≤ ∫ _x, (1 : ℝ) ∂P :=
        integral_mono hfint (integrable_const _) fun x ↦
          endpointPrefixCutoff_le_one l endpointScale prefixScale _
      _ = 1 := by simp

lemma phase_rademacher_expectation_mem_unit {n l : ℕ}
    (endpointScale prefixScale : ℝ) (v : Fin n → Fin l → ℂ) :
    0 ≤ phaseRademacherExpectation endpointScale prefixScale v ∧
      phaseRademacherExpectation endpointScale prefixScale v ≤ 1 := by
  exact phase_expectation_mem_unit endpointScale prefixScale v _

lemma phase_gaussian_expectation_mem_unit {n l : ℕ}
    (endpointScale prefixScale : ℝ) (v : Fin n → Fin l → ℂ) :
    0 ≤ phaseGaussianExpectation endpointScale prefixScale v ∧
      phaseGaussianExpectation endpointScale prefixScale v ≤ 1 := by
  exact phase_expectation_mem_unit endpointScale prefixScale v _

lemma phase_replacement {n l : ℕ} (endpointScale prefixScale : ℝ)
    (v : Fin n → Fin l → ℂ) :
    |phaseRademacherExpectation endpointScale prefixScale v -
        phaseGaussianExpectation endpointScale prefixScale v| ≤
      ∑ i, endpointPrefixDirectionBudget l endpointScale prefixScale (v i) / 6 := by
  exact endpointPrefixCutoff_rademacher_gaussian_replacement
    n l endpointScale prefixScale v

lemma pair_replacement {n l : ℕ} (endpointScale prefixScale : ℝ)
    (v : Fin n → PairIncrementSpace l) :
    |pairRademacherExpectation endpointScale prefixScale v -
        pairGaussianExpectation endpointScale prefixScale v| ≤
      ∑ i, pairEndpointPrefixDirectionBudget l endpointScale prefixScale (v i) / 6 := by
  exact pairEndpointPrefixCutoff_rademacher_gaussian_replacement
    n l endpointScale prefixScale v

lemma abs_mul_sub_mul_le_of_unit {a b c d : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    |a * b - c * d| ≤ |a - c| + |b - d| := by
  have habsa : |a| ≤ 1 := by simpa [abs_of_nonneg ha0] using ha1
  have habsd : |d| ≤ 1 := by simpa [abs_of_nonneg hd0] using hd1
  calc
    |a * b - c * d| = |a * (b - d) + d * (a - c)| := by ring_nf
    _ ≤ |a * (b - d)| + |d * (a - c)| := abs_add_le _ _
    _ = |a| * |b - d| + |d| * |a - c| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * |b - d| + 1 * |a - c| := by
      gcongr
    _ = |a - c| + |b - d| := by ring

/-- Telescope the four-real-coordinate Gaussian coupling one increment block
at a time.  The caller supplies the standard hybrid expectations `Q`; the
step identity records that the `j`-th correlated block is replaced by an
independent copy. -/
theorem gaussianPair_block_decoupling
    {b : ℕ}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    (Q : ℕ → ℝ)
    (x₀ x₁ y₀ y₁ : Fin b → H)
    (m : Fin b → ℝ) (hm : ∀ j, 0 ≤ m j) (hmone : ∀ j, m j ≤ 1)
    (hx₁one : ∀ j, ‖x₁ j‖ ≤ 1)
    (hxy₀₀ : ∀ j, |inner ℝ (x₀ j) (y₀ j)| ≤ m j)
    (hxy₀₁ : ∀ j, |inner ℝ (x₀ j) (y₁ j)| ≤ m j)
    (hxy₁₀ : ∀ j, |inner ℝ (x₁ j) (y₀ j)| ≤ m j)
    (hxy₁₁ : ∀ j, |inner ℝ (x₁ j) (y₁ j)| ≤ m j)
    (K : Fin b → ℝ≥0) (f : Fin b → EuclideanSpace ℝ (Fin 4) → ℝ)
    (hf : ∀ j, LipschitzWith (K j) (f j))
    (hstep : ∀ j : Fin b,
      |Q j - Q (j + 1)| =
        GaussianDecoupling.gaussianPairDiscrepancy
          (x₀ j) (x₁ j) (y₀ j) (y₁ j) (f j)) :
    |Q 0 - Q b| ≤
      ∑ j : Fin b, 12 * (K j : ℝ) * (m j) ^ (1 / 4 : ℝ) := by
  calc
    |Q 0 - Q b| ≤ ∑ j : Fin b, |Q j - Q (j + 1)| :=
      Erdos88.Invariance.telescoping_abs Q b
    _ = ∑ j : Fin b,
        GaussianDecoupling.gaussianPairDiscrepancy
          (x₀ j) (x₁ j) (y₀ j) (y₁ j) (f j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hstep j
    _ ≤ ∑ j : Fin b, 12 * (K j : ℝ) * (m j) ^ (1 / 4 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact GaussianDecoupling.gaussianPairDiscrepancy_le_rpow_quarter
        (x₀ j) (x₁ j) (y₀ j) (y₁ j)
        (hm j) (hmone j) (hx₁one j)
        (hxy₀₀ j) (hxy₀₁ j) (hxy₁₀ j) (hxy₁₁ j)
        (f j) (hf j)

/-- The Lindeberg/triangle-inequality wrapper around any Gaussian
factorization estimate.  Together with `gaussianPair_block_decoupling`, this
is the multi-block form of the pair argument. -/
theorem endpointPrefixCutoff_pair_approx_factorization_of_gaussian_bound
    {n l : ℕ} (endpointScale prefixScale : ℝ)
    (v : Fin n → PairIncrementSpace l) {D : ℝ}
    (hgauss :
      |pairGaussianExpectation endpointScale prefixScale v -
          phaseGaussianExpectation endpointScale prefixScale (fun i ↦ v i 0) *
            phaseGaussianExpectation endpointScale prefixScale (fun i ↦ v i 1)| ≤ D) :
    |pairRademacherExpectation endpointScale prefixScale v -
        phaseRademacherExpectation endpointScale prefixScale (fun i ↦ v i 0) *
          phaseRademacherExpectation endpointScale prefixScale (fun i ↦ v i 1)| ≤
      (∑ i, pairEndpointPrefixDirectionBudget l endpointScale prefixScale (v i) / 6) +
      (∑ i, endpointPrefixDirectionBudget l endpointScale prefixScale (v i 0) / 6) +
      (∑ i, endpointPrefixDirectionBudget l endpointScale prefixScale (v i 1) / 6) + D := by
  let Rj := pairRademacherExpectation endpointScale prefixScale v
  let Gj := pairGaussianExpectation endpointScale prefixScale v
  let R₀ := phaseRademacherExpectation endpointScale prefixScale (fun i ↦ v i 0)
  let R₁ := phaseRademacherExpectation endpointScale prefixScale (fun i ↦ v i 1)
  let G₀ := phaseGaussianExpectation endpointScale prefixScale (fun i ↦ v i 0)
  let G₁ := phaseGaussianExpectation endpointScale prefixScale (fun i ↦ v i 1)
  let Bj := ∑ i, pairEndpointPrefixDirectionBudget l endpointScale prefixScale (v i) / 6
  let B₀ := ∑ i, endpointPrefixDirectionBudget l endpointScale prefixScale (v i 0) / 6
  let B₁ := ∑ i, endpointPrefixDirectionBudget l endpointScale prefixScale (v i 1) / 6
  have hjoint : |Rj - Gj| ≤ Bj := by
    exact pair_replacement endpointScale prefixScale v
  have hphase₀ : |R₀ - G₀| ≤ B₀ := by
    exact phase_replacement endpointScale prefixScale (fun i ↦ v i 0)
  have hphase₁ : |R₁ - G₁| ≤ B₁ := by
    exact phase_replacement endpointScale prefixScale (fun i ↦ v i 1)
  have hG₀ := phase_gaussian_expectation_mem_unit
    endpointScale prefixScale (fun i ↦ v i 0)
  have hG₁ := phase_gaussian_expectation_mem_unit
    endpointScale prefixScale (fun i ↦ v i 1)
  have hR₀ := phase_rademacher_expectation_mem_unit
    endpointScale prefixScale (fun i ↦ v i 0)
  have hR₁ := phase_rademacher_expectation_mem_unit
    endpointScale prefixScale (fun i ↦ v i 1)
  have hprod0 : |G₀ * G₁ - R₀ * R₁| ≤ |G₀ - R₀| + |G₁ - R₁| := by
    exact abs_mul_sub_mul_le_of_unit hG₀.1 hG₀.2 hG₁.1 hG₁.2
      hR₀.1 hR₀.2 hR₁.1 hR₁.2
  have hprod : |G₀ * G₁ - R₀ * R₁| ≤ B₀ + B₁ := by
    apply hprod0.trans
    exact add_le_add (by simpa [abs_sub_comm] using hphase₀)
      (by simpa [abs_sub_comm] using hphase₁)
  change |Rj - R₀ * R₁| ≤ Bj + B₀ + B₁ + D
  have hgauss' : |Gj - G₀ * G₁| ≤ D := hgauss
  calc
    |Rj - R₀ * R₁| ≤ |Rj - Gj| + |Gj - R₀ * R₁| :=
      abs_sub_le _ _ _
    _ ≤ |Rj - Gj| + (|Gj - G₀ * G₁| + |G₀ * G₁ - R₀ * R₁|) := by
      gcongr
      exact abs_sub_le _ _ _
    _ ≤ Bj + (D + (B₀ + B₁)) := by
      gcongr
    _ = Bj + B₀ + B₁ + D := by ring

/-- Fully combined multi-block statement: Lindeberg replacement on the joint
two-phase cutoff and on both marginals, followed by blockwise Gaussian
decoupling. -/
theorem endpointPrefixCutoff_pair_approx_factorization_blockwise
    {n l b : ℕ} (endpointScale prefixScale : ℝ)
    (v : Fin n → PairIncrementSpace l)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    (Q : ℕ → ℝ)
    (x₀ x₁ y₀ y₁ : Fin b → H)
    (m : Fin b → ℝ) (hm : ∀ j, 0 ≤ m j) (hmone : ∀ j, m j ≤ 1)
    (hx₁one : ∀ j, ‖x₁ j‖ ≤ 1)
    (hxy₀₀ : ∀ j, |inner ℝ (x₀ j) (y₀ j)| ≤ m j)
    (hxy₀₁ : ∀ j, |inner ℝ (x₀ j) (y₁ j)| ≤ m j)
    (hxy₁₀ : ∀ j, |inner ℝ (x₁ j) (y₀ j)| ≤ m j)
    (hxy₁₁ : ∀ j, |inner ℝ (x₁ j) (y₁ j)| ≤ m j)
    (K : Fin b → ℝ≥0) (f : Fin b → EuclideanSpace ℝ (Fin 4) → ℝ)
    (hf : ∀ j, LipschitzWith (K j) (f j))
    (hstep : ∀ j : Fin b,
      |Q j - Q (j + 1)| =
        GaussianDecoupling.gaussianPairDiscrepancy
          (x₀ j) (x₁ j) (y₀ j) (y₁ j) (f j))
    (hstart : Q 0 = pairGaussianExpectation endpointScale prefixScale v)
    (hend : Q b =
      phaseGaussianExpectation endpointScale prefixScale (fun i ↦ v i 0) *
        phaseGaussianExpectation endpointScale prefixScale (fun i ↦ v i 1)) :
    |pairRademacherExpectation endpointScale prefixScale v -
        phaseRademacherExpectation endpointScale prefixScale (fun i ↦ v i 0) *
          phaseRademacherExpectation endpointScale prefixScale (fun i ↦ v i 1)| ≤
      (∑ i, pairEndpointPrefixDirectionBudget l endpointScale prefixScale (v i) / 6) +
      (∑ i, endpointPrefixDirectionBudget l endpointScale prefixScale (v i 0) / 6) +
      (∑ i, endpointPrefixDirectionBudget l endpointScale prefixScale (v i 1) / 6) +
      ∑ j : Fin b, 12 * (K j : ℝ) * (m j) ^ (1 / 4 : ℝ) := by
  have hblock := gaussianPair_block_decoupling Q x₀ x₁ y₀ y₁ m hm hmone
    hx₁one hxy₀₀ hxy₀₁ hxy₁₀ hxy₁₁ K f hf hstep
  have hgauss :
      |pairGaussianExpectation endpointScale prefixScale v -
          phaseGaussianExpectation endpointScale prefixScale (fun i ↦ v i 0) *
            phaseGaussianExpectation endpointScale prefixScale (fun i ↦ v i 1)| ≤
        ∑ j : Fin b, 12 * (K j : ℝ) * (m j) ^ (1 / 4 : ℝ) := by
    rw [← hstart, ← hend]
    exact hblock
  exact endpointPrefixCutoff_pair_approx_factorization_of_gaussian_bound
    endpointScale prefixScale v hgauss

/-- Application-ready two-phase approximate factorization.  `hcorr` and
`hind` are only representation identities: they identify the joint Gaussian
cutoff expectation and the product of its marginals with, respectively, the
correlated and independent Hilbert-space Gaussian models used by the
Gram--Schmidt decoupling theorem.  All approximation errors are explicit. -/
theorem endpointPrefixCutoff_pair_approx_factorization
    {n l : ℕ} (endpointScale prefixScale : ℝ)
    (v : Fin n → PairIncrementSpace l)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    (x₀ x₁ y₀ y₁ : H) {m : ℝ} (hm : 0 ≤ m) (hmone : m ≤ 1)
    (hx₁one : ‖x₁‖ ≤ 1)
    (hxy₀₀ : |inner ℝ x₀ y₀| ≤ m)
    (hxy₀₁ : |inner ℝ x₀ y₁| ≤ m)
    (hxy₁₀ : |inner ℝ x₁ y₀| ≤ m)
    (hxy₁₁ : |inner ℝ x₁ y₁| ≤ m)
    {K : ℝ≥0} (f : EuclideanSpace ℝ (Fin 4) → ℝ) (hf : LipschitzWith K f)
    (hcorr :
      pairGaussianExpectation endpointScale prefixScale v =
        ∫ z : PiLp 2 (fun _ : Fin 2 ↦ H),
          f (GaussianDecoupling.innerFamilyCLM
            (![GaussianDecoupling.pairL2 x₀ 0, GaussianDecoupling.pairL2 x₁ 0,
                GaussianDecoupling.pairL2 y₀ 0, GaussianDecoupling.pairL2 y₁ 0] :
              Fin 4 → PiLp 2 (fun _ : Fin 2 ↦ H)) z)
          ∂(stdGaussian (PiLp 2 (fun _ : Fin 2 ↦ H))))
    (hind :
      phaseGaussianExpectation endpointScale prefixScale (fun i ↦ v i 0) *
          phaseGaussianExpectation endpointScale prefixScale (fun i ↦ v i 1) =
        ∫ z : PiLp 2 (fun _ : Fin 2 ↦ H),
          f (GaussianDecoupling.innerFamilyCLM
            (![GaussianDecoupling.pairL2 x₀ 0, GaussianDecoupling.pairL2 x₁ 0,
                GaussianDecoupling.pairL2 0 y₀, GaussianDecoupling.pairL2 0 y₁] :
              Fin 4 → PiLp 2 (fun _ : Fin 2 ↦ H)) z)
          ∂(stdGaussian (PiLp 2 (fun _ : Fin 2 ↦ H)))) :
    |pairRademacherExpectation endpointScale prefixScale v -
        phaseRademacherExpectation endpointScale prefixScale (fun i ↦ v i 0) *
          phaseRademacherExpectation endpointScale prefixScale (fun i ↦ v i 1)| ≤
      (∑ i, pairEndpointPrefixDirectionBudget l endpointScale prefixScale (v i) / 6) +
      (∑ i, endpointPrefixDirectionBudget l endpointScale prefixScale (v i 0) / 6) +
      (∑ i, endpointPrefixDirectionBudget l endpointScale prefixScale (v i 1) / 6) +
      12 * (K : ℝ) * m ^ (1 / 4 : ℝ) := by
  let Rj := pairRademacherExpectation endpointScale prefixScale v
  let Gj := pairGaussianExpectation endpointScale prefixScale v
  let R₀ := phaseRademacherExpectation endpointScale prefixScale (fun i ↦ v i 0)
  let R₁ := phaseRademacherExpectation endpointScale prefixScale (fun i ↦ v i 1)
  let G₀ := phaseGaussianExpectation endpointScale prefixScale (fun i ↦ v i 0)
  let G₁ := phaseGaussianExpectation endpointScale prefixScale (fun i ↦ v i 1)
  let Bj := ∑ i, pairEndpointPrefixDirectionBudget l endpointScale prefixScale (v i) / 6
  let B₀ := ∑ i, endpointPrefixDirectionBudget l endpointScale prefixScale (v i 0) / 6
  let B₁ := ∑ i, endpointPrefixDirectionBudget l endpointScale prefixScale (v i 1) / 6
  let D := 12 * (K : ℝ) * m ^ (1 / 4 : ℝ)
  have hjoint : |Rj - Gj| ≤ Bj := by
    exact pair_replacement endpointScale prefixScale v
  have hphase₀ : |R₀ - G₀| ≤ B₀ := by
    exact phase_replacement endpointScale prefixScale (fun i ↦ v i 0)
  have hphase₁ : |R₁ - G₁| ≤ B₁ := by
    exact phase_replacement endpointScale prefixScale (fun i ↦ v i 1)
  have hdec0 := GaussianDecoupling.gaussianPairDiscrepancy_le_rpow_quarter
    x₀ x₁ y₀ y₁ hm hmone hx₁one hxy₀₀ hxy₀₁ hxy₁₀ hxy₁₁ f hf
  have hdec : |Gj - G₀ * G₁| ≤ D := by
    dsimp only [Gj, G₀, G₁, D]
    rw [hcorr, hind]
    simpa only [GaussianDecoupling.gaussianPairDiscrepancy] using hdec0
  have hG₀ := phase_gaussian_expectation_mem_unit
    endpointScale prefixScale (fun i ↦ v i 0)
  have hG₁ := phase_gaussian_expectation_mem_unit
    endpointScale prefixScale (fun i ↦ v i 1)
  have hR₀ := phase_rademacher_expectation_mem_unit
    endpointScale prefixScale (fun i ↦ v i 0)
  have hR₁ := phase_rademacher_expectation_mem_unit
    endpointScale prefixScale (fun i ↦ v i 1)
  have hprod0 : |G₀ * G₁ - R₀ * R₁| ≤ |G₀ - R₀| + |G₁ - R₁| := by
    exact abs_mul_sub_mul_le_of_unit hG₀.1 hG₀.2 hG₁.1 hG₁.2
      hR₀.1 hR₀.2 hR₁.1 hR₁.2
  have hprod : |G₀ * G₁ - R₀ * R₁| ≤ B₀ + B₁ := by
    apply hprod0.trans
    exact add_le_add (by simpa [abs_sub_comm] using hphase₀)
      (by simpa [abs_sub_comm] using hphase₁)
  change |Rj - R₀ * R₁| ≤ Bj + B₀ + B₁ + D
  calc
    |Rj - R₀ * R₁| ≤ |Rj - Gj| + |Gj - R₀ * R₁| :=
      abs_sub_le _ _ _
    _ ≤ |Rj - Gj| + (|Gj - G₀ * G₁| + |G₀ * G₁ - R₀ * R₁|) := by
      gcongr
      exact abs_sub_le _ _ _
    _ ≤ Bj + (D + (B₀ + B₁)) := by
      gcongr
    _ = Bj + B₀ + B₁ + D := by ring

end
end PairFactorization

/-! ## Finite-grid branching and compact survival -/

namespace FiniteGridBranching

open MeasureTheory ProbabilityTheory Set

noncomputable section

variable {Ω ι X : Type*} [MeasurableSpace Ω]

/-- The smooth survivor count on a finite candidate grid. -/
def weightedCount (C : Finset ι) (w : ι → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ x ∈ C, w x ω

lemma weightedCount_memLp_two (μ : Measure Ω) (C : Finset ι)
    (w : ι → Ω → ℝ) (hw : ∀ x ∈ C, MemLp (w x) 2 μ) :
    MemLp (weightedCount C w) 2 μ := by
  classical
  induction C using Finset.induction_on with
  | empty =>
      change MemLp (fun _ω ↦ ∑ x ∈ (∅ : Finset ι), w x _ω) 2 μ
      simp
  | @insert x C hx ih =>
      change MemLp (fun ω ↦ ∑ y ∈ insert x C, w y ω) 2 μ
      simp only [Finset.sum_insert hx]
      have hxmem : MemLp (w x) 2 μ := hw x (Finset.mem_insert_self x C)
      have hrest : MemLp (fun ω ↦ ∑ y ∈ C, w y ω) 2 μ := by
        apply ih
        intro y hy
        exact hw y (Finset.mem_insert_of_mem hy)
      exact hxmem.add hrest

lemma integral_weightedCount (μ : Measure Ω) (C : Finset ι)
    (w : ι → Ω → ℝ) (hw : ∀ x ∈ C, Integrable (w x) μ) :
    μ[weightedCount C w] = ∑ x ∈ C, μ[w x] := by
  exact integral_finset_sum C hw

lemma weightedCount_sq (C : Finset ι) (w : ι → Ω → ℝ) (ω : Ω) :
    weightedCount C w ω ^ 2 =
      ∑ x ∈ C, ∑ y ∈ C, w x ω * w y ω := by
  simp only [weightedCount, pow_two, Finset.sum_mul_sum]

lemma integral_weightedCount_sq (μ : Measure Ω) [IsFiniteMeasure μ]
    (C : Finset ι)
    (w : ι → Ω → ℝ) (hw : ∀ x ∈ C, MemLp (w x) 2 μ) :
    μ[(weightedCount C w) ^ 2] =
      ∑ x ∈ C, ∑ y ∈ C, μ[fun ω ↦ w x ω * w y ω] := by
  rw [show (weightedCount C w : Ω → ℝ) ^ 2 =
      (fun ω ↦ ∑ x ∈ C, ∑ y ∈ C, w x ω * w y ω) by
    funext ω
    exact weightedCount_sq C w ω]
  calc
    (∫ ω, ∑ x ∈ C, ∑ y ∈ C, w x ω * w y ω ∂μ) =
        ∑ x ∈ C, ∫ ω, ∑ y ∈ C, w x ω * w y ω ∂μ := by
      apply integral_finset_sum C
      intro x hx
      apply integrable_finsetSum C
      intro y hy
      have hxy : MemLp (fun ω ↦ w x ω * w y ω) 1 μ := by
        exact (hw y hy).mul (hw x hx)
      exact hxy.integrable (by norm_num)
    _ = ∑ x ∈ C, ∑ y ∈ C, μ[fun ω ↦ w x ω * w y ω] := by
      apply Finset.sum_congr rfl
      intro x hx
      apply integral_finset_sum C
      intro y hy
      have hxy : MemLp (fun ω ↦ w x ω * w y ω) 1 μ := by
        exact (hw y hy).mul (hw x hx)
      exact hxy.integrable (by norm_num)

/-- Summing a pointwise pair-factorization estimate gives the required
second-moment estimate.  `pairError` may encode both the small error on
uncorrelated pairs and the trivial error on the exceptional pairs. -/
lemma secondMoment_weightedCount_le (μ : Measure Ω) [IsFiniteMeasure μ]
    (C : Finset ι)
    (w : ι → Ω → ℝ) (pairError : ι → ι → ℝ) (E : ℝ)
    (hw : ∀ x ∈ C, MemLp (w x) 2 μ)
    (hpair : ∀ x ∈ C, ∀ y ∈ C,
      μ[fun ω ↦ w x ω * w y ω] ≤ μ[w x] * μ[w y] + pairError x y)
    (herror : (∑ x ∈ C, ∑ y ∈ C, pairError x y) ≤ E) :
    μ[(weightedCount C w) ^ 2] ≤ μ[weightedCount C w] ^ 2 + E := by
  rw [integral_weightedCount_sq μ C w hw,
    integral_weightedCount μ C w (fun x hx ↦ (hw x hx).integrable (by norm_num))]
  rw [pow_two, Finset.sum_mul_sum]
  calc
    (∑ x ∈ C, ∑ y ∈ C, μ[fun ω ↦ w x ω * w y ω])
        ≤ ∑ x ∈ C, ∑ y ∈ C,
            (μ[w x] * μ[w y] + pairError x y) := by
          exact Finset.sum_le_sum fun x hx ↦ Finset.sum_le_sum fun y hy ↦
            hpair x hx y hy
    _ = (∑ x ∈ C, ∑ y ∈ C, μ[w x] * μ[w y]) +
          ∑ x ∈ C, ∑ y ∈ C, pairError x y := by
        simp only [Finset.sum_add_distrib]
    _ ≤ (∑ x ∈ C, ∑ y ∈ C, μ[w x] * μ[w y]) + E := by gcongr

/-- A large-sieve correlation count is consumed in exactly this form.  On
ordinary pairs the factorization error is `e`; on correlated pairs one pays
one additional unit. -/
lemma pairError_sum_le_of_correlation_count (C : Finset ι)
    (corr : ι → ι → Prop) [DecidableRel corr] {e D : ℝ} (he : 0 ≤ e)
    (hcorr : (∑ x ∈ C, ∑ y ∈ C, if corr x y then (1 : ℝ) else 0) ≤ D) :
    (∑ x ∈ C, ∑ y ∈ C, (e + if corr x y then (1 : ℝ) else 0)) ≤
      e * (C.card : ℝ) ^ 2 + D := by
  have heq : (∑ x ∈ C, ∑ y ∈ C,
      (e + if corr x y then (1 : ℝ) else 0)) =
      e * (C.card : ℝ) ^ 2 +
        ∑ x ∈ C, ∑ y ∈ C, (if corr x y then (1 : ℝ) else 0) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const]
    push_cast
    ring
  rw [heq]
  gcongr

/-- Pointwise one-point estimates sum to a lower bound for the expected
smooth survivor count. -/
lemma mean_weightedCount_ge (μ : Measure Ω) (C : Finset ι)
    (w : ι → Ω → ℝ) {p : ℝ}
    (hw : ∀ x ∈ C, Integrable (w x) μ)
    (hone : ∀ x ∈ C, p ≤ μ[w x]) :
    p * (C.card : ℝ) ≤ μ[weightedCount C w] := by
  rw [integral_weightedCount μ C w hw]
  calc
    p * (C.card : ℝ) = ∑ _x ∈ C, p := by simp [mul_comm]
    _ ≤ ∑ x ∈ C, μ[w x] := Finset.sum_le_sum fun x hx ↦ hone x hx

/-- The one-generation estimate in the form needed by the branching
argument.  The hypotheses are exactly: a one-point lower bound and a total
pair-error bound. -/
theorem measure_weightedCount_lt_half_lower_le
    (μ : Measure Ω) [IsProbabilityMeasure μ] (C : Finset ι)
    (w : ι → Ω → ℝ) {p E : ℝ}
    (hp : 0 < p) (hC : C.Nonempty) (hE : 0 ≤ E)
    (hw : ∀ x ∈ C, MemLp (w x) 2 μ)
    (hone : ∀ x ∈ C, p ≤ μ[w x])
    (hsecond : μ[(weightedCount C w) ^ 2] ≤
      μ[weightedCount C w] ^ 2 + E) :
    μ {ω | weightedCount C w ω < p * (C.card : ℝ) / 2} ≤
      ENNReal.ofReal (4 * E / (p * (C.card : ℝ)) ^ 2) := by
  let Y := weightedCount C w
  let lower : ℝ := p * (C.card : ℝ)
  have hcard : (0 : ℝ) < C.card := by exact_mod_cast hC.card_pos
  have hlower : 0 < lower := mul_pos hp hcard
  have hY : MemLp Y 2 μ := weightedCount_memLp_two μ C w hw
  have hmean : lower ≤ μ[Y] := mean_weightedCount_ge μ C w
    (fun x hx ↦ (hw x hx).integrable (by norm_num)) hone
  have hvar : Var[Y; μ] ≤ E := by
    rw [variance_eq_sub hY]
    linarith
  let c : ℝ := μ[Y] - lower / 2
  have hc : 0 < c := by dsimp [c]; linarith
  have hcheb := Erdos527.measure_lt_expectation_sub_le μ hY hc hvar
  have hset : {ω | Y ω < μ[Y] - c} = {ω | Y ω < lower / 2} := by
    ext ω
    simp only [mem_setOf_eq]
    dsimp [c]
    ring_nf
  rw [hset] at hcheb
  change μ {ω | Y ω < lower / 2} ≤ _
  refine hcheb.trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hc_lower : lower / 2 ≤ c := by dsimp [c]; linarith
  have hc0 : 0 ≤ c := le_of_lt hc
  have hhalf0 : 0 < lower / 2 := by positivity
  have hc_sq : (lower / 2) ^ 2 ≤ c ^ 2 := by nlinarith
  have hdiv : E / c ^ 2 ≤ E / (lower / 2) ^ 2 := by
    exact div_le_div_of_nonneg_left hE (sq_pos_of_pos hhalf0) hc_sq
  calc
    E / c ^ 2 ≤ E / (lower / 2) ^ 2 := hdiv
    _ = 4 * E / lower ^ 2 := by field_simp; ring

/-- The total pair-error specialization that exposes the usual two analytic
inputs: a uniform error `e` off the correlation relation, and an ordered
correlated-pair count `D`. -/
theorem measure_weightedCount_lt_half_of_pair_bounds
    (μ : Measure Ω) [IsProbabilityMeasure μ] (C : Finset ι)
    (w : ι → Ω → ℝ) (corr : ι → ι → Prop) [DecidableRel corr]
    {p e D : ℝ} (hp : 0 < p) (hC : C.Nonempty) (he : 0 ≤ e) (hD : 0 ≤ D)
    (hw : ∀ x ∈ C, MemLp (w x) 2 μ)
    (hone : ∀ x ∈ C, p ≤ μ[w x])
    (hpair : ∀ x ∈ C, ∀ y ∈ C,
      μ[fun ω ↦ w x ω * w y ω] ≤
        μ[w x] * μ[w y] + (e + if corr x y then 1 else 0))
    (hcorr : (∑ x ∈ C, ∑ y ∈ C, if corr x y then (1 : ℝ) else 0) ≤ D) :
    μ {ω | weightedCount C w ω < p * (C.card : ℝ) / 2} ≤
      ENNReal.ofReal
        (4 * (e * (C.card : ℝ) ^ 2 + D) / (p * (C.card : ℝ)) ^ 2) := by
  have hE : 0 ≤ e * (C.card : ℝ) ^ 2 + D := by positivity
  apply measure_weightedCount_lt_half_lower_le μ C w hp hC hE hw hone
  apply secondMoment_weightedCount_le μ C w
    (fun x y ↦ e + if corr x y then 1 else 0)
    (e * (C.card : ℝ) ^ 2 + D) hw hpair
  exact pairError_sum_le_of_correlation_count C corr he hcorr

/-- Actual alive children are those candidates on which the (hard) goodness
predicate holds. -/
def aliveCandidates (C : Finset ι) (good : ι → Ω → Prop)
    [∀ x ω, Decidable (good x ω)] (ω : Ω) : Finset ι :=
  C.filter fun x ↦ good x ω

/-- The smooth cutoff is bounded above by the hard survivor indicator, hence
the weighted count is bounded by the number of actual alive children. -/
lemma weightedCount_le_card_aliveCandidates (C : Finset ι)
    (w : ι → Ω → ℝ) (good : ι → Ω → Prop)
    [∀ x ω, Decidable (good x ω)]
    (hsandwich : ∀ x ∈ C, ∀ ω,
      w x ω ≤ if good x ω then 1 else 0) (ω : Ω) :
    weightedCount C w ω ≤ ((aliveCandidates C good ω).card : ℝ) := by
  rw [weightedCount]
  calc
    (∑ x ∈ C, w x ω) ≤
        ∑ x ∈ C, (if good x ω then (1 : ℝ) else 0) :=
      Finset.sum_le_sum fun x hx ↦ hsandwich x hx ω
    _ = ((aliveCandidates C good ω).card : ℝ) := by
      simp [aliveCandidates]

/-- Fully packaged one-generation grid transition: pair estimates for the
smooth cutoff imply a lower-tail estimate for the cardinality of the hard
alive-child set.  The desired next-generation size `s` only has to fit below
half of the first-moment lower bound. -/
theorem measure_aliveCandidates_card_lt_of_pair_bounds
    (μ : Measure Ω) [IsProbabilityMeasure μ] (C : Finset ι)
    (w : ι → Ω → ℝ) (good : ι → Ω → Prop)
    [∀ x ω, Decidable (good x ω)]
    (corr : ι → ι → Prop) [DecidableRel corr]
    {p e D s : ℝ} (hp : 0 < p) (hC : C.Nonempty)
    (he : 0 ≤ e) (hD : 0 ≤ D)
    (hs : s ≤ p * (C.card : ℝ) / 2)
    (hw : ∀ x ∈ C, MemLp (w x) 2 μ)
    (hone : ∀ x ∈ C, p ≤ μ[w x])
    (hpair : ∀ x ∈ C, ∀ y ∈ C,
      μ[fun ω ↦ w x ω * w y ω] ≤
        μ[w x] * μ[w y] + (e + if corr x y then 1 else 0))
    (hcorr : (∑ x ∈ C, ∑ y ∈ C, if corr x y then (1 : ℝ) else 0) ≤ D)
    (hsandwich : ∀ x ∈ C, ∀ ω,
      w x ω ≤ if good x ω then 1 else 0) :
    μ {ω | ((aliveCandidates C good ω).card : ℝ) < s} ≤
      ENNReal.ofReal
        (4 * (e * (C.card : ℝ) ^ 2 + D) / (p * (C.card : ℝ)) ^ 2) := by
  refine (measure_mono ?_).trans
    (measure_weightedCount_lt_half_of_pair_bounds μ C w corr hp hC he hD
      hw hone hpair hcorr)
  intro ω hω
  change weightedCount C w ω < p * (C.card : ℝ) / 2
  exact (weightedCount_le_card_aliveCandidates C w good hsandwich ω).trans_lt
    (hω.trans_le hs)

/-! ### Assembly across generations -/

variable [TopologicalSpace X]

/-- The quantitative size invariant at generation `k`. -/
def StrongAt (A : ℕ → Ω → Finset X) (size : ℕ → ℕ) (k : ℕ) : Set Ω :=
  {ω | size k ≤ (A k ω).card}

/-- A transition fails only when its parent satisfies the size invariant but
its child does not.  This formulation is what a conditional-on-the-past
one-generation estimate bounds after integration over all past histories. -/
def transitionFailure (A : ℕ → Ω → Finset X) (size : ℕ → ℕ)
    (k : ℕ) : Set Ω :=
  StrongAt A size k \ StrongAt A size (k + 1)

/-- No quantitative branching transition fails from `start` onward. -/
def NoTransitionFailureFrom (A : ℕ → Ω → Finset X)
    (size : ℕ → ℕ) (start : ℕ) : Set Ω :=
  {ω | ∀ k ≥ start, ω ∉ transitionFailure A size k}

/-- The quantitative size invariant holds at every generation from `start`. -/
def AllStrongFrom (A : ℕ → Ω → Finset X)
    (size : ℕ → ℕ) (start : ℕ) : Set Ω :=
  {ω | ∀ k ≥ start, ω ∈ StrongAt A size k}

lemma noTransitionFailure_implies_allStrong
    (A : ℕ → Ω → Finset X) (size : ℕ → ℕ) (start : ℕ) (ω : Ω)
    (hstart : ω ∈ StrongAt A size start)
    (hno : ω ∈ NoTransitionFailureFrom A size start) :
    ω ∈ AllStrongFrom A size start := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact hstart
  | succ k hk hstrong =>
      by_contra hnext
      exact (hno k hk) ⟨hstrong, hnext⟩

/-- Summable bounds for transition failures imply simultaneous survival of
the quantitative size invariant at all later generations.  Notice that the
failure bound is unconditional but only charges paths whose parent is still
strong; this is exactly the result of integrating a uniform conditional
one-generation estimate. -/
theorem measure_allStrongFrom_ge
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ℕ → Ω → Finset X) (size : ℕ → ℕ) (start : ℕ)
    (b : ℕ → ℝ≥0∞) {η : ℝ≥0∞}
    (hreset : ∀ ω, ω ∈ StrongAt A size start)
    (hmeas : ∀ k ≥ start, MeasurableSet (transitionFailure A size k))
    (hfail : ∀ j, μ (transitionFailure A size (start + j)) ≤ b j)
    (htail : (∑' j, b j) ≤ η) :
    1 - η ≤ μ (AllStrongFrom A size start) := by
  let good : ℕ → Set Ω :=
    fun j ↦ (transitionFailure A size (start + j))ᶜ
  have hgood : ∀ k, MeasurableSet (good k) := by
    intro j
    exact (hmeas (start + j) (Nat.le_add_right start j)).compl
  have htail' : (∑' j, μ ((good j)ᶜ)) ≤ η := by
    calc
      (∑' j, μ ((good j)ᶜ)) ≤ ∑' j, b j := by
        gcongr with j
        simpa only [good, compl_compl] using hfail j
      _ ≤ η := htail
  have hnofail := Erdos527.measure_all_generations_good_ge μ good hgood 0
    (η := η) (by simpa only [Nat.zero_add] using htail')
  refine hnofail.trans (measure_mono ?_)
  intro ω hω
  apply noTransitionFailure_implies_allStrong A size start ω (hreset ω)
  intro k hk
  have hj := hω (k - start) (Nat.zero_le _)
  simpa only [good, mem_compl_iff, Nat.add_sub_of_le hk] using hj

/-- Event that the nested thick alive sets have a common point from the
chosen reset generation onward. -/
def HasLimitPointFrom (K : ℕ → Ω → Set X) (start : ℕ) : Set Ω :=
  {ω | ∃ x, ∀ k ≥ start, x ∈ K k ω}

/-- Pathwise compactness step.  The hypotheses expose exactly what the grid
geometry must prove: positive target sizes, nonempty thickenings of nonempty
alive sets, eventual nesting, one compact initial set, and closedness. -/
theorem hasLimitPointFrom_of_allStrong
    (A : ℕ → Ω → Finset X) (size : ℕ → ℕ) (K : ℕ → Ω → Set X)
    (start : ℕ) (ω : Ω)
    (hsize : ∀ k ≥ start, 0 < size k)
    (hKnonempty : ∀ k ≥ start, (A k ω).Nonempty → (K k ω).Nonempty)
    (hnested : ∀ k ≥ start, K (k + 1) ω ⊆ K k ω)
    (hcompact : IsCompact (K start ω))
    (hclosed : ∀ k ≥ start, IsClosed (K k ω))
    (hstrong : ω ∈ AllStrongFrom A size start) :
    ω ∈ HasLimitPointFrom K start := by
  have hne : ∀ n, (K (start + n) ω).Nonempty := by
    intro n
    apply hKnonempty (start + n) (Nat.le_add_right start n)
    apply Finset.card_pos.mp
    exact (hsize (start + n) (Nat.le_add_right start n)).trans_le
      (hstrong (start + n) (Nat.le_add_right start n))
  have hnested' : ∀ n, K (start + (n + 1)) ω ⊆ K (start + n) ω := by
    intro n
    simpa only [Nat.add_assoc] using
      hnested (start + n) (Nat.le_add_right start n)
  have hclosed' : ∀ n, IsClosed (K (start + n) ω) :=
    fun n ↦ hclosed (start + n) (Nat.le_add_right start n)
  obtain ⟨x, hx⟩ := Erdos527.exists_mem_all_of_nested_compact
    (fun n ↦ K (start + n) ω) hnested' hne hcompact hclosed'
  refine ⟨x, ?_⟩
  intro k hk
  have hx' := hx (k - start)
  simpa only [Nat.add_sub_of_le hk] using hx'

/-- Complete probability wrapper: summable transition failures plus the
finite-grid nesting facts produce, with the same probability lower bound, a
common point of all thick alive generations. -/
theorem measure_hasLimitPointFrom_ge
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ℕ → Ω → Finset X) (size : ℕ → ℕ) (K : ℕ → Ω → Set X)
    (start : ℕ) (b : ℕ → ℝ≥0∞) {η : ℝ≥0∞}
    (hreset : ∀ ω, ω ∈ StrongAt A size start)
    (hmeas : ∀ k ≥ start, MeasurableSet (transitionFailure A size k))
    (hfail : ∀ j, μ (transitionFailure A size (start + j)) ≤ b j)
    (htail : (∑' j, b j) ≤ η)
    (hsize : ∀ k ≥ start, 0 < size k)
    (hKnonempty : ∀ k ≥ start, ∀ ω,
      (A k ω).Nonempty → (K k ω).Nonempty)
    (hnested : ∀ k ≥ start, ∀ ω, K (k + 1) ω ⊆ K k ω)
    (hcompact : ∀ ω, IsCompact (K start ω))
    (hclosed : ∀ k ≥ start, ∀ ω, IsClosed (K k ω)) :
    1 - η ≤ μ (HasLimitPointFrom K start) := by
  refine (measure_allStrongFrom_ge μ A size start b hreset hmeas hfail htail).trans
    (measure_mono ?_)
  intro ω hω
  exact hasLimitPointFrom_of_allStrong A size K start ω hsize
    (fun k hk ↦ hKnonempty k hk ω) (fun k hk ↦ hnested k hk ω)
    (hcompact ω) (fun k hk ↦ hclosed k hk ω) hω

/-! ### Concrete thickening geometry for circle grids -/

variable {Y : Type*} [PseudoMetricSpace Y]

/-- Finite union of closed balls around the alive grid points. -/
def thickAlive (A : Finset Y) (r : ℝ) : Set Y :=
  ⋃ y ∈ A, Metric.closedBall y r

lemma mem_thickAlive_iff {A : Finset Y} {r : ℝ} {x : Y} :
    x ∈ thickAlive A r ↔ ∃ y ∈ A, dist x y ≤ r := by
  simp [thickAlive, dist_comm]

lemma thickAlive_nonempty {A : Finset Y} {r : ℝ}
    (hA : A.Nonempty) (hr : 0 ≤ r) : (thickAlive A r).Nonempty := by
  obtain ⟨y, hy⟩ := hA
  refine ⟨y, ?_⟩
  rw [mem_thickAlive_iff]
  exact ⟨y, hy, by simpa using hr⟩

lemma thickAlive_isClosed (A : Finset Y) (r : ℝ) :
    IsClosed (thickAlive A r) := by
  apply isClosed_biUnion_finset
  intro y hy
  exact Metric.isClosed_closedBall

lemma thickAlive_isCompact [CompactSpace Y] (A : Finset Y) (r : ℝ) :
    IsCompact (thickAlive A r) :=
  (thickAlive_isClosed A r).isCompact

/-- The precise child-radius inequality used to prove successive thick alive
sets are nested.  In the Erdős 527 grids, `dist y x` is the child-parent
radius and `s`,`r` are the next/current thickening radii. -/
lemma thickAlive_mono_of_children {A B : Finset Y} {r s : ℝ}
    (hchild : ∀ y ∈ B, ∃ x ∈ A, dist y x + s ≤ r) :
    thickAlive B s ⊆ thickAlive A r := by
  intro z hz
  rw [mem_thickAlive_iff] at hz ⊢
  obtain ⟨y, hyB, hzy⟩ := hz
  obtain ⟨x, hxA, hyx⟩ := hchild y hyB
  refine ⟨x, hxA, ?_⟩
  calc
    dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
    _ ≤ s + dist y x := by gcongr
    _ = dist y x + s := add_comm _ _
    _ ≤ r := hyx

/-- Specialization of the compact-limit wrapper to the finite unions of
closed balls naturally produced by the cyclic grid construction. -/
theorem measure_exists_mem_all_thickAlive_ge
    {Ω : Type*} [MeasurableSpace Ω] [CompactSpace Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ℕ → Ω → Finset Y) (size : ℕ → ℕ) (radius : ℕ → ℝ)
    (start : ℕ) (b : ℕ → ℝ≥0∞) {η : ℝ≥0∞}
    (hreset : ∀ ω, ω ∈ StrongAt A size start)
    (hmeas : ∀ k ≥ start, MeasurableSet (transitionFailure A size k))
    (hfail : ∀ j, μ (transitionFailure A size (start + j)) ≤ b j)
    (htail : (∑' j, b j) ≤ η)
    (hsize : ∀ k ≥ start, 0 < size k)
    (hradius : ∀ k ≥ start, 0 ≤ radius k)
    (hchild : ∀ k ≥ start, ∀ ω, ∀ y ∈ A (k + 1) ω,
      ∃ x ∈ A k ω, dist y x + radius (k + 1) ≤ radius k) :
    1 - η ≤ μ {ω | ∃ x, ∀ k ≥ start,
      x ∈ thickAlive (A k ω) (radius k)} := by
  let K : ℕ → Ω → Set Y := fun k ω ↦ thickAlive (A k ω) (radius k)
  change 1 - η ≤ μ (HasLimitPointFrom K start)
  apply measure_hasLimitPointFrom_ge μ A size K start b hreset hmeas hfail htail
    hsize
  · intro k hk ω hA
    exact thickAlive_nonempty hA (hradius k hk)
  · intro k hk ω
    exact thickAlive_mono_of_children (hchild k hk ω)
  · intro ω
    exact thickAlive_isCompact _ _
  · intro k hk ω
    exact thickAlive_isClosed _ _

end

end FiniteGridBranching
end Erdos527

namespace Erdos527

open Filter MeasureTheory Set

/-! ## Probability-one terminal-event wrappers -/

section ProbabilityOneWrappers

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- A possibly nonmeasurable property holds almost surely if it contains measurable
sets whose failure probabilities are arbitrarily small. -/
theorem ae_of_arbitrarily_small_measurable_good_sets
    (P : Ω → Prop)
    (hgood : ∀ ε : ℝ≥0∞, 0 < ε → ε ≠ ∞ →
      ∃ G : Set Ω, MeasurableSet G ∧ G ⊆ {ω | P ω} ∧ μ Gᶜ ≤ ε) :
    ∀ᵐ ω ∂μ, P ω := by
  rw [ae_iff]
  apply le_antisymm
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _hzero_top
    have hε' : (0 : ℝ≥0∞) < (ε : ℝ≥0∞) := ENNReal.coe_pos.mpr hε
    rcases hgood (ε : ℝ≥0∞) hε' (ne_of_lt ENNReal.coe_lt_top) with
      ⟨G, hG, hGP, hGfail⟩
    calc
      μ {ω | ¬P ω} ≤ μ Gᶜ := measure_mono (compl_subset_compl.mpr hGP)
      _ ≤ (ε : ℝ≥0∞) := hGfail
      _ = 0 + (ε : ℝ≥0∞) := by simp
  · exact bot_le

variable [IsProbabilityMeasure μ]

/-- The same wrapper in the common `1 - ε` lower-bound form. -/
theorem ae_of_arbitrarily_high_measurable_good_sets
    (P : Ω → Prop)
    (hgood : ∀ ε : ℝ≥0∞, 0 < ε → ε ≤ 1 →
      ∃ G : Set Ω, MeasurableSet G ∧ G ⊆ {ω | P ω} ∧ 1 - ε ≤ μ G) :
    ∀ᵐ ω ∂μ, P ω := by
  apply ae_of_arbitrarily_small_measurable_good_sets μ P
  intro ε hε _hεtop
  let δ := min ε 1
  have hδpos : 0 < δ := lt_min hε one_pos
  have hδone : δ ≤ 1 := min_le_right _ _
  have hδtop : δ ≠ ∞ := ne_of_lt (hδone.trans_lt ENNReal.one_lt_top)
  rcases hgood δ hδpos hδone with ⟨G, hG, hGP, hmass⟩
  refine ⟨G, hG, hGP, ?_⟩
  calc
    μ Gᶜ ≤ 1 - (1 - δ) := prob_compl_le_one_sub_of_le_prob hmass hG
    _ = δ := by
      let d : ℝ≥0 := δ.toNNReal
      have hdcoe : (d : ℝ≥0∞) = δ := ENNReal.coe_toNNReal hδtop
      have hd : d ≤ 1 := by
        rw [← ENNReal.coe_le_coe, ENNReal.coe_one, hdcoe]
        exact hδone
      rw [← hdcoe]
      change (1 : ℝ≥0∞) - (1 - (d : ℝ≥0∞)) = (d : ℝ≥0∞)
      rw [← ENNReal.coe_one, ← ENNReal.coe_sub, ← ENNReal.coe_sub,
        tsub_tsub_cancel_of_le hd]
    _ ≤ ε := min_le_left _ _

/-- If the terminal property is known to be null-measurable, lower bounds
on its own probability suffice. Without `hP`, full outer measure alone does
not imply an almost-everywhere statement. -/
theorem ae_of_probability_lower_bound_real
    (P : Ω → Prop) (hP : NullMeasurableSet {ω | P ω} μ)
    (hmass : ∀ η : ℝ, 0 < η → η ≤ 1 → 1 - η ≤ μ.real {ω | P ω}) :
    ∀ᵐ ω ∂μ, P ω := by
  rw [ae_iff, ← measureReal_eq_zero_iff]
  change μ.real ({ω | P ω}ᶜ) = 0
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro η hη
    let δ := min η 1
    have hδpos : 0 < δ := lt_min hη one_pos
    have hδone : δ ≤ 1 := min_le_right _ _
    rw [probReal_compl_eq_one_sub₀ hP]
    have h := hmass δ hδpos hδone
    have hδeta : δ ≤ η := min_le_left _ _
    linarith
  · exact measureReal_nonneg

/-- Borel--Cantelli wrapper for a truncation-level construction. The desired
terminal property itself need not be measurable. -/
theorem ae_of_summable_truncation_failures
    (P : Ω → Prop) (bad : ℕ → Set Ω) (p : ℕ → ℝ)
    (hp : Summable p) (hbad : ∀ k, μ.real (bad k) ≤ p k)
    (hterminal : ∀ ω, (∀ᶠ k : ℕ in atTop, ω ∉ bad k) → P ω) :
    ∀ᵐ ω ∂μ, P ω := by
  filter_upwards [ae_eventually_notMem_of_measureReal_le bad p hp hbad] with ω hω
  exact hterminal ω hω

/-- Real-valued variant, matching the `Measure.real` estimates used by the
finite-dimensional probability argument. -/
theorem ae_of_arbitrarily_high_measurable_good_sets_real
    (P : Ω → Prop)
    (hgood : ∀ η : ℝ, 0 < η → η ≤ 1 →
      ∃ G : Set Ω, MeasurableSet G ∧ G ⊆ {ω | P ω} ∧ 1 - η ≤ μ.real G) :
    ∀ᵐ ω ∂μ, P ω := by
  rw [ae_iff, ← measureReal_eq_zero_iff]
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro η hη
    let δ := min η 1
    have hδpos : 0 < δ := lt_min hη one_pos
    have hδone : δ ≤ 1 := min_le_right _ _
    rcases hgood δ hδpos hδone with ⟨G, hG, hGP, hmass⟩
    have hGfail : μ.real Gᶜ ≤ δ := by
      rw [probReal_compl_eq_one_sub hG]
      linarith
    calc
      μ.real {ω | ¬P ω} ≤ μ.real Gᶜ :=
        measureReal_mono (compl_subset_compl.mpr hGP)
      _ ≤ δ := hGfail
      _ ≤ η := min_le_left _ _
      _ = 0 + η := by simp
  · exact measureReal_nonneg

end ProbabilityOneWrappers

/-- The exact terminal event in Erdős Problem 527. -/
def convergenceEvent (a : ℕ → ℝ) : Set (ℕ → ℝ) :=
  {ε | ∃ z : ℂ, ‖z‖ = 1 ∧ SeriesConvergesAt a ε z}

/-- Final probability-one wrapper using `ℝ≥0∞` probability estimates. -/
theorem erdos_527_of_probability_lower_bound
    (a : ℕ → ℝ) (_hsq : SquareSumDiverges a)
    (_hsmall : DecaysFasterThanInvSqrt a)
    (hanalytic : ∀ ε : ℝ≥0∞, 0 < ε → ε ≤ 1 →
      ∃ G : Set (ℕ → ℝ), MeasurableSet G ∧ G ⊆ convergenceEvent a ∧
        1 - ε ≤ rademacherProductMeasure G) :
    ∀ᵐ ε ∂rademacherProductMeasure,
      ∃ z : ℂ, ‖z‖ = 1 ∧ SeriesConvergesAt a ε z := by
  exact ae_of_arbitrarily_high_measurable_good_sets rademacherProductMeasure
    (fun ε ↦ ∃ z : ℂ, ‖z‖ = 1 ∧ SeriesConvergesAt a ε z) hanalytic

/-- Final probability-one wrapper using summable truncation failures. -/
theorem erdos_527_of_summable_truncation_failures
    (a : ℕ → ℝ) (_hsq : SquareSumDiverges a)
    (_hsmall : DecaysFasterThanInvSqrt a)
    (bad : ℕ → Set (ℕ → ℝ)) (p : ℕ → ℝ)
    (hp : Summable p)
    (hbad : ∀ k, rademacherProductMeasure.real (bad k) ≤ p k)
    (hterminal : ∀ ε, (∀ᶠ k : ℕ in atTop, ε ∉ bad k) →
      ∃ z : ℂ, ‖z‖ = 1 ∧ SeriesConvergesAt a ε z) :
    ∀ᵐ ε ∂rademacherProductMeasure,
      ∃ z : ℂ, ‖z‖ = 1 ∧ SeriesConvergesAt a ε z := by
  exact ae_of_summable_truncation_failures rademacherProductMeasure
    (fun ε ↦ ∃ z : ℂ, ‖z‖ = 1 ∧ SeriesConvergesAt a ε z)
    bad p hp hbad hterminal

/-- Final probability-one wrapper using real-valued probability estimates. -/
theorem erdos_527_of_probability_lower_bound_real
    (a : ℕ → ℝ) (_hsq : SquareSumDiverges a)
    (_hsmall : DecaysFasterThanInvSqrt a)
    (hanalytic : ∀ η : ℝ, 0 < η → η ≤ 1 →
      ∃ G : Set (ℕ → ℝ), MeasurableSet G ∧ G ⊆ convergenceEvent a ∧
        1 - η ≤ rademacherProductMeasure.real G) :
    ∀ᵐ ε ∂rademacherProductMeasure,
      ∃ z : ℂ, ‖z‖ = 1 ∧ SeriesConvergesAt a ε z := by
  exact ae_of_arbitrarily_high_measurable_good_sets_real
    rademacherProductMeasure
    (fun ε ↦ ∃ z : ℂ, ‖z‖ = 1 ∧ SeriesConvergesAt a ε z) hanalytic

end Erdos527

/- Concrete scalar closure source: E527Partition.lean -/

namespace Erdos527.ScalarGaussianPath

noncomputable section

def prependGreedy (a x : ℝ) : List (List ℝ) → List (List ℝ)
  | [] => [[x]]
  | b :: bs => if b.sum < a then (x :: b) :: bs else [x] :: b :: bs

def greedyChunks (a : ℝ) : List ℝ → List (List ℝ)
  | [] => []
  | x :: xs => prependGreedy a x (greedyChunks a xs)

lemma greedyChunks_spec (a : ℝ) (ha : 0 ≤ a) (xs : List ℝ)
    (hx0 : ∀ x ∈ xs, 0 ≤ x) (hxle : ∀ x ∈ xs, x ≤ a) :
    (greedyChunks a xs).flatten = xs ∧
    (∀ b ∈ greedyChunks a xs, b ≠ []) ∧
    (∀ b ∈ greedyChunks a xs, b.sum ≤ 2 * a) ∧
    (∀ b ∈ (greedyChunks a xs).tail, a ≤ b.sum) := by
  induction xs with
  | nil => simp [greedyChunks]
  | cons x xs ih =>
      have hx0' : 0 ≤ x := hx0 x (by simp)
      have hxle' : x ≤ a := hxle x (by simp)
      have hxs0 : ∀ y ∈ xs, 0 ≤ y := by
        intro y hy
        exact hx0 y (by simp [hy])
      have hxsle : ∀ y ∈ xs, y ≤ a := by
        intro y hy
        exact hxle y (by simp [hy])
      specialize ih hxs0 hxsle
      cases hgc : greedyChunks a xs with
      | nil =>
          have hxs : xs = [] := by simpa [hgc] using ih.1.symm
          subst xs
          simp only [greedyChunks, prependGreedy.eq_def]
          constructor
          · rfl
          constructor
          · intro b hb
            simp only [List.mem_singleton] at hb
            subst b
            simp
          constructor
          · intro b hb
            simp only [List.mem_singleton] at hb
            subst b
            simp only [List.sum_singleton]
            linarith
          · simp
      | cons b bs =>
          have hbmem : b ∈ greedyChunks a xs := by simp [hgc]
          have hbsmem : ∀ c ∈ bs, c ∈ greedyChunks a xs := by
            intro c hc
            simp [hgc, hc]
          by_cases hba : b.sum < a
          · have hb0 : 0 ≤ b.sum := by
              apply List.sum_nonneg
              intro y hy
              apply hxs0 y
              rw [← ih.1]
              simp [hgc, hy]
            have hbne : b ≠ [] := ih.2.1 b hbmem
            have hbhi : b.sum ≤ 2 * a := ih.2.2.1 b hbmem
            have hbstail : ∀ c ∈ bs, a ≤ c.sum := by
              intro c hc
              exact ih.2.2.2 c (by simp [hgc, hc])
            simp only [greedyChunks, hgc, prependGreedy.eq_def, hba, if_pos]
            change ((x :: b) :: bs).flatten = x :: xs ∧
              (∀ c ∈ (x :: b) :: bs, c ≠ []) ∧
              (∀ c ∈ (x :: b) :: bs, c.sum ≤ 2 * a) ∧
              ∀ c ∈ ((x :: b) :: bs).tail, a ≤ c.sum
            constructor
            · simpa [hgc] using ih.1
            constructor
            · intro c hc
              simp only [List.mem_cons] at hc
              rcases hc with rfl | hc
              · simp
              · exact ih.2.1 c (hbsmem c hc)
            constructor
            · intro c hc
              simp only [List.mem_cons] at hc
              rcases hc with rfl | hc
              · simp only [List.sum_cons]
                linarith
              · exact ih.2.2.1 c (hbsmem c hc)
            · simpa using hbstail
          · have hbalow : a ≤ b.sum := le_of_not_gt hba
            have hbne : b ≠ [] := ih.2.1 b hbmem
            have hbhi : b.sum ≤ 2 * a := ih.2.2.1 b hbmem
            have hbstail : ∀ c ∈ bs, a ≤ c.sum := by
              intro c hc
              exact ih.2.2.2 c (by simp [hgc, hc])
            simp only [greedyChunks, hgc, prependGreedy.eq_def, hba, if_neg]
            change ([x] :: b :: bs).flatten = x :: xs ∧
              (∀ c ∈ [x] :: b :: bs, c ≠ []) ∧
              (∀ c ∈ [x] :: b :: bs, c.sum ≤ 2 * a) ∧
              ∀ c ∈ ([x] :: b :: bs).tail, a ≤ c.sum
            constructor
            · simpa [hgc] using ih.1
            constructor
            · intro c hc
              simp only [List.mem_cons] at hc
              rcases hc with rfl | rfl | hc
              · simp
              · exact hbne
              · exact ih.2.1 c (hbsmem c hc)
            constructor
            · intro c hc
              simp only [List.mem_cons] at hc
              rcases hc with rfl | rfl | hc
              · simpa using hxle'.trans (by linarith)
              · exact hbhi
              · exact ih.2.2.1 c (hbsmem c hc)
            · intro c hc
              simp only [List.tail_cons, List.mem_cons] at hc
              rcases hc with rfl | hc
              · exact hbalow
              · exact hbstail c hc

def mergeFirstSmall (a : ℝ) : List (List ℝ) → List (List ℝ)
  | b :: c :: cs => if b.sum < a then (b ++ c) :: cs else b :: c :: cs
  | cs => cs

lemma length_mul_le_sum_map_sum (a : ℝ) (blocks : List (List ℝ))
    (h : ∀ b ∈ blocks, a ≤ b.sum) :
    (blocks.length : ℝ) * a ≤ (blocks.map List.sum).sum := by
  induction blocks with
  | nil => simp
  | cons b bs ih =>
      have hb : a ≤ b.sum := h b (by simp)
      have hbs : ∀ c ∈ bs, a ≤ c.sum := by
        intro c hc
        exact h c (by simp [hc])
      specialize ih hbs
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one, List.map_cons,
        List.sum_cons]
      nlinarith

theorem exists_variance_chunks (a : ℝ) (ha : 0 < a) (xs : List ℝ)
    (hx0 : ∀ x ∈ xs, 0 ≤ x) (hxle : ∀ x ∈ xs, x ≤ a)
    (htotal : a ≤ xs.sum) :
    ∃ blocks : List (List ℝ),
      blocks.flatten = xs ∧
      (∀ b ∈ blocks, b ≠ []) ∧
      (∀ b ∈ blocks, a ≤ b.sum ∧ b.sum ≤ 3 * a) ∧
      (blocks.length : ℝ) * a ≤ xs.sum := by
  have hs := greedyChunks_spec a ha.le xs hx0 hxle
  cases hcs : greedyChunks a xs with
  | nil =>
      have hflat : ([] : List (List ℝ)).flatten = xs := by simpa [hcs] using hs.1
      have hxs : xs = [] := by simpa using hflat.symm
      subst xs
      simp at htotal
      linarith
  | cons b bs =>
      cases hbs : bs with
      | nil =>
          have hflat : [b].flatten = xs := by simpa [hcs, hbs] using hs.1
          have hbxs : b = xs := by simpa using hflat
          have hbmem : b ∈ greedyChunks a xs := by simp [hcs]
          refine ⟨[b], hflat, ?_, ?_, ?_⟩
          · intro c hc
            exact hs.2.1 c (by simpa [hcs, hbs] using hc)
          · intro c hc
            simp only [List.mem_singleton] at hc
            subst c
            exact ⟨by simpa [hbxs] using htotal,
              (hs.2.2.1 b hbmem).trans (by linarith)⟩
          · simp only [List.length_singleton, Nat.cast_one, one_mul]
            simpa [hbxs] using htotal
      | cons c ds =>
          have hshape : greedyChunks a xs = b :: c :: ds := by simpa [hbs] using hcs
          have hflat : (b :: c :: ds).flatten = xs := by simpa [hshape] using hs.1
          have hbmem : b ∈ greedyChunks a xs := by simp [hshape]
          have hcmem : c ∈ greedyChunks a xs := by simp [hshape]
          have htail : ∀ d ∈ c :: ds, a ≤ d.sum := by
            intro d hd
            exact hs.2.2.2 d (by simpa [hshape] using hd)
          by_cases hbsmall : b.sum < a
          · let blocks : List (List ℝ) := (b ++ c) :: ds
            have hblocks_flat : blocks.flatten = xs := by
              simpa [blocks, List.flatten_cons, List.append_assoc] using hflat
            have hblocks_ne : ∀ d ∈ blocks, d ≠ [] := by
              intro d hd
              rcases (by simpa [blocks] using hd : d = b ++ c ∨ d ∈ ds) with rfl | hd
              · exact List.append_ne_nil_of_right_ne_nil b (hs.2.1 c hcmem)
              · exact hs.2.1 d (by simp [hshape, hd])
            have hblocks_bounds : ∀ d ∈ blocks, a ≤ d.sum ∧ d.sum ≤ 3 * a := by
              intro d hd
              rcases (by simpa [blocks] using hd : d = b ++ c ∨ d ∈ ds) with rfl | hd
              · have hclo : a ≤ c.sum := htail c (by simp)
                have hchi : c.sum ≤ 2 * a := hs.2.2.1 c hcmem
                have hb0 : 0 ≤ b.sum := by
                  apply List.sum_nonneg
                  intro x hx
                  apply hx0 x
                  rw [← hblocks_flat]
                  simp [blocks, hx]
                simp only [List.sum_append]
                constructor <;> linarith
              · exact ⟨htail d (by simp [hd]),
                  (hs.2.2.1 d (by simp [hshape, hd])).trans (by linarith)⟩
            refine ⟨blocks, hblocks_flat, hblocks_ne, hblocks_bounds, ?_⟩
            have hlen := length_mul_le_sum_map_sum a blocks
              (fun d hd => (hblocks_bounds d hd).1)
            rw [← List.sum_flatten, hblocks_flat] at hlen
            exact hlen
          · let blocks : List (List ℝ) := b :: c :: ds
            have hblocks_flat : blocks.flatten = xs := by simpa [blocks] using hflat
            have hblocks_ne : ∀ d ∈ blocks, d ≠ [] := by
              intro d hd
              exact hs.2.1 d (by simpa [blocks, hshape] using hd)
            have hblocks_bounds : ∀ d ∈ blocks, a ≤ d.sum ∧ d.sum ≤ 3 * a := by
              intro d hd
              have hdmem : d ∈ greedyChunks a xs := by simpa [blocks, hshape] using hd
              refine ⟨?_, (hs.2.2.1 d hdmem).trans (by linarith)⟩
              rcases (by simpa [blocks] using hd : d = b ∨ d ∈ c :: ds) with rfl | hd
              · exact le_of_not_gt hbsmall
              · exact htail d hd
            refine ⟨blocks, hblocks_flat, hblocks_ne, hblocks_bounds, ?_⟩
            have hlen := length_mul_le_sum_map_sum a blocks
              (fun d hd => (hblocks_bounds d hd).1)
            rw [← List.sum_flatten, hblocks_flat] at hlen
            exact hlen

theorem exists_variance_chunks_fin {n : ℕ} (q : Fin n → ℝ) (u : ℝ)
    (hu : 0 < u) (hq0 : ∀ i, 0 ≤ q i)
    (hqle : ∀ i, q i ≤ u ^ 2 / 128)
    (htotal : u ^ 2 / 128 ≤ ∑ i, q i) :
    ∃ blocks : List (List ℝ),
      blocks.flatten = List.ofFn q ∧
      (∀ b ∈ blocks, b ≠ []) ∧
      (∀ b ∈ blocks, u ^ 2 / 128 ≤ b.sum ∧ b.sum ≤ u ^ 2 / 32) ∧
      (blocks.length : ℝ) ≤ 128 * ((∑ i, q i) / u ^ 2) := by
  let a : ℝ := u ^ 2 / 128
  have ha : 0 < a := by positivity
  have hx0 : ∀ x ∈ List.ofFn q, 0 ≤ x := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact hq0 i
  have hxle : ∀ x ∈ List.ofFn q, x ≤ a := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact hqle i
  have htotal' : a ≤ (List.ofFn q).sum := by
    simpa only [a, List.sum_ofFn] using htotal
  obtain ⟨blocks, hflat, hne, hbounds, hcount⟩ :=
    exists_variance_chunks a ha (List.ofFn q) hx0 hxle htotal'
  refine ⟨blocks, hflat, hne, ?_, ?_⟩
  · intro b hb
    have h := hbounds b hb
    constructor
    · simpa only [a] using h.1
    · calc
        b.sum ≤ 3 * a := h.2
        _ ≤ u ^ 2 / 32 := by
          dsimp [a]
          nlinarith [sq_nonneg u]
  · have hcount' : (blocks.length : ℝ) * a ≤ ∑ i, q i := by
      simpa only [List.sum_ofFn] using hcount
    have hdiv : (blocks.length : ℝ) ≤ (∑ i, q i) / a :=
      (le_div_iff₀ ha).2 hcount'
    calc
      (blocks.length : ℝ) ≤ (∑ i, q i) / a := hdiv
      _ = 128 * ((∑ i, q i) / u ^ 2) := by
        dsimp [a]
        field_simp
        <;> ring

end

end Erdos527.ScalarGaussianPath


/- Concrete scalar closure source: IterateBlocks.lean -/

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Set Filter Finset

namespace Erdos527.ScalarGaussianPath

/-- The trajectory record visible strictly before macroblock `k`. -/
def blockHistory {Ω : Type*} (S : ℕ → ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) :
    ℕ × ℕ → ℝ := fun p ↦ if p.1 < k then S p.1 p.2 ω else 0

/-- The endpoint sum of the first `k` trajectories stored in a history. -/
def historyState (n : ℕ → ℕ) (k : ℕ) (x : ℕ × ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range k, x (j, n j)

/-- All first `k` macroblocks stayed in their translated tube, and their
current endpoint sum lies in the reset core. -/
def historyGood (n : ℕ → ℕ) (u : ℝ) (k : ℕ) : Set (ℕ × ℕ → ℝ) :=
  {x | (∀ j < k, ∀ i : Fin (n j + 1),
      |historyState n j x + x (j, i.1)| ≤ 5 * u / 4) ∧
    historyState n k x ∈ Set.Icc (-u / 4) (u / 4)}

/-- The concrete event after the first `k` macroblocks. -/
def blockGoodEvent {Ω : Type*} (S : ℕ → ℕ → Ω → ℝ)
    (n : ℕ → ℕ) (u : ℝ) (k : ℕ) : Set Ω :=
  blockHistory S k ⁻¹' historyGood n u k

/-- The complete path-and-small-endpoint event, with block `m` reserved for
the final reset. -/
def blockPathEndpointEvent {Ω : Type*} (S : ℕ → ℕ → Ω → ℝ)
    (n : ℕ → ℕ) (u r : ℝ) (m : ℕ) : Set Ω :=
  {ω | ω ∈ blockGoodEvent S n u m ∧
    (∀ i : Fin (n m + 1),
      |historyState n m (blockHistory S m ω) + S m i.1 ω| ≤ 5 * u / 4) ∧
    historyState n m (blockHistory S m ω) + S m (n m) ω ∈ Set.Icc (-r) r}

lemma measurable_blockHistory
    {Ω : Type*} [MeasurableSpace Ω] (S : ℕ → ℕ → Ω → ℝ)
    (hS : ∀ j t, Measurable (S j t)) (k : ℕ) :
    Measurable (blockHistory S k) := by
  rw [measurable_pi_iff]
  intro p
  by_cases hp : p.1 < k
  · simpa [blockHistory, hp] using hS p.1 p.2
  · simp [blockHistory, hp]

lemma measurable_historyState (n : ℕ → ℕ) (k : ℕ) :
    Measurable (historyState n k) := by
  unfold historyState
  fun_prop

lemma measurableSet_historyGood (n : ℕ → ℕ) (u : ℝ) (k : ℕ) :
    MeasurableSet (historyGood n u k) := by
  have hpath : MeasurableSet {x : ℕ × ℕ → ℝ |
      ∀ j < k, ∀ i : Fin (n j + 1),
        |historyState n j x + x (j, i.1)| ≤ 5 * u / 4} := by
    rw [show {x : ℕ × ℕ → ℝ |
        ∀ j < k, ∀ i : Fin (n j + 1),
          |historyState n j x + x (j, i.1)| ≤ 5 * u / 4} =
        ⋂ j : Fin k, ⋂ i : Fin (n j.1 + 1),
          {x | |historyState n j.1 x + x (j.1, i.1)| ≤ 5 * u / 4} by
      ext x
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · intro h j i
        exact h j.1 j.2 i
      · intro h j hj i
        exact h ⟨j, hj⟩ i]
    exact MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun i ↦
      measurableSet_le
        ((measurable_historyState n j.1).add (measurable_pi_apply (j.1, i.1))).abs
        measurable_const
  exact hpath.inter (measurableSet_Icc.preimage (measurable_historyState n k))

lemma blockGoodEvent_zero
    {Ω : Type*} (S : ℕ → ℕ → Ω → ℝ) (n : ℕ → ℕ) (u : ℝ) (hu : 0 < u) :
    blockGoodEvent S n u 0 = Set.univ := by
  ext ω
  constructor
  · intro _
    trivial
  · intro _
    change (∀ j < 0, ∀ i : Fin (n j + 1),
        |historyState n j (blockHistory S 0 ω) + blockHistory S 0 ω (j, i.1)| ≤
          5 * u / 4) ∧
      historyState n 0 (blockHistory S 0 ω) ∈ Set.Icc (-u / 4) (u / 4)
    constructor
    · intro j hj
      omega
    · change (0 : ℝ) ∈ Set.Icc (-u / 4) (u / 4)
      constructor <;> linarith

lemma historyState_blockHistory_mono
    {Ω : Type*} (S : ℕ → ℕ → Ω → ℝ) (n : ℕ → ℕ)
    {j k : ℕ} (hjk : j ≤ k) (ω : Ω) :
    historyState n j (blockHistory S (k + 1) ω) =
      historyState n j (blockHistory S k ω) := by
  unfold historyState blockHistory
  apply Finset.sum_congr rfl
  intro t ht
  have htj : t < j := Finset.mem_range.mp ht
  have htk : t < k := htj.trans_le hjk
  simp [htk, htk.trans (Nat.lt_succ_self k)]

lemma historyState_blockHistory_succ
    {Ω : Type*} (S : ℕ → ℕ → Ω → ℝ) (n : ℕ → ℕ)
    (k : ℕ) (ω : Ω) :
    historyState n (k + 1) (blockHistory S (k + 1) ω) =
      historyState n k (blockHistory S k ω) + S k (n k) ω := by
  simp only [historyState, Finset.sum_range_succ, blockHistory]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j < k := Finset.mem_range.mp hj
  simp [hjk, hjk.trans (Nat.lt_succ_self k)]
  simp [Nat.lt_succ_self k]

lemma blockGoodEvent_step_of
    {Ω : Type*} (S : ℕ → ℕ → Ω → ℝ) (n : ℕ → ℕ)
    (u : ℝ) (k : ℕ) {ω : Ω}
    (hprev : ω ∈ blockGoodEvent S n u k)
    (hpath : ∀ i : Fin (n k + 1),
      |historyState n k (blockHistory S k ω) + S k i.1 ω| ≤ 5 * u / 4)
    (hend : historyState n k (blockHistory S k ω) + S k (n k) ω ∈
      Set.Icc (-u / 4) (u / 4)) :
    ω ∈ blockGoodEvent S n u (k + 1) := by
  rcases hprev with ⟨hprevpath, hprevend⟩
  constructor
  · intro j hj i
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjk | rfl
    · have hold := hprevpath j hjk i
      rw [historyState_blockHistory_mono S n (Nat.le_of_lt hjk)]
      have hcoord : blockHistory S (k + 1) ω (j, i.1) =
          blockHistory S k ω (j, i.1) := by
        simp [blockHistory, hjk, hjk.trans (Nat.lt_succ_self k)]
      rw [hcoord]
      exact hold
    · rw [historyState_blockHistory_mono S n le_rfl]
      simpa [blockHistory, Nat.lt_succ_self] using hpath i
  · rw [historyState_blockHistory_succ]
    exact hend

lemma coreFactor_le_one :
    ((1 / 2 : ℝ≥0∞) *
      ENNReal.ofReal ((1 / 8 : ℝ) * Real.exp (-256))) ≤ 1 := by
  have he : Real.exp (-256) ≤ 1 := by
    simpa using Real.exp_le_one_iff.mpr (by norm_num : (-256 : ℝ) ≤ 0)
  have hr : (1 / 8 : ℝ) * Real.exp (-256) ≤ 1 := by
    nlinarith [Real.exp_pos (-256)]
  calc
    (1 / 2 : ℝ≥0∞) * ENNReal.ofReal ((1 / 8 : ℝ) * Real.exp (-256)) ≤
        1 * 1 := mul_le_mul' (by norm_num) (by simpa using ENNReal.ofReal_le_one.mpr hr)
    _ = 1 := one_mul 1

/-- Concrete iteration of a finite family of independent Gaussian martingale
macroblocks.  The first `m` blocks reset into the core; block `m` makes the
final reset into `[-r,r]`. -/
theorem gaussian_independent_blocks_path_endpoint_lower
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (𝒢 : ℕ → MeasureTheory.Filtration ℕ ‹MeasurableSpace Ω›)
    (S : ℕ → ℕ → Ω → ℝ) (n : ℕ → ℕ) (v : ℕ → ℝ≥0)
    (prefixVar : (k : ℕ) → Fin (n k + 1) → ℝ)
    (hS : ∀ k, MeasureTheory.Martingale (S k) (𝒢 k) P)
    (hL2 : ∀ k j, MemLp (S k j) 2 P)
    (hjoint : ∀ k, ProbabilityTheory.HasGaussianLaw
      (fun ω ↦ (fun i : Fin (n k + 1) ↦ S k i.1 ω, S k (n k) ω)) P)
    (hcov : ∀ k i, ProbabilityTheory.covariance
      (fun ω ↦ S k i.1 ω) (S k (n k)) P = prefixVar k i)
    (hYY : ∀ k, ProbabilityTheory.covariance (S k (n k)) (S k (n k)) P =
      (v k : ℝ))
    (hYlaw : ∀ k, ProbabilityTheory.HasLaw (S k (n k))
      (ProbabilityTheory.gaussianReal 0 (v k)) P)
    (hq0 : ∀ k i, 0 ≤ prefixVar k i / (v k : ℝ))
    (hq1 : ∀ k i, prefixVar k i / (v k : ℝ) ≤ 1)
    (hterminal : ∀ k, ∫ ω, (S k (n k) ω) ^ 2 ∂P ≤ (v k : ℝ))
    (hindep : ∀ k, ProbabilityTheory.IndepFun (blockHistory S k)
      (fun (ω : Ω) (i : Fin (n k + 1)) ↦ S k i.1 ω) P)
    (m : ℕ) (V u r : ℝ) (hu : 0 < u) (hr : 0 ≤ r) (hru : r ≤ u / 4)
    (hvlo : ∀ k ≤ m, u ^ 2 / 128 ≤ (v k : ℝ))
    (hvhi : ∀ k ≤ m, (v k : ℝ) ≤ u ^ 2 / 32)
    (hcount : ((m + 1 : ℕ) : ℝ) ≤ 1 + 128 * (V / u ^ 2)) :
    ENNReal.ofReal ((r / u) * Real.exp (-33280 * (1 + V / u ^ 2))) ≤
      P (blockPathEndpointEvent S n u r m) := by
  let q : ℝ≥0∞ := (1 / 2 : ℝ≥0∞) *
    ENNReal.ofReal ((1 / 8 : ℝ) * Real.exp (-256))
  let E : ℕ → Set Ω := fun k ↦ blockGoodEvent S n u (min k m)
  have hSmeas : ∀ k j, Measurable (S k j) := fun k j ↦
    (hS k).stronglyMeasurable j |>.measurable.le ((𝒢 k).le j)
  have hhist_meas : ∀ k, Measurable (blockHistory S k) :=
    fun k ↦ measurable_blockHistory S hSmeas k
  have hzero : E 0 = Set.univ := by
    simp only [E, Nat.zero_min]
    exact blockGoodEvent_zero S n u hu
  have hstep : ∀ k, q * P (E k) ≤ P (E (k + 1)) := by
    intro k
    by_cases hk : k < m
    · have hmink : min k m = k := Nat.min_eq_left (Nat.le_of_lt hk)
      have hminks : min (k + 1) m = k + 1 := Nat.min_eq_left hk
      rw [show E k = blockGoodEvent S n u k by simp [E, hmink],
        show E (k + 1) = blockGoodEvent S n u (k + 1) by simp [E, hminks]]
      have hcore : ∀ x ∈ historyGood n u k, |historyState n k x| ≤ u / 4 := by
        intro x hx
        rcases hx.2 with ⟨hlo, hhi⟩
        rw [abs_le]
        constructor <;> linarith
      have hraw := gaussian_martingale_adaptive_core_step_lower
        (hhist_meas k) (measurable_historyState n k) (hS k) (hL2 k)
        (n k) (v k) (prefixVar k) (hjoint k) (hcov k) (hYY k) (hYlaw k)
        (hq0 k) (hq1 k) u hu (hvlo k (Nat.le_of_lt hk))
        (hvhi k (Nat.le_of_lt hk)) (hterminal k)
        (measurableSet_historyGood n u k) hcore (hindep k)
      change q * P (blockHistory S k ⁻¹' historyGood n u k) ≤ _ at hraw
      exact hraw.trans (measure_mono (by
        rintro ω ⟨hprev, hnew⟩
        exact blockGoodEvent_step_of S n u k hprev hnew.1 hnew.2))
    · have hkm : m ≤ k := Nat.le_of_not_gt hk
      have hmin : min k m = m := Nat.min_eq_right hkm
      have hmins : min (k + 1) m = m := Nat.min_eq_right (hkm.trans (Nat.le_succ k))
      rw [show E k = blockGoodEvent S n u m by simp [E, hmin],
        show E (k + 1) = blockGoodEvent S n u m by simp [E, hmins]]
      exact (mul_le_mul' coreFactor_le_one le_rfl).trans (by simp)
  have hfinal : ((1 / 2 : ℝ≥0∞) *
      ENNReal.ofReal ((r / (2 * u)) * Real.exp (-256))) * P (E m) ≤
      P (blockPathEndpointEvent S n u r m) := by
    have hEm : E m = blockGoodEvent S n u m := by simp [E]
    rw [hEm]
    let transition : Set ((ℕ × ℕ → ℝ) × (Fin (n m + 1) → ℝ)) := {z |
      (∀ i, |historyState n m z.1 + z.2 i| ≤ 5 * u / 4) ∧
      historyState n m z.1 + z.2 ⟨n m, Nat.lt_succ_self (n m)⟩ ∈ Set.Icc (-r) r}
    have htransition : MeasurableSet transition := by
      have hp : MeasurableSet {z : (ℕ × ℕ → ℝ) × (Fin (n m + 1) → ℝ) |
          ∀ i, |historyState n m z.1 + z.2 i| ≤ 5 * u / 4} := by
        rw [show {z : (ℕ × ℕ → ℝ) × (Fin (n m + 1) → ℝ) |
            ∀ i, |historyState n m z.1 + z.2 i| ≤ 5 * u / 4} =
            ⋂ i, {z | |historyState n m z.1 + z.2 i| ≤ 5 * u / 4} by ext z; simp]
        exact MeasurableSet.iInter fun i ↦ measurableSet_le
          (((measurable_historyState n m).comp measurable_fst).add
            ((measurable_pi_apply i).comp measurable_snd) |>.abs) measurable_const
      exact hp.inter (measurableSet_Icc.preimage
        (((measurable_historyState n m).comp measurable_fst).add
          ((measurable_pi_apply (⟨n m, Nat.lt_succ_self (n m)⟩ : Fin (n m + 1))).comp
            measurable_snd)))
    apply indepFun_transition_lower (hindep m) (hhist_meas m)
      (measurable_pi_iff.mpr fun i ↦ hSmeas m i.1)
      (measurableSet_historyGood n u m) htransition
    intro x hx
    have hxcore : |historyState n m x| ≤ u / 4 := by
      rcases hx.2 with ⟨hlo, hhi⟩
      rw [abs_le]
      constructor <;> linarith
    have hblock := gaussian_martingale_path_endpoint_lower
      (hS m) (hL2 m) (n m) (v m) (prefixVar m) (hjoint m) (hcov m)
      (hYY m) (hYlaw m) (hq0 m) (hq1 m) u (-historyState n m x) r hu hr hru
      (by simpa only [abs_neg] using hxcore) (hvlo m le_rfl) (hvhi m le_rfl)
      (hterminal m)
    refine hblock.trans ?_
    rw [Measure.map_apply (measurable_pi_iff.mpr fun i ↦ hSmeas m i.1)
      (measurable_prodMk_left htransition)]
    apply measure_mono
    rintro ω ⟨hp, he⟩
    constructor
    · intro i
      calc
        |historyState n m x + S m i.1 ω| ≤
            |historyState n m x| + |S m i.1 ω| := abs_add_le _ _
        _ ≤ u / 4 + u := add_le_add hxcore (hp i)
        _ = 5 * u / 4 := by ring
    · rcases he with ⟨hlo, hhi⟩
      constructor <;> linarith
  exact gaussian_iterated_path_endpoint_lower E
    (blockPathEndpointEvent S n u r m) m V u r hu hr hcount hzero hstep hfinal


end Erdos527.ScalarGaussianPath

/- Concrete scalar closure source: Erdos527SmallVariance.lean -/

open scoped BigOperators ENNReal NNReal ProbabilityTheory Topology

namespace Erdos527.ScalarGaussianPath

open Asymptotics Filter MeasureTheory ProbabilityTheory

/-- A centered Gaussian whose variance is at most `u^2 / 32` has a uniform
linear amount of mass in `[-r/2,r/2]`. -/
theorem gaussianReal_centered_half_Icc_small_variance_lower
    (v : ℝ≥0) (u r : ℝ) (hu : 0 < u) (hr : 0 ≤ r) (hru : r ≤ u)
    (hvhi : (v : ℝ) ≤ u ^ 2 / 32) :
    ENNReal.ofReal ((r / (2 * u)) * Real.exp (-256)) ≤
      ProbabilityTheory.gaussianReal 0 v (Set.Icc (-r / 2) (r / 2)) := by
  by_cases hr0 : r = 0
  · simp [hr0]
  have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  by_cases hv0 : v = 0
  · rw [hv0, ProbabilityTheory.gaussianReal_zero_var]
    rw [MeasureTheory.Measure.dirac_apply' 0 measurableSet_Icc]
    simp only [Set.indicator, Set.mem_Icc]
    rw [if_pos]
    · simp only [Pi.one_apply]
      apply ENNReal.ofReal_le_one.mpr
      have hratio : r / (2 * u) ≤ 1 := by
        apply (div_le_iff₀ (by positivity : 0 < 2 * u)).2
        linarith
      calc
        r / (2 * u) * Real.exp (-256) ≤ 1 * 1 := by
          gcongr
          exact Real.exp_le_one_iff.mpr (by norm_num)
        _ = 1 := one_mul 1
    · constructor <;> linarith
  have hvpos : 0 < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv0)
  let h : ℝ := r / 2
  have hh : 0 < h := by dsimp [h]; positivity
  by_cases hvsmall : (v : ℝ) ≤ h ^ 2 / 2
  · let μ : Measure ℝ := ProbabilityTheory.gaussianReal 0 v
    let bad : Set ℝ := {x | h ≤ |x|}
    have hbad_meas : MeasurableSet bad :=
      measurableSet_le measurable_const measurable_id.abs
    have hcheb : μ bad ≤ ENNReal.ofReal ((v : ℝ) / h ^ 2) := by
      have h0 : ∫ x, x ∂μ = 0 := by
        simpa [μ] using
          (ProbabilityTheory.integral_id_gaussianReal (v := v) ( μ := (0 : ℝ)))
      have hc := ProbabilityTheory.meas_ge_le_variance_div_sq
        (ProbabilityTheory.memLp_id_gaussianReal (v := v) ( μ := (0 : ℝ)) 2) hh
      rw [ProbabilityTheory.variance_id_gaussianReal] at hc
      simpa only [μ, bad, Function.id_def, h0, sub_zero,
        ProbabilityTheory.variance_fun_id_gaussianReal] using hc
    have hbad_real : μ.real bad ≤ 1 / 2 := by
      have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcheb
      rw [ENNReal.toReal_ofReal (div_nonneg (NNReal.coe_nonneg v) (sq_nonneg h))] at ht
      exact ht.trans (by
        apply (div_le_iff₀ (sq_pos_of_pos hh)).2
        nlinarith)
    have hhalf : (1 / 2 : ℝ≥0∞) ≤ μ (Set.Icc (-r / 2) (r / 2)) := by
      apply half_le_measure_of_compl_subset hbad_meas hbad_real
      intro x hx
      change ¬ h ≤ |x| at hx
      change -r / 2 ≤ x ∧ x ≤ r / 2
      rw [show h = r / 2 by rfl] at hx
      simpa only [neg_div] using abs_le.mp (le_of_lt (lt_of_not_ge hx))
    refine le_trans ?_ hhalf
    have hreal : r / (2 * u) * Real.exp (-256) ≤ 1 / 2 := by
      have hratio : r / (2 * u) ≤ 1 / 2 := by
        apply (div_le_iff₀ (by positivity : 0 < 2 * u)).2
        linarith
      calc
        r / (2 * u) * Real.exp (-256) ≤ (1 / 2) * 1 := by
          gcongr
          exact Real.exp_le_one_iff.mpr (by norm_num)
        _ = 1 / 2 := mul_one _
    have hof := ENNReal.ofReal_le_ofReal hreal
    have hhalf_ofReal : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by
      simpa using ENNReal.ofReal_div_of_pos (x := (1 : ℝ)) (y := 2) (by norm_num)
    simpa only [hhalf_ofReal] using hof
  · have hvlo : h ^ 2 / 2 < (v : ℝ) := lt_of_not_ge hvsmall
    have hdenom_pos : 0 < Real.sqrt (2 * Real.pi * (v : ℝ)) := by positivity
    have hdenom_sq : (Real.sqrt (2 * Real.pi * (v : ℝ))) ^ 2 =
        2 * Real.pi * (v : ℝ) := by
      rw [Real.sq_sqrt]
      positivity
    have hdenom_le : Real.sqrt (2 * Real.pi * (v : ℝ)) ≤ u := by
      have hmul : 2 * Real.pi * (v : ℝ) ≤ u ^ 2 := by
        nlinarith [Real.pi_lt_four, Real.pi_pos, NNReal.coe_nonneg v,
          sq_nonneg u]
      nlinarith [Real.sqrt_nonneg (2 * Real.pi * (v : ℝ)), sq_pos_of_pos hu]
    have hquot : h ^ 2 / (2 * (v : ℝ)) ≤ 1 := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * (v : ℝ))).2
      nlinarith
    have hpdf : Real.exp (-1) / u ≤
        ProbabilityTheory.gaussianPDFReal 0 v h := by
      rw [ProbabilityTheory.gaussianPDFReal]
      simp only [NNReal.coe_eq_zero, hv0, if_false, sub_zero]
      have hpref : 1 / u ≤ 1 / Real.sqrt (2 * Real.pi * (v : ℝ)) :=
        one_div_le_one_div_of_le hdenom_pos hdenom_le
      have hexp : Real.exp (-1) ≤
          Real.exp (-(h ^ 2 / (2 * (v : ℝ)))) :=
        Real.exp_le_exp.mpr (by linarith)
      calc
        Real.exp (-1) / u = (1 / u) * Real.exp (-1) := by ring
        _ ≤ (1 / Real.sqrt (2 * Real.pi * (v : ℝ))) * Real.exp (-1) := by
          gcongr
        _ ≤ (1 / Real.sqrt (2 * Real.pi * (v : ℝ))) *
            Real.exp (-(h ^ 2 / (2 * (v : ℝ)))) := by gcongr
        _ = _ := by ring_nf
    have hmass : ENNReal.ofReal
          ((2 * h) * ProbabilityTheory.gaussianPDFReal 0 v h) ≤
        ProbabilityTheory.gaussianReal 0 v (Set.Icc (-r / 2) (r / 2)) := by
      simpa only [h, abs_zero, zero_add, zero_sub, neg_div] using
        (gaussianReal_Icc_lower v hv0 0 h hh.le)
    refine le_trans ?_ hmass
    apply ENNReal.ofReal_le_ofReal
    have hexp256 : Real.exp (-256) ≤ Real.exp (-1) :=
      Real.exp_le_exp.mpr (by norm_num)
    calc
      r / (2 * u) * Real.exp (-256) ≤
          r / (2 * u) * Real.exp (-1) := by gcongr
      _ = (2 * h) * (Real.exp (-1) / (2 * u)) := by
        dsimp [h]
        ring
      _ ≤ (2 * h) * ProbabilityTheory.gaussianPDFReal 0 v h := by
        have hweak : Real.exp (-1) / (2 * u) ≤
            ProbabilityTheory.gaussianPDFReal 0 v h := by
          calc
            Real.exp (-1) / (2 * u) ≤ Real.exp (-1) / u := by
              have he : 0 ≤ Real.exp (-1) := Real.exp_nonneg _
              have : 0 ≤ 1 / u := le_of_lt (one_div_pos.mpr hu)
              calc
                Real.exp (-1) / (2 * u) = (1 / 2) * (Real.exp (-1) / u) := by
                  field_simp
                  <;> ring
                _ ≤ 1 * (Real.exp (-1) / u) := by gcongr <;> norm_num
                _ = Real.exp (-1) / u := one_mul _
            _ ≤ _ := hpdf
        exact mul_le_mul_of_nonneg_left hweak (by positivity)

/-- A centered finite Gaussian martingale with total variance at most `u²/32`
stays in the radius-`u` tube and ends in `[-r,r]` with probability bounded
below linearly in `r/u`, without any positive lower bound on the variance. -/
theorem gaussian_martingale_small_variance_path_endpoint_lower
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {G : MeasureTheory.Filtration ℕ ‹MeasurableSpace Ω›}
    {S : ℕ → Ω → ℝ} [IsProbabilityMeasure P]
    (hS : MeasureTheory.Martingale S G P)
    (hL2 : ∀ j, MemLp (S j) 2 P)
    (n : ℕ) (v : ℝ≥0) (prefixVar : Fin (n + 1) → ℝ)
    (hjoint : ProbabilityTheory.HasGaussianLaw
      (fun ω ↦ (fun i : Fin (n + 1) ↦ S i.1 ω, S n ω)) P)
    (hcov : ∀ i, ProbabilityTheory.covariance (fun ω ↦ S i.1 ω) (S n) P =
      prefixVar i)
    (hYY : ProbabilityTheory.covariance (S n) (S n) P = (v : ℝ))
    (hYlaw : ProbabilityTheory.HasLaw (S n)
      (ProbabilityTheory.gaussianReal 0 v) P)
    (hq0 : ∀ i, 0 ≤ prefixVar i / (v : ℝ))
    (hq1 : ∀ i, prefixVar i / (v : ℝ) ≤ 1)
    (u r : ℝ) (hu : 0 < u) (hr : 0 ≤ r) (hru : r ≤ u)
    (hvhi : (v : ℝ) ≤ u ^ 2 / 32)
    (hterminal : ∫ ω, (S n ω) ^ 2 ∂P ≤ (v : ℝ)) :
    ENNReal.ofReal ((r / u) * Real.exp (-260)) ≤
      P {ω | (∀ i : Fin (n + 1), |S i.1 ω| ≤ u) ∧ |S n ω| ≤ r} := by
  have hlhs_half : ENNReal.ofReal ((r / u) * Real.exp (-260)) ≤
      (1 / 2 : ℝ≥0∞) := by
    have heone : (2 : ℝ) ≤ Real.exp 1 := by
      nlinarith [Real.add_one_le_exp 1]
    have hneg : Real.exp (-260) ≤ (1 / 2 : ℝ) := by
      have h260 : Real.exp 1 ≤ Real.exp 260 :=
        Real.exp_le_exp.mpr (by norm_num)
      rw [Real.exp_neg]
      simpa only [one_div] using
        (one_div_le_one_div_of_le (by positivity) (heone.trans h260))
    have hreal : (r / u) * Real.exp (-260) ≤ 1 / 2 := by
      have hratio : r / u ≤ 1 := (div_le_one hu).2 hru
      calc
        (r / u) * Real.exp (-260) ≤ 1 * (1 / 2) := by
          gcongr
        _ = 1 / 2 := one_mul _
    have hof := ENNReal.ofReal_le_ofReal hreal
    have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by
      simpa using ENNReal.ofReal_div_of_pos (x := (1 : ℝ)) (y := 2) (by norm_num)
    simpa only [hhalf] using hof
  by_cases hv0 : v = 0
  · have hpath : (1 / 2 : ℝ≥0∞) ≤
        P {ω | ∀ i : Fin (n + 1), |S i.1 ω| ≤ u / 2} := by
      simpa only [zero_div, zero_mul, sub_zero] using
        (martingale_bridge_tube_mass_ge_half hS hL2 n
          (fun _ : Fin (n + 1) ↦ 0) u 0 hu (by norm_num)
          (by nlinarith [sq_nonneg u])
          (by simpa only [hv0, NNReal.coe_zero] using hterminal)
          (fun _ ↦ le_rfl) (fun _ ↦ by norm_num))
    have hYzero : S n =ᵐ[P] (fun _ ↦ 0) := by
      have hy := hYlaw
      rw [hv0, ProbabilityTheory.gaussianReal_zero_var] at hy
      exact hy.ae_eq_of_dirac
    refine hlhs_half.trans (hpath.trans ?_)
    apply measure_mono_ae
    filter_upwards [hYzero] with ω hY hpathω
    constructor
    · intro i
      exact (hpathω i).trans (by linarith)
    · simp only [hY, abs_zero]
      exact hr
  · let q : Fin (n + 1) → ℝ := fun i ↦ prefixVar i / (v : ℝ)
    let B : Ω → Fin (n + 1) → ℝ :=
      fun ω i ↦ S i.1 ω - q i * S n ω
    let tube : Set (Fin (n + 1) → ℝ) := {x | ∀ i, |x i| ≤ u / 2}
    have hvne : (v : ℝ) ≠ 0 := by exact_mod_cast hv0
    have hBindep : ProbabilityTheory.IndepFun B (S n) P := by
      exact gaussian_bridge_process_indep_endpoint prefixVar (v : ℝ) hvne
        hjoint hcov hYY
    have htube_meas : MeasurableSet tube := measurableSet_pi_abs_le (u / 2)
    have htube_mass : (1 / 2 : ℝ≥0∞) ≤ P (B ⁻¹' tube) := by
      simpa only [B, tube, Set.preimage_setOf_eq] using
        martingale_bridge_tube_mass_ge_half hS hL2 n q u (v : ℝ) hu
          (NNReal.coe_nonneg v) hvhi hterminal
          (by simpa only [q] using hq0) (by simpa only [q] using hq1)
    have hendpoint : ENNReal.ofReal
          ((r / (2 * u)) * Real.exp (-256)) ≤
        P ((S n) ⁻¹' Set.Icc (-r / 2) (r / 2)) := by
      calc
        ENNReal.ofReal ((r / (2 * u)) * Real.exp (-256)) ≤
            ProbabilityTheory.gaussianReal 0 v (Set.Icc (-r / 2) (r / 2)) :=
          gaussianReal_centered_half_Icc_small_variance_lower
            v u r hu hr hru hvhi
        _ = P ((S n) ⁻¹' Set.Icc (-r / 2) (r / 2)) := by
          rw [← hYlaw.map_eq,
            Measure.map_apply_of_aemeasurable hYlaw.aemeasurable measurableSet_Icc]
    have hinter : (1 / 2 : ℝ≥0∞) *
          ENNReal.ofReal ((r / (2 * u)) * Real.exp (-256)) ≤
        P (B ⁻¹' tube ∩ (S n) ⁻¹' Set.Icc (-r / 2) (r / 2)) := by
      exact indepFun_measure_inter_preimage_lower hBindep htube_meas
        measurableSet_Icc htube_mass hendpoint
    refine (gaussian_final_macroblock_constant_lower u r hu hr).trans
      (hinter.trans (measure_mono ?_))
    rintro ω ⟨hBtube, hYinterval⟩
    have hYabsHalf : |S n ω| ≤ r / 2 := by
      rw [abs_le]
      change S n ω ∈ Set.Icc (-r / 2) (r / 2) at hYinterval
      simpa only [Set.mem_Icc, neg_div] using hYinterval
    have hYabs : |S n ω| ≤ r := hYabsHalf.trans (by linarith)
    refine ⟨?_, hYabs⟩
    intro i
    have hBabs : |B ω i| ≤ u / 2 := hBtube i
    calc
      |S i.1 ω| = |B ω i + q i * S n ω| := by
        congr 1
        simp only [B]
        ring
      _ ≤ |B ω i| + |q i * S n ω| := abs_add_le _ _
      _ = |B ω i| + q i * |S n ω| := by
        rw [abs_mul, abs_of_nonneg (hq0 i)]
      _ ≤ u / 2 + 1 * (r / 2) := by
        apply add_le_add hBabs
        exact mul_le_mul (hq1 i) hYabsHalf (abs_nonneg _) (by norm_num)
      _ ≤ u := by linarith


end Erdos527.ScalarGaussianPath

/- Concrete scalar closure source: CanonicalGaussian.lean -/

open scoped BigOperators ENNReal NNReal ProbabilityTheory Topology
open MeasureTheory ProbabilityTheory Finset

namespace Erdos527.ScalarGaussianPath.Canonical

noncomputable def sqNN (c : ℝ) : ℝ≥0 := NNReal.mk (c ^ 2) (sq_nonneg c)

theorem coord_hasLaw {n : ℕ} (i : Fin n) :
    HasLaw (fun x : EuclideanSpace ℝ (Fin n) ↦ x i) (gaussianReal 0 1)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  have h := (measurePreserving_eval_multivariateGaussian
    (μ := (0 : EuclideanSpace ℝ (Fin n)))
    (S := (1 : Matrix (Fin n) (Fin n) ℝ)) Matrix.PosSemidef.one
    (i := i)).hasLaw
  rw [multivariateGaussian_zero_one] at h
  simpa using h

theorem coord_covariance {n : ℕ} (i j : Fin n) :
    cov[(fun x : EuclideanSpace ℝ (Fin n) ↦ x i),
      (fun x : EuclideanSpace ℝ (Fin n) ↦ x j);
      stdGaussian (EuclideanSpace ℝ (Fin n))] = if i = j then 1 else 0 := by
  have hi : (fun x : EuclideanSpace ℝ (Fin n) ↦ x i) =
      (fun x ↦ inner ℝ ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis i) x) := by
    funext x
    exact (EuclideanSpace.basisFun_inner (Fin n) ℝ x i).symm
  have hj : (fun x : EuclideanSpace ℝ (Fin n) ↦ x j) =
      (fun x ↦ inner ℝ ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis j) x) := by
    funext x
    exact (EuclideanSpace.basisFun_inner (Fin n) ℝ x j).symm
  rw [hi, hj, ← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id
      ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis i)
      ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis j),
    covarianceBilin_stdGaussian]
  rw [innerSL_apply_apply]
  change inner ℝ ((EuclideanSpace.basisFun (Fin n) ℝ) i)
      ((EuclideanSpace.basisFun (Fin n) ℝ) j) = _
  rw [EuclideanSpace.basisFun_inner]
  simp

theorem coord_iIndep {n : ℕ} :
    iIndepFun (fun i : Fin n ↦ fun x : EuclideanSpace ℝ (Fin n) ↦ x i)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun _ ↦ by fun_prop)]
  calc
    (stdGaussian (EuclideanSpace ℝ (Fin n))).map
        (fun x ↦ fun i ↦ x i) =
        (Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1)).map
          ((fun x : EuclideanSpace ℝ (Fin n) ↦ fun i ↦ x i) ∘
            WithLp.toLp 2) := by
              rw [← map_pi_eq_stdGaussian, Measure.map_map]
              all_goals fun_prop
    _ = Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1) := by
      change (Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1)).map id = _
      rw [Measure.map_id]
    _ = Measure.pi (fun i ↦
        (stdGaussian (EuclideanSpace ℝ (Fin n))).map (fun x ↦ x i)) := by
      congr 1
      funext i
      exact (coord_hasLaw i).map_eq.symm

theorem scaledCoord_hasLaw {n : ℕ} (c : Fin n → ℝ) (i : Fin n) :
    HasLaw (fun x : EuclideanSpace ℝ (Fin n) ↦ c i * x i)
      (gaussianReal 0 (sqNN (c i)))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  have h := gaussianReal_const_mul (coord_hasLaw i) (c i)
  change HasLaw (fun x : EuclideanSpace ℝ (Fin n) ↦ c i * x i)
      (gaussianReal 0 (NNReal.mk (c i ^ 2) (sq_nonneg (c i)))) _
  simpa using h

theorem scaledCoord_iIndep {n : ℕ} (c : Fin n → ℝ) :
    iIndepFun (fun i : Fin n ↦ fun x : EuclideanSpace ℝ (Fin n) ↦ c i * x i)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  have h := coord_iIndep (n := n)
  exact h.comp (fun i y ↦ c i * y) (fun _ ↦ by fun_prop)

/-- The `k`th weighted coordinate, extended by zero past a finite vector. -/
noncomputable def finiteWeightedCoord {n : ℕ} (c : Fin n → ℝ) (k : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  if hk : k < n then c ⟨k, hk⟩ * x ⟨k, hk⟩ else 0

/-- Continuous-linear form of `finiteWeightedCoord`. -/
noncomputable def finiteWeightedCoordCLM {n : ℕ} (c : Fin n → ℝ) (k : ℕ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  if hk : k < n then
    c ⟨k, hk⟩ • (innerSL ℝ) ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis ⟨k, hk⟩)
  else 0

@[simp] theorem finiteWeightedCoordCLM_apply {n : ℕ} (c : Fin n → ℝ) (k : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    finiteWeightedCoordCLM c k x = finiteWeightedCoord c k x := by
  by_cases hk : k < n
  · rw [finiteWeightedCoordCLM, dif_pos hk, finiteWeightedCoord, dif_pos hk]
    change c ⟨k, hk⟩ *
      inner ℝ ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis ⟨k, hk⟩) x = _
    rw [show ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis ⟨k, hk⟩) =
        (EuclideanSpace.basisFun (Fin n) ℝ) ⟨k, hk⟩ by rfl,
      EuclideanSpace.basisFun_inner]
  · simp [finiteWeightedCoordCLM, finiteWeightedCoord, hk]

theorem finiteWeightedCoord_of_lt {n : ℕ} (c : Fin n → ℝ) (k : ℕ) (hk : k < n) :
    finiteWeightedCoord c k = fun x ↦ c ⟨k, hk⟩ * x ⟨k, hk⟩ := by
  funext x
  rw [finiteWeightedCoord, dif_pos hk]

theorem finiteWeightedCoord_of_not_lt {n : ℕ} (c : Fin n → ℝ) (k : ℕ)
    (hk : ¬k < n) : finiteWeightedCoord c k = 0 := by
  funext x
  rw [finiteWeightedCoord, dif_neg hk]
  rfl

theorem finiteWeightedCoord_stronglyMeasurable {n : ℕ} (c : Fin n → ℝ) (k : ℕ) :
    StronglyMeasurable (finiteWeightedCoord c k) := by
  have heq : finiteWeightedCoord c k = finiteWeightedCoordCLM c k := by
    funext x
    exact (finiteWeightedCoordCLM_apply c k x).symm
  rw [heq]
  exact (finiteWeightedCoordCLM c k).continuous.stronglyMeasurable

/-- Every finite restriction of the zero-extended coordinate family is jointly
Gaussian, in the product topology used by `HasGaussianLaw`. -/
theorem finiteWeightedCoord_jointGaussian_restrict {n : ℕ} (c : Fin n → ℝ)
    (s : Finset ℕ) :
    HasGaussianLaw (fun x : EuclideanSpace ℝ (Fin n) ↦
      fun k : s ↦ finiteWeightedCoord c k.1 x)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ] (k : s) → ℝ :=
    ContinuousLinearMap.pi fun k : s ↦ finiteWeightedCoordCLM c k.1
  have hid : HasGaussianLaw (id : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n)) (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    IsGaussian.hasGaussianLaw_id
  have hm := HasGaussianLaw.map_of_measurable L hid (by fun_prop)
  convert hm using 1
  funext x k
  exact (finiteWeightedCoordCLM_apply c k.1 x).symm

theorem finiteWeightedCoord_covariance {n : ℕ} (c : Fin n → ℝ) (k l : ℕ) :
    cov[finiteWeightedCoord c k, finiteWeightedCoord c l;
      stdGaussian (EuclideanSpace ℝ (Fin n))] =
      if h : k = l ∧ k < n then (c ⟨k, h.2⟩) ^ 2 else 0 := by
  by_cases hk : k < n
  · by_cases hl : l < n
    · rw [finiteWeightedCoord_of_lt c k hk, finiteWeightedCoord_of_lt c l hl,
        covariance_const_mul_left, covariance_const_mul_right, coord_covariance]
      by_cases hkl : k = l
      · subst l
        simp only [if_pos, true_and, covariance_const_mul_left,
          covariance_const_mul_right]
        have heq : (⟨k, hk⟩ : Fin n) = ⟨k, hl⟩ := rfl
        rw [heq]
        rw [dif_pos hk]
        ring
      · have hfin : (⟨k, hk⟩ : Fin n) ≠ ⟨l, hl⟩ := by
          intro h
          exact hkl (congrArg Fin.val h)
        rw [if_neg hfin]
        simp [hkl]
    · have hkl : k ≠ l := by
        intro h
        subst l
        exact hl hk
      rw [finiteWeightedCoord_of_lt c k hk, finiteWeightedCoord_of_not_lt c l hl]
      simp [hkl]
  · rw [finiteWeightedCoord_of_not_lt c k hk]
    simp [hk]

/-- The zero-extended finite weighted coordinates remain mutually independent.
The proof checks every finite restriction, so repeated zero coordinates cause
no issue. -/
theorem finiteWeightedCoord_iIndep {n : ℕ} (c : Fin n → ℝ) :
    iIndepFun (finiteWeightedCoord c)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  rw [iIndepFun_iff_finset]
  intro s
  apply (finiteWeightedCoord_jointGaussian_restrict c s).iIndepFun_of_covariance_eq_zero
  intro i j hij
  rw [finiteWeightedCoord_covariance]
  split_ifs with h
  · exact (hij (Subtype.ext h.1)).elim
  · rfl

theorem finiteWeightedCoord_memLp_two {n : ℕ} (c : Fin n → ℝ) (k : ℕ) :
    MemLp (finiteWeightedCoord c k) 2
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  by_cases hk : k < n
  · have h := (scaledCoord_hasLaw c ⟨k, hk⟩).hasGaussianLaw.memLp_two
    rw [finiteWeightedCoord_of_lt c k hk]
    exact h
  · rw [finiteWeightedCoord_of_not_lt c k hk]
    exact MemLp.zero

theorem finiteWeightedCoord_integral {n : ℕ} (c : Fin n → ℝ) (k : ℕ) :
    ∫ x, finiteWeightedCoord c k x ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) = 0 := by
  by_cases hk : k < n
  · rw [finiteWeightedCoord_of_lt c k hk]
    rw [integral_const_mul]
    have h := (coord_hasLaw (⟨k, hk⟩ : Fin n)).integral_eq
    rw [h, integral_id_gaussianReal, mul_zero]
  · rw [finiteWeightedCoord_of_not_lt c k hk]
    simp

/-- The canonical partial-sum process of a finite weighted standard Gaussian
vector, frozen after the last coordinate. -/
noncomputable def finiteGaussianPartialSum {n : ℕ} (c : Fin n → ℝ) :
    ℕ → EuclideanSpace ℝ (Fin n) → ℝ :=
  partialSum (finiteWeightedCoord c)

theorem finiteGaussianPartialSum_martingale {n : ℕ} (c : Fin n → ℝ) :
    MeasureTheory.Martingale (finiteGaussianPartialSum c)
      (MeasureTheory.Filtration.natural (finiteWeightedCoord c)
        (finiteWeightedCoord_stronglyMeasurable c))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  exact iIndepFun_martingale_partialSum
    (finiteWeightedCoord_stronglyMeasurable c)
    (finiteWeightedCoord_iIndep c)
    (fun k ↦ (finiteWeightedCoord_memLp_two c k).integrable one_le_two)
    (finiteWeightedCoord_integral c)

theorem finiteGaussianPartialSum_memLp_two {n : ℕ} (c : Fin n → ℝ) (k : ℕ) :
    MemLp (finiteGaussianPartialSum c k) 2
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  change MemLp (fun x ↦ ∑ i ∈ Finset.range (k + 1), finiteWeightedCoord c i x) 2 _
  exact memLp_finsetSum _ (fun i _ ↦ finiteWeightedCoord_memLp_two c i)

/-- Continuous-linear form of a finite weighted prefix sum. -/
noncomputable def finiteGaussianPrefixCLM {n : ℕ} (c : Fin n → ℝ) (k : ℕ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  ∑ i ∈ Finset.range (k + 1), finiteWeightedCoordCLM c i

@[simp] theorem finiteGaussianPrefixCLM_apply {n : ℕ} (c : Fin n → ℝ) (k : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    finiteGaussianPrefixCLM c k x = finiteGaussianPartialSum c k x := by
  simp only [finiteGaussianPrefixCLM, map_sum, ContinuousLinearMap.sum_apply,
    finiteWeightedCoordCLM_apply, finiteGaussianPartialSum, partialSum]

/-- The complete prefix path and endpoint are a jointly Gaussian random
variable in the product topology appearing in the scalar bridge theorem. -/
theorem finiteGaussian_pathEndpoint_joint (N : ℕ) (c : Fin (N + 1) → ℝ) :
    HasGaussianLaw
      (fun x : EuclideanSpace ℝ (Fin (N + 1)) ↦
        (fun i : Fin (N + 1) ↦ finiteGaussianPartialSum c i.1 x,
          finiteGaussianPartialSum c N x))
      (stdGaussian (EuclideanSpace ℝ (Fin (N + 1))) ) := by
  let L : EuclideanSpace ℝ (Fin (N + 1)) →L[ℝ]
      ((Fin (N + 1) → ℝ) × ℝ) :=
    (ContinuousLinearMap.pi fun i : Fin (N + 1) ↦
      finiteGaussianPrefixCLM c i.1).prod (finiteGaussianPrefixCLM c N)
  have hid : HasGaussianLaw (id : EuclideanSpace ℝ (Fin (N + 1)) →
      EuclideanSpace ℝ (Fin (N + 1)))
      (stdGaussian (EuclideanSpace ℝ (Fin (N + 1)))) :=
    IsGaussian.hasGaussianLaw_id
  have hm := HasGaussianLaw.map_of_measurable L hid (by fun_prop)
  convert hm using 1
  funext x
  apply Prod.ext
  · funext i
    exact (finiteGaussianPrefixCLM_apply c i.1 x).symm
  · exact (finiteGaussianPrefixCLM_apply c N x).symm

/-- Variance of one zero-extended weighted coordinate. -/
noncomputable def finiteWeightedVariance {n : ℕ} (c : Fin n → ℝ) (k : ℕ) : ℝ :=
  if hk : k < n then (c ⟨k, hk⟩) ^ 2 else 0

lemma finiteWeightedVariance_nonneg {n : ℕ} (c : Fin n → ℝ) (k : ℕ) :
    0 ≤ finiteWeightedVariance c k := by
  by_cases hk : k < n
  · rw [finiteWeightedVariance, dif_pos hk]
    exact sq_nonneg _
  · rw [finiteWeightedVariance, dif_neg hk]

lemma finiteWeightedCoord_covariance_eq_ite {n : ℕ} (c : Fin n → ℝ) (k l : ℕ) :
    cov[finiteWeightedCoord c k, finiteWeightedCoord c l;
      stdGaussian (EuclideanSpace ℝ (Fin n))] =
      if k = l then finiteWeightedVariance c k else 0 := by
  rw [finiteWeightedCoord_covariance]
  by_cases hkl : k = l
  · subst l
    simp only [if_pos, true_and]
    rfl
  · simp [hkl]

/-- Squared energy accumulated through a prefix. -/
noncomputable def finiteGaussianPrefixEnergy (N : ℕ) (c : Fin (N + 1) → ℝ)
    (i : Fin (N + 1)) : ℝ :=
  ∑ j ∈ Finset.range (i.1 + 1), finiteWeightedVariance c j

/-- Total squared energy of the finite weighted block. -/
noncomputable def finiteGaussianTotalEnergy (N : ℕ) (c : Fin (N + 1) → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1), finiteWeightedVariance c j

lemma finiteGaussianPrefixEnergy_nonneg (N : ℕ) (c : Fin (N + 1) → ℝ)
    (i : Fin (N + 1)) : 0 ≤ finiteGaussianPrefixEnergy N c i := by
  exact Finset.sum_nonneg fun j _ ↦ finiteWeightedVariance_nonneg c j

lemma finiteGaussianPrefixEnergy_le_total (N : ℕ) (c : Fin (N + 1) → ℝ)
    (i : Fin (N + 1)) :
    finiteGaussianPrefixEnergy N c i ≤ finiteGaussianTotalEnergy N c := by
  unfold finiteGaussianPrefixEnergy finiteGaussianTotalEnergy
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (Nat.succ_le_succ (Nat.le_of_lt_succ i.2))
  · intro j hj hnot
    exact finiteWeightedVariance_nonneg c j

theorem finiteGaussian_prefix_covariance_total (N : ℕ) (c : Fin (N + 1) → ℝ)
    (i : Fin (N + 1)) :
    cov[finiteGaussianPartialSum c i.1, finiteGaussianPartialSum c N;
      stdGaussian (EuclideanSpace ℝ (Fin (N + 1)))] =
      finiteGaussianPrefixEnergy N c i := by
  unfold finiteGaussianPartialSum partialSum finiteGaussianPrefixEnergy
  rw [covariance_fun_sum_fun_sum'
    (fun k _ ↦ finiteWeightedCoord_memLp_two c k)
    (fun k _ ↦ finiteWeightedCoord_memLp_two c k)]
  apply Finset.sum_congr rfl
  intro k hk
  have hkN : k ∈ Finset.range (N + 1) := by
    have hki : k < i.1 + 1 := Finset.mem_range.mp hk
    exact Finset.mem_range.mpr (lt_of_lt_of_le hki (Nat.succ_le_succ (Nat.le_of_lt_succ i.2)))
  rw [Finset.sum_eq_single k]
  · rw [finiteWeightedCoord_covariance_eq_ite, if_pos rfl]
  · intro l hl hne
    rw [finiteWeightedCoord_covariance_eq_ite, if_neg (Ne.symm hne)]
  · exact fun h ↦ (h hkN).elim

theorem finiteGaussian_total_covariance (N : ℕ) (c : Fin (N + 1) → ℝ) :
    cov[finiteGaussianPartialSum c N, finiteGaussianPartialSum c N;
      stdGaussian (EuclideanSpace ℝ (Fin (N + 1)))] =
      finiteGaussianTotalEnergy N c := by
  have h := finiteGaussian_prefix_covariance_total N c
    (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))
  simpa [finiteGaussianPrefixEnergy, finiteGaussianTotalEnergy] using h

theorem finiteGaussianPartialSum_integral {n : ℕ} (c : Fin n → ℝ) (k : ℕ) :
    ∫ x, finiteGaussianPartialSum c k x
        ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) = 0 := by
  change ∫ x, ∑ i ∈ Finset.range (k + 1), finiteWeightedCoord c i x
      ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) = 0
  rw [integral_finsetSum _ (fun i _ ↦
      (finiteWeightedCoord_memLp_two c i).integrable one_le_two)]
  exact Finset.sum_eq_zero fun i _ ↦ finiteWeightedCoord_integral c i

/-- The total block energy as a nonnegative-real variance parameter. -/
noncomputable def finiteGaussianTotalVariance (N : ℕ) (c : Fin (N + 1) → ℝ) : ℝ≥0 :=
  ⟨finiteGaussianTotalEnergy N c, by
    unfold finiteGaussianTotalEnergy
    exact Finset.sum_nonneg fun j _ ↦ finiteWeightedVariance_nonneg c j⟩

@[simp] theorem coe_finiteGaussianTotalVariance (N : ℕ) (c : Fin (N + 1) → ℝ) :
    (finiteGaussianTotalVariance N c : ℝ) = finiteGaussianTotalEnergy N c := rfl

theorem finiteGaussian_endpoint_hasLaw (N : ℕ) (c : Fin (N + 1) → ℝ) :
    HasLaw (finiteGaussianPartialSum c N)
      (gaussianReal 0 (finiteGaussianTotalVariance N c))
      (stdGaussian (EuclideanSpace ℝ (Fin (N + 1)))) := by
  have hG := (finiteGaussian_pathEndpoint_joint N c).snd
  refine ⟨hG.aemeasurable, ?_⟩
  rw [hG.map_eq_gaussianReal, finiteGaussianPartialSum_integral]
  congr 2
  apply NNReal.eq
  rw [Real.coe_toNNReal _ (variance_nonneg _ _),
    ← covariance_self hG.aemeasurable, finiteGaussian_total_covariance]
  rfl

theorem finiteGaussian_endpoint_sq_integral (N : ℕ) (c : Fin (N + 1) → ℝ) :
    ∫ x, (finiteGaussianPartialSum c N x) ^ 2
        ∂(stdGaussian (EuclideanSpace ℝ (Fin (N + 1))) ) =
      finiteGaussianTotalEnergy N c := by
  have hG := (finiteGaussian_pathEndpoint_joint N c).snd
  have hv := finiteGaussian_total_covariance N c
  rw [covariance_self hG.aemeasurable,
    variance_eq_integral hG.aemeasurable, finiteGaussianPartialSum_integral] at hv
  simpa using hv

/-- All canonical finite-vector inputs discharged for the scalar Gaussian
path/endpoint lower bound.  This is the directly reusable one-macroblock
interface: the caller supplies only the deterministic energy bounds and the
target interval parameters. -/
theorem canonical_finiteGaussian_path_endpoint_lower
    (N : ℕ) (c : Fin (N + 1) → ℝ) (u center h : ℝ)
    (hu : 0 < u) (hh : 0 ≤ h) (hhu : h ≤ u / 4)
    (hcenter : |center| ≤ u / 4)
    (hvlo : u ^ 2 / 128 ≤ finiteGaussianTotalEnergy N c)
    (hvhi : finiteGaussianTotalEnergy N c ≤ u ^ 2 / 32) :
    (1 / 2 : ℝ≥0∞) *
        ENNReal.ofReal ((h / (2 * u)) * Real.exp (-256)) ≤
      (stdGaussian (EuclideanSpace ℝ (Fin (N + 1)))) {x |
        (∀ i : Fin (N + 1), |finiteGaussianPartialSum c i.1 x| ≤ u) ∧
          finiteGaussianPartialSum c N x ∈ Set.Icc (center - h) (center + h)} := by
  have hVpos : 0 < finiteGaussianTotalEnergy N c := by
    have hupos : 0 < u ^ 2 / 128 := by positivity
    exact hupos.trans_le hvlo
  apply gaussian_martingale_path_endpoint_lower
    (finiteGaussianPartialSum_martingale c)
    (finiteGaussianPartialSum_memLp_two c)
    N (finiteGaussianTotalVariance N c) (finiteGaussianPrefixEnergy N c)
    (finiteGaussian_pathEndpoint_joint N c)
    (finiteGaussian_prefix_covariance_total N c)
    (by simpa using finiteGaussian_total_covariance N c)
    (finiteGaussian_endpoint_hasLaw N c)
  · intro i
    exact div_nonneg (finiteGaussianPrefixEnergy_nonneg N c i) hVpos.le
  · intro i
    apply (div_le_one hVpos).2
    exact finiteGaussianPrefixEnergy_le_total N c i
  · exact hu
  · exact hh
  · exact hhu
  · exact hcenter
  · simpa using hvlo
  · simpa using hvhi
  · rw [finiteGaussian_endpoint_sq_integral]
    exact le_rfl


end Erdos527.ScalarGaussianPath.Canonical

/- Concrete scalar closure source: CircularScalarLaw.lean -/

open scoped BigOperators ENNReal NNReal ProbabilityTheory Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Finset

namespace Erdos527.GaussianCircularization

noncomputable section

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {Q : Measure Ω'} {n : ℕ}

/-- The positive scalar coefficient with the same variance as the real part
of one circularized complex increment. -/
def scalarAmplitude (z : ℂ) : ℝ := Real.sqrt (Complex.normSq z)

lemma scalarAmplitude_sq (z : ℂ) : scalarAmplitude z ^ 2 = Complex.normSq z := by
  rw [scalarAmplitude, Real.sq_sqrt]
  exact Complex.normSq_nonneg z

def scalarRow (c : Fin n → ℂ) (t : Fin (n + 1)) (i : Fin n) : ℝ :=
  if i.1 < t.1 then scalarAmplitude (c i) else 0

def scalarPath (c : Fin n → ℂ) (q : Fin n → Ω' → ℝ) :
    Ω' → EuclideanSpace ℝ (Fin (n + 1)) :=
  linearPath (scalarRow c) q

lemma realRow_dot_self_eq_scalarRow (c : Fin n → ℂ) (s t : Fin (n + 1)) :
    (∑ j : Fin n ⊕ Fin n, realRow c s j * realRow c t j) =
      ∑ i : Fin n, scalarRow c s i * scalarRow c t i := by
  classical
  rw [Fintype.sum_sum_type]
  simp only [realRow, scalarRow]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases his : i.1 < s.1 <;> by_cases hit : i.1 < t.1
  · simp only [his, hit, if_true]
    rw [show scalarAmplitude (c i) * scalarAmplitude (c i) =
      scalarAmplitude (c i) ^ 2 by ring, scalarAmplitude_sq]
    simp [Complex.normSq_apply]
  all_goals simp [his, hit]

lemma integral_scalarPath (c : Fin n → ℂ) (q : Fin n → Ω' → ℝ)
    (hq : IndependentStandardGaussians q Q) (t : Fin (n + 1)) :
    ∫ ω, scalarPath c q ω t ∂Q = 0 :=
  integral_linearPath hq (scalarRow c) t

lemma covariance_scalarPath (c : Fin n → ℂ) (q : Fin n → Ω' → ℝ)
    (hq : IndependentStandardGaussians q Q) (s t : Fin (n + 1)) :
    cov[(fun ω ↦ scalarPath c q ω s), (fun ω ↦ scalarPath c q ω t); Q] =
      ∑ i, scalarRow c s i * scalarRow c t i := by
  exact covariance_linearPath hq (scalarRow c) (scalarRow c) s t

/-- The real circularized path has exactly the law of a scalar Gaussian walk
whose increment variances are `‖c i‖²`. -/
theorem map_realPath_eq_map_scalarPath
    (c : Fin n → ℂ) (g h : Fin n → Ω → ℝ) (q : Fin n → Ω' → ℝ)
    (hu : IndependentStandardGaussians (doubledFamily g h) P)
    (hq : IndependentStandardGaussians q Q) :
    Measure.map (realPath c g h) P = Measure.map (scalarPath c q) Q := by
  have hR := hasGaussianLaw_linearPath hu (realRow c)
  have hS := hasGaussianLaw_linearPath hq (scalarRow c)
  unfold HasEuclideanGaussianLaw at hR hS
  change Measure.map (linearPath (realRow c) (doubledFamily g h)) P =
    Measure.map (linearPath (scalarRow c) q) Q
  letI := hu.indep.isProbabilityMeasure
  letI := hq.indep.isProbabilityMeasure
  letI : IsGaussian (Measure.map (linearPath (realRow c) (doubledFamily g h)) P) :=
    hR.isGaussian_map
  letI : IsGaussian (Measure.map (linearPath (scalarRow c) q) Q) :=
    hS.isGaussian_map
  apply IsGaussian.ext
  · rw [integral_map hR.aemeasurable IsGaussian.integrable_id.aestronglyMeasurable,
      integral_map hS.aemeasurable IsGaussian.integrable_id.aestronglyMeasurable]
    ext t
    simp only [id_eq]
    rw [eval_integral_piLp
        (fun s ↦ (hR.memLp_two.eval_piLp s).integrable (by norm_num)) t,
      eval_integral_piLp
        (fun s ↦ (hS.memLp_two.eval_piLp s).integrable (by norm_num)) t]
    exact (integral_linearPath hu (realRow c) t).trans
      (integral_linearPath hq (scalarRow c) t).symm
  · ext x y
    unfold linearPath
    have hmR (t : Fin (n + 1)) :
        MemLp (fun ω ↦ ∑ j, realRow c t j * doubledFamily g h j ω) 2 P :=
      memLp_finsetSum Finset.univ fun j _ ↦ (hu.memLp_two j).const_mul _
    have hmS (t : Fin (n + 1)) :
        MemLp (fun ω ↦ ∑ j, scalarRow c t j * q j ω) 2 Q :=
      memLp_finsetSum Finset.univ fun j _ ↦ (hq.memLp_two j).const_mul _
    rw [covarianceBilin_apply_pi hmR, covarianceBilin_apply_pi hmS]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    have hcr := covariance_linearPath hu (realRow c) (realRow c) s t
    have hcs := covariance_linearPath hq (scalarRow c) (scalarRow c) s t
    unfold linearPath at hcr hcs
    have hc : cov[(fun ω ↦ ∑ j, realRow c s j * doubledFamily g h j ω),
        (fun ω ↦ ∑ j, realRow c t j * doubledFamily g h j ω); P] =
      cov[(fun ω ↦ ∑ j, scalarRow c s j * q j ω),
        (fun ω ↦ ∑ j, scalarRow c t j * q j ω); Q] := by
      calc
        _ = ∑ j, realRow c s j * realRow c t j := hcr
        _ = ∑ j, scalarRow c s j * scalarRow c t j :=
          realRow_dot_self_eq_scalarRow c s t
        _ = _ := hcs.symm
    exact congrArg (fun z ↦ x s * y t * z) hc

theorem measure_realPath_mem_eq_scalarPath_mem
    (c : Fin n → ℂ) (g h : Fin n → Ω → ℝ) (q : Fin n → Ω' → ℝ)
    (hu : IndependentStandardGaussians (doubledFamily g h) P)
    (hq : IndependentStandardGaussians q Q)
    (A : Set (EuclideanSpace ℝ (Fin (n + 1)))) (hA : MeasurableSet A) :
    P { ω | realPath c g h ω ∈ A } = Q { ω | scalarPath c q ω ∈ A } := by
  rw [show { ω | realPath c g h ω ∈ A } = realPath c g h ⁻¹' A by rfl,
    show { ω | scalarPath c q ω ∈ A } = scalarPath c q ⁻¹' A by rfl,
    ← Measure.map_apply_of_aemeasurable
      (aemeasurable_realPath c g h hu) hA,
    ← Measure.map_apply_of_aemeasurable
      ((by
        have hs := hasGaussianLaw_linearPath hq (scalarRow c)
        unfold HasEuclideanGaussianLaw at hs
        exact hs.aemeasurable) : AEMeasurable (scalarPath c q) Q) hA,
    map_realPath_eq_map_scalarPath c g h q hu hq]


end
end Erdos527.GaussianCircularization

/- Concrete scalar closure source: PartitionToBlocks.lean -/

open scoped BigOperators
open Finset

namespace Erdos527.ScalarGaussianPath.FullAssembly

noncomputable section

def testBlockIndex {n B : ℕ} (len : Fin B → ℕ)
    (hsum : ∑ k, len k = n) (k : Fin B) (j : Fin (len k)) : Fin n :=
  Fin.cast hsum (finSigmaFinEquiv ⟨k, j⟩)


lemma sum_len_before_eq {α : Type*} (blocks : List (List α))
    (k : Fin blocks.length) :
    ∑ i : Fin k, (blocks.get (Fin.castLE k.isLt.le i)).length =
      ((blocks.map List.length).take k).sum := by
  rw [← List.ofFn_getElem_eq_map]
  rw [List.sum_take_ofFn]
  apply Finset.sum_bij (fun i _ ↦ Fin.castLE k.isLt.le i)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact i.isLt
  · intro i hi j hj hij
    exact Fin.castLE_injective _ hij
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨⟨j, hj⟩, Finset.mem_univ _, ?_⟩
    rfl
  · intro i hi
    rfl

lemma blocks_length_sum {n : ℕ} (q : Fin n → ℝ) (blocks : List (List ℝ))
    (hflat : blocks.flatten = List.ofFn q) :
    ∑ k : Fin blocks.length, (blocks.get k).length = n := by
  rw [← List.sum_ofFn]
  have hof : List.ofFn (fun k : Fin blocks.length ↦ (blocks.get k).length) =
      blocks.map List.length := by
    simpa using List.ofFn_getElem_eq_map blocks List.length
  rw [hof]
  have hlength := congrArg List.length hflat
  simpa only [List.length_flatten, List.length_ofFn] using hlength

lemma get_flatten_block {α : Type*} (blocks : List (List α))
    (k : Fin blocks.length) (j : Fin (blocks.get k).length)
    (hvalid : ((blocks.map List.length).take k).sum + j < blocks.flatten.length) :
    blocks.flatten[((blocks.map List.length).take k).sum + j]'hvalid =
      (blocks.get k).get j := by
  let off := ((blocks.map List.length).take k).sum
  let stop := ((blocks.map List.length).take (k + 1)).sum
  have hseg : (blocks.flatten.take stop).drop off = blocks[k.1]'k.isLt := by
    simpa only [off, stop] using
      List.drop_take_succ_flatten_eq_getElem blocks k k.isLt
  have hjdrop : j.1 < ((blocks.flatten.take stop).drop off).length := by
    rw [hseg]
    exact j.isLt
  have hget := List.getElem_of_eq hseg hjdrop
  rw [List.getElem_drop, List.getElem_take] at hget
  simpa using hget

lemma testBlockIndex_val_eq {n : ℕ} (q : Fin n → ℝ) (blocks : List (List ℝ))
    (hflat : blocks.flatten = List.ofFn q)
    (hsum : ∑ k : Fin blocks.length, (blocks.get k).length = n)
    (k : Fin blocks.length) (j : Fin (blocks.get k).length) :
    (testBlockIndex (fun k : Fin blocks.length ↦ (blocks.get k).length)
        hsum k j).val =
      ((blocks.map List.length).take k).sum + j := by
  unfold testBlockIndex
  rw [Fin.val_cast, finSigmaFinEquiv_apply]
  rw [sum_len_before_eq]

lemma q_testBlockIndex_eq_get {n : ℕ} (q : Fin n → ℝ)
    (blocks : List (List ℝ)) (hflat : blocks.flatten = List.ofFn q)
    (hsum : ∑ k : Fin blocks.length, (blocks.get k).length = n)
    (k : Fin blocks.length) (j : Fin (blocks.get k).length) :
    q (testBlockIndex (fun k : Fin blocks.length ↦ (blocks.get k).length)
        hsum k j) = (blocks.get k).get j := by
  let idx : Fin n := testBlockIndex
    (fun k : Fin blocks.length ↦ (blocks.get k).length) hsum k j
  have hlength : blocks.flatten.length = n := by
    have h := congrArg List.length hflat
    simpa only [List.length_ofFn] using h
  have hvalid : idx.val < blocks.flatten.length := by
    rw [hlength]
    exact idx.isLt
  have hflatget := List.getElem_of_eq hflat hvalid
  have hq : blocks.flatten[idx.val]'hvalid = q idx := by
    simpa only [List.getElem_ofFn] using hflatget
  have hidx : idx.val = ((blocks.map List.length).take k).sum + j := by
    exact testBlockIndex_val_eq q blocks hflat hsum k j
  have hvalid' : ((blocks.map List.length).take k).sum + j <
      blocks.flatten.length := by
    rwa [← hidx]
  calc
    q idx = blocks.flatten[idx.val]'hvalid := hq.symm
    _ = blocks.flatten[((blocks.map List.length).take k).sum + j]'hvalid' := by
      congr
    _ = (blocks.get k).get j := get_flatten_block blocks k j hvalid'

lemma testBlockIndex_energy_eq {n : ℕ} (q : Fin n → ℝ)
    (blocks : List (List ℝ)) (hflat : blocks.flatten = List.ofFn q)
    (hsum : ∑ k : Fin blocks.length, (blocks.get k).length = n)
    (k : Fin blocks.length) :
    (∑ j : Fin (blocks.get k).length,
      q (testBlockIndex (fun k : Fin blocks.length ↦ (blocks.get k).length)
        hsum k j)) = (blocks.get k).sum := by
  calc
    _ = ∑ j : Fin (blocks.get k).length, (blocks.get k).get j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact q_testBlockIndex_eq_get q blocks hflat hsum k j
    _ = (List.ofFn (blocks.get k).get).sum := by rw [List.sum_ofFn]
    _ = (blocks.get k).sum := by rw [List.ofFn_get]

theorem exists_consecutive_variance_partition {n : ℕ} (q : Fin n → ℝ) (u : ℝ)
    (hu : 0 < u) (hq0 : ∀ i, 0 ≤ q i)
    (hqle : ∀ i, q i ≤ u ^ 2 / 128)
    (htotal : u ^ 2 / 128 ≤ ∑ i, q i) :
    ∃ (B : ℕ) (len : Fin B → ℕ) (hsum : ∑ k, len k = n),
      0 < B ∧
      (∀ k, 0 < len k) ∧
      (∀ k, u ^ 2 / 128 ≤
          ∑ j : Fin (len k), q (testBlockIndex len hsum k j) ∧
        (∑ j : Fin (len k), q (testBlockIndex len hsum k j)) ≤ u ^ 2 / 32) ∧
      (B : ℝ) ≤ 128 * ((∑ i, q i) / u ^ 2) := by
  obtain ⟨blocks, hflat, hne, hbounds, hcount⟩ :=
    exists_variance_chunks_fin q u hu hq0 hqle htotal
  let len : Fin blocks.length → ℕ := fun k ↦ (blocks.get k).length
  have hsum : ∑ k, len k = n := by
    exact blocks_length_sum q blocks hflat
  have hB : 0 < blocks.length := by
    have hqsum : 0 < ∑ i, q i := by
      have hu2 : 0 < u ^ 2 / 128 := by positivity
      exact hu2.trans_le htotal
    have hflatsum : blocks.flatten.sum = ∑ i, q i := by
      rw [hflat, List.sum_ofFn]
    have hflatne : blocks.flatten ≠ [] := by
      intro hnil
      rw [hnil] at hflatsum
      simp only [List.sum_nil] at hflatsum
      linarith
    apply Nat.pos_of_ne_zero
    intro hzero
    have hblocks : blocks = [] := List.eq_nil_of_length_eq_zero hzero
    exact hflatne (by simp only [hblocks, List.flatten_nil])
  refine ⟨blocks.length, len, hsum, hB, ?_, ?_, hcount⟩
  · intro k
    apply Nat.pos_of_ne_zero
    intro hz
    exact hne (blocks.get k) (List.get_mem blocks k)
      (List.eq_nil_of_length_eq_zero hz)
  · intro k
    have hb := hbounds (blocks.get k) (List.get_mem blocks k)
    have he := testBlockIndex_energy_eq q blocks hflat hsum k
    simpa only [len, he] using hb

end

end Erdos527.ScalarGaussianPath.FullAssembly

/- Concrete scalar closure source: FullScalarAssembly.lean -/

open scoped BigOperators ENNReal NNReal ProbabilityTheory Topology
open MeasureTheory ProbabilityTheory Set Filter Finset

namespace Erdos527.ScalarGaussianPath.FullAssembly

noncomputable section

open Erdos527.GaussianCircularization
open Erdos527.ScalarGaussianPath.Canonical

/-- The order-preserving index of coordinate `j` in consecutive block `k`. -/
def blockIndex {n B : ℕ} (len : Fin B → ℕ)
    (hsum : ∑ k, len k = n) (k : Fin B) (j : Fin (len k)) : Fin n :=
  Fin.cast hsum (finSigmaFinEquiv ⟨k, j⟩)

lemma blockIndex_injective {n B : ℕ} (len : Fin B → ℕ)
    (hsum : ∑ k, len k = n) :
    Function.Injective (fun p : (k : Fin B) × Fin (len k) ↦
      blockIndex len hsum p.1 p.2) := by
  intro p q hpq
  apply finSigmaFinEquiv.injective
  exact (Fin.cast_inj hsum).mp hpq

lemma blockIndex_ne_of_ne {n B : ℕ} (len : Fin B → ℕ)
    (hsum : ∑ k, len k = n) {k l : Fin B} (hkl : k ≠ l)
    (i : Fin (len k)) (j : Fin (len l)) :
    blockIndex len hsum k i ≠ blockIndex len hsum l j := by
  intro h
  have hp : (⟨k, i⟩ : (k : Fin B) × Fin (len k)) = ⟨l, j⟩ :=
    blockIndex_injective len hsum h
  exact hkl (congrArg Sigma.fst hp)

/-- The coordinates belonging to a single consecutive block. -/
def blockCoordinates {n B : ℕ} (len : Fin B → ℕ)
    (hsum : ∑ k, len k = n) (k : Fin B)
    (x : EuclideanSpace ℝ (Fin n)) : Fin (len k) → ℝ :=
  fun j ↦ x (blockIndex len hsum k j)

/-- Weighted partial sums within one block, frozen after its last coordinate. -/
def blockPartialSum {n B : ℕ} (a : Fin n → ℝ) (len : Fin B → ℕ)
    (hsum : ∑ k, len k = n) (k : Fin B) :
    ℕ → EuclideanSpace ℝ (Fin n) → ℝ :=
  fun t x ↦ ∑ j : Fin (len k),
    if j.1 ≤ t then a (blockIndex len hsum k j) * x (blockIndex len hsum k j) else 0

lemma blockPartialSum_measurable {n B : ℕ} (a : Fin n → ℝ) (len : Fin B → ℕ)
    (hsum : ∑ k, len k = n) (k : Fin B) (t : ℕ) :
    Measurable (blockPartialSum a len hsum k t) := by
  unfold blockPartialSum
  apply Finset.measurable_sum Finset.univ
  intro j hj
  by_cases hjt : j.1 ≤ t
  · simp only [hjt, if_true]
    fun_prop
  · simp only [hjt, if_false]
    fun_prop

/-- The whole family of block coordinate vectors is jointly Gaussian. -/
lemma blockCoordinates_jointGaussian {n B : ℕ} (len : Fin B → ℕ)
    (hsum : ∑ k, len k = n) :
    HasGaussianLaw
      (fun x : EuclideanSpace ℝ (Fin n) ↦
        fun k (j : Fin (len k)) ↦ blockCoordinates len hsum k x j)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ]
      ((k : Fin B) → Fin (len k) → ℝ) :=
    ContinuousLinearMap.pi fun k ↦ ContinuousLinearMap.pi fun j ↦
      (innerSL ℝ) ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis
        (blockIndex len hsum k j))
  have hid : HasGaussianLaw (id : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n)) (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    IsGaussian.hasGaussianLaw_id
  have hm := HasGaussianLaw.map_of_measurable L hid (by fun_prop)
  convert hm using 1
  funext x k j
  change x (blockIndex len hsum k j) = _
  exact (EuclideanSpace.basisFun_inner (Fin n) ℝ x (blockIndex len hsum k j)).symm

lemma blockCoordinates_iIndep {n B : ℕ} (len : Fin B → ℕ)
    (hsum : ∑ k, len k = n) :
    iIndepFun (fun k (x : EuclideanSpace ℝ (Fin n)) ↦
      blockCoordinates len hsum k x)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  apply (blockCoordinates_jointGaussian len hsum).iIndepFun_of_covariance_eval
  intro k l hkl i j
  change cov[(fun x : EuclideanSpace ℝ (Fin n) ↦
      x (blockIndex len hsum k i)),
    (fun x : EuclideanSpace ℝ (Fin n) ↦ x (blockIndex len hsum l j));
      stdGaussian (EuclideanSpace ℝ (Fin n))] = 0
  rw [coord_covariance, if_neg (blockIndex_ne_of_ne len hsum hkl i j)]

lemma blockPartialSum_iIndep {n B : ℕ} (a : Fin n → ℝ) (len : Fin B → ℕ)
    (hsum : ∑ k, len k = n) :
    iIndepFun (fun k (x : EuclideanSpace ℝ (Fin n)) t ↦
      blockPartialSum a len hsum k t x)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  apply (blockCoordinates_iIndep len hsum).comp
    (fun k y t ↦ ∑ j : Fin (len k),
      if j.1 ≤ t then a (blockIndex len hsum k j) * y j else 0)
  intro k
  rw [measurable_pi_iff]
  intro t
  apply Finset.measurable_sum Finset.univ
  intro j hj
  by_cases hjt : j.1 ≤ t
  · simp only [hjt, if_true]
    fun_prop
  · simp only [hjt, if_false]
    fun_prop

/-- The canonical one-block estimate with a positive length rather than a
`N+1`-shaped coefficient type. -/
theorem canonical_finiteGaussian_path_endpoint_lower_pos
    (n : ℕ) (hn : 0 < n) (c : Fin n → ℝ) (u center h : ℝ)
    (hu : 0 < u) (hh : 0 ≤ h) (hhu : h ≤ u / 4)
    (hcenter : |center| ≤ u / 4)
    (hvlo : u ^ 2 / 128 ≤ ∑ i, c i ^ 2)
    (hvhi : (∑ i, c i ^ 2) ≤ u ^ 2 / 32) :
    (1 / 2 : ℝ≥0∞) *
        ENNReal.ofReal ((h / (2 * u)) * Real.exp (-256)) ≤
      (stdGaussian (EuclideanSpace ℝ (Fin n))) {x |
        (∀ i : Fin n, |finiteGaussianPartialSum c i.1 x| ≤ u) ∧
          finiteGaussianPartialSum c (n - 1) x ∈ Set.Icc (center - h) (center + h)} := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have henergy : finiteGaussianTotalEnergy N c = ∑ i, c i ^ 2 := by
    unfold finiteGaussianTotalEnergy
    rw [← Fin.sum_univ_eq_sum_range (finiteWeightedVariance c) (N + 1)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [finiteWeightedVariance, dif_pos i.2]
  have h := canonical_finiteGaussian_path_endpoint_lower N c u center h
    hu hh hhu hcenter (by simpa only [henergy] using hvlo)
    (by simpa only [henergy] using hvhi)
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using h

/-- Euclidean vector of the coordinates in block `k`. -/
def blockEuclideanCoordinates {n B : ℕ} (len : Fin B → ℕ)
    (hsum : ∑ k, len k = n) (k : Fin B)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin (len k)) :=
  WithLp.toLp 2 (blockCoordinates len hsum k x)

lemma blockEuclideanCoordinates_hasLaw {n B : ℕ} (len : Fin B → ℕ)
    (hsum : ∑ k, len k = n) (k : Fin B) :
    HasLaw (blockEuclideanCoordinates len hsum k)
      (stdGaussian (EuclideanSpace ℝ (Fin (len k))))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  let e : Fin (len k) → Fin n := fun j ↦ blockIndex len hsum k j
  have he : Function.Injective e := by
    intro i j hij
    have hp : (⟨k, i⟩ : (k : Fin B) × Fin (len k)) = ⟨k, j⟩ :=
      blockIndex_injective len hsum hij
    cases hp
    rfl
  have hind : iIndepFun (fun j (x : EuclideanSpace ℝ (Fin n)) ↦ x (e j))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    ProbabilityTheory.iIndepFun.precomp he (coord_iIndep (n := n))
  have hlaw : ∀ j, HasLaw (fun x : EuclideanSpace ℝ (Fin n) ↦ x (e j))
      (gaussianReal 0 1) (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    fun j ↦ coord_hasLaw (e j)
  have hpi := hind.hasLaw_pi hlaw
  refine ⟨(by unfold blockEuclideanCoordinates blockCoordinates; fun_prop), ?_⟩
  change (stdGaussian (EuclideanSpace ℝ (Fin n))).map
      (fun x ↦ WithLp.toLp 2 (fun j ↦ x (e j))) = _
  rw [show (fun x : EuclideanSpace ℝ (Fin n) ↦
      WithLp.toLp 2 (fun j ↦ x (e j))) =
      (WithLp.toLp 2) ∘ (fun x : EuclideanSpace ℝ (Fin n) ↦ fun j ↦ x (e j)) by rfl,
    ← MeasureTheory.Measure.map_map]
  · rw [hpi.map_eq, map_pi_eq_stdGaussian]
  · fun_prop
  · fun_prop

/-- Coefficients of a single block, in its local consecutive order. -/
def blockCoeffs {n B : ℕ} (a : Fin n → ℝ) (len : Fin B → ℕ)
    (hsum : ∑ k, len k = n) (k : Fin B) : Fin (len k) → ℝ :=
  fun j ↦ a (blockIndex len hsum k j)

lemma blockPartialSum_eq_local {n B : ℕ} (a : Fin n → ℝ) (len : Fin B → ℕ)
    (hsum : ∑ k, len k = n) (k : Fin B) (t : Fin (len k))
    (x : EuclideanSpace ℝ (Fin n)) :
    blockPartialSum a len hsum k t.1 x =
      finiteGaussianPartialSum (blockCoeffs a len hsum k) t.1
        (blockEuclideanCoordinates len hsum k x) := by
  unfold blockPartialSum finiteGaussianPartialSum partialSum blockCoeffs
    blockEuclideanCoordinates blockCoordinates
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero]
  apply Finset.sum_bij (fun j _ ↦ j.1)
  · intro j hj
    rw [Finset.mem_filter] at hj
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj.2)
  · intro i hi j hj hij
    exact Fin.ext hij
  · intro j hj
    have hjlen : j < len k := (Finset.mem_range.mp hj).trans_le
      (Nat.succ_le_iff.mpr t.2)
    refine ⟨⟨j, hjlen⟩, ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, Nat.le_of_lt_succ (Finset.mem_range.mp hj)⟩
  · intro j hj
    rw [finiteWeightedCoord, dif_pos j.2]

lemma block_energy_eq {n B : ℕ} (a : Fin n → ℝ) (len : Fin B → ℕ)
    (hsum : ∑ k, len k = n) (k : Fin B) :
    (∑ j, blockCoeffs a len hsum k j ^ 2) =
      ∑ j : Fin (len k), a (blockIndex len hsum k j) ^ 2 := rfl

/-- A selected block in the global standard Gaussian vector has the same
one-block lower bound as its local canonical copy. -/
theorem block_path_endpoint_lower
    {n B : ℕ} (a : Fin n → ℝ) (len : Fin B → ℕ)
    (hsum : ∑ k, len k = n) (k : Fin B) (hlen : 0 < len k)
    (u center h : ℝ) (hu : 0 < u) (hh : 0 ≤ h) (hhu : h ≤ u / 4)
    (hcenter : |center| ≤ u / 4)
    (hvlo : u ^ 2 / 128 ≤ ∑ j : Fin (len k), a (blockIndex len hsum k j) ^ 2)
    (hvhi : (∑ j : Fin (len k), a (blockIndex len hsum k j) ^ 2) ≤ u ^ 2 / 32) :
    (1 / 2 : ℝ≥0∞) *
        ENNReal.ofReal ((h / (2 * u)) * Real.exp (-256)) ≤
      (stdGaussian (EuclideanSpace ℝ (Fin n))) {x |
        (∀ i : Fin (len k), |blockPartialSum a len hsum k i.1 x| ≤ u) ∧
          blockPartialSum a len hsum k (len k - 1) x ∈
            Set.Icc (center - h) (center + h)} := by
  let d := blockCoeffs a len hsum k
  let F : EuclideanSpace ℝ (Fin (len k)) → Fin (len k) → ℝ :=
    fun y i ↦ finiteGaussianPartialSum d i.1 y
  let A : Set (EuclideanSpace ℝ (Fin (len k))) := {y |
    (∀ i : Fin (len k), |finiteGaussianPartialSum d i.1 y| ≤ u) ∧
      finiteGaussianPartialSum d (len k - 1) y ∈ Set.Icc (center - h) (center + h)}
  have hF : Measurable F := by
    rw [measurable_pi_iff]
    intro i
    dsimp [F]
    unfold finiteGaussianPartialSum partialSum
    apply Finset.measurable_sum
    intro j hj
    exact (finiteWeightedCoord_stronglyMeasurable d j).measurable
  have hend : Measurable (finiteGaussianPartialSum d (len k - 1)) :=
    by
      unfold finiteGaussianPartialSum partialSum
      apply Finset.measurable_sum
      intro j hj
      exact (finiteWeightedCoord_stronglyMeasurable d j).measurable
  have hA : MeasurableSet A := by
    exact (measurableSet_pi_abs_le u).preimage hF |>.inter
      (measurableSet_Icc.preimage hend)
  have hlocal := canonical_finiteGaussian_path_endpoint_lower_pos (len k) hlen d
    u center h hu hh hhu hcenter
    (by simpa only [d, block_energy_eq] using hvlo)
    (by simpa only [d, block_energy_eq] using hvhi)
  have hlaw := blockEuclideanCoordinates_hasLaw len hsum k
  have hmeasure :
      (stdGaussian (EuclideanSpace ℝ (Fin n)))
          ((blockEuclideanCoordinates len hsum k) ⁻¹' A) =
        (stdGaussian (EuclideanSpace ℝ (Fin (len k)))) A := by
    rw [← hlaw.map_eq, Measure.map_apply
      (by unfold blockEuclideanCoordinates blockCoordinates; fun_prop) hA]
  rw [← hmeasure] at hlocal
  apply hlocal.trans_eq
  congr 1
  ext x
  simp only [Set.mem_preimage, A, Set.mem_setOf_eq, d]
  let last : Fin (len k) := ⟨len k - 1, by omega⟩
  have hlast : blockPartialSum a len hsum k (len k - 1) x =
      finiteGaussianPartialSum (blockCoeffs a len hsum k) (len k - 1)
        (blockEuclideanCoordinates len hsum k x) := by
    simpa only [last] using blockPartialSum_eq_local a len hsum k last x
  constructor
  · rintro ⟨hp, he⟩
    constructor
    · intro i
      simpa only [blockPartialSum_eq_local] using hp i
    · simpa only [hlast] using he
  · rintro ⟨hp, he⟩
    constructor
    · intro i
      simpa only [blockPartialSum_eq_local] using hp i
    · simpa only [hlast] using he

/-- The finite family of block paths, extended by zero outside its natural
index range so that it fits the `ℕ`-indexed iteration interface. -/
def assembledBlockPath {n m : ℕ} (a : Fin n → ℝ) (len : Fin (m + 1) → ℕ)
    (hsum : ∑ k, len k = n) (k t : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  if hk : k < m + 1 then blockPartialSum a len hsum ⟨k, hk⟩ t x else 0

def assembledBlockLast {m : ℕ} (len : Fin (m + 1) → ℕ) (k : ℕ) : ℕ :=
  if hk : k < m + 1 then len ⟨k, hk⟩ - 1 else 0

@[simp] lemma assembledBlockPath_of_le {n m : ℕ} (a : Fin n → ℝ)
    (len : Fin (m + 1) → ℕ) (hsum : ∑ k, len k = n)
    {k : ℕ} (hk : k ≤ m) (t : ℕ) :
    assembledBlockPath a len hsum k t =
      blockPartialSum a len hsum ⟨k, Nat.lt_succ_iff.mpr hk⟩ t := by
  unfold assembledBlockPath
  funext x
  rw [dif_pos (Nat.lt_succ_iff.mpr hk)]

@[simp] lemma assembledBlockLast_of_le {m : ℕ} (len : Fin (m + 1) → ℕ)
    {k : ℕ} (hk : k ≤ m) :
    assembledBlockLast len k = len ⟨k, Nat.lt_succ_iff.mpr hk⟩ - 1 := by
  unfold assembledBlockLast
  rw [dif_pos (Nat.lt_succ_iff.mpr hk)]

lemma assembledBlockPath_measurable {n m : ℕ} (a : Fin n → ℝ)
    (len : Fin (m + 1) → ℕ) (hsum : ∑ k, len k = n) (k t : ℕ) :
    Measurable (assembledBlockPath a len hsum k t) := by
  unfold assembledBlockPath
  split_ifs
  · exact blockPartialSum_measurable a len hsum _ t
  · fun_prop

/-- Every earlier assembled path is independent of the current block path. -/
lemma assembled_history_indep_current
    {n m : ℕ} (a : Fin n → ℝ) (len : Fin (m + 1) → ℕ)
    (hsum : ∑ k, len k = n) {k : ℕ} (hk : k ≤ m) :
    IndepFun (blockHistory (assembledBlockPath a len hsum) k)
      (fun (x : EuclideanSpace ℝ (Fin n))
        (i : Fin (assembledBlockLast len k + 1)) ↦
          assembledBlockPath a len hsum k i.1 x)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  let K : Fin (m + 1) := ⟨k, Nat.lt_succ_iff.mpr hk⟩
  let U : Finset (Fin (m + 1)) := Finset.Iio K
  have hdisj : Disjoint U ({K} : Finset (Fin (m + 1))) := by
    rw [Finset.disjoint_singleton_right]
    simp [U]
  have hpaths := blockPartialSum_iIndep a len hsum
  have hm : ∀ q : Fin (m + 1), Measurable
      (fun x : EuclideanSpace ℝ (Fin n) ↦ fun t ↦
        blockPartialSum a len hsum q t x) := by
    intro q
    rw [measurable_pi_iff]
    exact blockPartialSum_measurable a len hsum q
  have hp : IndepFun
      (fun x : EuclideanSpace ℝ (Fin n) ↦
        fun q : U ↦ fun t ↦ blockPartialSum a len hsum q.1 t x)
      (fun x : EuclideanSpace ℝ (Fin n) ↦
        fun q : ({K} : Finset (Fin (m + 1))) ↦
          fun t ↦ blockPartialSum a len hsum q.1 t x)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    ProbabilityTheory.iIndepFun.indepFun_finset U {K} hdisj hpaths hm
  let leftMap : ((q : U) → ℕ → ℝ) → (ℕ × ℕ → ℝ) := fun y p ↦
    if hp : p.1 < k then y ⟨⟨p.1, by omega⟩, by
      simp only [U, Finset.mem_Iio, K, Fin.mk_lt_mk]
      exact hp⟩ p.2 else 0
  let rightMap : ((q : ({K} : Finset (Fin (m + 1)))) → ℕ → ℝ) →
      (Fin (assembledBlockLast len k + 1) → ℝ) := fun y i ↦
    y ⟨K, by simp⟩ i.1
  have hleft : Measurable leftMap := by
    rw [measurable_pi_iff]
    intro p
    by_cases hpk : p.1 < k
    · simp only [leftMap, hpk, dite_true]
      fun_prop
    · simp only [leftMap, hpk, dite_false]
      fun_prop
  have hright : Measurable rightMap := by
    rw [measurable_pi_iff]
    intro i
    dsimp [rightMap]
    fun_prop
  have hc := hp.comp hleft hright
  convert hc using 1
  · funext x p
    by_cases hpk : p.1 < k
    · simp only [Function.comp_apply, leftMap, hpk, dite_true, blockHistory]
      rw [if_true, assembledBlockPath_of_le a len hsum (hpk.le.trans hk)]
    · simp [Function.comp_apply, leftMap, hpk, blockHistory]
  · funext x i
    simp only [Function.comp_apply, rightMap]
    rw [assembledBlockPath_of_le a len hsum hk]

/-- Iteration of the concrete consecutive blocks in one canonical standard
Gaussian vector. -/
theorem canonical_gaussian_partition_path_endpoint_lower
    {n m : ℕ} (a : Fin n → ℝ) (len : Fin (m + 1) → ℕ)
    (hsum : ∑ k, len k = n) (hlen : ∀ k, 0 < len k)
    (V u r : ℝ) (hu : 0 < u) (hr : 0 ≤ r) (hru : r ≤ u / 4)
    (hvlo : ∀ k, u ^ 2 / 128 ≤
      ∑ j : Fin (len k), a (blockIndex len hsum k j) ^ 2)
    (hvhi : ∀ k, (∑ j : Fin (len k),
      a (blockIndex len hsum k j) ^ 2) ≤ u ^ 2 / 32)
    (hcount : ((m + 1 : ℕ) : ℝ) ≤ 1 + 128 * (V / u ^ 2)) :
    ENNReal.ofReal ((r / u) * Real.exp (-33280 * (1 + V / u ^ 2))) ≤
      (stdGaussian (EuclideanSpace ℝ (Fin n)))
        (blockPathEndpointEvent (assembledBlockPath a len hsum)
          (assembledBlockLast len) u r m) := by
  let P : Measure (EuclideanSpace ℝ (Fin n)) :=
    stdGaussian (EuclideanSpace ℝ (Fin n))
  let S := assembledBlockPath a len hsum
  let last := assembledBlockLast len
  let q : ℝ≥0∞ := (1 / 2 : ℝ≥0∞) *
    ENNReal.ofReal ((1 / 8 : ℝ) * Real.exp (-256))
  let E : ℕ → Set (EuclideanSpace ℝ (Fin n)) :=
    fun k ↦ blockGoodEvent S last u (min k m)
  have hSmeas : ∀ k t, Measurable (S k t) :=
    fun k t ↦ assembledBlockPath_measurable a len hsum k t
  have hhist : ∀ k, Measurable (blockHistory S k) :=
    fun k ↦ measurable_blockHistory S hSmeas k
  have hzero : E 0 = Set.univ := by
    simp only [E, Nat.zero_min]
    exact blockGoodEvent_zero S last u hu
  have hstep : ∀ k, q * P (E k) ≤ P (E (k + 1)) := by
    intro k
    by_cases hk : k < m
    · have hklem : k ≤ m := hk.le
      have hmink : min k m = k := Nat.min_eq_left hk.le
      have hminks : min (k + 1) m = k + 1 := Nat.min_eq_left hk
      rw [show E k = blockGoodEvent S last u k by simp [E, hmink],
        show E (k + 1) = blockGoodEvent S last u (k + 1) by simp [E, hminks]]
      let K : Fin (m + 1) := ⟨k, Nat.lt_succ_iff.mpr hklem⟩
      let Y : EuclideanSpace ℝ (Fin n) → Fin (last k + 1) → ℝ :=
        fun x i ↦ S k i.1 x
      let transition : Set ((ℕ × ℕ → ℝ) × (Fin (last k + 1) → ℝ)) := {z |
        (∀ i, |historyState last k z.1 + z.2 i| ≤ 5 * u / 4) ∧
        historyState last k z.1 + z.2 ⟨last k, Nat.lt_succ_self (last k)⟩ ∈
          Set.Icc (-u / 4) (u / 4)}
      have hY : Measurable Y := measurable_pi_iff.mpr fun i ↦ hSmeas k i.1
      have htransition : MeasurableSet transition := by
        have hp : MeasurableSet {z : (ℕ × ℕ → ℝ) × (Fin (last k + 1) → ℝ) |
            ∀ i, |historyState last k z.1 + z.2 i| ≤ 5 * u / 4} := by
          rw [show {z : (ℕ × ℕ → ℝ) × (Fin (last k + 1) → ℝ) |
              ∀ i, |historyState last k z.1 + z.2 i| ≤ 5 * u / 4} =
              ⋂ i, {z | |historyState last k z.1 + z.2 i| ≤ 5 * u / 4} by
            ext z; simp]
          exact MeasurableSet.iInter fun i ↦ measurableSet_le
            (((measurable_historyState last k).comp measurable_fst).add
              ((measurable_pi_apply i).comp measurable_snd) |>.abs) measurable_const
        exact hp.inter (measurableSet_Icc.preimage
          (((measurable_historyState last k).comp measurable_fst).add
            ((measurable_pi_apply (⟨last k, Nat.lt_succ_self (last k)⟩ :
              Fin (last k + 1))).comp measurable_snd)))
      have hind : IndepFun (blockHistory S k) Y P := by
        simpa only [S, last, Y, P] using
          assembled_history_indep_current a len hsum hklem
      have hraw := indepFun_transition_lower hind (hhist k) hY
        (measurableSet_historyGood last u k) htransition q
      apply (hraw ?_).trans (measure_mono ?_)
      · intro x hx
        have hlastlen : last k + 1 = len K := by
          dsimp [last, K]
          rw [assembledBlockLast_of_le len hklem]
          exact Nat.sub_add_cancel (hlen K)
        have hlastval : last k = len K - 1 := by
          dsimp [last, K]
          exact assembledBlockLast_of_le len hklem
        have hxcore : |historyState last k x| ≤ u / 4 := by
          rcases hx.2 with ⟨hlo, hhi⟩
          rw [abs_le]
          constructor <;> linarith
        have hblock := block_path_endpoint_lower a len hsum K (hlen K)
          u (-historyState last k x) (u / 4) hu (by positivity) (by linarith)
          (by simpa only [abs_neg] using hxcore) (hvlo K) (hvhi K)
        have hqeq : (1 / 2 : ℝ≥0∞) *
            ENNReal.ofReal (((u / 4) / (2 * u)) * Real.exp (-256)) = q := by
          congr 1
          congr 1
          field_simp
          ring
        rw [hqeq] at hblock
        refine hblock.trans ?_
        rw [Measure.map_apply hY (measurable_prodMk_left htransition)]
        apply measure_mono
        rintro ω ⟨hp, he⟩
        constructor
        · intro i
          have hpi := hp (Fin.cast hlastlen i)
          have hYi : Y ω i =
              blockPartialSum a len hsum K (Fin.cast hlastlen i).1 ω := by
            dsimp [Y, S]
            rw [assembledBlockPath_of_le a len hsum hklem]
          calc
            |historyState last k x + Y ω i| ≤
                |historyState last k x| + |Y ω i| := abs_add_le _ _
            _ ≤ u / 4 + u := add_le_add hxcore (by simpa only [hYi] using hpi)
            _ = 5 * u / 4 := by ring
        · simp only [Prod.fst, Prod.snd]
          change historyState last k x + Y ω ⟨last k, _⟩ ∈ _
          dsimp [Y, S]
          rw [assembledBlockPath_of_le a len hsum hklem, hlastval]
          change blockPartialSum a len hsum K (len K - 1) ω ∈ _ at he
          rcases he with ⟨hlo, hhi⟩
          constructor <;> linarith
      · rintro ω ⟨hprev, hnew⟩
        exact blockGoodEvent_step_of S last u k hprev hnew.1 hnew.2
    · have hkm : m ≤ k := Nat.le_of_not_gt hk
      have hmin : min k m = m := Nat.min_eq_right hkm
      have hmins : min (k + 1) m = m := Nat.min_eq_right (hkm.trans (Nat.le_succ k))
      rw [show E k = blockGoodEvent S last u m by simp [E, hmin],
        show E (k + 1) = blockGoodEvent S last u m by simp [E, hmins]]
      exact (mul_le_mul' coreFactor_le_one le_rfl).trans (by simp)
  have hfinal : ((1 / 2 : ℝ≥0∞) *
      ENNReal.ofReal ((r / (2 * u)) * Real.exp (-256))) * P (E m) ≤
      P (blockPathEndpointEvent S last u r m) := by
    have hEm : E m = blockGoodEvent S last u m := by simp [E]
    rw [hEm]
    let K : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
    let Y : EuclideanSpace ℝ (Fin n) → Fin (last m + 1) → ℝ :=
      fun x i ↦ S m i.1 x
    let transition : Set ((ℕ × ℕ → ℝ) × (Fin (last m + 1) → ℝ)) := {z |
      (∀ i, |historyState last m z.1 + z.2 i| ≤ 5 * u / 4) ∧
      historyState last m z.1 + z.2 ⟨last m, Nat.lt_succ_self (last m)⟩ ∈
        Set.Icc (-r) r}
    have hY : Measurable Y := measurable_pi_iff.mpr fun i ↦ hSmeas m i.1
    have htransition : MeasurableSet transition := by
      have hp : MeasurableSet {z : (ℕ × ℕ → ℝ) × (Fin (last m + 1) → ℝ) |
          ∀ i, |historyState last m z.1 + z.2 i| ≤ 5 * u / 4} := by
        rw [show {z : (ℕ × ℕ → ℝ) × (Fin (last m + 1) → ℝ) |
            ∀ i, |historyState last m z.1 + z.2 i| ≤ 5 * u / 4} =
            ⋂ i, {z | |historyState last m z.1 + z.2 i| ≤ 5 * u / 4} by
          ext z; simp]
        exact MeasurableSet.iInter fun i ↦ measurableSet_le
          (((measurable_historyState last m).comp measurable_fst).add
            ((measurable_pi_apply i).comp measurable_snd) |>.abs) measurable_const
      exact hp.inter (measurableSet_Icc.preimage
        (((measurable_historyState last m).comp measurable_fst).add
          ((measurable_pi_apply (⟨last m, Nat.lt_succ_self (last m)⟩ :
            Fin (last m + 1))).comp measurable_snd)))
    have hind : IndepFun (blockHistory S m) Y P := by
      simpa only [S, last, Y, P] using
        assembled_history_indep_current a len hsum (le_refl m)
    have hraw := indepFun_transition_lower hind (hhist m) hY
      (measurableSet_historyGood last u m) htransition
      ((1 / 2 : ℝ≥0∞) * ENNReal.ofReal ((r / (2 * u)) * Real.exp (-256)))
    apply (hraw ?_).trans (measure_mono ?_)
    · intro x hx
      have hlastlen : last m + 1 = len K := by
        dsimp [last, K]
        rw [assembledBlockLast_of_le len (le_refl m)]
        exact Nat.sub_add_cancel (hlen K)
      have hlastval : last m = len K - 1 := by
        dsimp [last, K]
        exact assembledBlockLast_of_le len (le_refl m)
      have hxcore : |historyState last m x| ≤ u / 4 := by
        rcases hx.2 with ⟨hlo, hhi⟩
        rw [abs_le]
        constructor <;> linarith
      have hblock := block_path_endpoint_lower a len hsum K (hlen K)
        u (-historyState last m x) r hu hr hru
        (by simpa only [abs_neg] using hxcore) (hvlo K) (hvhi K)
      refine hblock.trans ?_
      rw [Measure.map_apply hY (measurable_prodMk_left htransition)]
      apply measure_mono
      rintro ω ⟨hp, he⟩
      constructor
      · intro i
        have hpi := hp (Fin.cast hlastlen i)
        have hYi : Y ω i =
            blockPartialSum a len hsum K (Fin.cast hlastlen i).1 ω := by
          dsimp [Y, S]
          rw [assembledBlockPath_of_le a len hsum (le_refl m)]
        calc
          |historyState last m x + Y ω i| ≤
              |historyState last m x| + |Y ω i| := abs_add_le _ _
          _ ≤ u / 4 + u := add_le_add hxcore (by simpa only [hYi] using hpi)
          _ = 5 * u / 4 := by ring
      · simp only [Prod.fst, Prod.snd]
        change historyState last m x + Y ω ⟨last m, _⟩ ∈ _
        dsimp [Y, S]
        rw [assembledBlockPath_of_le a len hsum (le_refl m), hlastval]
        change blockPartialSum a len hsum K (len K - 1) ω ∈ _ at he
        rcases he with ⟨hlo, hhi⟩
        constructor <;> linarith
    · intro ω hω
      exact hω
  exact gaussian_iterated_path_endpoint_lower E
    (blockPathEndpointEvent S last u r m) m V u r hu hr hcount hzero hstep hfinal

/-- Greedy deterministic variance partition specialized to the canonical
Gaussian walk.  The resulting blocks are consecutive in the original order. -/
theorem canonical_gaussian_large_variance_blocks_lower
    {n : ℕ} (a : Fin n → ℝ) (u r : ℝ)
    (hu : 0 < u) (hr : 0 ≤ r) (hru : r ≤ u / 4)
    (hsmall : ∀ i, a i ^ 2 ≤ u ^ 2 / 128)
    (hlarge : u ^ 2 / 128 ≤ ∑ i, a i ^ 2) :
    ∃ (m : ℕ) (len : Fin (m + 1) → ℕ) (hsum : ∑ k, len k = n),
      (∀ k, 0 < len k) ∧
      ENNReal.ofReal ((r / u) *
          Real.exp (-33280 * (1 + (∑ i, a i ^ 2) / u ^ 2))) ≤
        (stdGaussian (EuclideanSpace ℝ (Fin n)))
          (blockPathEndpointEvent (assembledBlockPath a len hsum)
            (assembledBlockLast len) u r m) := by
  let q : Fin n → ℝ := fun i ↦ a i ^ 2
  obtain ⟨B, len, hsum, hB, hlen, hbounds, hcount⟩ :=
    exists_consecutive_variance_partition q u hu (fun i ↦ sq_nonneg (a i))
      (by simpa only [q] using hsmall) (by simpa only [q] using hlarge)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hB)
  refine ⟨m, len, hsum, hlen, ?_⟩
  apply canonical_gaussian_partition_path_endpoint_lower a len hsum hlen
    (∑ i, a i ^ 2) u r hu hr hru
  · intro k
    have hk := (hbounds k).1
    simpa only [q, testBlockIndex, blockIndex] using hk
  · intro k
    have hk := (hbounds k).2
    simpa only [q, testBlockIndex, blockIndex] using hk
  · have hc : (((m + 1 : ℕ) : ℝ)) ≤
        128 * ((∑ i, a i ^ 2) / u ^ 2) := by
      simpa only [q] using hcount
    linarith

/-- Direct small-total-variance alternative for a nonempty canonical walk. -/
theorem canonical_gaussian_small_variance_path_endpoint_lower_pos
    (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ) (u r : ℝ)
    (hu : 0 < u) (hr : 0 ≤ r) (hru : r ≤ u)
    (hvhi : (∑ i, a i ^ 2) ≤ u ^ 2 / 32) :
    ENNReal.ofReal ((r / u) * Real.exp (-260)) ≤
      (stdGaussian (EuclideanSpace ℝ (Fin n))) {x |
        (∀ i : Fin n, |finiteGaussianPartialSum a i.1 x| ≤ u) ∧
          |finiteGaussianPartialSum a (n - 1) x| ≤ r} := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have henergy : finiteGaussianTotalEnergy N a = ∑ i, a i ^ 2 := by
    unfold finiteGaussianTotalEnergy
    rw [← Fin.sum_univ_eq_sum_range (finiteWeightedVariance a) (N + 1)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [finiteWeightedVariance, dif_pos i.2]
  let v := finiteGaussianTotalVariance N a
  have hq0 : ∀ i : Fin (N + 1), 0 ≤
      finiteGaussianPrefixEnergy N a i / (v : ℝ) := by
    intro i
    exact div_nonneg (finiteGaussianPrefixEnergy_nonneg N a i) (NNReal.coe_nonneg v)
  have hq1 : ∀ i : Fin (N + 1),
      finiteGaussianPrefixEnergy N a i / (v : ℝ) ≤ 1 := by
    intro i
    by_cases hv : (v : ℝ) = 0
    · simp only [hv, div_zero]
      norm_num
    · apply (div_le_one (lt_of_le_of_ne (NNReal.coe_nonneg v) (Ne.symm hv))).2
      exact finiteGaussianPrefixEnergy_le_total N a i
  have h := gaussian_martingale_small_variance_path_endpoint_lower
    (finiteGaussianPartialSum_martingale a)
    (finiteGaussianPartialSum_memLp_two a) N v
    (finiteGaussianPrefixEnergy N a)
    (finiteGaussian_pathEndpoint_joint N a)
    (finiteGaussian_prefix_covariance_total N a)
    (by simpa [v] using finiteGaussian_total_covariance N a)
    (finiteGaussian_endpoint_hasLaw N a) hq0 hq1 u r hu hr hru
    (by simpa only [v, coe_finiteGaussianTotalVariance, henergy] using hvhi)
    (by rw [finiteGaussian_endpoint_sq_integral]; exact le_rfl)
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using h

end

end Erdos527.ScalarGaussianPath.FullAssembly

/- Concrete scalar closure source: ScalarPathCanonicalBridge.lean -/

open scoped BigOperators ENNReal NNReal ProbabilityTheory Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Finset

namespace Erdos527.GaussianCircularization

noncomputable section

open Erdos527.ScalarGaussianPath
open Erdos527.ScalarGaussianPath.Canonical

variable {n : ℕ}

def amplitudeCoeffs (c : Fin n → ℂ) : Fin n → ℝ := fun i ↦ scalarAmplitude (c i)

def canonicalCoords (n : ℕ) (i : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ := x i

lemma canonicalCoords_standard (n : ℕ) :
    IndependentStandardGaussians (canonicalCoords n)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  constructor
  · exact fun i ↦ coord_hasLaw i
  · exact coord_iIndep

lemma scalarPath_canonicalCoords_apply (c : Fin n → ℂ)
    (x : EuclideanSpace ℝ (Fin n)) (t : Fin (n + 1)) :
    scalarPath c (canonicalCoords n) x t =
      ∑ i with i.1 < t.1, amplitudeCoeffs c i * x i := by
  simp [scalarPath, linearPath, scalarRow, canonicalCoords, amplitudeCoeffs,
    Finset.sum_ite]

lemma scalarPath_succ_eq_partialSum (c : Fin n → ℂ)
    (x : EuclideanSpace ℝ (Fin n)) (k : Fin n) :
    scalarPath c (canonicalCoords n) x ⟨k.1 + 1, by omega⟩ =
      finiteGaussianPartialSum (amplitudeCoeffs c) k.1 x := by
  rw [scalarPath_canonicalCoords_apply]
  unfold finiteGaussianPartialSum partialSum
  apply Finset.sum_bij (fun i _ ↦ i.1)
  · intro i hi
    rw [Finset.mem_filter] at hi
    exact Finset.mem_range.mpr hi.2
  · intro i hi j hj hij
    exact Fin.ext hij
  · intro j hj
    have hjn : j < n := by
      have hjk : j < k.1 + 1 := Finset.mem_range.mp hj
      omega
    refine ⟨⟨j, hjn⟩, ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, Finset.mem_range.mp hj⟩
  · intro i hi
    rw [finiteWeightedCoord, dif_pos i.2]

lemma scalarPath_zero (c : Fin n → ℂ) (x : EuclideanSpace ℝ (Fin n)) :
    scalarPath c (canonicalCoords n) x 0 = 0 := by
  rw [scalarPath_canonicalCoords_apply]
  simp

lemma finiteGaussianTotalEnergy_amplitude (N : ℕ) (c : Fin (N + 1) → ℂ) :
    finiteGaussianTotalEnergy N (amplitudeCoeffs c) =
      ∑ i : Fin (N + 1), Complex.normSq (c i) := by
  unfold finiteGaussianTotalEnergy
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [finiteWeightedVariance, dif_pos i.2]
  exact scalarAmplitude_sq (c i)

theorem scalarPath_canonical_regular_lower
    (N : ℕ) (c : Fin (N + 1) → ℂ) (u r : ℝ)
    (hu : 0 < u) (hr : 0 ≤ r) (hru : r ≤ u / 4)
    (hvlo : u ^ 2 / 128 ≤ ∑ i, Complex.normSq (c i))
    (hvhi : (∑ i, Complex.normSq (c i)) ≤ u ^ 2 / 32) :
    (1 / 2 : ℝ≥0∞) *
        ENNReal.ofReal ((r / (2 * u)) * Real.exp (-256)) ≤
      (stdGaussian (EuclideanSpace ℝ (Fin (N + 1)))) {x |
        scalarPath c (canonicalCoords (N + 1)) x ∈
          pathEndpointSet u (Set.Icc (-r) r)} := by
  have hbase := canonical_finiteGaussian_path_endpoint_lower N
    (amplitudeCoeffs c) u 0 r hu hr hru (by
      rw [abs_zero]
      positivity)
    (by simpa [finiteGaussianTotalEnergy_amplitude] using hvlo)
    (by simpa [finiteGaussianTotalEnergy_amplitude] using hvhi)
  exact hbase.trans (measure_mono (by
    rintro x ⟨hpath, hend⟩
    constructor
    · intro t
      refine Fin.cases ?_ (fun k ↦ ?_) t
      · rw [scalarPath_zero]
        simpa using hu.le
      · change ‖scalarPath c (canonicalCoords (N + 1)) x
            ⟨k.1 + 1, by omega⟩‖ ≤ u
        rw [scalarPath_succ_eq_partialSum]
        simpa only [Real.norm_eq_abs] using hpath k
    · have he := scalarPath_succ_eq_partialSum c x
          (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))
      have hlast : (⟨N + 1, by omega⟩ : Fin (N + 2)) = Fin.last (N + 1) := by
        apply Fin.ext
        rfl
      rw [← hlast, he]
      simpa using hend))


end
end Erdos527.GaussianCircularization

/- Concrete scalar closure source: BlockEventGlobal.lean -/

open scoped BigOperators ENNReal NNReal ProbabilityTheory Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Set Filter Finset

namespace Erdos527.ScalarGaussianPath.FullAssembly

noncomputable section

open Erdos527.GaussianCircularization

def blockNatOffset {B : ℕ} (len : Fin B → ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, if hi : i < B then len ⟨i, hi⟩ else 0

def globalCoordTerm {n : ℕ} (a : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (i : ℕ) : ℝ :=
  if hi : i < n then a ⟨i, hi⟩ * x ⟨i, hi⟩ else 0

lemma blockNatOffset_succ {B : ℕ} (len : Fin B → ℕ)
    {k : ℕ} (hk : k < B) :
    blockNatOffset len (k + 1) = blockNatOffset len k + len ⟨k, hk⟩ := by
  simp [blockNatOffset, Finset.sum_range_succ, hk]

lemma blockIndex_val_eq_natOffset {n B : ℕ} (len : Fin B → ℕ)
    (hsum : ∑ k, len k = n) (k : Fin B) (j : Fin (len k)) :
    (blockIndex len hsum k j).val = blockNatOffset len k.1 + j.1 := by
  unfold blockIndex blockNatOffset
  rw [Fin.val_cast, finSigmaFinEquiv_apply]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range
    (fun i ↦ if hi : i < B then len ⟨i, hi⟩ else 0) k]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i.1 < B := i.isLt.trans k.isLt
  simp only [hik, dif_pos]
  congr 1

lemma blockPartialSum_eq_shifted_range {n B : ℕ} (a : Fin n → ℝ)
    (len : Fin B → ℕ) (hsum : ∑ k, len k = n)
    (k : Fin B) (t : Fin (len k)) (x : EuclideanSpace ℝ (Fin n)) :
    blockPartialSum a len hsum k t.1 x =
      ∑ j ∈ Finset.range (t.1 + 1),
        globalCoordTerm a x (blockNatOffset len k.1 + j) := by
  unfold blockPartialSum
  rw [show Finset.range (t.1 + 1) =
      Finset.filter (fun j ↦ j ≤ t.1) (Finset.range (len k)) by
    ext j
    simp only [Finset.mem_range, Finset.mem_filter]
    omega]
  rw [Finset.sum_filter]
  rw [← Fin.sum_univ_eq_sum_range
    (fun j ↦ if j ≤ t.1 then
      globalCoordTerm a x (blockNatOffset len k.1 + j) else 0) (len k)]
  apply Finset.sum_congr rfl
  intro j hj
  have hjlen : j.1 < len k := j.isLt
  by_cases hjt : j.1 ≤ t.1
  · simp only [hjt, if_true]
    unfold globalCoordTerm
    have hidx := (blockIndex len hsum k ⟨j, hjlen⟩).isLt
    rw [← blockIndex_val_eq_natOffset len hsum k j]
    simp only [hidx, dif_pos]
  · simp only [hjt, if_false]

lemma blockPartialSum_last_eq_shifted_range {n B : ℕ} (a : Fin n → ℝ)
    (len : Fin B → ℕ) (hsum : ∑ k, len k = n)
    (hlen : ∀ k, 0 < len k) (k : Fin B)
    (x : EuclideanSpace ℝ (Fin n)) :
    blockPartialSum a len hsum k (len k - 1) x =
      ∑ j ∈ Finset.range (len k),
        globalCoordTerm a x (blockNatOffset len k.1 + j) := by
  let t : Fin (len k) := ⟨len k - 1, by have := hlen k; omega⟩
  have h := blockPartialSum_eq_shifted_range a len hsum k t x
  simpa only [t, Nat.sub_add_cancel (hlen k)] using h

lemma historyState_assembled_eq_range {n m : ℕ} (a : Fin n → ℝ)
    (len : Fin (m + 1) → ℕ) (hsum : ∑ k, len k = n)
    (hlen : ∀ k, 0 < len k) (x : EuclideanSpace ℝ (Fin n))
    (k : ℕ) (hk : k ≤ m) :
    historyState (assembledBlockLast len) k
        (blockHistory (assembledBlockPath a len hsum) k x) =
      ∑ i ∈ Finset.range (blockNatOffset len k), globalCoordTerm a x i := by
  induction k with
  | zero => simp [historyState, blockNatOffset]
  | succ k ih =>
      have hkm : k ≤ m := by omega
      have hkB : k < m + 1 := Nat.lt_succ_iff.mpr hkm
      rw [historyState_blockHistory_succ]
      rw [ih hkm]
      rw [assembledBlockPath_of_le a len hsum hkm,
        assembledBlockLast_of_le len hkm]
      let K : Fin (m + 1) := ⟨k, hkB⟩
      have hlast := blockPartialSum_last_eq_shifted_range a len hsum hlen K x
      change blockPartialSum a len hsum K (len K - 1) x = _ at hlast
      rw [hlast, ← Finset.sum_range_add]
      rw [blockNatOffset_succ len hkB]

lemma translated_block_sum_eq_global_range {n m : ℕ} (a : Fin n → ℝ)
    (len : Fin (m + 1) → ℕ) (hsum : ∑ k, len k = n)
    (hlen : ∀ k, 0 < len k) (x : EuclideanSpace ℝ (Fin n))
    (k : ℕ) (hk : k ≤ m) (t : Fin (len ⟨k, Nat.lt_succ_iff.mpr hk⟩)) :
    historyState (assembledBlockLast len) k
        (blockHistory (assembledBlockPath a len hsum) k x) +
      assembledBlockPath a len hsum k t.1 x =
      ∑ i ∈ Finset.range (blockNatOffset len k + (t.1 + 1)),
        globalCoordTerm a x i := by
  rw [historyState_assembled_eq_range a len hsum hlen x k hk]
  rw [assembledBlockPath_of_le a len hsum hk]
  rw [blockPartialSum_eq_shifted_range]
  rw [← Finset.sum_range_add (globalCoordTerm a x)
    (blockNatOffset len k) (t.1 + 1)]

lemma blockNatOffset_all {n B : ℕ} (len : Fin B → ℕ)
    (hsum : ∑ k, len k = n) : blockNatOffset len B = n := by
  unfold blockNatOffset
  rw [← Fin.sum_univ_eq_sum_range
    (fun i ↦ if hi : i < B then len ⟨i, hi⟩ else 0) B]
  simpa using hsum

lemma scalarPath_eq_global_range {n : ℕ} (c : Fin n → ℂ)
    (x : EuclideanSpace ℝ (Fin n)) (t : Fin (n + 1)) :
    scalarPath c (canonicalCoords n) x t =
      ∑ i ∈ Finset.range t.1, globalCoordTerm (amplitudeCoeffs c) x i := by
  rw [scalarPath_canonicalCoords_apply]
  apply Finset.sum_bij (fun i _ ↦ i.1)
  · intro i hi
    rw [Finset.mem_filter] at hi
    exact Finset.mem_range.mpr hi.2
  · intro i hi j hj hij
    exact Fin.ext hij
  · intro j hj
    have hjt : j < t.1 := Finset.mem_range.mp hj
    have hjn : j < n := hjt.trans_le (by omega)
    refine ⟨⟨j, hjn⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjt⟩
  · intro i hi
    unfold globalCoordTerm
    simp only [i.isLt, dif_pos]

lemma blockIndex_eq_of_symm {n B : ℕ} (len : Fin B → ℕ)
    (hsum : ∑ k, len k = n) (p : Fin n) :
    let z := finSigmaFinEquiv.symm (Fin.cast hsum.symm p)
    blockIndex len hsum z.1 z.2 = p := by
  dsimp
  unfold blockIndex
  apply Fin.ext
  simpa using congrArg Fin.val
    (finSigmaFinEquiv.apply_symm_apply (Fin.cast hsum.symm p))

theorem blockPathEndpointEvent_subset_scalarPath
    {n m : ℕ} (c : Fin n → ℂ) (len : Fin (m + 1) → ℕ)
    (hsum : ∑ k, len k = n) (hlen : ∀ k, 0 < len k)
    (u r : ℝ) (hu : 0 ≤ u) (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ blockPathEndpointEvent
      (assembledBlockPath (amplitudeCoeffs c) len hsum)
      (assembledBlockLast len) u r m) :
    scalarPath c (canonicalCoords n) x ∈
      pathEndpointSet (5 * u / 4) (Set.Icc (-r) r) := by
  let S := assembledBlockPath (amplitudeCoeffs c) len hsum
  let last := assembledBlockLast len
  rcases hx with ⟨hcore, hfinalPath, hfinalEnd⟩
  constructor
  · intro T
    refine Fin.cases ?_ (fun p ↦ ?_) T
    · rw [scalarPath_zero]
      simpa only [Real.norm_eq_abs, abs_zero] using (by nlinarith : 0 ≤ 5 * u / 4)
    · let z := finSigmaFinEquiv.symm (Fin.cast hsum.symm p)
      let K : Fin (m + 1) := z.1
      let j : Fin (len K) := z.2
      have hKle : K.1 ≤ m := Nat.le_of_lt_succ K.isLt
      have hidx : blockIndex len hsum K j = p := by
        simpa only [z, K, j] using blockIndex_eq_of_symm len hsum p
      have htranslated :
          |historyState last K.1 (blockHistory S K.1 x) + S K.1 j.1 x| ≤
            5 * u / 4 := by
        have hlenEq : assembledBlockLast len K.1 + 1 = len K := by
          rw [assembledBlockLast_of_le len hKle]
          exact Nat.sub_add_cancel (hlen K)
        by_cases hKm : K.1 < m
        · have hc := hcore.1 K.1 hKm (Fin.cast hlenEq.symm j)
          have hhistEq :
              historyState last K.1 (blockHistory S m x) =
                historyState last K.1 (blockHistory S K.1 x) := by
            unfold historyState blockHistory
            apply Finset.sum_congr rfl
            intro q hq
            have hqK : q < K.1 := Finset.mem_range.mp hq
            simp only [hqK, hqK.trans hKm, if_true]
          rw [hhistEq] at hc
          simpa only [S, last, blockHistory, hKm, if_true,
            Fin.val_cast] using hc
        · have hKeq : K.1 = m := by omega
          have hf := hfinalPath (Fin.cast (by simpa only [hKeq] using hlenEq.symm) j)
          simpa only [hKeq, Fin.val_cast] using hf
      have hid := translated_block_sum_eq_global_range
        (amplitudeCoeffs c) len hsum hlen x K.1 hKle j
      have hoff : blockNatOffset len K.1 + (j.1 + 1) = p.1 + 1 := by
        have hv := congrArg Fin.val hidx
        rw [blockIndex_val_eq_natOffset] at hv
        omega
      change ‖scalarPath c (canonicalCoords n) x ⟨p.1 + 1, by omega⟩‖ ≤ _
      rw [Real.norm_eq_abs]
      calc
        |scalarPath c (canonicalCoords n) x ⟨p.1 + 1, by omega⟩| =
            |∑ i ∈ Finset.range (p.1 + 1),
              globalCoordTerm (amplitudeCoeffs c) x i| := by
                rw [scalarPath_eq_global_range]
        _ = |∑ i ∈ Finset.range (blockNatOffset len K.1 + (j.1 + 1)),
              globalCoordTerm (amplitudeCoeffs c) x i| := by rw [hoff]
        _ = |historyState last K.1 (blockHistory S K.1 x) + S K.1 j.1 x| := by
              rw [hid]
        _ ≤ 5 * u / 4 := htranslated
  · have hK : m < m + 1 := Nat.lt_succ_self m
    let K : Fin (m + 1) := ⟨m, hK⟩
    let j : Fin (len K) := ⟨len K - 1, by have := hlen K; omega⟩
    have hid := translated_block_sum_eq_global_range
      (amplitudeCoeffs c) len hsum hlen x m (le_refl m) j
    have hoff : blockNatOffset len m + (j.1 + 1) = n := by
      rw [show j.1 + 1 = len K by
        dsimp [j]
        exact Nat.sub_add_cancel (hlen K)]
      rw [← blockNatOffset_succ len hK, blockNatOffset_all len hsum]
    change scalarPath c (canonicalCoords n) x (Fin.last n) ∈ Set.Icc (-r) r
    have hscalar : scalarPath c (canonicalCoords n) x (Fin.last n) =
        historyState (assembledBlockLast len) m
            (blockHistory (assembledBlockPath (amplitudeCoeffs c) len hsum) m x) +
          assembledBlockPath (amplitudeCoeffs c) len hsum m j.1 x := by
      calc
        scalarPath c (canonicalCoords n) x (Fin.last n) =
          ∑ i ∈ Finset.range n, globalCoordTerm (amplitudeCoeffs c) x i := by
            simpa using scalarPath_eq_global_range c x (Fin.last n)
        _ = ∑ i ∈ Finset.range (blockNatOffset len m + (j.1 + 1)),
            globalCoordTerm (amplitudeCoeffs c) x i := by rw [hoff]
        _ = historyState (assembledBlockLast len) m
            (blockHistory (assembledBlockPath (amplitudeCoeffs c) len hsum) m x) +
          assembledBlockPath (amplitudeCoeffs c) len hsum m j.1 x := hid.symm
    rw [hscalar]
    have hjlast : j.1 = assembledBlockLast len m := by
      dsimp [j, K]
      rw [assembledBlockLast_of_le len (le_refl m)]
    simpa only [hjlast] using hfinalEnd


end

end Erdos527.ScalarGaussianPath.FullAssembly

/- Concrete scalar closure source: CanonicalAllScalar.lean -/

open scoped BigOperators ENNReal NNReal ProbabilityTheory Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Set Filter Finset

namespace Erdos527.ScalarGaussianPath.FullAssembly

noncomputable section

open Erdos527.GaussianCircularization
open Erdos527.ScalarGaussianPath.Canonical

lemma scalarPath_event_of_partialSums {n : ℕ} (hn : 0 < n)
    (c : Fin n → ℂ) (u r : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (hu : 0 ≤ u)
    (hx : (∀ i : Fin n,
      |finiteGaussianPartialSum (amplitudeCoeffs c) i.1 x| ≤ u) ∧
      |finiteGaussianPartialSum (amplitudeCoeffs c) (n - 1) x| ≤ r) :
    scalarPath c (canonicalCoords n) x ∈
      pathEndpointSet u (Set.Icc (-r) r) := by
  constructor
  · intro t
    refine Fin.cases ?_ (fun i ↦ ?_) t
    · rw [scalarPath_zero]
      simpa only [norm_zero] using hu
    · change ‖scalarPath c (canonicalCoords n) x
          ⟨i.1 + 1, by omega⟩‖ ≤ u
      rw [scalarPath_succ_eq_partialSum]
      simpa only [Real.norm_eq_abs] using hx.1 i
  · obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    have he := scalarPath_succ_eq_partialSum c x
      (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))
    change scalarPath c (canonicalCoords (N + 1)) x (Fin.last (N + 1)) ∈ _
    have hlast : (Fin.last (N + 1)) =
        (⟨N + 1, by omega⟩ : Fin (N + 2)) := by rfl
    rw [hlast, he]
    rw [Set.mem_Icc, ← abs_le]
    simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using hx.2

theorem canonical_scalarPath_all_variances_lower_pos
    (n : ℕ) (hn : 0 < n) (c : Fin n → ℂ) (u r : ℝ)
    (hu : 0 < u) (hr : 0 ≤ r) (hru : r ≤ u / 4)
    (hsmall : ∀ i, Complex.normSq (c i) ≤ u ^ 2 / 128) :
    ENNReal.ofReal ((r / u) * Real.exp (-33280 *
        (1 + (∑ i, Complex.normSq (c i)) / u ^ 2))) ≤
      (stdGaussian (EuclideanSpace ℝ (Fin n))) {x |
        scalarPath c (canonicalCoords n) x ∈
          pathEndpointSet (5 * u / 4) (Set.Icc (-r) r)} := by
  let a := amplitudeCoeffs c
  have ha_sq : ∀ i, a i ^ 2 = Complex.normSq (c i) :=
    fun i ↦ scalarAmplitude_sq (c i)
  have henergy : (∑ i, a i ^ 2) = ∑ i, Complex.normSq (c i) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact ha_sq i
  by_cases hlarge : u ^ 2 / 128 ≤ ∑ i, Complex.normSq (c i)
  · obtain ⟨m, len, hsum, hlen, hbound⟩ :=
      canonical_gaussian_large_variance_blocks_lower a u r hu hr hru
        (fun i ↦ by simpa only [ha_sq] using hsmall i)
        (by simpa only [ha_sq] using hlarge)
    rw [henergy] at hbound
    exact hbound.trans (measure_mono (fun x hx ↦
      blockPathEndpointEvent_subset_scalarPath c len hsum hlen u r hu.le x hx))
  · have hvhi : (∑ i, a i ^ 2) ≤ u ^ 2 / 32 := by
      have hu2 : 0 < u ^ 2 := sq_pos_of_pos hu
      have hlt : (∑ i, Complex.normSq (c i)) < u ^ 2 / 128 :=
        lt_of_not_ge hlarge
      rw [henergy]
      nlinarith
    have hbase := canonical_gaussian_small_variance_path_endpoint_lower_pos
      n hn a u r hu hr (hru.trans (by linarith)) hvhi
    have hfactor : 0 ≤ r / u := div_nonneg hr hu.le
    have hVnonneg : 0 ≤ (∑ i, Complex.normSq (c i)) / u ^ 2 :=
      div_nonneg (Finset.sum_nonneg (fun i _ ↦ Complex.normSq_nonneg _)) (sq_nonneg u)
    have hexp : Real.exp (-33280 *
        (1 + (∑ i, Complex.normSq (c i)) / u ^ 2)) ≤ Real.exp (-260) := by
      rw [Real.exp_le_exp]
      nlinarith
    calc
      ENNReal.ofReal ((r / u) * Real.exp (-33280 *
          (1 + (∑ i, Complex.normSq (c i)) / u ^ 2))) ≤
          ENNReal.ofReal ((r / u) * Real.exp (-260)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hexp hfactor)
      _ ≤ (stdGaussian (EuclideanSpace ℝ (Fin n))) {x |
          (∀ i : Fin n, |finiteGaussianPartialSum a i.1 x| ≤ u) ∧
            |finiteGaussianPartialSum a (n - 1) x| ≤ r} := hbase
      _ ≤ (stdGaussian (EuclideanSpace ℝ (Fin n))) {x |
          scalarPath c (canonicalCoords n) x ∈
            pathEndpointSet (5 * u / 4) (Set.Icc (-r) r)} := by
        apply measure_mono
        intro x hx
        have he := scalarPath_event_of_partialSums hn c u r x hu.le hx
        exact ⟨fun t ↦ (he.1 t).trans (by linarith), he.2⟩

theorem canonical_scalarPath_all_variances_lower
    (n : ℕ) (c : Fin n → ℂ) (u r : ℝ)
    (hu : 0 < u) (hr : 0 ≤ r) (hru : r ≤ u / 4)
    (hsmall : ∀ i, Complex.normSq (c i) ≤ u ^ 2 / 128) :
    ENNReal.ofReal ((r / u) * Real.exp (-33280 *
        (1 + (∑ i, Complex.normSq (c i)) / u ^ 2))) ≤
      (stdGaussian (EuclideanSpace ℝ (Fin n))) {x |
        scalarPath c (canonicalCoords n) x ∈
          pathEndpointSet (5 * u / 4) (Set.Icc (-r) r)} := by
  by_cases hn : n = 0
  · subst n
    have hevent : {x : EuclideanSpace ℝ (Fin 0) |
        scalarPath c (canonicalCoords 0) x ∈
          pathEndpointSet (5 * u / 4) (Set.Icc (-r) r)} = Set.univ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      constructor
      · intro t
        have ht : t = (0 : Fin 1) := Fin.eq_zero t
        subst ht
        rw [scalarPath_zero]
        norm_num
        linarith
      · change scalarPath c (canonicalCoords 0) x 0 ∈ Set.Icc (-r) r
        rw [scalarPath_zero]
        exact ⟨neg_nonpos.mpr hr, hr⟩
    rw [hevent, measure_univ]
    apply ENNReal.ofReal_le_one.mpr
    have hratio : r / u ≤ 1 := by
      apply (div_le_one hu).2
      linarith
    have hratio0 : 0 ≤ r / u := div_nonneg hr hu.le
    have he : Real.exp (-33280 *
        (1 + (∑ i : Fin 0, Complex.normSq (c i)) / u ^ 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      simp
    have he0 := Real.exp_pos (-33280 *
        (1 + (∑ i : Fin 0, Complex.normSq (c i)) / u ^ 2))
    nlinarith
  · exact canonical_scalarPath_all_variances_lower_pos n (Nat.pos_of_ne_zero hn)
      c u r hu hr hru hsmall

theorem circularized_realPath_all_variances_lower
    {n : ℕ} {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    (c : Fin n → ℂ) (g h : Fin n → Omega → ℝ)
    (hgh : IndependentStandardGaussians (doubledFamily g h) P)
    (u r : ℝ) (hu : 0 < u) (hr : 0 ≤ r) (hru : r ≤ u / 4)
    (hsmall : ∀ i, Complex.normSq (c i) ≤ u ^ 2 / 128) :
    ENNReal.ofReal ((r / u) * Real.exp (-33280 *
        (1 + (∑ i, Complex.normSq (c i)) / u ^ 2))) ≤
      P {x | realPath c g h x ∈
        pathEndpointSet (5 * u / 4) (Set.Icc (-r) r)} := by
  rw [Erdos527.GaussianCircularization.measure_realPath_mem_eq_scalarPath_mem
    c g h (canonicalCoords n)
    hgh (canonicalCoords_standard n)
    (pathEndpointSet (5 * u / 4) (Set.Icc (-r) r))
    (measurableSet_pathEndpointSet _ measurableSet_Icc)]
  exact canonical_scalarPath_all_variances_lower n c u r hu hr hru hsmall


end
end Erdos527.ScalarGaussianPath.FullAssembly

/-! ## Complete one-point Gaussian cutoff lower bound -/

namespace Erdos527.GaussianCutoffBridge

noncomputable section

/-- The complete scalar Gaussian estimate, circularization, and tube-to-cutoff bridge,
specialized to the flat one-point coefficient vector.  `V` may be any upper bound for the
total complex square energy. -/
theorem flat_gaussian_cutoff_lower_of_energy
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) (z : ℂ)
    (g h : Fin (scale N0 (k + 1) - scale N0 k) → Ω → ℝ)
    (hgh : GaussianCircularization.IndependentStandardGaussians
      (GaussianCircularization.doubledFamily g h) P)
    (u r V endpointScale prefixScale : ℝ)
    (hu : 0 < u) (hr : 0 ≤ r) (hru : r ≤ u / 4)
    (hsmall : ∀ i, Complex.normSq
      (OnePointLindeberg.flatPhaseCoefficient a N0 k z i) ≤ u ^ 2 / 128)
    (hV : (∑ i, Complex.normSq
      (OnePointLindeberg.flatPhaseCoefficient a N0 k z i)) ≤ V)
    (hend : |endpointScale| * (2 * r) ≤ 1)
    (hprefix : |prefixScale| * (5 * u / 2) ≤ 1) :
    (ENNReal.ofReal ((r / u) * Real.exp (-33280 * (1 + V / u ^ 2))) ^ 2).toReal ≤
      ∫ x, SmoothCutoffC4.endpointPrefixCutoff
          (uniformBlockCount k) endpointScale prefixScale
          (CutoffLindebergBridge.NormedLindeberg.linearCombination
            (OnePointLindeberg.flatBlockIncrementDirection a hN0 k z) x)
        ∂Erdos88.Invariance.gaussianProductMeasure
          (scale N0 (k + 1) - scale N0 k) := by
  let n := scale N0 (k + 1) - scale N0 k
  let c : Fin n → ℂ := OnePointLindeberg.flatPhaseCoefficient a N0 k z
  let qV : ℝ≥0∞ := ENNReal.ofReal
    ((r / u) * Real.exp (-33280 * (1 + V / u ^ 2)))
  let q : ℝ≥0∞ := ENNReal.ofReal
    ((r / u) * Real.exp (-33280 *
      (1 + (∑ i, Complex.normSq (c i)) / u ^ 2)))
  have hratio : 0 ≤ r / u := div_nonneg hr hu.le
  have henergy : (∑ i, Complex.normSq (c i)) ≤ V := hV
  have hdiv : (∑ i, Complex.normSq (c i)) / u ^ 2 ≤ V / u ^ 2 :=
    div_le_div_of_nonneg_right henergy (sq_nonneg u)
  have hexp : Real.exp (-33280 * (1 + V / u ^ 2)) ≤
      Real.exp (-33280 *
        (1 + (∑ i, Complex.normSq (c i)) / u ^ 2)) := by
    rw [Real.exp_le_exp]
    nlinarith
  have hqVq : qV ≤ q := by
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left hexp hratio
  have hreal := ScalarGaussianPath.FullAssembly.circularized_realPath_all_variances_lower
    c g h hgh u r hu hr hru hsmall
  have hreal' : qV ≤ P {x | GaussianCircularization.realPath c g h x ∈
      GaussianCircularization.pathEndpointSet (5 * u / 4) (Set.Icc (-r) r)} :=
    hqVq.trans hreal
  have htube : qV ^ 2 ≤ P (GaussianTubeGlue.complexTubeEvent c g
      (2 * (5 * u / 4)) (2 * r)) := by
    calc
      qV ^ 2 ≤
          P {x | GaussianCircularization.realPath c g h x ∈
            GaussianCircularization.pathEndpointSet
              (5 * u / 4) (Set.Icc (-r) r)} ^ 2 := by
        gcongr
      _ ≤ P (GaussianTubeGlue.complexTubeEvent c g
          (2 * (5 * u / 4)) (2 * r)) :=
        GaussianTubeGlue.original_complex_tube_lower_sq
          c g h hgh (5 * u / 4) r
  have hGind : iIndepFun g P := by
    simpa [GaussianCircularization.doubledFamily] using
      (ProbabilityTheory.iIndepFun.precomp (f :=
        GaussianCircularization.doubledFamily g h) Sum.inl_injective hgh.indep)
  have hGlaw : HasLaw (fun ω i ↦ g i ω)
      (GaussianTubeGlue.standardGaussianProduct n) P := by
    exact iIndepFun.hasLaw_pi (fun i ↦ hgh.law (Sum.inl i)) hGind
  change (qV ^ 2).toReal ≤ _
  apply ennreal_complexTube_lower_le_flat_gaussian_integral
    P a hN0 k z g hGlaw endpointScale prefixScale
      (2 * (5 * u / 4)) (2 * r) (qV ^ 2)
  · simpa only using hend
  · convert hprefix using 1 <;> ring
  · exact htube

end

end Erdos527.GaussianCutoffBridge

/-! ## Explicit branching parameters and summable transition budgets -/
open scoped BigOperators ENNReal NNReal Topology
open Filter MeasureTheory ProbabilityTheory

namespace Erdos527
namespace BranchParameterArithmetic

/-- Deterministic number of phases retained after scale `k`. -/
def targetSize (k : ℕ) : ℕ := 2 ^ (1000 * k ^ 2)

/-- One-point survival probability budget. -/
noncomputable def onePointTarget (k : ℕ) : ℝ :=
  ((2 ^ stepExponent k : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))

/-- Threshold below which a pair is treated as decorrelated. -/
noncomputable def correlationThreshold (k : ℕ) : ℝ :=
  (2 : ℝ) ^ (-(200 : ℝ) * (k : ℝ) ^ 2)

/-- A deliberately generous summable transition-failure budget. -/
noncomputable def transitionFailureBound (N0 k : ℕ) : ℝ :=
  (scale N0 k : ℝ) ^ (-(1 / 20 : ℝ))

lemma targetSize_pos (k : ℕ) : 0 < targetSize k := by
  simp [targetSize]

lemma targetSize_ne_zero (k : ℕ) : targetSize k ≠ 0 :=
  (targetSize_pos k).ne'

lemma onePointTarget_pos (k : ℕ) : 0 < onePointTarget k := by
  exact Real.rpow_pos_of_pos (by positivity) _

lemma onePointTarget_nonneg (k : ℕ) : 0 ≤ onePointTarget k :=
  (onePointTarget_pos k).le

lemma onePointTarget_le_one (k : ℕ) : onePointTarget k ≤ 1 := by
  rw [onePointTarget]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast one_le_stepFactor k)
    (by norm_num)

lemma correlationThreshold_pos (k : ℕ) : 0 < correlationThreshold k := by
  exact Real.rpow_pos_of_pos (by norm_num) _

lemma correlationThreshold_nonneg (k : ℕ) : 0 ≤ correlationThreshold k :=
  (correlationThreshold_pos k).le

lemma correlationThreshold_le_one (k : ℕ) : correlationThreshold k ≤ 1 := by
  rw [correlationThreshold]
  apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
  exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg _)

lemma transitionFailureBound_nonneg (N0 k : ℕ) :
    0 ≤ transitionFailureBound N0 k := by
  exact Real.rpow_nonneg (Nat.cast_nonneg _) _

lemma transitionFailureBound_pos {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) :
    0 < transitionFailureBound N0 k := by
  exact Real.rpow_pos_of_pos (by exact_mod_cast scale_pos hN0 k) _

lemma targetSize_succ (k : ℕ) :
    targetSize (k + 1) = targetSize k * 2 ^ (2000 * k + 1000) := by
  unfold targetSize
  rw [show 1000 * (k + 1) ^ 2 = 1000 * k ^ 2 + (2000 * k + 1000) by ring,
    pow_add]

lemma targetSize_le_scale {N0 k : ℕ} (hN0 : 0 < N0) (hk : 1000 ≤ k) :
    targetSize k ≤ scale N0 k := by
  have hexp : 1000 * k ^ 2 ≤ k ^ 3 := by
    nlinarith
  calc
    targetSize k = 2 ^ (1000 * k ^ 2) := rfl
    _ ≤ 2 ^ (k ^ 3) := Nat.pow_le_pow_right (by norm_num) hexp
    _ ≤ scale N0 k := pow_cube_le_scale hN0 k

lemma eventually_targetSize_le_scale {N0 : ℕ} (hN0 : 0 < N0) :
    ∀ᶠ k : ℕ in atTop, targetSize k ≤ scale N0 k := by
  filter_upwards [eventually_ge_atTop 1000] with k hk
  exact targetSize_le_scale hN0 hk

/-- The polynomial loss in the number of retained children costs at most a
thirtieth power of the step factor. -/
lemma branchChildDenom_le_stepFactor_rpow_thirtieth {k : ℕ} (hk : 1000 ≤ k) :
    (Grid.branchChildDenom k : ℝ) ≤
      ((2 ^ stepExponent k : ℕ) : ℝ) ^ (1 / 30 : ℝ) := by
  have hbase : k + 2 ≤ 2 ^ k := Grid.add_two_le_two_pow (by omega)
  have hnat : Grid.branchChildDenom k ≤ 2 ^ (k * 20) := by
    calc
      Grid.branchChildDenom k = (k + 2) ^ 20 := rfl
      _ ≤ (2 ^ k) ^ 20 := Nat.pow_le_pow_left hbase 20
      _ = 2 ^ (k * 20) := by rw [← pow_mul]
  have hexpNat : 30 * (k * 20) ≤ stepExponent k := by
    simp only [stepExponent]
    nlinarith
  have hexpReal : (k * 20 : ℕ) ≤ (stepExponent k : ℕ) / (30 : ℝ) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 30)).2
    have hcast : ((30 * (k * 20) : ℕ) : ℝ) ≤ (stepExponent k : ℝ) := by
      exact_mod_cast hexpNat
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_comm, mul_left_comm,
      mul_assoc] using hcast
  calc
    (Grid.branchChildDenom k : ℝ) ≤ ((2 ^ (k * 20) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    _ = (2 : ℝ) ^ ((k * 20 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      norm_num
    _ ≤ (2 : ℝ) ^ ((stepExponent k : ℕ) / (30 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexpReal
    _ = (((2 ^ stepExponent k : ℕ) : ℝ)) ^ (1 / 30 : ℝ) := by
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]
      rw [div_eq_mul_inv]
      convert Real.rpow_natCast_mul (by positivity : (0 : ℝ) ≤ 2)
        (stepExponent k) (1 / 30 : ℝ) using 1
      all_goals norm_num

lemma eventually_branchChildDenom_le_stepFactor_rpow_thirtieth :
    ∀ᶠ k : ℕ in atTop,
      (Grid.branchChildDenom k : ℝ) ≤
        ((2 ^ stepExponent k : ℕ) : ℝ) ^ (1 / 30 : ℝ) := by
  filter_upwards [eventually_ge_atTop 1000] with k hk
  exact branchChildDenom_le_stepFactor_rpow_thirtieth hk

lemma targetSize_cast_eq_two_rpow (k : ℕ) :
    (targetSize k : ℝ) = (2 : ℝ) ^ ((1000 * k ^ 2 : ℕ) : ℝ) := by
  calc
    (targetSize k : ℝ) = ((2 ^ (1000 * k ^ 2) : ℕ) : ℝ) := rfl
    _ = (2 : ℝ) ^ (1000 * k ^ 2 : ℕ) := by norm_num
    _ = (2 : ℝ) ^ ((1000 * k ^ 2 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]

lemma stepFactor_cast_eq_two_rpow (k : ℕ) :
    ((2 ^ stepExponent k : ℕ) : ℝ) =
      (2 : ℝ) ^ ((stepExponent k : ℕ) : ℝ) := by
  rw [Real.rpow_natCast]
  norm_num

lemma onePointTarget_eq_two_rpow (k : ℕ) :
    onePointTarget k =
      (2 : ℝ) ^ ((stepExponent k : ℕ) * (-(1 / 4 : ℝ))) := by
  rw [onePointTarget, stepFactor_cast_eq_two_rpow]
  exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) _ _).symm

lemma branchChildDenom_cast_le_two_rpow {k : ℕ} (hk : 3 ≤ k) :
    (Grid.branchChildDenom k : ℝ) ≤
      (2 : ℝ) ^ ((k * 20 : ℕ) : ℝ) := by
  have hbase : k + 2 ≤ 2 ^ k := Grid.add_two_le_two_pow hk
  have hnat : Grid.branchChildDenom k ≤ 2 ^ (k * 20) := by
    calc
      Grid.branchChildDenom k = (k + 2) ^ 20 := rfl
      _ ≤ (2 ^ k) ^ 20 := Nat.pow_le_pow_left hbase 20
      _ = 2 ^ (k * 20) := by rw [← pow_mul]
  calc
    (Grid.branchChildDenom k : ℝ) ≤ ((2 ^ (k * 20) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    _ = (2 : ℝ) ^ ((k * 20 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      norm_num

/-- Before integer division, the expected-child budget exceeds four times the
next target.  The factor four leaves room for both the floor and the `1/2`
lower-tail threshold. -/
lemma four_mul_targetSize_succ_mul_branchChildDenom_le {k : ℕ} (hk : 1000 ≤ k) :
    4 * (targetSize (k + 1) : ℝ) * (Grid.branchChildDenom k : ℝ) ≤
      onePointTarget k * (targetSize k : ℝ) *
        ((2 ^ stepExponent k : ℕ) : ℝ) := by
  have hD := branchChildDenom_cast_le_two_rpow (show 3 ≤ k by omega)
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hexp :
      (2 : ℝ) + (1000 * (k + 1) ^ 2 : ℕ) + (k * 20 : ℕ) ≤
        (stepExponent k : ℕ) * (-(1 / 4 : ℝ)) +
          (1000 * k ^ 2 : ℕ) + (stepExponent k : ℕ) := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    simp only [stepExponent]
    push_cast
    norm_num
    nlinarith
  calc
    4 * (targetSize (k + 1) : ℝ) * (Grid.branchChildDenom k : ℝ) ≤
        4 * (targetSize (k + 1) : ℝ) *
          (2 : ℝ) ^ ((k * 20 : ℕ) : ℝ) := by
      exact mul_le_mul_of_nonneg_left hD
        (mul_nonneg (by norm_num) (Nat.cast_nonneg (targetSize (k + 1))))
    _ = (2 : ℝ) ^
          ((2 : ℝ) + (1000 * (k + 1) ^ 2 : ℕ) + (k * 20 : ℕ)) := by
      rw [targetSize_cast_eq_two_rpow]
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ ≤ (2 : ℝ) ^
          ((stepExponent k : ℕ) * (-(1 / 4 : ℝ)) +
            (1000 * k ^ 2 : ℕ) + (stepExponent k : ℕ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = onePointTarget k * (targetSize k : ℝ) *
          ((2 ^ stepExponent k : ℕ) : ℝ) := by
      rw [onePointTarget_eq_two_rpow, targetSize_cast_eq_two_rpow,
        stepFactor_cast_eq_two_rpow,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]

/-- Casting a nontrivial natural quotient loses at most a factor two. -/
lemma half_real_div_lt_nat_div {m d : ℕ} (hd : 0 < d) (hdm : d ≤ m) :
    (m : ℝ) / (2 * d) < (m / d : ℕ) := by
  have hq : 0 < m / d := Nat.div_pos hdm hd
  have hm : m < d * (m / d + 1) := Nat.lt_mul_div_succ m hd
  have hq2 : m / d + 1 ≤ 2 * (m / d) := by omega
  have hm' : m < 2 * d * (m / d) := by
    calc
      m < d * (m / d + 1) := hm
      _ ≤ d * (2 * (m / d)) := Nat.mul_le_mul_left d hq2
      _ = 2 * d * (m / d) := by ring
  rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * d)]
  have hmR : (m : ℝ) < ((2 * d * (m / d) : ℕ) : ℝ) := by exact_mod_cast hm'
  simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_comm, mul_left_comm, mul_assoc] using hmR

/-- Application-ready one-generation size inequality, including the natural
quotient that is the exact cardinality of the retained child grid. -/
lemma targetSize_succ_le_expected_children_half {k : ℕ} (hk : 1000 ≤ k) :
    (targetSize (k + 1) : ℝ) ≤
      onePointTarget k *
          ((targetSize k : ℝ) *
            ((2 ^ stepExponent k / Grid.branchChildDenom k : ℕ) : ℝ)) / 2 := by
  let F : ℕ := 2 ^ stepExponent k
  let D : ℕ := Grid.branchChildDenom k
  have hD : 0 < D := Grid.branchChildDenom_pos k
  have hDF : D ≤ F := Grid.branchChildDenom_le_scale_refinement (by omega)
  have hfloor : (F : ℝ) / (2 * D) < (F / D : ℕ) :=
    half_real_div_lt_nat_div hD hDF
  have hbudget : 4 * (targetSize (k + 1) : ℝ) * (D : ℝ) ≤
      onePointTarget k * (targetSize k : ℝ) * (F : ℝ) := by
    simpa only [F, D] using four_mul_targetSize_succ_mul_branchChildDenom_le hk
  have hpositive : 0 < onePointTarget k * (targetSize k : ℝ) :=
    mul_pos (onePointTarget_pos k) (by exact_mod_cast targetSize_pos k)
  have hfloor' :
      onePointTarget k * (targetSize k : ℝ) * ((F : ℝ) / (2 * D)) <
        onePointTarget k * (targetSize k : ℝ) * (F / D : ℕ) := by
    exact mul_lt_mul_of_pos_left hfloor hpositive
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  calc
    (targetSize (k + 1) : ℝ) ≤
        (onePointTarget k * (targetSize k : ℝ) * F) / (4 * D) := by
      apply (le_div_iff₀ (mul_pos (by norm_num) hDreal)).2
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hbudget
    _ = (onePointTarget k * (targetSize k : ℝ) * ((F : ℝ) / (2 * D))) / 2 := by
      field_simp [ne_of_gt hDreal]
      <;> ring
    _ ≤ (onePointTarget k * (targetSize k : ℝ) * (F / D : ℕ)) / 2 := by
      exact div_le_div_of_nonneg_right hfloor'.le (by norm_num)
    _ = onePointTarget k *
          ((targetSize k : ℝ) * (F / D : ℕ)) / 2 := by ring

lemma eventually_targetSize_succ_le_expected_children_half :
    ∀ᶠ k : ℕ in atTop,
      (targetSize (k + 1) : ℝ) ≤
        onePointTarget k *
            ((targetSize k : ℝ) *
              ((2 ^ stepExponent k / Grid.branchChildDenom k : ℕ) : ℝ)) / 2 := by
  filter_upwards [eventually_ge_atTop 1000] with k hk
  exact targetSize_succ_le_expected_children_half hk

lemma stepFactor_pow_ten_eq_two_rpow (k : ℕ) :
    (((2 ^ stepExponent k : ℕ) : ℝ) ^ 10) =
      (2 : ℝ) ^ ((10 : ℝ) * (stepExponent k : ℕ)) := by
  rw [stepFactor_cast_eq_two_rpow]
  calc
    ((2 : ℝ) ^ ((stepExponent k : ℕ) : ℝ)) ^ 10 =
        ((2 : ℝ) ^ ((stepExponent k : ℕ) : ℝ)) ^ (10 : ℝ) := by
          exact (Real.rpow_natCast _ 10).symm
    _ = (2 : ℝ) ^ (((stepExponent k : ℕ) : ℝ) * (10 : ℝ)) :=
      (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) _ _).symm
    _ = (2 : ℝ) ^ ((10 : ℝ) * (stepExponent k : ℕ)) := by
      apply congrArg (fun x : ℝ ↦ (2 : ℝ) ^ x)
      ring

/-- The normalized off-correlation term appearing after the second-moment
division by the square of the one-point probability. -/
noncomputable def offCorrelationFailureBound (k : ℕ) : ℝ :=
  48 * (((2 ^ stepExponent k : ℕ) : ℝ) ^ 10) *
    correlationThreshold k ^ (1 / 4 : ℝ) / onePointTarget k ^ 2

lemma offCorrelationFailureBound_nonneg (k : ℕ) :
    0 ≤ offCorrelationFailureBound k := by
  exact div_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg _) _))
      (Real.rpow_nonneg (correlationThreshold_nonneg k) _))
    (sq_nonneg _)

lemma correlationThreshold_rpow_quarter_eq (k : ℕ) :
    correlationThreshold k ^ (1 / 4 : ℝ) =
      (2 : ℝ) ^ ((-(50 : ℝ)) * (k : ℝ) ^ 2) := by
  rw [correlationThreshold, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  apply congrArg (fun x : ℝ ↦ (2 : ℝ) ^ x)
  ring

lemma onePointTarget_sq_eq (k : ℕ) :
    onePointTarget k ^ 2 =
      (2 : ℝ) ^
        (2 * ((stepExponent k : ℕ) * (-(1 / 4 : ℝ)))) := by
  rw [pow_two, onePointTarget_eq_two_rpow,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 2
  ring

lemma offCorrelationFailureBound_eq (k : ℕ) :
    offCorrelationFailureBound k =
      48 * (2 : ℝ) ^
        ((10 : ℝ) * (stepExponent k : ℕ) +
          (-(50 : ℝ)) * (k : ℝ) ^ 2 -
          2 * ((stepExponent k : ℕ) * (-(1 / 4 : ℝ)))) := by
  rw [offCorrelationFailureBound, stepFactor_pow_ten_eq_two_rpow,
    correlationThreshold_rpow_quarter_eq, onePointTarget_sq_eq]
  rw [mul_assoc 48,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  rw [mul_div_assoc,
    ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]

/-- Even after normalization by `p²`, the off-correlation error is bounded
by a geometric sequence. -/
lemma offCorrelationFailureBound_le_geometric {k : ℕ} (hk : 3 ≤ k) :
    offCorrelationFailureBound k ≤ ((1 / 2 : ℝ) ^ k) := by
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hexp :
      (6 : ℝ) + ((10 : ℝ) * (stepExponent k : ℕ) +
        (-(50 : ℝ)) * (k : ℝ) ^ 2 -
        2 * ((stepExponent k : ℕ) * (-(1 / 4 : ℝ)))) ≤ -(k : ℝ) := by
    simp only [stepExponent]
    push_cast
    norm_num
    nlinarith
  calc
    offCorrelationFailureBound k =
        48 * (2 : ℝ) ^
          ((10 : ℝ) * (stepExponent k : ℕ) +
            (-(50 : ℝ)) * (k : ℝ) ^ 2 -
            2 * ((stepExponent k : ℕ) * (-(1 / 4 : ℝ)))) :=
      offCorrelationFailureBound_eq k
    _ ≤ (2 : ℝ) ^ (6 : ℝ) *
        (2 : ℝ) ^
          ((10 : ℝ) * (stepExponent k : ℕ) +
            (-(50 : ℝ)) * (k : ℝ) ^ 2 -
            2 * ((stepExponent k : ℕ) * (-(1 / 4 : ℝ)))) := by
      gcongr
      norm_num
    _ = (2 : ℝ) ^
        ((6 : ℝ) + ((10 : ℝ) * (stepExponent k : ℕ) +
          (-(50 : ℝ)) * (k : ℝ) ^ 2 -
          2 * ((stepExponent k : ℕ) * (-(1 / 4 : ℝ))))) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ ≤ (2 : ℝ) ^ (-(k : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = (1 / 2 : ℝ) ^ k := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_natCast]
      rw [← inv_pow]
      norm_num

lemma summable_offCorrelationFailureBound :
    Summable offCorrelationFailureBound := by
  have hgeom : Summable (fun k : ℕ ↦ 4294967296 * (1 / 2 : ℝ) ^ k) := by
    exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 4294967296
  apply Summable.of_nonneg_of_le offCorrelationFailureBound_nonneg _ hgeom
  intro k
  by_cases hk : k < 3
  · rw [offCorrelationFailureBound_eq]
    have he :
        (10 : ℝ) * (stepExponent k : ℕ) +
          (-(50 : ℝ)) * (k : ℝ) ^ 2 -
          2 * ((stepExponent k : ℕ) * (-(1 / 4 : ℝ))) ≤ 24 := by
      interval_cases k <;> norm_num [stepExponent]
    calc
      48 * (2 : ℝ) ^
          ((10 : ℝ) * (stepExponent k : ℕ) +
            (-(50 : ℝ)) * (k : ℝ) ^ 2 -
            2 * ((stepExponent k : ℕ) * (-(1 / 4 : ℝ)))) ≤
          48 * (2 : ℝ) ^ (24 : ℝ) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (by norm_num) he) (by norm_num)
      _ ≤ 4294967296 * (1 / 2 : ℝ) ^ k := by
        interval_cases k <;> norm_num
  · calc
      offCorrelationFailureBound k ≤ (1 / 2 : ℝ) ^ k :=
        offCorrelationFailureBound_le_geometric (by omega)
      _ ≤ 4294967296 * (1 / 2 : ℝ) ^ k := by
        have hpow : 0 ≤ (1 / 2 : ℝ) ^ k := pow_nonneg (by norm_num) _
        nlinarith

/-- A correlated-pair contribution allowing a very generous tenth power of
the step factor in the large-sieve/counting loss.  In a second-moment bound
this is the expression obtained from `D ≤ 4 M ρ⁻² F¹⁰`. -/
noncomputable def correlatedPairFailureBound (k : ℕ) : ℝ :=
  16 * (correlationThreshold k)⁻¹ ^ 2 *
      (((2 ^ stepExponent k : ℕ) : ℝ) ^ 10) /
    (onePointTarget k ^ 2 * (targetSize k : ℝ))

lemma correlatedPairFailureBound_nonneg (k : ℕ) :
    0 ≤ correlatedPairFailureBound k := by
  exact div_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num) (sq_nonneg _))
      (pow_nonneg (Nat.cast_nonneg _) _))
    (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _))

lemma correlationThreshold_inv_sq_eq (k : ℕ) :
    (correlationThreshold k)⁻¹ ^ 2 =
      (2 : ℝ) ^ ((400 : ℝ) * (k : ℝ) ^ 2) := by
  rw [correlationThreshold]
  rw [show ((2 : ℝ) ^ ((-(200 : ℝ)) * (k : ℝ) ^ 2))⁻¹ =
      (2 : ℝ) ^ (-((-(200 : ℝ)) * (k : ℝ) ^ 2)) by
        exact (Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) _).symm]
  rw [pow_two, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 2
  ring

lemma correlatedPairFailureBound_eq (k : ℕ) :
    correlatedPairFailureBound k =
      16 * (2 : ℝ) ^
        ((400 : ℝ) * (k : ℝ) ^ 2 +
          (10 : ℝ) * (stepExponent k : ℕ) -
          (2 * ((stepExponent k : ℕ) * (-(1 / 4 : ℝ))) +
            (1000 * k ^ 2 : ℕ))) := by
  rw [correlatedPairFailureBound, correlationThreshold_inv_sq_eq,
    stepFactor_pow_ten_eq_two_rpow, onePointTarget_sq_eq,
    targetSize_cast_eq_two_rpow,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  rw [mul_assoc 16,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  rw [mul_div_assoc,
    ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]

lemma correlatedPairFailureBound_le_geometric {k : ℕ} (hk : 1 ≤ k) :
    correlatedPairFailureBound k ≤ (1 / 2 : ℝ) ^ k := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hexp :
      (4 : ℝ) + ((400 : ℝ) * (k : ℝ) ^ 2 +
        (10 : ℝ) * (stepExponent k : ℕ) -
        (2 * ((stepExponent k : ℕ) * (-(1 / 4 : ℝ))) +
          (1000 * k ^ 2 : ℕ))) ≤ -(k : ℝ) := by
    simp only [stepExponent]
    push_cast
    norm_num
    nlinarith
  calc
    correlatedPairFailureBound k =
        16 * (2 : ℝ) ^
          ((400 : ℝ) * (k : ℝ) ^ 2 +
            (10 : ℝ) * (stepExponent k : ℕ) -
            (2 * ((stepExponent k : ℕ) * (-(1 / 4 : ℝ))) +
              (1000 * k ^ 2 : ℕ))) := correlatedPairFailureBound_eq k
    _ = (2 : ℝ) ^
        ((4 : ℝ) + ((400 : ℝ) * (k : ℝ) ^ 2 +
          (10 : ℝ) * (stepExponent k : ℕ) -
          (2 * ((stepExponent k : ℕ) * (-(1 / 4 : ℝ))) +
            (1000 * k ^ 2 : ℕ)))) := by
      rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) by norm_num,
        Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ ≤ (2 : ℝ) ^ (-(k : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = (1 / 2 : ℝ) ^ k := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast,
        ← inv_pow]
      norm_num

lemma summable_correlatedPairFailureBound :
    Summable correlatedPairFailureBound := by
  have hgeom : Summable (fun k : ℕ ↦ 65536 * (1 / 2 : ℝ) ^ k) := by
    exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 65536
  apply Summable.of_nonneg_of_le correlatedPairFailureBound_nonneg _ hgeom
  intro k
  rcases k with _ | k
  · rw [correlatedPairFailureBound_eq]
    norm_num [stepExponent]
    have hr : (2 : ℝ) ^ (21 / 2 : ℝ) ≤ (2 : ℝ) ^ (12 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    calc
      16 * (2 : ℝ) ^ (21 / 2 : ℝ) ≤ 16 * (2 : ℝ) ^ (12 : ℝ) :=
        mul_le_mul_of_nonneg_left hr (by norm_num)
      _ = 65536 := by norm_num
  · calc
      correlatedPairFailureBound (k + 1) ≤ (1 / 2 : ℝ) ^ (k + 1) :=
        correlatedPairFailureBound_le_geometric (by omega)
      _ ≤ 65536 * (1 / 2 : ℝ) ^ (k + 1) := by
        have hpow : 0 ≤ (1 / 2 : ℝ) ^ (k + 1) := pow_nonneg (by norm_num) _
        nlinarith

/-- Directly discharge the ordinary-pair part of the branching variance
bound from a `12 F¹⁰ ρ¹/⁴` factorization estimate. -/
lemma normalized_offCorrelation_charge_le (k : ℕ) {e : ℝ}
    (he : e ≤ 12 * (((2 ^ stepExponent k : ℕ) : ℝ) ^ 10) *
      correlationThreshold k ^ (1 / 4 : ℝ)) :
    4 * e / onePointTarget k ^ 2 ≤ offCorrelationFailureBound k := by
  unfold offCorrelationFailureBound
  have hp2 : 0 ≤ onePointTarget k ^ 2 := sq_nonneg _
  apply div_le_div_of_nonneg_right _ hp2
  nlinarith

/-- The same budget absorbs the Lindeberg part of the pair error whenever
`18 E` is below the conservative decorrelation allowance. -/
lemma normalized_lindeberg_charge_le (k : ℕ) {E : ℝ}
    (hE : 18 * E ≤ 12 * (((2 ^ stepExponent k : ℕ) : ℝ) ^ 10) *
      correlationThreshold k ^ (1 / 4 : ℝ)) :
    4 * (18 * E) / onePointTarget k ^ 2 ≤ offCorrelationFailureBound k :=
  normalized_offCorrelation_charge_le k hE

/-- Directly discharge the exceptional correlated-pair part.  `C` is the
actual candidate count; it is enough that it dominates `targetSize k`.
The hypothesis is the generic output of a large-sieve count summed over the
first phase. -/
lemma normalized_correlated_charge_le (k : ℕ) {C D : ℝ}
    (hC : (targetSize k : ℝ) ≤ C)
    (hD : D ≤ 4 * C * (correlationThreshold k)⁻¹ ^ 2 *
      (((2 ^ stepExponent k : ℕ) : ℝ) ^ 10)) :
    4 * D / (onePointTarget k * C) ^ 2 ≤ correlatedPairFailureBound k := by
  let A : ℝ := (correlationThreshold k)⁻¹ ^ 2 *
    (((2 ^ stepExponent k : ℕ) : ℝ) ^ 10)
  have hT : (0 : ℝ) < targetSize k := by exact_mod_cast targetSize_pos k
  have hCpos : 0 < C := hT.trans_le hC
  have hp : 0 < onePointTarget k := onePointTarget_pos k
  have hA : 0 ≤ A := mul_nonneg (sq_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
  have hnum : 4 * D ≤ 16 * C * A := by
    dsimp only [A]
    nlinarith
  calc
    4 * D / (onePointTarget k * C) ^ 2 ≤
        (16 * C * A) / (onePointTarget k * C) ^ 2 :=
      div_le_div_of_nonneg_right hnum (sq_nonneg _)
    _ = (16 * A) / (onePointTarget k ^ 2 * C) := by
      field_simp [ne_of_gt hp, ne_of_gt hCpos]
      <;> ring
    _ ≤ (16 * A) /
        (onePointTarget k ^ 2 * (targetSize k : ℝ)) := by
      have hden : onePointTarget k ^ 2 * (targetSize k : ℝ) ≤
          onePointTarget k ^ 2 * C :=
        mul_le_mul_of_nonneg_left hC (sq_nonneg _)
      exact div_le_div_of_nonneg_left
        (mul_nonneg (by norm_num) hA)
        (mul_pos (sq_pos_of_pos hp) hT) hden
    _ = correlatedPairFailureBound k := by
      simp only [correlatedPairFailureBound, A]
      ring

lemma summable_total_pairFailureBound :
    Summable (fun k : ℕ ↦
      offCorrelationFailureBound k + correlatedPairFailureBound k) :=
  summable_offCorrelationFailureBound.add summable_correlatedPairFailureBound

lemma summable_transitionFailureBound {N0 : ℕ} (hN0 : 0 < N0) :
    Summable (transitionFailureBound N0) := by
  exact summable_scale_rpow_neg hN0 (by norm_num)

end BranchParameterArithmetic
end Erdos527

namespace Erdos527
namespace BranchParameterArithmetic

/-- The analytic part of the transition failure, before auxiliary grid
exceptions are added. -/
noncomputable def pairFailureBound (k : ℕ) : ℝ :=
  offCorrelationFailureBound k + correlatedPairFailureBound k

lemma pairFailureBound_nonneg (k : ℕ) : 0 ≤ pairFailureBound k := by
  exact add_nonneg (offCorrelationFailureBound_nonneg k)
    (correlatedPairFailureBound_nonneg k)

lemma summable_pairFailureBound : Summable pairFailureBound := by
  exact summable_offCorrelationFailureBound.add
    summable_correlatedPairFailureBound

/-- Single real majorant for all analytic branching errors and the two
auxiliary finite-grid errors at absolute scale `k`. -/
noncomputable def analyticFailureBound
    (a : ℕ → ℝ) (N0 k : ℕ) : ℝ :=
  offCorrelationFailureBound k + correlatedPairFailureBound k +
    FailureMeasurability.combinedFailureBound a N0 k

lemma analyticFailureBound_nonneg
    (a : ℕ → ℝ) (N0 k : ℕ) :
    0 ≤ analyticFailureBound a N0 k := by
  exact add_nonneg
    (add_nonneg (offCorrelationFailureBound_nonneg k)
      (correlatedPairFailureBound_nonneg k))
    (FailureMeasurability.combinedFailureBound_nonneg a N0 k)

lemma summable_analyticFailureBound
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) :
    Summable (analyticFailureBound a N0) := by
  change Summable (fun k ↦ pairFailureBound k +
    FailureMeasurability.combinedFailureBound a N0 k)
  exact summable_pairFailureBound.add
    (FailureMeasurability.summable_combinedFailureBound a hsmall hN0)

/-- The shifted ENNReal tail of the complete analytic majorant tends to zero.
The statement uses `start + t`, matching the absolute-scale convention in the
recursive probability assembly. -/
lemma ofReal_analyticFailureTail_tendsto_zero
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) :
    Tendsto (fun start : ℕ ↦ ∑' t : ℕ,
        ENNReal.ofReal (analyticFailureBound a N0 (start + t)))
      atTop (nhds 0) := by
  have htail : Tendsto (fun start : ℕ ↦ ∑' t : ℕ,
      ENNReal.ofReal (analyticFailureBound a N0 (t + start)))
      atTop (nhds 0) := by
    exact ENNReal.tendsto_sum_nat_add
      (fun k ↦ ENNReal.ofReal (analyticFailureBound a N0 k))
      (summable_analyticFailureBound a hsmall hN0).tsum_ofReal_ne_top
  simpa only [Nat.add_comm] using htail

lemma ofReal_analyticFailureBound_eq_split
    (a : ℕ → ℝ) (N0 k : ℕ) :
    ENNReal.ofReal (analyticFailureBound a N0 k) =
      ENNReal.ofReal (pairFailureBound k) +
        ENNReal.ofReal (FailureMeasurability.combinedFailureBound a N0 k) := by
  change ENNReal.ofReal (pairFailureBound k +
      FailureMeasurability.combinedFailureBound a N0 k) = _
  exact ENNReal.ofReal_add (pairFailureBound_nonneg k)
    (FailureMeasurability.combinedFailureBound_nonneg a N0 k)

/-- Split form tailored to `FinalProbabilityAssembly`, whose transition and
grid bounds are supplied as separate functions `b` and `c`. -/
lemma splitFailureTail_tendsto_zero
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) :
    Tendsto (fun start : ℕ ↦ ∑' t : ℕ,
        (ENNReal.ofReal (pairFailureBound (start + t)) +
          ENNReal.ofReal
            (FailureMeasurability.combinedFailureBound a N0 (start + t))))
      atTop (nhds 0) := by
  have heq :
      (fun start : ℕ ↦ ∑' t : ℕ,
        (ENNReal.ofReal (pairFailureBound (start + t)) +
          ENNReal.ofReal
            (FailureMeasurability.combinedFailureBound a N0 (start + t)))) =
      (fun start : ℕ ↦ ∑' t : ℕ,
        ENNReal.ofReal (analyticFailureBound a N0 (start + t))) := by
    funext start
    apply tsum_congr
    intro t
    exact (ofReal_analyticFailureBound_eq_split a N0 (start + t)).symm
  rw [heq]
  exact ofReal_analyticFailureTail_tendsto_zero a hsmall hN0

end BranchParameterArithmetic
end Erdos527

open scoped BigOperators ENNReal NNReal ProbabilityTheory Topology

namespace Erdos527

open Filter MeasureTheory ProbabilityTheory

namespace RecursiveAlive

noncomputable section

/-- A scale-local predicate, evaluated only on the restriction of the signs to
the scale currently being exposed. -/
abbrev LocalGood (N0 : ℕ) :=
  (k : ℕ) → ℂ →
    (Fin (scale N0 (k + 1) - scale N0 k) → ℝ) → Prop

/-- Root grid with positivity evidence packaged, so clients do not need to
thread `NeZero (scale N0 k)` typeclass arguments through recursive statements. -/
noncomputable def rootGrid (N0 : ℕ) (hN0 : 0 < N0) (k : ℕ) : Finset ℂ := by
  letI : NeZero (scale N0 k) := ⟨scale_ne_zero hN0.ne' k⟩
  exact Grid.complexRootGrid (scale N0 k)

/-- Retained children with all positivity instances packaged. -/
noncomputable def scaleChildren (N0 : ℕ) (hN0 : 0 < N0) (k : ℕ)
    (A : Finset ℂ) : Finset ℂ := by
  letI : NeZero N0 := ⟨hN0.ne'⟩
  letI : NeZero (scale N0 k) := ⟨scale_ne_zero hN0.ne' k⟩
  exact Grid.scaleChildRootUnion N0 k A

noncomputable def filterGood {N0 : ℕ} (good : LocalGood N0) (k : ℕ)
    (x : Fin (scale N0 (k + 1) - scale N0 k) → ℝ) (A : Finset ℂ) : Finset ℂ := by
  classical
  exact A.filter (fun z => good k z x)

@[simp] lemma mem_filterGood {N0 : ℕ} (good : LocalGood N0) (k : ℕ)
    (x : Fin (scale N0 (k + 1) - scale N0 k) → ℝ) (A : Finset ℂ) (z : ℂ) :
    z ∈ filterGood good k x A ↔ z ∈ A ∧ good k z x := by
  classical
  simp [filterGood]

lemma filterGood_subset {N0 : ℕ} (good : LocalGood N0) (k : ℕ)
    (x : Fin (scale N0 (k + 1) - scale N0 k) → ℝ) (A : Finset ℂ) :
    filterGood good k x A ⊆ A := by
  classical
  exact Finset.filter_subset _ _

lemma scaleChildren_subset_rootGrid_succ (N0 : ℕ) (hN0 : 0 < N0)
    (k : ℕ) (A : Finset ℂ) :
    scaleChildren N0 hN0 k A ⊆ rootGrid N0 hN0 (k + 1) := by
  letI : NeZero N0 := ⟨hN0.ne'⟩
  letI : NeZero (scale N0 k) := ⟨scale_ne_zero hN0.ne' k⟩
  simpa only [scaleChildren, rootGrid, scale_succ] using
    Grid.scaleChildRootUnion_subset_grid N0 k A

/-- The alive construction, indexed by the number of generations after a
reset at `start`.  Generation zero is the full root grid at scale `start`;
the successor generation filters the prescribed children using only the new
scale restriction. -/
noncomputable def aliveRel (N0 : ℕ) (hN0 : 0 < N0) (start : ℕ)
    (good : LocalGood N0) : ℕ → (ℕ → ℝ) → Finset ℂ
  | 0, _ => by
      exact rootGrid N0 hN0 start
  | t + 1, ε => by
      classical
      let k := start + t
      exact filterGood good k (FlatVectorAPI.scaleRestriction ε N0 k)
        (scaleChildren N0 hN0 k (aliveRel N0 hN0 start good t ε))

@[simp] lemma aliveRel_zero (N0 : ℕ) (hN0 : 0 < N0) (start : ℕ)
    (good : LocalGood N0) (ε : ℕ → ℝ) :
    aliveRel N0 hN0 start good 0 ε =
      rootGrid N0 hN0 start := by
  simp [aliveRel]

@[simp] lemma aliveRel_succ (N0 : ℕ) (hN0 : 0 < N0) (start t : ℕ)
    (good : LocalGood N0) (ε : ℕ → ℝ) :
    aliveRel N0 hN0 start good (t + 1) ε =
      filterGood good (start + t)
        (FlatVectorAPI.scaleRestriction ε N0 (start + t))
        (scaleChildren N0 hN0 (start + t)
          (aliveRel N0 hN0 start good t ε)) := by
  simp [aliveRel]

/-- Every recursive alive set lies in the exact complex-root grid for its
generation. -/
theorem aliveRel_subset_grid (N0 : ℕ) (hN0 : 0 < N0) (start : ℕ)
    (good : LocalGood N0) (t : ℕ) (ε : ℕ → ℝ) :
    aliveRel N0 hN0 start good t ε ⊆
      rootGrid N0 hN0 (start + t) := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [aliveRel_succ]
      refine (filterGood_subset _ _ _ _).trans ?_
      simpa only [Nat.add_assoc] using
        scaleChildren_subset_rootGrid_succ N0 hN0 (start + t)
          (aliveRel N0 hN0 start good t ε)

/-- Before the local-good filter is applied, the candidate family has exactly
the branching-factor multiple of the parent cardinality. -/
theorem card_aliveRel_candidates (N0 : ℕ) (hN0 : 0 < N0) (start t : ℕ)
    (good : LocalGood N0) (ε : ℕ → ℝ) :
    (scaleChildren N0 hN0 (start + t)
      (aliveRel N0 hN0 start good t ε)).card =
      (aliveRel N0 hN0 start good t ε).card *
        (2 ^ stepExponent (start + t) / (start + t + 2) ^ 20) := by
  letI : NeZero N0 := ⟨hN0.ne'⟩
  letI : NeZero (scale N0 (start + t)) :=
    ⟨scale_ne_zero hN0.ne' (start + t)⟩
  simp only [scaleChildren]
  exact Grid.card_scaleChildRootUnion N0 (start + t)
    (by simpa [rootGrid] using aliveRel_subset_grid N0 hN0 start good t ε)

/-- Every surviving child has a surviving parent and its thickened root ball
is contained in the parent's thickened root ball. -/
theorem exists_aliveRel_parent_with_nesting_of_mem (N0 : ℕ) (hN0 : 0 < N0)
    (start t : ℕ) (good : LocalGood N0) (ε : ℕ → ℝ) {z : ℂ}
    (hz : z ∈ aliveRel N0 hN0 start good (t + 1) ε) :
    ∃ w ∈ aliveRel N0 hN0 start good t ε,
      ‖z - w‖ +
          Grid.branchRootRadius (scale N0 (start + t + 1)) (start + t + 1) ≤
        Grid.branchRootRadius (scale N0 (start + t)) (start + t) ∧
      Metric.closedBall z
          (Grid.branchRootRadius (scale N0 (start + t + 1)) (start + t + 1)) ⊆
        Metric.closedBall w
          (Grid.branchRootRadius (scale N0 (start + t)) (start + t)) := by
  rw [aliveRel_succ, mem_filterGood] at hz
  unfold scaleChildren at hz
  letI : NeZero N0 := ⟨hN0.ne'⟩
  letI : NeZero (scale N0 (start + t)) :=
    ⟨scale_ne_zero hN0.ne' (start + t)⟩
  obtain ⟨p, hp, hdist, hball⟩ :=
    Grid.exists_scale_parent_with_nesting_of_mem N0 (start + t) hz.1
  refine ⟨Grid.complexGridPoint (scale N0 (start + t)) p, hp, ?_, ?_⟩
  · rw [← scale_succ] at hdist
    simpa only [Nat.add_assoc] using hdist
  · rw [← scale_succ] at hball
    simpa only [Nat.add_assoc] using hball

/-- Alive generation `t` depends only on the local restrictions of the first
`t` exposed scales. -/
theorem aliveRel_eq_of_restrictions_eq (N0 : ℕ) (hN0 : 0 < N0)
    (start : ℕ) (good : LocalGood N0) {ε ε' : ℕ → ℝ} {t : ℕ}
    (h : ∀ j < t,
      FlatVectorAPI.scaleRestriction ε N0 (start + j) =
        FlatVectorAPI.scaleRestriction ε' N0 (start + j)) :
    aliveRel N0 hN0 start good t ε = aliveRel N0 hN0 start good t ε' := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [aliveRel_succ, aliveRel_succ]
      have hprev : aliveRel N0 hN0 start good t ε =
          aliveRel N0 hN0 start good t ε' :=
        ih fun j hj => h j (by omega)
      have hnew := h t (Nat.lt_succ_self t)
      rw [hprev, hnew]

/-- Coordinate-level finite dependence of the recursive alive set. -/
theorem aliveRel_eq_of_eq_on_scale_interval (N0 : ℕ) (hN0 : 0 < N0)
    (start : ℕ) (good : LocalGood N0) {ε ε' : ℕ → ℝ} {t : ℕ}
    (h : ∀ n ∈ Finset.Ico (scale N0 start) (scale N0 (start + t)),
      ε n = ε' n) :
    aliveRel N0 hN0 start good t ε = aliveRel N0 hN0 start good t ε' := by
  apply aliveRel_eq_of_restrictions_eq N0 hN0 start good
  intro j hj
  funext i
  apply h
  simp only [Finset.mem_Ico, FlatVectorAPI.scaleRestriction,
    FlatVectorAPI.scaleCoefficient]
  constructor
  · exact le_trans (scale_monotone N0 (Nat.le_add_right start j))
      (Nat.le_add_right _ i.val)
  · have hij : start + j + 1 ≤ start + t := by omega
    have hi : scale N0 (start + j) + i.val < scale N0 (start + j + 1) := by
      have := i.isLt
      omega
    exact lt_of_lt_of_le hi (scale_monotone N0 hij)

lemma parentIndices_image_complexGridPoint (q : ℕ) [NeZero q]
    (B : Finset (ZMod q)) :
    Grid.parentIndices q (B.image (Grid.complexGridPoint q)) = B := by
  ext p
  rw [Grid.mem_parentIndices_iff]
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨a, ha, hap⟩
    exact (Grid.complexGridPoint_injective q hap) ▸ ha
  · intro hp
    exact ⟨p, hp, rfl⟩

noncomputable def indexToRoot (N0 : ℕ) (hN0 : 0 < N0) (k : ℕ) :
    ZMod (scale N0 k) → ℂ := by
  letI : NeZero (scale N0 k) := ⟨scale_ne_zero hN0.ne' k⟩
  exact Grid.complexGridPoint (scale N0 k)

/-- Finite index code of an alive set.  Unlike `Finset ℂ`, this is a genuinely
finite measurable state space. -/
noncomputable def aliveCode (N0 : ℕ) (hN0 : 0 < N0) (start : ℕ)
    (good : LocalGood N0) (t : ℕ) (ε : ℕ → ℝ) :
    Finset (ZMod (scale N0 (start + t))) := by
  letI : NeZero (scale N0 (start + t)) :=
    ⟨scale_ne_zero hN0.ne' (start + t)⟩
  exact Grid.parentIndices (scale N0 (start + t))
    (aliveRel N0 hN0 start good t ε)

lemma aliveCode_image (N0 : ℕ) (hN0 : 0 < N0) (start : ℕ)
    (good : LocalGood N0) (t : ℕ) (ε : ℕ → ℝ) :
    (aliveCode N0 hN0 start good t ε).image
        (indexToRoot N0 hN0 (start + t)) =
      aliveRel N0 hN0 start good t ε := by
  letI : NeZero (scale N0 (start + t)) :=
    ⟨scale_ne_zero hN0.ne' (start + t)⟩
  simpa only [indexToRoot, aliveCode] using Grid.image_parentIndices_eq _
    (by simpa [rootGrid] using aliveRel_subset_grid N0 hN0 start good t ε)

/-- Measurability assumption on a scale-local good predicate. -/
def LocalGoodMeasurable {N0 : ℕ} (good : LocalGood N0) : Prop :=
  ∀ k z, MeasurableSet {x | good k z x}

/-- Membership of a fixed phase in a recursive alive generation is measurable.
This is the useful measurable finite-state assertion; it avoids imposing an
artificial discrete measurable structure on `Finset ℂ`. -/
theorem measurableSet_mem_aliveRel {N0 : ℕ} (hN0 : 0 < N0) (start : ℕ)
    {good : LocalGood N0} (hgood : LocalGoodMeasurable good)
    (t : ℕ) (z : ℂ) :
    MeasurableSet {ε : ℕ → ℝ | z ∈ aliveRel N0 hN0 start good t ε} := by
  induction t generalizing z with
  | zero =>
      by_cases hz : z ∈ rootGrid N0 hN0 start
      · simpa [hz]
      · simpa [hz]
  | succ t ih =>
      let k := start + t
      have hcand : MeasurableSet {ε : ℕ → ℝ |
          z ∈ scaleChildren N0 hN0 k
            (aliveRel N0 hN0 start good t ε)} := by
        unfold scaleChildren
        letI : NeZero N0 := ⟨hN0.ne'⟩
        letI : NeZero (scale N0 k) := ⟨scale_ne_zero hN0.ne' k⟩
        rw [show {ε : ℕ → ℝ |
            z ∈ Grid.scaleChildRootUnion N0 k
              (aliveRel N0 hN0 start good t ε)} =
            ⋃ p : ZMod (scale N0 k),
              {ε | Grid.complexGridPoint (scale N0 k) p ∈
                  aliveRel N0 hN0 start good t ε ∧
                z ∈ Grid.nearChildRoots (scale N0 k) (2 ^ stepExponent k)
                  (Grid.branchChildDenom k) p} by
          ext ε
          simp only [Set.mem_setOf_eq, Set.mem_iUnion]
          exact Grid.mem_childRootUnion_iff _ _ _ _ _]
        apply MeasurableSet.iUnion
        intro p
        by_cases hzp : z ∈ Grid.nearChildRoots (scale N0 k)
            (2 ^ stepExponent k) (Grid.branchChildDenom k) p
        · simpa only [hzp, and_true] using
            ih (Grid.complexGridPoint (scale N0 k) p)
        · simp only [hzp, and_false, Set.setOf_false]
          exact MeasurableSet.empty
      have hlocal : MeasurableSet {ε : ℕ → ℝ |
          good k z (FlatVectorAPI.scaleRestriction ε N0 k)} :=
        (hgood k z).preimage (FlatVectorAPI.measurable_scaleRestriction N0 k)
      rw [show {ε : ℕ → ℝ | z ∈ aliveRel N0 hN0 start good (t + 1) ε} =
          {ε | z ∈ scaleChildren N0 hN0 k
              (aliveRel N0 hN0 start good t ε)} ∩
            {ε | good k z (FlatVectorAPI.scaleRestriction ε N0 k)} by
        ext ε
        simp only [aliveRel_succ, mem_filterGood, Set.mem_setOf_eq,
          Set.mem_inter_iff, k]]
      exact hcand.inter hlocal

/-- Equality to a fixed finite alive set is measurable. -/
theorem measurableSet_aliveRel_eq {N0 : ℕ} (hN0 : 0 < N0) (start : ℕ)
    {good : LocalGood N0} (hgood : LocalGoodMeasurable good)
    (t : ℕ) (A : Finset ℂ) :
    MeasurableSet {ε : ℕ → ℝ | aliveRel N0 hN0 start good t ε = A} := by
  let G := rootGrid N0 hN0 (start + t)
  by_cases hA : A ⊆ G
  · rw [show {ε : ℕ → ℝ | aliveRel N0 hN0 start good t ε = A} =
        ⋂ z ∈ G, if z ∈ A then
          {ε | z ∈ aliveRel N0 hN0 start good t ε}
        else {ε | z ∉ aliveRel N0 hN0 start good t ε} by
      ext ε
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro heq z hzG
        subst A
        split_ifs <;> simp_all
      · intro hz
        apply Finset.Subset.antisymm
        · intro z hzlive
          have := hz z (aliveRel_subset_grid N0 hN0 start good t ε hzlive)
          split_ifs at this with hzin
          · exact hzin
          · exact False.elim (this hzlive)
        · intro z hzA
          have := hz z (hA hzA)
          simp only [hzA, ↓reduceIte, Set.mem_setOf_eq] at this
          exact this]
    apply MeasurableSet.biInter G.finite_toSet.to_countable
    intro z hzG
    split_ifs
    · exact measurableSet_mem_aliveRel hN0 start hgood t z
    · exact (measurableSet_mem_aliveRel hN0 start hgood t z).compl
  · have hempty : {ε : ℕ → ℝ | aliveRel N0 hN0 start good t ε = A} = ∅ := by
      ext ε
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro heq
      apply hA
      rw [← heq]
      exact aliveRel_subset_grid N0 hN0 start good t ε
    rw [hempty]
    exact MeasurableSet.empty

lemma indexToRoot_injective (N0 : ℕ) (hN0 : 0 < N0) (k : ℕ) :
    Function.Injective (indexToRoot N0 hN0 k) := by
  letI : NeZero (scale N0 k) := ⟨scale_ne_zero hN0.ne' k⟩
  exact Grid.complexGridPoint_injective _

theorem measurableSet_aliveCode_eq {N0 : ℕ} (hN0 : 0 < N0) (start : ℕ)
    {good : LocalGood N0} (hgood : LocalGoodMeasurable good) (t : ℕ)
    (B : Finset (ZMod (scale N0 (start + t)))) :
    MeasurableSet {ε : ℕ → ℝ | aliveCode N0 hN0 start good t ε = B} := by
  rw [show {ε : ℕ → ℝ | aliveCode N0 hN0 start good t ε = B} =
      {ε | aliveRel N0 hN0 start good t ε =
        B.image (indexToRoot N0 hN0 (start + t))} by
    ext ε
    simp only [Set.mem_setOf_eq]
    constructor
    · intro heq
      rw [← aliveCode_image N0 hN0 start good t ε, heq]
    · intro heq
      apply Finset.image_injective (indexToRoot_injective N0 hN0 (start + t))
      rw [aliveCode_image N0 hN0 start good t ε, heq]]
  exact measurableSet_aliveRel_eq hN0 start hgood t _

theorem measurable_aliveCode {N0 : ℕ} (hN0 : 0 < N0) (start : ℕ)
    {good : LocalGood N0} (hgood : LocalGoodMeasurable good) (t : ℕ) :
    Measurable (aliveCode N0 hN0 start good t) := by
  rw [measurable_finset_iff]
  intro p
  rw [← measurableSet_setOfPred]
  letI : NeZero (scale N0 (start + t)) :=
    ⟨scale_ne_zero hN0.ne' (start + t)⟩
  simpa only [aliveCode, Grid.mem_parentIndices_iff] using
    measurableSet_mem_aliveRel hN0 start hgood t
      (Grid.complexGridPoint (scale N0 (start + t)) p)

/-- Coordinates exposed before generation `t`. -/
def pastCoordinateSet (N0 start t : ℕ) : Finset ℕ :=
  Finset.Ico (scale N0 start) (scale N0 (start + t))

/-- Canonical zero extension of a finite past-coordinate vector. -/
def extendPast (N0 start t : ℕ)
    (x : pastCoordinateSet N0 start t → ℝ) : ℕ → ℝ :=
  fun n => if hn : n ∈ pastCoordinateSet N0 start t then x ⟨n, hn⟩ else 0

lemma measurable_extendPast (N0 start t : ℕ) :
    Measurable (extendPast N0 start t) := by
  apply measurable_pi_lambda
  intro n
  by_cases hn : n ∈ pastCoordinateSet N0 start t
  · simpa [extendPast, hn] using
      (measurable_pi_apply (⟨n, hn⟩ : pastCoordinateSet N0 start t))
  · simp [extendPast, hn]

noncomputable def pastAliveCode (N0 : ℕ) (hN0 : 0 < N0) (start : ℕ)
    (good : LocalGood N0) (t : ℕ)
    (x : pastCoordinateSet N0 start t → ℝ) :
    Finset (ZMod (scale N0 (start + t))) :=
  aliveCode N0 hN0 start good t (extendPast N0 start t x)

theorem aliveCode_factor_past (N0 : ℕ) (hN0 : 0 < N0) (start : ℕ)
    (good : LocalGood N0) (t : ℕ) (ε : ℕ → ℝ) :
    pastAliveCode N0 hN0 start good t
        (restrictCoords (pastCoordinateSet N0 start t) ε) =
      aliveCode N0 hN0 start good t ε := by
  unfold pastAliveCode aliveCode
  congr 1
  apply aliveRel_eq_of_eq_on_scale_interval N0 hN0 start good
  intro n hn
  simp [extendPast, pastCoordinateSet, restrictCoords, hn]

theorem measurable_pastAliveCode {N0 : ℕ} (hN0 : 0 < N0) (start : ℕ)
    {good : LocalGood N0} (hgood : LocalGoodMeasurable good) (t : ℕ) :
    Measurable (pastAliveCode N0 hN0 start good t) := by
  exact (measurable_aliveCode hN0 start hgood t).comp
    (measurable_extendPast N0 start t)

lemma disjoint_pastCoordinateSet_scaleCoordinateSet {N0 : ℕ} (hN0 : 0 < N0)
    (start t : ℕ) :
    Disjoint (pastCoordinateSet N0 start t)
      (FlatVectorAPI.scaleCoordinateSet N0 (start + t)) := by
  rw [Finset.disjoint_left]
  intro n hn hnfresh
  simp only [pastCoordinateSet, FlatVectorAPI.scaleCoordinateSet,
    Finset.mem_Ico] at hn hnfresh
  omega

/-- The actual alive state is independent of the fresh scale restriction.  It
factors through all earlier coordinates, which are disjoint from the current
scale coordinate set. -/
theorem indepFun_aliveCode_scaleRestriction {N0 : ℕ} (hN0 : 0 < N0)
    (start : ℕ) {good : LocalGood N0} (hgood : LocalGoodMeasurable good)
    (t : ℕ) :
    IndepFun (aliveCode N0 hN0 start good t)
      (fun ε : ℕ → ℝ =>
        FlatVectorAPI.scaleRestriction ε N0 (start + t))
      rademacherProductMeasure := by
  let S := pastCoordinateSet N0 start t
  let T := FlatVectorAPI.scaleCoordinateSet N0 (start + t)
  have hbase : IndepFun (restrictCoords S) (restrictCoords T)
      rademacherProductMeasure :=
    indepFun_restrictCoords_of_disjoint
      (disjoint_pastCoordinateSet_scaleCoordinateSet hN0 start t)
  have hcomp := hbase.comp (measurable_pastAliveCode hN0 start hgood t)
    (FlatVectorAPI.measurable_scaleSubtypeRestriction N0 (start + t))
  have hpast : pastAliveCode N0 hN0 start good t ∘ restrictCoords S =
      aliveCode N0 hN0 start good t := by
    funext ε
    exact aliveCode_factor_past N0 hN0 start good t ε
  have hfresh : FlatVectorAPI.scaleSubtypeRestriction N0 (start + t) ∘
      restrictCoords T = fun ε : ℕ → ℝ =>
        FlatVectorAPI.scaleRestriction ε N0 (start + t) := by
    rfl
  rwa [hpast, hfresh] at hcomp

/-- A generic transition-failure predicate on the finite parent and the newly
exposed scale coordinates. -/
abbrev LocalFailure (N0 : ℕ) :=
  (k : ℕ) → Finset ℂ →
    (Fin (scale N0 (k + 1) - scale N0 k) → ℝ) → Prop

def LocalFailureMeasurable {N0 : ℕ} (bad : LocalFailure N0) : Prop :=
  ∀ k A, MeasurableSet {x | bad k A x}

def transitionFailure {N0 : ℕ} (hN0 : 0 < N0) (start : ℕ)
    (good : LocalGood N0) (bad : LocalFailure N0) (t : ℕ) : Set (ℕ → ℝ) :=
  {ε | bad (start + t) (aliveRel N0 hN0 start good t ε)
    (FlatVectorAPI.scaleRestriction ε N0 (start + t))}

/-- A transition failure is measurable: split into the finitely many possible
parent subsets, then use the local measurability on the fresh scale. -/
theorem measurableSet_transitionFailure {N0 : ℕ} (hN0 : 0 < N0)
    (start : ℕ) {good : LocalGood N0} (hgood : LocalGoodMeasurable good)
    {bad : LocalFailure N0} (hbad : LocalFailureMeasurable bad) (t : ℕ) :
    MeasurableSet (transitionFailure hN0 start good bad t) := by
  let G := rootGrid N0 hN0 (start + t)
  rw [show transitionFailure hN0 start good bad t =
      ⋃ A ∈ G.powerset,
        {ε | aliveRel N0 hN0 start good t ε = A} ∩
          {ε | bad (start + t) A
            (FlatVectorAPI.scaleRestriction ε N0 (start + t))} by
    ext ε
    simp only [transitionFailure, Set.mem_setOf_eq, Set.mem_iUnion,
      Set.mem_inter_iff, Finset.mem_powerset]
    constructor
    · intro hb
      exact ⟨aliveRel N0 hN0 start good t ε,
        aliveRel_subset_grid N0 hN0 start good t ε, rfl, hb⟩
    · rintro ⟨A, hAG, heq, hb⟩
      simpa only [heq] using hb]
  apply MeasurableSet.biUnion (G.powerset.finite_toSet.to_countable)
  intro A hA
  exact (measurableSet_aliveRel_eq hN0 start hgood t A).inter
    ((hbad (start + t) A).preimage
      (FlatVectorAPI.measurable_scaleRestriction N0 (start + t)))

/-- Abstract finite-state conditioning.  The fresh vector `X` is independent
of a finite past state.  If every deterministic state has transition-failure
probability at most `b`, then the adaptive transition has the same bound. -/
theorem measure_adaptive_failure_le_of_indepPast
    {Ω Past Fresh : Type*} [MeasurableSpace Ω] [MeasurableSpace Past]
    [MeasurableSpace Fresh] [Fintype Past] [MeasurableSingletonClass Past]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (past : Ω → Past) (X : Ω → Fresh) (bad : Past → Fresh → Prop)
    (hpast : Measurable past) (hX : Measurable X)
    (hindep : IndepFun past X P)
    (hbad : ∀ s, MeasurableSet {x | bad s x}) (b : ℝ≥0∞)
    (hfixed : ∀ s, P (X ⁻¹' {x | bad s x}) ≤ b) :
    P {ω | bad (past ω) (X ω)} ≤ b := by
  let E : Past → Set Ω := fun s =>
    (past ⁻¹' ({s} : Set Past)) ∩ (X ⁻¹' {x | bad s x})
  have hEmeas : ∀ s, MeasurableSet (E s) := fun s =>
    ((MeasurableSet.singleton s).preimage hpast).inter
      ((hbad s).preimage hX)
  have hdisj : ((Finset.univ : Finset Past) : Set Past).PairwiseDisjoint E := by
    intro s hs s' hs' hne
    change Disjoint (E s) (E s')
    rw [Set.disjoint_left]
    intro ω hω hω'
    have hsval : past ω = s := by simpa [E] using hω.1
    have hsval' : past ω = s' := by simpa [E] using hω'.1
    exact hne (hsval.symm.trans hsval')
  have hunion : {ω | bad (past ω) (X ω)} = ⋃ s ∈ (Finset.univ : Finset Past), E s := by
    ext ω
    simp [E]
  rw [hunion, measure_biUnion_finset hdisj (fun s _ => hEmeas s)]
  calc
    (∑ s ∈ (Finset.univ : Finset Past), P (E s)) =
        ∑ s : Past, P (past ⁻¹' ({s} : Set Past)) *
          P (X ⁻¹' {x | bad s x}) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact hindep.measure_inter_preimage_eq_mul _ _
        (MeasurableSet.singleton s) (hbad s)
    _ ≤ ∑ s : Past, P (past ⁻¹' ({s} : Set Past)) * b := by
      apply Finset.sum_le_sum
      intro s hs
      exact mul_le_mul_right (hfixed s) _
    _ = (∑ s : Past, P (past ⁻¹' ({s} : Set Past))) * b := by
      rw [Finset.sum_mul]
    _ = b := by
      have hfibdisj : ((Finset.univ : Finset Past) : Set Past).PairwiseDisjoint
          (fun s => past ⁻¹' ({s} : Set Past)) := by
        intro s hs s' hs' hne
        change Disjoint (past ⁻¹' ({s} : Set Past)) (past ⁻¹' ({s'} : Set Past))
        rw [Set.disjoint_left]
        intro ω hω hω'
        have heq : s = s' := by
          have hs : past ω = s := by simpa using hω
          have hs' : past ω = s' := by simpa using hω'
          exact hs.symm.trans hs'
        exact hne heq
      have hfibunion : (⋃ s ∈ (Finset.univ : Finset Past),
          past ⁻¹' ({s} : Set Past)) = Set.univ := by
        ext ω
        simp
      have hsum : (∑ s : Past, P (past ⁻¹' ({s} : Set Past))) = 1 := by
        rw [← measure_biUnion_finset hfibdisj
          (fun s _ => (MeasurableSet.singleton s).preimage hpast), hfibunion,
          measure_univ]
      rw [hsum, one_mul]

/-- Concrete adaptive transition bound for the recursive alive process.  A
fixed-parent estimate under the finite Rademacher scale law transfers exactly
to the infinite product, and independence of `aliveCode` removes the adaptive
choice of the parent. -/
theorem measure_recursive_adaptive_failure_le
    {N0 : ℕ} (hN0 : 0 < N0) (start : ℕ)
    {good : LocalGood N0} (hgood : LocalGoodMeasurable good) (t : ℕ)
    (bad : Finset ℂ →
      (Fin (scale N0 (start + t + 1) - scale N0 (start + t)) → ℝ) → Prop)
    (hbad : ∀ A, A ⊆ rootGrid N0 hN0 (start + t) →
      MeasurableSet {x | bad A x})
    (b : ℝ≥0∞)
    (hfixed : ∀ A, (hA : A ⊆ rootGrid N0 hN0 (start + t)) →
      Erdos88.Invariance.rademacherProductMeasure
          (scale N0 (start + t + 1) - scale N0 (start + t))
          {x | bad A x} ≤ b) :
    rademacherProductMeasure {ε | bad (aliveRel N0 hN0 start good t ε)
      (FlatVectorAPI.scaleRestriction ε N0 (start + t))} ≤ b := by
  let decode : Finset (ZMod (scale N0 (start + t))) → Finset ℂ :=
    fun B => B.image (indexToRoot N0 hN0 (start + t))
  have hdecode : ∀ B, decode B ⊆ rootGrid N0 hN0 (start + t) := by
    intro B z hz
    simp only [decode, Finset.mem_image] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    unfold indexToRoot rootGrid
    letI : NeZero (scale N0 (start + t)) :=
      ⟨scale_ne_zero hN0.ne' (start + t)⟩
    simp [Grid.complexRootGrid]
  have hlocal_meas : ∀ B, MeasurableSet {x | bad (decode B) x} :=
    fun B => hbad (decode B) (hdecode B)
  have hlocal_bound : ∀ B,
      rademacherProductMeasure
        ((fun ε : ℕ → ℝ => FlatVectorAPI.scaleRestriction ε N0 (start + t)) ⁻¹'
          {x | bad (decode B) x}) ≤ b := by
    intro B
    rw [FlatVectorAPI.measure_preimage_scaleRestriction_rademacher N0 (start + t)
      (hlocal_meas B)]
    exact hfixed (decode B) (hdecode B)
  letI : NeZero (scale N0 (start + t)) :=
    ⟨scale_ne_zero hN0.ne' (start + t)⟩
  have h := measure_adaptive_failure_le_of_indepPast
    (P := rademacherProductMeasure)
    (aliveCode N0 hN0 start good t)
    (fun ε : ℕ → ℝ => FlatVectorAPI.scaleRestriction ε N0 (start + t))
    (fun B x => bad (decode B) x)
    (measurable_aliveCode hN0 start hgood t)
    (FlatVectorAPI.measurable_scaleRestriction N0 (start + t))
    (indepFun_aliveCode_scaleRestriction hN0 start hgood t)
    hlocal_meas b hlocal_bound
  rw [show {ε | bad (aliveRel N0 hN0 start good t ε)
      (FlatVectorAPI.scaleRestriction ε N0 (start + t))} =
      {ε | bad (decode (aliveCode N0 hN0 start good t ε))
        (FlatVectorAPI.scaleRestriction ε N0 (start + t))} by
    ext ε
    simp only [Set.mem_setOf_eq]
    rw [show decode (aliveCode N0 hN0 start good t ε) =
        aliveRel N0 hN0 start good t ε by
      exact aliveCode_image N0 hN0 start good t ε]]
  exact h

end

end RecursiveAlive

end Erdos527
open scoped BigOperators ENNReal NNReal ProbabilityTheory Topology

namespace Erdos527

open Filter MeasureTheory ProbabilityTheory

namespace FlatAliveGood

noncomputable section

open SmoothCutoffC4 CutoffLindebergBridge

/-- Reciprocal endpoint radius used by the smooth flat cutoff. -/
def flatEndpointScale (k : ℕ) : ℝ :=
  4 * (((k + 1 : ℕ) : ℝ) ^ 2)

/-- Reciprocal prefix radius used by the smooth flat cutoff. -/
noncomputable def flatPrefixScale (a : ℕ → ℝ) (N0 k : ℕ) : ℝ :=
  4 / Real.sqrt (coefficientEnvelope a N0 k)

/-- Smooth weight of a finite sign vector at one phase and one scale. -/
noncomputable def flatWeight (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0)
    (k : ℕ) (z : ℂ)
    (x : Fin (scale N0 (k + 1) - scale N0 k) → ℝ) : ℝ :=
  endpointPrefixCutoff (uniformBlockCount k) (flatEndpointScale k)
    (flatPrefixScale a N0 k)
    (NormedLindeberg.linearCombination
      (OnePointLindeberg.flatBlockIncrementDirection a hN0 k z) x)

/-- Hard local-good predicate: the smooth cutoff has nonzero weight. -/
def flatGood (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) :
    RecursiveAlive.LocalGood N0 :=
  fun k z x => flatWeight a hN0 k z x ≠ 0

def flatGoodSet (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0)
    (k : ℕ) (z : ℂ) :
    Set (Fin (scale N0 (k + 1) - scale N0 k) → ℝ) :=
  {x | flatGood a hN0 k z x}

/-- Evaluation on an infinite sign sequence uses exactly the finite restriction
to the current scale. -/
noncomputable def flatWeightAtSigns (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0)
    (k : ℕ) (z : ℂ) (ε : ℕ → ℝ) : ℝ :=
  flatWeight a hN0 k z (FlatVectorAPI.scaleRestriction ε N0 k)

lemma measurable_flatWeight (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0)
    (k : ℕ) (z : ℂ) :
    Measurable (flatWeight a hN0 k z) := by
  exact (endpointPrefixCutoff_contDiff (uniformBlockCount k)
      (flatEndpointScale k) (flatPrefixScale a N0 k)).continuous.measurable.comp
    (NormedLindeberg.measurable_linearCombination _)

lemma measurable_flatWeightAtSigns (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0)
    (k : ℕ) (z : ℂ) :
    Measurable (flatWeightAtSigns a hN0 k z) := by
  exact (measurable_flatWeight a hN0 k z).comp
    (FlatVectorAPI.measurable_scaleRestriction N0 k)

lemma flatWeight_nonneg (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0)
    (k : ℕ) (z : ℂ)
    (x : Fin (scale N0 (k + 1) - scale N0 k) → ℝ) :
    0 ≤ flatWeight a hN0 k z x := by
  exact endpointPrefixCutoff_nonneg (uniformBlockCount k)
    (flatEndpointScale k) (flatPrefixScale a N0 k) _

lemma flatWeight_le_one (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0)
    (k : ℕ) (z : ℂ)
    (x : Fin (scale N0 (k + 1) - scale N0 k) → ℝ) :
    flatWeight a hN0 k z x ≤ 1 := by
  exact endpointPrefixCutoff_le_one (uniformBlockCount k)
    (flatEndpointScale k) (flatPrefixScale a N0 k) _

lemma abs_flatWeight_le_one (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0)
    (k : ℕ) (z : ℂ)
    (x : Fin (scale N0 (k + 1) - scale N0 k) → ℝ) :
    |flatWeight a hN0 k z x| ≤ 1 := by
  rw [abs_of_nonneg (flatWeight_nonneg a hN0 k z x)]
  exact flatWeight_le_one a hN0 k z x

/-- The bounded smooth weight belongs to every `Lᵖ` under every finite measure. -/
lemma flatWeight_memLp (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0)
    (k : ℕ) (z : ℂ) (p : ℝ≥0∞)
    (P : Measure (Fin (scale N0 (k + 1) - scale N0 k) → ℝ))
    [IsFiniteMeasure P] :
    MemLp (flatWeight a hN0 k z) p P := by
  apply MemLp.of_bound (measurable_flatWeight a hN0 k z).aestronglyMeasurable 1
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs] using abs_flatWeight_le_one a hN0 k z x

lemma flatWeight_memLp_rademacher (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0)
    (k : ℕ) (z : ℂ) (p : ℝ≥0∞) :
    MemLp (flatWeight a hN0 k z) p
      (Erdos88.Invariance.rademacherProductMeasure
        (scale N0 (k + 1) - scale N0 k)) := by
  exact flatWeight_memLp a hN0 k z p _

theorem flatGood_measurable (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) :
    RecursiveAlive.LocalGoodMeasurable (flatGood a hN0) := by
  intro k z
  change MeasurableSet {x | flatWeight a hN0 k z x ≠ 0}
  rw [show {x | flatWeight a hN0 k z x ≠ 0} =
      {x | flatWeight a hN0 k z x = 0}ᶜ by ext x; simp]
  exact (measurableSet_eq_fun
    (measurable_flatWeight a hN0 k z) measurable_const).compl

lemma measurableSet_flatGoodSet (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0)
    (k : ℕ) (z : ℂ) :
    MeasurableSet (flatGoodSet a hN0 k z) :=
  flatGood_measurable a hN0 k z

/-- Indicator of the hard-good predicate, with classical decidability packaged. -/
noncomputable def flatGoodIndicator (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0)
    (k : ℕ) (z : ℂ)
    (x : Fin (scale N0 (k + 1) - scale N0 k) → ℝ) : ℝ := by
  classical
  exact if flatGood a hN0 k z x then 1 else 0

/-- The smooth weight is pointwise dominated by the indicator of its nonzero
hard-good set. -/
lemma flatWeight_le_indicator_good (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0)
    (k : ℕ) (z : ℂ)
    (x : Fin (scale N0 (k + 1) - scale N0 k) → ℝ) :
    flatWeight a hN0 k z x ≤ flatGoodIndicator a hN0 k z x := by
  classical
  by_cases hx : flatGood a hN0 k z x
  · simpa [flatGoodIndicator, hx] using flatWeight_le_one a hN0 k z x
  · have hzero : flatWeight a hN0 k z x = 0 := not_ne_iff.mp hx
    simp [flatGoodIndicator, hx, hzero]

lemma flatWeight_le_ite_good (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0)
    (k : ℕ) (z : ℂ)
    (x : Fin (scale N0 (k + 1) - scale N0 k) → ℝ) :
    flatWeight a hN0 k z x ≤
      @ite ℝ (flatGood a hN0 k z x) (Classical.propDecidable _) 1 0 := by
  simpa only [flatGoodIndicator] using flatWeight_le_indicator_good a hN0 k z x

/-- Nonzero cutoff support forces the complete scale endpoint into the inner
transport radius `1 / (2 (k+1)^2)`. -/
lemma endpoint_norm_lt_of_flatGood (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0)
    (k : ℕ) (z : ℂ)
    (x : Fin (scale N0 (k + 1) - scale N0 k) → ℝ)
    (hx : flatGood a hN0 k z x) :
    ‖∑ r, NormedLindeberg.linearCombination
        (OnePointLindeberg.flatBlockIncrementDirection a hN0 k z) x r‖ <
      1 / (2 * (((k + 1 : ℕ) : ℝ) ^ 2)) := by
  have hsupport := endpoint_norm_lt_two_of_endpointPrefixCutoff_ne_zero
    (uniformBlockCount k) (flatEndpointScale k) (flatPrefixScale a N0 k)
    (NormedLindeberg.linearCombination
      (OnePointLindeberg.flatBlockIncrementDirection a hN0 k z) x) hx
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (by simp [flatEndpointScale]; positivity)] at hsupport
  have hden : 0 < 2 * (((k + 1 : ℕ) : ℝ) ^ 2) := by positivity
  rw [lt_div_iff₀ hden]
  simp only [flatEndpointScale] at hsupport
  nlinarith

/-- Nonzero cutoff support forces every flat-block prefix into the inner
transport radius `sqrt(envelope)/2`. -/
lemma prefix_norm_lt_of_flatGood (a : ℕ → ℝ)
    {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) (z : ℂ)
    (x : Fin (scale N0 (k + 1) - scale N0 k) → ℝ)
    (hx : flatGood a hN0 k z x) (j : Fin (uniformBlockCount k)) :
    ‖∑ r ∈ Finset.Iic j,
        NormedLindeberg.linearCombination
          (OnePointLindeberg.flatBlockIncrementDirection a hN0 k z) x r‖ <
      Real.sqrt (coefficientEnvelope a N0 k) / 2 := by
  have hδ : 0 < coefficientEnvelope a N0 k := by
    have hk : 0 < Real.sqrt (((k + 1 : ℕ) : ℝ)) := by positivity
    exact (inv_pos.mpr hk).trans_le
      (inv_sqrt_succ_le_coefficientEnvelope a N0 k)
  have hsqrt : 0 < Real.sqrt (coefficientEnvelope a N0 k) :=
    Real.sqrt_pos.2 hδ
  have hsupport := prefix_norm_lt_two_of_endpointPrefixCutoff_ne_zero
    (uniformBlockCount k) (flatEndpointScale k) (flatPrefixScale a N0 k)
    (NormedLindeberg.linearCombination
      (OnePointLindeberg.flatBlockIncrementDirection a hN0 k z) x) hx j
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (by simp [flatPrefixScale]; positivity)] at hsupport
  have hquot :
      (4 * ‖∑ r ∈ Finset.Iic j,
        NormedLindeberg.linearCombination
          (OnePointLindeberg.flatBlockIncrementDirection a hN0 k z) x r‖) /
          Real.sqrt (coefficientEnvelope a N0 k) < 2 := by
    simpa only [flatPrefixScale, div_mul_eq_mul_div] using hsupport
  have hmul := (div_lt_iff₀ hsqrt).mp hquot
  nlinarith

/-- Recursive alive phases for the concrete flat cutoff predicate. -/
noncomputable def flatAlive (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0)
    (start t : ℕ) (ε : ℕ → ℝ) : Finset ℂ :=
  RecursiveAlive.aliveRel N0 hN0 start (flatGood a hN0) t ε

/-- Candidate children before the smooth local-good filter. -/
noncomputable def flatCandidates (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0)
    (start t : ℕ) (ε : ℕ → ℝ) : Finset ℂ :=
  RecursiveAlive.scaleChildren N0 hN0 (start + t)
    (flatAlive a hN0 start t ε)

/-- Good children obtained by applying the concrete scale-local cutoff. -/
noncomputable def flatGoodTransition (a : ℕ → ℝ) {N0 : ℕ}
    (hN0 : 0 < N0) (k : ℕ) (A : Finset ℂ)
    (x : Fin (scale N0 (k + 1) - scale N0 k) → ℝ) : Finset ℂ :=
  RecursiveAlive.filterGood (flatGood a hN0) k x
    (RecursiveAlive.scaleChildren N0 hN0 k A)

lemma flatAlive_succ (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0)
    (start t : ℕ) (ε : ℕ → ℝ) :
    flatAlive a hN0 start (t + 1) ε =
      flatGoodTransition a hN0 (start + t) (flatAlive a hN0 start t ε)
        (FlatVectorAPI.scaleRestriction ε N0 (start + t)) := by
  simp [flatAlive, flatGoodTransition, RecursiveAlive.aliveRel_succ]

lemma flatAlive_subset_grid (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0)
    (start t : ℕ) (ε : ℕ → ℝ) :
    flatAlive a hN0 start t ε ⊆
      RecursiveAlive.rootGrid N0 hN0 (start + t) :=
  RecursiveAlive.aliveRel_subset_grid N0 hN0 start (flatGood a hN0) t ε

lemma measurableSet_mem_flatAlive (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0)
    (start t : ℕ) (z : ℂ) :
    MeasurableSet {ε : ℕ → ℝ | z ∈ flatAlive a hN0 start t ε} :=
  RecursiveAlive.measurableSet_mem_aliveRel hN0 start
    (flatGood_measurable a hN0) t z

lemma card_flatCandidates (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0)
    (start t : ℕ) (ε : ℕ → ℝ) :
    (flatCandidates a hN0 start t ε).card =
      (flatAlive a hN0 start t ε).card *
        (2 ^ stepExponent (start + t) / (start + t + 2) ^ 20) :=
  RecursiveAlive.card_aliveRel_candidates N0 hN0 start t
    (flatGood a hN0) ε

lemma card_flatCandidateSet (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0)
    (k : ℕ) {A : Finset ℂ} (hA : A ⊆ RecursiveAlive.rootGrid N0 hN0 k) :
    (RecursiveAlive.scaleChildren N0 hN0 k A).card =
      A.card * (2 ^ stepExponent k / (k + 2) ^ 20) := by
  letI : NeZero N0 := ⟨hN0.ne'⟩
  letI : NeZero (scale N0 k) := ⟨scale_ne_zero hN0.ne' k⟩
  simpa only [RecursiveAlive.scaleChildren] using
    Grid.card_scaleChildRootUnion N0 k
      (by simpa [RecursiveAlive.rootGrid] using hA)

lemma flatGoodTransition_subset_candidates (a : ℕ → ℝ) {N0 : ℕ}
    (hN0 : 0 < N0) (k : ℕ) (A : Finset ℂ)
    (x : Fin (scale N0 (k + 1) - scale N0 k) → ℝ) :
    flatGoodTransition a hN0 k A x ⊆
      RecursiveAlive.scaleChildren N0 hN0 k A := by
  exact RecursiveAlive.filterGood_subset _ _ _ _

lemma flatGoodTransition_subset_grid (a : ℕ → ℝ) {N0 : ℕ}
    (hN0 : 0 < N0) (k : ℕ) (A : Finset ℂ)
    (x : Fin (scale N0 (k + 1) - scale N0 k) → ℝ) :
    flatGoodTransition a hN0 k A x ⊆
      RecursiveAlive.rootGrid N0 hN0 (k + 1) := by
  exact (flatGoodTransition_subset_candidates a hN0 k A x).trans
    (RecursiveAlive.scaleChildren_subset_rootGrid_succ N0 hN0 k A)

/-- For a fixed candidate, membership in the good transition set is a measurable
event of the fresh finite scale vector. -/
lemma measurableSet_mem_flatGoodTransition (a : ℕ → ℝ) {N0 : ℕ}
    (hN0 : 0 < N0) (k : ℕ) (A : Finset ℂ) (z : ℂ) :
    MeasurableSet {x | z ∈ flatGoodTransition a hN0 k A x} := by
  by_cases hz : z ∈ RecursiveAlive.scaleChildren N0 hN0 k A
  · rw [show {x | z ∈ flatGoodTransition a hN0 k A x} =
        {x | flatGood a hN0 k z x} by
      ext x
      simp [flatGoodTransition, RecursiveAlive.mem_filterGood, hz]]
    exact flatGood_measurable a hN0 k z
  · rw [show {x | z ∈ flatGoodTransition a hN0 k A x} = ∅ by
      ext x
      simp [flatGoodTransition, RecursiveAlive.mem_filterGood, hz]]
    exact MeasurableSet.empty

lemma exists_flatGoodTransition_parent_with_nesting_of_mem
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) (A : Finset ℂ)
    (x : Fin (scale N0 (k + 1) - scale N0 k) → ℝ) {z : ℂ}
    (hz : z ∈ flatGoodTransition a hN0 k A x) :
    ∃ w ∈ A,
      ‖z - w‖ + Grid.branchRootRadius (scale N0 (k + 1)) (k + 1) ≤
        Grid.branchRootRadius (scale N0 k) k ∧
      Metric.closedBall z (Grid.branchRootRadius (scale N0 (k + 1)) (k + 1)) ⊆
        Metric.closedBall w (Grid.branchRootRadius (scale N0 k) k) := by
  have hzchild : z ∈ RecursiveAlive.scaleChildren N0 hN0 k A :=
    flatGoodTransition_subset_candidates a hN0 k A x hz
  unfold RecursiveAlive.scaleChildren at hzchild
  letI : NeZero N0 := ⟨hN0.ne'⟩
  letI : NeZero (scale N0 k) := ⟨scale_ne_zero hN0.ne' k⟩
  obtain ⟨p, hp, hdist, hball⟩ :=
    Grid.exists_scale_parent_with_nesting_of_mem N0 k hzchild
  refine ⟨Grid.complexGridPoint (scale N0 k) p, hp, ?_, ?_⟩
  · rw [← scale_succ] at hdist
    exact hdist
  · rw [← scale_succ] at hball
    exact hball

lemma exists_flatAlive_parent_with_nesting_of_mem
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (start t : ℕ)
    (ε : ℕ → ℝ) {z : ℂ} (hz : z ∈ flatAlive a hN0 start (t + 1) ε) :
    ∃ w ∈ flatAlive a hN0 start t ε,
      ‖z - w‖ +
          Grid.branchRootRadius (scale N0 (start + t + 1)) (start + t + 1) ≤
        Grid.branchRootRadius (scale N0 (start + t)) (start + t) ∧
      Metric.closedBall z
          (Grid.branchRootRadius (scale N0 (start + t + 1)) (start + t + 1)) ⊆
        Metric.closedBall w
          (Grid.branchRootRadius (scale N0 (start + t)) (start + t)) := by
  exact RecursiveAlive.exists_aliveRel_parent_with_nesting_of_mem
    N0 hN0 start t (flatGood a hN0) ε hz

end

end FlatAliveGood

end Erdos527

open scoped BigOperators ENNReal NNReal Topology
open Filter MeasureTheory ProbabilityTheory

namespace Erdos527
namespace OnePointAsymptotic

noncomputable section

lemma coefficientEnvelope_pos (a : ℕ → ℝ) (N0 k : ℕ) :
    0 < coefficientEnvelope a N0 k := by
  apply lt_of_lt_of_le _ (inv_sqrt_succ_le_coefficientEnvelope a N0 k)
  exact inv_pos.mpr (Real.sqrt_pos.2 (by positivity))

lemma eventually_coefficientEnvelope_le
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ k : ℕ in atTop, coefficientEnvelope a N0 k ≤ c := by
  have h := (coefficientEnvelope_tendsto_zero a hsmall hN0).eventually
    (Metric.closedBall_mem_nhds (x := (0 : ℝ)) hc)
  filter_upwards [h] with k hk
  rw [Real.dist_eq, sub_zero,
    abs_of_pos (coefficientEnvelope_pos a N0 k)] at hk
  exact hk

lemma eventually_coefficientEnvelope_le_one
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) :
    ∀ᶠ k : ℕ in atTop, coefficientEnvelope a N0 k ≤ 1 :=
  eventually_coefficientEnvelope_le a hsmall hN0 (by norm_num)

/- The explicit smallness constant leaves more than a factor two of slack in
the exponent comparison below. -/
lemma eventually_coefficientEnvelope_le_one_billionth
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) :
    ∀ᶠ k : ℕ in atTop,
      coefficientEnvelope a N0 k ≤ (1 / 1000000000 : ℝ) :=
  eventually_coefficientEnvelope_le a hsmall hN0 (by norm_num)

lemma succ_pow_four_le_stepFactor_rpow_thirtieth {k : ℕ} (hk : 40 ≤ k) :
    ((k + 1 : ℕ) : ℝ) ^ 4 ≤
      (((2 ^ stepExponent k : ℕ) : ℝ)) ^ (1 / 30 : ℝ) := by
  have hkpow : k + 1 ≤ 2 ^ k := by
    exact (Grid.add_two_le_two_pow (by omega)).trans' (by omega)
  have hpolyNat : (k + 1) ^ 4 ≤ 2 ^ (k * 4) := by
    calc
      (k + 1) ^ 4 ≤ (2 ^ k) ^ 4 := Nat.pow_le_pow_left hkpow 4
      _ = 2 ^ (k * 4) := by rw [pow_mul]
  have hexpNat : 30 * (k * 4) ≤ stepExponent k := by
    simp only [stepExponent]
    nlinarith
  have hexpReal : ((k * 4 : ℕ) : ℝ) ≤
      ((stepExponent k : ℕ) : ℝ) / 30 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 30)).2
    have hcast : ((30 * (k * 4) : ℕ) : ℝ) ≤ stepExponent k := by
      exact_mod_cast hexpNat
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_comm] using hcast
  calc
    (((k + 1 : ℕ) : ℝ) ^ 4) ≤ ((2 ^ (k * 4) : ℕ) : ℝ) := by
      exact_mod_cast hpolyNat
    _ = (2 : ℝ) ^ (((k * 4 : ℕ) : ℝ)) := by
      rw [Real.rpow_natCast]
      norm_num
    _ ≤ (2 : ℝ) ^ (((stepExponent k : ℕ) : ℝ) / 30) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexpReal
    _ = (((2 ^ stepExponent k : ℕ) : ℝ)) ^ (1 / 30 : ℝ) := by
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]
      rw [div_eq_mul_inv]
      convert Real.rpow_natCast_mul (by positivity : (0 : ℝ) ≤ 2)
        (stepExponent k) (1 / 30 : ℝ) using 1
      all_goals norm_num

lemma four_div_succ_pow_four_ge_stepFactor_rpow_neg_twentieth
    {k : ℕ} (hk : 40 ≤ k) :
    (((2 ^ stepExponent k : ℕ) : ℝ)) ^ (-(1 / 20 : ℝ)) ≤
      4 / (((k + 1 : ℕ) : ℝ) ^ 4) := by
  have hpoly := succ_pow_four_le_stepFactor_rpow_thirtieth hk
  have hK : 0 < (((k + 1 : ℕ) : ℝ) ^ 4) := by positivity
  have hF : 1 ≤ (((2 ^ stepExponent k : ℕ) : ℝ)) := by
    exact_mod_cast one_le_stepFactor k
  have hFpos : 0 < (((2 ^ stepExponent k : ℕ) : ℝ)) := lt_of_lt_of_le zero_lt_one hF
  have hneg : (-(1 / 20 : ℝ)) ≤ -(1 / 30 : ℝ) := by norm_num
  calc
    (((2 ^ stepExponent k : ℕ) : ℝ)) ^ (-(1 / 20 : ℝ)) ≤
        (((2 ^ stepExponent k : ℕ) : ℝ)) ^ (-(1 / 30 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast one_le_stepFactor k) hneg
    _ = ((((2 ^ stepExponent k : ℕ) : ℝ)) ^ (1 / 30 : ℝ))⁻¹ := by
      rw [Real.rpow_neg (by positivity)]
    _ ≤ ((((k + 1 : ℕ) : ℝ) ^ 4))⁻¹ := by
      exact (inv_le_inv₀ (Real.rpow_pos_of_pos hFpos _)
        (by positivity : 0 < (((k + 1 : ℕ) : ℝ) ^ 4))).2 hpoly
    _ ≤ 4 / (((k + 1 : ℕ) : ℝ) ^ 4) := by
      rw [div_eq_mul_inv]
      nlinarith [inv_pos.mpr hK]

lemma fixed_gaussian_loss_ge_stepFactor_rpow_neg_twentieth
    {k : ℕ} (hk : 1000 ≤ k) :
    (((2 ^ stepExponent k : ℕ) : ℝ)) ^ (-(1 / 20 : ℝ)) ≤
      Real.exp (-66560) := by
  rw [BranchParameterArithmetic.stepFactor_cast_eq_two_rpow]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < 2)]
  rw [Real.exp_le_exp]
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hstep : (2662400 : ℝ) ≤ stepExponent k := by
    simp only [stepExponent]
    push_cast
    nlinarith
  nlinarith

lemma variable_gaussian_loss_ge_stepFactor_rpow_neg_tenth
    {k : ℕ} {δ : ℝ} (_hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 1000000000) :
    (((2 ^ stepExponent k : ℕ) : ℝ)) ^ (-(1 / 10 : ℝ)) ≤
      Real.exp (-17039360 * (stepExponent k : ℝ) * δ) := by
  rw [BranchParameterArithmetic.stepFactor_cast_eq_two_rpow]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < 2)]
  rw [Real.exp_le_exp]
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hs : 0 ≤ (stepExponent k : ℝ) := by positivity
  nlinarith

lemma gaussian_real_lower_ge_onePointTarget
    {k : ℕ} (hk : 1000 ≤ k) {δ : ℝ}
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 1000000000) :
    2 * BranchParameterArithmetic.onePointTarget k ≤
      ((1 / (8 * (((k + 1 : ℕ) : ℝ) ^ 2)) /
          (Real.sqrt δ / 16)) *
        Real.exp (-33280 *
          (1 + ((stepExponent k : ℝ) * δ ^ 2) /
            (Real.sqrt δ / 16) ^ 2))) ^ 2 := by
  let F : ℝ := ((2 ^ stepExponent k : ℕ) : ℝ)
  let K : ℝ := ((k + 1 : ℕ) : ℝ)
  have hδone : δ ≤ 1 := hδsmall.trans (by norm_num)
  have hsqrtpos : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hsqrtsq : (Real.sqrt δ) ^ 2 = δ := Real.sq_sqrt hδ.le
  have hsqrtle : Real.sqrt δ ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hδone
  have hK : 0 < K := by dsimp [K]; positivity
  have hFone : 1 ≤ F := by
    dsimp [F]
    exact_mod_cast one_le_stepFactor k
  have hratio : 2 / K ^ 2 ≤
      (1 / (8 * K ^ 2)) / (Real.sqrt δ / 16) := by
    field_simp [ne_of_gt hK, ne_of_gt hsqrtpos]
    nlinarith
  have hratio_nonneg : 0 ≤ 2 / K ^ 2 := by positivity
  have hexppos : 0 < Real.exp (-33280 *
      (1 + ((stepExponent k : ℝ) * δ ^ 2) /
        (Real.sqrt δ / 16) ^ 2)) := Real.exp_pos _
  have hraw :
      ((2 / K ^ 2) * Real.exp (-33280 *
          (1 + ((stepExponent k : ℝ) * δ ^ 2) /
            (Real.sqrt δ / 16) ^ 2))) ^ 2 ≤
      (((1 / (8 * K ^ 2)) / (Real.sqrt δ / 16)) *
        Real.exp (-33280 *
          (1 + ((stepExponent k : ℝ) * δ ^ 2) /
            (Real.sqrt δ / 16) ^ 2))) ^ 2 := by
    gcongr
  have hquot :
      ((stepExponent k : ℝ) * δ ^ 2) / (Real.sqrt δ / 16) ^ 2 =
        256 * (stepExponent k : ℝ) * δ := by
    rw [div_pow, hsqrtsq]
    norm_num
    field_simp [ne_of_gt hδ]
    <;> ring
  have hexp_eq :
      Real.exp (-33280 *
          (1 + ((stepExponent k : ℝ) * δ ^ 2) /
            (Real.sqrt δ / 16) ^ 2)) ^ 2 =
        Real.exp (-66560) *
          Real.exp (-17039360 * (stepExponent k : ℝ) * δ) := by
    rw [hquot, pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hpoly : F ^ (-(1 / 20 : ℝ)) ≤ 4 / K ^ 4 := by
    simpa only [F, K] using
      four_div_succ_pow_four_ge_stepFactor_rpow_neg_twentieth (k := k) (by omega)
  have hfixed : F ^ (-(1 / 20 : ℝ)) ≤ Real.exp (-66560) := by
    simpa only [F] using
      fixed_gaussian_loss_ge_stepFactor_rpow_neg_twentieth (k := k) hk
  have hvariable : F ^ (-(1 / 10 : ℝ)) ≤
      Real.exp (-17039360 * (stepExponent k : ℝ) * δ) := by
    simpa only [F] using variable_gaussian_loss_ge_stepFactor_rpow_neg_tenth
      (k := k) hδ.le hδsmall
  have hfactor :
      F ^ (-(1 / 20 : ℝ)) * F ^ (-(1 / 20 : ℝ)) *
          F ^ (-(1 / 10 : ℝ)) ≤
        (4 / K ^ 4) * Real.exp (-66560) *
          Real.exp (-17039360 * (stepExponent k : ℝ) * δ) := by
    gcongr
  have hcombine :
      F ^ (-(1 / 20 : ℝ)) * F ^ (-(1 / 20 : ℝ)) *
          F ^ (-(1 / 10 : ℝ)) = F ^ (-(1 / 5 : ℝ)) := by
    rw [← Real.rpow_add (lt_of_lt_of_le zero_lt_one hFone),
      ← Real.rpow_add (lt_of_lt_of_le zero_lt_one hFone)]
    congr 2 <;> norm_num
  have hroot30 : K ^ 4 ≤ F ^ (1 / 30 : ℝ) := by
    simpa only [F, K] using
      succ_pow_four_le_stepFactor_rpow_thirtieth (k := k) (by omega)
  have hrootmono : F ^ (1 / 30 : ℝ) ≤ F ^ (1 / 20 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hFone (by norm_num)
  have htwoK : (2 : ℝ) ≤ K ^ 4 := by
    dsimp only [K]
    push_cast
    have hx : (2 : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast (show 2 ≤ k + 1 by omega)
    have hx2 : (4 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith
    nlinarith [sq_nonneg (((k : ℝ) + 1) ^ 2 - 4)]
  have hroot : (2 : ℝ) ≤ F ^ (1 / 20 : ℝ) :=
    htwoK.trans (hroot30.trans hrootmono)
  have htargetF :
      2 * F ^ (-(1 / 4 : ℝ)) ≤ F ^ (-(1 / 5 : ℝ)) := by
    calc
      2 * F ^ (-(1 / 4 : ℝ)) ≤
          F ^ (1 / 20 : ℝ) * F ^ (-(1 / 4 : ℝ)) := by
        exact mul_le_mul_of_nonneg_right hroot (Real.rpow_nonneg (by positivity) _)
      _ = F ^ (-(1 / 5 : ℝ)) := by
        rw [← Real.rpow_add (lt_of_lt_of_le zero_lt_one hFone)]
        congr 2
        norm_num
  have hsimple :
      (4 / K ^ 4) * Real.exp (-66560) *
          Real.exp (-17039360 * (stepExponent k : ℝ) * δ) =
        ((2 / K ^ 2) * Real.exp (-33280 *
          (1 + ((stepExponent k : ℝ) * δ ^ 2) /
            (Real.sqrt δ / 16) ^ 2))) ^ 2 := by
    rw [mul_pow, hexp_eq]
    field_simp [ne_of_gt hK]
    <;> ring
  calc
    2 * BranchParameterArithmetic.onePointTarget k =
        2 * F ^ (-(1 / 4 : ℝ)) := by rfl
    _ ≤ F ^ (-(1 / 5 : ℝ)) := htargetF
    _ = F ^ (-(1 / 20 : ℝ)) * F ^ (-(1 / 20 : ℝ)) *
          F ^ (-(1 / 10 : ℝ)) := hcombine.symm
    _ ≤ (4 / K ^ 4) * Real.exp (-66560) *
          Real.exp (-17039360 * (stepExponent k : ℝ) * δ) := hfactor
    _ = ((2 / K ^ 2) * Real.exp (-33280 *
          (1 + ((stepExponent k : ℝ) * δ ^ 2) /
            (Real.sqrt δ / 16) ^ 2))) ^ 2 := hsimple
    _ ≤ (((1 / (8 * K ^ 2)) / (Real.sqrt δ / 16)) *
        Real.exp (-33280 *
          (1 + ((stepExponent k : ℝ) * δ ^ 2) /
            (Real.sqrt δ / 16) ^ 2))) ^ 2 := hraw

lemma gaussian_ennreal_lower_ge_onePointTarget
    {k : ℕ} (hk : 1000 ≤ k) {δ : ℝ}
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 1000000000) :
    2 * BranchParameterArithmetic.onePointTarget k ≤
      (ENNReal.ofReal
        ((1 / (8 * (((k + 1 : ℕ) : ℝ) ^ 2)) /
            (Real.sqrt δ / 16)) *
          Real.exp (-33280 *
            (1 + ((stepExponent k : ℝ) * δ ^ 2) /
              (Real.sqrt δ / 16) ^ 2))) ^ 2).toReal := by
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal]
  · exact gaussian_real_lower_ge_onePointTarget hk hδ hδsmall
  · exact mul_nonneg
      (div_nonneg (by positivity) (div_nonneg (Real.sqrt_nonneg _) (by norm_num)))
      (Real.exp_pos _).le

lemma eventually_gaussian_ennreal_lower_ge_onePointTarget
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) :
    ∀ᶠ k : ℕ in atTop,
    2 * BranchParameterArithmetic.onePointTarget k ≤
        (ENNReal.ofReal
          ((1 / (8 * (((k + 1 : ℕ) : ℝ) ^ 2)) /
              (Real.sqrt (coefficientEnvelope a N0 k) / 16)) *
            Real.exp (-33280 *
              (1 + ((stepExponent k : ℝ) * coefficientEnvelope a N0 k ^ 2) /
                (Real.sqrt (coefficientEnvelope a N0 k) / 16) ^ 2))) ^ 2).toReal := by
  filter_upwards [eventually_ge_atTop 1000,
    eventually_coefficientEnvelope_le_one_billionth a hsmall hN0] with k hk hδ
  exact gaussian_ennreal_lower_ge_onePointTarget hk
    (coefficientEnvelope_pos a N0 k) hδ

end
end OnePointAsymptotic
end Erdos527


open scoped BigOperators ENNReal NNReal ProbabilityTheory Topology

namespace Erdos527

open Filter MeasureTheory ProbabilityTheory

namespace OnePointLindebergAsymptotic

noncomputable section

def concreteEndpointScale (k : ℕ) : ℝ := 4 * (k + 1 : ℕ) ^ 2

def concretePrefixScale (a : ℕ → ℝ) (N0 k : ℕ) : ℝ :=
  4 / Real.sqrt (coefficientEnvelope a N0 k)

lemma coefficientEnvelope_pos (a : ℕ → ℝ) (N0 k : ℕ) :
    0 < coefficientEnvelope a N0 k := by
  apply lt_of_lt_of_le _ (inv_sqrt_succ_le_coefficientEnvelope a N0 k)
  positivity

lemma one_div_nat_succ_le_coefficientEnvelope
    (a : ℕ → ℝ) (N0 k : ℕ) :
    1 / (k + 1 : ℕ) ≤ coefficientEnvelope a N0 k := by
  apply le_trans _ (inv_sqrt_succ_le_coefficientEnvelope a N0 k)
  rw [div_eq_mul_inv, one_mul]
  apply inv_anti₀
  · positivity
  · exact (Real.sqrt_le_self_iff).2 (Or.inr (by norm_num))

lemma concretePrefixScale_le
    (a : ℕ → ℝ) (N0 k : ℕ)
    (henv : coefficientEnvelope a N0 k ≤ 1) :
    concretePrefixScale a N0 k ≤ 4 * (k + 1 : ℕ) := by
  let δ := coefficientEnvelope a N0 k
  have hδpos : 0 < δ := coefficientEnvelope_pos a N0 k
  have hδfloor : 1 / (k + 1 : ℕ) ≤ δ :=
    one_div_nat_succ_le_coefficientEnvelope a N0 k
  have hδsqrt : δ ≤ Real.sqrt δ := by
    rw [Real.le_sqrt_self_iff]
    exact henv
  have hsqrtpos : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδpos
  have hinv : 1 / Real.sqrt δ ≤ (k + 1 : ℕ) := by
    apply (div_le_iff₀ hsqrtpos).2
    have hmul : 1 ≤ (k + 1 : ℕ) * δ := by
      have hkpos : (0 : ℝ) < (k + 1 : ℕ) := by positivity
      simpa [mul_comm] using (div_le_iff₀ hkpos).1 hδfloor
    exact hmul.trans (mul_le_mul_of_nonneg_left hδsqrt (by positivity))
  unfold concretePrefixScale
  simpa [δ, div_eq_mul_inv] using
    (mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 4))

lemma uniformBlockCount_cast_le (k : ℕ) :
    (uniformBlockCount k : ℝ) ≤
      ((2 ^ (k + stepExponent k) : ℕ) : ℝ) := by
  have hnat : uniformBlockCount k ≤ 2 ^ (k + stepExponent k) := by
    rw [uniformBlockCount, pow_add]
    exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  exact_mod_cast hnat

lemma uniformBlockCount_succ_cast_le (k : ℕ) :
    ((uniformBlockCount k + 1 : ℕ) : ℝ) ≤
      ((2 ^ (k + stepExponent k + 1) : ℕ) : ℝ) := by
  have hpos : 1 ≤ uniformBlockCount k := uniformBlockCount_pos k
  have hnat : uniformBlockCount k + 1 ≤ 2 ^ (k + stepExponent k + 1) := by
    calc
      uniformBlockCount k + 1 ≤ 2 * uniformBlockCount k := by omega
      _ ≤ 2 * 2 ^ (k + stepExponent k) :=
        Nat.mul_le_mul_left 2 (by
          rw [uniformBlockCount, pow_add]
          exact Nat.mul_le_mul_left _ (Nat.sub_le _ _))
      _ = 2 ^ (k + stepExponent k + 1) := by
        rw [pow_succ]
        ring
  exact_mod_cast hnat

lemma concreteScaleSum_le (a : ℕ → ℝ) (N0 k : ℕ)
    (henv : coefficientEnvelope a N0 k ≤ 1) :
    |concreteEndpointScale k| + |concretePrefixScale a N0 k| ≤
      8 * (k + 1 : ℕ) ^ 2 := by
  have hk : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have hp := concretePrefixScale_le a N0 k henv
  have hpnonneg : 0 ≤ concretePrefixScale a N0 k := by
    unfold concretePrefixScale
    positivity
  have henonneg : 0 ≤ concreteEndpointScale k := by
    unfold concreteEndpointScale
    positivity
  rw [abs_of_nonneg henonneg, abs_of_nonneg hpnonneg]
  unfold concreteEndpointScale
  nlinarith [sq_nonneg ((k + 1 : ℕ) - 1)]

lemma nat_succ_sq_le_two_pow_two_mul {k : ℕ} (hk : 1 ≤ k) :
    (k + 1) ^ 2 ≤ 2 ^ (2 * k) := by
  have hbase : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  calc
    (k + 1) ^ 2 ≤ (2 ^ k) ^ 2 := Nat.pow_le_pow_left hbase 2
    _ = 2 ^ (2 * k) := by rw [← pow_mul]; congr 1 <;> omega

lemma concreteScaleSum_le_two_pow {a : ℕ → ℝ} {N0 k : ℕ}
    (hk : 1 ≤ k) (henv : coefficientEnvelope a N0 k ≤ 1) :
    |concreteEndpointScale k| + |concretePrefixScale a N0 k| ≤
      ((2 ^ (2 * k + 3) : ℕ) : ℝ) := by
  calc
    |concreteEndpointScale k| + |concretePrefixScale a N0 k| ≤
      8 * (k + 1 : ℕ) ^ 2 := concreteScaleSum_le a N0 k henv
    _ ≤ 8 * ((2 ^ (2 * k) : ℕ) : ℝ) := by
      gcongr
      exact_mod_cast nat_succ_sq_le_two_pow_two_mul hk
    _ = ((2 ^ (2 * k + 3) : ℕ) : ℝ) := by
      push_cast
      rw [pow_add]
      norm_num
      ring

lemma flatCutoffOperatorBudget_concrete_le {a : ℕ → ℝ} {N0 k : ℕ}
    (hk : 1 ≤ k) (henv : coefficientEnvelope a N0 k ≤ 1) :
    OnePointLindeberg.flatCutoffOperatorBudget k
        (concreteEndpointScale k) (concretePrefixScale a N0 k) ≤
      SmoothCutoffC4.cutoffC4 *
        ((2 ^ (4 * k + 2 * stepExponent k + 4) : ℕ) : ℝ) := by
  unfold OnePointLindeberg.flatCutoffOperatorBudget
  apply mul_le_mul_of_nonneg_left _ SmoothCutoffC4.cutoffC4_nonneg
  calc
    (((uniformBlockCount k + 1 : ℕ) : ℝ) *
        (|concreteEndpointScale k| + |concretePrefixScale a N0 k|) *
        (uniformBlockCount k : ℝ)) ≤
      ((2 ^ (k + stepExponent k + 1) : ℕ) : ℝ) *
        ((2 ^ (2 * k + 3) : ℕ) : ℝ) *
        ((2 ^ (k + stepExponent k) : ℕ) : ℝ) := by
          gcongr
          · exact_mod_cast uniformBlockCount_succ_cast_le k
          · exact concreteScaleSum_le_two_pow hk henv
          · exact_mod_cast uniformBlockCount_cast_le k
    _ = ((2 ^ (4 * k + 2 * stepExponent k + 4) : ℕ) : ℝ) := by
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]
      rw [← pow_add, ← pow_add]
      congr 1
      omega

lemma scale_gap_cast_le_scale_mul_stepFactor (N0 k : ℕ) :
    ((scale N0 (k + 1) - scale N0 k : ℕ) : ℝ) ≤
      (scale N0 k : ℝ) * (2 ^ stepExponent k : ℕ) := by
  exact_mod_cast (Nat.sub_le (scale N0 (k + 1)) (scale N0 k)).trans_eq
    (scale_succ N0 k)

lemma flatOnePointLindebergError_concrete_le
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) {k : ℕ} (hk : 1 ≤ k)
    (henv : coefficientEnvelope a N0 k ≤ 1) :
    OnePointLindeberg.flatOnePointLindebergError a N0 k
        (concreteEndpointScale k) (concretePrefixScale a N0 k) ≤
      SmoothCutoffC4.cutoffC4 ^ 4 *
        ((2 ^ (16 * k + 9 * stepExponent k + 16) : ℕ) : ℝ) /
          (scale N0 k : ℝ) := by
  let δ := coefficientEnvelope a N0 k
  let S : ℝ := scale N0 k
  let F : ℝ := (2 ^ stepExponent k : ℕ)
  let B := OnePointLindeberg.flatCutoffOperatorBudget k
    (concreteEndpointScale k) (concretePrefixScale a N0 k)
  let Q : ℝ := ((2 ^ (4 * k + 2 * stepExponent k + 4) : ℕ) : ℝ)
  have hSpos : 0 < S := by
    dsimp only [S]
    exact_mod_cast scale_pos hN0 k
  have hFnonneg : 0 ≤ F := by positivity
  have hBnonneg : 0 ≤ B := by
    exact OnePointLindeberg.flatCutoffOperatorBudget_nonneg _ _ _
  have hB : B ≤ SmoothCutoffC4.cutoffC4 * Q := by
    exact flatCutoffOperatorBudget_concrete_le hk henv
  have hB4 : B ^ 4 ≤ (SmoothCutoffC4.cutoffC4 * Q) ^ 4 :=
    pow_le_pow_left₀ hBnonneg hB 4
  have hgap : ((scale N0 (k + 1) - scale N0 k : ℕ) : ℝ) ≤ S * F := by
    exact scale_gap_cast_le_scale_mul_stepFactor N0 k
  have hδnonneg : 0 ≤ δ := coefficientEnvelope_nonneg a hsmall N0 k
  have hδsq : δ ^ 2 ≤ 1 := by nlinarith [sq_nonneg (δ - 1)]
  have hfrac0 : 0 ≤ (δ ^ 2 / S) ^ 2 := sq_nonneg _
  have hfrac : (δ ^ 2 / S) ^ 2 ≤ (1 / S) ^ 2 := by
    apply pow_le_pow_left₀ (div_nonneg (sq_nonneg _) hSpos.le) _ 2
    exact div_le_div_of_nonneg_right hδsq hSpos.le
  have hmajor0 : 0 ≤
      (SmoothCutoffC4.cutoffC4 * Q) ^ 4 * (S * F) * (1 / S) ^ 2 := by
    positivity
  unfold OnePointLindeberg.flatOnePointLindebergError
  change B ^ 4 *
      (((scale N0 (k + 1) - scale N0 k : ℕ) : ℝ) * (δ ^ 2 / S) ^ 2) / 6 ≤ _
  calc
    B ^ 4 * (((scale N0 (k + 1) - scale N0 k : ℕ) : ℝ) *
          (δ ^ 2 / S) ^ 2) / 6 ≤
        ((SmoothCutoffC4.cutoffC4 * Q) ^ 4 * (S * F) * (1 / S) ^ 2) / 6 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      calc
        B ^ 4 * (((scale N0 (k + 1) - scale N0 k : ℕ) : ℝ) *
            (δ ^ 2 / S) ^ 2) ≤
            (SmoothCutoffC4.cutoffC4 * Q) ^ 4 *
              ((S * F) * (1 / S) ^ 2) := by
          apply mul_le_mul hB4
          · exact mul_le_mul hgap hfrac hfrac0 (by positivity)
          · exact mul_nonneg (Nat.cast_nonneg _) hfrac0
          · positivity
        _ = (SmoothCutoffC4.cutoffC4 * Q) ^ 4 * (S * F) *
            (1 / S) ^ 2 := by ring
    _ ≤ (SmoothCutoffC4.cutoffC4 * Q) ^ 4 * (S * F) * (1 / S) ^ 2 := by
      exact div_le_self hmajor0 (by norm_num)
    _ = SmoothCutoffC4.cutoffC4 ^ 4 *
        ((2 ^ (16 * k + 9 * stepExponent k + 16) : ℕ) : ℝ) /
          (scale N0 k : ℝ) := by
      dsimp only [Q, S, F]
      field_simp [ne_of_gt hSpos]
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]
      rw [← pow_mul]
      have hp : (2 : ℝ) ^ ((4 * k + 2 * stepExponent k + 4) * 4) *
          2 ^ stepExponent k =
          2 ^ (16 * k + 9 * stepExponent k + 16) := by
        rw [← pow_add]
        congr 1
        omega
      calc
        SmoothCutoffC4.cutoffC4 ^ 4 *
              2 ^ ((4 * k + 2 * stepExponent k + 4) * 4) *
              2 ^ stepExponent k / (scale N0 k : ℝ) =
            SmoothCutoffC4.cutoffC4 ^ 4 *
              (2 ^ ((4 * k + 2 * stepExponent k + 4) * 4) *
                2 ^ stepExponent k) / (scale N0 k : ℝ) := by ring
        _ = SmoothCutoffC4.cutoffC4 ^ 4 *
              2 ^ (16 * k + 9 * stepExponent k + 16) /
                (scale N0 k : ℝ) := by rw [hp]

lemma inverse_stepFactor_le_onePointTarget (k : ℕ) :
    1 / ((2 ^ stepExponent k : ℕ) : ℝ) ≤
      BranchParameterArithmetic.onePointTarget k := by
  let F : ℝ := (2 ^ stepExponent k : ℕ)
  have hFpos : 0 < F := by positivity
  rw [BranchParameterArithmetic.onePointTarget]
  change 1 / F ≤ F ^ (-(1 / 4 : ℝ))
  rw [show 1 / F = F ^ (-(1 : ℝ)) by
    rw [Real.rpow_neg_one]
    exact one_div F]
  have hFone : 1 ≤ F := by
    dsimp only [F]
    exact_mod_cast one_le_stepFactor k
  exact Real.rpow_le_rpow_of_exponent_le hFone (by norm_num)

lemma cubic_dominates_lindeberg_exponent {k : ℕ} (hk : 32 ≤ k) :
    k + (16 * k + 9 * stepExponent k + 16) + 1 + stepExponent k ≤ k ^ 3 := by
  simp only [stepExponent]
  nlinarith

lemma eventual_cutoffC4_pow_four_le_two_pow :
    ∀ᶠ k : ℕ in atTop,
      SmoothCutoffC4.cutoffC4 ^ 4 ≤ ((2 ^ k : ℕ) : ℝ) := by
  have ht : Tendsto (fun k : ℕ ↦ ((2 ^ k : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
  exact ht.eventually_ge_atTop (SmoothCutoffC4.cutoffC4 ^ 4)

lemma eventual_concrete_error_le_inverse_stepFactor_half
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) :
    ∀ᶠ k : ℕ in atTop,
      OnePointLindeberg.flatOnePointLindebergError a N0 k
          (concreteEndpointScale k) (concretePrefixScale a N0 k) ≤
        1 / (2 * ((2 ^ stepExponent k : ℕ) : ℝ)) := by
  have henv : ∀ᶠ k : ℕ in atTop, coefficientEnvelope a N0 k ≤ 1 :=
    (coefficientEnvelope_tendsto_zero a hsmall hN0).eventually_le_const
      (by norm_num : (0 : ℝ) < 1)
  filter_upwards [henv, eventual_cutoffC4_pow_four_le_two_pow,
    eventually_ge_atTop 32] with k hδ hC hk
  apply (flatOnePointLindebergError_concrete_le a hsmall hN0 (by omega) hδ).trans
  have hSpos : (0 : ℝ) < scale N0 k := by exact_mod_cast scale_pos hN0 k
  have hFpos : (0 : ℝ) < (2 ^ stepExponent k : ℕ) := by positivity
  apply (div_le_div_iff₀ hSpos (mul_pos (by norm_num) hFpos)).2
  calc
    SmoothCutoffC4.cutoffC4 ^ 4 *
          ((2 ^ (16 * k + 9 * stepExponent k + 16) : ℕ) : ℝ) *
          (2 * ((2 ^ stepExponent k : ℕ) : ℝ)) ≤
        ((2 ^ k : ℕ) : ℝ) *
          ((2 ^ (16 * k + 9 * stepExponent k + 16) : ℕ) : ℝ) *
          (2 * ((2 ^ stepExponent k : ℕ) : ℝ)) := by
      gcongr
    _ = ((2 ^ (k + (16 * k + 9 * stepExponent k + 16) + 1 +
          stepExponent k) : ℕ) : ℝ) := by
      exact_mod_cast (show
        2 ^ k * 2 ^ (16 * k + 9 * stepExponent k + 16) *
            (2 * 2 ^ stepExponent k) =
          2 ^ (k + (16 * k + 9 * stepExponent k + 16) + 1 +
            stepExponent k) by
        simp only [pow_add, pow_one]
        ring)
    _ ≤ ((2 ^ (k ^ 3) : ℕ) : ℝ) := by
      exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ))
        (cubic_dominates_lindeberg_exponent hk)
    _ ≤ 1 * (scale N0 k : ℝ) := by
      simpa using (show ((2 ^ (k ^ 3) : ℕ) : ℝ) ≤ (scale N0 k : ℝ) by
        exact_mod_cast pow_cube_le_scale hN0 k)

theorem eventually_flatOnePointLindebergError_le_target_half
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) :
    ∀ᶠ k : ℕ in atTop,
      OnePointLindeberg.flatOnePointLindebergError a N0 k
          (concreteEndpointScale k) (concretePrefixScale a N0 k) ≤
        BranchParameterArithmetic.onePointTarget k / 2 := by
  filter_upwards [eventual_concrete_error_le_inverse_stepFactor_half
      a hsmall hN0] with k hk
  calc
    OnePointLindeberg.flatOnePointLindebergError a N0 k
        (concreteEndpointScale k) (concretePrefixScale a N0 k) ≤
      1 / (2 * ((2 ^ stepExponent k : ℕ) : ℝ)) := hk
    _ = (1 / ((2 ^ stepExponent k : ℕ) : ℝ)) / 2 := by ring
    _ ≤ BranchParameterArithmetic.onePointTarget k / 2 := by
      exact div_le_div_of_nonneg_right (inverse_stepFactor_le_onePointTarget k)
        (by norm_num)

end

end OnePointLindebergAsymptotic
end Erdos527


open scoped BigOperators ENNReal NNReal ProbabilityTheory Topology
open Filter MeasureTheory ProbabilityTheory

namespace Erdos527

namespace OnePointApplication

noncomputable section

def endpointScale (k : ℕ) : ℝ := 4 * (k + 1 : ℝ) ^ 2

noncomputable def prefixScale (a : ℕ → ℝ) (N0 k : ℕ) : ℝ :=
  4 / Real.sqrt (coefficientEnvelope a N0 k)

noncomputable def gaussianRadius (a : ℕ → ℝ) (N0 k : ℕ) : ℝ :=
  Real.sqrt (coefficientEnvelope a N0 k) / 16

noncomputable def endpointRadius (k : ℕ) : ℝ :=
  1 / (8 * (k + 1 : ℝ) ^ 2)

noncomputable def scaleEnergyBound (a : ℕ → ℝ) (N0 k : ℕ) : ℝ :=
  stepExponent k * coefficientEnvelope a N0 k ^ 2

lemma coefficientEnvelope_pos (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    (N0 k : ℕ) : 0 < coefficientEnvelope a N0 k := by
  exact lt_of_lt_of_le (inv_pos.mpr (Real.sqrt_pos.2 (by positivity)))
    (inv_sqrt_succ_le_coefficientEnvelope a N0 k)

lemma gaussianRadius_pos (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    (N0 k : ℕ) : 0 < gaussianRadius a N0 k := by
  unfold gaussianRadius
  exact div_pos (Real.sqrt_pos.2 (coefficientEnvelope_pos a hsmall N0 k)) (by norm_num)

lemma endpointRadius_nonneg (k : ℕ) : 0 ≤ endpointRadius k := by
  unfold endpointRadius
  positivity

lemma endpointScale_endpointRadius (k : ℕ) :
    |endpointScale k| * (2 * endpointRadius k) = 1 := by
  unfold endpointScale endpointRadius
  have hk : (0 : ℝ) < k + 1 := by positivity
  rw [abs_of_pos (mul_pos (by norm_num) (sq_pos_of_pos hk))]
  field_simp
  ring

lemma prefixScale_gaussianRadius (a : ℕ → ℝ)
    (hsmall : DecaysFasterThanInvSqrt a) (N0 k : ℕ) :
    |prefixScale a N0 k| * (5 * gaussianRadius a N0 k / 2) = 5 / 8 := by
  have hδ : 0 < coefficientEnvelope a N0 k :=
    coefficientEnvelope_pos a hsmall N0 k
  have hs : 0 < Real.sqrt (coefficientEnvelope a N0 k) := Real.sqrt_pos.2 hδ
  unfold prefixScale gaussianRadius
  rw [abs_of_pos (div_pos (by norm_num) hs)]
  field_simp
  norm_num

lemma endpointRadius_le_gaussianRadius_div_four
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    (N0 : ℕ) {k : ℕ} (hk : 7 ≤ k)
    (hδle : coefficientEnvelope a N0 k ≤ 1) :
    endpointRadius k ≤ gaussianRadius a N0 k / 4 := by
  let K : ℝ := k + 1
  let δ : ℝ := coefficientEnvelope a N0 k
  have hK : 0 < K := by dsimp [K]; positivity
  have hK8 : 8 ≤ K := by
    dsimp only [K]
    exact_mod_cast (show 8 ≤ k + 1 by omega)
  have hδ : 0 < δ := coefficientEnvelope_pos a hsmall N0 k
  have hsK0 : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
  have hsKsq : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK.le
  have hsKle : Real.sqrt K ≤ K := by nlinarith
  have hinvK : K⁻¹ ≤ (Real.sqrt K)⁻¹ := by
    exact (inv_le_inv₀ hK (Real.sqrt_pos.2 hK)).2 hsKle
  have hδlo : (Real.sqrt K)⁻¹ ≤ δ := by
    simpa [K, δ, Nat.cast_add, Nat.cast_one] using
      inv_sqrt_succ_le_coefficientEnvelope a N0 k
  have hKδ : K⁻¹ ≤ δ := hinvK.trans hδlo
  have hsδ0 : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg δ
  have hsδsq : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt hδ.le
  have hδle' : δ ≤ 1 := by simpa only [δ] using hδle
  have hsδle : Real.sqrt δ ≤ 1 := by nlinarith
  have hδsqrt : δ ≤ Real.sqrt δ := by nlinarith
  have h8 : 8 / K ^ 2 ≤ K⁻¹ := by
    calc
      8 / K ^ 2 ≤ K / K ^ 2 :=
        div_le_div_of_nonneg_right hK8 (sq_nonneg K)
      _ = K⁻¹ := by field_simp [ne_of_gt hK]
  have hmain : 8 / K ^ 2 ≤ Real.sqrt δ := h8.trans (hKδ.trans hδsqrt)
  unfold endpointRadius gaussianRadius
  dsimp only [K, δ] at hmain ⊢
  calc
    1 / (8 * (k + 1 : ℝ) ^ 2) = (8 / (k + 1 : ℝ) ^ 2) / 64 := by
      field_simp [ne_of_gt (show (0 : ℝ) < k + 1 by positivity)]
      norm_num
    _ ≤ Real.sqrt (coefficientEnvelope a N0 k) / 64 :=
      div_le_div_of_nonneg_right hmain (by norm_num)
    _ = (Real.sqrt (coefficientEnvelope a N0 k) / 16) / 4 := by ring

lemma eventually_endpointRadius_le_gaussianRadius_div_four
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) :
    ∀ᶠ k : ℕ in atTop,
      endpointRadius k ≤ gaussianRadius a N0 k / 4 := by
  have henv : ∀ᶠ k : ℕ in atTop, coefficientEnvelope a N0 k ≤ 1 :=
    (coefficientEnvelope_tendsto_zero a hsmall hN0).eventually
      (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventually_ge_atTop 7, henv] with k hk hδ
  exact endpointRadius_le_gaussianRadius_div_four a hsmall N0 hk hδ

lemma flatPhaseCoefficient_normSq
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) (z : ℂ)
    (hz : ‖z‖ = 1) (i : Fin (scale N0 (k + 1) - scale N0 k)) :
    Complex.normSq (OnePointLindeberg.flatPhaseCoefficient a N0 k z i) =
      a (OnePointLindeberg.flatScaleIndex N0 k i) ^ 2 := by
  rw [← Complex.sq_norm]
  simp only [OnePointLindeberg.flatPhaseCoefficient, norm_mul, Complex.norm_real,
    norm_pow, hz, one_pow, mul_one, Real.norm_eq_abs, sq_abs]

lemma flatPhaseCoefficient_energy_le
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) (z : ℂ) (hz : ‖z‖ = 1) :
    (∑ i, Complex.normSq
        (OnePointLindeberg.flatPhaseCoefficient a N0 k z i)) ≤
      scaleEnergyBound a N0 k := by
  rw [show (∑ i, Complex.normSq
      (OnePointLindeberg.flatPhaseCoefficient a N0 k z i)) =
      ∑ n ∈ Finset.Ico (scale N0 k) (scale N0 (k + 1)), a n ^ 2 by
    simp_rw [flatPhaseCoefficient_normSq a hN0 k z hz]
    change (∑ i : Fin (scale N0 (k + 1) - scale N0 k),
        (fun j : ℕ ↦ a (scale N0 k + j) ^ 2) i) = _
    calc
      (∑ i : Fin (scale N0 (k + 1) - scale N0 k),
          (fun j : ℕ ↦ a (scale N0 k + j) ^ 2) i) =
          ∑ i ∈ Finset.range (scale N0 (k + 1) - scale N0 k),
            a (scale N0 k + i) ^ 2 :=
        Fin.sum_univ_eq_sum_range
          (fun j : ℕ ↦ a (scale N0 k + j) ^ 2)
          (scale N0 (k + 1) - scale N0 k)
      _ = _ := (Finset.sum_Ico_eq_sum_range (fun n ↦ a n ^ 2)
        (scale N0 k) (scale N0 (k + 1))).symm]
  unfold scaleEnergyBound
  simpa only [sq_abs] using
    (Erdos527.sum_sq_scale_le a (coefficientEnvelope_nonneg a hsmall N0 k) hN0
      (fun n hn ↦ scaledAbs_le_coefficientEnvelope a hsmall
        (Finset.mem_Ico.mp hn).1))

lemma eventually_flatPhaseCoefficient_small
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) :
    ∀ᶠ k : ℕ in atTop, ∀ (z : ℂ), ‖z‖ = 1 → ∀ i,
      Complex.normSq (OnePointLindeberg.flatPhaseCoefficient a N0 k z i) ≤
        gaussianRadius a N0 k ^ 2 / 128 := by
  have henv : ∀ᶠ k : ℕ in atTop, coefficientEnvelope a N0 k ≤ 1 :=
    (coefficientEnvelope_tendsto_zero a hsmall hN0).eventually
      (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  have hscale : ∀ᶠ k : ℕ in atTop, 32768 ≤ scale N0 k :=
    (scale_tendsto_atTop hN0).eventually_ge_atTop 32768
  filter_upwards [henv, hscale] with k hδle hS z hz i
  have hδ : 0 < coefficientEnvelope a N0 k :=
    coefficientEnvelope_pos a hsmall N0 k
  have hscaled := sq_abs_le_div_of_scaled_le (scale_pos hN0 k)
    (OnePointLindeberg.flatScaleIndex_ge N0 k i) hδ.le
    (scaledAbs_le_coefficientEnvelope a hsmall
      (OnePointLindeberg.flatScaleIndex_ge N0 k i))
  rw [flatPhaseCoefficient_normSq a hN0 k z hz]
  unfold gaussianRadius
  have hSreal : (32768 : ℝ) ≤ scale N0 k := by exact_mod_cast hS
  calc
    a (OnePointLindeberg.flatScaleIndex N0 k i) ^ 2 ≤
        coefficientEnvelope a N0 k ^ 2 / scale N0 k := by
          simpa only [sq_abs] using hscaled
    _ ≤ coefficientEnvelope a N0 k / 32768 := by
      rw [div_le_div_iff₀ (by exact_mod_cast scale_pos hN0 k) (by norm_num)]
      nlinarith
    _ = (Real.sqrt (coefficientEnvelope a N0 k) / 16) ^ 2 / 128 := by
      rw [div_pow, Real.sq_sqrt hδ.le]
      norm_num
      ring

def doubledCanonicalIndex (n : ℕ) : Fin n ⊕ Fin n → Fin (n + n) :=
  Sum.elim (Fin.castAdd n) (Fin.natAdd n)

lemma doubledCanonicalIndex_injective (n : ℕ) :
    Function.Injective (doubledCanonicalIndex n) := by
  rw [doubledCanonicalIndex, Sum.elim_injective]
  refine ⟨Fin.castAdd_injective n n, Fin.natAdd_injective n n, ?_⟩
  intro i j hij
  have := congrArg Fin.val hij
  change i.val = n + j.val at this
  omega

def doubledCanonicalCoords (n : ℕ) (j : Fin n ⊕ Fin n)
    (x : EuclideanSpace ℝ (Fin (n + n))) : ℝ :=
  x (doubledCanonicalIndex n j)

lemma doubledCanonicalCoords_standard (n : ℕ) :
    GaussianCircularization.IndependentStandardGaussians
      (doubledCanonicalCoords n)
      (stdGaussian (EuclideanSpace ℝ (Fin (n + n)))) := by
  constructor
  · intro j
    exact ScalarGaussianPath.Canonical.coord_hasLaw (doubledCanonicalIndex n j)
  · change iIndepFun
      (fun j (x : EuclideanSpace ℝ (Fin (n + n))) ↦
        x (doubledCanonicalIndex n j)) _
    exact ProbabilityTheory.iIndepFun.precomp (doubledCanonicalIndex_injective n)
      (ScalarGaussianPath.Canonical.coord_iIndep (n := n + n))

def canonicalFirstCoords (n : ℕ) (i : Fin n)
    (x : EuclideanSpace ℝ (Fin (n + n))) : ℝ :=
  x (Fin.castAdd n i)

def canonicalSecondCoords (n : ℕ) (i : Fin n)
    (x : EuclideanSpace ℝ (Fin (n + n))) : ℝ :=
  x (Fin.natAdd n i)

lemma doubledFamily_canonicalCoords (n : ℕ) :
    GaussianCircularization.doubledFamily
      (canonicalFirstCoords n) (canonicalSecondCoords n) =
        doubledCanonicalCoords n := by
  funext j x
  cases j <;> rfl

/-- The fully concrete Gaussian estimate, uniform in the unit phase. -/
theorem eventually_two_mul_onePointTarget_le_flat_gaussian_expectation
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) :
    ∀ᶠ k : ℕ in atTop, ∀ z : ℂ, ‖z‖ = 1 →
      2 * BranchParameterArithmetic.onePointTarget k ≤
        ∫ x, SmoothCutoffC4.endpointPrefixCutoff
            (uniformBlockCount k) (endpointScale k) (prefixScale a N0 k)
            (CutoffLindebergBridge.NormedLindeberg.linearCombination
              (OnePointLindeberg.flatBlockIncrementDirection a hN0 k z) x)
          ∂Erdos88.Invariance.gaussianProductMeasure
            (scale N0 (k + 1) - scale N0 k) := by
  have hq := OnePointAsymptotic.eventually_gaussian_ennreal_lower_ge_onePointTarget
    a hsmall hN0
  have hru := eventually_endpointRadius_le_gaussianRadius_div_four
    a hsmall hN0
  have hcoord := eventually_flatPhaseCoefficient_small a hsmall hN0
  filter_upwards [hq, hru, hcoord] with k hqk hruk hcoordk z hz
  let n := scale N0 (k + 1) - scale N0 k
  let P : Measure (EuclideanSpace ℝ (Fin (n + n))) :=
    stdGaussian (EuclideanSpace ℝ (Fin (n + n)))
  have hgh : GaussianCircularization.IndependentStandardGaussians
      (GaussianCircularization.doubledFamily
        (canonicalFirstCoords n) (canonicalSecondCoords n)) P := by
    rw [doubledFamily_canonicalCoords]
    exact doubledCanonicalCoords_standard n
  have hG := GaussianCutoffBridge.flat_gaussian_cutoff_lower_of_energy
    (Ω := EuclideanSpace ℝ (Fin (n + n))) (P := P)
    a hN0 k z (canonicalFirstCoords n) (canonicalSecondCoords n) hgh
    (gaussianRadius a N0 k) (endpointRadius k) (scaleEnergyBound a N0 k)
    (endpointScale k) (prefixScale a N0 k)
    (gaussianRadius_pos a hsmall N0 k) (endpointRadius_nonneg k) hruk
    (hcoordk z hz) (flatPhaseCoefficient_energy_le a hsmall hN0 k z hz)
    (by rw [endpointScale_endpointRadius])
    (by rw [prefixScale_gaussianRadius a hsmall]; norm_num)
  exact hqk.trans (by
    simpa only [gaussianRadius, endpointRadius, scaleEnergyBound,
      Nat.cast_add, Nat.cast_one] using hG)

/-- Concrete one-point replacement: eventually every unit phase has Rademacher
cutoff expectation at least the full branching target. -/
theorem eventually_onePointTarget_le_flat_rademacher_expectation
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) :
    ∀ᶠ k : ℕ in atTop, ∀ z : ℂ, ‖z‖ = 1 →
      BranchParameterArithmetic.onePointTarget k ≤
        ∫ x, SmoothCutoffC4.endpointPrefixCutoff
            (uniformBlockCount k) (endpointScale k) (prefixScale a N0 k)
            (CutoffLindebergBridge.NormedLindeberg.linearCombination
              (OnePointLindeberg.flatBlockIncrementDirection a hN0 k z) x)
          ∂Erdos88.Invariance.rademacherProductMeasure
            (scale N0 (k + 1) - scale N0 k) := by
  have hG := eventually_two_mul_onePointTarget_le_flat_gaussian_expectation
    a hsmall hN0
  have hE :=
    OnePointLindebergAsymptotic.eventually_flatOnePointLindebergError_le_target_half
      a hsmall hN0
  filter_upwards [hG, hE] with k hGk hEk z hz
  have hreplace := OnePointLindeberg.half_lower_bound_flat_rademacher_expectation
    a hsmall hN0 k z hz (endpointScale k) (prefixScale a N0 k)
      (2 * BranchParameterArithmetic.onePointTarget k) (hGk z hz) (by
        have hnonneg := BranchParameterArithmetic.onePointTarget_nonneg k
        have herr : OnePointLindeberg.flatOnePointLindebergError a N0 k
            (endpointScale k) (prefixScale a N0 k) ≤
            BranchParameterArithmetic.onePointTarget k / 2 := by
          simpa only [endpointScale, prefixScale,
            OnePointLindebergAsymptotic.concreteEndpointScale,
            OnePointLindebergAsymptotic.concretePrefixScale, Nat.cast_add,
            Nat.cast_one] using hEk
        linarith)
  convert hreplace using 1 <;> ring

theorem eventually_onePointTarget_le_flatWeight_integral
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) :
    ∀ᶠ k : ℕ in atTop, ∀ z : ℂ, ‖z‖ = 1 →
      BranchParameterArithmetic.onePointTarget k ≤
        ∫ x, FlatAliveGood.flatWeight a hN0 k z x
          ∂Erdos88.Invariance.rademacherProductMeasure
            (scale N0 (k + 1) - scale N0 k) := by
  filter_upwards [eventually_onePointTarget_le_flat_rademacher_expectation
      a hsmall hN0] with k hk z hz
  simpa only [FlatAliveGood.flatWeight, FlatAliveGood.flatEndpointScale,
    FlatAliveGood.flatPrefixScale, endpointScale, prefixScale, Nat.cast_add,
    Nat.cast_one] using hk z hz

end

end OnePointApplication
end Erdos527

namespace Erdos527
namespace FlatTransitionFailure

noncomputable section

open MeasureTheory

/-- A scale transition is bad exactly when its parent is quantitatively large
but its concrete flat-good children fail the next target. -/
def flatTransitionBad (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) :
    RecursiveAlive.LocalFailure N0 :=
  fun k A x =>
    BranchParameterArithmetic.targetSize k ≤ A.card ∧
      (FlatAliveGood.flatGoodTransition a hN0 k A x).card <
        BranchParameterArithmetic.targetSize (k + 1)

/-- Equality of the finite transition output to a fixed set is measurable.
The proof only uses the finite candidate set, avoiding any countability
assumption on the ambient phase space. -/
lemma measurableSet_flatGoodTransition_eq
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (A B : Finset ℂ) :
    MeasurableSet {x | FlatAliveGood.flatGoodTransition a hN0 k A x = B} := by
  let C := RecursiveAlive.scaleChildren N0 hN0 k A
  by_cases hB : B ⊆ C
  · rw [show {x | FlatAliveGood.flatGoodTransition a hN0 k A x = B} =
        ⋂ z ∈ C, if z ∈ B then
          {x | z ∈ FlatAliveGood.flatGoodTransition a hN0 k A x}
        else {x | z ∉ FlatAliveGood.flatGoodTransition a hN0 k A x} by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro heq z hzC
        by_cases hzB : z ∈ B
        · simp only [hzB, ↓reduceIte, Set.mem_setOf_eq]
          rwa [heq]
        · simp only [hzB, ↓reduceIte, Set.mem_setOf_eq]
          rwa [heq]
      · intro hz
        apply Finset.Subset.antisymm
        · intro z hzT
          have hzC : z ∈ C := by
            exact FlatAliveGood.flatGoodTransition_subset_candidates
              a hN0 k A x hzT
          have h := hz z hzC
          split_ifs at h with hzB
          · exact hzB
          · exact False.elim (h hzT)
        · intro z hzB
          have h := hz z (hB hzB)
          simp only [hzB, ↓reduceIte, Set.mem_setOf_eq] at h
          exact h]
    apply MeasurableSet.biInter C.finite_toSet.to_countable
    intro z hzC
    split_ifs
    · exact FlatAliveGood.measurableSet_mem_flatGoodTransition a hN0 k A z
    · exact (FlatAliveGood.measurableSet_mem_flatGoodTransition a hN0 k A z).compl
  · have hempty :
        {x | FlatAliveGood.flatGoodTransition a hN0 k A x = B} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro heq
      apply hB
      rw [← heq]
      exact FlatAliveGood.flatGoodTransition_subset_candidates a hN0 k A x
    rw [hempty]
    exact MeasurableSet.empty

/-- The concrete bad-transition predicate is measurable in the fresh finite
scale vector for every deterministic parent. -/
theorem flatTransitionBad_measurable (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) :
    RecursiveAlive.LocalFailureMeasurable (flatTransitionBad a hN0) := by
  intro k A
  by_cases hparent : BranchParameterArithmetic.targetSize k ≤ A.card
  · simp only [flatTransitionBad, hparent, true_and]
    let C := RecursiveAlive.scaleChildren N0 hN0 k A
    let small : Finset (Finset ℂ) :=
      C.powerset.filter fun B =>
        B.card < BranchParameterArithmetic.targetSize (k + 1)
    rw [show {x |
          (FlatAliveGood.flatGoodTransition a hN0 k A x).card <
            BranchParameterArithmetic.targetSize (k + 1)} =
        ⋃ B ∈ small,
          {x | FlatAliveGood.flatGoodTransition a hN0 k A x = B} by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter,
        Finset.mem_powerset, small]
      constructor
      · intro hcard
        refine ⟨FlatAliveGood.flatGoodTransition a hN0 k A x, ?_, rfl⟩
        exact ⟨FlatAliveGood.flatGoodTransition_subset_candidates
          a hN0 k A x, hcard⟩
      · rintro ⟨B, ⟨hBC, hcard⟩, heq⟩
        rwa [heq]]
    apply MeasurableSet.biUnion small.finite_toSet.to_countable
    intro B hB
    exact measurableSet_flatGoodTransition_eq a hN0 k A B
  · rw [show {x | flatTransitionBad a hN0 k A x} = ∅ by
      ext x
      simp [flatTransitionBad, hparent]]
    exact MeasurableSet.empty

/-- The recursive local-failure event is exactly the standard finite-grid
branching failure for the relative-time concrete alive process and the
correspondingly shifted target-size sequence. -/
theorem recursiveTransitionFailure_eq_finiteGridBranching
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (start t : ℕ) :
    RecursiveAlive.transitionFailure hN0 start
        (FlatAliveGood.flatGood a hN0) (flatTransitionBad a hN0) t =
      FiniteGridBranching.transitionFailure
        (FlatAliveGood.flatAlive a hN0 start)
        (fun u => BranchParameterArithmetic.targetSize (start + u)) t := by
  ext ε
  simp only [RecursiveAlive.transitionFailure, Set.mem_setOf_eq,
    flatTransitionBad, FiniteGridBranching.transitionFailure,
    FiniteGridBranching.StrongAt, Set.mem_diff]
  rw [show RecursiveAlive.aliveRel N0 hN0 start
        (FlatAliveGood.flatGood a hN0) t ε =
      FlatAliveGood.flatAlive a hN0 start t ε by rfl]
  rw [← FlatAliveGood.flatAlive_succ a hN0 start t ε]
  simp only [not_le]
  simp only [Nat.add_assoc]

/-- A uniform fixed-parent bound under the finite Rademacher law transfers to
the actual adaptive flat-alive transition in the infinite product. -/
theorem measure_finiteGridBranching_transitionFailure_le
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (start t : ℕ)
    (b : ℝ≥0∞)
    (hfixed : ∀ A,
      A ⊆ RecursiveAlive.rootGrid N0 hN0 (start + t) →
      Erdos88.Invariance.rademacherProductMeasure
          (scale N0 (start + t + 1) - scale N0 (start + t))
          {x | flatTransitionBad a hN0 (start + t) A x} ≤ b) :
    rademacherProductMeasure
        (FiniteGridBranching.transitionFailure
          (FlatAliveGood.flatAlive a hN0 start)
          (fun u => BranchParameterArithmetic.targetSize (start + u)) t) ≤ b := by
  rw [← recursiveTransitionFailure_eq_finiteGridBranching a hN0 start t]
  exact RecursiveAlive.measure_recursive_adaptive_failure_le
    hN0 start (FlatAliveGood.flatGood_measurable a hN0) t
    (fun A x => flatTransitionBad a hN0 (start + t) A x)
    (fun A hA => flatTransitionBad_measurable a hN0 (start + t) A)
    b hfixed

end

end FlatTransitionFailure
end Erdos527

open scoped BigOperators

namespace Erdos527.PairCorrelationApplication

open Filter

noncomputable section

open CorrelationCount

/-- The canonical root-grid index of a complex number; it is meaningful on the root grid. -/
noncomputable def rootIndex (q : ℕ) [NeZero q] (z : ℂ) : ZMod q :=
  if hz : z ∈ Grid.complexRootGrid q then
    Classical.choose (Finset.mem_image.mp hz)
  else 0

lemma rootIndex_spec (q : ℕ) [NeZero q] {z : ℂ}
    (hz : z ∈ Grid.complexRootGrid q) :
    Grid.complexGridPoint q (rootIndex q z) = z := by
  rw [rootIndex, dif_pos hz]
  exact (Classical.choose_spec (Finset.mem_image.mp hz)).2

/-- Additive unit-circle phase corresponding to a complex root-grid point. -/
noncomputable def phasePoint (q : ℕ) [NeZero q] (z : ℂ) : UnitAddCircle :=
  Grid.gridPoint q (rootIndex q z)

lemma phasePoint_separated (q : ℕ) [NeZero q] {z w : ℂ}
    (hz : z ∈ Grid.complexRootGrid q) (hw : w ∈ Grid.complexRootGrid q)
    (hzw : z ≠ w) :
    (1 : ℝ) / q ≤ dist (phasePoint q z) (phasePoint q w) := by
  apply Grid.one_div_natCast_le_gridPoint_dist
  intro hidx
  apply hzw
  rw [← rootIndex_spec q hz, ← rootIndex_spec q hw, hidx]

/-- Correlation on at least one flat uniform block of scale `k`. -/
def PairCorrelated (a : ℕ → ℝ) (N0 k : ℕ) (q : ℕ) [NeZero q]
    (ρ : ℝ) (z w : ℂ) : Prop :=
  ∃ r : Fin (uniformBlockCount k),
    IsCorrelated (fun n => (a n : ℂ))
      (uniformEndpoint N0 k r - 1) (uniformBlockLength N0 k)
      (phasePoint q z) (phasePoint q w) ρ

lemma Ioc_uniformEndpoint_sub_one_eq_uniformBlock
    {N0 : ℕ} (hN0 : 0 < N0) (k r : ℕ) :
    Finset.Ioc (uniformEndpoint N0 k r - 1)
      (uniformEndpoint N0 k r - 1 + uniformBlockLength N0 k) =
      uniformBlock N0 k r := by
  ext n
  have he : 0 < uniformEndpoint N0 k r :=
    (scale_pos hN0 k).trans_le (uniformBlock_start_ge_scale N0 k r)
  simp only [Finset.mem_Ioc, uniformBlock, Finset.mem_Ico, uniformEndpoint_succ]
  omega

lemma uniformIoc_start_ge_scale {N0 : ℕ} (hN0 : 0 < N0) (k r n : ℕ)
    (hn : n ∈ Finset.Ioc (uniformEndpoint N0 k r - 1)
      (uniformEndpoint N0 k r - 1 + uniformBlockLength N0 k)) :
    scale N0 k ≤ n := by
  have he : scale N0 k ≤ uniformEndpoint N0 k r :=
    uniformBlock_start_ge_scale N0 k r
  have hepos : 0 < uniformEndpoint N0 k r :=
    (scale_pos hN0 k).trans_le he
  simp only [Finset.mem_Ioc] at hn
  omega

lemma uniformBlockLength_le_scale (N0 k : ℕ) :
    uniformBlockLength N0 k ≤ scale N0 k := by
  rw [← uniformBlockLength_mul_parts N0 k]
  exact Nat.le_mul_of_pos_right _ (by positivity)

lemma uniformIoc_coefficient_sq_le
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) {k r n : ℕ}
    (henv : coefficientEnvelope a N0 k ≤ 1)
    (hn : n ∈ Finset.Ioc (uniformEndpoint N0 k r - 1)
      (uniformEndpoint N0 k r - 1 + uniformBlockLength N0 k)) :
    ‖(a n : ℂ)‖ ^ 2 ≤ (scale N0 k : ℝ)⁻¹ := by
  have hSn : scale N0 k ≤ n := uniformIoc_start_ge_scale hN0 k r n hn
  have hscaled : scaledAbs a n ≤ 1 :=
    (scaledAbs_le_coefficientEnvelope a hsmall hSn).trans henv
  have hs := sq_abs_le_div_of_scaled_le (scale_pos hN0 k) hSn (by norm_num) hscaled
  simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs, one_pow, one_div] using hs

lemma card_blockCorrelated_le
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) {k q : ℕ} [NeZero q]
    (C : Finset ℂ) (hC : C ⊆ Grid.complexRootGrid q)
    (henv : coefficientEnvelope a N0 k ≤ 1)
    (z : ℂ) {r : ℕ} {ρ : ℝ} (hρ : 0 < ρ) :
    ((correlatedIndices (fun n => (a n : ℂ))
      (uniformEndpoint N0 k r - 1) (uniformBlockLength N0 k)
      (phasePoint q z) (fun w : ↑C => phasePoint q w.1) ρ).card : ℝ) ≤
      4 * (ρ⁻¹) ^ 2 *
        ((uniformBlockLength N0 k : ℝ) + (q : ℝ)) *
        (uniformBlockLength N0 k : ℝ) * (scale N0 k : ℝ)⁻¹ ^ 2 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hδ : 0 < (1 : ℝ) / q := div_pos (by norm_num) hqR
  have hsep : ∀ (u v : ↑C), u ≠ v →
      (1 : ℝ) / q ≤ dist (phasePoint q u.1) (phasePoint q v.1) := by
    intro u v huv
    apply phasePoint_separated q (hC u.2) (hC v.2)
    intro huvval
    exact huv (Subtype.ext huvval)
  have hmain := card_correlatedIndices_le (fun n => (a n : ℂ))
    (uniformEndpoint N0 k r - 1) (uniformBlockLength N0 k) (scale N0 k)
    (uniformBlockLength_le_scale N0 k) (phasePoint q z)
    (fun w : ↑C => phasePoint q w.1) hδ hρ hsep
    (fun n hn => uniformIoc_coefficient_sq_le a hsmall hN0 henv hn)
  convert hmain using 1
  rw [one_div, inv_inv]

noncomputable def fixedPairCharge
    (a : ℕ → ℝ) (N0 k q : ℕ) [NeZero q] (ρ : ℝ) (C : Finset ℂ) (z : ℂ) : ℝ := by
  classical
  exact ∑ w ∈ C, if PairCorrelated a N0 k q ρ z w then 1 else 0

lemma sum_pairCorrelated_fixed_le_explicit
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) {k q : ℕ} [NeZero q]
    (C : Finset ℂ) (hC : C ⊆ Grid.complexRootGrid q)
    (henv : coefficientEnvelope a N0 k ≤ 1)
    (z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    fixedPairCharge a N0 k q ρ C z ≤
      (uniformBlockCount k : ℝ) *
        (4 * (ρ⁻¹) ^ 2 *
          ((uniformBlockLength N0 k : ℝ) + (q : ℝ)) *
          (uniformBlockLength N0 k : ℝ) * (scale N0 k : ℝ)⁻¹ ^ 2) := by
  classical
  unfold fixedPairCharge
  let blockCorr : Fin (uniformBlockCount k) → ↑C → Prop := fun r w =>
    IsCorrelated (fun n => (a n : ℂ))
      (uniformEndpoint N0 k r - 1) (uniformBlockLength N0 k)
      (phasePoint q z) (phasePoint q w.1) ρ
  calc
    (∑ w ∈ C, if PairCorrelated a N0 k q ρ z w then (1 : ℝ) else 0) =
        ∑ w : ↑C, if PairCorrelated a N0 k q ρ z w.1 then (1 : ℝ) else 0 := by
          exact Finset.sum_subtype C (fun _ => Iff.rfl) _
    _ ≤ ∑ w : ↑C, ∑ r : Fin (uniformBlockCount k),
        if blockCorr r w then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro w hw
      by_cases hp : PairCorrelated a N0 k q ρ z w.1
      · simp only [hp, if_true]
        rcases hp with ⟨r, hr⟩
        have hr' : blockCorr r w := hr
        calc
          (1 : ℝ) = if blockCorr r w then 1 else 0 := (if_pos hr').symm
          _ ≤ ∑ s : Fin (uniformBlockCount k),
              if blockCorr s w then 1 else 0 :=
            Finset.single_le_sum (s := Finset.univ)
              (f := fun s => if blockCorr s w then (1 : ℝ) else 0)
              (fun s _ => by positivity) (Finset.mem_univ r)
      · simp only [hp, if_false]
        positivity
    _ = ∑ r : Fin (uniformBlockCount k),
        ((correlatedIndices (fun n => (a n : ℂ))
          (uniformEndpoint N0 k r - 1) (uniformBlockLength N0 k)
          (phasePoint q z) (fun w : ↑C => phasePoint q w.1) ρ).card : ℝ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_boole]
      simp [blockCorr, correlatedIndices]
    _ ≤ ∑ _r : Fin (uniformBlockCount k),
        4 * (ρ⁻¹) ^ 2 *
          ((uniformBlockLength N0 k : ℝ) + (q : ℝ)) *
          (uniformBlockLength N0 k : ℝ) * (scale N0 k : ℝ)⁻¹ ^ 2 := by
      apply Finset.sum_le_sum
      intro r hr
      exact card_blockCorrelated_le a hsmall hN0 C hC henv z hρ
    _ = (uniformBlockCount k : ℝ) *
        (4 * (ρ⁻¹) ^ 2 *
          ((uniformBlockLength N0 k : ℝ) + (q : ℝ)) *
          (uniformBlockLength N0 k : ℝ) * (scale N0 k : ℝ)⁻¹ ^ 2) := by simp

lemma uniformCorrelationFactor_le_stepFactor_pow_ten
    {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) :
    (uniformBlockCount k : ℝ) *
        ((uniformBlockLength N0 k : ℝ) + (scale N0 (k + 1) : ℝ)) *
        (uniformBlockLength N0 k : ℝ) * (scale N0 k : ℝ)⁻¹ ^ 2 ≤
      ((2 ^ stepExponent k : ℕ) : ℝ) ^ 10 := by
  let R : ℝ := uniformBlockCount k
  let M : ℝ := uniformBlockLength N0 k
  let S : ℝ := scale N0 k
  let Q : ℝ := scale N0 (k + 1)
  let F : ℝ := 2 ^ stepExponent k
  have hS : 0 < S := by
    dsimp only [S]
    exact_mod_cast scale_pos hN0 k
  have hF : 2 ≤ F := by
    dsimp only [F]
    exact_mod_cast two_le_stepFactor k
  have hQ : Q = S * F := by
    dsimp only [Q, S, F]
    exact_mod_cast scale_succ N0 k
  have hRM : R * M = Q - S := by
    dsimp only [R, M, Q, S]
    rw [← Nat.cast_mul, ← scale_gap_eq_uniformBlockCount_mul_length,
      Nat.cast_sub (scale_monotone N0 (Nat.le_succ k))]
  have hMnonneg : 0 ≤ M := by positivity
  have hQnonneg : 0 ≤ Q := by positivity
  have hRMle : R * M ≤ Q := by rw [hRM]; linarith
  have hMleS : M ≤ S := by
    dsimp only [M, S]
    exact_mod_cast uniformBlockLength_le_scale N0 k
  have hSleQ : S ≤ Q := by
    rw [hQ]
    nlinarith
  have hMplusQ : M + Q ≤ 2 * Q := by linarith
  have hprod : R * (M + Q) * M ≤ 2 * Q ^ 2 := by
    calc
      R * (M + Q) * M = (R * M) * (M + Q) := by ring
      _ ≤ Q * (2 * Q) :=
        mul_le_mul hRMle hMplusQ (by positivity) hQnonneg
      _ = 2 * Q ^ 2 := by ring
  have hnormalized : R * (M + Q) * M * S⁻¹ ^ 2 ≤ 2 * F ^ 2 := by
    calc
      R * (M + Q) * M * S⁻¹ ^ 2 ≤ (2 * Q ^ 2) * S⁻¹ ^ 2 :=
        mul_le_mul_of_nonneg_right hprod (sq_nonneg _)
      _ = 2 * F ^ 2 := by
        rw [hQ]
        field_simp
  have hF8nat : (2 : ℕ) ≤ (2 ^ stepExponent k) ^ 8 := by
    calc
      2 ≤ 2 ^ stepExponent k := two_le_stepFactor k
      _ = (2 ^ stepExponent k) ^ 1 := by simp
      _ ≤ (2 ^ stepExponent k) ^ 8 :=
        Nat.pow_le_pow_right (by positivity) (by omega)
  have hF8 : (2 : ℝ) ≤ F ^ 8 := by
    dsimp only [F]
    exact_mod_cast hF8nat
  have hfinal : R * (M + Q) * M * S⁻¹ ^ 2 ≤ F ^ 10 := by
    calc
      R * (M + Q) * M * S⁻¹ ^ 2 ≤ 2 * F ^ 2 := hnormalized
      _ ≤ F ^ 8 * F ^ 2 := by gcongr
      _ = F ^ 10 := by ring
  simpa only [R, M, S, Q, F, Nat.cast_pow, Nat.cast_ofNat] using hfinal

lemma scale_fixedPairCharge_le
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (C : Finset ℂ) (hC : C ⊆ RecursiveAlive.rootGrid N0 hN0 (k + 1))
    (henv : coefficientEnvelope a N0 k ≤ 1)
    (z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    letI : NeZero (scale N0 (k + 1)) := ⟨scale_ne_zero hN0.ne' (k + 1)⟩
    fixedPairCharge a N0 k (scale N0 (k + 1)) ρ C z ≤
      4 * (ρ⁻¹) ^ 2 * (((2 ^ stepExponent k : ℕ) : ℝ) ^ 10) := by
  letI : NeZero (scale N0 (k + 1)) := ⟨scale_ne_zero hN0.ne' (k + 1)⟩
  have hC' : C ⊆ Grid.complexRootGrid (scale N0 (k + 1)) := by
    simpa only [RecursiveAlive.rootGrid] using hC
  have hraw := sum_pairCorrelated_fixed_le_explicit a hsmall hN0 C hC' henv z hρ
  have hfactor := uniformCorrelationFactor_le_stepFactor_pow_ten hN0 k
  calc
    fixedPairCharge a N0 k (scale N0 (k + 1)) ρ C z ≤
        (uniformBlockCount k : ℝ) *
          (4 * (ρ⁻¹) ^ 2 *
            ((uniformBlockLength N0 k : ℝ) + (scale N0 (k + 1) : ℝ)) *
            (uniformBlockLength N0 k : ℝ) * (scale N0 k : ℝ)⁻¹ ^ 2) := hraw
    _ = 4 * (ρ⁻¹) ^ 2 *
        ((uniformBlockCount k : ℝ) *
          ((uniformBlockLength N0 k : ℝ) + (scale N0 (k + 1) : ℝ)) *
          (uniformBlockLength N0 k : ℝ) * (scale N0 k : ℝ)⁻¹ ^ 2) := by ring
    _ ≤ 4 * (ρ⁻¹) ^ 2 * (((2 ^ stepExponent k : ℕ) : ℝ) ^ 10) := by
      exact mul_le_mul_of_nonneg_left hfactor (mul_nonneg (by norm_num) (sq_nonneg _))

/-- Scale-specialized correlation of two candidate complex roots. -/
noncomputable def scalePairCorrelated
    (a : ℕ → ℝ) (N0 : ℕ) (hN0 : 0 < N0) (k : ℕ) (ρ : ℝ)
    (z w : ℂ) : Prop := by
  letI : NeZero (scale N0 (k + 1)) := ⟨scale_ne_zero hN0.ne' (k + 1)⟩
  exact PairCorrelated a N0 k (scale N0 (k + 1)) ρ z w

/-- Ordered correlated-pair charge on a candidate set. -/
noncomputable def orderedPairCharge
    (a : ℕ → ℝ) (N0 : ℕ) (hN0 : 0 < N0) (k : ℕ) (ρ : ℝ)
    (C : Finset ℂ) : ℝ := by
  classical
  exact ∑ z ∈ C, ∑ w ∈ C, if scalePairCorrelated a N0 hN0 k ρ z w then 1 else 0

lemma orderedPairCharge_eq_sum_fixedPairCharge
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) (ρ : ℝ)
    (C : Finset ℂ) :
    orderedPairCharge a N0 hN0 k ρ C =
      letI : NeZero (scale N0 (k + 1)) := ⟨scale_ne_zero hN0.ne' (k + 1)⟩
      ∑ z ∈ C, fixedPairCharge a N0 k (scale N0 (k + 1)) ρ C z := by
  classical
  unfold orderedPairCharge fixedPairCharge scalePairCorrelated PairCorrelated
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro w hw
  split <;> simp_all

/-- Ordered pair-count consequence of the large sieve for a candidate subset of the exact
successor root grid. -/
theorem orderedPairCharge_le
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (C : Finset ℂ) (hC : C ⊆ RecursiveAlive.rootGrid N0 hN0 (k + 1))
    (henv : coefficientEnvelope a N0 k ≤ 1)
    {ρ : ℝ} (hρ : 0 < ρ) :
    orderedPairCharge a N0 hN0 k ρ C ≤
      4 * (C.card : ℝ) * (ρ⁻¹) ^ 2 * (((2 ^ stepExponent k : ℕ) : ℝ) ^ 10) := by
  letI : NeZero (scale N0 (k + 1)) := ⟨scale_ne_zero hN0.ne' (k + 1)⟩
  rw [orderedPairCharge_eq_sum_fixedPairCharge]
  calc
    (∑ z ∈ C, fixedPairCharge a N0 k (scale N0 (k + 1)) ρ C z) ≤
        ∑ _z ∈ C,
          4 * (ρ⁻¹) ^ 2 * (((2 ^ stepExponent k : ℕ) : ℝ) ^ 10) := by
      exact Finset.sum_le_sum fun z hz => scale_fixedPairCharge_le a hsmall hN0 k C hC henv z hρ
    _ = 4 * (C.card : ℝ) * (ρ⁻¹) ^ 2 *
        (((2 ^ stepExponent k : ℕ) : ℝ) ^ 10) := by
      simp
      ring

end


end Erdos527.PairCorrelationApplication

open MeasureTheory

noncomputable section

namespace PairSelectPi

variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace A] (μ : Measure A) [SigmaFinite μ] [IsProbabilityMeasure μ]

def selectPi (s : Finset ι) (p : (ι → A) × (ι → A)) : ι → A :=
  fun i ↦ if i ∈ s then p.2 i else p.1 i

lemma measurePreserving_selectPi (s : Finset ι) :
    MeasurePreserving (selectPi s)
      ((Measure.pi fun _ : ι ↦ μ).prod (Measure.pi fun _ : ι ↦ μ))
      (Measure.pi fun _ : ι ↦ μ) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow A A ι
  have he : MeasurePreserving e
      (Measure.pi fun _ : ι ↦ μ.prod μ)
      ((Measure.pi fun _ : ι ↦ μ).prod (Measure.pi fun _ : ι ↦ μ)) :=
    measurePreserving_arrowProdEquivProdArrow A A ι (fun _ ↦ μ) (fun _ ↦ μ)
  have hcoord : ∀ i : ι, MeasurePreserving
      (fun p : A × A ↦ if i ∈ s then p.2 else p.1) (μ.prod μ) μ := by
    intro i
    by_cases hi : i ∈ s
    · simpa [hi] using (measurePreserving_snd (μ := μ) (ν := μ))
    · simpa [hi] using (measurePreserving_fst (μ := μ) (ν := μ))
  have hp : MeasurePreserving
      (fun p : ι → A × A ↦ fun i ↦ if i ∈ s then (p i).2 else (p i).1)
      (Measure.pi fun _ : ι ↦ μ.prod μ) (Measure.pi fun _ : ι ↦ μ) :=
    measurePreserving_pi (fun _ : ι ↦ μ.prod μ) (fun _ : ι ↦ μ) hcoord
  have hc := hp.comp he.symm
  convert hc using 1
  funext p i
  rfl

lemma integral_selectPi {s : Finset ι} (F : (ι → A) → ℝ)
    (hF : AEStronglyMeasurable F (Measure.pi fun _ : ι ↦ μ)) :
    ∫ p : (ι → A) × (ι → A), F (selectPi s p)
        ∂((Measure.pi fun _ : ι ↦ μ).prod (Measure.pi fun _ : ι ↦ μ)) =
      ∫ x, F x ∂(Measure.pi fun _ : ι ↦ μ) := by
  let hmp := measurePreserving_selectPi μ s
  have hF' : AEStronglyMeasurable F
      (((Measure.pi fun _ : ι ↦ μ).prod (Measure.pi fun _ : ι ↦ μ)).map
        (selectPi s)) := by
    rw [hmp.map_eq]
    exact hF
  calc
    _ = ∫ y, F y ∂(((Measure.pi fun _ : ι ↦ μ).prod
          (Measure.pi fun _ : ι ↦ μ)).map (selectPi s)) :=
      (integral_map hmp.aemeasurable hF').symm
    _ = _ := by rw [hmp.map_eq]

/-- Simultaneously splice two independent output sequences from two independent
pairs of input sequences.  This keeps the two output sequences independent. -/
def selectPairPi (s : Finset ι)
    (p : ((ι → A) × (ι → A)) × ((ι → A) × (ι → A))) :
    (ι → A) × (ι → A) :=
  (fun i ↦ if i ∈ s then p.2.1 i else p.1.1 i,
   fun i ↦ if i ∈ s then p.2.2 i else p.1.2 i)

@[simp] lemma selectPairPi_fst_apply (s : Finset ι)
    (p : ((ι → A) × (ι → A)) × ((ι → A) × (ι → A))) (i : ι) :
    (selectPairPi s p).1 i = if i ∈ s then p.2.1 i else p.1.1 i := by
  rfl

@[simp] lemma selectPairPi_snd_apply (s : Finset ι)
    (p : ((ι → A) × (ι → A)) × ((ι → A) × (ι → A))) (i : ι) :
    (selectPairPi s p).2 i = if i ∈ s then p.2.2 i else p.1.2 i := by
  rfl

lemma measurePreserving_selectPairPi (s : Finset ι) :
    MeasurePreserving (selectPairPi s)
      (((Measure.pi fun _ : ι ↦ μ).prod (Measure.pi fun _ : ι ↦ μ)).prod
        ((Measure.pi fun _ : ι ↦ μ).prod (Measure.pi fun _ : ι ↦ μ)))
      ((Measure.pi fun _ : ι ↦ μ).prod (Measure.pi fun _ : ι ↦ μ)) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow A A ι
  have he : MeasurePreserving e
      (Measure.pi fun _ : ι ↦ μ.prod μ)
      ((Measure.pi fun _ : ι ↦ μ).prod (Measure.pi fun _ : ι ↦ μ)) :=
    measurePreserving_arrowProdEquivProdArrow A A ι (fun _ ↦ μ) (fun _ ↦ μ)
  have hpre := he.symm.prod he.symm
  have hsel : MeasurePreserving (selectPi s)
      ((Measure.pi fun _ : ι ↦ μ.prod μ).prod
        (Measure.pi fun _ : ι ↦ μ.prod μ))
      (Measure.pi fun _ : ι ↦ μ.prod μ) :=
    measurePreserving_selectPi (μ.prod μ) s
  have hc := he.comp (hsel.comp hpre)
  convert hc using 1
  funext p
  ext i <;>
    by_cases hi : i ∈ s <;>
    simp [selectPairPi, Function.comp_def, selectPi, e, hi,
      MeasurableEquiv.arrowProdEquivProdArrow,
      Equiv.arrowProdEquivProdArrow_apply,
      Equiv.arrowProdEquivProdArrow_symm_apply]

lemma integral_selectPairPi {s : Finset ι}
    (F : ((ι → A) × (ι → A)) → ℝ)
    (hF : AEStronglyMeasurable F
      ((Measure.pi fun _ : ι ↦ μ).prod (Measure.pi fun _ : ι ↦ μ))) :
    ∫ p, F (selectPairPi s p)
        ∂(((Measure.pi fun _ : ι ↦ μ).prod (Measure.pi fun _ : ι ↦ μ)).prod
          ((Measure.pi fun _ : ι ↦ μ).prod (Measure.pi fun _ : ι ↦ μ))) =
      ∫ p, F p ∂((Measure.pi fun _ : ι ↦ μ).prod
        (Measure.pi fun _ : ι ↦ μ)) := by
  let hmp := measurePreserving_selectPairPi μ s
  have hF' : AEStronglyMeasurable F
      ((((Measure.pi fun _ : ι ↦ μ).prod (Measure.pi fun _ : ι ↦ μ)).prod
        ((Measure.pi fun _ : ι ↦ μ).prod (Measure.pi fun _ : ι ↦ μ))).map
          (selectPairPi s)) := by
    rw [hmp.map_eq]
    exact hF
  calc
    _ = ∫ y, F y ∂((((Measure.pi fun _ : ι ↦ μ).prod
          (Measure.pi fun _ : ι ↦ μ)).prod
          ((Measure.pi fun _ : ι ↦ μ).prod
          (Measure.pi fun _ : ι ↦ μ))).map (selectPairPi s)) :=
      (integral_map hmp.aemeasurable hF').symm
    _ = _ := by rw [hmp.map_eq]

end PairSelectPi


namespace Erdos527.PairCanonicalHybrid

open scoped BigOperators ENNReal NNReal Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Finset
open PairFactorization OnePointLindeberg CorrelationCount FlatVectorAPI

noncomputable section

abbrev CoeffSpace (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The real coordinate vector of the coefficients in flat block `r`. -/
def blockCoordVector (a : ℕ → ℝ) (z : ℂ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (r : Fin (uniformBlockCount k)) (p : Bool) :
    CoeffSpace (scale N0 (k + 1) - scale N0 k) :=
  WithLp.toLp 2 fun i ↦
    if uniformBlockOfOffset hN0 k i = r then
      coord p ((a (scaleCoefficient N0 k i) : ℂ) * z ^ scaleCoefficient N0 k i)
    else 0

@[simp] lemma blockCoordVector_apply (a : ℕ → ℝ) (z : ℂ) {N0 : ℕ}
    (hN0 : 0 < N0) (k : ℕ) (r : Fin (uniformBlockCount k)) (p : Bool)
    (i : Fin (scale N0 (k + 1) - scale N0 k)) :
    blockCoordVector a z hN0 k r p i =
      if uniformBlockOfOffset hN0 k i = r then
        coord p ((a (scaleCoefficient N0 k i) : ℂ) * z ^ scaleCoefficient N0 k i)
      else 0 := rfl

lemma inner_blockCoordVector (a : ℕ → ℝ) (z w : ℂ) {N0 : ℕ}
    (hN0 : 0 < N0) (k : ℕ) (r s : Fin (uniformBlockCount k)) (p q : Bool) :
    inner ℝ (blockCoordVector a z hN0 k r p)
        (blockCoordVector a w hN0 k s q) =
      ∑ i,
        (if uniformBlockOfOffset hN0 k i = r then
          coord p ((a (scaleCoefficient N0 k i) : ℂ) * z ^ scaleCoefficient N0 k i)
        else 0) *
        (if uniformBlockOfOffset hN0 k i = s then
          coord q ((a (scaleCoefficient N0 k i) : ℂ) * w ^ scaleCoefficient N0 k i)
        else 0) := by
  rw [PiLp.inner_apply]
  simp only [blockCoordVector_apply, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma inner_blockCoordVector_ne (a : ℕ → ℝ) (z w : ℂ) {N0 : ℕ}
    (hN0 : 0 < N0) (k : ℕ) {r s : Fin (uniformBlockCount k)} (hrs : r ≠ s)
    (p q : Bool) :
    inner ℝ (blockCoordVector a z hN0 k r p)
        (blockCoordVector a w hN0 k s q) = 0 := by
  rw [inner_blockCoordVector]
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hir : uniformBlockOfOffset hN0 k i = r
  · have his : uniformBlockOfOffset hN0 k i ≠ s := fun h ↦ hrs (hir.symm.trans h)
    rw [if_pos hir, if_neg his, mul_zero]
  · rw [if_neg hir, zero_mul]

/-- The exact first-derivative operator budget of the two-phase cutoff. -/
def pairCutoffLipschitzNN (l : ℕ) (endpointScale prefixScale : ℝ) : ℝ≥0 :=
  ⟨SmoothCutoffC4.cutoffC4 *
      (∑ q : Fin 2 × Option (Fin l),
        ‖pairEndpointPrefixForms l endpointScale prefixScale q‖),
    mul_nonneg SmoothCutoffC4.cutoffC4_nonneg
      (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)⟩

lemma pairEndpointPrefixCutoff_lipschitz (l : ℕ)
    (endpointScale prefixScale : ℝ) :
    LipschitzWith (pairCutoffLipschitzNN l endpointScale prefixScale)
      (pairEndpointPrefixCutoff l endpointScale prefixScale) := by
  refine lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ) ?_ ?_
  · exact (pairEndpointPrefixCutoff_contDiff l endpointScale prefixScale).differentiable
      (by simp)
  · intro w
    have hreal :
        ‖fderiv ℝ (pairEndpointPrefixCutoff l endpointScale prefixScale) w‖ ≤
          SmoothCutoffC4.cutoffC4 *
            ∑ q : Fin 2 × Option (Fin l),
              ‖pairEndpointPrefixForms l endpointScale prefixScale q‖ := by
      change
        ‖fderiv ℝ (SmoothCutoffC4.cutoffProduct
          (Finset.univ : Finset (Fin 2 × Option (Fin l)))
          (pairEndpointPrefixForms l endpointScale prefixScale)) w‖ ≤ _
      rw [← norm_iteratedFDeriv_one]
      simpa using SmoothCutoffC4.norm_iteratedFDeriv_cutoffProduct_le
        (u := (Finset.univ : Finset (Fin 2 × Option (Fin l))))
        (pairEndpointPrefixForms l endpointScale prefixScale) w
        (by norm_num : 1 ≤ 4)
    exact_mod_cast hreal

/-- Insert four real coordinates (real/imaginary for the two phases) into one
flat-block coordinate. -/
def insertFour (l : ℕ) (j : Fin l) (t : EuclideanSpace ℝ (Fin 4)) :
    PairIncrementSpace l :=
  fun q r ↦ if r = j then
    if q = 0 then (t 0 : ℂ) + Complex.I * (t 1 : ℂ)
    else (t 2 : ℂ) + Complex.I * (t 3 : ℂ)
  else 0

lemma insertFour_sub (l : ℕ) (j : Fin l)
    (s t : EuclideanSpace ℝ (Fin 4)) :
    insertFour l j s - insertFour l j t = insertFour l j (s - t) := by
  ext q r
  by_cases hr : r = j
  · fin_cases q <;> simp [insertFour, hr, sub_eq_add_neg] <;> ring_nf
  · simp [insertFour, hr]

lemma norm_complex_pair_zero_one_le (t : EuclideanSpace ℝ (Fin 4)) :
    ‖(t 0 : ℂ) + Complex.I * (t 1 : ℂ)‖ ≤ ‖t‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg t), Complex.sq_norm,
    Complex.normSq_apply, EuclideanSpace.norm_sq_eq]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, mul_zero, Complex.I_im, mul_one, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, zero_mul, zero_add, Real.norm_eq_abs]
  rw [Fin.sum_univ_four]
  nlinarith [sq_nonneg |t 2|, sq_nonneg |t 3|, sq_abs (t 0), sq_abs (t 1)]

lemma norm_complex_pair_two_three_le (t : EuclideanSpace ℝ (Fin 4)) :
    ‖(t 2 : ℂ) + Complex.I * (t 3 : ℂ)‖ ≤ ‖t‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg t), Complex.sq_norm,
    Complex.normSq_apply, EuclideanSpace.norm_sq_eq]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, mul_zero, Complex.I_im, mul_one, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, zero_mul, zero_add, Real.norm_eq_abs]
  rw [Fin.sum_univ_four]
  nlinarith [sq_nonneg |t 0|, sq_nonneg |t 1|, sq_abs (t 2), sq_abs (t 3)]

lemma norm_insertFour_le (l : ℕ) (j : Fin l) (t : EuclideanSpace ℝ (Fin 4)) :
    ‖insertFour l j t‖ ≤ ‖t‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg t)]
  intro q
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg t)]
  intro r
  by_cases hr : r = j
  · fin_cases q
    · simpa [insertFour, hr] using norm_complex_pair_zero_one_le t
    · simpa [insertFour, hr] using norm_complex_pair_two_three_le t
  · simp [insertFour, hr, norm_nonneg t]

lemma insertFour_lipschitz (l : ℕ) (j : Fin l) :
    LipschitzWith 1 (insertFour l j) := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro s t
  rw [insertFour_sub]
  simpa using norm_insertFour_le l j (s - t)

/-- The four-coordinate conditional cutoff obtained by averaging over a
random contribution from all other flat blocks. -/
def conditionalPairCutoff {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (l : ℕ) (j : Fin l) (endpointScale prefixScale : ℝ)
    (base : Ω → PairIncrementSpace l) (t : EuclideanSpace ℝ (Fin 4)) : ℝ :=
  ∫ ω, pairEndpointPrefixCutoff l endpointScale prefixScale
    (base ω + insertFour l j t) ∂P

lemma conditionalPairCutoff_integrand_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (l : ℕ) (j : Fin l) (endpointScale prefixScale : ℝ)
    (base : Ω → PairIncrementSpace l) (hbase : Measurable base)
    (t : EuclideanSpace ℝ (Fin 4)) :
    Measurable (fun ω ↦ pairEndpointPrefixCutoff l endpointScale prefixScale
      (base ω + insertFour l j t)) :=
  (pairEndpointPrefixCutoff_contDiff l endpointScale prefixScale).continuous.measurable.comp
    (hbase.add measurable_const)

lemma conditionalPairCutoff_integrand_norm_le_one
    {Ω : Type*} [MeasurableSpace Ω]
    (l : ℕ) (j : Fin l) (endpointScale prefixScale : ℝ)
    (base : Ω → PairIncrementSpace l)
    (t : EuclideanSpace ℝ (Fin 4)) (ω : Ω) :
    ‖pairEndpointPrefixCutoff l endpointScale prefixScale
      (base ω + insertFour l j t)‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg
    (pairEndpointPrefixCutoff_nonneg l endpointScale prefixScale _)]
  exact pairEndpointPrefixCutoff_le_one l endpointScale prefixScale _

lemma conditionalPairCutoff_integrand_lipschitz
    {Ω : Type*} [MeasurableSpace Ω]
    (l : ℕ) (j : Fin l) (endpointScale prefixScale : ℝ)
    (base : Ω → PairIncrementSpace l) (ω : Ω) :
    LipschitzWith (pairCutoffLipschitzNN l endpointScale prefixScale)
      (fun t : EuclideanSpace ℝ (Fin 4) ↦
        pairEndpointPrefixCutoff l endpointScale prefixScale
          (base ω + insertFour l j t)) := by
  have htrans : LipschitzWith 1
      (fun t : EuclideanSpace ℝ (Fin 4) ↦ base ω + insertFour l j t) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    simpa only [one_mul, dist_eq_norm, add_sub_add_left_eq_sub] using
      (insertFour_lipschitz l j).dist_le_mul s t
  simpa [Function.comp_def] using
    (pairEndpointPrefixCutoff_lipschitz l endpointScale prefixScale).comp htrans

lemma conditionalPairCutoff_lipschitz {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (l : ℕ) (j : Fin l) (endpointScale prefixScale : ℝ)
    (base : Ω → PairIncrementSpace l) (hbase : Measurable base) :
    LipschitzWith (pairCutoffLipschitzNN l endpointScale prefixScale)
      (conditionalPairCutoff P l j endpointScale prefixScale base) := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro s t
  rw [Real.norm_eq_abs, conditionalPairCutoff, conditionalPairCutoff]
  have hpoint (ω : Ω) :
      |pairEndpointPrefixCutoff l endpointScale prefixScale
          (base ω + insertFour l j s) -
        pairEndpointPrefixCutoff l endpointScale prefixScale
          (base ω + insertFour l j t)| ≤
        (pairCutoffLipschitzNN l endpointScale prefixScale : ℝ) *
          ‖insertFour l j s - insertFour l j t‖ := by
    simpa using (pairEndpointPrefixCutoff_lipschitz l endpointScale prefixScale).norm_sub_le
      (base ω + insertFour l j s) (base ω + insertFour l j t)
  let fs : Ω → ℝ := fun ω ↦ pairEndpointPrefixCutoff l endpointScale prefixScale
    (base ω + insertFour l j s)
  let ft : Ω → ℝ := fun ω ↦ pairEndpointPrefixCutoff l endpointScale prefixScale
    (base ω + insertFour l j t)
  have hmeas (u : EuclideanSpace ℝ (Fin 4)) : Measurable
      (fun ω ↦ pairEndpointPrefixCutoff l endpointScale prefixScale
        (base ω + insertFour l j u)) :=
    (pairEndpointPrefixCutoff_contDiff l endpointScale prefixScale).continuous.measurable.comp
      (hbase.add measurable_const)
  have hint (u : EuclideanSpace ℝ (Fin 4)) : Integrable
      (fun ω ↦ pairEndpointPrefixCutoff l endpointScale prefixScale
        (base ω + insertFour l j u)) P := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) (hmeas u).aestronglyMeasurable
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg
      (pairEndpointPrefixCutoff_nonneg l endpointScale prefixScale _)]
    exact pairEndpointPrefixCutoff_le_one l endpointScale prefixScale _
  rw [← integral_sub (hint s) (hint t)]
  calc
    |∫ ω, (fs ω - ft ω) ∂P| ≤ ∫ ω, |fs ω - ft ω| ∂P :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _ω, (pairCutoffLipschitzNN l endpointScale prefixScale : ℝ) *
          ‖insertFour l j s - insertFour l j t‖ ∂P := by
      apply integral_mono (hint s |>.sub (hint t) |>.abs) (integrable_const _)
      intro ω
      exact hpoint ω
    _ = (pairCutoffLipschitzNN l endpointScale prefixScale : ℝ) *
          ‖insertFour l j s - insertFour l j t‖ := by simp
    _ ≤ (pairCutoffLipschitzNN l endpointScale prefixScale : ℝ) *
          ‖s - t‖ := by
      gcongr
      rw [insertFour_sub]
      exact norm_insertFour_le l j (s - t)

/-- After all other flat blocks have been averaged out, replacing the two
phase coordinates of block `j` by independent copies is literally the
four-coordinate Gaussian discrepancy used by `GaussianDecoupling`. -/
lemma gaussianPairDiscrepancy_conditionalPairCutoff
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (l : ℕ) (j : Fin l) (endpointScale prefixScale : ℝ)
    (base : Ω → PairIncrementSpace l)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    (x₀ x₁ y₀ y₁ : H) :
    GaussianDecoupling.gaussianPairDiscrepancy x₀ x₁ y₀ y₁
        (conditionalPairCutoff P l j endpointScale prefixScale base) =
      abs ((∫ z : PiLp 2 (fun _ : Fin 2 ↦ H),
          ∫ ω, pairEndpointPrefixCutoff l endpointScale prefixScale
            (base ω + insertFour l j
              (GaussianDecoupling.innerFamilyCLM
                (![GaussianDecoupling.pairL2 x₀ 0,
                   GaussianDecoupling.pairL2 x₁ 0,
                   GaussianDecoupling.pairL2 y₀ 0,
                   GaussianDecoupling.pairL2 y₁ 0] :
                    Fin 4 → PiLp 2 (fun _ : Fin 2 ↦ H)) z)) ∂P
          ∂(stdGaussian (PiLp 2 (fun _ : Fin 2 ↦ H)))) -
        ∫ z : PiLp 2 (fun _ : Fin 2 ↦ H),
          ∫ ω, pairEndpointPrefixCutoff l endpointScale prefixScale
            (base ω + insertFour l j
              (GaussianDecoupling.innerFamilyCLM
                (![GaussianDecoupling.pairL2 x₀ 0,
                   GaussianDecoupling.pairL2 x₁ 0,
                   GaussianDecoupling.pairL2 0 y₀,
                   GaussianDecoupling.pairL2 0 y₁] :
                    Fin 4 → PiLp 2 (fun _ : Fin 2 ↦ H)) z)) ∂P
          ∂(stdGaussian (PiLp 2 (fun _ : Fin 2 ↦ H)))) := by
  rfl

end
end Erdos527.PairCanonicalHybrid


namespace Erdos527.PairHybridAlgebra

open scoped BigOperators
open Finset
open OnePointLindeberg CutoffLindebergBridge

noncomputable section

/-- Replace exactly the coefficient coordinates belonging to flat block `j`. -/
def spliceScaleBlock {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (j : Fin (uniformBlockCount k))
    (context fresh : Fin (scale N0 (k + 1) - scale N0 k) → ℝ) :
    Fin (scale N0 (k + 1) - scale N0 k) → ℝ :=
  fun i ↦ if uniformBlockOfOffset hN0 k i = j then fresh i else context i

lemma linearCombination_spliceScaleBlock
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) (z : ℂ)
    (j r : Fin (uniformBlockCount k))
    (context fresh : Fin (scale N0 (k + 1) - scale N0 k) → ℝ) :
    NormedLindeberg.linearCombination
        (flatBlockIncrementDirection a hN0 k z)
        (spliceScaleBlock hN0 k j context fresh) r =
      if r = j then
        NormedLindeberg.linearCombination
          (flatBlockIncrementDirection a hN0 k z) fresh r
      else
        NormedLindeberg.linearCombination
          (flatBlockIncrementDirection a hN0 k z) context r := by
  simp only [flat_linearCombination_apply]
  by_cases hrj : r = j
  · subst j
    rw [if_pos rfl]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_filter] at hi
    rw [spliceScaleBlock, if_pos hi.2]
  · rw [if_neg hrj]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_filter] at hi
    have hij : uniformBlockOfOffset hN0 k i ≠ j := by
      intro h
      exact hrj (hi.2.symm.trans h)
    rw [spliceScaleBlock, if_neg hij]

/-- The hybrid outside block `j`: phase zero uses `g`; phase one uses `h`
below `j` and `g` above `j`, while block `j` itself is zeroed. -/
def hybridContext
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) (zx zy : ℂ)
    (j : Fin (uniformBlockCount k))
    (g h : Fin (scale N0 (k + 1) - scale N0 k) → ℝ) :
    PairFactorization.PairIncrementSpace (uniformBlockCount k) :=
  fun q r ↦ if r = j then 0 else if q = 0 then
    NormedLindeberg.linearCombination
      (flatBlockIncrementDirection a hN0 k zx) g r
  else if r.val < j.val then
    NormedLindeberg.linearCombination
      (flatBlockIncrementDirection a hN0 k zy) h r
  else
    NormedLindeberg.linearCombination
      (flatBlockIncrementDirection a hN0 k zy) g r

/-- Four real coordinates of the current block. -/
def localBlockFour
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) (zx zy : ℂ)
    (j : Fin (uniformBlockCount k))
    (gx gy : Fin (scale N0 (k + 1) - scale N0 k) → ℝ) :
    EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![
    CorrelationCount.coord false
      (NormedLindeberg.linearCombination
        (flatBlockIncrementDirection a hN0 k zx) gx j),
    CorrelationCount.coord true
      (NormedLindeberg.linearCombination
        (flatBlockIncrementDirection a hN0 k zx) gx j),
    CorrelationCount.coord false
      (NormedLindeberg.linearCombination
        (flatBlockIncrementDirection a hN0 k zy) gy j),
    CorrelationCount.coord true
      (NormedLindeberg.linearCombination
        (flatBlockIncrementDirection a hN0 k zy) gy j)]

def insertLocalFour (l : ℕ) (j : Fin l) (t : EuclideanSpace ℝ (Fin 4)) :
    PairFactorization.PairIncrementSpace l :=
  fun q r ↦ if r = j then
    if q = 0 then (t 0 : ℂ) + Complex.I * (t 1 : ℂ)
    else (t 2 : ℂ) + Complex.I * (t 3 : ℂ)
  else 0

def flatGaussianHybrid
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) (zx zy : ℂ)
    (t : ℕ) (g h : Fin (scale N0 (k + 1) - scale N0 k) → ℝ) :
    PairFactorization.PairIncrementSpace (uniformBlockCount k) :=
  fun q r ↦ if q = 0 then
    NormedLindeberg.linearCombination
      (flatBlockIncrementDirection a hN0 k zx) g r
  else if r.val < t then
    NormedLindeberg.linearCombination
      (flatBlockIncrementDirection a hN0 k zy) h r
  else
    NormedLindeberg.linearCombination
      (flatBlockIncrementDirection a hN0 k zy) g r

/-- Reconstructing a complex block entry from its real and imaginary
coordinates. -/
lemma complex_coord_reconstruct (z : ℂ) :
    (CorrelationCount.coord false z : ℂ) +
        Complex.I * (CorrelationCount.coord true z : ℂ) = z := by
  apply Complex.ext <;> simp [CorrelationCount.coord]

lemma flatGaussianHybrid_splice_current_correlated
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) (zx zy : ℂ)
    (j : Fin (uniformBlockCount k))
    (g h freshG freshH : Fin (scale N0 (k + 1) - scale N0 k) → ℝ) :
    flatGaussianHybrid a hN0 k zx zy j.val
        (spliceScaleBlock hN0 k j g freshG)
        (spliceScaleBlock hN0 k j h freshH) =
      hybridContext a hN0 k zx zy j g h +
        insertLocalFour (uniformBlockCount k) j
          (localBlockFour a hN0 k zx zy j freshG freshG) := by
  ext q r
  fin_cases q
  · by_cases hr : r = j
    · subst r
      simp only [flatGaussianHybrid, if_pos, hybridContext, Pi.add_apply,
        insertLocalFour, localBlockFour, PiLp.toLp_apply, Matrix.cons_val_zero,
        zero_add]
      rw [linearCombination_spliceScaleBlock a hN0 k zx j j g freshG]
      simpa using (complex_coord_reconstruct
        (NormedLindeberg.linearCombination
          (flatBlockIncrementDirection a hN0 k zx) freshG j)).symm
    · simp only [flatGaussianHybrid, if_pos, hybridContext, hr, if_false,
        Pi.add_apply, insertLocalFour, zero_add]
      rw [linearCombination_spliceScaleBlock]
      simp [hr]
  · by_cases hr : r = j
    · subst r
      simp only [flatGaussianHybrid, Fin.isValue, OfNat.ofNat_ne_zero, if_false,
        lt_self_iff_false, hybridContext, if_pos, Pi.add_apply, insertLocalFour,
        localBlockFour, PiLp.toLp_apply, Matrix.cons_val_one, zero_add]
      rw [linearCombination_spliceScaleBlock a hN0 k zy j j g freshG]
      simpa using (complex_coord_reconstruct
        (NormedLindeberg.linearCombination
          (flatBlockIncrementDirection a hN0 k zy) freshG j)).symm
    · simp only [flatGaussianHybrid, Fin.isValue, OfNat.ofNat_ne_zero, if_false,
        hybridContext, hr, Pi.add_apply, insertLocalFour, zero_add]
      by_cases hlt : r.val < j.val
      · simp only [hlt, if_true]
        rw [linearCombination_spliceScaleBlock a hN0 k zy j r h freshH]
        simp [hr]
      · simp only [hlt, if_false]
        rw [linearCombination_spliceScaleBlock a hN0 k zy j r g freshG]
        simp [hr]

lemma flatGaussianHybrid_splice_current_independent
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) (zx zy : ℂ)
    (j : Fin (uniformBlockCount k))
    (g h freshG freshH : Fin (scale N0 (k + 1) - scale N0 k) → ℝ) :
    flatGaussianHybrid a hN0 k zx zy (j.val + 1)
        (spliceScaleBlock hN0 k j g freshG)
        (spliceScaleBlock hN0 k j h freshH) =
      hybridContext a hN0 k zx zy j g h +
        insertLocalFour (uniformBlockCount k) j
          (localBlockFour a hN0 k zx zy j freshG freshH) := by
  ext q r
  fin_cases q
  · by_cases hr : r = j
    · subst r
      simp only [flatGaussianHybrid, if_pos, hybridContext, Pi.add_apply,
        insertLocalFour, localBlockFour, PiLp.toLp_apply, Matrix.cons_val_zero,
        zero_add]
      rw [linearCombination_spliceScaleBlock a hN0 k zx j j g freshG]
      simpa using (complex_coord_reconstruct
        (NormedLindeberg.linearCombination
          (flatBlockIncrementDirection a hN0 k zx) freshG j)).symm
    · simp only [flatGaussianHybrid, if_pos, hybridContext, hr, if_false,
        Pi.add_apply, insertLocalFour, zero_add]
      rw [linearCombination_spliceScaleBlock]
      simp [hr]
  · by_cases hr : r = j
    · subst r
      simp only [flatGaussianHybrid, Fin.isValue, OfNat.ofNat_ne_zero, if_false,
        Nat.lt_add_one, hybridContext, if_pos, Pi.add_apply, insertLocalFour,
        localBlockFour, PiLp.toLp_apply, Matrix.cons_val_one, zero_add]
      rw [linearCombination_spliceScaleBlock a hN0 k zy j j h freshH]
      simpa using (complex_coord_reconstruct
        (NormedLindeberg.linearCombination
          (flatBlockIncrementDirection a hN0 k zy) freshH j)).symm
    · simp only [flatGaussianHybrid, Fin.isValue, OfNat.ofNat_ne_zero, if_false,
        hybridContext, hr, Pi.add_apply, insertLocalFour, zero_add]
      have hiff : r.val < j.val + 1 ↔ r.val < j.val := by omega
      rw [if_congr hiff rfl rfl]
      by_cases hlt : r.val < j.val
      · simp only [hlt, if_true]
        rw [linearCombination_spliceScaleBlock a hN0 k zy j r h freshH]
        simp [hr]
      · simp only [hlt, if_false]
        rw [linearCombination_spliceScaleBlock a hN0 k zy j r g freshG]
        simp [hr]

end
end Erdos527.PairHybridAlgebra


namespace Erdos527.GaussianDecoupling

open scoped ENNReal NNReal Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Finset

noncomputable section

set_option backward.isDefEq.respectTransparency false in
lemma map_innerFamilyCLM_stdGaussian_eq_of_cross_gram_eq
    {H₁ H₂ ι : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [FiniteDimensional ℝ H₁] [MeasurableSpace H₁] [BorelSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
    [FiniteDimensional ℝ H₂] [MeasurableSpace H₂] [BorelSpace H₂]
    [Fintype ι] [DecidableEq ι] (c : ι → H₁) (d : ι → H₂)
    (hgram : ∀ i j, inner ℝ (c i) (c j) = inner ℝ (d i) (d j)) :
    (stdGaussian H₁).map (innerFamilyCLM c) =
      (stdGaussian H₂).map (innerFamilyCLM d) := by
  apply IsGaussian.ext
  · rw [integral_map (by fun_prop) (by fun_prop),
      integral_map (by fun_prop) (by fun_prop)]
    simp only [id_eq]
    rw [(innerFamilyCLM c).integral_comp_id_comm IsGaussian.integrable_id,
      (innerFamilyCLM d).integral_comp_id_comm IsGaussian.integrable_id,
      integral_id_stdGaussian, integral_id_stdGaussian]
    simp
  rw [← ContinuousLinearMap.toBilinForm_inj]
  refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun ι ℝ).toBasis fun i j ↦ ?_
  simp only [ContinuousLinearMap.toBilinForm_apply]
  rw [covarianceBilin_map IsGaussian.memLp_two_id,
    covarianceBilin_map IsGaussian.memLp_two_id,
    covarianceBilin_stdGaussian, covarianceBilin_stdGaussian]
  have hadj₁ (e : ι → H₁) (k : ι) :
      ContinuousLinearMap.adjoint (innerFamilyCLM e)
          ((EuclideanSpace.basisFun ι ℝ).toBasis k) = e k := by
    apply ext_inner_right ℝ
    intro x
    rw [ContinuousLinearMap.adjoint_inner_left]
    simp [innerFamilyCLM_apply, PiLp.inner_apply]
  have hadj₂ (e : ι → H₂) (k : ι) :
      ContinuousLinearMap.adjoint (innerFamilyCLM e)
          ((EuclideanSpace.basisFun ι ℝ).toBasis k) = e k := by
    apply ext_inner_right ℝ
    intro x
    rw [ContinuousLinearMap.adjoint_inner_left]
    simp [innerFamilyCLM_apply, PiLp.inner_apply]
  rw [hadj₁ c i, hadj₁ c j, hadj₂ d i, hadj₂ d j]
  exact hgram i j

lemma integral_innerFamilyCLM_stdGaussian_eq_of_cross_gram_eq
    {H₁ H₂ ι : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [FiniteDimensional ℝ H₁] [MeasurableSpace H₁] [BorelSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
    [FiniteDimensional ℝ H₂] [MeasurableSpace H₂] [BorelSpace H₂]
    [Fintype ι] [DecidableEq ι] (c : ι → H₁) (d : ι → H₂)
    (hgram : ∀ i j, inner ℝ (c i) (c j) = inner ℝ (d i) (d j))
    (f : EuclideanSpace ℝ ι → ℝ) (hf : Measurable f) :
    ∫ x : H₁, f (innerFamilyCLM c x) ∂(stdGaussian H₁) =
      ∫ x : H₂, f (innerFamilyCLM d x) ∂(stdGaussian H₂) := by
  calc
    _ = ∫ y, f y ∂((stdGaussian H₁).map (innerFamilyCLM c)) := by
      exact (integral_map (by fun_prop) hf.aestronglyMeasurable).symm
    _ = ∫ y, f y ∂((stdGaussian H₂).map (innerFamilyCLM d)) := by
      rw [map_innerFamilyCLM_stdGaussian_eq_of_cross_gram_eq c d hgram]
    _ = _ := by
      exact integral_map (by fun_prop) hf.aestronglyMeasurable

end
end Erdos527.GaussianDecoupling


namespace Erdos527.PairTwoCopyTransport

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory WithLp
open GaussianDecoupling

noncomputable section

lemma stdGaussian_prod_map_toLp
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] :
    ((stdGaussian H).prod (stdGaussian H)).map (toLp 2) =
      stdGaussian (WithLp 2 (H × H)) := by
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_prod, charFun_stdGaussian, charFun_stdGaussian,
    charFun_stdGaussian, ← Complex.exp_add]
  congr 1
  norm_cast
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp only [WithLp.fst, WithLp.snd]
  ring

/-- The canonical linear isometry from an L² product to a two-coordinate
Pi-L² space. -/
def prodLpToPairL2
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] :
    WithLp 2 (H × H) ≃ₗᵢ[ℝ] PiLp 2 (fun _ : Fin 2 ↦ H) where
  toLinearEquiv :=
    (WithLp.linearEquiv 2 ℝ (H × H)).trans
      ((LinearEquiv.finTwoArrow ℝ H).symm.trans
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ H)).symm.toLinearEquiv)
  norm_map' x := by
    rw [WithLp.prod_norm_eq_of_L2, PiLp.norm_eq_of_L2]
    simp [Fin.sum_univ_two]

@[simp] lemma prodLpToPairL2_apply_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x : WithLp 2 (H × H)) :
    prodLpToPairL2 x 0 = x.fst := rfl

@[simp] lemma prodLpToPairL2_apply_one
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x : WithLp 2 (H × H)) :
    prodLpToPairL2 x 1 = x.snd := rfl

lemma map_stdGaussian_prod_pairL2
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] :
    ((stdGaussian H).prod (stdGaussian H)).map
        (fun p ↦ pairL2 p.1 p.2) =
      stdGaussian (PiLp 2 (fun _ : Fin 2 ↦ H)) := by
  calc
    _ = ((stdGaussian H).prod (stdGaussian H)).map
          ((prodLpToPairL2 (H := H)) ∘ toLp 2) := by
      apply Measure.map_congr
      filter_upwards with p
      ext q
      fin_cases q <;> rfl
    _ = (Measure.map (toLp 2)
          ((stdGaussian H).prod (stdGaussian H))).map
          (prodLpToPairL2 (H := H)) :=
      (Measure.map_map (prodLpToPairL2 (H := H)).continuous.measurable
        (MeasurableEquiv.toLp 2 (H × H)).measurable).symm
    _ = (stdGaussian (WithLp 2 (H × H))).map
          (prodLpToPairL2 (H := H)) := by
      rw [stdGaussian_prod_map_toLp]
    _ = _ := stdGaussian_map (prodLpToPairL2 (H := H))

def concreteTwoCopiesToPairL2 (n : ℕ)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    PiLp 2 (fun _ : Fin 2 ↦ EuclideanSpace ℝ (Fin n)) :=
  pairL2 (toLp 2 p.1) (toLp 2 p.2)

lemma map_concreteTwoCopiesToPairL2 (n : ℕ) :
    ((Erdos88.Invariance.gaussianProductMeasure n).prod
      (Erdos88.Invariance.gaussianProductMeasure n)).map
        (concreteTwoCopiesToPairL2 n) =
      stdGaussian (PiLp 2
        (fun _ : Fin 2 ↦ EuclideanSpace ℝ (Fin n))) := by
  let μ := Erdos88.Invariance.gaussianProductMeasure n
  let H := EuclideanSpace ℝ (Fin n)
  have hmap : μ.map (toLp 2) = stdGaussian H := by
    exact map_pi_eq_stdGaussian
  have hp := (MeasurePreserving.mk
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable hmap).prod
      (MeasurePreserving.mk
        (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable hmap)
  have hprod : (μ.prod μ).map (Prod.map (toLp 2) (toLp 2)) =
      (stdGaussian H).prod (stdGaussian H) := hp.map_eq
  have hpair : Measurable (fun p : H × H ↦ pairL2 p.1 p.2) := by
    have heq : (fun p : H × H ↦ pairL2 p.1 p.2) =
        fun p ↦ prodLpToPairL2 (toLp 2 p) := by
      funext p
      ext q
      fin_cases q <;> rfl
    rw [heq]
    fun_prop
  calc
    _ = (μ.prod μ).map
          ((fun p : H × H ↦ pairL2 p.1 p.2) ∘
            Prod.map (toLp 2) (toLp 2)) := by
      apply Measure.map_congr
      filter_upwards with p
      rfl
    _ = ((μ.prod μ).map (Prod.map (toLp 2) (toLp 2))).map
          (fun p : H × H ↦ pairL2 p.1 p.2) :=
      (Measure.map_map hpair hp.measurable).symm
    _ = ((stdGaussian H).prod (stdGaussian H)).map
          (fun p : H × H ↦ pairL2 p.1 p.2) := by rw [hprod]
    _ = _ := map_stdGaussian_prod_pairL2 (H := H)

end
end Erdos527.PairTwoCopyTransport


namespace Erdos527.DirectGaussianPair

open scoped BigOperators ENNReal NNReal Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Finset
open WithLp
open CutoffLindebergBridge PairFactorization GaussianDecoupling
open SmoothCutoffC4
open CorrelationCount

noncomputable section

/-- The concrete product Gaussian used by the Lindeberg argument is the
standard Gaussian after applying the canonical `L²` coercion. -/
lemma map_gaussianProductMeasure_toLp (n : ℕ) :
    (Erdos88.Invariance.gaussianProductMeasure n).map (toLp 2) =
      stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  exact map_pi_eq_stdGaussian

lemma integral_gaussianProductMeasure_toLp {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : AEStronglyMeasurable F (stdGaussian (EuclideanSpace ℝ (Fin n)))) :
    ∫ x, F (toLp 2 x) ∂Erdos88.Invariance.gaussianProductMeasure n =
      ∫ z, F z ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  rw [← map_gaussianProductMeasure_toLp n]
  have hF' : AEStronglyMeasurable F
      ((Erdos88.Invariance.gaussianProductMeasure n).map (toLp 2)) := by
    rw [map_gaussianProductMeasure_toLp]
    exact hF
  exact (integral_map
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable.aemeasurable hF').symm

/-- The row vector giving one real coordinate of one complex block
increment. -/
def coordinateRow {n l : ℕ} (v : Fin n → Fin l → ℂ)
    (r : Fin l) (q : Bool) : EuclideanSpace ℝ (Fin n) :=
  toLp 2 (fun i ↦ coord q (v i r))

@[simp] lemma coordinateRow_apply {n l : ℕ} (v : Fin n → Fin l → ℂ)
    (r : Fin l) (q : Bool) (i : Fin n) :
    coordinateRow v r q i = coord q (v i r) := by
  rfl

lemma coord_linearCombination_eq_inner_coordinateRow {n l : ℕ}
    (v : Fin n → Fin l → ℂ) (x : Fin n → ℝ)
    (r : Fin l) (q : Bool) :
    coord q
        (NormedLindeberg.linearCombination v x r) =
      inner ℝ (coordinateRow v r q) (toLp 2 x) := by
  rw [PiLp.inner_apply]
  simp only [coordinateRow_apply, NormedLindeberg.linearCombination,
    Finset.sum_apply, Pi.smul_apply]
  rw [coord_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show x i • v i r = ((x i : ℂ) * v i r) by simp, coord_real_mul]
  simp [real_inner_comm]

/-- Four real rows belonging to the two complex increments in block `r`. -/
def pairBlockRows {n l : ℕ}
    (v : Fin n → PairIncrementSpace l) (r : Fin l) :
    Fin 4 → EuclideanSpace ℝ (Fin n) :=
  ![coordinateRow (fun i ↦ v i 0) r false,
    coordinateRow (fun i ↦ v i 0) r true,
    coordinateRow (fun i ↦ v i 1) r false,
    coordinateRow (fun i ↦ v i 1) r true]

lemma innerFamily_pairBlockRows_apply {n l : ℕ}
    (v : Fin n → PairIncrementSpace l) (x : Fin n → ℝ)
    (r : Fin l) :
    innerFamilyCLM (pairBlockRows v r) (toLp 2 x) =
      ![coord false
          (NormedLindeberg.linearCombination (fun i ↦ v i 0) x r),
        coord true
          (NormedLindeberg.linearCombination (fun i ↦ v i 0) x r),
        coord false
          (NormedLindeberg.linearCombination (fun i ↦ v i 1) x r),
        coord true
          (NormedLindeberg.linearCombination (fun i ↦ v i 1) x r)] := by
  ext j
  fin_cases j <;>
    simp [pairBlockRows, innerFamilyCLM_apply,
      coord_linearCombination_eq_inner_coordinateRow]

/-- Bounded continuous functions of concrete Gaussian block rows may be
transported without a representation hypothesis to `stdGaussian`. -/
lemma integral_pairBlockRows_gaussianProduct {n l : ℕ}
    (v : Fin n → PairIncrementSpace l) (r : Fin l)
    (F : EuclideanSpace ℝ (Fin 4) → ℝ) (hF : Continuous F) :
    (∫ x, F (innerFamilyCLM (pairBlockRows v r) (toLp 2 x))
        ∂Erdos88.Invariance.gaussianProductMeasure n) =
      ∫ z, F (innerFamilyCLM (pairBlockRows v r) z)
        ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  exact integral_gaussianProductMeasure_toLp
    (fun z ↦ F (innerFamilyCLM (pairBlockRows v r) z))
    ((hF.comp (innerFamilyCLM (pairBlockRows v r)).continuous).aestronglyMeasurable)

/-- Product expectations really are integrals over two independent copies;
this is the endpoint identity required at the fully decoupled end of the
canonical hybrid. -/
lemma phaseGaussianExpectation_mul_eq_prod_integral {n l : ℕ}
    (endpointScale prefixScale : ℝ)
    (vx vy : Fin n → Fin l → ℂ) :
    phaseGaussianExpectation endpointScale prefixScale vx *
        phaseGaussianExpectation endpointScale prefixScale vy =
      ∫ p : (Fin n → ℝ) × (Fin n → ℝ),
        SmoothCutoffC4.endpointPrefixCutoff l endpointScale prefixScale
            (NormedLindeberg.linearCombination vx p.1) *
          SmoothCutoffC4.endpointPrefixCutoff l endpointScale prefixScale
            (NormedLindeberg.linearCombination vy p.2)
        ∂((Erdos88.Invariance.gaussianProductMeasure n).prod
          (Erdos88.Invariance.gaussianProductMeasure n)) := by
  simpa [phaseGaussianExpectation] using
    (integral_prod_mul
      (fun x ↦ endpointPrefixCutoff l endpointScale prefixScale
        (NormedLindeberg.linearCombination vx x))
      (fun y ↦ endpointPrefixCutoff l endpointScale prefixScale
        (NormedLindeberg.linearCombination vy y))).symm

/-- Averaging a uniformly Lipschitz family against a probability measure
preserves the Lipschitz constant.  The unit bound is tailored to the cutoff
functions below and makes integrability automatic. -/
lemma lipschitzWith_integral_context
    {G : Type*} [MeasurableSpace G] (P : Measure G) [IsProbabilityMeasure P]
    {K : ℝ≥0} (F : EuclideanSpace ℝ (Fin 4) → G → ℝ)
    (hFmeas : ∀ x, AEStronglyMeasurable (F x) P)
    (hFunit : ∀ x g, ‖F x g‖ ≤ 1)
    (hFlip : ∀ g, LipschitzWith K (fun x ↦ F x g)) :
    LipschitzWith K (fun x ↦ ∫ g, F x g ∂P) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hx : Integrable (F x) P :=
    Integrable.mono' (integrable_const (1 : ℝ)) (hFmeas x)
      (Filter.Eventually.of_forall (hFunit x))
  have hy : Integrable (F y) P :=
    Integrable.mono' (integrable_const (1 : ℝ)) (hFmeas y)
      (Filter.Eventually.of_forall (hFunit y))
  rw [Real.dist_eq, ← integral_sub hx hy]
  have hnorm := norm_integral_le_of_norm_le_const
    (μ := P) (f := fun g ↦ F x g - F y g)
    (C := (K : ℝ) * dist x y)
    (Filter.Eventually.of_forall fun g ↦ hFlip g |>.dist_le_mul x y)
  simpa [Real.norm_eq_abs] using hnorm

/-- Gaussian decoupling remains valid after adjoining and averaging an
arbitrary bounded independent context.  This is the exact form needed in a
block hybrid: the four displayed variables are the current block and `g` is
the collection of all other blocks. -/
theorem gaussianPairDiscrepancy_with_context_le_rpow_quarter
    {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    [MeasurableSpace G] (P : Measure G) [IsProbabilityMeasure P]
    (x₀ x₁ y₀ y₁ : H) {m : ℝ} (hm : 0 ≤ m) (hmone : m ≤ 1)
    (hx₁one : ‖x₁‖ ≤ 1)
    (hxy₀₀ : |inner ℝ x₀ y₀| ≤ m)
    (hxy₀₁ : |inner ℝ x₀ y₁| ≤ m)
    (hxy₁₀ : |inner ℝ x₁ y₀| ≤ m)
    (hxy₁₁ : |inner ℝ x₁ y₁| ≤ m)
    {K : ℝ≥0} (F : EuclideanSpace ℝ (Fin 4) → G → ℝ)
    (hFmeas : ∀ x, AEStronglyMeasurable (F x) P)
    (hFunit : ∀ x g, ‖F x g‖ ≤ 1)
    (hFlip : ∀ g, LipschitzWith K (fun x ↦ F x g)) :
    GaussianDecoupling.gaussianPairDiscrepancy x₀ x₁ y₀ y₁
        (fun x ↦ ∫ g, F x g ∂P) ≤
      12 * (K : ℝ) * m ^ (1 / 4 : ℝ) := by
  exact GaussianDecoupling.gaussianPairDiscrepancy_le_rpow_quarter
    x₀ x₁ y₀ y₁ hm hmone hx₁one
    hxy₀₀ hxy₀₁ hxy₁₀ hxy₁₁
    (fun x ↦ ∫ g, F x g ∂P)
    (lipschitzWith_integral_context P F hFmeas hFunit hFlip)

/-- Package two phase directions into the common-sign pair direction. -/
def pairDirectionOf {n l : ℕ} (vx vy : Fin n → Fin l → ℂ) :
    Fin n → PairIncrementSpace l :=
  fun i q ↦ if q = 0 then vx i else vy i

@[simp] lemma pairDirectionOf_zero {n l : ℕ} (vx vy : Fin n → Fin l → ℂ)
    (i : Fin n) : pairDirectionOf vx vy i 0 = vx i := by
  simp [pairDirectionOf]

@[simp] lemma pairDirectionOf_one {n l : ℕ} (vx vy : Fin n → Fin l → ℂ)
    (i : Fin n) : pairDirectionOf vx vy i 1 = vy i := by
  simp [pairDirectionOf]

/-- Canonical Gaussian block hybrid: the first phase always uses `g`; in
the second phase blocks below `t` use the independent copy `h`, while later
blocks still use `g`. -/
def gaussianBlockHybrid {n l : ℕ} (vx vy : Fin n → Fin l → ℂ)
    (t : ℕ) (g h : Fin n → ℝ) : PairIncrementSpace l :=
  fun q r ↦ if q = 0 then
    NormedLindeberg.linearCombination vx g r
  else if r.val < t then
    NormedLindeberg.linearCombination vy h r
  else
    NormedLindeberg.linearCombination vy g r

def gaussianBlockHybridExpectation {n l : ℕ}
    (endpointScale prefixScale : ℝ) (vx vy : Fin n → Fin l → ℂ)
    (t : ℕ) : ℝ :=
  ∫ p : (Fin n → ℝ) × (Fin n → ℝ),
    pairEndpointPrefixCutoff l endpointScale prefixScale
      (gaussianBlockHybrid vx vy t p.1 p.2)
    ∂((Erdos88.Invariance.gaussianProductMeasure n).prod
      (Erdos88.Invariance.gaussianProductMeasure n))

lemma gaussianBlockHybrid_zero {n l : ℕ} (vx vy : Fin n → Fin l → ℂ)
    (g h : Fin n → ℝ) :
    gaussianBlockHybrid vx vy 0 g h =
      NormedLindeberg.linearCombination (pairDirectionOf vx vy) g := by
  ext q r
  fin_cases q <;> simp [gaussianBlockHybrid, pairDirectionOf,
    NormedLindeberg.linearCombination]

lemma gaussianBlockHybrid_end {n l : ℕ} (vx vy : Fin n → Fin l → ℂ)
    (g h : Fin n → ℝ) :
    gaussianBlockHybrid vx vy l g h =
      fun q ↦ if q = 0 then
        NormedLindeberg.linearCombination vx g
      else NormedLindeberg.linearCombination vy h := by
  ext q r
  fin_cases q <;> simp [gaussianBlockHybrid, Fin.isLt]

lemma gaussianBlockHybridExpectation_zero {n l : ℕ}
    (endpointScale prefixScale : ℝ) (vx vy : Fin n → Fin l → ℂ) :
    gaussianBlockHybridExpectation endpointScale prefixScale vx vy 0 =
      pairGaussianExpectation endpointScale prefixScale (pairDirectionOf vx vy) := by
  unfold gaussianBlockHybridExpectation pairGaussianExpectation
  rw [show (∫ p : (Fin n → ℝ) × (Fin n → ℝ),
      pairEndpointPrefixCutoff l endpointScale prefixScale
        (gaussianBlockHybrid vx vy 0 p.1 p.2)
      ∂((Erdos88.Invariance.gaussianProductMeasure n).prod
        (Erdos88.Invariance.gaussianProductMeasure n))) =
      ∫ p : (Fin n → ℝ) × (Fin n → ℝ),
        pairEndpointPrefixCutoff l endpointScale prefixScale
          (NormedLindeberg.linearCombination (pairDirectionOf vx vy) p.1)
      ∂((Erdos88.Invariance.gaussianProductMeasure n).prod
        (Erdos88.Invariance.gaussianProductMeasure n)) by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun p ↦ by
      change pairEndpointPrefixCutoff l endpointScale prefixScale
        (gaussianBlockHybrid vx vy 0 p.1 p.2) = _
      rw [gaussianBlockHybrid_zero]]
  simpa using (integral_fun_fst
    (μ := Erdos88.Invariance.gaussianProductMeasure n)
    (ν := Erdos88.Invariance.gaussianProductMeasure n)
    (fun x ↦ pairEndpointPrefixCutoff l endpointScale prefixScale
      (NormedLindeberg.linearCombination (pairDirectionOf vx vy) x)))

lemma gaussianBlockHybridExpectation_end {n l : ℕ}
    (endpointScale prefixScale : ℝ) (vx vy : Fin n → Fin l → ℂ) :
    gaussianBlockHybridExpectation endpointScale prefixScale vx vy l =
      phaseGaussianExpectation endpointScale prefixScale vx *
        phaseGaussianExpectation endpointScale prefixScale vy := by
  unfold gaussianBlockHybridExpectation
  rw [show (∫ p : (Fin n → ℝ) × (Fin n → ℝ),
      pairEndpointPrefixCutoff l endpointScale prefixScale
        (gaussianBlockHybrid vx vy l p.1 p.2)
      ∂((Erdos88.Invariance.gaussianProductMeasure n).prod
        (Erdos88.Invariance.gaussianProductMeasure n))) =
      ∫ p : (Fin n → ℝ) × (Fin n → ℝ),
        endpointPrefixCutoff l endpointScale prefixScale
            (NormedLindeberg.linearCombination vx p.1) *
          endpointPrefixCutoff l endpointScale prefixScale
            (NormedLindeberg.linearCombination vy p.2)
      ∂((Erdos88.Invariance.gaussianProductMeasure n).prod
        (Erdos88.Invariance.gaussianProductMeasure n)) by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun p ↦ by
      change pairEndpointPrefixCutoff l endpointScale prefixScale
        (gaussianBlockHybrid vx vy l p.1 p.2) = _
      rw [gaussianBlockHybrid_end, pairEndpointPrefixCutoff_eq]
      simp]
  exact (phaseGaussianExpectation_mul_eq_prod_integral
    endpointScale prefixScale vx vy).symm

end
end Erdos527.DirectGaussianPair


open scoped BigOperators ComplexConjugate
open Finset

namespace Erdos527
namespace FlatCovariance

noncomputable section

open CorrelationCount

/-- The real or imaginary coefficient vector of one uniform block at a phase. -/
def uniformBlockCoordVector (a : ℕ → ℝ) (x : UnitAddCircle) (p : Bool)
    (N0 k r : ℕ) : EuclideanSpace ℝ (Fin (uniformBlockLength N0 k)) :=
  WithLp.toLp 2 fun i ↦
    coord p (phaseValue (fun n ↦ (a n : ℂ))
      (uniformEndpoint N0 k r + i.1) x)

@[simp] lemma uniformBlockCoordVector_apply
    (a : ℕ → ℝ) (x : UnitAddCircle) (p : Bool) (N0 k r : ℕ)
    (i : Fin (uniformBlockLength N0 k)) :
    uniformBlockCoordVector a x p N0 k r i =
      coord p (phaseValue (fun n ↦ (a n : ℂ))
        (uniformEndpoint N0 k r + i.1) x) := rfl

/-- The local Euclidean inner product is exactly the large-sieve covariance
on the corresponding natural-number uniform block. -/
lemma inner_uniformBlockCoordVector
    (a : ℕ → ℝ) (x y : UnitAddCircle) (p q : Bool)
    {N0 : ℕ} (hN0 : 0 < N0) (k r : ℕ) :
    inner ℝ (uniformBlockCoordVector a x p N0 k r)
        (uniformBlockCoordVector a y q N0 k r) =
      blockCovariance (fun n ↦ (a n : ℂ))
        (uniformEndpoint N0 k r - 1) (uniformBlockLength N0 k) x y p q := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial, uniformBlockCoordVector_apply]
  rw [Fin.sum_univ_eq_sum_range
    (fun i ↦
      coord q (phaseValue (fun n ↦ (a n : ℂ)) (uniformEndpoint N0 k r + i) y) *
        coord p (phaseValue (fun n ↦ (a n : ℂ)) (uniformEndpoint N0 k r + i) x))
    (uniformBlockLength N0 k)]
  unfold blockCovariance
  have hstart : 0 < uniformEndpoint N0 k r :=
    (scale_pos hN0 k).trans_le (uniformBlock_start_ge_scale N0 k r)
  have hset :
      Finset.Ioc (uniformEndpoint N0 k r - 1)
          (uniformEndpoint N0 k r - 1 + uniformBlockLength N0 k) =
        Finset.Ico (uniformEndpoint N0 k r)
          (uniformEndpoint N0 k r + uniformBlockLength N0 k) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hset, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_comm]

/-- Squared norm of the coordinate vector, in local consecutive coordinates. -/
lemma norm_uniformBlockCoordVector_sq
    (a : ℕ → ℝ) (x : UnitAddCircle) (p : Bool)
    (N0 k r : ℕ) :
    ‖uniformBlockCoordVector a x p N0 k r‖ ^ 2 =
      ∑ i : Fin (uniformBlockLength N0 k),
        |coord p (phaseValue (fun n ↦ (a n : ℂ))
          (uniformEndpoint N0 k r + i.1) x)| ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [uniformBlockCoordVector_apply, Real.norm_eq_abs]

/-- A coordinate vector has norm at most the square root of the coefficient
energy in that uniform block. -/
lemma norm_uniformBlockCoordVector_le_sqrt_energy
    (a : ℕ → ℝ) (x : UnitAddCircle) (p : Bool)
    {N0 : ℕ} (hN0 : 0 < N0) (k r : ℕ) :
    ‖uniformBlockCoordVector a x p N0 k r‖ ≤
      Real.sqrt (∑ n ∈ uniformBlock N0 k r, |a n| ^ 2) := by
  rw [← sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _),
    norm_uniformBlockCoordVector_sq, Real.sq_sqrt]
  · rw [Fin.sum_univ_eq_sum_range
      (fun i ↦ |coord p (phaseValue (fun n ↦ (a n : ℂ))
        (uniformEndpoint N0 k r + i) x)| ^ 2)
      (uniformBlockLength N0 k)]
    rw [uniformBlock, uniformEndpoint_succ, Finset.sum_Ico_eq_sum_range]
    rw [Nat.add_sub_cancel_left]
    apply Finset.sum_le_sum
    intro i hi
    have hc := abs_coord_le_norm p
      (phaseValue (fun n ↦ (a n : ℂ)) (uniformEndpoint N0 k r + i) x)
    have hnorm :
        ‖phaseValue (fun n ↦ (a n : ℂ)) (uniformEndpoint N0 k r + i) x‖ =
          |a (uniformEndpoint N0 k r + i)| := by
      rw [phaseValue, norm_mul,
        show ‖BoundedGaps.Maynard.unitAddCircleAddChar
            ((uniformEndpoint N0 k r + i) • x)‖ = 1 by
          change ‖((AddCircle.toCircle ((uniformEndpoint N0 k r + i) • x) : Circle) : ℂ)‖ = 1
          exact Circle.norm_coe _]
      simp [Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm] at hc
    exact (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).2 hc
  · exact Finset.sum_nonneg fun n hn ↦ sq_nonneg |a n|

/-- In particular, block energy at most one makes every real/imaginary
coefficient vector a unit-ball vector. -/
lemma norm_uniformBlockCoordVector_le_one
    (a : ℕ → ℝ) (x : UnitAddCircle) (p : Bool)
    {N0 : ℕ} (hN0 : 0 < N0) (k r : ℕ)
    (henergy : (∑ n ∈ uniformBlock N0 k r, |a n| ^ 2) ≤ 1) :
    ‖uniformBlockCoordVector a x p N0 k r‖ ≤ 1 := by
  calc
    ‖uniformBlockCoordVector a x p N0 k r‖ ≤
        Real.sqrt (∑ n ∈ uniformBlock N0 k r, |a n| ^ 2) :=
      norm_uniformBlockCoordVector_le_sqrt_energy a x p hN0 k r
    _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt henergy
    _ = 1 := by norm_num

end

end FlatCovariance
end Erdos527

namespace Erdos527
namespace PairFactorization

open scoped BigOperators
open SmoothCutoffC4 CutoffLindebergBridge
open OnePointLindeberg

noncomputable section

/-- The common-sign replacement direction at two phases.  The outer `Fin 2`
coordinate records the phase and the inner coordinate records the flat block. -/
def flatPairDirection (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (z w : ℂ) (i : Fin (scale N0 (k + 1) - scale N0 k)) :
    PairIncrementSpace (uniformBlockCount k) :=
  fun q ↦ if q = 0 then
    flatBlockIncrementDirection a hN0 k z i
  else
    flatBlockIncrementDirection a hN0 k w i

@[simp] lemma flatPairDirection_apply_zero
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (z w : ℂ) (i : Fin (scale N0 (k + 1) - scale N0 k)) :
    flatPairDirection a hN0 k z w i 0 =
      flatBlockIncrementDirection a hN0 k z i := by
  simp [flatPairDirection]

@[simp] lemma flatPairDirection_apply_one
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (z w : ℂ) (i : Fin (scale N0 (k + 1) - scale N0 k)) :
    flatPairDirection a hN0 k z w i 1 =
      flatBlockIncrementDirection a hN0 k w i := by
  simp [flatPairDirection]

lemma norm_flatPairDirection_le
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) (z w : ℂ)
    (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    (i : Fin (scale N0 (k + 1) - scale N0 k)) :
    ‖flatPairDirection a hN0 k z w i‖ ≤
      |a (flatScaleIndex N0 k i)| := by
  rw [pi_norm_le_iff_of_nonneg (abs_nonneg _)]
  intro q
  fin_cases q
  · simpa using norm_flatBlockIncrementDirection_le a hN0 k z hz i
  · simpa using norm_flatBlockIncrementDirection_le a hN0 k w hw i

/-- Passing from a one-phase endpoint/prefix form to either coordinate of the
two-phase product does not increase its operator norm. -/
lemma norm_pairEndpointPrefixForms_le (l : ℕ) (endpointScale prefixScale : ℝ)
    (q : Fin 2 × Option (Fin l)) :
    ‖pairEndpointPrefixForms l endpointScale prefixScale q‖ ≤
      ‖endpointPrefixForms l endpointScale prefixScale q.2‖ := by
  have hproj : ‖(ContinuousLinearMap.proj q.1 :
      PairIncrementSpace l →L[ℝ] (Fin l → ℂ))‖ ≤ 1 := by
    apply (ContinuousLinearMap.proj q.1 :
      PairIncrementSpace l →L[ℝ] (Fin l → ℂ)).opNorm_le_bound zero_le_one
    intro x
    simpa using norm_le_pi_norm x q.1
  calc
    ‖pairEndpointPrefixForms l endpointScale prefixScale q‖ ≤
        ‖endpointPrefixForms l endpointScale prefixScale q.2‖ *
          ‖(ContinuousLinearMap.proj q.1 :
            PairIncrementSpace l →L[ℝ] (Fin l → ℂ))‖ := by
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖endpointPrefixForms l endpointScale prefixScale q.2‖ * 1 := by
      exact mul_le_mul_of_nonneg_left hproj (norm_nonneg _)
    _ = ‖endpointPrefixForms l endpointScale prefixScale q.2‖ := mul_one _

/-- The two-phase cutoff has at most twice the one-phase operator budget. -/
lemma sum_norm_pairEndpointPrefixForms_le (l : ℕ)
    (endpointScale prefixScale : ℝ) :
    (∑ q : Fin 2 × Option (Fin l),
        ‖pairEndpointPrefixForms l endpointScale prefixScale q‖) ≤
      2 * (((l + 1 : ℕ) : ℝ) *
        (|endpointScale| + |prefixScale|) * l) := by
  calc
    (∑ q : Fin 2 × Option (Fin l),
        ‖pairEndpointPrefixForms l endpointScale prefixScale q‖) ≤
        ∑ q : Fin 2 × Option (Fin l),
          ‖endpointPrefixForms l endpointScale prefixScale q.2‖ := by
      exact Finset.sum_le_sum fun q _ ↦
        norm_pairEndpointPrefixForms_le l endpointScale prefixScale q
    _ = 2 * (∑ j : Option (Fin l),
          ‖endpointPrefixForms l endpointScale prefixScale j‖) := by
      rw [Fintype.sum_prod_type, Fin.sum_univ_two]
      ring
    _ ≤ 2 * (((l + 1 : ℕ) : ℝ) *
          (|endpointScale| + |prefixScale|) * l) := by
      gcongr
      exact sum_norm_endpointPrefixForms_le l endpointScale prefixScale

/-- Polynomial operator factor for a common-sign, two-phase replacement. -/
def flatPairCutoffOperatorBudget (k : ℕ)
    (endpointScale prefixScale : ℝ) : ℝ :=
  2 * flatCutoffOperatorBudget k endpointScale prefixScale

lemma flatPairCutoffOperatorBudget_nonneg (k : ℕ)
    (endpointScale prefixScale : ℝ) :
    0 ≤ flatPairCutoffOperatorBudget k endpointScale prefixScale := by
  exact mul_nonneg (by norm_num)
    (flatCutoffOperatorBudget_nonneg k endpointScale prefixScale)

/-- Pointwise fourth-order budget for one common sign at two unit phases. -/
lemma flat_pair_directionBudget_le
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) (z w : ℂ)
    (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) (endpointScale prefixScale : ℝ)
    (i : Fin (scale N0 (k + 1) - scale N0 k)) :
    pairEndpointPrefixDirectionBudget (uniformBlockCount k)
        endpointScale prefixScale (flatPairDirection a hN0 k z w i) ≤
      (flatPairCutoffOperatorBudget k endpointScale prefixScale *
        |a (flatScaleIndex N0 k i)|) ^ 4 := by
  unfold pairEndpointPrefixDirectionBudget flatPairCutoffOperatorBudget
  apply pow_le_pow_left₀
    (mul_nonneg
      (mul_nonneg cutoffC4_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _))
      (norm_nonneg _))
  calc
    cutoffC4 *
          (∑ q : Fin 2 × Option (Fin (uniformBlockCount k)),
            ‖pairEndpointPrefixForms (uniformBlockCount k)
              endpointScale prefixScale q‖) *
          ‖flatPairDirection a hN0 k z w i‖
        ≤ cutoffC4 *
          (2 * ((((uniformBlockCount k + 1 : ℕ) : ℝ) *
            (|endpointScale| + |prefixScale|) * uniformBlockCount k))) *
          |a (flatScaleIndex N0 k i)| := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          (sum_norm_pairEndpointPrefixForms_le
            (uniformBlockCount k) endpointScale prefixScale)
          cutoffC4_nonneg
      · exact norm_flatPairDirection_le a hN0 k z w hz hw i
      · exact norm_nonneg _
      · exact mul_nonneg cutoffC4_nonneg
          (mul_nonneg (by norm_num)
            (mul_nonneg
              (mul_nonneg (by positivity)
                (add_nonneg (abs_nonneg _) (abs_nonneg _)))
              (by positivity)))
    _ = (2 * flatCutoffOperatorBudget k endpointScale prefixScale) *
          |a (flatScaleIndex N0 k i)| := by
      unfold flatCutoffOperatorBudget
      ring

/-- Before inserting the universal `1/6` Lindeberg factor, the joint budget is
bounded by the pair operator factor times the exact fourth coefficient mass. -/
lemma sum_flatPair_directionBudget_le_fourth_mass
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) (z w : ℂ)
    (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) (endpointScale prefixScale : ℝ) :
    (∑ i : Fin (scale N0 (k + 1) - scale N0 k),
      pairEndpointPrefixDirectionBudget (uniformBlockCount k)
        endpointScale prefixScale (flatPairDirection a hN0 k z w i)) ≤
      (flatPairCutoffOperatorBudget k endpointScale prefixScale) ^ 4 *
        ∑ i : Fin (scale N0 (k + 1) - scale N0 k),
          |a (flatScaleIndex N0 k i)| ^ 4 := by
  calc
    (∑ i : Fin (scale N0 (k + 1) - scale N0 k),
      pairEndpointPrefixDirectionBudget (uniformBlockCount k)
        endpointScale prefixScale (flatPairDirection a hN0 k z w i)) ≤
        ∑ i : Fin (scale N0 (k + 1) - scale N0 k),
          (flatPairCutoffOperatorBudget k endpointScale prefixScale *
            |a (flatScaleIndex N0 k i)|) ^ 4 := by
      exact Finset.sum_le_sum fun i _ ↦
        flat_pair_directionBudget_le a hN0 k z w hz hw endpointScale prefixScale i
    _ = (flatPairCutoffOperatorBudget k endpointScale prefixScale) ^ 4 *
        ∑ i : Fin (scale N0 (k + 1) - scale N0 k),
          |a (flatScaleIndex N0 k i)| ^ 4 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [mul_pow]

/-- The complete two-phase Lindeberg budget costs at most `2^4 = 16` times
the already-defined one-point error. -/
lemma sum_flatPair_directionBudget_div_le_sixteen_error
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) (z w : ℂ)
    (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) (endpointScale prefixScale : ℝ) :
    (∑ i : Fin (scale N0 (k + 1) - scale N0 k),
      pairEndpointPrefixDirectionBudget (uniformBlockCount k)
        endpointScale prefixScale (flatPairDirection a hN0 k z w i) / 6) ≤
      16 * flatOnePointLindebergError a N0 k endpointScale prefixScale := by
  rw [← Finset.sum_div]
  apply (div_le_div_of_nonneg_right
    ((sum_flatPair_directionBudget_le_fourth_mass
      a hN0 k z w hz hw endpointScale prefixScale).trans
      (mul_le_mul_of_nonneg_left
        (sum_abs_four_flatScale_le a hsmall hN0 k)
        (Even.pow_nonneg (by norm_num) _))) (by norm_num)).trans_eq
  unfold flatPairCutoffOperatorBudget flatOnePointLindebergError
  ring

/-- The full two-phase endpoint/prefix cutoff is globally Lipschitz with the same
polynomial operator factor used in the flat joint Lindeberg estimate. -/
theorem pairEndpointPrefixCutoff_lipschitz (k : ℕ)
    (endpointScale prefixScale : ℝ) :
    LipschitzWith
      (Real.toNNReal (flatPairCutoffOperatorBudget k endpointScale prefixScale))
      (pairEndpointPrefixCutoff (uniformBlockCount k) endpointScale prefixScale) := by
  apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
  · exact (pairEndpointPrefixCutoff_contDiff
      (uniformBlockCount k) endpointScale prefixScale).differentiable (by norm_num)
  · intro w
    apply NNReal.coe_le_coe.mp
    rw [coe_nnnorm, ← norm_iteratedFDeriv_one]
    change
      ‖iteratedFDeriv ℝ 1
        (cutoffProduct (Finset.univ : Finset
          (Fin 2 × Option (Fin (uniformBlockCount k))))
          (pairEndpointPrefixForms (uniformBlockCount k)
            endpointScale prefixScale)) w‖ ≤
        (Real.toNNReal
          (flatPairCutoffOperatorBudget k endpointScale prefixScale) : ℝ)
    calc
      ‖iteratedFDeriv ℝ 1
          (cutoffProduct (Finset.univ : Finset
            (Fin 2 × Option (Fin (uniformBlockCount k))))
            (pairEndpointPrefixForms (uniformBlockCount k)
              endpointScale prefixScale)) w‖ ≤
          cutoffC4 *
            (∑ q : Fin 2 × Option (Fin (uniformBlockCount k)),
              ‖pairEndpointPrefixForms (uniformBlockCount k)
                endpointScale prefixScale q‖) := by
        simpa using (norm_iteratedFDeriv_cutoffProduct_le
            (u := (Finset.univ : Finset
              (Fin 2 × Option (Fin (uniformBlockCount k)))))
            (pairEndpointPrefixForms (uniformBlockCount k)
              endpointScale prefixScale) w (by norm_num : 1 ≤ 4))
      _ ≤ cutoffC4 *
          (2 * (((((uniformBlockCount k + 1 : ℕ) : ℝ) *
            (|endpointScale| + |prefixScale|) * uniformBlockCount k)))) := by
        exact mul_le_mul_of_nonneg_left
          (sum_norm_pairEndpointPrefixForms_le
            (uniformBlockCount k) endpointScale prefixScale) cutoffC4_nonneg
      _ = flatPairCutoffOperatorBudget k endpointScale prefixScale := by
        unfold flatPairCutoffOperatorBudget flatCutoffOperatorBudget
        ring
      _ = (Real.toNNReal
          (flatPairCutoffOperatorBudget k endpointScale prefixScale) : ℝ) := by
        rw [Real.coe_toNNReal', max_eq_left
          (flatPairCutoffOperatorBudget_nonneg k endpointScale prefixScale)]

/-- Once the genuinely Gaussian two-phase factorization has been proved, all three
Rademacher--Gaussian replacements cost at most eighteen copies of the existing
one-point error: sixteen for the joint cutoff and one for each marginal. -/
theorem flat_pair_rademacher_factorization_of_gaussian_bound
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) (z w : ℂ)
    (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    (endpointScale prefixScale D : ℝ)
    (hgauss :
      |pairGaussianExpectation endpointScale prefixScale
          (flatPairDirection a hN0 k z w) -
        phaseGaussianExpectation endpointScale prefixScale
            (flatBlockIncrementDirection a hN0 k z) *
          phaseGaussianExpectation endpointScale prefixScale
            (flatBlockIncrementDirection a hN0 k w)| ≤ D) :
    |pairRademacherExpectation endpointScale prefixScale
          (flatPairDirection a hN0 k z w) -
        phaseRademacherExpectation endpointScale prefixScale
            (flatBlockIncrementDirection a hN0 k z) *
          phaseRademacherExpectation endpointScale prefixScale
            (flatBlockIncrementDirection a hN0 k w)| ≤
      18 * flatOnePointLindebergError a N0 k endpointScale prefixScale + D := by
  have hmain := endpointPrefixCutoff_pair_approx_factorization_of_gaussian_bound
    endpointScale prefixScale (flatPairDirection a hN0 k z w) hgauss
  have hjoint := sum_flatPair_directionBudget_div_le_sixteen_error
    a hsmall hN0 k z w hz hw endpointScale prefixScale
  have hzerr := OnePointLindeberg.sum_flat_directionBudget_div_le_error
    a hsmall hN0 k z hz endpointScale prefixScale
  have hwerr := OnePointLindeberg.sum_flat_directionBudget_div_le_error
    a hsmall hN0 k w hw endpointScale prefixScale
  have hzerr' :
      (∑ i, endpointPrefixDirectionBudget (uniformBlockCount k)
        endpointScale prefixScale (flatPairDirection a hN0 k z w i 0) / 6) ≤
        flatOnePointLindebergError a N0 k endpointScale prefixScale := by
    simpa using hzerr
  have hwerr' :
      (∑ i, endpointPrefixDirectionBudget (uniformBlockCount k)
        endpointScale prefixScale (flatPairDirection a hN0 k z w i 1) / 6) ≤
        flatOnePointLindebergError a N0 k endpointScale prefixScale := by
    simpa using hwerr
  apply hmain.trans
  calc
    (∑ i, pairEndpointPrefixDirectionBudget (uniformBlockCount k)
          endpointScale prefixScale (flatPairDirection a hN0 k z w i) / 6) +
        (∑ i, endpointPrefixDirectionBudget (uniformBlockCount k)
          endpointScale prefixScale
          (flatPairDirection a hN0 k z w i 0) / 6) +
        (∑ i, endpointPrefixDirectionBudget (uniformBlockCount k)
          endpointScale prefixScale
          (flatPairDirection a hN0 k z w i 1) / 6) + D ≤
      16 * flatOnePointLindebergError a N0 k endpointScale prefixScale +
        flatOnePointLindebergError a N0 k endpointScale prefixScale +
        flatOnePointLindebergError a N0 k endpointScale prefixScale + D := by
      gcongr
    _ = 18 * flatOnePointLindebergError a N0 k endpointScale prefixScale + D := by
      ring

end

end PairFactorization
end Erdos527


namespace Erdos527.PairHybridIntegration

open scoped BigOperators ENNReal NNReal Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Finset
open PairFactorization OnePointLindeberg CorrelationCount FlatVectorAPI
open BoundedGaps.Maynard

noncomputable section

lemma inner_blockCoordVector_toLp_eq_coord_linearCombination
    (a : ℕ → ℝ) (z : ℂ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (r : Fin (uniformBlockCount k)) (p : Bool)
    (g : Fin (scale N0 (k + 1) - scale N0 k) → ℝ) :
    inner ℝ (PairCanonicalHybrid.blockCoordVector a z hN0 k r p)
        (WithLp.toLp 2 g) =
      coord p (CutoffLindebergBridge.NormedLindeberg.linearCombination
        (flatBlockIncrementDirection a hN0 k z) g r) := by
  rw [PiLp.inner_apply, flat_linearCombination_apply, coord_sum]
  simp only [PairCanonicalHybrid.blockCoordVector_apply,
    RCLike.inner_apply, conj_trivial, PiLp.toLp_apply]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hir : uniformBlockOfOffset hN0 k i = r
  · rw [if_pos hir, if_pos hir]
    simp only [flatPhaseCoefficient, flatScaleIndex, scaleCoefficient]
    cases p <;> simp [coord, Complex.mul_re, Complex.mul_im] <;> ring
  · rw [if_neg hir, if_neg hir]
    simp

def phasePoint (x : UnitAddCircle) : ℂ := unitAddCircleAddChar x

def blockOffset {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (j : Fin (uniformBlockCount k))
    (i : Fin (uniformBlockLength N0 k)) :
    Fin (scale N0 (k + 1) - scale N0 k) :=
  ⟨j.val * uniformBlockLength N0 k + i.val, by
    rw [scale_gap_eq_uniformBlockCount_mul_length]
    have h₁ : j.val * uniformBlockLength N0 k + i.val <
        j.val * uniformBlockLength N0 k + uniformBlockLength N0 k :=
      Nat.add_lt_add_left i.isLt _
    have h₂ : j.val * uniformBlockLength N0 k + uniformBlockLength N0 k =
        (j.val + 1) * uniformBlockLength N0 k := by
      simp [Nat.add_mul]
    rw [h₂] at h₁
    exact h₁.trans_le (Nat.mul_le_mul_right _ (Nat.succ_le_of_lt j.isLt))⟩

@[simp] lemma uniformBlockOfOffset_blockOffset {N0 : ℕ} (hN0 : 0 < N0)
    (k : ℕ) (j : Fin (uniformBlockCount k))
    (i : Fin (uniformBlockLength N0 k)) :
    uniformBlockOfOffset hN0 k (blockOffset hN0 k j i) = j := by
  apply Fin.ext
  simp only [uniformBlockOfOffset_val, blockOffset]
  rw [show j.val * uniformBlockLength N0 k + i.val =
      uniformBlockLength N0 k * j.val + i.val by rw [Nat.mul_comm]]
  rw [Nat.mul_add_div (uniformBlockLength_pos hN0 k)]
  simp [Nat.div_eq_of_lt i.isLt]

@[simp] lemma scaleCoefficient_blockOffset {N0 : ℕ} (hN0 : 0 < N0)
    (k : ℕ) (j : Fin (uniformBlockCount k))
    (i : Fin (uniformBlockLength N0 k)) :
    scaleCoefficient N0 k (blockOffset hN0 k j i) =
      uniformEndpoint N0 k j + i.val := by
  simp [scaleCoefficient, blockOffset, uniformEndpoint]
  omega

lemma blockCoordVector_blockOffset
    (a : ℕ → ℝ) (x : UnitAddCircle) (p : Bool)
    {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (j : Fin (uniformBlockCount k)) (i : Fin (uniformBlockLength N0 k)) :
    PairCanonicalHybrid.blockCoordVector a (phasePoint x) hN0 k j p
        (blockOffset hN0 k j i) =
      FlatCovariance.uniformBlockCoordVector a x p N0 k j i := by
  rw [PairCanonicalHybrid.blockCoordVector_apply,
    if_pos (uniformBlockOfOffset_blockOffset hN0 k j i)]
  simp only [FlatCovariance.uniformBlockCoordVector_apply,
    scaleCoefficient_blockOffset, phasePoint, phaseValue]
  rw [AddChar.map_nsmul_eq_pow]

lemma blockOffset_injective {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (j : Fin (uniformBlockCount k)) :
    Function.Injective (blockOffset hN0 k j) := by
  intro i i' h
  apply Fin.ext
  have := Fin.mk.inj h
  change j.val * uniformBlockLength N0 k + i.val =
    j.val * uniformBlockLength N0 k + i'.val at this
  omega

lemma exists_blockOffset_of_uniformBlockOfOffset_eq
    {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (j : Fin (uniformBlockCount k))
    (u : Fin (scale N0 (k + 1) - scale N0 k))
    (hu : uniformBlockOfOffset hN0 k u = j) :
    ∃ i : Fin (uniformBlockLength N0 k), blockOffset hN0 k j i = u := by
  let L := uniformBlockLength N0 k
  have hL : 0 < L := uniformBlockLength_pos hN0 k
  have hdiv : u.val / L = j.val := by
    simpa [L] using Fin.mk.inj hu
  let i : Fin L := ⟨u.val % L, Nat.mod_lt _ hL⟩
  refine ⟨i, Fin.ext ?_⟩
  simp only [blockOffset, i, L]
  rw [← hdiv]
  change u.val / L * L + u.val % L = u.val
  rw [Nat.mul_comm, Nat.div_add_mod]

lemma inner_blockCoordVector_phasePoint_eq_blockCovariance
    (a : ℕ → ℝ) (x y : UnitAddCircle) (p q : Bool)
    {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (j : Fin (uniformBlockCount k)) :
    inner ℝ
        (PairCanonicalHybrid.blockCoordVector a (phasePoint x) hN0 k j p)
        (PairCanonicalHybrid.blockCoordVector a (phasePoint y) hN0 k j q) =
      blockCovariance (fun n ↦ (a n : ℂ))
        (uniformEndpoint N0 k j - 1) (uniformBlockLength N0 k) x y p q := by
  rw [← FlatCovariance.inner_uniformBlockCoordVector a x y p q hN0 k j]
  rw [PairCanonicalHybrid.inner_blockCoordVector, PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial,
    FlatCovariance.uniformBlockCoordVector_apply]
  rw [show (∑ u,
      (if uniformBlockOfOffset hN0 k u = j then
        coord p ((a (scaleCoefficient N0 k u) : ℂ) *
          phasePoint x ^ scaleCoefficient N0 k u) else 0) *
      (if uniformBlockOfOffset hN0 k u = j then
        coord q ((a (scaleCoefficient N0 k u) : ℂ) *
          phasePoint y ^ scaleCoefficient N0 k u) else 0)) =
      ∑ u with uniformBlockOfOffset hN0 k u = j,
        coord p ((a (scaleCoefficient N0 k u) : ℂ) *
          phasePoint x ^ scaleCoefficient N0 k u) *
        coord q ((a (scaleCoefficient N0 k u) : ℂ) *
          phasePoint y ^ scaleCoefficient N0 k u) by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro u hu
    by_cases h : uniformBlockOfOffset hN0 k u = j <;> simp [h]]
  symm
  refine Finset.sum_bij (fun i _ ↦ blockOffset hN0 k j i) ?_ ?_ ?_ ?_
  · intro i hi
    simp
  · intro i hi i' hi' heq
    exact blockOffset_injective hN0 k j heq
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    obtain ⟨i, rfl⟩ := exists_blockOffset_of_uniformBlockOfOffset_eq hN0 k j u hu
    exact ⟨i, Finset.mem_univ i, rfl⟩
  · intro i hi
    rw [scaleCoefficient_blockOffset]
    simp only [phaseValue, phasePoint]
    rw [AddChar.map_nsmul_eq_pow, AddChar.map_nsmul_eq_pow]
    ring

lemma norm_blockCoordVector_phasePoint_eq_uniformBlockCoordVector
    (a : ℕ → ℝ) (x : UnitAddCircle) (p : Bool)
    {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (j : Fin (uniformBlockCount k)) :
    ‖PairCanonicalHybrid.blockCoordVector a (phasePoint x) hN0 k j p‖ =
      ‖FlatCovariance.uniformBlockCoordVector a x p N0 k j‖ := by
  have hg := inner_blockCoordVector_phasePoint_eq_blockCovariance
    a x x p p hN0 k j
  have hl := FlatCovariance.inner_uniformBlockCoordVector
    a x x p p hN0 k j
  have hs :
      ‖PairCanonicalHybrid.blockCoordVector a (phasePoint x) hN0 k j p‖ ^ 2 =
        ‖FlatCovariance.uniformBlockCoordVector a x p N0 k j‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    exact hg.trans hl.symm
  nlinarith [norm_nonneg
    (PairCanonicalHybrid.blockCoordVector a (phasePoint x) hN0 k j p),
    norm_nonneg (FlatCovariance.uniformBlockCoordVector a x p N0 k j)]

lemma norm_blockCoordVector_phasePoint_le_sqrt_energy
    (a : ℕ → ℝ) (x : UnitAddCircle) (p : Bool)
    {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (j : Fin (uniformBlockCount k)) :
    ‖PairCanonicalHybrid.blockCoordVector a (phasePoint x) hN0 k j p‖ ≤
      Real.sqrt (∑ n ∈ uniformBlock N0 k j, |a n| ^ 2) := by
  rw [norm_blockCoordVector_phasePoint_eq_uniformBlockCoordVector]
  exact FlatCovariance.norm_uniformBlockCoordVector_le_sqrt_energy
    a x p hN0 k j

lemma norm_blockCoordVector_phasePoint_le_one
    (a : ℕ → ℝ) (x : UnitAddCircle) (p : Bool)
    {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (j : Fin (uniformBlockCount k))
    (henergy : (∑ n ∈ uniformBlock N0 k j, |a n| ^ 2) ≤ 1) :
    ‖PairCanonicalHybrid.blockCoordVector a (phasePoint x) hN0 k j p‖ ≤ 1 := by
  rw [norm_blockCoordVector_phasePoint_eq_uniformBlockCoordVector]
  exact FlatCovariance.norm_uniformBlockCoordVector_le_one
    a x p hN0 k j henergy

def correlatedBlockRows
    (a : ℕ → ℝ) (zx zy : ℂ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (j : Fin (uniformBlockCount k)) :
    Fin 4 → PiLp 2 (fun _ : Fin 2 ↦
      EuclideanSpace ℝ (Fin (scale N0 (k + 1) - scale N0 k))) :=
  ![GaussianDecoupling.pairL2
      (PairCanonicalHybrid.blockCoordVector a zx hN0 k j false) 0,
    GaussianDecoupling.pairL2
      (PairCanonicalHybrid.blockCoordVector a zx hN0 k j true) 0,
    GaussianDecoupling.pairL2
      (PairCanonicalHybrid.blockCoordVector a zy hN0 k j false) 0,
    GaussianDecoupling.pairL2
      (PairCanonicalHybrid.blockCoordVector a zy hN0 k j true) 0]

def independentBlockRows
    (a : ℕ → ℝ) (zx zy : ℂ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (j : Fin (uniformBlockCount k)) :
    Fin 4 → PiLp 2 (fun _ : Fin 2 ↦
      EuclideanSpace ℝ (Fin (scale N0 (k + 1) - scale N0 k))) :=
  ![GaussianDecoupling.pairL2
      (PairCanonicalHybrid.blockCoordVector a zx hN0 k j false) 0,
    GaussianDecoupling.pairL2
      (PairCanonicalHybrid.blockCoordVector a zx hN0 k j true) 0,
    GaussianDecoupling.pairL2 0
      (PairCanonicalHybrid.blockCoordVector a zy hN0 k j false),
    GaussianDecoupling.pairL2 0
      (PairCanonicalHybrid.blockCoordVector a zy hN0 k j true)]

lemma localBlockFour_correlated_eq_innerFamily
    (a : ℕ → ℝ) (zx zy : ℂ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (j : Fin (uniformBlockCount k))
    (g h : Fin (scale N0 (k + 1) - scale N0 k) → ℝ) :
    PairHybridAlgebra.localBlockFour a hN0 k zx zy j g g =
      GaussianDecoupling.innerFamilyCLM
        (correlatedBlockRows a zx zy hN0 k j)
        (GaussianDecoupling.pairL2 (WithLp.toLp 2 g) (WithLp.toLp 2 h)) := by
  ext i
  fin_cases i <;>
    simp [PairHybridAlgebra.localBlockFour, correlatedBlockRows,
      GaussianDecoupling.innerFamilyCLM_apply,
      inner_blockCoordVector_toLp_eq_coord_linearCombination]

lemma localBlockFour_independent_eq_innerFamily
    (a : ℕ → ℝ) (zx zy : ℂ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (j : Fin (uniformBlockCount k))
    (g h : Fin (scale N0 (k + 1) - scale N0 k) → ℝ) :
    PairHybridAlgebra.localBlockFour a hN0 k zx zy j g h =
      GaussianDecoupling.innerFamilyCLM
        (independentBlockRows a zx zy hN0 k j)
        (GaussianDecoupling.pairL2 (WithLp.toLp 2 g) (WithLp.toLp 2 h)) := by
  ext i
  fin_cases i <;>
    simp [PairHybridAlgebra.localBlockFour, independentBlockRows,
      GaussianDecoupling.innerFamilyCLM_apply,
      inner_blockCoordVector_toLp_eq_coord_linearCombination]

lemma measurable_concreteTwoCopiesToPairL2 (n : ℕ) :
    Measurable (PairTwoCopyTransport.concreteTwoCopiesToPairL2 n) := by
  let H := EuclideanSpace ℝ (Fin n)
  have hpair : Measurable (fun p : H × H ↦
      GaussianDecoupling.pairL2 p.1 p.2) := by
    have heq : (fun p : H × H ↦ GaussianDecoupling.pairL2 p.1 p.2) =
        fun p ↦ PairTwoCopyTransport.prodLpToPairL2 (WithLp.toLp 2 p) := by
      funext p
      ext q
      fin_cases q <;> rfl
    rw [heq]
    fun_prop
  exact hpair.comp
    ((MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable.prodMap
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable)

lemma integral_localBlockFour_correlated
    (a : ℕ → ℝ) (zx zy : ℂ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (j : Fin (uniformBlockCount k))
    (f : EuclideanSpace ℝ (Fin 4) → ℝ) (hf : Measurable f) :
    (∫ p :
        (Fin (scale N0 (k + 1) - scale N0 k) → ℝ) ×
          (Fin (scale N0 (k + 1) - scale N0 k) → ℝ),
      f (PairHybridAlgebra.localBlockFour a hN0 k zx zy j p.1 p.1)
      ∂((Erdos88.Invariance.gaussianProductMeasure
          (scale N0 (k + 1) - scale N0 k)).prod
        (Erdos88.Invariance.gaussianProductMeasure
          (scale N0 (k + 1) - scale N0 k)))) =
      ∫ z : PiLp 2 (fun _ : Fin 2 ↦
          EuclideanSpace ℝ (Fin (scale N0 (k + 1) - scale N0 k))),
        f (GaussianDecoupling.innerFamilyCLM
          (correlatedBlockRows a zx zy hN0 k j) z)
        ∂(stdGaussian (PiLp 2 (fun _ : Fin 2 ↦
          EuclideanSpace ℝ (Fin (scale N0 (k + 1) - scale N0 k))))) := by
  let n := scale N0 (k + 1) - scale N0 k
  let μ := (Erdos88.Invariance.gaussianProductMeasure n).prod
    (Erdos88.Invariance.gaussianProductMeasure n)
  let T := PairTwoCopyTransport.concreteTwoCopiesToPairL2 n
  have hT : Measurable T := measurable_concreteTwoCopiesToPairL2 n
  have hcomp : AEStronglyMeasurable
      (fun z ↦ f (GaussianDecoupling.innerFamilyCLM
        (correlatedBlockRows a zx zy hN0 k j) z)) (μ.map T) :=
    ((hf.comp (GaussianDecoupling.innerFamilyCLM
      (correlatedBlockRows a zx zy hN0 k j)).continuous.measurable)).aestronglyMeasurable
  calc
    _ = ∫ p, f (GaussianDecoupling.innerFamilyCLM
          (correlatedBlockRows a zx zy hN0 k j) (T p)) ∂μ := by
      apply integral_congr_ae
      filter_upwards with p
      exact congrArg f (localBlockFour_correlated_eq_innerFamily
        a zx zy hN0 k j p.1 p.2)
    _ = ∫ z, f (GaussianDecoupling.innerFamilyCLM
          (correlatedBlockRows a zx zy hN0 k j) z) ∂(μ.map T) :=
      (integral_map hT.aemeasurable hcomp).symm
    _ = _ := by
      rw [PairTwoCopyTransport.map_concreteTwoCopiesToPairL2]

lemma integral_localBlockFour_independent
    (a : ℕ → ℝ) (zx zy : ℂ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (j : Fin (uniformBlockCount k))
    (f : EuclideanSpace ℝ (Fin 4) → ℝ) (hf : Measurable f) :
    (∫ p :
        (Fin (scale N0 (k + 1) - scale N0 k) → ℝ) ×
          (Fin (scale N0 (k + 1) - scale N0 k) → ℝ),
      f (PairHybridAlgebra.localBlockFour a hN0 k zx zy j p.1 p.2)
      ∂((Erdos88.Invariance.gaussianProductMeasure
          (scale N0 (k + 1) - scale N0 k)).prod
        (Erdos88.Invariance.gaussianProductMeasure
          (scale N0 (k + 1) - scale N0 k)))) =
      ∫ z : PiLp 2 (fun _ : Fin 2 ↦
          EuclideanSpace ℝ (Fin (scale N0 (k + 1) - scale N0 k))),
        f (GaussianDecoupling.innerFamilyCLM
          (independentBlockRows a zx zy hN0 k j) z)
        ∂(stdGaussian (PiLp 2 (fun _ : Fin 2 ↦
          EuclideanSpace ℝ (Fin (scale N0 (k + 1) - scale N0 k))))) := by
  let n := scale N0 (k + 1) - scale N0 k
  let μ := (Erdos88.Invariance.gaussianProductMeasure n).prod
    (Erdos88.Invariance.gaussianProductMeasure n)
  let T := PairTwoCopyTransport.concreteTwoCopiesToPairL2 n
  have hT : Measurable T := measurable_concreteTwoCopiesToPairL2 n
  have hcomp : AEStronglyMeasurable
      (fun z ↦ f (GaussianDecoupling.innerFamilyCLM
        (independentBlockRows a zx zy hN0 k j) z)) (μ.map T) :=
    ((hf.comp (GaussianDecoupling.innerFamilyCLM
      (independentBlockRows a zx zy hN0 k j)).continuous.measurable)).aestronglyMeasurable
  calc
    _ = ∫ p, f (GaussianDecoupling.innerFamilyCLM
          (independentBlockRows a zx zy hN0 k j) (T p)) ∂μ := by
      apply integral_congr_ae
      filter_upwards with p
      exact congrArg f (localBlockFour_independent_eq_innerFamily
        a zx zy hN0 k j p.1 p.2)
    _ = ∫ z, f (GaussianDecoupling.innerFamilyCLM
          (independentBlockRows a zx zy hN0 k j) z) ∂(μ.map T) :=
      (integral_map hT.aemeasurable hcomp).symm
    _ = _ := by
      rw [PairTwoCopyTransport.map_concreteTwoCopiesToPairL2]

end
end Erdos527.PairHybridIntegration


namespace Erdos527.PairApplication

open scoped BigOperators ENNReal NNReal Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Finset
open PairFactorization OnePointLindeberg CorrelationCount FlatVectorAPI
open CutoffLindebergBridge GaussianDecoupling
open PairCanonicalHybrid PairHybridAlgebra DirectGaussianPair
open PairTwoCopyTransport

noncomputable section

abbrev Gap (N0 k : ℕ) := scale N0 (k + 1) - scale N0 k
abbrev HGap (N0 k : ℕ) := EuclideanSpace ℝ (Fin (Gap N0 k))

lemma measurable_concreteTwoCopiesToPairL2 (n : ℕ) :
    Measurable (concreteTwoCopiesToPairL2 n) := by
  let H := EuclideanSpace ℝ (Fin n)
  have heq : concreteTwoCopiesToPairL2 n =
      fun p : (Fin n → ℝ) × (Fin n → ℝ) ↦
        prodLpToPairL2 (WithLp.toLp 2
          ((WithLp.toLp 2 p.1 : H), (WithLp.toLp 2 p.2 : H))) := by
    funext p
    ext q
    fin_cases q <;> rfl
  rw [heq]
  fun_prop

lemma blockCoordVector_eq_coordinateRow
    (a : ℕ → ℝ) (z : ℂ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (r : Fin (uniformBlockCount k)) (p : Bool) :
    blockCoordVector a z hN0 k r p =
      coordinateRow (flatBlockIncrementDirection a hN0 k z) r p := by
  ext i
  simp only [blockCoordVector_apply, coordinateRow_apply,
    flatBlockIncrementDirection, flatPhaseCoefficient, flatScaleIndex,
    scaleCoefficient]
  by_cases hi : uniformBlockOfOffset hN0 k i = r
  · rw [if_pos hi, if_pos hi.symm]
  · rw [if_neg hi, if_neg (Ne.symm hi)]
    cases p <;> simp [coord]

lemma inner_blockCoordVector_toLp
    (a : ℕ → ℝ) (z : ℂ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (r : Fin (uniformBlockCount k)) (p : Bool)
    (g : Fin (Gap N0 k) → ℝ) :
    inner ℝ (blockCoordVector a z hN0 k r p) (WithLp.toLp 2 g) =
      coord p (NormedLindeberg.linearCombination
        (flatBlockIncrementDirection a hN0 k z) g r) := by
  rw [blockCoordVector_eq_coordinateRow]
  exact (coord_linearCombination_eq_inner_coordinateRow
    (flatBlockIncrementDirection a hN0 k z) g r p).symm

def correlatedBlockFamily
    (a : ℕ → ℝ) (zx zy : ℂ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (j : Fin (uniformBlockCount k)) :
    Fin 4 → PiLp 2 (fun _ : Fin 2 ↦ HGap N0 k) :=
  ![pairL2 (blockCoordVector a zx hN0 k j false) 0,
    pairL2 (blockCoordVector a zx hN0 k j true) 0,
    pairL2 (blockCoordVector a zy hN0 k j false) 0,
    pairL2 (blockCoordVector a zy hN0 k j true) 0]

def independentBlockFamily
    (a : ℕ → ℝ) (zx zy : ℂ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (j : Fin (uniformBlockCount k)) :
    Fin 4 → PiLp 2 (fun _ : Fin 2 ↦ HGap N0 k) :=
  ![pairL2 (blockCoordVector a zx hN0 k j false) 0,
    pairL2 (blockCoordVector a zx hN0 k j true) 0,
    pairL2 0 (blockCoordVector a zy hN0 k j false),
    pairL2 0 (blockCoordVector a zy hN0 k j true)]

lemma innerFamily_correlatedBlockFamily
    (a : ℕ → ℝ) (zx zy : ℂ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (j : Fin (uniformBlockCount k))
    (p : (Fin (Gap N0 k) → ℝ) × (Fin (Gap N0 k) → ℝ)) :
    innerFamilyCLM (correlatedBlockFamily a zx zy hN0 k j)
        (concreteTwoCopiesToPairL2 (Gap N0 k) p) =
      localBlockFour a hN0 k zx zy j p.1 p.1 := by
  ext q
  fin_cases q <;>
    simp [correlatedBlockFamily, concreteTwoCopiesToPairL2,
      innerFamilyCLM_apply, localBlockFour, inner_blockCoordVector_toLp]

lemma innerFamily_independentBlockFamily
    (a : ℕ → ℝ) (zx zy : ℂ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (j : Fin (uniformBlockCount k))
    (p : (Fin (Gap N0 k) → ℝ) × (Fin (Gap N0 k) → ℝ)) :
    innerFamilyCLM (independentBlockFamily a zx zy hN0 k j)
        (concreteTwoCopiesToPairL2 (Gap N0 k) p) =
      localBlockFour a hN0 k zx zy j p.1 p.2 := by
  ext q
  fin_cases q <;>
    simp [independentBlockFamily, concreteTwoCopiesToPairL2,
      innerFamilyCLM_apply, localBlockFour, inner_blockCoordVector_toLp]

lemma integral_localBlockFour_correlated_eq_stdGaussian
    (a : ℕ → ℝ) (zx zy : ℂ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (j : Fin (uniformBlockCount k))
    (f : EuclideanSpace ℝ (Fin 4) → ℝ) (hf : Continuous f) :
    (∫ p : (Fin (Gap N0 k) → ℝ) × (Fin (Gap N0 k) → ℝ),
        f (localBlockFour a hN0 k zx zy j p.1 p.1)
        ∂((Erdos88.Invariance.gaussianProductMeasure (Gap N0 k)).prod
          (Erdos88.Invariance.gaussianProductMeasure (Gap N0 k)))) =
      ∫ z, f (innerFamilyCLM
          (correlatedBlockFamily a zx zy hN0 k j) z)
        ∂stdGaussian (PiLp 2 (fun _ : Fin 2 ↦ HGap N0 k)) := by
  let μ := (Erdos88.Invariance.gaussianProductMeasure (Gap N0 k)).prod
      (Erdos88.Invariance.gaussianProductMeasure (Gap N0 k))
  let T := concreteTwoCopiesToPairL2 (Gap N0 k)
  have hm : μ.map T =
      stdGaussian (PiLp 2 (fun _ : Fin 2 ↦ HGap N0 k)) :=
    map_concreteTwoCopiesToPairL2 (Gap N0 k)
  have hmeas : AEStronglyMeasurable
      (fun z ↦ f (innerFamilyCLM
        (correlatedBlockFamily a zx zy hN0 k j) z))
      (stdGaussian (PiLp 2 (fun _ : Fin 2 ↦ HGap N0 k))) :=
    (hf.comp (innerFamilyCLM
      (correlatedBlockFamily a zx zy hN0 k j)).continuous).aestronglyMeasurable
  rw [← hm]
  rw [integral_map]
  · apply integral_congr_ae
    filter_upwards with p
    rw [innerFamily_correlatedBlockFamily]
  · exact (measurable_concreteTwoCopiesToPairL2 (Gap N0 k)).aemeasurable
  · simpa [hm] using hmeas

lemma integral_localBlockFour_independent_eq_stdGaussian
    (a : ℕ → ℝ) (zx zy : ℂ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (j : Fin (uniformBlockCount k))
    (f : EuclideanSpace ℝ (Fin 4) → ℝ) (hf : Continuous f) :
    (∫ p : (Fin (Gap N0 k) → ℝ) × (Fin (Gap N0 k) → ℝ),
        f (localBlockFour a hN0 k zx zy j p.1 p.2)
        ∂((Erdos88.Invariance.gaussianProductMeasure (Gap N0 k)).prod
          (Erdos88.Invariance.gaussianProductMeasure (Gap N0 k)))) =
      ∫ z, f (innerFamilyCLM
          (independentBlockFamily a zx zy hN0 k j) z)
        ∂stdGaussian (PiLp 2 (fun _ : Fin 2 ↦ HGap N0 k)) := by
  let μ := (Erdos88.Invariance.gaussianProductMeasure (Gap N0 k)).prod
      (Erdos88.Invariance.gaussianProductMeasure (Gap N0 k))
  let T := concreteTwoCopiesToPairL2 (Gap N0 k)
  have hm : μ.map T =
      stdGaussian (PiLp 2 (fun _ : Fin 2 ↦ HGap N0 k)) :=
    map_concreteTwoCopiesToPairL2 (Gap N0 k)
  have hmeas : AEStronglyMeasurable
      (fun z ↦ f (innerFamilyCLM
        (independentBlockFamily a zx zy hN0 k j) z))
      (stdGaussian (PiLp 2 (fun _ : Fin 2 ↦ HGap N0 k))) :=
    (hf.comp (innerFamilyCLM
      (independentBlockFamily a zx zy hN0 k j)).continuous).aestronglyMeasurable
  rw [← hm]
  rw [integral_map]
  · apply integral_congr_ae
    filter_upwards with p
    rw [innerFamily_independentBlockFamily]
  · exact (measurable_concreteTwoCopiesToPairL2 (Gap N0 k)).aemeasurable
  · simpa [hm] using hmeas

def blockOffsetSet {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (j : Fin (uniformBlockCount k)) : Finset (Fin (Gap N0 k)) :=
  Finset.univ.filter (fun i ↦ uniformBlockOfOffset hN0 k i = j)

@[simp] lemma mem_blockOffsetSet {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (j : Fin (uniformBlockCount k)) (i : Fin (Gap N0 k)) :
    i ∈ blockOffsetSet hN0 k j ↔ uniformBlockOfOffset hN0 k i = j := by
  simp [blockOffsetSet]

lemma selectPairPi_eq_splice
    {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (j : Fin (uniformBlockCount k))
    (p : ((Fin (Gap N0 k) → ℝ) × (Fin (Gap N0 k) → ℝ)) ×
      ((Fin (Gap N0 k) → ℝ) × (Fin (Gap N0 k) → ℝ))) :
    PairSelectPi.selectPairPi (blockOffsetSet hN0 k j) p =
      (spliceScaleBlock hN0 k j p.1.1 p.2.1,
        spliceScaleBlock hN0 k j p.1.2 p.2.2) := by
  apply Prod.ext
  · funext i
    simp [PairSelectPi.selectPairPi, PairSelectPi.selectPi,
      MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow,
      spliceScaleBlock, blockOffsetSet]
  · funext i
    simp [PairSelectPi.selectPairPi, PairSelectPi.selectPi,
      MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow,
      spliceScaleBlock, blockOffsetSet]

lemma measurable_linearCombination {n l : ℕ} (v : Fin n → Fin l → ℂ)
    (r : Fin l) :
    Measurable (fun x : Fin n → ℝ ↦ NormedLindeberg.linearCombination v x r) := by
  unfold NormedLindeberg.linearCombination
  fun_prop

lemma cutoff_flatGaussianHybrid_measurable
    (a : ℕ → ℝ) (zx zy : ℂ) {N0 : ℕ} (hN0 : 0 < N0) (k t : ℕ)
    (endpointScale prefixScale : ℝ) :
    Measurable (fun p : (Fin (Gap N0 k) → ℝ) × (Fin (Gap N0 k) → ℝ) ↦
      pairEndpointPrefixCutoff (uniformBlockCount k) endpointScale prefixScale
        (flatGaussianHybrid a hN0 k zx zy t p.1 p.2)) := by
  apply (pairEndpointPrefixCutoff_contDiff _ _ _).continuous.measurable.comp
  apply measurable_pi_lambda
  intro q
  apply measurable_pi_lambda
  intro r
  by_cases hq : q = 0
  · subst q
    simp only [flatGaussianHybrid, if_pos]
    exact (measurable_linearCombination
      (flatBlockIncrementDirection a hN0 k zx) r).comp measurable_fst
  · have hq1 : q = 1 := Fin.eq_one_of_ne_zero q hq
    subst q
    simp only [flatGaussianHybrid, if_neg (by decide : (1 : Fin 2) ≠ 0)]
    by_cases hr : r.val < t
    · simp only [if_pos hr]
      exact (measurable_linearCombination
        (flatBlockIncrementDirection a hN0 k zy) r).comp measurable_snd
    · simp only [if_neg hr]
      exact (measurable_linearCombination
        (flatBlockIncrementDirection a hN0 k zy) r).comp measurable_fst

lemma integral_hybrid_eq_double_spliced
    (a : ℕ → ℝ) (zx zy : ℂ) {N0 : ℕ} (hN0 : 0 < N0) (k t : ℕ)
    (j : Fin (uniformBlockCount k)) (endpointScale prefixScale : ℝ) :
    (∫ p : (Fin (Gap N0 k) → ℝ) × (Fin (Gap N0 k) → ℝ),
      pairEndpointPrefixCutoff (uniformBlockCount k) endpointScale prefixScale
        (flatGaussianHybrid a hN0 k zx zy t p.1 p.2)
      ∂((Erdos88.Invariance.gaussianProductMeasure (Gap N0 k)).prod
        (Erdos88.Invariance.gaussianProductMeasure (Gap N0 k)))) =
    ∫ p : ((Fin (Gap N0 k) → ℝ) × (Fin (Gap N0 k) → ℝ)) ×
        ((Fin (Gap N0 k) → ℝ) × (Fin (Gap N0 k) → ℝ)),
      pairEndpointPrefixCutoff (uniformBlockCount k) endpointScale prefixScale
        (flatGaussianHybrid a hN0 k zx zy t
          (spliceScaleBlock hN0 k j p.1.1 p.2.1)
          (spliceScaleBlock hN0 k j p.1.2 p.2.2))
      ∂(((Erdos88.Invariance.gaussianProductMeasure (Gap N0 k)).prod
          (Erdos88.Invariance.gaussianProductMeasure (Gap N0 k))).prod
        ((Erdos88.Invariance.gaussianProductMeasure (Gap N0 k)).prod
          (Erdos88.Invariance.gaussianProductMeasure (Gap N0 k)))) := by
  let γ := Erdos88.Invariance.standardGaussian
  let μ := Erdos88.Invariance.gaussianProductMeasure (Gap N0 k)
  let F := fun p : (Fin (Gap N0 k) → ℝ) × (Fin (Gap N0 k) → ℝ) ↦
    pairEndpointPrefixCutoff (uniformBlockCount k) endpointScale prefixScale
      (flatGaussianHybrid a hN0 k zx zy t p.1 p.2)
  have hsel := PairSelectPi.integral_selectPairPi
    (A := ℝ) (ι := Fin (Gap N0 k)) γ
    (s := blockOffsetSet hN0 k j) F
    (cutoff_flatGaussianHybrid_measurable a zx zy hN0 k t
      endpointScale prefixScale).aestronglyMeasurable
  have hμ : (Measure.pi fun _ : Fin (Gap N0 k) ↦ γ) = μ := by
    rfl
  rw [hμ] at hsel
  rw [← hsel]
  apply integral_congr_ae
  filter_upwards with p
  rw [selectPairPi_eq_splice]

lemma integral_hybrid_current_correlated
    (a : ℕ → ℝ) (zx zy : ℂ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (j : Fin (uniformBlockCount k)) (endpointScale prefixScale : ℝ) :
    (∫ p : (Fin (Gap N0 k) → ℝ) × (Fin (Gap N0 k) → ℝ),
      pairEndpointPrefixCutoff (uniformBlockCount k) endpointScale prefixScale
        (flatGaussianHybrid a hN0 k zx zy j.val p.1 p.2)
      ∂((Erdos88.Invariance.gaussianProductMeasure (Gap N0 k)).prod
        (Erdos88.Invariance.gaussianProductMeasure (Gap N0 k)))) =
    ∫ fresh : (Fin (Gap N0 k) → ℝ) × (Fin (Gap N0 k) → ℝ),
      conditionalPairCutoff
        ((Erdos88.Invariance.gaussianProductMeasure (Gap N0 k)).prod
          (Erdos88.Invariance.gaussianProductMeasure (Gap N0 k)))
        (uniformBlockCount k) j endpointScale prefixScale
        (fun context ↦ hybridContext a hN0 k zx zy j context.1 context.2)
        (localBlockFour a hN0 k zx zy j fresh.1 fresh.1)
      ∂((Erdos88.Invariance.gaussianProductMeasure (Gap N0 k)).prod
        (Erdos88.Invariance.gaussianProductMeasure (Gap N0 k))) := by
  let μ := Erdos88.Invariance.gaussianProductMeasure (Gap N0 k)
  let P := μ.prod μ
  let F := fun p : (Fin (Gap N0 k) → ℝ) × (Fin (Gap N0 k) → ℝ) ↦
    pairEndpointPrefixCutoff (uniformBlockCount k) endpointScale prefixScale
      (flatGaussianHybrid a hN0 k zx zy j.val p.1 p.2)
  let S := blockOffsetSet hN0 k j
  let sel : (((Fin (Gap N0 k) → ℝ) × (Fin (Gap N0 k) → ℝ)) ×
      ((Fin (Gap N0 k) → ℝ) × (Fin (Gap N0 k) → ℝ))) →
      ((Fin (Gap N0 k) → ℝ) × (Fin (Gap N0 k) → ℝ)) :=
    PairSelectPi.selectPairPi S
  let G := fun p : ((Fin (Gap N0 k) → ℝ) × (Fin (Gap N0 k) → ℝ)) ×
      ((Fin (Gap N0 k) → ℝ) × (Fin (Gap N0 k) → ℝ)) ↦
    pairEndpointPrefixCutoff (uniformBlockCount k) endpointScale prefixScale
      (flatGaussianHybrid a hN0 k zx zy j.val
        (spliceScaleBlock hN0 k j p.1.1 p.2.1)
        (spliceScaleBlock hN0 k j p.1.2 p.2.2))
  have hG_eq : G = F ∘ sel := by
    funext p
    dsimp only [G, Function.comp_apply, F, sel, S]
    rw [selectPairPi_eq_splice]
  have hsel : Measurable sel := by
    exact (PairSelectPi.measurePreserving_selectPairPi
      Erdos88.Invariance.standardGaussian S).measurable
  have hGmeas : Measurable G := by
    rw [hG_eq]
    exact (cutoff_flatGaussianHybrid_measurable a zx zy hN0 k j.val
      endpointScale prefixScale).comp hsel
  have hGint : Integrable G (P.prod P) := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) hGmeas.aestronglyMeasurable
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg
      (pairEndpointPrefixCutoff_nonneg _ _ _ _)]
    exact pairEndpointPrefixCutoff_le_one _ _ _ _
  rw [integral_hybrid_eq_double_spliced a zx zy hN0 k j.val j
    endpointScale prefixScale]
  change (∫ p, G p ∂P.prod P) = _
  rw [integral_prod_symm G hGint]
  apply integral_congr_ae
  filter_upwards with fresh
  unfold conditionalPairCutoff
  apply integral_congr_ae
  filter_upwards with context
  dsimp only [G]
  rw [flatGaussianHybrid_splice_current_correlated]
  rfl

lemma integral_hybrid_current_independent
    (a : ℕ → ℝ) (zx zy : ℂ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (j : Fin (uniformBlockCount k)) (endpointScale prefixScale : ℝ) :
    (∫ p : (Fin (Gap N0 k) → ℝ) × (Fin (Gap N0 k) → ℝ),
      pairEndpointPrefixCutoff (uniformBlockCount k) endpointScale prefixScale
        (flatGaussianHybrid a hN0 k zx zy (j.val + 1) p.1 p.2)
      ∂((Erdos88.Invariance.gaussianProductMeasure (Gap N0 k)).prod
        (Erdos88.Invariance.gaussianProductMeasure (Gap N0 k)))) =
    ∫ fresh : (Fin (Gap N0 k) → ℝ) × (Fin (Gap N0 k) → ℝ),
      conditionalPairCutoff
        ((Erdos88.Invariance.gaussianProductMeasure (Gap N0 k)).prod
          (Erdos88.Invariance.gaussianProductMeasure (Gap N0 k)))
        (uniformBlockCount k) j endpointScale prefixScale
        (fun context ↦ hybridContext a hN0 k zx zy j context.1 context.2)
        (localBlockFour a hN0 k zx zy j fresh.1 fresh.2)
      ∂((Erdos88.Invariance.gaussianProductMeasure (Gap N0 k)).prod
        (Erdos88.Invariance.gaussianProductMeasure (Gap N0 k))) := by
  let μ := Erdos88.Invariance.gaussianProductMeasure (Gap N0 k)
  let P := μ.prod μ
  let F := fun p : (Fin (Gap N0 k) → ℝ) × (Fin (Gap N0 k) → ℝ) ↦
    pairEndpointPrefixCutoff (uniformBlockCount k) endpointScale prefixScale
      (flatGaussianHybrid a hN0 k zx zy (j.val + 1) p.1 p.2)
  let S := blockOffsetSet hN0 k j
  let sel : (((Fin (Gap N0 k) → ℝ) × (Fin (Gap N0 k) → ℝ)) ×
      ((Fin (Gap N0 k) → ℝ) × (Fin (Gap N0 k) → ℝ))) →
      ((Fin (Gap N0 k) → ℝ) × (Fin (Gap N0 k) → ℝ)) :=
    PairSelectPi.selectPairPi S
  let G := fun p : ((Fin (Gap N0 k) → ℝ) × (Fin (Gap N0 k) → ℝ)) ×
      ((Fin (Gap N0 k) → ℝ) × (Fin (Gap N0 k) → ℝ)) ↦
    pairEndpointPrefixCutoff (uniformBlockCount k) endpointScale prefixScale
      (flatGaussianHybrid a hN0 k zx zy (j.val + 1)
        (spliceScaleBlock hN0 k j p.1.1 p.2.1)
        (spliceScaleBlock hN0 k j p.1.2 p.2.2))
  have hG_eq : G = F ∘ sel := by
    funext p
    dsimp only [G, Function.comp_apply, F, sel, S]
    rw [selectPairPi_eq_splice]
  have hsel : Measurable sel := by
    exact (PairSelectPi.measurePreserving_selectPairPi
      Erdos88.Invariance.standardGaussian S).measurable
  have hGmeas : Measurable G := by
    rw [hG_eq]
    exact (cutoff_flatGaussianHybrid_measurable a zx zy hN0 k (j.val + 1)
      endpointScale prefixScale).comp hsel
  have hGint : Integrable G (P.prod P) := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) hGmeas.aestronglyMeasurable
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg
      (pairEndpointPrefixCutoff_nonneg _ _ _ _)]
    exact pairEndpointPrefixCutoff_le_one _ _ _ _
  rw [integral_hybrid_eq_double_spliced a zx zy hN0 k (j.val + 1) j
    endpointScale prefixScale]
  change (∫ p, G p ∂P.prod P) = _
  rw [integral_prod_symm G hGint]
  apply integral_congr_ae
  filter_upwards with fresh
  unfold conditionalPairCutoff
  apply integral_congr_ae
  filter_upwards with context
  dsimp only [G]
  rw [flatGaussianHybrid_splice_current_independent]
  rfl

lemma hybridContext_measurable
    (a : ℕ → ℝ) (zx zy : ℂ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (j : Fin (uniformBlockCount k)) :
    Measurable (fun context :
        (Fin (Gap N0 k) → ℝ) × (Fin (Gap N0 k) → ℝ) ↦
      hybridContext a hN0 k zx zy j context.1 context.2) := by
  apply measurable_pi_lambda
  intro q
  apply measurable_pi_lambda
  intro r
  by_cases hr : r = j
  · simp [hybridContext, hr]
  by_cases hq : q = 0
  · subst q
    simp only [hybridContext, hr, if_false, if_pos]
    exact (measurable_linearCombination
      (flatBlockIncrementDirection a hN0 k zx) r).comp measurable_fst
  · have hq1 : q = 1 := Fin.eq_one_of_ne_zero q hq
    subst q
    simp only [hybridContext, hr, if_false,
      if_neg (by decide : (1 : Fin 2) ≠ 0)]
    by_cases hlt : r.val < j.val
    · simp only [if_pos hlt]
      exact (measurable_linearCombination
        (flatBlockIncrementDirection a hN0 k zy) r).comp measurable_snd
    · simp only [if_neg hlt]
      exact (measurable_linearCombination
        (flatBlockIncrementDirection a hN0 k zy) r).comp measurable_fst

theorem flat_gaussian_hybrid_step_le
    (a : ℕ → ℝ) (zx zy : ℂ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (j : Fin (uniformBlockCount k)) (endpointScale prefixScale rho : ℝ)
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hx1 : ‖blockCoordVector a zx hN0 k j true‖ ≤ 1)
    (h00 : |inner ℝ (blockCoordVector a zx hN0 k j false)
      (blockCoordVector a zy hN0 k j false)| ≤ rho)
    (h01 : |inner ℝ (blockCoordVector a zx hN0 k j false)
      (blockCoordVector a zy hN0 k j true)| ≤ rho)
    (h10 : |inner ℝ (blockCoordVector a zx hN0 k j true)
      (blockCoordVector a zy hN0 k j false)| ≤ rho)
    (h11 : |inner ℝ (blockCoordVector a zx hN0 k j true)
      (blockCoordVector a zy hN0 k j true)| ≤ rho) :
    |(∫ p : (Fin (Gap N0 k) → ℝ) × (Fin (Gap N0 k) → ℝ),
        pairEndpointPrefixCutoff (uniformBlockCount k) endpointScale prefixScale
          (flatGaussianHybrid a hN0 k zx zy j.val p.1 p.2)
        ∂((Erdos88.Invariance.gaussianProductMeasure (Gap N0 k)).prod
          (Erdos88.Invariance.gaussianProductMeasure (Gap N0 k))) -
      ∫ p : (Fin (Gap N0 k) → ℝ) × (Fin (Gap N0 k) → ℝ),
        pairEndpointPrefixCutoff (uniformBlockCount k) endpointScale prefixScale
          (flatGaussianHybrid a hN0 k zx zy (j.val + 1) p.1 p.2)
        ∂((Erdos88.Invariance.gaussianProductMeasure (Gap N0 k)).prod
          (Erdos88.Invariance.gaussianProductMeasure (Gap N0 k))))| ≤
      12 * (pairCutoffLipschitzNN (uniformBlockCount k)
        endpointScale prefixScale : ℝ) * rho ^ (1 / 4 : ℝ) := by
  let P := (Erdos88.Invariance.gaussianProductMeasure (Gap N0 k)).prod
    (Erdos88.Invariance.gaussianProductMeasure (Gap N0 k))
  let base : ((Fin (Gap N0 k) → ℝ) × (Fin (Gap N0 k) → ℝ)) →
      PairIncrementSpace (uniformBlockCount k) :=
    fun context ↦ hybridContext a hN0 k zx zy j context.1 context.2
  let f := conditionalPairCutoff P (uniformBlockCount k) j
    endpointScale prefixScale base
  have hbase : Measurable base :=
    hybridContext_measurable a zx zy hN0 k j
  have hf : LipschitzWith
      (pairCutoffLipschitzNN (uniformBlockCount k) endpointScale prefixScale) f :=
    conditionalPairCutoff_lipschitz P (uniformBlockCount k) j
      endpointScale prefixScale base hbase
  have hdec := GaussianDecoupling.gaussianPairDiscrepancy_le_rpow_quarter
    (blockCoordVector a zx hN0 k j false)
    (blockCoordVector a zx hN0 k j true)
    (blockCoordVector a zy hN0 k j false)
    (blockCoordVector a zy hN0 k j true)
    hrho0 hrho1 hx1 h00 h01 h10 h11 f hf
  rw [integral_hybrid_current_correlated a zx zy hN0 k j
    endpointScale prefixScale,
    integral_hybrid_current_independent a zx zy hN0 k j
      endpointScale prefixScale]
  rw [integral_localBlockFour_correlated_eq_stdGaussian
    a zx zy hN0 k j f hf.continuous,
    integral_localBlockFour_independent_eq_stdGaussian
    a zx zy hN0 k j f hf.continuous]
  simpa [GaussianDecoupling.gaussianPairDiscrepancy,
    correlatedBlockFamily, independentBlockFamily] using hdec

lemma gaussianBlockHybrid_eq_flatGaussianHybrid
    (a : ℕ → ℝ) (zx zy : ℂ) {N0 : ℕ} (hN0 : 0 < N0) (k t : ℕ)
    (g h : Fin (Gap N0 k) → ℝ) :
    gaussianBlockHybrid
        (flatBlockIncrementDirection a hN0 k zx)
        (flatBlockIncrementDirection a hN0 k zy) t g h =
      flatGaussianHybrid a hN0 k zx zy t g h := by
  rfl

lemma pairDirectionOf_flat_eq_flatPairDirection
    (a : ℕ → ℝ) (zx zy : ℂ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) :
    pairDirectionOf
        (flatBlockIncrementDirection a hN0 k zx)
        (flatBlockIncrementDirection a hN0 k zy) =
      PairFactorization.flatPairDirection a hN0 k zx zy := by
  ext i q r
  fin_cases q <;> simp [pairDirectionOf, PairFactorization.flatPairDirection]

theorem flat_pair_factorization_of_block_bounds
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) (zx zy : ℂ)
    (hzx : ‖zx‖ = 1) (hzy : ‖zy‖ = 1)
    (endpointScale prefixScale rho : ℝ)
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hx1 : ∀ j : Fin (uniformBlockCount k),
      ‖blockCoordVector a zx hN0 k j true‖ ≤ 1)
    (h00 : ∀ j : Fin (uniformBlockCount k),
      |inner ℝ (blockCoordVector a zx hN0 k j false)
        (blockCoordVector a zy hN0 k j false)| ≤ rho)
    (h01 : ∀ j : Fin (uniformBlockCount k),
      |inner ℝ (blockCoordVector a zx hN0 k j false)
        (blockCoordVector a zy hN0 k j true)| ≤ rho)
    (h10 : ∀ j : Fin (uniformBlockCount k),
      |inner ℝ (blockCoordVector a zx hN0 k j true)
        (blockCoordVector a zy hN0 k j false)| ≤ rho)
    (h11 : ∀ j : Fin (uniformBlockCount k),
      |inner ℝ (blockCoordVector a zx hN0 k j true)
        (blockCoordVector a zy hN0 k j true)| ≤ rho) :
    |pairRademacherExpectation endpointScale prefixScale
          (PairFactorization.flatPairDirection a hN0 k zx zy) -
        phaseRademacherExpectation endpointScale prefixScale
            (flatBlockIncrementDirection a hN0 k zx) *
          phaseRademacherExpectation endpointScale prefixScale
            (flatBlockIncrementDirection a hN0 k zy)| ≤
      18 * flatOnePointLindebergError a N0 k endpointScale prefixScale +
        12 * (uniformBlockCount k : ℝ) *
          (pairCutoffLipschitzNN (uniformBlockCount k)
            endpointScale prefixScale : ℝ) * rho ^ (1 / 4 : ℝ) := by
  let vx := flatBlockIncrementDirection a hN0 k zx
  let vy := flatBlockIncrementDirection a hN0 k zy
  let Q := gaussianBlockHybridExpectation endpointScale prefixScale vx vy
  let K : ℝ := (pairCutoffLipschitzNN (uniformBlockCount k)
    endpointScale prefixScale : ℝ)
  have hstep (j : Fin (uniformBlockCount k)) :
      |Q j - Q (j + 1)| ≤ 12 * K * rho ^ (1 / 4 : ℝ) := by
    dsimp only [Q, gaussianBlockHybridExpectation, vx, vy, K]
    simpa only [gaussianBlockHybrid_eq_flatGaussianHybrid] using
      flat_gaussian_hybrid_step_le a zx zy hN0 k j endpointScale prefixScale rho
        hrho0 hrho1 (hx1 j) (h00 j) (h01 j) (h10 j) (h11 j)
  have htel := Erdos88.Invariance.telescoping_abs Q (uniformBlockCount k)
  have hgaussQ : |Q 0 - Q (uniformBlockCount k)| ≤
      12 * (uniformBlockCount k : ℝ) * K * rho ^ (1 / 4 : ℝ) := by
    apply htel.trans
    calc
      (∑ j : Fin (uniformBlockCount k), |Q j - Q (j + 1)|) ≤
          ∑ _j : Fin (uniformBlockCount k),
            12 * K * rho ^ (1 / 4 : ℝ) :=
        Finset.sum_le_sum fun j _ ↦ hstep j
      _ = 12 * (uniformBlockCount k : ℝ) * K *
          rho ^ (1 / 4 : ℝ) := by simp; ring
  have hQ0 : Q 0 = pairGaussianExpectation endpointScale prefixScale
      (PairFactorization.flatPairDirection a hN0 k zx zy) := by
    dsimp only [Q]
    rw [gaussianBlockHybridExpectation_zero]
    rw [pairDirectionOf_flat_eq_flatPairDirection]
  have hQend : Q (uniformBlockCount k) =
      phaseGaussianExpectation endpointScale prefixScale
          (flatBlockIncrementDirection a hN0 k zx) *
        phaseGaussianExpectation endpointScale prefixScale
          (flatBlockIncrementDirection a hN0 k zy) := by
    exact gaussianBlockHybridExpectation_end endpointScale prefixScale vx vy
  have hgauss :
      |pairGaussianExpectation endpointScale prefixScale
          (PairFactorization.flatPairDirection a hN0 k zx zy) -
        phaseGaussianExpectation endpointScale prefixScale
            (flatBlockIncrementDirection a hN0 k zx) *
          phaseGaussianExpectation endpointScale prefixScale
            (flatBlockIncrementDirection a hN0 k zy)| ≤
      12 * (uniformBlockCount k : ℝ) * K * rho ^ (1 / 4 : ℝ) := by
    rw [← hQ0, ← hQend]
    exact hgaussQ
  exact PairFactorization.flat_pair_rademacher_factorization_of_gaussian_bound
    a hsmall hN0 k zx zy hzx hzy endpointScale prefixScale
      (12 * (uniformBlockCount k : ℝ) * K * rho ^ (1 / 4 : ℝ)) hgauss

lemma abs_blockCovariance_le_of_not_isCorrelated
    (a : ℕ → ℂ) (m M : ℕ) (x y : UnitAddCircle) (rho : ℝ)
    (h : ¬ IsCorrelated a m M x y rho) (p q : Bool) :
    |blockCovariance a m M x y p q| ≤ rho := by
  apply le_of_not_gt
  intro hpq
  exact h ⟨p, q, hpq.le⟩

lemma uniformBlock_energy_le_one_of_envelope
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ)
    (henv : coefficientEnvelope a N0 k ≤ 1)
    (j : Fin (uniformBlockCount k)) :
    (∑ n ∈ uniformBlock N0 k j, |a n| ^ 2) ≤ 1 := by
  have hδ0 := coefficientEnvelope_nonneg a hsmall N0 k
  have hscaled : ∀ n ∈ uniformBlock N0 k j,
      Real.sqrt (n : ℝ) * |a n| ≤ coefficientEnvelope a N0 k := by
    intro n hn
    apply scaledAbs_le_coefficientEnvelope a hsmall
    exact (uniformBlock_start_ge_scale N0 k j).trans
      (Finset.mem_Ico.mp hn).1
  have hraw := sum_sq_uniformBlock_le a hδ0 hN0 hscaled
  apply hraw.trans
  apply (div_le_one (by positivity : (0 : ℝ) < 2 ^ k)).2
  have hδsq : coefficientEnvelope a N0 k ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (coefficientEnvelope a N0 k)]
  exact hδsq.trans (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))

def phasePoint (x : UnitAddCircle) : ℂ :=
  BoundedGaps.Maynard.unitAddCircleAddChar x

lemma norm_phasePoint (x : UnitAddCircle) : ‖phasePoint x‖ = 1 := by
  change ‖((AddCircle.toCircle x : Circle) : ℂ)‖ = 1
  exact Circle.norm_coe _

lemma phasePoint_eq_pairHybrid_phasePoint (x : UnitAddCircle) :
    phasePoint x = PairHybridIntegration.phasePoint x := by
  rfl

/-- Representation-free flat two-phase factorization.  The only analytic
hypotheses beyond the coefficient assumptions are the eventually valid
envelope bound and the four-covariance `IsCorrelated` test on each block. -/
theorem flat_pair_factorization_of_not_correlated
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) (x y : UnitAddCircle)
    (endpointScale prefixScale rho : ℝ)
    (henv : coefficientEnvelope a N0 k ≤ 1)
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (huncorrelated : ∀ j : Fin (uniformBlockCount k),
      ¬ IsCorrelated (fun n ↦ (a n : ℂ))
        (uniformEndpoint N0 k j - 1) (uniformBlockLength N0 k) x y rho) :
    |pairRademacherExpectation endpointScale prefixScale
          (PairFactorization.flatPairDirection a hN0 k
            (phasePoint x) (phasePoint y)) -
        phaseRademacherExpectation endpointScale prefixScale
            (flatBlockIncrementDirection a hN0 k (phasePoint x)) *
          phaseRademacherExpectation endpointScale prefixScale
            (flatBlockIncrementDirection a hN0 k (phasePoint y))| ≤
      18 * flatOnePointLindebergError a N0 k endpointScale prefixScale +
        12 * (uniformBlockCount k : ℝ) *
          (pairCutoffLipschitzNN (uniformBlockCount k)
            endpointScale prefixScale : ℝ) * rho ^ (1 / 4 : ℝ) := by
  apply flat_pair_factorization_of_block_bounds a hsmall hN0 k
    (phasePoint x) (phasePoint y) (norm_phasePoint x) (norm_phasePoint y)
    endpointScale prefixScale rho hrho0 hrho1
  · intro j
    rw [phasePoint_eq_pairHybrid_phasePoint]
    exact PairHybridIntegration.norm_blockCoordVector_phasePoint_le_one
      a x true hN0 k j (uniformBlock_energy_le_one_of_envelope
        a hsmall hN0 k henv j)
  · intro j
    rw [phasePoint_eq_pairHybrid_phasePoint x,
      phasePoint_eq_pairHybrid_phasePoint y]
    rw [PairHybridIntegration.inner_blockCoordVector_phasePoint_eq_blockCovariance]
    exact abs_blockCovariance_le_of_not_isCorrelated _ _ _ _ _ _
      (huncorrelated j) false false
  · intro j
    rw [phasePoint_eq_pairHybrid_phasePoint x,
      phasePoint_eq_pairHybrid_phasePoint y]
    rw [PairHybridIntegration.inner_blockCoordVector_phasePoint_eq_blockCovariance]
    exact abs_blockCovariance_le_of_not_isCorrelated _ _ _ _ _ _
      (huncorrelated j) false true
  · intro j
    rw [phasePoint_eq_pairHybrid_phasePoint x,
      phasePoint_eq_pairHybrid_phasePoint y]
    rw [PairHybridIntegration.inner_blockCoordVector_phasePoint_eq_blockCovariance]
    exact abs_blockCovariance_le_of_not_isCorrelated _ _ _ _ _ _
      (huncorrelated j) true false
  · intro j
    rw [phasePoint_eq_pairHybrid_phasePoint x,
      phasePoint_eq_pairHybrid_phasePoint y]
    rw [PairHybridIntegration.inner_blockCoordVector_phasePoint_eq_blockCovariance]
    exact abs_blockCovariance_le_of_not_isCorrelated _ _ _ _ _ _
      (huncorrelated j) true true

lemma pairCutoffLipschitzNN_le_flatPairCutoffOperatorBudget
    (k : ℕ) (endpointScale prefixScale : ℝ) :
    (pairCutoffLipschitzNN (uniformBlockCount k)
        endpointScale prefixScale : ℝ) ≤
      PairFactorization.flatPairCutoffOperatorBudget k endpointScale prefixScale := by
  change SmoothCutoffC4.cutoffC4 *
      (∑ q : Fin 2 × Option (Fin (uniformBlockCount k)),
        ‖pairEndpointPrefixForms (uniformBlockCount k)
          endpointScale prefixScale q‖) ≤ _
  calc
    _ ≤ SmoothCutoffC4.cutoffC4 *
        (2 * (((((uniformBlockCount k + 1 : ℕ) : ℝ) *
          (|endpointScale| + |prefixScale|) * uniformBlockCount k)))) := by
      exact mul_le_mul_of_nonneg_left
        (PairFactorization.sum_norm_pairEndpointPrefixForms_le
          (uniformBlockCount k) endpointScale prefixScale)
        SmoothCutoffC4.cutoffC4_nonneg
    _ = PairFactorization.flatPairCutoffOperatorBudget k
        endpointScale prefixScale := by
      unfold PairFactorization.flatPairCutoffOperatorBudget
        flatCutoffOperatorBudget
      ring

/-- The one-sided form consumed by the finite-grid second-moment argument,
with the exact pair Lipschitz constant replaced by the pre-existing coarse
operator budget. -/
theorem flat_pair_expectation_le_product_add_of_not_correlated
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) (x y : UnitAddCircle)
    (endpointScale prefixScale rho : ℝ)
    (henv : coefficientEnvelope a N0 k ≤ 1)
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (huncorrelated : ∀ j : Fin (uniformBlockCount k),
      ¬ IsCorrelated (fun n ↦ (a n : ℂ))
        (uniformEndpoint N0 k j - 1) (uniformBlockLength N0 k) x y rho) :
    pairRademacherExpectation endpointScale prefixScale
          (PairFactorization.flatPairDirection a hN0 k
            (phasePoint x) (phasePoint y)) ≤
      phaseRademacherExpectation endpointScale prefixScale
            (flatBlockIncrementDirection a hN0 k (phasePoint x)) *
          phaseRademacherExpectation endpointScale prefixScale
            (flatBlockIncrementDirection a hN0 k (phasePoint y)) +
        (18 * flatOnePointLindebergError a N0 k endpointScale prefixScale +
          12 * (uniformBlockCount k : ℝ) *
            PairFactorization.flatPairCutoffOperatorBudget k
              endpointScale prefixScale * rho ^ (1 / 4 : ℝ)) := by
  have habs := flat_pair_factorization_of_not_correlated
    a hsmall hN0 k x y endpointScale prefixScale rho henv hrho0 hrho1
      huncorrelated
  have hK := pairCutoffLipschitzNN_le_flatPairCutoffOperatorBudget
    k endpointScale prefixScale
  have herr :
      18 * flatOnePointLindebergError a N0 k endpointScale prefixScale +
          12 * (uniformBlockCount k : ℝ) *
            (pairCutoffLipschitzNN (uniformBlockCount k)
              endpointScale prefixScale : ℝ) * rho ^ (1 / 4 : ℝ) ≤
        18 * flatOnePointLindebergError a N0 k endpointScale prefixScale +
          12 * (uniformBlockCount k : ℝ) *
            PairFactorization.flatPairCutoffOperatorBudget k
              endpointScale prefixScale * rho ^ (1 / 4 : ℝ) := by
    gcongr
  have habs' := habs.trans herr
  have hle := (le_abs_self
    (pairRademacherExpectation endpointScale prefixScale
          (PairFactorization.flatPairDirection a hN0 k
            (phasePoint x) (phasePoint y)) -
      phaseRademacherExpectation endpointScale prefixScale
            (flatBlockIncrementDirection a hN0 k (phasePoint x)) *
          phaseRademacherExpectation endpointScale prefixScale
            (flatBlockIncrementDirection a hN0 k (phasePoint y)))).trans habs'
  linarith

lemma uniformBlockCount_le_stepFactor_sq (k : ℕ) :
    uniformBlockCount k ≤ (2 ^ stepExponent k) ^ 2 := by
  unfold uniformBlockCount
  calc
    2 ^ k * (2 ^ stepExponent k - 1) ≤
        2 ^ stepExponent k * 2 ^ stepExponent k :=
      Nat.mul_le_mul
        (Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ))
          (le_stepExponent k))
        (Nat.sub_le _ _)
    _ = (2 ^ stepExponent k) ^ 2 := by ring

/-- The raw block telescope and pair-cutoff operator budget cost at most a
tenth power of the scale step factor, once the two elementary polynomial
inputs (cutoff constant and chosen scales) have been absorbed. -/
lemma uniformBlockCount_mul_flatPairBudget_le_stepFactor_pow_ten
    (k : ℕ) (endpointScale prefixScale : ℝ)
    (hscale : |endpointScale| + |prefixScale| ≤
      ((2 ^ stepExponent k : ℕ) : ℝ))
    (hC4 : 4 * SmoothCutoffC4.cutoffC4 ≤
      ((2 ^ stepExponent k : ℕ) : ℝ)) :
    (uniformBlockCount k : ℝ) *
        PairFactorization.flatPairCutoffOperatorBudget k
          endpointScale prefixScale ≤
      ((2 ^ stepExponent k : ℕ) : ℝ) ^ 10 := by
  let F : ℝ := ((2 ^ stepExponent k : ℕ) : ℝ)
  let L : ℝ := (uniformBlockCount k : ℝ)
  have hF1 : 1 ≤ F := by
    dsimp only [F]
    exact_mod_cast one_le_stepFactor k
  have hF0 : 0 ≤ F := le_trans (by norm_num) hF1
  have hL0 : 0 ≤ L := by positivity
  have hL : L ≤ F ^ 2 := by
    dsimp only [L, F]
    exact_mod_cast uniformBlockCount_le_stepFactor_sq k
  have hL1 : (((uniformBlockCount k + 1 : ℕ) : ℝ)) ≤ 2 * F ^ 2 := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith [sq_nonneg F]
  have hhead :
      2 * SmoothCutoffC4.cutoffC4 *
          (((uniformBlockCount k + 1 : ℕ) : ℝ)) ≤ F ^ 3 := by
    calc
      _ ≤ 2 * SmoothCutoffC4.cutoffC4 * (2 * F ^ 2) := by
        exact mul_le_mul_of_nonneg_left hL1
          (mul_nonneg (by norm_num) SmoothCutoffC4.cutoffC4_nonneg)
      _ = (4 * SmoothCutoffC4.cutoffC4) * F ^ 2 := by ring
      _ ≤ F * F ^ 2 := by
        exact mul_le_mul_of_nonneg_right hC4 (sq_nonneg F)
      _ = F ^ 3 := by ring
  calc
    L * PairFactorization.flatPairCutoffOperatorBudget k
          endpointScale prefixScale =
        L * (2 * SmoothCutoffC4.cutoffC4 *
          (((uniformBlockCount k + 1 : ℕ) : ℝ))) *
          (|endpointScale| + |prefixScale|) * L := by
      dsimp only [L]
      unfold PairFactorization.flatPairCutoffOperatorBudget
        flatCutoffOperatorBudget
      ring
    _ ≤ F ^ 2 * F ^ 3 * F * F ^ 2 := by
      gcongr
      exact mul_nonneg
        (mul_nonneg (by norm_num) SmoothCutoffC4.cutoffC4_nonneg)
        (by positivity)
    _ = F ^ 8 := by ring
    _ ≤ F ^ 10 := pow_le_pow_right₀ hF1 (by norm_num)

/-- Application form with the off-correlation loss normalized to the
generous `stepFactor^10` budget used by branching arithmetic. -/
theorem flat_pair_expectation_le_product_add_stepFactor_pow_ten
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) (x y : UnitAddCircle)
    (endpointScale prefixScale rho : ℝ)
    (henv : coefficientEnvelope a N0 k ≤ 1)
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hscale : |endpointScale| + |prefixScale| ≤
      ((2 ^ stepExponent k : ℕ) : ℝ))
    (hC4 : 4 * SmoothCutoffC4.cutoffC4 ≤
      ((2 ^ stepExponent k : ℕ) : ℝ))
    (huncorrelated : ∀ j : Fin (uniformBlockCount k),
      ¬ IsCorrelated (fun n ↦ (a n : ℂ))
        (uniformEndpoint N0 k j - 1) (uniformBlockLength N0 k) x y rho) :
    pairRademacherExpectation endpointScale prefixScale
          (PairFactorization.flatPairDirection a hN0 k
            (phasePoint x) (phasePoint y)) ≤
      phaseRademacherExpectation endpointScale prefixScale
            (flatBlockIncrementDirection a hN0 k (phasePoint x)) *
          phaseRademacherExpectation endpointScale prefixScale
            (flatBlockIncrementDirection a hN0 k (phasePoint y)) +
        (18 * flatOnePointLindebergError a N0 k endpointScale prefixScale +
          12 * ((2 ^ stepExponent k : ℕ) : ℝ) ^ 10 *
            rho ^ (1 / 4 : ℝ)) := by
  have hraw := flat_pair_expectation_le_product_add_of_not_correlated
    a hsmall hN0 k x y endpointScale prefixScale rho henv hrho0 hrho1
      huncorrelated
  have hpoly := uniformBlockCount_mul_flatPairBudget_le_stepFactor_pow_ten
    k endpointScale prefixScale hscale hC4
  have hoff :
      12 * (uniformBlockCount k : ℝ) *
          PairFactorization.flatPairCutoffOperatorBudget k
            endpointScale prefixScale * rho ^ (1 / 4 : ℝ) ≤
        12 * ((2 ^ stepExponent k : ℕ) : ℝ) ^ 10 *
          rho ^ (1 / 4 : ℝ) := by
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hrho0 _)
    nlinarith
  apply hraw.trans
  calc
    _ = (12 * (uniformBlockCount k : ℝ) *
          PairFactorization.flatPairCutoffOperatorBudget k
            endpointScale prefixScale * rho ^ (1 / 4 : ℝ)) +
        18 * flatOnePointLindebergError a N0 k endpointScale prefixScale +
        phaseRademacherExpectation endpointScale prefixScale
            (flatBlockIncrementDirection a hN0 k (phasePoint x)) *
          phaseRademacherExpectation endpointScale prefixScale
            (flatBlockIncrementDirection a hN0 k (phasePoint y)) := by ring
    _ ≤ (12 * ((2 ^ stepExponent k : ℕ) : ℝ) ^ 10 *
          rho ^ (1 / 4 : ℝ)) +
        18 * flatOnePointLindebergError a N0 k endpointScale prefixScale +
        phaseRademacherExpectation endpointScale prefixScale
            (flatBlockIncrementDirection a hN0 k (phasePoint x)) *
          phaseRademacherExpectation endpointScale prefixScale
            (flatBlockIncrementDirection a hN0 k (phasePoint y)) := by
      gcongr
    _ = _ := by ring

end
end Erdos527.PairApplication

open scoped BigOperators ENNReal
open Filter MeasureTheory Set

namespace Erdos527.FinalProbabilityAssembly

noncomputable section

variable {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X]

/-- Simultaneously exclude every branching transition failure and every
auxiliary grid failure. -/
def noCombinedFailureSet
    (A : ℕ → Ω → Finset X) (size : ℕ → ℕ)
    (gridFailure : ℕ → Set Ω) : Set Ω :=
  (⋃ t : ℕ,
    FiniteGridBranching.transitionFailure A size t ∪ gridFailure t)ᶜ

theorem measurableSet_noCombinedFailureSet
    (A : ℕ → Ω → Finset X) (size : ℕ → ℕ)
    (gridFailure : ℕ → Set Ω)
    (htransitionMeas : ∀ t,
      MeasurableSet (FiniteGridBranching.transitionFailure A size t))
    (hgridMeas : ∀ t, MeasurableSet (gridFailure t)) :
    MeasurableSet (noCombinedFailureSet A size gridFailure) := by
  apply MeasurableSet.compl
  apply MeasurableSet.iUnion
  intro t
  exact (htransitionMeas t).union (hgridMeas t)

lemma compl_noCombinedFailureSet
    (A : ℕ → Ω → Finset X) (size : ℕ → ℕ)
    (gridFailure : ℕ → Set Ω) :
    (noCombinedFailureSet A size gridFailure)ᶜ =
      ⋃ t : ℕ,
        FiniteGridBranching.transitionFailure A size t ∪ gridFailure t := by
  unfold noCombinedFailureSet
  rw [compl_compl]

/-- Quantitative union bound for the combined no-failure event. -/
theorem measure_compl_noCombinedFailureSet_le
    (μ : Measure Ω)
    (A : ℕ → Ω → Finset X) (size : ℕ → ℕ)
    (gridFailure : ℕ → Set Ω) (b c : ℕ → ℝ≥0∞)
    (htransitionBound : ∀ t,
      μ (FiniteGridBranching.transitionFailure A size t) ≤ b t)
    (hgridBound : ∀ t, μ (gridFailure t) ≤ c t) :
    μ (noCombinedFailureSet A size gridFailure)ᶜ ≤
      ∑' t, (b t + c t) := by
  rw [compl_noCombinedFailureSet]
  calc
    μ (⋃ t : ℕ,
        FiniteGridBranching.transitionFailure A size t ∪ gridFailure t)
        ≤ ∑' t : ℕ,
          μ (FiniteGridBranching.transitionFailure A size t ∪ gridFailure t) :=
      measure_iUnion_le _
    _ ≤ ∑' t : ℕ, (b t + c t) := by
      apply ENNReal.tsum_le_tsum
      intro t
      exact (measure_union_le _ _).trans
        (add_le_add (htransitionBound t) (hgridBound t))

/-- A direct probability-one-assembly lemma. Its output is a measurable set
of mass at least `1 - tsum (b+c)`. Every point of this set has nonempty alive
sets at all relative generations and avoids every auxiliary grid failure. -/
theorem exists_measurable_noCombinedFailureSet
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ℕ → Ω → Finset X) (size : ℕ → ℕ)
    (gridFailure : ℕ → Set Ω) (b c : ℕ → ℝ≥0∞)
    (hinitial : ∀ ω, ω ∈ FiniteGridBranching.StrongAt A size 0)
    (hsize : ∀ t, 0 < size t)
    (htransitionMeas : ∀ t,
      MeasurableSet (FiniteGridBranching.transitionFailure A size t))
    (hgridMeas : ∀ t, MeasurableSet (gridFailure t))
    (htransitionBound : ∀ t,
      μ (FiniteGridBranching.transitionFailure A size t) ≤ b t)
    (hgridBound : ∀ t, μ (gridFailure t) ≤ c t) :
    ∃ G : Set Ω,
      MeasurableSet G ∧
      1 - (∑' t, (b t + c t)) ≤ μ G ∧
      ∀ ω ∈ G,
        (∀ t, (A t ω).Nonempty) ∧
        (∀ t, ω ∉ gridFailure t) := by
  let G := noCombinedFailureSet A size gridFailure
  have hGmeas : MeasurableSet G :=
    measurableSet_noCombinedFailureSet A size gridFailure
      htransitionMeas hgridMeas
  have hGcompl : μ Gᶜ ≤ ∑' t, (b t + c t) :=
    measure_compl_noCombinedFailureSet_le μ A size gridFailure b c
      htransitionBound hgridBound
  refine ⟨G, hGmeas, ?_, ?_⟩
  · rw [← compl_compl G, prob_compl_eq_one_sub hGmeas.compl]
    exact tsub_le_tsub_left hGcompl 1
  · intro ω hω
    have havoid : ∀ t,
        ω ∉ FiniteGridBranching.transitionFailure A size t ∧
          ω ∉ gridFailure t := by
      simpa only [G, noCombinedFailureSet, mem_compl_iff, mem_iUnion,
        mem_union, not_exists, not_or] using hω
    have hstrong :
        ω ∈ FiniteGridBranching.AllStrongFrom A size 0 := by
      apply FiniteGridBranching.noTransitionFailure_implies_allStrong
        A size 0 ω (hinitial ω)
      intro t _ht
      exact (havoid t).1
    constructor
    · intro t
      apply Finset.card_pos.mp
      exact (hsize t).trans_le (hstrong t (Nat.zero_le t))
    · intro t
      exact (havoid t).2

/-- Specialization to the shifted concrete flat-alive process. This is the
shape needed by the final Erdős 527 assembly: transition failures use relative
time `t`, while their target size is the absolute-scale target at `start+t`. -/
theorem exists_measurable_flatAlive_noFailureSet
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (start : ℕ)
    (gridFailure : ℕ → Set (ℕ → ℝ)) (b c : ℕ → ℝ≥0∞)
    (hinitial : ∀ ε,
      ε ∈ FiniteGridBranching.StrongAt
        (FlatAliveGood.flatAlive a hN0 start)
        (fun t => BranchParameterArithmetic.targetSize (start + t)) 0)
    (htransitionMeas : ∀ t,
      MeasurableSet
        (FiniteGridBranching.transitionFailure
          (FlatAliveGood.flatAlive a hN0 start)
          (fun u => BranchParameterArithmetic.targetSize (start + u)) t))
    (hgridMeas : ∀ t, MeasurableSet (gridFailure t))
    (htransitionBound : ∀ t,
      rademacherProductMeasure
        (FiniteGridBranching.transitionFailure
          (FlatAliveGood.flatAlive a hN0 start)
          (fun u => BranchParameterArithmetic.targetSize (start + u)) t) ≤ b t)
    (hgridBound : ∀ t, rademacherProductMeasure (gridFailure t) ≤ c t) :
    ∃ G : Set (ℕ → ℝ),
      MeasurableSet G ∧
      1 - (∑' t, (b t + c t)) ≤ rademacherProductMeasure G ∧
      ∀ ε ∈ G,
        (∀ t, (FlatAliveGood.flatAlive a hN0 start t ε).Nonempty) ∧
        (∀ t, ε ∉ gridFailure t) := by
  exact exists_measurable_noCombinedFailureSet rademacherProductMeasure
    (FlatAliveGood.flatAlive a hN0 start)
    (fun t => BranchParameterArithmetic.targetSize (start + t))
    gridFailure b c hinitial
    (fun t => BranchParameterArithmetic.targetSize_pos (start + t))
    htransitionMeas hgridMeas htransitionBound hgridBound

/-- Fully concrete auxiliary-grid specialization. The grid failures are the
union of the flat-prefix and derivative grid exceptions at absolute scale
`start+t`; their ENNReal majorant is the `ofReal` of the combined real bound. -/
theorem exists_measurable_flatAlive_combinedGrid_goodSet
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} [NeZero N0] (hN0 : 0 < N0) (start : ℕ)
    (b : ℕ → ℝ≥0∞)
    (hinitial : ∀ ε,
      ε ∈ FiniteGridBranching.StrongAt
        (FlatAliveGood.flatAlive a hN0 start)
        (fun t => BranchParameterArithmetic.targetSize (start + t)) 0)
    (htransitionMeas : ∀ t,
      MeasurableSet
        (FiniteGridBranching.transitionFailure
          (FlatAliveGood.flatAlive a hN0 start)
          (fun u => BranchParameterArithmetic.targetSize (start + u)) t))
    (htransitionBound : ∀ t,
      rademacherProductMeasure
        (FiniteGridBranching.transitionFailure
          (FlatAliveGood.flatAlive a hN0 start)
          (fun u => BranchParameterArithmetic.targetSize (start + u)) t) ≤ b t)
    (henv : ∀ t, coefficientEnvelope a N0 (start + t) ≤ 1)
    (hlog : ∀ t,
      (2080 : ℝ) ≤ Real.log (scale N0 (start + t + 1) : ℝ)) :
    ∃ G : Set (ℕ → ℝ),
      MeasurableSet G ∧
      1 - (∑' t, (b t + ENNReal.ofReal
        (FailureMeasurability.combinedFailureBound a N0 (start + t)))) ≤
          rademacherProductMeasure G ∧
      ∀ ε ∈ G,
        (∀ t, (FlatAliveGood.flatAlive a hN0 start t ε).Nonempty) ∧
        (∀ t,
          ε ∉ FailureMeasurability.combinedGridFailure a N0 (start + t)) := by
  apply exists_measurable_flatAlive_noFailureSet a hN0 start
    (fun t => FailureMeasurability.combinedGridFailure a N0 (start + t))
    b
    (fun t => ENNReal.ofReal
      (FailureMeasurability.combinedFailureBound a N0 (start + t)))
    hinitial htransitionMeas
  · intro t
    exact FailureMeasurability.measurableSet_combinedGridFailure
      a N0 (start + t)
  · exact htransitionBound
  · intro t
    simpa only [FailureMeasurability.combinedFailureBound] using
      FailureMeasurability.measure_combinedGridFailure_le_ofReal
        a hsmall hN0 (start + t) (henv t) (hlog t)

end

end Erdos527.FinalProbabilityAssembly

open scoped BigOperators Topology
open Filter Set

namespace Erdos527

section ConcretePathwise

lemma eight_le_prefixPhaseGridSize {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) :
    8 ≤ prefixPhaseGridSize N0 k := by
  have hs2 : 2 ≤ scale N0 (k + 1) := by
    have htwo : 2 ≤ 2 ^ (k + 1) := by
      simpa only [pow_one] using Nat.pow_le_pow_right
        (by norm_num : 0 < (2 : ℕ)) (by omega : 1 ≤ k + 1)
    exact htwo.trans (two_pow_le_scale hN0 (k + 1))
  unfold prefixPhaseGridSize
  calc
    8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ 16 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    _ ≤ scale N0 (k + 1) ^ 16 := Nat.pow_le_pow_left hs2 16

lemma norm_eq_one_of_mem_flatAlive
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (start t : ℕ)
    (ε : ℕ → ℝ) {z : ℂ}
    (hz : z ∈ FlatAliveGood.flatAlive a hN0 start t ε) :
    ‖z‖ = 1 := by
  have hzgrid := FlatAliveGood.flatAlive_subset_grid a hN0 start t ε hz
  letI : NeZero (scale N0 (start + t)) := ⟨scale_ne_zero hN0.ne' (start + t)⟩
  simp only [RecursiveAlive.rootGrid, Grid.complexRootGrid,
    Finset.mem_image, Finset.mem_univ, true_and] at hzgrid
  obtain ⟨j, rfl⟩ := hzgrid
  exact Grid.norm_complexGridPoint _ _

lemma flatGood_of_mem_flatAlive_succ
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (start t : ℕ)
    (ε : ℕ → ℝ) {z : ℂ}
    (hz : z ∈ FlatAliveGood.flatAlive a hN0 start (t + 1) ε) :
    FlatAliveGood.flatGood a hN0 (start + t) z
      (FlatVectorAPI.scaleRestriction ε N0 (start + t)) := by
  rw [FlatAliveGood.flatAlive_succ] at hz
  have hz' :
      z ∈ RecursiveAlive.scaleChildren N0 hN0 (start + t)
          (FlatAliveGood.flatAlive a hN0 start t ε) ∧
        FlatAliveGood.flatGood a hN0 (start + t) z
          (FlatVectorAPI.scaleRestriction ε N0 (start + t)) := by
    simpa [FlatAliveGood.flatGoodTransition, RecursiveAlive.filterGood] using hz
  exact hz'.2

/-- Raw complement of the derivative grid failure implies the uniform
whole-circle derivative estimate, with no almost-sure wrapper. -/
lemma derivativeScalePrefix_uniform_bound_of_not_failure
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} [NeZero N0] (hN0 : 0 < N0) (k : ℕ)
    (henv : coefficientEnvelope a N0 k ≤ 1)
    (hε : ∀ n, |ε n| ≤ 1)
    (hnot : ε ∉ DerivativeEvents.derivativeGridFailure a N0 k) :
    ∀ l : ℕ, scale N0 k ≤ l → l ≤ scale N0 (k + 1) →
      ∀ z : ℂ, ‖z‖ = 1 →
        ‖DerivativeEvents.signedDerivativePolynomial a ε
            (DerivativeEvents.scalePrefix N0 k l) z‖ <
          DerivativeEvents.derivativeThreshold N0 k := by
  intro l hlower hl z hz
  rw [← DerivativeEvents.signedPolynomial_derivativeCoefficient]
  apply norm_signedPolynomial_lt_of_not_gridPolynomialFailure
    (DerivativeEvents.derivativeCoefficient a) ε
    (DerivativeEvents.scalePrefix N0 k l) (prefixPhaseGridSize N0 k)
    (eight_le_prefixPhaseGridSize hN0 k)
    (DerivativeEvents.derivative_phase_mesh_error_le
      a hsmall hN0 k l henv hl) (fun n _ ↦ hε n)
  · intro hfail
    apply hnot
    unfold DerivativeEvents.derivativeGridFailure
    simp only [Set.mem_iUnion]
    exact ⟨⟨l, by omega⟩, hfail⟩
  · exact hz

lemma branchRootRadius_nonneg_local (q k : ℕ) :
    0 ≤ Grid.branchRootRadius q k := by
  unfold Grid.branchRootRadius
  positivity

lemma shifted_flatAlive_thickenings_nested
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (start : ℕ)
    (ε : ℕ → ℝ) :
    ∀ t,
      thickenedFinitePhaseSet
          (fun s ↦ FlatAliveGood.flatAlive a hN0 start (s + 1) ε)
          (fun s ↦ Grid.branchRootRadius
            (scale N0 (start + s + 1)) (start + s + 1)) (t + 1) ⊆
        thickenedFinitePhaseSet
          (fun s ↦ FlatAliveGood.flatAlive a hN0 start (s + 1) ε)
          (fun s ↦ Grid.branchRootRadius
            (scale N0 (start + s + 1)) (start + s + 1)) t := by
  intro t z hz
  rcases hz with ⟨hzunit, w, hw, hzw⟩
  obtain ⟨p, hp, _hsep, hball⟩ :=
    FlatAliveGood.exists_flatAlive_parent_with_nesting_of_mem
      a hN0 start (t + 1) ε (by simpa [Nat.add_assoc] using hw)
  refine ⟨hzunit, p, by simpa [Nat.add_assoc] using hp, ?_⟩
  apply hball
  simpa [Metric.mem_closedBall, Nat.add_assoc] using hzw

lemma shifted_flatAlive_thickenings_nonempty
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (start : ℕ)
    (ε : ℕ → ℝ)
    (halive : ∀ t, (FlatAliveGood.flatAlive a hN0 start t ε).Nonempty) :
    ∀ t,
      (thickenedFinitePhaseSet
        (fun s ↦ FlatAliveGood.flatAlive a hN0 start (s + 1) ε)
        (fun s ↦ Grid.branchRootRadius
          (scale N0 (start + s + 1)) (start + s + 1)) t).Nonempty := by
  intro t
  obtain ⟨w, hw⟩ := halive (t + 1)
  refine ⟨w, norm_eq_one_of_mem_flatAlive a hN0 start (t + 1) ε hw,
    w, hw, ?_⟩
  simpa using branchRootRadius_nonneg_local
    (scale N0 (start + t + 1)) (start + t + 1)

lemma wholeScale_bound_of_shifted_flatAlive_thickening
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} [NeZero N0] (hN0 : 0 < N0) (start : ℕ)
    (ε : ℕ → ℝ)
    (henv : ∀ k, start ≤ k → coefficientEnvelope a N0 k ≤ 1)
    (hderNot : ∀ k, start ≤ k →
      ε ∉ DerivativeEvents.derivativeGridFailure a N0 k)
    (hmargin : ∀ k, start ≤ k →
      DerivativeEvents.transportError N0 k ≤
        1 / (2 * (((k + 1 : ℕ) : ℝ) ^ 2)))
    (hε : ∀ n, |ε n| ≤ 1) (t : ℕ) {z : ℂ}
    (hz : z ∈ thickenedFinitePhaseSet
      (fun s ↦ FlatAliveGood.flatAlive a hN0 start (s + 1) ε)
      (fun s ↦ Grid.branchRootRadius
        (scale N0 (start + s + 1)) (start + s + 1)) t) :
    ‖∑ n ∈ Finset.Ico (scale N0 (start + t))
        (scale N0 (start + t + 1)), seriesTerm a ε z n‖ ≤
      1 / (((start + t + 1 : ℕ) : ℝ) ^ 2) := by
  rcases hz with ⟨hzunit, w, hw, hzw⟩
  have hwunit := norm_eq_one_of_mem_flatAlive a hN0 start (t + 1) ε hw
  have hwgood := flatGood_of_mem_flatAlive_succ a hN0 start t ε hw
  have hroot := FlatAliveGood.endpoint_norm_lt_of_flatGood
    a hN0 (start + t) w (FlatVectorAPI.scaleRestriction ε N0 (start + t)) hwgood
  rw [GaussianCutoffBridge.flatBlockIncrementDirection_eq_flatDirection,
    FlatVectorAPI.sum_linearCombination_flatDirection_scaleRestriction] at hroot
  have hder : ∀ u : ℂ, ‖u‖ = 1 →
      ‖DerivativeEvents.signedDerivativePolynomial a ε
        (Finset.Ico (scale N0 (start + t))
          (scale N0 (start + t + 1))) u‖ ≤
        DerivativeEvents.derivativeThreshold N0 (start + t) := by
    intro u hu
    exact (derivativeScalePrefix_uniform_bound_of_not_failure
      a hsmall hN0 (start + t) (henv _ (by omega)) hε
      (hderNot _ (by omega)) (scale N0 (start + t + 1))
      (scale_le_scale_succ N0 (start + t)) (by rfl) u hu).le
  have htransport := DerivativeEvents.norm_signedPolynomial_sub_le_pi_div_two
    a ε (Finset.Ico (scale N0 (start + t))
      (scale N0 (start + t + 1)))
    (DerivativeEvents.derivativeThreshold N0 (start + t))
    hzunit hwunit hder
  have hdist : ‖z - w‖ ≤ Grid.branchRootRadius
      (scale N0 (start + t + 1)) (start + t + 1) := by
    simpa only [dist_eq_norm] using hzw
  have htransportError :
      ‖signedPolynomial a ε
          (Finset.Ico (scale N0 (start + t))
            (scale N0 (start + t + 1))) z -
        signedPolynomial a ε
          (Finset.Ico (scale N0 (start + t))
            (scale N0 (start + t + 1))) w‖ ≤
        DerivativeEvents.transportError N0 (start + t) := by
    calc
      _ ≤ (Real.pi / 2) *
          DerivativeEvents.derivativeThreshold N0 (start + t) * ‖z - w‖ :=
        htransport
      _ ≤ (Real.pi / 2) *
          DerivativeEvents.derivativeThreshold N0 (start + t) *
            Grid.branchRootRadius (scale N0 (start + t + 1))
              (start + t + 1) := by
        exact mul_le_mul_of_nonneg_left hdist
          (mul_nonneg (div_nonneg Real.pi_pos.le (by norm_num))
            (DerivativeEvents.derivativeThreshold_pos hN0 (start + t)).le)
      _ = DerivativeEvents.transportError N0 (start + t) := rfl
  change ‖signedPolynomial a ε
    (Finset.Ico (scale N0 (start + t))
      (scale N0 (start + t + 1))) z‖ ≤ _
  calc
    _ ≤ ‖signedPolynomial a ε
          (Finset.Ico (scale N0 (start + t))
            (scale N0 (start + t + 1))) z -
        signedPolynomial a ε
          (Finset.Ico (scale N0 (start + t))
            (scale N0 (start + t + 1))) w‖ +
        ‖signedPolynomial a ε
          (Finset.Ico (scale N0 (start + t))
            (scale N0 (start + t + 1))) w‖ := by
      simpa only [sub_add_cancel] using norm_add_le
        (signedPolynomial a ε
          (Finset.Ico (scale N0 (start + t))
            (scale N0 (start + t + 1))) z -
          signedPolynomial a ε
            (Finset.Ico (scale N0 (start + t))
              (scale N0 (start + t + 1))) w)
        (signedPolynomial a ε
          (Finset.Ico (scale N0 (start + t))
            (scale N0 (start + t + 1))) w)
    _ ≤ 1 / (2 * (((start + t + 1 : ℕ) : ℝ) ^ 2)) +
        1 / (2 * (((start + t + 1 : ℕ) : ℝ) ^ 2)) :=
      add_le_add (htransportError.trans (hmargin _ (by omega))) hroot.le
    _ = 1 / (((start + t + 1 : ℕ) : ℝ) ^ 2) := by ring

lemma flatPrefix_bound_of_shifted_flatAlive_thickening
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} [NeZero N0] (hN0 : 0 < N0) (start : ℕ)
    (ε : ℕ → ℝ)
    (henv : ∀ k, start ≤ k → coefficientEnvelope a N0 k ≤ 1)
    (hderNot : ∀ k, start ≤ k →
      ε ∉ DerivativeEvents.derivativeGridFailure a N0 k)
    (hmargin : ∀ k, start ≤ k →
      DerivativeEvents.transportError N0 k ≤
        Real.sqrt (coefficientEnvelope a N0 k) / 2)
    (hε : ∀ n, |ε n| ≤ 1) (t : ℕ) {z : ℂ}
    (hz : z ∈ thickenedFinitePhaseSet
      (fun s ↦ FlatAliveGood.flatAlive a hN0 start (s + 1) ε)
      (fun s ↦ Grid.branchRootRadius
        (scale N0 (start + s + 1)) (start + s + 1)) t) :
    ∀ r ≤ uniformBlockCount (start + t),
      ‖∑ n ∈ Finset.Ico (scale N0 (start + t))
          (uniformEndpoint N0 (start + t) r), seriesTerm a ε z n‖ ≤
        Real.sqrt (coefficientEnvelope a N0 (start + t)) := by
  rcases hz with ⟨hzunit, w, hw, hzw⟩
  have hwunit := norm_eq_one_of_mem_flatAlive a hN0 start (t + 1) ε hw
  have hwgood := flatGood_of_mem_flatAlive_succ a hN0 start t ε hw
  intro r hrle
  cases r with
  | zero =>
      simp [uniformEndpoint_zero, Real.sqrt_nonneg]
  | succ r =>
      have hr : r < uniformBlockCount (start + t) := by omega
      let j : Fin (uniformBlockCount (start + t)) := ⟨r, hr⟩
      have hroot := FlatAliveGood.prefix_norm_lt_of_flatGood
        a hN0 (start + t) w
          (FlatVectorAPI.scaleRestriction ε N0 (start + t)) hwgood j
      rw [GaussianCutoffBridge.flatBlockIncrementDirection_eq_flatDirection,
        FlatVectorAPI.sum_Iic_linearCombination_flatDirection_scaleRestriction] at hroot
      have hend : uniformEndpoint N0 (start + t) (r + 1) ≤
          scale N0 (start + t + 1) := by
        calc
          uniformEndpoint N0 (start + t) (r + 1) ≤
              uniformEndpoint N0 (start + t)
                (uniformBlockCount (start + t)) := by
            unfold uniformEndpoint
            exact Nat.add_le_add_left
              (Nat.mul_le_mul_right (uniformBlockLength N0 (start + t)) hrle)
              (scale N0 (start + t))
          _ = scale N0 (start + t + 1) :=
            uniformEndpoint_last N0 (start + t)
      have hder : ∀ u : ℂ, ‖u‖ = 1 →
          ‖DerivativeEvents.signedDerivativePolynomial a ε
            (Finset.Ico (scale N0 (start + t))
              (uniformEndpoint N0 (start + t) (r + 1))) u‖ ≤
            DerivativeEvents.derivativeThreshold N0 (start + t) := by
        intro u hu
        exact (derivativeScalePrefix_uniform_bound_of_not_failure
          a hsmall hN0 (start + t) (henv _ (by omega)) hε
          (hderNot _ (by omega)) (uniformEndpoint N0 (start + t) (r + 1))
          (uniformBlock_start_ge_scale N0 (start + t) (r + 1))
          hend u hu).le
      have htransport := DerivativeEvents.norm_signedPolynomial_sub_le_pi_div_two
        a ε (Finset.Ico (scale N0 (start + t))
          (uniformEndpoint N0 (start + t) (r + 1)))
        (DerivativeEvents.derivativeThreshold N0 (start + t))
        hzunit hwunit hder
      have hdist : ‖z - w‖ ≤ Grid.branchRootRadius
          (scale N0 (start + t + 1)) (start + t + 1) := by
        simpa only [dist_eq_norm] using hzw
      have htransportError :
          ‖signedPolynomial a ε
              (Finset.Ico (scale N0 (start + t))
                (uniformEndpoint N0 (start + t) (r + 1))) z -
            signedPolynomial a ε
              (Finset.Ico (scale N0 (start + t))
                (uniformEndpoint N0 (start + t) (r + 1))) w‖ ≤
            DerivativeEvents.transportError N0 (start + t) := by
        calc
          _ ≤ (Real.pi / 2) *
              DerivativeEvents.derivativeThreshold N0 (start + t) *
                ‖z - w‖ := htransport
          _ ≤ (Real.pi / 2) *
              DerivativeEvents.derivativeThreshold N0 (start + t) *
                Grid.branchRootRadius (scale N0 (start + t + 1))
                  (start + t + 1) := by
            exact mul_le_mul_of_nonneg_left hdist
              (mul_nonneg (div_nonneg Real.pi_pos.le (by norm_num))
                (DerivativeEvents.derivativeThreshold_pos hN0 (start + t)).le)
          _ = DerivativeEvents.transportError N0 (start + t) := rfl
      change ‖signedPolynomial a ε
        (Finset.Ico (scale N0 (start + t))
          (uniformEndpoint N0 (start + t) (r + 1))) z‖ ≤ _
      calc
        _ ≤ ‖signedPolynomial a ε
              (Finset.Ico (scale N0 (start + t))
                (uniformEndpoint N0 (start + t) (r + 1))) z -
            signedPolynomial a ε
              (Finset.Ico (scale N0 (start + t))
                (uniformEndpoint N0 (start + t) (r + 1))) w‖ +
            ‖signedPolynomial a ε
              (Finset.Ico (scale N0 (start + t))
                (uniformEndpoint N0 (start + t) (r + 1))) w‖ := by
          simpa only [sub_add_cancel] using norm_add_le
            (signedPolynomial a ε
              (Finset.Ico (scale N0 (start + t))
                (uniformEndpoint N0 (start + t) (r + 1))) z -
              signedPolynomial a ε
                (Finset.Ico (scale N0 (start + t))
                  (uniformEndpoint N0 (start + t) (r + 1))) w)
            (signedPolynomial a ε
              (Finset.Ico (scale N0 (start + t))
                (uniformEndpoint N0 (start + t) (r + 1))) w)
        _ ≤ Real.sqrt (coefficientEnvelope a N0 (start + t)) / 2 +
            Real.sqrt (coefficientEnvelope a N0 (start + t)) / 2 :=
          add_le_add (htransportError.trans (hmargin _ (by omega)))
            (by simpa [j] using hroot.le)
        _ = Real.sqrt (coefficientEnvelope a N0 (start + t)) := by ring

lemma intraBlock_bound_of_raw_prefix_complement
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} [NeZero N0] (hN0 : 0 < N0) (start : ℕ)
    (ε : ℕ → ℝ)
    (henv : ∀ k, start ≤ k → coefficientEnvelope a N0 k ≤ 1)
    (hprefixNot : ∀ k, start ≤ k →
      ε ∉ flatPrefixGridFailure a N0 k (prefixPhaseGridSize N0 k)
        (prefixTolerance N0 k / 2))
    (hε : ∀ n, |ε n| ≤ 1) :
    ∀ t z, ‖z‖ = 1 →
      ∀ r < uniformBlockCount (start + t),
        ∀ l < uniformBlockLength N0 (start + t),
          ‖∑ n ∈ uniformPrefix N0 (start + t) r l,
              seriesTerm a ε z n‖ ≤ prefixTolerance N0 (start + t) := by
  intro t z hz r hr l hl
  let rf : Fin (uniformBlockCount (start + t)) := ⟨r, hr⟩
  let lf : Fin (uniformBlockLength N0 (start + t)) := ⟨l, hl⟩
  letI : NeZero (prefixPhaseGridSize N0 (start + t)) :=
    ⟨(prefixPhaseGridSize_pos hN0 (start + t)).ne'⟩
  have hbound := flatPrefix_uniform_bound_of_not_failure a ε
    (q := prefixPhaseGridSize N0 (start + t))
    (eight_le_prefixPhaseGridSize hN0 (start + t))
    (fun r l ↦ prefix_phase_mesh_error_le a hsmall hN0 (start + t)
      (henv _ (by omega)) r l) hε (hprefixNot _ (by omega)) rf lf z hz
  change ‖signedPolynomial a ε (uniformPrefix N0 (start + t) rf lf) z‖ ≤ _
  exact hbound.le

/-- A fully pathwise bridge from the recursively surviving flat phases and
the two raw prefix-event complements to the convergence event. -/
theorem convergenceEvent_of_flatAlive_pathwise
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} [NeZero N0] (hN0 : 0 < N0) (start : ℕ)
    (ε : ℕ → ℝ)
    (halive : ∀ t, (FlatAliveGood.flatAlive a hN0 start t ε).Nonempty)
    (henv : ∀ k, start ≤ k → coefficientEnvelope a N0 k ≤ 1)
    (hprefixNot : ∀ k, start ≤ k →
      ε ∉ flatPrefixGridFailure a N0 k (prefixPhaseGridSize N0 k)
        (prefixTolerance N0 k / 2))
    (hderNot : ∀ k, start ≤ k →
      ε ∉ DerivativeEvents.derivativeGridFailure a N0 k)
    (hendpointMargin : ∀ k, start ≤ k →
      DerivativeEvents.transportError N0 k ≤
        1 / (2 * (((k + 1 : ℕ) : ℝ) ^ 2)))
    (hprefixMargin : ∀ k, start ≤ k →
      DerivativeEvents.transportError N0 k ≤
        Real.sqrt (coefficientEnvelope a N0 k) / 2)
    (hεsign : ∀ n, ε n = 1 ∨ ε n = -1) :
    ε ∈ convergenceEvent a := by
  have hε : ∀ n, |ε n| ≤ 1 := by
    intro n
    rcases hεsign n with h | h <;> simp [h]
  have hδ0 : Tendsto
      (fun t ↦ coefficientEnvelope a N0 (start + t)) atTop (nhds 0) := by
    simpa [Nat.add_comm] using
      (Filter.tendsto_add_atTop_iff_nat
        (f := coefficientEnvelope a N0) start).mpr
          (coefficientEnvelope_tendsto_zero a hsmall hN0)
  have htol0 : Tendsto
      (fun t ↦ prefixTolerance N0 (start + t)) atTop (nhds 0) := by
    simpa [Nat.add_comm] using
      (Filter.tendsto_add_atTop_iff_nat
        (f := prefixTolerance N0) start).mpr
          (prefixTolerance_tendsto_zero hN0)
  have hconv := exists_unit_summable_conditional_of_reset_nested_alive_flat
    (f := fun z n ↦ seriesTerm a ε z n)
    (phase := fun t ↦ FlatAliveGood.flatAlive a hN0 start (t + 1) ε)
    (radius := fun t ↦ Grid.branchRootRadius
      (scale N0 (start + t + 1)) (start + t + 1))
    (δ := coefficientEnvelope a N0)
    (tol := prefixTolerance N0) hN0 start
    (shifted_flatAlive_thickenings_nested a hN0 start ε)
    (shifted_flatAlive_thickenings_nonempty a hN0 start ε halive)
    hδ0 htol0 (fun k ↦ Real.sqrt_nonneg _)
    (fun t z hz ↦ wholeScale_bound_of_shifted_flatAlive_thickening
      a hsmall hN0 start ε henv hderNot hendpointMargin hε t hz)
    (fun t z hz ↦ flatPrefix_bound_of_shifted_flatAlive_thickening
      a hsmall hN0 start ε henv hderNot hprefixMargin hε t hz)
    (intraBlock_bound_of_raw_prefix_complement
      a hsmall hN0 start ε henv hprefixNot hε)
  simpa [convergenceEvent, SeriesConvergesAt] using hconv

end ConcretePathwise

end Erdos527

open scoped BigOperators ENNReal NNReal ProbabilityTheory Topology
open Filter MeasureTheory ProbabilityTheory

namespace Erdos527.PairApplication

open OnePointLindeberg CorrelationCount PairFactorization
open OnePointLindebergAsymptotic
open BranchParameterArithmetic
open PairApplication

lemma lindeberg_exponent_le_cube {k : ℕ} (hk : 100 ≤ k) :
    k + (16 * k + 9 * stepExponent k + 16) + 50 * k ^ 2 ≤ k ^ 3 := by
  simp only [stepExponent]
  nlinarith

lemma flatOnePointLindebergError_concrete_le_correlation_quarter
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) {k : ℕ} (hk : 100 ≤ k)
    (henv : coefficientEnvelope a N0 k ≤ 1)
    (hC : SmoothCutoffC4.cutoffC4 ^ 4 ≤ ((2 ^ k : ℕ) : ℝ)) :
    flatOnePointLindebergError a N0 k
        (concreteEndpointScale k) (concretePrefixScale a N0 k) ≤
      correlationThreshold k ^ (1 / 4 : ℝ) := by
  apply (flatOnePointLindebergError_concrete_le a hsmall hN0 (by omega) henv).trans
  rw [correlationThreshold_rpow_quarter_eq]
  have hscale : ((2 ^ (k ^ 3) : ℕ) : ℝ) ≤ (scale N0 k : ℝ) := by
    exact_mod_cast pow_cube_le_scale hN0 k
  have hscalePos : (0 : ℝ) < scale N0 k := by exact_mod_cast scale_pos hN0 k
  apply (div_le_iff₀ hscalePos).2
  calc
    SmoothCutoffC4.cutoffC4 ^ 4 *
          ((2 ^ (16 * k + 9 * stepExponent k + 16) : ℕ) : ℝ) ≤
        ((2 ^ k : ℕ) : ℝ) *
          ((2 ^ (16 * k + 9 * stepExponent k + 16) : ℕ) : ℝ) := by
      gcongr
    _ = (2 : ℝ) ^ ((k + (16 * k + 9 * stepExponent k + 16) : ℕ) : ℝ) := by
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]
      rw [← pow_add, Real.rpow_natCast]
    _ ≤ (2 : ℝ) ^ (((k ^ 3 : ℕ) : ℝ) - (((50 * k ^ 2 : ℕ) : ℝ))) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hcast :
          ((k + (16 * k + 9 * stepExponent k + 16) + 50 * k ^ 2 : ℕ) : ℝ) ≤
            ((k ^ 3 : ℕ) : ℝ) := by
        exact_mod_cast lindeberg_exponent_le_cube hk
      push_cast at hcast ⊢
      linarith
    _ = (2 : ℝ) ^ (-(50 : ℝ) * (k : ℝ) ^ 2) *
          ((2 ^ (k ^ 3) : ℕ) : ℝ) := by
      rw [show ((2 ^ (k ^ 3) : ℕ) : ℝ) =
          (2 : ℝ) ^ (((k ^ 3 : ℕ) : ℝ)) by
        rw [Real.rpow_natCast]
        norm_num]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 2
      norm_num only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
      push_cast
      ring
    _ ≤ (2 : ℝ) ^ (-(50 : ℝ) * (k : ℝ) ^ 2) *
          (scale N0 k : ℝ) := by
      gcongr

lemma uniformBlockCount_mul_flatPairBudget_le_stepFactor_pow_eight
    (k : ℕ) (endpointScale prefixScale : ℝ)
    (hscale : |endpointScale| + |prefixScale| ≤
      ((2 ^ stepExponent k : ℕ) : ℝ))
    (hC4 : 4 * SmoothCutoffC4.cutoffC4 ≤
      ((2 ^ stepExponent k : ℕ) : ℝ)) :
    (uniformBlockCount k : ℝ) *
        flatPairCutoffOperatorBudget k endpointScale prefixScale ≤
      ((2 ^ stepExponent k : ℕ) : ℝ) ^ 8 := by
  let F : ℝ := ((2 ^ stepExponent k : ℕ) : ℝ)
  let L : ℝ := (uniformBlockCount k : ℝ)
  have hF1 : 1 ≤ F := by
    dsimp only [F]
    exact_mod_cast one_le_stepFactor k
  have hF0 : 0 ≤ F := le_trans (by norm_num) hF1
  have hL0 : 0 ≤ L := by positivity
  have hL : L ≤ F ^ 2 := by
    dsimp only [L, F]
    exact_mod_cast uniformBlockCount_le_stepFactor_sq k
  have hL1 : (((uniformBlockCount k + 1 : ℕ) : ℝ)) ≤ 2 * F ^ 2 := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith [sq_nonneg F]
  have hhead :
      2 * SmoothCutoffC4.cutoffC4 *
          (((uniformBlockCount k + 1 : ℕ) : ℝ)) ≤ F ^ 3 := by
    calc
      _ ≤ 2 * SmoothCutoffC4.cutoffC4 * (2 * F ^ 2) := by
        exact mul_le_mul_of_nonneg_left hL1
          (mul_nonneg (by norm_num) SmoothCutoffC4.cutoffC4_nonneg)
      _ = (4 * SmoothCutoffC4.cutoffC4) * F ^ 2 := by ring
      _ ≤ F * F ^ 2 := by
        exact mul_le_mul_of_nonneg_right hC4 (sq_nonneg F)
      _ = F ^ 3 := by ring
  calc
    L * flatPairCutoffOperatorBudget k endpointScale prefixScale =
        L * (2 * SmoothCutoffC4.cutoffC4 *
          (((uniformBlockCount k + 1 : ℕ) : ℝ))) *
          (|endpointScale| + |prefixScale|) * L := by
      dsimp only [L]
      unfold flatPairCutoffOperatorBudget flatCutoffOperatorBudget
      ring
    _ ≤ F ^ 2 * F ^ 3 * F * F ^ 2 := by
      gcongr
      exact mul_nonneg
        (mul_nonneg (by norm_num) SmoothCutoffC4.cutoffC4_nonneg)
        (by positivity)
    _ = F ^ 8 := by ring

lemma concreteScaleSum_le_stepFactor
    (a : ℕ → ℝ) {N0 k : ℕ} (hk : 1 ≤ k)
    (henv : coefficientEnvelope a N0 k ≤ 1) :
    |concreteEndpointScale k| + |concretePrefixScale a N0 k| ≤
      ((2 ^ stepExponent k : ℕ) : ℝ) := by
  apply (concreteScaleSum_le_two_pow hk henv).trans
  have hexp : 2 * k + 3 ≤ stepExponent k := by
    unfold stepExponent
    nlinarith
  exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hexp

lemma cutoffC4_four_le_stepFactor
    {k : ℕ} (hk : 1 ≤ k)
    (hC : SmoothCutoffC4.cutoffC4 ^ 4 ≤ ((2 ^ k : ℕ) : ℝ)) :
    4 * SmoothCutoffC4.cutoffC4 ≤ ((2 ^ stepExponent k : ℕ) : ℝ) := by
  have hc1 : SmoothCutoffC4.cutoffC4 ≤ SmoothCutoffC4.cutoffC4 ^ 4 := by
    have hcLower : 1 ≤ SmoothCutoffC4.cutoffC4 :=
      SmoothCutoffC4.one_le_cutoffC4
    have hc0 := SmoothCutoffC4.cutoffC4_nonneg
    calc
      SmoothCutoffC4.cutoffC4 ≤ SmoothCutoffC4.cutoffC4 ^ 2 := by nlinarith
      _ ≤ SmoothCutoffC4.cutoffC4 ^ 4 := by nlinarith [sq_nonneg (SmoothCutoffC4.cutoffC4 ^ 2 - 1)]
  calc
    4 * SmoothCutoffC4.cutoffC4 ≤ 4 * ((2 ^ k : ℕ) : ℝ) := by
      nlinarith
    _ ≤ ((2 ^ stepExponent k : ℕ) : ℝ) := by
      have hexp : k + 2 ≤ stepExponent k := by
        simp only [stepExponent]
        nlinarith
      exact_mod_cast (show 4 * 2 ^ k ≤ 2 ^ stepExponent k by
        rw [show 4 * 2 ^ k = 2 ^ (k + 2) by rw [pow_add]; norm_num; ring]
        exact Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hexp)

theorem flat_pair_factorization_single_budget
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) {k : ℕ} (hk : 100 ≤ k)
    (x y : UnitAddCircle)
    (henv : coefficientEnvelope a N0 k ≤ 1)
    (hC : SmoothCutoffC4.cutoffC4 ^ 4 ≤ ((2 ^ k : ℕ) : ℝ))
    (huncorrelated : ∀ j : Fin (uniformBlockCount k),
      ¬ IsCorrelated (fun n ↦ (a n : ℂ))
        (uniformEndpoint N0 k j - 1) (uniformBlockLength N0 k) x y
        (correlationThreshold k)) :
    |pairRademacherExpectation (concreteEndpointScale k)
          (concretePrefixScale a N0 k)
          (flatPairDirection a hN0 k (phasePoint x) (phasePoint y)) -
      phaseRademacherExpectation (concreteEndpointScale k)
            (concretePrefixScale a N0 k)
            (flatBlockIncrementDirection a hN0 k (phasePoint x)) *
          phaseRademacherExpectation (concreteEndpointScale k)
            (concretePrefixScale a N0 k)
            (flatBlockIncrementDirection a hN0 k (phasePoint y))| ≤
      12 * (((2 ^ stepExponent k : ℕ) : ℝ) ^ 10) *
        correlationThreshold k ^ (1 / 4 : ℝ) := by
  have hscale := concreteScaleSum_le_stepFactor a (by omega) henv
  have hC4 := cutoffC4_four_le_stepFactor (by omega) hC
  have hraw := flat_pair_factorization_of_not_correlated
    a hsmall hN0 k x y (concreteEndpointScale k) (concretePrefixScale a N0 k)
      (correlationThreshold k) henv (correlationThreshold_nonneg k)
      (correlationThreshold_le_one k) huncorrelated
  have hK := pairCutoffLipschitzNN_le_flatPairCutoffOperatorBudget
    k (concreteEndpointScale k) (concretePrefixScale a N0 k)
  have hraw' := hraw.trans (show
      18 * flatOnePointLindebergError a N0 k
            (concreteEndpointScale k) (concretePrefixScale a N0 k) +
          12 * (uniformBlockCount k : ℝ) *
            (PairCanonicalHybrid.pairCutoffLipschitzNN
              (uniformBlockCount k) (concreteEndpointScale k)
                (concretePrefixScale a N0 k) : ℝ) *
              correlationThreshold k ^ (1 / 4 : ℝ) ≤
        18 * flatOnePointLindebergError a N0 k
            (concreteEndpointScale k) (concretePrefixScale a N0 k) +
          12 * (uniformBlockCount k : ℝ) *
            flatPairCutoffOperatorBudget k (concreteEndpointScale k)
              (concretePrefixScale a N0 k) *
              correlationThreshold k ^ (1 / 4 : ℝ) by
    gcongr
    exact Real.rpow_nonneg (correlationThreshold_nonneg k) _)
  have hpoly8 := uniformBlockCount_mul_flatPairBudget_le_stepFactor_pow_eight
    k (concreteEndpointScale k) (concretePrefixScale a N0 k) hscale hC4
  have hE := flatOnePointLindebergError_concrete_le_correlation_quarter
    a hsmall hN0 hk henv hC
  let F : ℝ := ((2 ^ stepExponent k : ℕ) : ℝ)
  let R : ℝ := correlationThreshold k ^ (1 / 4 : ℝ)
  have hF2 : 2 ≤ F := by dsimp only [F]; exact_mod_cast two_le_stepFactor k
  have hR0 : 0 ≤ R := by
    dsimp only [R]
    exact Real.rpow_nonneg (correlationThreshold_nonneg k) _
  have hF8 : 12 * F ^ 8 * R ≤ 3 * F ^ 10 * R := by
    have hF0 : 0 ≤ F := le_trans (by norm_num) hF2
    have hF2sq : 4 ≤ F ^ 2 := by nlinarith
    have hpow8 : 0 ≤ F ^ 8 := pow_nonneg hF0 _
    have hcore : 4 * F ^ 8 ≤ F ^ 10 := by
      calc
        4 * F ^ 8 ≤ F ^ 2 * F ^ 8 :=
          mul_le_mul_of_nonneg_right hF2sq hpow8
        _ = F ^ 10 := by ring
    nlinarith
  have hE' : 18 * flatOnePointLindebergError a N0 k
        (concreteEndpointScale k) (concretePrefixScale a N0 k) ≤
      9 * F ^ 10 * R := by
    have hF10 : 2 ≤ F ^ 10 := by
      calc 2 ≤ 2 ^ 10 := by norm_num
           _ ≤ F ^ 10 := pow_le_pow_left₀ (by norm_num) hF2 10
    dsimp only [R]
    nlinarith
  have hG : 12 * (uniformBlockCount k : ℝ) *
        flatPairCutoffOperatorBudget k (concreteEndpointScale k)
          (concretePrefixScale a N0 k) *
          correlationThreshold k ^ (1 / 4 : ℝ) ≤
      3 * ((2 ^ stepExponent k : ℕ) : ℝ) ^ 10 *
          correlationThreshold k ^ (1 / 4 : ℝ) := by
    calc
      _ = 12 * ((uniformBlockCount k : ℝ) *
          flatPairCutoffOperatorBudget k (concreteEndpointScale k)
            (concretePrefixScale a N0 k)) *
          correlationThreshold k ^ (1 / 4 : ℝ) := by ring
      _ ≤ 12 * ((2 ^ stepExponent k : ℕ) : ℝ) ^ 8 *
          correlationThreshold k ^ (1 / 4 : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpoly8 (by norm_num))
          (Real.rpow_nonneg (correlationThreshold_nonneg k) _)
      _ ≤ _ := by simpa only [F, R] using hF8
  exact hraw'.trans (by
    dsimp only [F, R] at hE'
    nlinarith)

theorem flat_pair_expectation_le_product_add_single_budget
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) {k : ℕ} (hk : 100 ≤ k)
    (x y : UnitAddCircle)
    (henv : coefficientEnvelope a N0 k ≤ 1)
    (hC : SmoothCutoffC4.cutoffC4 ^ 4 ≤ ((2 ^ k : ℕ) : ℝ))
    (huncorrelated : ∀ j : Fin (uniformBlockCount k),
      ¬ IsCorrelated (fun n ↦ (a n : ℂ))
        (uniformEndpoint N0 k j - 1) (uniformBlockLength N0 k) x y
        (correlationThreshold k)) :
    pairRademacherExpectation (concreteEndpointScale k)
          (concretePrefixScale a N0 k)
          (flatPairDirection a hN0 k (phasePoint x) (phasePoint y)) ≤
      phaseRademacherExpectation (concreteEndpointScale k)
            (concretePrefixScale a N0 k)
            (flatBlockIncrementDirection a hN0 k (phasePoint x)) *
          phaseRademacherExpectation (concreteEndpointScale k)
            (concretePrefixScale a N0 k)
            (flatBlockIncrementDirection a hN0 k (phasePoint y)) +
        12 * (((2 ^ stepExponent k : ℕ) : ℝ) ^ 10) *
          correlationThreshold k ^ (1 / 4 : ℝ) := by
  have hscale := concreteScaleSum_le_stepFactor a (by omega) henv
  have hC4 := cutoffC4_four_le_stepFactor (by omega) hC
  have hraw := flat_pair_expectation_le_product_add_of_not_correlated
    a hsmall hN0 k x y (concreteEndpointScale k) (concretePrefixScale a N0 k)
      (correlationThreshold k) henv (correlationThreshold_nonneg k)
      (correlationThreshold_le_one k) huncorrelated
  have hpoly8 := uniformBlockCount_mul_flatPairBudget_le_stepFactor_pow_eight
    k (concreteEndpointScale k) (concretePrefixScale a N0 k) hscale hC4
  have hE := flatOnePointLindebergError_concrete_le_correlation_quarter
    a hsmall hN0 hk henv hC
  let F : ℝ := ((2 ^ stepExponent k : ℕ) : ℝ)
  let R : ℝ := correlationThreshold k ^ (1 / 4 : ℝ)
  have hF2 : 2 ≤ F := by dsimp only [F]; exact_mod_cast two_le_stepFactor k
  have hR0 : 0 ≤ R := by
    dsimp only [R]
    exact Real.rpow_nonneg (correlationThreshold_nonneg k) _
  have hF8 : 12 * F ^ 8 * R ≤ 3 * F ^ 10 * R := by
    have hF0 : 0 ≤ F := le_trans (by norm_num) hF2
    have hF2sq : 4 ≤ F ^ 2 := by nlinarith
    have hpow8 : 0 ≤ F ^ 8 := pow_nonneg hF0 _
    have hcore : 4 * F ^ 8 ≤ F ^ 10 := by
      calc
        4 * F ^ 8 ≤ F ^ 2 * F ^ 8 :=
          mul_le_mul_of_nonneg_right hF2sq hpow8
        _ = F ^ 10 := by ring
    nlinarith
  have hE' : 18 * flatOnePointLindebergError a N0 k
        (concreteEndpointScale k) (concretePrefixScale a N0 k) ≤
      9 * F ^ 10 * R := by
    have hF10 : 2 ≤ F ^ 10 := by
      calc 2 ≤ 2 ^ 10 := by norm_num
           _ ≤ F ^ 10 := pow_le_pow_left₀ (by norm_num) hF2 10
    dsimp only [R]
    nlinarith
  apply hraw.trans
  dsimp only [F, R] at hF8 hE' ⊢
  have hG : 12 * (uniformBlockCount k : ℝ) *
        flatPairCutoffOperatorBudget k (concreteEndpointScale k)
          (concretePrefixScale a N0 k) *
          correlationThreshold k ^ (1 / 4 : ℝ) ≤
      3 * ((2 ^ stepExponent k : ℕ) : ℝ) ^ 10 *
          correlationThreshold k ^ (1 / 4 : ℝ) := by
    calc
      _ = 12 * ((uniformBlockCount k : ℝ) *
          flatPairCutoffOperatorBudget k (concreteEndpointScale k)
            (concretePrefixScale a N0 k)) *
          correlationThreshold k ^ (1 / 4 : ℝ) := by ring
      _ ≤ 12 * ((2 ^ stepExponent k : ℕ) : ℝ) ^ 8 *
          correlationThreshold k ^ (1 / 4 : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpoly8 (by norm_num))
          (Real.rpow_nonneg (correlationThreshold_nonneg k) _)
      _ ≤ _ := hF8
  nlinarith

theorem eventually_flat_pair_expectation_le_product_add_single_budget
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) :
    ∀ᶠ k : ℕ in atTop, ∀ x y : UnitAddCircle,
      (∀ j : Fin (uniformBlockCount k),
        ¬ IsCorrelated (fun n ↦ (a n : ℂ))
          (uniformEndpoint N0 k j - 1) (uniformBlockLength N0 k) x y
          (correlationThreshold k)) →
      pairRademacherExpectation (concreteEndpointScale k)
            (concretePrefixScale a N0 k)
            (flatPairDirection a hN0 k (phasePoint x) (phasePoint y)) ≤
        phaseRademacherExpectation (concreteEndpointScale k)
              (concretePrefixScale a N0 k)
              (flatBlockIncrementDirection a hN0 k (phasePoint x)) *
            phaseRademacherExpectation (concreteEndpointScale k)
              (concretePrefixScale a N0 k)
              (flatBlockIncrementDirection a hN0 k (phasePoint y)) +
          12 * (((2 ^ stepExponent k : ℕ) : ℝ) ^ 10) *
            correlationThreshold k ^ (1 / 4 : ℝ) := by
  filter_upwards [OnePointAsymptotic.eventually_coefficientEnvelope_le_one a hsmall hN0,
    eventual_cutoffC4_pow_four_le_two_pow, eventually_ge_atTop 100]
      with k henv hC hk
  intro x y huncorrelated
  exact flat_pair_expectation_le_product_add_single_budget
    a hsmall hN0 hk x y henv hC huncorrelated

theorem eventually_flat_pair_factorization_single_budget
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) :
    ∀ᶠ k : ℕ in atTop, ∀ x y : UnitAddCircle,
      (∀ j : Fin (uniformBlockCount k),
        ¬ IsCorrelated (fun n ↦ (a n : ℂ))
          (uniformEndpoint N0 k j - 1) (uniformBlockLength N0 k) x y
          (correlationThreshold k)) →
      |pairRademacherExpectation (concreteEndpointScale k)
            (concretePrefixScale a N0 k)
            (flatPairDirection a hN0 k (phasePoint x) (phasePoint y)) -
        phaseRademacherExpectation (concreteEndpointScale k)
              (concretePrefixScale a N0 k)
              (flatBlockIncrementDirection a hN0 k (phasePoint x)) *
            phaseRademacherExpectation (concreteEndpointScale k)
              (concretePrefixScale a N0 k)
              (flatBlockIncrementDirection a hN0 k (phasePoint y))| ≤
          12 * (((2 ^ stepExponent k : ℕ) : ℝ) ^ 10) *
            correlationThreshold k ^ (1 / 4 : ℝ) := by
  filter_upwards [OnePointAsymptotic.eventually_coefficientEnvelope_le_one a hsmall hN0,
    eventual_cutoffC4_pow_four_le_two_pow, eventually_ge_atTop 100]
      with k henv hC hk
  intro x y huncorrelated
  exact flat_pair_factorization_single_budget
    a hsmall hN0 hk x y henv hC huncorrelated


end Erdos527.PairApplication

open scoped BigOperators ENNReal NNReal ProbabilityTheory Topology

open MeasureTheory ProbabilityTheory Filter

namespace Erdos527.FixedParentTransition

open BranchParameterArithmetic RecursiveAlive FlatAliveGood FlatTransitionFailure
open FiniteGridBranching PairCorrelationApplication PairApplication
open OnePointApplication OnePointLindeberg PairFactorization CutoffLindebergBridge
open OnePointLindebergAsymptotic SmoothCutoffC4
open CorrelationCount

noncomputable section

lemma complex_phasePoint_eq_root
    (q : ℕ) [NeZero q] {z : ℂ} (hz : z ∈ Grid.complexRootGrid q) :
    PairApplication.phasePoint
        (PairCorrelationApplication.phasePoint q z) = z := by
  calc
    PairApplication.phasePoint
        (PairCorrelationApplication.phasePoint q z) =
        Grid.complexGridPoint q
          (PairCorrelationApplication.rootIndex q z) := by
      rw [Grid.complexGridPoint, ZMod.stdAddChar_apply]
      rfl
    _ = z := PairCorrelationApplication.rootIndex_spec q hz

lemma phaseRademacherExpectation_flat_eq
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) (z : ℂ) :
    PairFactorization.phaseRademacherExpectation
        (FlatAliveGood.flatEndpointScale k) (FlatAliveGood.flatPrefixScale a N0 k)
        (OnePointLindeberg.flatBlockIncrementDirection a hN0 k z) =
      ∫ x, FlatAliveGood.flatWeight a hN0 k z x
        ∂Erdos88.Invariance.rademacherProductMeasure
          (scale N0 (k + 1) - scale N0 k) := by
  rfl

lemma pairRademacherExpectation_flat_eq
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (k : ℕ) (z w : ℂ) :
    PairFactorization.pairRademacherExpectation
        (FlatAliveGood.flatEndpointScale k) (FlatAliveGood.flatPrefixScale a N0 k)
        (PairFactorization.flatPairDirection a hN0 k z w) =
      ∫ x, FlatAliveGood.flatWeight a hN0 k z x *
          FlatAliveGood.flatWeight a hN0 k w x
        ∂Erdos88.Invariance.rademacherProductMeasure
          (scale N0 (k + 1) - scale N0 k) := by
  rw [PairFactorization.pairRademacherExpectation_eq_integral_mul]
  simp only [PairFactorization.flatPairDirection_apply_zero,
    PairFactorization.flatPairDirection_apply_one]
  rfl

/-- The concrete one-generation estimate with all analytic inputs exposed.
The eventual theorem below supplies these four scale-local hypotheses. -/
theorem fixedParent_transition_bad_le
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) {k : ℕ} (hk : 1000 ≤ k)
    (henv : coefficientEnvelope a N0 k ≤ 1)
    (honePoint : ∀ z : ℂ, ‖z‖ = 1 →
      onePointTarget k ≤
        ∫ x, flatWeight a hN0 k z x
          ∂Erdos88.Invariance.rademacherProductMeasure
            (scale N0 (k + 1) - scale N0 k))
    (hpairFactor : ∀ x y : UnitAddCircle,
      (∀ j : Fin (uniformBlockCount k),
        ¬ IsCorrelated (fun n ↦ (a n : ℂ))
          (uniformEndpoint N0 k j - 1) (uniformBlockLength N0 k) x y
          (correlationThreshold k)) →
      pairRademacherExpectation (concreteEndpointScale k)
            (concretePrefixScale a N0 k)
            (flatPairDirection a hN0 k
              (PairApplication.phasePoint x)
              (PairApplication.phasePoint y)) ≤
        phaseRademacherExpectation (concreteEndpointScale k)
              (concretePrefixScale a N0 k)
              (flatBlockIncrementDirection a hN0 k
                (PairApplication.phasePoint x)) *
            phaseRademacherExpectation (concreteEndpointScale k)
              (concretePrefixScale a N0 k)
              (flatBlockIncrementDirection a hN0 k
                (PairApplication.phasePoint y)) +
          12 * (((2 ^ stepExponent k : ℕ) : ℝ) ^ 10) *
            correlationThreshold k ^ (1 / 4 : ℝ))
    (A : Finset ℂ) (hAgrid : A ⊆ RecursiveAlive.rootGrid N0 hN0 k)
    (hAsize : targetSize k ≤ A.card) :
    Erdos88.Invariance.rademacherProductMeasure
        (scale N0 (k + 1) - scale N0 k)
        {x | FlatTransitionFailure.flatTransitionBad a hN0 k A x} ≤
      ENNReal.ofReal
        (offCorrelationFailureBound k + correlatedPairFailureBound k) := by
  classical
  letI : NeZero N0 := ⟨hN0.ne'⟩
  letI : NeZero (scale N0 (k + 1)) :=
    ⟨scale_ne_zero hN0.ne' (k + 1)⟩
  let μ := Erdos88.Invariance.rademacherProductMeasure
    (scale N0 (k + 1) - scale N0 k)
  let C := RecursiveAlive.scaleChildren N0 hN0 k A
  let w : ℂ → (Fin (scale N0 (k + 1) - scale N0 k) → ℝ) → ℝ :=
    fun z ↦ flatWeight a hN0 k z
  let good : ℂ → (Fin (scale N0 (k + 1) - scale N0 k) → ℝ) → Prop :=
    fun z x ↦ flatGood a hN0 k z x
  let corr : ℂ → ℂ → Prop :=
    scalePairCorrelated a N0 hN0 k (correlationThreshold k)
  let e : ℝ := 12 * (((2 ^ stepExponent k : ℕ) : ℝ) ^ 10) *
    correlationThreshold k ^ (1 / 4 : ℝ)
  let D : ℝ := orderedPairCharge a N0 hN0 k (correlationThreshold k) C
  have hCgrid : C ⊆ RecursiveAlive.rootGrid N0 hN0 (k + 1) := by
    exact RecursiveAlive.scaleChildren_subset_rootGrid_succ N0 hN0 k A
  have hCcard : C.card =
      A.card * (2 ^ stepExponent k / (k + 2) ^ 20) := by
    exact card_flatCandidateSet a hN0 k hAgrid
  have hrep : 0 < 2 ^ stepExponent k / (k + 2) ^ 20 := by
    apply Nat.div_pos
    · simpa only [Grid.branchChildDenom] using
        (Grid.branchChildDenom_le_scale_refinement (k := k) (by omega))
    · positivity
  have hApos : 0 < A.card := (targetSize_pos k).trans_le hAsize
  have hCnonempty : C.Nonempty := by
    apply Finset.card_pos.mp
    rw [hCcard]
    positivity
  have hs : (targetSize (k + 1) : ℝ) ≤
      onePointTarget k * (C.card : ℝ) / 2 := by
    calc
      (targetSize (k + 1) : ℝ) ≤
          onePointTarget k *
            ((targetSize k : ℝ) *
              ((2 ^ stepExponent k / Grid.branchChildDenom k : ℕ) : ℝ)) / 2 :=
        targetSize_succ_le_expected_children_half hk
      _ ≤ onePointTarget k *
            ((A.card : ℝ) *
              ((2 ^ stepExponent k / Grid.branchChildDenom k : ℕ) : ℝ)) / 2 := by
        gcongr
        · exact onePointTarget_nonneg k
      _ = onePointTarget k * (C.card : ℝ) / 2 := by
        rw [hCcard]
        simp only [Grid.branchChildDenom, Nat.cast_mul]
  have hw : ∀ z ∈ C, MemLp (w z) 2 μ := by
    intro z hz
    exact flatWeight_memLp_rademacher a hN0 k z 2
  have hone : ∀ z ∈ C, onePointTarget k ≤ μ[w z] := by
    intro z hz
    apply honePoint z
    have hzroot : z ∈ Grid.complexRootGrid (scale N0 (k + 1)) := by
      simpa only [RecursiveAlive.rootGrid] using hCgrid hz
    rcases Finset.mem_image.mp hzroot with ⟨j, hj, rfl⟩
    exact Grid.norm_complexGridPoint _ _
  have he : 0 ≤ e := by
    dsimp only [e]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg _) _))
      (Real.rpow_nonneg (correlationThreshold_nonneg k) _)
  have hD : 0 ≤ D := by
    dsimp only [D, orderedPairCharge]
    positivity
  have hcharge :
      (∑ z ∈ C, ∑ y ∈ C, if corr z y then (1 : ℝ) else 0) ≤ D := by
    rfl
  have hpair : ∀ z ∈ C, ∀ y ∈ C,
      μ[fun x ↦ w z x * w y x] ≤
        μ[w z] * μ[w y] + (e + if corr z y then 1 else 0) := by
    intro z hz y hy
    by_cases hzy : corr z y
    · have hzmem := hw z hz
      have hymem := hw y hy
      have hprodLp : MemLp (fun x ↦ w z x * w y x) 1 μ :=
        hymem.mul hzmem
      have hprod : Integrable (fun x ↦ w z x * w y x) μ :=
        hprodLp.integrable (by norm_num)
      have hjoint : μ[fun x ↦ w z x * w y x] ≤ 1 := by
        change (∫ x, w z x * w y x ∂μ) ≤ 1
        calc
          (∫ x, w z x * w y x ∂μ) ≤ ∫ _x, (1 : ℝ) ∂μ := by
            apply integral_mono hprod (integrable_const (1 : ℝ))
            intro x
            have hz0 := flatWeight_nonneg a hN0 k z x
            have hz1 := flatWeight_le_one a hN0 k z x
            have hy0 := flatWeight_nonneg a hN0 k y x
            have hy1 := flatWeight_le_one a hN0 k y x
            dsimp only [w]
            calc
              flatWeight a hN0 k z x * flatWeight a hN0 k y x ≤
                  1 * flatWeight a hN0 k y x :=
                mul_le_mul_of_nonneg_right hz1 hy0
              _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hy1 (by norm_num)
              _ = 1 := by ring
          _ = 1 := by simp [μ]
      have hzmean : 0 ≤ μ[w z] := by
        apply integral_nonneg
        intro x
        exact flatWeight_nonneg a hN0 k z x
      have hymean : 0 ≤ μ[w y] := by
        apply integral_nonneg
        intro x
        exact flatWeight_nonneg a hN0 k y x
      simp only [hzy, if_true]
      nlinarith [mul_nonneg hzmean hymean]
    · have hzroot : z ∈ Grid.complexRootGrid (scale N0 (k + 1)) := by
        simpa only [RecursiveAlive.rootGrid] using hCgrid hz
      have hyroot : y ∈ Grid.complexRootGrid (scale N0 (k + 1)) := by
        simpa only [RecursiveAlive.rootGrid] using hCgrid hy
      have huncorr : ∀ j : Fin (uniformBlockCount k),
          ¬ IsCorrelated (fun n ↦ (a n : ℂ))
            (uniformEndpoint N0 k j - 1) (uniformBlockLength N0 k)
            (PairCorrelationApplication.phasePoint (scale N0 (k + 1)) z)
            (PairCorrelationApplication.phasePoint (scale N0 (k + 1)) y)
            (correlationThreshold k) := by
        intro j hj
        apply hzy
        exact ⟨j, hj⟩
      have hraw := hpairFactor
        (PairCorrelationApplication.phasePoint (scale N0 (k + 1)) z)
        (PairCorrelationApplication.phasePoint (scale N0 (k + 1)) y) huncorr
      rw [complex_phasePoint_eq_root (scale N0 (k + 1)) hzroot,
        complex_phasePoint_eq_root (scale N0 (k + 1)) hyroot] at hraw
      change pairRademacherExpectation (flatEndpointScale k)
          (flatPrefixScale a N0 k) (flatPairDirection a hN0 k z y) ≤
        phaseRademacherExpectation (flatEndpointScale k) (flatPrefixScale a N0 k)
              (flatBlockIncrementDirection a hN0 k z) *
            phaseRademacherExpectation (flatEndpointScale k) (flatPrefixScale a N0 k)
              (flatBlockIncrementDirection a hN0 k y) + e at hraw
      rw [pairRademacherExpectation_flat_eq a hN0 k z y,
        phaseRademacherExpectation_flat_eq a hN0 k z,
        phaseRademacherExpectation_flat_eq a hN0 k y] at hraw
      simpa only [hzy, if_false, add_zero, μ, w, e] using hraw
  have hsandwich : ∀ z ∈ C, ∀ x,
      w z x ≤ if good z x then 1 else 0 := by
    intro z hz x
    exact flatWeight_le_ite_good a hN0 k z x
  have hraw := measure_aliveCandidates_card_lt_of_pair_bounds
    μ C w good corr (onePointTarget_pos k) hCnonempty he hD hs
    hw hone hpair hcharge hsandwich
  have hCtarget : (targetSize k : ℝ) ≤ (C.card : ℝ) := by
    have hrepOne : 1 ≤ 2 ^ stepExponent k / (k + 2) ^ 20 := hrep
    have hAC : A.card ≤ C.card := by
      rw [hCcard]
      exact Nat.le_mul_of_pos_right A.card hrep
    exact_mod_cast hAsize.trans hAC
  have hordered := orderedPairCharge_le a hsmall hN0 k C hCgrid henv
    (correlationThreshold_pos k)
  have hoff : 4 * e / onePointTarget k ^ 2 ≤
      offCorrelationFailureBound k := by
    apply normalized_offCorrelation_charge_le k
    exact le_rfl
  have hcorrNorm : 4 * D / (onePointTarget k * (C.card : ℝ)) ^ 2 ≤
      correlatedPairFailureBound k := by
    apply normalized_correlated_charge_le k hCtarget
    simpa only [D] using hordered
  have hCcardpos : (0 : ℝ) < C.card := by
    exact_mod_cast hCnonempty.card_pos
  have hnormalized :
      4 * (e * (C.card : ℝ) ^ 2 + D) /
          (onePointTarget k * (C.card : ℝ)) ^ 2 ≤
        offCorrelationFailureBound k + correlatedPairFailureBound k := by
    rw [show 4 * (e * (C.card : ℝ) ^ 2 + D) /
          (onePointTarget k * (C.card : ℝ)) ^ 2 =
        4 * e / onePointTarget k ^ 2 +
          4 * D / (onePointTarget k * (C.card : ℝ)) ^ 2 by
      field_simp [ne_of_gt (onePointTarget_pos k), ne_of_gt hCcardpos]
      <;> ring]
    exact add_le_add hoff hcorrNorm
  have hraw' := hraw.trans (ENNReal.ofReal_le_ofReal hnormalized)
  simpa only [FlatTransitionFailure.flatTransitionBad, hAsize, true_and,
    FiniteGridBranching.aliveCandidates, FlatAliveGood.flatGoodTransition,
    RecursiveAlive.filterGood, Nat.cast_lt, μ, C, w, good, corr, e, D] using hraw'

/-- All hypotheses of `fixedParent_transition_bad_le` hold eventually and
uniformly in the deterministic parent set. -/
theorem eventually_fixedParent_transition_bad_le
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) :
    ∀ᶠ k : ℕ in atTop, ∀ A : Finset ℂ,
      A ⊆ RecursiveAlive.rootGrid N0 hN0 k →
      targetSize k ≤ A.card →
      Erdos88.Invariance.rademacherProductMeasure
          (scale N0 (k + 1) - scale N0 k)
          {x | FlatTransitionFailure.flatTransitionBad a hN0 k A x} ≤
        ENNReal.ofReal
          (offCorrelationFailureBound k + correlatedPairFailureBound k) := by
  filter_upwards [eventually_ge_atTop 1000,
    OnePointAsymptotic.eventually_coefficientEnvelope_le_one a hsmall hN0,
    OnePointApplication.eventually_onePointTarget_le_flatWeight_integral
      a hsmall hN0,
    PairApplication.eventually_flat_pair_expectation_le_product_add_single_budget
      a hsmall hN0] with k hk henv hone hpair
  intro A hAgrid hAsize
  exact fixedParent_transition_bad_le a hsmall hN0 hk henv hone hpair
    A hAgrid hAsize

/-- The same eventual estimate is uniform over *all* deterministic parents:
for a small parent the charged local-failure event is empty by definition. -/
theorem eventually_uniform_fixedParent_transition_bad_le
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) :
    ∀ᶠ k : ℕ in atTop, ∀ A : Finset ℂ,
      A ⊆ RecursiveAlive.rootGrid N0 hN0 k →
      Erdos88.Invariance.rademacherProductMeasure
          (scale N0 (k + 1) - scale N0 k)
          {x | FlatTransitionFailure.flatTransitionBad a hN0 k A x} ≤
        ENNReal.ofReal
          (offCorrelationFailureBound k + correlatedPairFailureBound k) := by
  filter_upwards [eventually_fixedParent_transition_bad_le a hsmall hN0]
    with k hk
  intro A hAgrid
  by_cases hAsize : targetSize k ≤ A.card
  · exact hk A hAgrid hAsize
  · simp only [FlatTransitionFailure.flatTransitionBad, hAsize, false_and,
      Set.setOf_false, measure_empty]
    exact bot_le

/-- A single sufficiently late reset scale gives the desired unconditional
bound at every subsequent adaptive generation. -/
theorem exists_start_adaptive_transitionFailure_le
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) :
    ∃ start : ℕ, ∀ t : ℕ,
      rademacherProductMeasure
          (FiniteGridBranching.transitionFailure
            (FlatAliveGood.flatAlive a hN0 start)
            (fun u ↦ targetSize (start + u)) t) ≤
        ENNReal.ofReal
          (offCorrelationFailureBound (start + t) +
            correlatedPairFailureBound (start + t)) := by
  have hev := eventually_uniform_fixedParent_transition_bad_le a hsmall hN0
  rw [Filter.eventually_atTop] at hev
  rcases hev with ⟨start, hstart⟩
  refine ⟨start, fun t ↦ ?_⟩
  apply FlatTransitionFailure.measure_finiteGridBranching_transitionFailure_le
    a hN0 start t
  intro A hAgrid
  exact hstart (start + t) (Nat.le_add_right start t) A hAgrid

/-- The ENNReal tail of the complete pair-failure budget tends to zero. -/
theorem ofReal_totalPairFailureTail_tendsto_zero :
    Tendsto (fun k ↦ ∑' j : ℕ,
        ENNReal.ofReal
          (offCorrelationFailureBound (j + k) +
            correlatedPairFailureBound (j + k)))
      atTop (nhds 0) := by
  exact ENNReal.tendsto_sum_nat_add
    (fun k ↦ ENNReal.ofReal
      (offCorrelationFailureBound k + correlatedPairFailureBound k))
    summable_total_pairFailureBound.tsum_ofReal_ne_top

/-- In particular, every shifted adaptive majorant has finite total mass. -/
theorem shifted_totalPairFailure_tsum_ne_top (start : ℕ) :
    (∑' t : ℕ, ENNReal.ofReal
      (offCorrelationFailureBound (start + t) +
        correlatedPairFailureBound (start + t))) ≠ ∞ := by
  have hsum : Summable (fun t : ℕ ↦
      offCorrelationFailureBound (start + t) +
        correlatedPairFailureBound (start + t)) :=
    summable_total_pairFailureBound.comp_injective
      (fun _ _ h ↦ Nat.add_left_cancel h)
  exact hsum.tsum_ofReal_ne_top

end

end Erdos527.FixedParentTransition

open scoped BigOperators ENNReal NNReal ProbabilityTheory Topology
open Filter MeasureTheory ProbabilityTheory Set

namespace Erdos527.TerminalAE

noncomputable section

/-- After every sufficiently late reset, each subsequent adaptive transition
has the shifted pair-correlation failure bound. -/
def EventualAdaptiveTransitionBound
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) : Prop :=
  ∀ᶠ start : ℕ in atTop, ∀ t : ℕ,
    rademacherProductMeasure
        (FiniteGridBranching.transitionFailure
          (FlatAliveGood.flatAlive a hN0 start)
          (fun u => BranchParameterArithmetic.targetSize (start + u)) t) ≤
      ENNReal.ofReal
        (BranchParameterArithmetic.offCorrelationFailureBound (start + t) +
          BranchParameterArithmetic.correlatedPairFailureBound (start + t))

/-- An eventual property holds at every shift from every sufficiently late
starting point. -/
lemma eventually_forall_add_of_eventually {P : ℕ → Prop}
    (hP : ∀ᶠ k : ℕ in atTop, P k) :
    ∀ᶠ start : ℕ in atTop, ∀ t : ℕ, P (start + t) := by
  rcases eventually_atTop.1 hP with ⟨K, hK⟩
  filter_upwards [eventually_ge_atTop K] with start hstart
  intro t
  exact hK (start + t) (hstart.trans (Nat.le_add_right start t))

lemma measurableSet_shifted_flatAlive_transitionFailure
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) (start t : ℕ) :
    MeasurableSet
      (FiniteGridBranching.transitionFailure
        (FlatAliveGood.flatAlive a hN0 start)
        (fun u => BranchParameterArithmetic.targetSize (start + u)) t) := by
  rw [← FlatTransitionFailure.recursiveTransitionFailure_eq_finiteGridBranching
    a hN0 start t]
  exact RecursiveAlive.measurableSet_transitionFailure hN0 start
    (FlatAliveGood.flatGood_measurable a hN0)
    (FlatTransitionFailure.flatTransitionBad_measurable a hN0) t

lemma initial_flatAlive_strong
    (a : ℕ → ℝ) {N0 : ℕ} (hN0 : 0 < N0) {start : ℕ}
    (htarget : BranchParameterArithmetic.targetSize start ≤ scale N0 start) :
    ∀ ε,
      ε ∈ FiniteGridBranching.StrongAt
        (FlatAliveGood.flatAlive a hN0 start)
        (fun t => BranchParameterArithmetic.targetSize (start + t)) 0 := by
  intro ε
  simp only [FiniteGridBranching.StrongAt, Set.mem_setOf_eq, Nat.add_zero]
  rw [show FlatAliveGood.flatAlive a hN0 start 0 ε =
      RecursiveAlive.rootGrid N0 hN0 start by rfl]
  simpa only [RecursiveAlive.rootGrid, Grid.card_complexRootGrid] using htarget

lemma eventualAdaptiveTransitionBound
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) :
    EventualAdaptiveTransitionBound a hN0 := by
  have hparent :=
    FixedParentTransition.eventually_uniform_fixedParent_transition_bad_le
      a hsmall hN0
  have hshifted := eventually_forall_add_of_eventually hparent
  filter_upwards [hshifted] with start hstart
  intro t
  apply FlatTransitionFailure.measure_finiteGridBranching_transitionFailure_le
    a hN0 start t
  intro A hAgrid
  exact hstart t A hAgrid

lemma ofReal_pairFailureTail_tendsto_zero :
    Tendsto (fun start ↦ ∑' t : ℕ,
      ENNReal.ofReal
        (BranchParameterArithmetic.offCorrelationFailureBound (start + t) +
          BranchParameterArithmetic.correlatedPairFailureBound (start + t)))
      atTop (𝓝 0) := by
  simpa only [Nat.add_comm] using
    FixedParentTransition.ofReal_totalPairFailureTail_tendsto_zero

/-- Total shifted tail of branching and auxiliary-grid failures. -/
def totalFailureTail (a : ℕ → ℝ) (N0 start : ℕ) : ℝ≥0∞ :=
  ∑' t : ℕ,
    (ENNReal.ofReal
        (BranchParameterArithmetic.offCorrelationFailureBound (start + t) +
          BranchParameterArithmetic.correlatedPairFailureBound (start + t)) +
      ENNReal.ofReal
        (FailureMeasurability.combinedFailureBound a N0 (start + t)))

lemma totalFailureTail_tendsto_zero
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} (hN0 : 0 < N0) :
    Tendsto (totalFailureTail a N0) atTop (𝓝 0) := by
  have ht : Tendsto (fun start ↦ ∑' t : ℕ,
      ENNReal.ofReal
        (BranchParameterArithmetic.offCorrelationFailureBound (start + t) +
          BranchParameterArithmetic.correlatedPairFailureBound (start + t)))
      atTop (𝓝 0) := ofReal_pairFailureTail_tendsto_zero
  have hg : Tendsto (fun start ↦ ∑' t : ℕ,
      ENNReal.ofReal
        (FailureMeasurability.combinedFailureBound a N0 (start + t)))
      atTop (𝓝 0) := by
    simpa only [Nat.add_comm] using
      FailureMeasurability.ofReal_combinedFailureTail_tendsto_zero
        a hsmall hN0
  have hadd := ht.add hg
  rw [show totalFailureTail a N0 = fun start ↦
      (∑' t : ℕ, ENNReal.ofReal
        (BranchParameterArithmetic.offCorrelationFailureBound (start + t) +
          BranchParameterArithmetic.correlatedPairFailureBound (start + t))) +
      (∑' t : ℕ, ENNReal.ofReal
        (FailureMeasurability.combinedFailureBound a N0 (start + t))) by
    funext start
    exact ENNReal.tsum_add]
  simpa only [add_zero] using hadd

/-- The measurable set of genuine sign sequences. -/
def signSequenceSet : Set (ℕ → ℝ) :=
  {ε | ∀ n, ε n = 1 ∨ ε n = -1}

lemma measurableSet_signSequenceSet : MeasurableSet signSequenceSet := by
  rw [show signSequenceSet = ⋂ n : ℕ,
      (fun ε : ℕ → ℝ => ε n) ⁻¹' ({1} ∪ {-1} : Set ℝ) by
    ext ε
    simp only [signSequenceSet, Set.mem_setOf_eq, Set.mem_iInter,
      Set.mem_preimage, Set.mem_union, Set.mem_singleton_iff]]
  apply MeasurableSet.iInter
  intro n
  exact ((MeasurableSet.singleton 1).union (MeasurableSet.singleton (-1))).preimage
    (measurable_pi_apply n)

lemma ae_mem_signSequenceSet :
    ∀ᵐ ε ∂rademacherProductMeasure, ε ∈ signSequenceSet := by
  simpa only [signSequenceSet, Set.mem_setOf_eq] using ae_rademacherProduct_signs

/-- For every requested error, the eventual adaptive transition estimate
produces a measurable subset of the exact convergence event with mass at
least `1-η`. -/
theorem exists_measurable_convergence_goodSet
    (a : ℕ → ℝ) (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} [NeZero N0] (hN0 : 0 < N0)
    (hadaptive : EventualAdaptiveTransitionBound a hN0)
    (η : ℝ≥0∞) (hη : 0 < η) (_hηone : η ≤ 1) :
    ∃ G : Set (ℕ → ℝ), MeasurableSet G ∧ G ⊆ convergenceEvent a ∧
      1 - η ≤ rademacherProductMeasure G := by
  have htailEventually : ∀ᶠ start : ℕ in atTop,
      totalFailureTail a N0 start ≤ η := by
    have hlt := (tendsto_order.1
      (totalFailureTail_tendsto_zero a hsmall hN0)).2 η hη
    exact hlt.mono (fun _ hs => hs.le)
  have htargetEventually :=
    BranchParameterArithmetic.eventually_targetSize_le_scale hN0
  have henvEventually := eventually_forall_add_of_eventually
    (OnePointAsymptotic.eventually_coefficientEnvelope_le_one a hsmall hN0)
  have hlogEventually := eventually_forall_add_of_eventually
    (DerivativeEvents.eventually_derivative_log_large hN0)
  have hendpointEventually := eventually_forall_add_of_eventually
    (DerivativeEvents.eventually_transportError_le_inv_two_succ_sq hN0)
  have hprefixEventually := eventually_forall_add_of_eventually
    (DerivativeEvents.eventually_transportError_le_sqrt_coefficientEnvelope_div_two
      a hsmall hN0)
  have hall : ∀ᶠ start : ℕ in atTop,
      totalFailureTail a N0 start ≤ η ∧
      BranchParameterArithmetic.targetSize start ≤ scale N0 start ∧
      (∀ t : ℕ,
        rademacherProductMeasure
            (FiniteGridBranching.transitionFailure
              (FlatAliveGood.flatAlive a hN0 start)
              (fun u => BranchParameterArithmetic.targetSize (start + u)) t) ≤
          ENNReal.ofReal
            (BranchParameterArithmetic.offCorrelationFailureBound (start + t) +
              BranchParameterArithmetic.correlatedPairFailureBound (start + t))) ∧
      (∀ t, coefficientEnvelope a N0 (start + t) ≤ 1) ∧
      (∀ t, (2080 : ℝ) ≤ Real.log (scale N0 (start + t + 1) : ℝ)) ∧
      (∀ t, DerivativeEvents.transportError N0 (start + t) ≤
        1 / (2 * ((((start + t) + 1 : ℕ) : ℝ) ^ 2))) ∧
      (∀ t, DerivativeEvents.transportError N0 (start + t) ≤
        Real.sqrt (coefficientEnvelope a N0 (start + t)) / 2) := by
    filter_upwards [htailEventually, htargetEventually, hadaptive,
      henvEventually, hlogEventually, hendpointEventually, hprefixEventually]
        with start htail htarget htransition henv hlog hendpoint hprefix
    exact ⟨htail, htarget, htransition, henv, hlog, hendpoint, hprefix⟩
  rcases hall.exists with
    ⟨start, htail, htarget, htransition, henv, hlog, hendpoint, hprefix⟩
  rcases FinalProbabilityAssembly.exists_measurable_flatAlive_combinedGrid_goodSet
      a hsmall hN0 start
      (fun t ↦ ENNReal.ofReal
        (BranchParameterArithmetic.offCorrelationFailureBound (start + t) +
          BranchParameterArithmetic.correlatedPairFailureBound (start + t)))
      (initial_flatAlive_strong a hN0 htarget)
      (measurableSet_shifted_flatAlive_transitionFailure a hN0 start)
      htransition henv hlog with ⟨G₀, hG₀meas, hG₀mass, hG₀path⟩
  let G : Set (ℕ → ℝ) := G₀ ∩ signSequenceSet
  have hGmeas : MeasurableSet G :=
    hG₀meas.inter measurableSet_signSequenceSet
  have hGmeasure : rademacherProductMeasure G =
      rademacherProductMeasure G₀ := by
    apply measure_congr
    filter_upwards [ae_mem_signSequenceSet] with ε hε
    change (ε ∈ G) = (ε ∈ G₀)
    simp [G, hε]
  refine ⟨G, hGmeas, ?_, ?_⟩
  · intro ε hε
    have hpath := hG₀path ε hε.1
    have havoid := hpath.2
    have hprefixNot : ∀ k, start ≤ k →
        ε ∉ flatPrefixGridFailure a N0 k (prefixPhaseGridSize N0 k)
          (prefixTolerance N0 k / 2) := by
      intro k hk hp
      have hc := havoid (k - start)
      rw [Nat.add_sub_of_le hk] at hc
      exact hc (Or.inl hp)
    have hderNot : ∀ k, start ≤ k →
        ε ∉ DerivativeEvents.derivativeGridFailure a N0 k := by
      intro k hk hd
      have hc := havoid (k - start)
      rw [Nat.add_sub_of_le hk] at hc
      exact hc (Or.inr hd)
    exact convergenceEvent_of_flatAlive_pathwise a hsmall hN0 start ε
      hpath.1 (fun k hk => by
        obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
        exact henv t)
      hprefixNot hderNot
      (fun k hk => by
        obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
        exact hendpoint t)
      (fun k hk => by
        obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
        exact hprefix t)
      hε.2
  · rw [hGmeasure]
    exact (tsub_le_tsub_left htail 1).trans hG₀mass

/-- Exact almost-sure conclusion, conditional only on the adaptive transition
interface. -/
theorem ae_convergence_of_eventualAdaptiveTransitionBound
    (a : ℕ → ℝ) (hsq : SquareSumDiverges a)
    (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} [NeZero N0] (hN0 : 0 < N0)
    (hadaptive : EventualAdaptiveTransitionBound a hN0) :
    ∀ᵐ ε ∂rademacherProductMeasure,
      ∃ z : ℂ, ‖z‖ = 1 ∧ SeriesConvergesAt a ε z := by
  apply erdos_527_of_probability_lower_bound a hsq hsmall
  intro η hη hηone
  exact exists_measurable_convergence_goodSet
    a hsmall hN0 hadaptive η hη hηone

/-- The terminal almost-sure conclusion at any positive base scale. -/
theorem ae_convergence
    (a : ℕ → ℝ) (hsq : SquareSumDiverges a)
    (hsmall : DecaysFasterThanInvSqrt a)
    {N0 : ℕ} [NeZero N0] (hN0 : 0 < N0) :
    ∀ᵐ ε ∂rademacherProductMeasure,
      ∃ z : ℂ, ‖z‖ = 1 ∧ SeriesConvergesAt a ε z := by
  exact ae_convergence_of_eventualAdaptiveTransitionBound
    a hsq hsmall hN0 (eventualAdaptiveTransitionBound a hsmall hN0)

end

end Erdos527.TerminalAE

namespace Erdos527

/-- Erdős Problem 527: almost every Rademacher signing admits a point on the
unit circle at which the naturally ordered signed power series converges. -/
theorem erdos_527
    (a : ℕ → ℝ) (hsq : SquareSumDiverges a)
    (hsmall : DecaysFasterThanInvSqrt a) :
    ∀ᵐ ε ∂rademacherProductMeasure,
      ∃ z : ℂ, ‖z‖ = 1 ∧ SeriesConvergesAt a ε z := by
  exact TerminalAE.ae_convergence a hsq hsmall (N0 := 1) (by norm_num)

end Erdos527
