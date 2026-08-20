/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib

/-!
# Finite concentration tools for Erdős 722

The random reserve and random-greedy stages repeatedly apply concentration
to finite independent families.  This file packages Mathlib's sub-Gaussian
Hoeffding theorem in the exact bounded-variable form used by those stages.
-/

namespace Erdos722.Probability

open MeasureTheory ProbabilityTheory Finset

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The sub-Gaussian variance proxy for a real random variable taking values
in an interval of length one. -/
noncomputable def hoeffdingUnitVariance : NNReal := ((1 : NNReal) / 2) ^ 2

/-- Finite product space of independent Bernoulli coordinates. -/
noncomputable def bernoulliProductMeasure
    {ι : Type*} [Fintype ι] (p : Set.Icc (0 : ℝ) 1) : Measure (ι → Bool) :=
  Measure.pi fun _ : ι ↦ ProbabilityTheory.bernoulliMeasure true false p

noncomputable instance bernoulliProductMeasure.instIsProbabilityMeasure
    {ι : Type*} [Fintype ι] (p : Set.Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (bernoulliProductMeasure (ι := ι) p) := by
  unfold bernoulliProductMeasure
  infer_instance

/-- Finite product space with a possibly different Bernoulli parameter at
each coordinate.  The constant-parameter reserve experiment is a special
case; the regularity boost needs this heterogeneous form after applying the
local-decoder correction. -/
noncomputable def varyingBernoulliProductMeasure
    {ι : Type*} [Fintype ι] (p : ι → Set.Icc (0 : ℝ) 1) :
    Measure (ι → Bool) :=
  Measure.pi fun i : ι ↦ ProbabilityTheory.bernoulliMeasure true false (p i)

noncomputable instance varyingBernoulliProductMeasure.instIsProbabilityMeasure
    {ι : Type*} [Fintype ι] (p : ι → Set.Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (varyingBernoulliProductMeasure p) := by
  unfold varyingBernoulliProductMeasure
  infer_instance

/-- Real indicator of one Bernoulli coordinate. -/
def coordinateIndicator {ι : Type*} (i : ι) (ω : ι → Bool) : ℝ :=
  if ω i = true then 1 else 0

lemma coordinateIndicator_measurable {ι : Type*} [Fintype ι] (i : ι) :
    Measurable (coordinateIndicator i) := by
  exact (measurable_of_finite (fun b : Bool ↦ if b then (1 : ℝ) else 0)).comp
    (measurable_pi_apply i)

lemma coordinateIndicator_iIndep {ι : Type*} [Fintype ι]
    (p : Set.Icc (0 : ℝ) 1) :
    iIndepFun (fun i ↦ coordinateIndicator i)
      (bernoulliProductMeasure (ι := ι) p) := by
  have hbool : iIndepFun (fun i (ω : ι → Bool) ↦ ω i)
      (bernoulliProductMeasure (ι := ι) p) := by
    unfold bernoulliProductMeasure
    exact iIndepFun_pi (X := fun _ ↦ id)
      (fun _ ↦ measurable_id.aemeasurable)
  have h := hbool.comp (γ := fun _ ↦ ℝ)
    (mγ := fun _ ↦ Real.measurableSpace)
    (fun _ b ↦ if b then (1 : ℝ) else 0) (fun _ ↦ by fun_prop)
  change iIndepFun (fun i ω ↦ if ω i = true then (1 : ℝ) else 0)
    (bernoulliProductMeasure (ι := ι) p)
  simpa [Function.comp_def] using h

lemma coordinateIndicator_iIndep_varying {ι : Type*} [Fintype ι]
    (p : ι → Set.Icc (0 : ℝ) 1) :
    iIndepFun (fun i ↦ coordinateIndicator i)
      (varyingBernoulliProductMeasure p) := by
  have hbool : iIndepFun (fun i (ω : ι → Bool) ↦ ω i)
      (varyingBernoulliProductMeasure p) := by
    unfold varyingBernoulliProductMeasure
    exact iIndepFun_pi (X := fun _ ↦ id)
      (fun _ ↦ measurable_id.aemeasurable)
  have h := hbool.comp (γ := fun _ ↦ ℝ)
    (mγ := fun _ ↦ Real.measurableSpace)
    (fun _ b ↦ if b then (1 : ℝ) else 0) (fun _ ↦ by fun_prop)
  change iIndepFun (fun i ω ↦ if ω i = true then (1 : ℝ) else 0)
    (varyingBernoulliProductMeasure p)
  simpa [Function.comp_def] using h

lemma integral_coordinateIndicator {ι : Type*} [Fintype ι]
    (p : Set.Icc (0 : ℝ) 1) (i : ι) :
    ∫ ω, coordinateIndicator i ω ∂bernoulliProductMeasure (ι := ι) p = p := by
  rw [bernoulliProductMeasure]
  change (∫ ω : ι → Bool, (if ω i = true then (1 : ℝ) else 0)
    ∂Measure.pi fun _ : ι ↦
      ProbabilityTheory.bernoulliMeasure true false p) = p
  calc
    (∫ ω : ι → Bool, (if ω i = true then (1 : ℝ) else 0)
        ∂Measure.pi fun _ : ι ↦
          ProbabilityTheory.bernoulliMeasure true false p) =
        ∫ b : Bool, (if b = true then (1 : ℝ) else 0)
          ∂ProbabilityTheory.bernoulliMeasure true false p := by
      exact MeasureTheory.integral_comp_eval
        (ι := ι) (X := fun _ : ι ↦ Bool)
        (μ := fun _ : ι ↦ ProbabilityTheory.bernoulliMeasure true false p)
        (i := i) (f := fun b : Bool ↦ if b = true then (1 : ℝ) else 0)
        ((measurable_of_finite
          (fun b : Bool ↦ if b = true then (1 : ℝ) else 0)).aestronglyMeasurable)
    _ = p := by
      rw [ProbabilityTheory.integral_bernoulliMeasure]
      simp

lemma integral_coordinateIndicator_varying {ι : Type*} [Fintype ι]
    (p : ι → Set.Icc (0 : ℝ) 1) (i : ι) :
    ∫ ω, coordinateIndicator i ω ∂varyingBernoulliProductMeasure p = p i := by
  rw [varyingBernoulliProductMeasure]
  change (∫ ω : ι → Bool, (if ω i = true then (1 : ℝ) else 0)
    ∂Measure.pi fun j : ι ↦
      ProbabilityTheory.bernoulliMeasure true false (p j)) = p i
  calc
    (∫ ω : ι → Bool, (if ω i = true then (1 : ℝ) else 0)
        ∂Measure.pi fun j : ι ↦
          ProbabilityTheory.bernoulliMeasure true false (p j)) =
        ∫ b : Bool, (if b = true then (1 : ℝ) else 0)
          ∂ProbabilityTheory.bernoulliMeasure true false (p i) := by
      exact MeasureTheory.integral_comp_eval
        (ι := ι) (X := fun _ : ι ↦ Bool)
        (μ := fun j : ι ↦ ProbabilityTheory.bernoulliMeasure true false (p j))
        (i := i) (f := fun b : Bool ↦ if b = true then (1 : ℝ) else 0)
        ((measurable_of_finite
          (fun b : Bool ↦ if b = true then (1 : ℝ) else 0)).aestronglyMeasurable)
    _ = p i := by
      rw [ProbabilityTheory.integral_bernoulliMeasure]
      simp

lemma coordinateIndicator_mem_Icc {ι : Type*} [Fintype ι]
    (p : Set.Icc (0 : ℝ) 1) (i : ι) :
    ∀ᵐ ω ∂bernoulliProductMeasure (ι := ι) p,
      coordinateIndicator i ω ∈ Set.Icc (0 : ℝ) 1 := by
  filter_upwards [] with ω
  cases h : ω i <;> simp [coordinateIndicator, h]

lemma coordinateIndicator_mem_Icc_varying {ι : Type*} [Fintype ι]
    (p : ι → Set.Icc (0 : ℝ) 1) (i : ι) :
    ∀ᵐ ω ∂varyingBernoulliProductMeasure p,
      coordinateIndicator i ω ∈ Set.Icc (0 : ℝ) 1 := by
  filter_upwards [] with ω
  cases h : ω i <;> simp [coordinateIndicator, h]

/-- Regrouping a mutually independent family along disjoint fibres preserves
independence of the resulting vector-valued random variables. -/
lemma iIndepFun_curry_of_uncurry {ι : Type*} {κ : ι → Type*}
    {Ω' : Type*} [MeasurableSpace Ω']
    {𝓧 : (i : ι) → κ i → Type*} {m𝓧 : ∀ i j, MeasurableSpace (𝓧 i j)}
    {P : Measure Ω'} {Y : (i : ι) → (j : κ i) → Ω' → 𝓧 i j}
    (mY : ∀ i j, Measurable (Y i j))
    (h : iIndepFun (fun (p : (i : ι) × κ i) ω ↦ Y p.1 p.2 ω) P) :
    iIndepFun (fun i ω ↦ (Y i · ω)) P := by
  let F : (p : (i : ι) × κ i) → Ω' → 𝓧 p.1 p.2 :=
    fun p ω ↦ Y p.1 p.2 ω
  have hP : IsProbabilityMeasure P := h.isProbabilityMeasure
  have : ∀ i j, IsProbabilityMeasure (P.map (Y i j)) :=
    fun i j ↦ Measure.isProbabilityMeasure_map (mY i j).aemeasurable
  have hmF : ∀ p, Measurable (F p) := fun p ↦ mY p.1 p.2
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]
  apply (MeasurableEquiv.piCurry 𝓧).symm.map_measurableEquiv_injective
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  change P.map (fun ω p ↦ F p ω) =
    (Measure.infinitePi fun i ↦ P.map (fun ω j ↦ Y i j ω)).map
      (MeasurableEquiv.piCurry 𝓧).symm
  rw [(iIndepFun_iff_map_fun_eq_infinitePi_map hmF).1 h]
  have h_group : ∀ i,
      P.map (fun ω j ↦ Y i j ω) =
        Measure.infinitePi (fun j ↦ P.map (Y i j)) := by
    intro i
    have hi : iIndepFun (Y i) P := by
      apply iIndepFun.precomp (g := fun j : κ i ↦ Sigma.mk i j) (f := F)
      · intro a b hab
        cases hab
        rfl
      · exact h
    exact (iIndepFun_iff_map_fun_eq_infinitePi_map (mY i)).1 hi
  simp_rw [h_group]
  simpa [F] using
    (Measure.infinitePi_map_piCurry_symm
      (fun i j ↦ P.map (Y i j))).symm

/-- Indicator that every Bernoulli coordinate in one finite fibre is true. -/
def blockIndicator {ι κ : Type*} {δ : ι → Type*}
    [∀ i, Fintype (δ i)] (coord : (i : ι) × δ i → κ)
    (i : ι) (ω : κ → Bool) : ℝ :=
  ∏ j : δ i, coordinateIndicator (coord ⟨i, j⟩) ω

lemma blockIndicator_measurable
    {ι κ : Type*} [Fintype κ] {δ : ι → Type*} [∀ i, Fintype (δ i)]
    (coord : (i : ι) × δ i → κ) (i : ι) :
    Measurable (blockIndicator coord i) := by
  exact Finset.measurable_fun_prod _ fun j _ ↦
    coordinateIndicator_measurable (coord ⟨i, j⟩)

lemma blockIndicator_iIndep
    {ι κ : Type*} [Fintype κ] {δ : ι → Type*} [∀ i, Fintype (δ i)]
    (p : Set.Icc (0 : ℝ) 1) (coord : (i : ι) × δ i → κ)
    (hcoord : Function.Injective coord) :
    iIndepFun (fun i ↦ blockIndicator coord i)
      (bernoulliProductMeasure (ι := κ) p) := by
  let Y : (i : ι) → δ i → (κ → Bool) → ℝ :=
    fun i j ↦ coordinateIndicator (coord ⟨i, j⟩)
  have hflat : iIndepFun (fun (s : (i : ι) × δ i) ↦ Y s.1 s.2)
      (bernoulliProductMeasure (ι := κ) p) := by
    exact iIndepFun.precomp hcoord (coordinateIndicator_iIndep p)
  have hgroup : iIndepFun (fun i ω ↦ (Y i · ω))
      (bernoulliProductMeasure (ι := κ) p) :=
    iIndepFun_curry_of_uncurry
      (fun i j ↦ coordinateIndicator_measurable (coord ⟨i, j⟩)) hflat
  have hprod := hgroup.comp (γ := fun _ ↦ ℝ)
    (mγ := fun _ ↦ Real.measurableSpace)
    (fun i x ↦ ∏ j : δ i, x j) (fun _ ↦ by fun_prop)
  change iIndepFun
    (fun i ω ↦ ∏ j : δ i, coordinateIndicator (coord ⟨i, j⟩) ω)
    (bernoulliProductMeasure (ι := κ) p)
  simpa [Function.comp_def, Y] using hprod

lemma integral_blockIndicator
    {ι κ : Type*} [Fintype κ] {δ : ι → Type*} [∀ i, Fintype (δ i)]
    (p : Set.Icc (0 : ℝ) 1) (coord : (i : ι) × δ i → κ)
    (hcoord : Function.Injective coord) (i : ι) :
    ∫ ω, blockIndicator coord i ω
      ∂bernoulliProductMeasure (ι := κ) p = (p : ℝ) ^ Fintype.card (δ i) := by
  let X : δ i → (κ → Bool) → ℝ :=
    fun j ↦ coordinateIndicator (coord ⟨i, j⟩)
  have hXi : iIndepFun X (bernoulliProductMeasure (ι := κ) p) := by
    apply iIndepFun.precomp
      (g := fun j : δ i ↦ coord ⟨i, j⟩)
      (f := fun k ↦ coordinateIndicator k)
    · intro a b hab
      exact eq_of_heq (Sigma.mk.inj_iff.mp (hcoord hab) |>.2)
    · exact coordinateIndicator_iIndep p
  rw [show blockIndicator coord i = fun ω ↦ ∏ j, X j ω by rfl]
  rw [hXi.integral_fun_prod_eq_prod_integral
    (fun j ↦ (coordinateIndicator_measurable (coord ⟨i, j⟩)).aestronglyMeasurable)]
  simp [X, integral_coordinateIndicator p]

lemma blockIndicator_mem_Icc
    {ι κ : Type*} [Fintype κ] {δ : ι → Type*} [∀ i, Fintype (δ i)]
    (p : Set.Icc (0 : ℝ) 1) (coord : (i : ι) × δ i → κ) (i : ι) :
    ∀ᵐ ω ∂bernoulliProductMeasure (ι := κ) p,
      blockIndicator coord i ω ∈ Set.Icc (0 : ℝ) 1 := by
  filter_upwards [] with ω
  simp only [blockIndicator]
  constructor
  · apply Finset.prod_nonneg
    intro j hj
    cases h : ω (coord ⟨i, j⟩) <;> simp [coordinateIndicator, h]
  · apply Finset.prod_le_one
    · intro j hj
      cases h : ω (coord ⟨i, j⟩) <;> simp [coordinateIndicator, h]
    · intro j hj
      cases h : ω (coord ⟨i, j⟩) <;> simp [coordinateIndicator, h]

lemma blockIndicator_zero_or_one
    {ι κ : Type*} [Fintype κ] {δ : ι → Type*} [∀ i, Fintype (δ i)]
    (coord : (i : ι) × δ i → κ) (i : ι) (ω : κ → Bool) :
    blockIndicator coord i ω = 0 ∨ blockIndicator coord i ω = 1 := by
  classical
  by_cases hall : ∀ j : δ i, ω (coord ⟨i, j⟩) = true
  · right
    simp [blockIndicator, coordinateIndicator, hall]
  · push_neg at hall
    obtain ⟨j, hj⟩ := hall
    left
    unfold blockIndicator
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    cases h : ω (coord ⟨i, j⟩) <;> simp_all [coordinateIndicator]

private lemma mgf_zero_one
    {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω'} [IsProbabilityMeasure P]
    (X : Ω' → ℝ) (hX : Measurable X)
    (h01 : ∀ ω, X ω = 0 ∨ X ω = 1) (θ t : ℝ)
    (hmean : ∫ ω, X ω ∂P = θ) :
    mgf X P t = 1 + θ * (Real.exp t - 1) := by
  have hXint : Integrable X P := by
    apply Integrable.of_bound hX.aestronglyMeasurable 1
    filter_upwards [] with ω
    rcases h01 ω with h | h <;> simp [h]
  rw [mgf]
  calc
    (∫ ω, Real.exp (t * X ω) ∂P) =
        ∫ ω, (1 + X ω * (Real.exp t - 1)) ∂P := by
      apply integral_congr_ae
      filter_upwards [] with ω
      rcases h01 ω with h | h <;> simp [h]
    _ = (∫ _ω, (1 : ℝ) ∂P) + ∫ ω, X ω * (Real.exp t - 1) ∂P := by
      rw [integral_add (integrable_const _) (hXint.mul_const _)]
    _ = 1 + θ * (Real.exp t - 1) := by
      rw [integral_mul_const, hmean]
      simp

/-- Sum of a finite family of real random variables. -/
def finiteRandomSum {ι Ω' : Type*} [Fintype ι]
    (X : ι → Ω' → ℝ) (ω : Ω') : ℝ :=
  ∑ i, X i ω

private lemma finiteRandomSum_measurable
    {ι Ω' : Type*} [Fintype ι] [MeasurableSpace Ω']
    (X : ι → Ω' → ℝ) (hX : ∀ i, Measurable (X i)) :
    Measurable (finiteRandomSum X) := by
  exact Finset.measurable_sum _ fun i _ ↦ hX i

private lemma finiteRandomSum_nonneg_le_card
    {ι Ω' : Type*} [Fintype ι] (X : ι → Ω' → ℝ)
    (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1) (ω : Ω') :
    0 ≤ finiteRandomSum X ω ∧ finiteRandomSum X ω ≤ Fintype.card ι := by
  constructor
  · apply Finset.sum_nonneg
    intro i hi
    rcases h01 i ω with h | h <;> simp [finiteRandomSum, h]
  · calc
      finiteRandomSum X ω ≤ ∑ _i : ι, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        rcases h01 i ω with h | h <;> simp [finiteRandomSum, h]
      _ = Fintype.card ι := by simp

private lemma finiteRandomSum_exp_integrable
    {ι Ω' : Type*} [Fintype ι] [MeasurableSpace Ω']
    {P : Measure Ω'} [IsProbabilityMeasure P]
    (X : ι → Ω' → ℝ) (hX : ∀ i, Measurable (X i))
    (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1) (t : ℝ) :
    Integrable (fun ω ↦ Real.exp (t * finiteRandomSum X ω)) P := by
  apply Integrable.of_bound
    ((finiteRandomSum_measurable X hX).const_mul t).exp.aestronglyMeasurable
    (Real.exp (|t| * Fintype.card ι))
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hs := finiteRandomSum_nonneg_le_card X h01 ω
  have ht : t ≤ |t| := le_abs_self t
  have habs : 0 ≤ |t| := abs_nonneg t
  nlinarith

private lemma finiteRandomSum_mgf_le
    {ι Ω' : Type*} [Fintype ι] [MeasurableSpace Ω']
    {P : Measure Ω'} [IsProbabilityMeasure P]
    (X : ι → Ω' → ℝ) (hX : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X P)
    (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (θ : ι → ℝ) (hmean : ∀ i, ∫ ω, X i ω ∂P = θ i) (t : ℝ) :
    mgf (finiteRandomSum X) P t ≤
      Real.exp ((Real.exp t - 1) * ∑ i, θ i) := by
  have hsum : finiteRandomSum X = ∑ i, X i := by
    funext ω
    simp [finiteRandomSum]
  rw [hsum]
  calc
    mgf (∑ i, X i) P t =
        ∏ i, (1 + θ i * (Real.exp t - 1)) := by
      calc
        _ = ∏ i, mgf (X i) P t := by
          simpa using h_indep.mgf_sum hX Finset.univ (t := t)
        _ = _ := by
          apply Finset.prod_congr rfl
          intro i hi
          exact mgf_zero_one (X i) (hX i) (h01 i) (θ i) t (hmean i)
    _ ≤ ∏ i, Real.exp (θ i * (Real.exp t - 1)) := by
      apply Finset.prod_le_prod
      · intro i hi
        rw [← mgf_zero_one (X i) (hX i) (h01 i) (θ i) t (hmean i)]
        exact mgf_nonneg
      · intro i hi
        simpa [add_comm] using Real.add_one_le_exp (θ i * (Real.exp t - 1))
    _ = Real.exp (∑ i, θ i * (Real.exp t - 1)) := by
      rw [← Real.exp_sum]
    _ = Real.exp ((Real.exp t - 1) * ∑ i, θ i) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem finiteRandomSum_lower_half
    {ι Ω' : Type*} [Fintype ι] [MeasurableSpace Ω']
    {P : Measure Ω'} [IsProbabilityMeasure P]
    (X : ι → Ω' → ℝ) (hX : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X P)
    (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (θ : ι → ℝ) (hmean : ∀ i, ∫ ω, X i ω ∂P = θ i)
    (hθ : ∀ i, 0 ≤ θ i) :
    P.real {ω | finiteRandomSum X ω ≤ (∑ i, θ i) / 2} ≤
      Real.exp (-(∑ i, θ i) / 10) := by
  let M : ℝ := ∑ i, θ i
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ ↦ hθ i
  have hexp : Real.exp (-1) ≤ (2 / 5 : ℝ) :=
    Real.exp_neg_one_lt_d9.le.trans (by norm_num)
  calc
    P.real {ω | finiteRandomSum X ω ≤ M / 2} ≤
        Real.exp (-(-1 : ℝ) * (M / 2)) *
          mgf (finiteRandomSum X) P (-1) :=
      measure_le_le_exp_mul_mgf (M / 2) (by norm_num)
        (finiteRandomSum_exp_integrable X hX h01 (-1))
    _ ≤ Real.exp (-(-1 : ℝ) * (M / 2)) *
        Real.exp ((Real.exp (-1) - 1) * M) := by
      exact mul_le_mul_of_nonneg_left
        (finiteRandomSum_mgf_le X hX h_indep h01 θ hmean (-1))
        (Real.exp_nonneg _)
    _ = Real.exp (-(-1 : ℝ) * (M / 2) +
        (Real.exp (-1) - 1) * M) := by rw [Real.exp_add]
    _ ≤ Real.exp (-M / 10) := by
      apply Real.exp_le_exp.mpr
      nlinarith

theorem finiteRandomSum_upper_twice
    {ι Ω' : Type*} [Fintype ι] [MeasurableSpace Ω']
    {P : Measure Ω'} [IsProbabilityMeasure P]
    (X : ι → Ω' → ℝ) (hX : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X P)
    (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (θ : ι → ℝ) (hmean : ∀ i, ∫ ω, X i ω ∂P = θ i)
    (hθ : ∀ i, 0 ≤ θ i) :
    P.real {ω | 2 * (∑ i, θ i) ≤ finiteRandomSum X ω} ≤
      Real.exp (-(∑ i, θ i) / 5) := by
  let M : ℝ := ∑ i, θ i
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ ↦ hθ i
  have hexp : Real.exp 1 ≤ (14 / 5 : ℝ) :=
    Real.exp_one_lt_d9.le.trans (by norm_num)
  calc
    P.real {ω | 2 * M ≤ finiteRandomSum X ω} ≤
        Real.exp (-(1 : ℝ) * (2 * M)) *
          mgf (finiteRandomSum X) P 1 :=
      measure_ge_le_exp_mul_mgf (2 * M) (by norm_num)
        (finiteRandomSum_exp_integrable X hX h01 1)
    _ ≤ Real.exp (-(1 : ℝ) * (2 * M)) *
        Real.exp ((Real.exp 1 - 1) * M) := by
      exact mul_le_mul_of_nonneg_left
        (finiteRandomSum_mgf_le X hX h_indep h01 θ hmean 1)
        (Real.exp_nonneg _)
    _ = Real.exp (-(1 : ℝ) * (2 * M) +
        (Real.exp 1 - 1) * M) := by rw [Real.exp_add]
    _ ≤ Real.exp (-M / 5) := by
      apply Real.exp_le_exp.mpr
      nlinarith

/-- A finite independent family of random variables in `[0,1]` satisfies
the standard one-sided Hoeffding estimate after centering. -/
theorem measure_centered_sum_ge_le
    (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i, (X i ω - μ[X i])} ≤
      Real.exp
        (-ε ^ 2 /
          (2 * ∑ _i ∈ (Finset.univ : Finset ι),
            (hoeffdingUnitVariance : ℝ))) := by
  let Y : ι → Ω → ℝ := fun i ω ↦ X i ω - μ[X i]
  have hYindep : iIndepFun Y μ := by
    have h := h_indep.comp (fun i x ↦ x - μ[X i]) (by
      intro i
      fun_prop)
    simpa [Y, Function.comp_def] using h
  have hsubG : ∀ i, HasSubgaussianMGF (Y i) hoeffdingUnitVariance μ := by
    intro i
    simpa [Y, hoeffdingUnitVariance] using hasSubgaussianMGF_of_mem_Icc
      (hX i).aemeasurable (hbound i)
  simpa [Y] using HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    (c := fun _ ↦ hoeffdingUnitVariance) hYindep
    (s := Finset.univ) (fun i _ ↦ hsubG i) hε

/-- Lower-tail companion, obtained by applying the same sub-Gaussian
estimate to the negatives of the centered variables. -/
theorem measure_centered_sum_le_neg_le
    (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ∑ i, (X i ω - μ[X i]) ≤ -ε} ≤
      Real.exp
        (-ε ^ 2 /
          (2 * ∑ _i ∈ (Finset.univ : Finset ι),
            (hoeffdingUnitVariance : ℝ))) := by
  let Y : ι → Ω → ℝ := fun i ω ↦ -(X i ω - μ[X i])
  have hcentered : iIndepFun (fun i ω ↦ X i ω - μ[X i]) μ := by
    have h := h_indep.comp (fun i x ↦ x - μ[X i]) (by
      intro i
      fun_prop)
    simpa [Function.comp_def] using h
  have hYindep : iIndepFun Y μ := by
    have h := hcentered.comp (fun _ x ↦ -x) (by
      intro i
      fun_prop)
    simpa [Y, Function.comp_def] using h
  have hsubG : ∀ i, HasSubgaussianMGF (Y i) hoeffdingUnitVariance μ := by
    intro i
    have h := hasSubgaussianMGF_of_mem_Icc
      (hX i).aemeasurable (hbound i)
    have hcenter : HasSubgaussianMGF
        (fun ω ↦ X i ω - μ[X i]) hoeffdingUnitVariance μ := by
      simpa [hoeffdingUnitVariance] using h
    exact hcenter.neg.congr (ae_of_all _ fun ω ↦ by simp [Y])
  have htail := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    (c := fun _ ↦ hoeffdingUnitVariance) hYindep
    (s := Finset.univ) (fun i _ ↦ hsubG i) hε
  have hset :
      {ω | ∑ i, (X i ω - μ[X i]) ≤ -ε} =
        {ω | ε ≤ ∑ i, Y i ω} := by
    ext ω
    change (∑ i, (X i ω - μ[X i]) ≤ -ε) ↔ ε ≤ ∑ i, Y i ω
    rw [show (∑ i, Y i ω) = -(∑ i, (X i ω - μ[X i])) by
      simp [Y]]
    constructor <;> intro h <;> linarith
  rw [hset]
  simpa using htail

/-! ## Finite amplification -/

/-- If every task fails on at most `B` samples, then `g` independent sample
slots suffice simultaneously for every task as soon as the elementary
union-bound inequality `|tasks| B^g < |Sample|^g` holds.  This is the exact
finite counting form of the colour-group amplification used after the
second-moment estimates. -/
theorem exists_amplified_cover
    {Sample Task : Type*} [Fintype Sample] [Nonempty Sample]
    [DecidableEq Sample] [DecidableEq Task]
    (tasks : Finset Task) (bad : Task → Finset Sample)
    (B g : ℕ)
    (hbad : ∀ z ∈ tasks, (bad z).card ≤ B)
    (hunion : tasks.card * B ^ g < Fintype.card Sample ^ g) :
    ∃ choice : Fin g → Sample,
      ∀ z ∈ tasks, ∃ i : Fin g, choice i ∉ bad z := by
  classical
  let failure (z : Task) : Finset (Fin g → Sample) :=
    Fintype.piFinset fun _ : Fin g ↦ bad z
  let allFailures : Finset (Fin g → Sample) :=
    tasks.biUnion failure
  have hfailureCard (z : Task) :
      (failure z).card = (bad z).card ^ g := by
    exact Fintype.card_piFinset_const (bad z) g
  have hfailureLe (z : Task) (hz : z ∈ tasks) :
      (failure z).card ≤ B ^ g := by
    rw [hfailureCard]
    exact Nat.pow_le_pow_left (hbad z hz) g
  have hallFailuresCard : allFailures.card ≤ tasks.card * B ^ g := by
    calc
      allFailures.card ≤ ∑ z ∈ tasks, (failure z).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _z ∈ tasks, B ^ g := by
        apply Finset.sum_le_sum
        intro z hz
        exact hfailureLe z hz
      _ = tasks.card * B ^ g := by simp
  have hallCard :
      (Finset.univ : Finset (Fin g → Sample)).card =
        Fintype.card Sample ^ g := by
    simp [Fintype.card_fun]
  have hproper : allFailures.card <
      (Finset.univ : Finset (Fin g → Sample)).card := by
    rw [hallCard]
    exact hallFailuresCard.trans_lt hunion
  obtain ⟨choice, _hchoice, hchoice⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hproper
  refine ⟨choice, ?_⟩
  intro z hz
  by_contra hnone
  push Not at hnone
  apply hchoice
  apply Finset.mem_biUnion.mpr
  refine ⟨z, hz, ?_⟩
  simpa [failure] using hnone

/-- Scaled form of finite amplification.  It is often substantially easier
to prove the second-moment estimate as `D * |bad z| ≤ E * |Sample|` than
to divide by `D` and manufacture a common natural-number upper bound.  The
displayed inequality `|tasks| E^g < D^g` is exactly the corresponding union
bound after `g` independent repetitions. -/
theorem exists_amplified_cover_of_scaled_bad
    {Sample Task : Type*} [Fintype Sample] [Nonempty Sample]
    [DecidableEq Sample] [DecidableEq Task]
    (tasks : Finset Task) (bad : Task → Finset Sample)
    (D E g : ℕ) (hD : 0 < D)
    (hbad : ∀ z ∈ tasks,
      D * (bad z).card ≤ E * Fintype.card Sample)
    (hunion : tasks.card * E ^ g < D ^ g) :
    ∃ choice : Fin g → Sample,
      ∀ z ∈ tasks, ∃ i : Fin g, choice i ∉ bad z := by
  classical
  let failure (z : Task) : Finset (Fin g → Sample) :=
    Fintype.piFinset fun _ : Fin g ↦ bad z
  let allFailures : Finset (Fin g → Sample) :=
    tasks.biUnion failure
  have hfailureCard (z : Task) :
      (failure z).card = (bad z).card ^ g := by
    exact Fintype.card_piFinset_const (bad z) g
  have hfailureScaled (z : Task) (hz : z ∈ tasks) :
      D ^ g * (failure z).card ≤
        E ^ g * Fintype.card Sample ^ g := by
    rw [hfailureCard, ← mul_pow, ← mul_pow]
    exact Nat.pow_le_pow_left (hbad z hz) g
  have hallFailuresScaled :
      D ^ g * allFailures.card ≤
        tasks.card * (E ^ g * Fintype.card Sample ^ g) := by
    calc
      D ^ g * allFailures.card ≤
          D ^ g * ∑ z ∈ tasks, (failure z).card :=
        Nat.mul_le_mul_left _ Finset.card_biUnion_le
      _ = ∑ z ∈ tasks, D ^ g * (failure z).card := by
        rw [Finset.mul_sum]
      _ ≤ ∑ _z ∈ tasks,
          E ^ g * Fintype.card Sample ^ g := by
        apply Finset.sum_le_sum
        intro z hz
        exact hfailureScaled z hz
      _ = tasks.card * (E ^ g * Fintype.card Sample ^ g) := by simp
  have hproperScaled :
      D ^ g * allFailures.card <
        D ^ g * Fintype.card Sample ^ g := by
    apply hallFailuresScaled.trans_lt
    calc
      tasks.card * (E ^ g * Fintype.card Sample ^ g) =
          (tasks.card * E ^ g) * Fintype.card Sample ^ g := by ring
      _ < D ^ g * Fintype.card Sample ^ g :=
        Nat.mul_lt_mul_of_pos_right hunion (by positivity)
  have hDpow : 0 < D ^ g := pow_pos hD _
  have hproper : allFailures.card < Fintype.card Sample ^ g :=
    (Nat.mul_lt_mul_left hDpow).mp (by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        hproperScaled)
  have hallCard :
      (Finset.univ : Finset (Fin g → Sample)).card =
        Fintype.card Sample ^ g := by
    simp [Fintype.card_fun]
  have hproper' : allFailures.card <
      (Finset.univ : Finset (Fin g → Sample)).card := by
    rw [hallCard]
    exact hproper
  obtain ⟨choice, _hchoice, hchoice⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hproper'
  refine ⟨choice, ?_⟩
  intro z hz
  by_contra hnone
  push Not at hnone
  apply hchoice
  apply Finset.mem_biUnion.mpr
  refine ⟨z, hz, ?_⟩
  change choice ∈ failure z
  simpa [failure] using hnone

/-! ## Finite second moments -/

/-- The unnormalised variance identity for an integer-valued function on a
finite sample space.  Writing the identity with the factor `samples.card`
keeps all later random-rotation estimates in exact integer arithmetic. -/
lemma centeredSquareSum_identity
    {Sample : Type*} [DecidableEq Sample]
    (samples : Finset Sample) (X : Sample → ℕ) :
    let T := ∑ ω ∈ samples, X ω
    ∑ ω ∈ samples,
        (((samples.card : ℤ) * X ω - T) ^ 2) =
      (samples.card : ℤ) ^ 2 * (∑ ω ∈ samples, (X ω : ℤ) ^ 2) -
        (samples.card : ℤ) * (T : ℤ) ^ 2 := by
  dsimp
  let s : ℤ := samples.card
  let T : ℤ := ∑ ω ∈ samples, (X ω : ℤ)
  have hT : T = ((∑ ω ∈ samples, X ω : ℕ) : ℤ) := by
    simp [T]
  have hsq : (∑ ω ∈ samples, s ^ 2 * (X ω : ℤ) ^ 2) =
      s ^ 2 * (∑ ω ∈ samples, (X ω : ℤ) ^ 2) := by
    rw [Finset.mul_sum]
  have hcross : (∑ ω ∈ samples, 2 * s * T * (X ω : ℤ)) =
      2 * s * T ^ 2 := by
    rw [← Finset.mul_sum]
    change 2 * s * T * T = 2 * s * T ^ 2
    ring
  have hconst : (∑ _ω ∈ samples, T ^ 2) = s * T ^ 2 := by
    simp [s]
  rw [← hT]
  change ∑ ω ∈ samples, (s * (X ω : ℤ) - T) ^ 2 =
    s ^ 2 * (∑ ω ∈ samples, (X ω : ℤ) ^ 2) - s * T ^ 2
  calc
    (∑ ω ∈ samples, (s * (X ω : ℤ) - T) ^ 2) =
        ∑ ω ∈ samples,
          (s ^ 2 * (X ω : ℤ) ^ 2 -
            2 * s * T * (X ω : ℤ) + T ^ 2) := by
      apply Finset.sum_congr rfl
      intro ω _hω
      ring
    _ = s ^ 2 * (∑ ω ∈ samples, (X ω : ℤ) ^ 2) -
        s * T ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        hsq, hcross, hconst]
      ring

/-- Every zero of a nonnegative finite random variable contributes the
square of the total mass to the unnormalised variance.  This is the exact
finite Chebyshev inequality used for the random rotations in Lemma 6.3. -/
theorem card_zeros_mul_totalSquare_le_varianceNumerator
    {Sample : Type*} [DecidableEq Sample]
    (samples : Finset Sample) (X : Sample → ℕ) :
    let zeros := samples.filter fun ω ↦ X ω = 0
    let T := ∑ ω ∈ samples, X ω
    (zeros.card : ℤ) * (T : ℤ) ^ 2 ≤
      (samples.card : ℤ) ^ 2 *
          (∑ ω ∈ samples, (X ω : ℤ) ^ 2) -
        (samples.card : ℤ) * (T : ℤ) ^ 2 := by
  classical
  dsimp
  let T : ℤ := ∑ τ ∈ samples, (X τ : ℤ)
  have hT : T = ((∑ τ ∈ samples, X τ : ℕ) : ℤ) := by
    simp [T]
  let Y : Sample → ℤ := fun ω ↦
    ((samples.card : ℤ) * (X ω : ℤ) - T) ^ 2
  have hnonneg : ∀ ω, 0 ≤ Y ω := fun ω ↦ sq_nonneg _
  have hzeros : ∑ ω ∈ samples.filter (fun ω ↦ X ω = 0), Y ω =
      ((samples.filter fun ω ↦ X ω = 0).card : ℤ) * T ^ 2 := by
    calc
      (∑ ω ∈ samples.filter (fun ω ↦ X ω = 0), Y ω) =
          ∑ _ω ∈ samples.filter (fun ω ↦ X ω = 0), T ^ 2 := by
        apply Finset.sum_congr rfl
        intro ω hω
        have hX : X ω = 0 := (Finset.mem_filter.mp hω).2
        simp [Y, hX]
      _ = ((samples.filter fun ω ↦ X ω = 0).card : ℤ) * T ^ 2 := by
        simp
  rw [← hT]
  calc
    (((samples.filter fun ω ↦ X ω = 0).card : ℤ) * T ^ 2) =
        ∑ ω ∈ samples.filter (fun ω ↦ X ω = 0), Y ω :=
      hzeros.symm
    _ ≤ ∑ ω ∈ samples, Y ω := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun _ _ _ ↦ hnonneg _)
    _ = (samples.card : ℤ) ^ 2 *
          (∑ ω ∈ samples, (X ω : ℤ) ^ 2) -
        (samples.card : ℤ) * T ^ 2 := by
      simpa [Y] using centeredSquareSum_identity samples X

/-- Number of candidate configurations that succeed at one finite sample. -/
def finiteSuccessCount
    {Candidate Sample : Type*} [DecidableEq Candidate]
    [DecidableEq Sample]
    (candidates : Finset Candidate) (success : Candidate → Finset Sample)
    (ω : Sample) : ℕ :=
  (candidates.filter fun c ↦ ω ∈ success c).card

/-- Double-counting incidences computes the first moment of a finite
success count. -/
lemma sum_finiteSuccessCount
    {Candidate Sample : Type*} [DecidableEq Candidate]
    [DecidableEq Sample]
    (candidates : Finset Candidate) (samples : Finset Sample)
    (success : Candidate → Finset Sample) :
    ∑ ω ∈ samples, finiteSuccessCount candidates success ω =
      ∑ c ∈ candidates,
        (samples.filter fun ω ↦ ω ∈ success c).card := by
  classical
  simp only [finiteSuccessCount]
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]

/-- Double-counting ordered pairs of successful candidates computes the
second moment. -/
lemma sum_finiteSuccessCount_sq
    {Candidate Sample : Type*} [DecidableEq Candidate]
    [DecidableEq Sample]
    (candidates : Finset Candidate) (samples : Finset Sample)
    (success : Candidate → Finset Sample) :
    ∑ ω ∈ samples, (finiteSuccessCount candidates success ω) ^ 2 =
      ∑ c ∈ candidates, ∑ d ∈ candidates,
        (samples.filter fun ω ↦
          ω ∈ success c ∧ ω ∈ success d).card := by
  classical
  have hpoint (ω : Sample) :
      (finiteSuccessCount candidates success ω) ^ 2 =
        ∑ c ∈ candidates, ∑ d ∈ candidates,
          if ω ∈ success c ∧ ω ∈ success d then 1 else 0 := by
    simp only [finiteSuccessCount, pow_two]
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c hc
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hc' : ω ∈ success c <;>
      by_cases hd' : ω ∈ success d <;> simp [hc', hd']
  calc
    (∑ ω ∈ samples, (finiteSuccessCount candidates success ω) ^ 2) =
        ∑ ω ∈ samples, ∑ c ∈ candidates, ∑ d ∈ candidates,
          if ω ∈ success c ∧ ω ∈ success d then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro ω _hω
      exact hpoint ω
    _ = ∑ c ∈ candidates, ∑ d ∈ candidates, ∑ ω ∈ samples,
          if ω ∈ success c ∧ ω ∈ success d then 1 else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _hc
      rw [Finset.sum_comm]
    _ = ∑ c ∈ candidates, ∑ d ∈ candidates,
        (samples.filter fun ω ↦
          ω ∈ success c ∧ ω ∈ success d).card := by
      simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Division-free Paley--Zygmund form of the finite second-moment method.
If `Q` bounds the ordered-pair second moment and
`D * |Sample| * Q ≤ E * T²`, then at most the fraction `E / D` of all
samples have zero successes.  This scaled conclusion composes directly
with `exists_amplified_cover_of_scaled_bad`. -/
theorem card_samples_with_no_success_scaled
    {Candidate Sample : Type*} [Fintype Sample]
    [DecidableEq Candidate] [DecidableEq Sample]
    (candidates : Finset Candidate) (success : Candidate → Finset Sample)
    (D E Q : ℕ)
    (hT : 0 < ∑ c ∈ candidates, (success c).card)
    (hQ : ∑ c ∈ candidates, ∑ d ∈ candidates,
        (success c ∩ success d).card ≤ Q)
    (hscale :
      D * Fintype.card Sample * Q ≤
        E * (∑ c ∈ candidates, (success c).card) ^ 2) :
    D * ((Finset.univ : Finset Sample).filter fun ω ↦
        finiteSuccessCount candidates success ω = 0).card ≤
      E * Fintype.card Sample := by
  classical
  let samples := (Finset.univ : Finset Sample)
  let X := finiteSuccessCount candidates success
  let T := ∑ c ∈ candidates, (success c).card
  let Z := (samples.filter fun ω ↦ X ω = 0).card
  let S := Fintype.card Sample
  have hfirst : ∑ ω ∈ samples, X ω = T := by
    rw [sum_finiteSuccessCount]
    simp [samples, T, X]
  have hsecondNat : ∑ ω ∈ samples, (X ω) ^ 2 ≤ Q := by
    rw [sum_finiteSuccessCount_sq]
    have hinter (c d : Candidate) :
        (samples.filter fun ω ↦
          ω ∈ success c ∧ ω ∈ success d) = success c ∩ success d := by
      ext ω
      simp [samples]
    simpa only [hinter] using hQ
  have hsecondZ :
      (∑ ω ∈ samples, (X ω : ℤ) ^ 2) ≤ (Q : ℤ) := by
    exact_mod_cast hsecondNat
  have hcheb := card_zeros_mul_totalSquare_le_varianceNumerator samples X
  dsimp only at hcheb
  rw [hfirst] at hcheb
  have hsamples : samples.card = S := by simp [samples, S]
  rw [hsamples] at hcheb
  have hpalZ : (Z : ℤ) * (T : ℤ) ^ 2 ≤
      (S : ℤ) ^ 2 * (Q : ℤ) := by
    calc
      (Z : ℤ) * (T : ℤ) ^ 2 ≤
          (S : ℤ) ^ 2 *
              (∑ ω ∈ samples, (X ω : ℤ) ^ 2) -
            (S : ℤ) * (T : ℤ) ^ 2 := by
        simpa [Z] using hcheb
      _ ≤ (S : ℤ) ^ 2 *
          (∑ ω ∈ samples, (X ω : ℤ) ^ 2) := by
        exact sub_le_self _ (mul_nonneg (by positivity) (sq_nonneg _))
      _ ≤ (S : ℤ) ^ 2 * (Q : ℤ) := by
        gcongr
  have hpal : Z * T ^ 2 ≤ S ^ 2 * Q := by
    exact_mod_cast hpalZ
  have hscaled : D * Z * T ^ 2 ≤ E * S * T ^ 2 := by
    calc
      D * Z * T ^ 2 = D * (Z * T ^ 2) := by ring
      _ ≤ D * (S ^ 2 * Q) := Nat.mul_le_mul_left _ hpal
      _ = S * (D * S * Q) := by ring
      _ ≤ S * (E * T ^ 2) := by
        apply Nat.mul_le_mul_left
        simpa [S, T] using hscale
      _ = E * S * T ^ 2 := by ring
  have hTpow : 0 < T ^ 2 := pow_pos (by simpa [T] using hT) _
  have hresult : D * Z ≤ E * S := by
    apply Nat.le_of_mul_le_mul_right (c := T ^ 2) ?_ hTpow
    simpa [Nat.mul_assoc] using hscaled
  simpa [Z, X, samples, S] using hresult

/-- Uniform-success specialization of
`card_samples_with_no_success_scaled`, with exceptional candidate partners
charged by the trivial one-event bound. -/
theorem card_samples_with_no_success_scaled_of_pair_bounds
    {Candidate Sample : Type*} [Fintype Sample]
    [DecidableEq Candidate] [DecidableEq Sample]
    (candidates : Finset Candidate) (success : Candidate → Finset Sample)
    (good : Candidate → Candidate → Prop) [DecidableRel good]
    (A G L D E : ℕ)
    (hcandidates : 0 < candidates.card) (hApos : 0 < A)
    (hcard : ∀ c ∈ candidates, (success c).card = A)
    (hgood : ∀ c ∈ candidates, ∀ d ∈ candidates, good c d →
      (success c ∩ success d).card ≤ G)
    (hexceptional : ∀ c ∈ candidates,
      (candidates.filter fun d ↦ ¬good c d).card ≤ L)
    (hscale :
      D * Fintype.card Sample *
          (candidates.card ^ 2 * G + candidates.card * L * A) ≤
        E * (candidates.card * A) ^ 2) :
    D * ((Finset.univ : Finset Sample).filter fun ω ↦
        finiteSuccessCount candidates success ω = 0).card ≤
      E * Fintype.card Sample := by
  classical
  let Q := candidates.card ^ 2 * G + candidates.card * L * A
  have hinterAny : ∀ c ∈ candidates, ∀ d ∈ candidates,
      (success c ∩ success d).card ≤ A := by
    intro c hc d hd
    exact (Finset.card_le_card Finset.inter_subset_left).trans_eq
      (hcard c hc)
  have hinner : ∀ c ∈ candidates,
      (∑ d ∈ candidates, (success c ∩ success d).card) ≤
        candidates.card * G + L * A := by
    intro c hc
    let goodSet := candidates.filter fun d ↦ good c d
    let badSet := candidates.filter fun d ↦ ¬good c d
    rw [show (∑ d ∈ candidates, (success c ∩ success d).card) =
        (∑ d ∈ goodSet, (success c ∩ success d).card) +
          ∑ d ∈ badSet, (success c ∩ success d).card by
      simpa [goodSet, badSet] using
        (Finset.sum_filter_add_sum_filter_not candidates
          (fun d ↦ good c d)
          (fun d ↦ (success c ∩ success d).card)).symm]
    apply Nat.add_le_add
    · calc
        (∑ d ∈ goodSet, (success c ∩ success d).card) ≤
            ∑ _d ∈ goodSet, G := by
          apply Finset.sum_le_sum
          intro d hd
          have hddata := Finset.mem_filter.mp hd
          exact hgood c hc d hddata.1 hddata.2
        _ = goodSet.card * G := by simp
        _ ≤ candidates.card * G :=
          Nat.mul_le_mul_right G
            (Finset.card_le_card (Finset.filter_subset _ _))
    · calc
        (∑ d ∈ badSet, (success c ∩ success d).card) ≤
            ∑ _d ∈ badSet, A := by
          apply Finset.sum_le_sum
          intro d hd
          exact hinterAny c hc d (Finset.mem_filter.mp hd).1
        _ = badSet.card * A := by simp
        _ ≤ L * A := Nat.mul_le_mul_right A (by
          simpa [badSet] using hexceptional c hc)
  have hQ : ∑ c ∈ candidates, ∑ d ∈ candidates,
      (success c ∩ success d).card ≤ Q := by
    calc
      (∑ c ∈ candidates, ∑ d ∈ candidates,
          (success c ∩ success d).card) ≤
          ∑ _c ∈ candidates, (candidates.card * G + L * A) := by
        apply Finset.sum_le_sum
        intro c hc
        exact hinner c hc
      _ = Q := by simp [Q, pow_two]; ring
  have hT : ∑ c ∈ candidates, (success c).card =
      candidates.card * A := by
    calc
      (∑ c ∈ candidates, (success c).card) =
          ∑ _c ∈ candidates, A := by
        apply Finset.sum_congr rfl
        intro c hc
        exact hcard c hc
      _ = candidates.card * A := by simp
  apply card_samples_with_no_success_scaled candidates success D E Q
  · rw [hT]
    positivity
  · exact hQ
  · simpa [Q, hT] using hscale

/-- Finite Paley--Zygmund inequality in the scaled form needed for
amplification.  If the second moment is at most `R` times the square of the
first moment (after normalization by the sample-space size), then at least
a `1/R` fraction of the samples have a success, equivalently
`R * |bad| ≤ (R-1) * |Sample|`. -/
theorem card_samples_with_no_success_paley_scaled
    {Candidate Sample : Type*} [Fintype Sample]
    [DecidableEq Candidate] [DecidableEq Sample]
    (candidates : Finset Candidate) (success : Candidate → Finset Sample)
    (R Q : ℕ) (hR : 0 < R)
    (hT : 0 < ∑ c ∈ candidates, (success c).card)
    (hQ : ∑ c ∈ candidates, ∑ d ∈ candidates,
        (success c ∩ success d).card ≤ Q)
    (hratio :
      Fintype.card Sample * Q ≤
        R * (∑ c ∈ candidates, (success c).card) ^ 2) :
    R * ((Finset.univ : Finset Sample).filter fun ω ↦
        finiteSuccessCount candidates success ω = 0).card ≤
      (R - 1) * Fintype.card Sample := by
  classical
  let samples := (Finset.univ : Finset Sample)
  let X := finiteSuccessCount candidates success
  let T := ∑ c ∈ candidates, (success c).card
  let good := samples.filter fun ω ↦ X ω ≠ 0
  let bad := samples.filter fun ω ↦ X ω = 0
  let S := Fintype.card Sample
  have hfirst : ∑ ω ∈ samples, X ω = T := by
    rw [sum_finiteSuccessCount]
    simp [samples, T, X]
  have hsumGood : ∑ ω ∈ good, X ω = T := by
    calc
      (∑ ω ∈ good, X ω) =
          (∑ ω ∈ good, X ω) + ∑ ω ∈ bad, X ω := by
        simp [bad]
      _ = ∑ ω ∈ samples, X ω := by
        simpa [good, bad] using
          (Finset.sum_filter_add_sum_filter_not samples
            (fun ω ↦ X ω ≠ 0) X)
      _ = T := hfirst
  have hsecondGood : ∑ ω ∈ good, (X ω) ^ 2 ≤ Q := by
    calc
      (∑ ω ∈ good, (X ω) ^ 2) ≤
          ∑ ω ∈ samples, (X ω) ^ 2 :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = ∑ c ∈ candidates, ∑ d ∈ candidates,
          (success c ∩ success d).card := by
        rw [sum_finiteSuccessCount_sq]
        apply Finset.sum_congr rfl
        intro c hc
        apply Finset.sum_congr rfl
        intro d hd
        congr 1
        ext ω
        simp [samples]
      _ ≤ Q := hQ
  have hcauchy : T ^ 2 ≤ good.card * Q := by
    calc
      T ^ 2 = (∑ ω ∈ good, X ω) ^ 2 := by rw [hsumGood]
      _ ≤ good.card * ∑ ω ∈ good, (X ω) ^ 2 :=
        sq_sum_le_card_mul_sum_sq
      _ ≤ good.card * Q := Nat.mul_le_mul_left _ hsecondGood
  have hQpos : 0 < Q := by
    by_contra hnot
    have hQzero : Q = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hQzero] at hcauchy
    have hTpos : 0 < T := by simpa [T] using hT
    have hTsq : 0 < T ^ 2 := pow_pos hTpos _
    omega
  have hgoodScaled : S ≤ R * good.card := by
    apply Nat.le_of_mul_le_mul_right (c := Q) ?_ hQpos
    calc
      S * Q ≤ R * T ^ 2 := by simpa [S, T] using hratio
      _ ≤ R * (good.card * Q) := Nat.mul_le_mul_left _ hcauchy
      _ = (R * good.card) * Q := by ring
  have hpartition : bad.card + good.card = S := by
    have := Finset.card_filter_add_card_filter_not
      (s := samples) (p := fun ω ↦ X ω = 0)
    have hsamples : samples.card = S := by simp [samples, S]
    simpa [bad, good, hsamples, eq_comm] using this
  have hplus : R * bad.card + S ≤ R * S := by
    calc
      R * bad.card + S ≤ R * bad.card + R * good.card :=
        Nat.add_le_add_left hgoodScaled _
      _ = R * S := by rw [← Nat.mul_add, hpartition]
  have hRdecomp : R - 1 + 1 = R := Nat.sub_add_cancel (by omega)
  have hgoal : R * bad.card ≤ (R - 1) * S := by
    apply Nat.le_of_add_le_add_right (b := S)
    calc
      R * bad.card + S ≤ R * S := hplus
      _ = (R - 1 + 1) * S := congrArg (fun t ↦ t * S) hRdecomp.symm
      _ = (R - 1) * S + S := by rw [Nat.add_mul, one_mul]
  simpa [bad, X, samples, S] using hgoal

/-- Pair-correlation specialization of the scaled finite
Paley--Zygmund inequality. -/
theorem card_samples_with_no_success_paley_scaled_of_pair_bounds
    {Candidate Sample : Type*} [Fintype Sample]
    [DecidableEq Candidate] [DecidableEq Sample]
    (candidates : Finset Candidate) (success : Candidate → Finset Sample)
    (good : Candidate → Candidate → Prop) [DecidableRel good]
    (A G L R : ℕ) (hR : 0 < R)
    (hcandidates : 0 < candidates.card) (hApos : 0 < A)
    (hcard : ∀ c ∈ candidates, (success c).card = A)
    (hgood : ∀ c ∈ candidates, ∀ d ∈ candidates, good c d →
      (success c ∩ success d).card ≤ G)
    (hexceptional : ∀ c ∈ candidates,
      (candidates.filter fun d ↦ ¬good c d).card ≤ L)
    (hratio :
      Fintype.card Sample *
          (candidates.card ^ 2 * G + candidates.card * L * A) ≤
        R * (candidates.card * A) ^ 2) :
    R * ((Finset.univ : Finset Sample).filter fun ω ↦
        finiteSuccessCount candidates success ω = 0).card ≤
      (R - 1) * Fintype.card Sample := by
  classical
  let Q := candidates.card ^ 2 * G + candidates.card * L * A
  have hinterAny : ∀ c ∈ candidates, ∀ d ∈ candidates,
      (success c ∩ success d).card ≤ A := by
    intro c hc d hd
    exact (Finset.card_le_card Finset.inter_subset_left).trans_eq
      (hcard c hc)
  have hinner : ∀ c ∈ candidates,
      (∑ d ∈ candidates, (success c ∩ success d).card) ≤
        candidates.card * G + L * A := by
    intro c hc
    let goodSet := candidates.filter fun d ↦ good c d
    let badSet := candidates.filter fun d ↦ ¬good c d
    rw [show (∑ d ∈ candidates, (success c ∩ success d).card) =
        (∑ d ∈ goodSet, (success c ∩ success d).card) +
          ∑ d ∈ badSet, (success c ∩ success d).card by
      simpa [goodSet, badSet] using
        (Finset.sum_filter_add_sum_filter_not candidates
          (fun d ↦ good c d)
          (fun d ↦ (success c ∩ success d).card)).symm]
    apply Nat.add_le_add
    · calc
        (∑ d ∈ goodSet, (success c ∩ success d).card) ≤
            ∑ _d ∈ goodSet, G := by
          apply Finset.sum_le_sum
          intro d hd
          have hddata := Finset.mem_filter.mp hd
          exact hgood c hc d hddata.1 hddata.2
        _ = goodSet.card * G := by simp
        _ ≤ candidates.card * G :=
          Nat.mul_le_mul_right G
            (Finset.card_le_card (Finset.filter_subset _ _))
    · calc
        (∑ d ∈ badSet, (success c ∩ success d).card) ≤
            ∑ _d ∈ badSet, A := by
          apply Finset.sum_le_sum
          intro d hd
          exact hinterAny c hc d (Finset.mem_filter.mp hd).1
        _ = badSet.card * A := by simp
        _ ≤ L * A := Nat.mul_le_mul_right A (by
          simpa [badSet] using hexceptional c hc)
  have hQ : ∑ c ∈ candidates, ∑ d ∈ candidates,
      (success c ∩ success d).card ≤ Q := by
    calc
      (∑ c ∈ candidates, ∑ d ∈ candidates,
          (success c ∩ success d).card) ≤
          ∑ _c ∈ candidates, (candidates.card * G + L * A) := by
        apply Finset.sum_le_sum
        intro c hc
        exact hinner c hc
      _ = Q := by simp [Q, pow_two]; ring
  have hT : ∑ c ∈ candidates, (success c).card =
      candidates.card * A := by
    calc
      (∑ c ∈ candidates, (success c).card) =
          ∑ _c ∈ candidates, A := by
        apply Finset.sum_congr rfl
        intro c hc
        exact hcard c hc
      _ = candidates.card * A := by simp
  apply card_samples_with_no_success_paley_scaled
    candidates success R Q hR
  · rw [hT]
    positivity
  · exact hQ
  · simpa [Q, hT] using hratio

/-- Elementary factorization used to discharge the scalar hypothesis of
the preceding Paley--Zygmund theorem.  `Cg` controls the normalized
general-position correlation, while `Ce` controls the exceptional-partner
term. -/
lemma pairMomentRatio_of_separate_bounds
    (S C A G L Cg Ce : ℕ)
    (hgood : S * G ≤ Cg * A ^ 2)
    (hexceptional : S * L ≤ Ce * C * A) :
    S * (C ^ 2 * G + C * L * A) ≤
      (Cg + Ce) * (C * A) ^ 2 := by
  calc
    S * (C ^ 2 * G + C * L * A) =
        C ^ 2 * (S * G) + C * A * (S * L) := by ring
    _ ≤ C ^ 2 * (Cg * A ^ 2) + C * A * (Ce * C * A) :=
      Nat.add_le_add
        (Nat.mul_le_mul_left _ hgood)
        (Nat.mul_le_mul_left _ hexceptional)
    _ = (Cg + Ce) * (C * A) ^ 2 := by ring

/-- Finite second-moment zero bound stated directly in terms of candidate
success sets.  This is the reusable counting form of Chebyshev used by the
rotation covering arguments. -/
theorem card_samples_with_no_success_le
    {Candidate Sample : Type*} [Fintype Sample]
    [DecidableEq Candidate] [DecidableEq Sample]
    (candidates : Finset Candidate) (success : Candidate → Finset Sample)
    (B : ℕ)
    (hT : 0 < ∑ c ∈ candidates, (success c).card)
    (hvariance :
      (Fintype.card Sample : ℤ) ^ 2 *
          (∑ c ∈ candidates, ∑ d ∈ candidates,
            ((success c ∩ success d).card : ℤ)) -
        (Fintype.card Sample : ℤ) *
          ((∑ c ∈ candidates, (success c).card : ℕ) : ℤ) ^ 2 ≤
        (B : ℤ) *
          ((∑ c ∈ candidates, (success c).card : ℕ) : ℤ) ^ 2) :
    ((Finset.univ : Finset Sample).filter fun ω ↦
      finiteSuccessCount candidates success ω = 0).card ≤ B := by
  classical
  let samples := (Finset.univ : Finset Sample)
  let X := finiteSuccessCount candidates success
  let Tn := ∑ c ∈ candidates, (success c).card
  let Qz := ∑ c ∈ candidates, ∑ d ∈ candidates,
    ((success c ∩ success d).card : ℤ)
  have hfirst : ∑ ω ∈ samples, X ω = Tn := by
    rw [sum_finiteSuccessCount]
    simp [samples, Tn, X]
  have hsecond : ∑ ω ∈ samples, (X ω : ℤ) ^ 2 = Qz := by
    have hnat := sum_finiteSuccessCount_sq candidates samples success
    have hinter (c d : Candidate) :
        (samples.filter fun ω ↦
          ω ∈ success c ∧ ω ∈ success d) = success c ∩ success d := by
      ext ω
      simp [samples]
    simp_rw [hinter] at hnat
    have hcast := congrArg (fun z : ℕ ↦ (z : ℤ)) hnat
    simpa [samples, X, Qz] using hcast
  have hcheb := card_zeros_mul_totalSquare_le_varianceNumerator samples X
  dsimp only at hcheb
  rw [hfirst, hsecond] at hcheb
  have hsampleCard : samples.card = Fintype.card Sample := by
    simp [samples]
  rw [hsampleCard] at hcheb
  have hbound :
      (((samples.filter fun ω ↦ X ω = 0).card : ℤ) * (Tn : ℤ) ^ 2) ≤
        (B : ℤ) * (Tn : ℤ) ^ 2 := hcheb.trans (by
          simpa [Tn, Qz] using hvariance)
  have hTz : (0 : ℤ) < (Tn : ℤ) := by exact_mod_cast hT
  have hcardz :
      ((samples.filter fun ω ↦ X ω = 0).card : ℤ) ≤ (B : ℤ) := by
    nlinarith [sq_pos_of_pos hTz]
  exact_mod_cast hcardz

/-- A constant first moment, a uniform good-pair intersection bound, and
at most `L` exceptional partners per candidate imply an explicit finite
second-moment failure bound. -/
theorem card_samples_with_no_success_le_of_pair_bounds
    {Candidate Sample : Type*} [Fintype Sample]
    [DecidableEq Candidate] [DecidableEq Sample]
    (candidates : Finset Candidate) (success : Candidate → Finset Sample)
    (good : Candidate → Candidate → Prop) [DecidableRel good]
    (A G L B : ℕ)
    (hcandidates : 0 < candidates.card) (hApos : 0 < A)
    (hcard : ∀ c ∈ candidates, (success c).card = A)
    (hgood : ∀ c ∈ candidates, ∀ d ∈ candidates, good c d →
      (success c ∩ success d).card ≤ G)
    (hexceptional : ∀ c ∈ candidates,
      (candidates.filter fun d ↦ ¬good c d).card ≤ L)
    (hvariance :
      (Fintype.card Sample : ℤ) ^ 2 *
          ((candidates.card ^ 2 * G +
            candidates.card * L * A : ℕ) : ℤ) -
        (Fintype.card Sample : ℤ) *
          ((candidates.card * A : ℕ) : ℤ) ^ 2 ≤
        (B : ℤ) * ((candidates.card * A : ℕ) : ℤ) ^ 2) :
    ((Finset.univ : Finset Sample).filter fun ω ↦
      finiteSuccessCount candidates success ω = 0).card ≤ B := by
  classical
  have hinterAny : ∀ c ∈ candidates, ∀ d ∈ candidates,
      (success c ∩ success d).card ≤ A := by
    intro c hc d hd
    exact (Finset.card_le_card Finset.inter_subset_left).trans_eq
      (hcard c hc)
  have hinner : ∀ c ∈ candidates,
      (∑ d ∈ candidates, (success c ∩ success d).card) ≤
        candidates.card * G + L * A := by
    intro c hc
    let goodSet := candidates.filter fun d ↦ good c d
    let badSet := candidates.filter fun d ↦ ¬good c d
    have hpartition :
        (∑ d ∈ candidates, (success c ∩ success d).card) =
          (∑ d ∈ goodSet, (success c ∩ success d).card) +
            ∑ d ∈ badSet, (success c ∩ success d).card := by
      simpa [goodSet, badSet] using
        (Finset.sum_filter_add_sum_filter_not candidates
          (fun d ↦ good c d)
          (fun d ↦ (success c ∩ success d).card)).symm
    rw [hpartition]
    apply Nat.add_le_add
    · calc
        (∑ d ∈ goodSet, (success c ∩ success d).card) ≤
            ∑ _d ∈ goodSet, G := by
          apply Finset.sum_le_sum
          intro d hd
          have hddata := Finset.mem_filter.mp hd
          exact hgood c hc d hddata.1 hddata.2
        _ = goodSet.card * G := by simp
        _ ≤ candidates.card * G := by
          exact Nat.mul_le_mul_right G
            (Finset.card_le_card (Finset.filter_subset _ _))
    · calc
        (∑ d ∈ badSet, (success c ∩ success d).card) ≤
            ∑ _d ∈ badSet, A := by
          apply Finset.sum_le_sum
          intro d hd
          exact hinterAny c hc d (Finset.mem_filter.mp hd).1
        _ = badSet.card * A := by simp
        _ ≤ L * A := by
          exact Nat.mul_le_mul_right A (by
            simpa [badSet] using hexceptional c hc)
  have hQnat :
      (∑ c ∈ candidates, ∑ d ∈ candidates,
        (success c ∩ success d).card) ≤
          candidates.card ^ 2 * G + candidates.card * L * A := by
    calc
      (∑ c ∈ candidates, ∑ d ∈ candidates,
          (success c ∩ success d).card) ≤
          ∑ _c ∈ candidates, (candidates.card * G + L * A) := by
        apply Finset.sum_le_sum
        intro c hc
        exact hinner c hc
      _ = candidates.card ^ 2 * G + candidates.card * L * A := by
        simp [pow_two]
        ring
  have hTsum : ∑ c ∈ candidates, (success c).card =
      candidates.card * A := by
    calc
      (∑ c ∈ candidates, (success c).card) =
          ∑ _c ∈ candidates, A := by
        apply Finset.sum_congr rfl
        intro c hc
        exact hcard c hc
      _ = candidates.card * A := by simp
  apply card_samples_with_no_success_le candidates success B
  · rw [hTsum]
    positivity
  · have hQz :
        (∑ c ∈ candidates, ∑ d ∈ candidates,
          ((success c ∩ success d).card : ℤ)) ≤
            ((candidates.card ^ 2 * G +
              candidates.card * L * A : ℕ) : ℤ) := by
      exact_mod_cast hQnat
    have hMnonneg : (0 : ℤ) ≤ (Fintype.card Sample : ℤ) ^ 2 :=
      sq_nonneg _
    rw [hTsum]
    calc
      (Fintype.card Sample : ℤ) ^ 2 *
            (∑ c ∈ candidates, ∑ d ∈ candidates,
              ((success c ∩ success d).card : ℤ)) -
          (Fintype.card Sample : ℤ) *
            (↑candidates.card * ↑A) ^ 2 ≤
          (Fintype.card Sample : ℤ) ^ 2 *
              ((candidates.card ^ 2 * G +
                candidates.card * L * A : ℕ) : ℤ) -
            (Fintype.card Sample : ℤ) *
              (↑candidates.card * ↑A) ^ 2 := by
        exact sub_le_sub_right
          (mul_le_mul_of_nonneg_left hQz hMnonneg) _
      _ ≤ (B : ℤ) * (↑candidates.card * ↑A) ^ 2 := by
        simpa using hvariance

end Erdos722.Probability
