/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos721.LocalChangSanders

/-!
# The sharp local Chang--Sanders controller

The controller in `LocalChangSanders` is sufficient for the qualitative
density increment, but its direct quantitative specialization asks for an
`L¹` translation error of order `2⁻ᵐ`, where `m` is the local entropy.  This
loses an exponential factor in the Bohr radius.  Sanders' sharp local Chang
argument instead smooths the ambient Bohr probability first and uses the
monotonicity of relative Riesz dissociativity under convolution.

This file develops that sharper argument.  The first section changes from a
uniform probability on a finite carrier to an arbitrary finite probability
weight and proves Sanders' convolution-monotonicity lemma exactly.
-/

namespace Erdos721

open AddChar Finset Fintype Function MeasureTheory RCLike Real
open scoped BigOperators ComplexConjugate ENNReal Indicator mu NNReal Pointwise

namespace CyclicSharpLocalChangSanders

variable {N : ℕ} [NeZero N]

open CyclicFourier CyclicLocalChang CyclicLocalRieszSmoothing

/-! ## Weighted relative dissociativity -/

/-- The integral of a real function against a finite real weight. -/
noncomputable def weightedMean (mu : ZMod N → ℝ)
    (f : ZMod N → ℝ) : ℝ :=
  ∑ x : ZMod N, mu x * f x

/-- Riesz dissociativity relative to an arbitrary finite weight.  The
probability and nonnegativity hypotheses on the weight are kept separate:
the definition itself is the precise inequality which is monotone under
convolution. -/
def WeightedLocallyDissociated (mu : ZMod N → ℝ)
    (Delta : Finset (ZMod N)) (K : ℝ) : Prop :=
  ∀ omega : ZMod N → ℂ, (∀ r ∈ Delta, ‖omega r‖ ≤ 1) →
    weightedMean mu (rieszProduct Delta omega) ≤ Real.exp K

lemma weightedMean_mu_eq_finsetMean
    (S : Finset (ZMod N)) (f : ZMod N → ℝ) :
    weightedMean (μ_[ℝ] S) f = finsetMean S f := by
  classical
  unfold weightedMean finsetMean
  simp only [mu_apply, mul_ite, mul_one, mul_zero]
  calc
    (∑ x : ZMod N, (if x ∈ S then (S.card : ℝ)⁻¹ else 0) * f x) =
        ∑ x ∈ S, (S.card : ℝ)⁻¹ * f x := by simp
    _ = (S.card : ℝ)⁻¹ * ∑ x ∈ S, f x := by
      rw [Finset.mul_sum]

lemma weightedLocallyDissociated_mu_iff
    (S Delta : Finset (ZMod N)) (K : ℝ) :
    WeightedLocallyDissociated (μ_[ℝ] S) Delta K ↔
      LocallyDissociated S Delta K := by
  simp only [WeightedLocallyDissociated, LocallyDissociated,
    weightedMean_mu_eq_finsetMean]

/-- Translating the argument of a Riesz product merely rotates every
coefficient by a unit complex number. -/
lemma rieszProduct_add
    (Delta : Finset (ZMod N)) (omega : ZMod N → ℂ)
    (y z : ZMod N) :
    rieszProduct Delta omega (y + z) =
      rieszProduct Delta
        (fun r ↦ omega r * CyclicBohr.character r z) y := by
  unfold rieszProduct
  apply Finset.prod_congr rfl
  intro r hr
  rw [CyclicBohr.character_add]
  congr 2
  ring

lemma norm_mul_character_le_one
    {Delta : Finset (ZMod N)} {omega : ZMod N → ℂ}
    (homega : ∀ r ∈ Delta, ‖omega r‖ ≤ 1)
    (z : ZMod N) :
    ∀ r ∈ Delta,
      ‖omega r * CyclicBohr.character r z‖ ≤ 1 := by
  intro r hr
  rw [norm_mul, CyclicBohr.norm_character, mul_one]
  exact homega r hr

/-- Convolution-monotonicity of relative dissociativity (Sanders, Lemma
6.1), with the same Riesz-product parameter. -/
theorem WeightedLocallyDissociated.ddconv_left
    {mu : ZMod N → ℝ} {Delta : Finset (ZMod N)} {K : ℝ}
    (hDelta : WeightedLocallyDissociated mu Delta K)
    (nu : ZMod N → ℝ) (hnu_nonneg : 0 ≤ nu)
    (hnu_sum : ∑ z : ZMod N, nu z = 1) :
    WeightedLocallyDissociated (nu ∗ᵈ mu) Delta K := by
  intro omega homega
  unfold weightedMean
  rw [sum_ddconv_mul]
  calc
    (∑ z : ZMod N, ∑ y : ZMod N,
        nu z * mu y * rieszProduct Delta omega (z + y)) =
        ∑ z : ZMod N, nu z *
          weightedMean mu (rieszProduct Delta
            (fun r ↦ omega r * CyclicBohr.character r z)) := by
      apply Finset.sum_congr rfl
      intro z hz
      unfold weightedMean
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      rw [add_comm z y, rieszProduct_add]
      ring
    _ ≤ ∑ z : ZMod N, nu z * Real.exp K := by
      apply Finset.sum_le_sum
      intro z hz
      exact mul_le_mul_of_nonneg_left
        (hDelta (fun r ↦ omega r * CyclicBohr.character r z)
          (norm_mul_character_le_one homega z)) (hnu_nonneg z)
    _ = Real.exp K := by
      rw [← Finset.sum_mul, hnu_sum, one_mul]

/-- Sanders' full monotonicity statement also permits increasing the
dissociativity parameter. -/
theorem WeightedLocallyDissociated.ddconv_left_mono
    {mu : ZMod N → ℝ} {Delta : Finset (ZMod N)} {K K' : ℝ}
    (hDelta : WeightedLocallyDissociated mu Delta K)
    (nu : ZMod N → ℝ) (hnu_nonneg : 0 ≤ nu)
    (hnu_sum : ∑ z : ZMod N, nu z = 1) (hKK' : K ≤ K') :
    WeightedLocallyDissociated (nu ∗ᵈ mu) Delta K' := by
  intro omega homega
  exact (hDelta.ddconv_left nu hnu_nonneg hnu_sum omega homega).trans
    (Real.exp_le_exp.mpr hKK')

/-! ## Monotonicity in the frequency set -/

lemma rieszProduct_subset
    {E Delta : Finset (ZMod N)} (hE : E ⊆ Delta)
    (omega : ZMod N → ℂ) (x : ZMod N) :
    rieszProduct E omega x =
      rieszProduct Delta (fun r ↦ if r ∈ E then omega r else 0) x := by
  unfold rieszProduct
  let omega' : ZMod N → ℂ := fun r ↦ if r ∈ E then omega r else 0
  calc
    (∏ r ∈ E, (1 + (omega r * CyclicBohr.character r x).re)) =
        ∏ r ∈ E, (1 + (omega' r * CyclicBohr.character r x).re) := by
      apply Finset.prod_congr rfl
      intro r hr
      simp [omega', hr]
    _ = ∏ r ∈ Delta,
        (1 + (omega' r * CyclicBohr.character r x).re) := by
      rw [Finset.prod_subset hE]
      intro r hrDelta hrE
      simp [omega', hrE]

theorem WeightedLocallyDissociated.subset
    {mu : ZMod N → ℝ} {E Delta : Finset (ZMod N)} {K : ℝ}
    (hE : E ⊆ Delta)
    (hDelta : WeightedLocallyDissociated mu Delta K) :
    WeightedLocallyDissociated mu E K := by
  intro omega homega
  let omega' : ZMod N → ℂ := fun r ↦ if r ∈ E then omega r else 0
  have homega' : ∀ r ∈ Delta, ‖omega' r‖ ≤ 1 := by
    intro r hr
    by_cases hrE : r ∈ E
    · simpa [omega', hrE] using homega r hrE
    · simp [omega', hrE]
  rw [show rieszProduct E omega = rieszProduct Delta omega' by
    funext x
    exact rieszProduct_subset hE omega x]
  exact hDelta omega' homega'

/-- The unweighted local definition inherits both parts of Sanders'
monotonicity lemma. -/
theorem LocallyDissociated.weighted_convolution_subset
    {S E Delta : Finset (ZMod N)} {K K' : ℝ}
    (hE : E ⊆ Delta) (hDelta : LocallyDissociated S Delta K)
    (nu : ZMod N → ℝ) (hnu_nonneg : 0 ≤ nu)
    (hnu_sum : ∑ z : ZMod N, nu z = 1) (hKK' : K ≤ K') :
    WeightedLocallyDissociated (nu ∗ᵈ μ_[ℝ] S) E K' := by
  apply WeightedLocallyDissociated.subset hE
  apply WeightedLocallyDissociated.ddconv_left_mono
    ((weightedLocallyDissociated_mu_iff S Delta K).2 hDelta)
      nu hnu_nonneg hnu_sum hKK'

/-! ## The graded maximal dissociated set -/

lemma weightedLocallyDissociated_empty
    (mu : ZMod N → ℝ) (hmu_sum : ∑ x : ZMod N, mu x = 1) :
    WeightedLocallyDissociated mu ∅ 0 := by
  intro omega homega
  simp [weightedMean, rieszProduct, hmu_sum]

lemma WeightedLocallyDissociated.mono_parameter
    {mu : ZMod N → ℝ} {Delta : Finset (ZMod N)} {K K' : ℝ}
    (hKK' : K ≤ K') (hDelta : WeightedLocallyDissociated mu Delta K) :
    WeightedLocallyDissociated mu Delta K' := by
  intro omega homega
  exact (hDelta omega homega).trans (Real.exp_le_exp.mpr hKK')

/-- The linearly increasing dissociativity allowance used in Sanders'
greedy construction. -/
noncomputable def gradedParameter (eta : ℝ) (k : ℕ)
    (Delta : Finset (ZMod N)) : ℝ :=
  (Delta.card : ℝ) * eta / (2 * (k + 1 : ℕ))

def GradedDissociated (mu : ZMod N → ℝ) (eta : ℝ) (k : ℕ)
    (Delta : Finset (ZMod N)) : Prop :=
  WeightedLocallyDissociated mu Delta (gradedParameter eta k Delta)

lemma gradedParameter_empty (eta : ℝ) (k : ℕ) :
    gradedParameter (N := N) eta k ∅ = 0 := by
  simp [gradedParameter]

lemma gradedParameter_eq_half_of_card_eq_succ
    {eta : ℝ} {k : ℕ} {Delta : Finset (ZMod N)}
    (hcard : Delta.card = k + 1) :
    gradedParameter eta k Delta = eta / 2 := by
  unfold gradedParameter
  rw [hcard]
  have hk : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  field_simp

/-- Finite graded maximality.  If every `eta / 2`-dissociated subset of
`Gamma` has at most `k` elements, this produces a set of at most `k`
frequencies which cannot be enlarged even after increasing the allowed
Riesz mass by the next grade. -/
theorem exists_graded_maximal_dissociated
    (mu : ZMod N → ℝ) (Gamma : Finset (ZMod N))
    {eta : ℝ} (heta : 0 ≤ eta) (k : ℕ)
    (hmu_sum : ∑ x : ZMod N, mu x = 1)
    (hEntropy : ∀ E : Finset (ZMod N), E ⊆ Gamma →
      WeightedLocallyDissociated mu E (eta / 2) → E.card ≤ k) :
    ∃ Lambda : Finset (ZMod N),
      Lambda ⊆ Gamma ∧
      Lambda.card ≤ k ∧
      GradedDissociated mu eta k Lambda ∧
      ∀ gamma ∈ Gamma \ Lambda,
        ¬ GradedDissociated mu eta k (insert gamma Lambda) := by
  classical
  let candidates : Finset (Finset (ZMod N)) :=
    Gamma.powerset.filter fun E ↦
      E.card ≤ k + 1 ∧ GradedDissociated mu eta k E
  have hcandidates : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset,
      Finset.empty_subset, Finset.card_empty, Nat.zero_le, true_and]
    unfold GradedDissociated
    rw [gradedParameter_empty]
    exact weightedLocallyDissociated_empty mu hmu_sum
  obtain ⟨Lambda, hLambdaMax⟩ := candidates.exists_maximal hcandidates
  have hLambdaMem : Lambda ∈ candidates := hLambdaMax.1
  have hLambdaData : Lambda ⊆ Gamma ∧ Lambda.card ≤ k + 1 ∧
      GradedDissociated mu eta k Lambda := by
    simpa only [candidates, Finset.mem_filter, Finset.mem_powerset] using
      hLambdaMem
  have hLambdaCard : Lambda.card ≤ k := by
    by_contra hnot
    have hcard : Lambda.card = k + 1 := by omega
    have hdiss : WeightedLocallyDissociated mu Lambda (eta / 2) := by
      unfold GradedDissociated at hLambdaData
      rw [gradedParameter_eq_half_of_card_eq_succ hcard] at hLambdaData
      exact hLambdaData.2.2
    exact (not_le_of_gt (by omega : k < Lambda.card))
      (hEntropy Lambda hLambdaData.1 hdiss)
  refine ⟨Lambda, hLambdaData.1, hLambdaCard, hLambdaData.2.2, ?_⟩
  intro gamma hgamma
  rw [Finset.mem_sdiff] at hgamma
  intro hinsert
  have hinsertMem : insert gamma Lambda ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.insert_subset hgamma.1 hLambdaData.1, ?_, hinsert⟩
    rw [Finset.card_insert_of_notMem hgamma.2]
    omega
  exact hLambdaMax.not_gt hinsertMem (Finset.ssubset_insert hgamma.2)

/-! ## Correlation forced by failure at the next grade -/

/-- The (unnormalized) complex integral used after a graded insertion
fails.  Here `mu` is a probability mass, so no ambient-cardinality factor
is required. -/
noncomputable def weightedRieszCorrelation
    (mu : ZMod N → ℝ) (Delta : Finset (ZMod N))
    (omega : ZMod N → ℂ) (gamma : ZMod N) : ℂ :=
  ∑ x : ZMod N,
    (mu x * rieszProduct Delta omega x : ℝ) *
      CyclicBohr.character gamma x

lemma rieszProduct_insert
    {Delta : Finset (ZMod N)} {gamma : ZMod N}
    (hgamma : gamma ∉ Delta) (omega : ZMod N → ℂ) (x : ZMod N) :
    rieszProduct (insert gamma Delta) omega x =
      rieszProduct Delta omega x *
        (1 + (omega gamma * CyclicBohr.character gamma x).re) := by
  simp [rieszProduct, hgamma, mul_comm]

lemma weightedMean_rieszProduct_insert
    (mu : ZMod N → ℝ) {Delta : Finset (ZMod N)} {gamma : ZMod N}
    (hgamma : gamma ∉ Delta) (omega : ZMod N → ℂ) :
    weightedMean mu (rieszProduct (insert gamma Delta) omega) =
      weightedMean mu (rieszProduct Delta omega) +
        (omega gamma *
          weightedRieszCorrelation mu Delta omega gamma).re := by
  unfold weightedMean weightedRieszCorrelation
  simp_rw [rieszProduct_insert hgamma]
  have hexpand :
      (fun x : ZMod N ↦ mu x *
        (rieszProduct Delta omega x *
          (1 + (omega gamma * CyclicBohr.character gamma x).re))) =
      fun x : ZMod N ↦
        mu x * rieszProduct Delta omega x +
          mu x * rieszProduct Delta omega x *
            (omega gamma * CyclicBohr.character gamma x).re := by
    funext x
    ring
  rw [hexpand, Finset.sum_add_distrib]
  congr 1
  calc
    (∑ x : ZMod N,
        mu x * rieszProduct Delta omega x *
          (omega gamma * CyclicBohr.character gamma x).re) =
        ∑ x : ZMod N,
          (omega gamma *
            ((mu x * rieszProduct Delta omega x : ℝ) *
              CyclicBohr.character gamma x)).re := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, mul_zero, add_zero, sub_zero]
      ring
    _ = (∑ x : ZMod N,
        omega gamma *
          ((mu x * rieszProduct Delta omega x : ℝ) *
            CyclicBohr.character gamma x)).re := by
      rw [Complex.re_sum]
    _ = (omega gamma *
        ∑ x : ZMod N,
          (mu x * rieszProduct Delta omega x : ℝ) *
            CyclicBohr.character gamma x).re := by
      rw [Finset.mul_sum]

lemma gradedParameter_insert
    {eta : ℝ} {k : ℕ} {Delta : Finset (ZMod N)} {gamma : ZMod N}
    (hgamma : gamma ∉ Delta) :
    gradedParameter eta k (insert gamma Delta) =
      gradedParameter eta k Delta + eta / (2 * (k + 1 : ℕ)) := by
  unfold gradedParameter
  rw [Finset.card_insert_of_notMem hgamma]
  push_cast
  have hk : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  field_simp

/-- The gap between two consecutive exponential grades is at least the
grade spacing itself. -/
lemma grade_le_exp_gap {K a : ℝ} (hK : 0 ≤ K) (ha : 0 ≤ a) :
    a ≤ Real.exp (K + a) - Real.exp K := by
  have hExpK : 1 ≤ Real.exp K := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hK
  have hExpA : 1 + a ≤ Real.exp a := by
    simpa only [add_comm] using Real.add_one_le_exp a
  calc
    a ≤ Real.exp K * a := by nlinarith
    _ ≤ Real.exp K * (Real.exp a - 1) := by
      gcongr
      linarith
    _ = Real.exp (K + a) - Real.exp K := by
      rw [Real.exp_add]
      ring

/-- If adjoining a frequency fails the next graded dissociativity bound,
then the old Riesz product has a quantitatively large correlation with that
frequency.  This is the exact finite form of the transition between lines
(6.3) and (6.4) in Sanders' proof. -/
theorem exists_large_weightedRieszCorrelation_of_not_insert
    (mu : ZMod N → ℝ) (Lambda : Finset (ZMod N))
    {gamma : ZMod N} (hgamma : gamma ∉ Lambda)
    {eta : ℝ} (heta : 0 ≤ eta) (k : ℕ)
    (hLambda : GradedDissociated mu eta k Lambda)
    (hfail : ¬ GradedDissociated mu eta k (insert gamma Lambda)) :
    ∃ omega : ZMod N → ℂ,
      (∀ r ∈ Lambda, ‖omega r‖ ≤ 1) ∧
      eta / (2 * (k + 1 : ℕ)) <
        ‖weightedRieszCorrelation mu Lambda omega gamma‖ := by
  unfold GradedDissociated WeightedLocallyDissociated at hfail
  push_neg at hfail
  obtain ⟨omega, homegaInsert, hbad⟩ := hfail
  have homega : ∀ r ∈ Lambda, ‖omega r‖ ≤ 1 := by
    intro r hr
    exact homegaInsert r (Finset.mem_insert_of_mem hr)
  refine ⟨omega, homega, ?_⟩
  let K := gradedParameter eta k Lambda
  let a := eta / (2 * (k + 1 : ℕ))
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hK : 0 ≤ K := by
    dsimp only [K, gradedParameter]
    positivity
  have hbase : weightedMean mu (rieszProduct Lambda omega) ≤ Real.exp K :=
    hLambda omega homega
  have hinsert : gradedParameter eta k (insert gamma Lambda) = K + a := by
    simpa only [K, a] using gradedParameter_insert (eta := eta) (k := k) hgamma
  rw [hinsert, weightedMean_rieszProduct_insert mu hgamma omega] at hbad
  have hgap : Real.exp (K + a) - Real.exp K <
      (omega gamma * weightedRieszCorrelation mu Lambda omega gamma).re := by
    linarith
  have hcorr :
      (omega gamma * weightedRieszCorrelation mu Lambda omega gamma).re ≤
        ‖weightedRieszCorrelation mu Lambda omega gamma‖ := by
    calc
      (omega gamma * weightedRieszCorrelation mu Lambda omega gamma).re ≤
          ‖omega gamma * weightedRieszCorrelation mu Lambda omega gamma‖ :=
        Complex.re_le_norm _
      _ = ‖omega gamma‖ *
          ‖weightedRieszCorrelation mu Lambda omega gamma‖ := norm_mul _ _
      _ ≤ 1 * ‖weightedRieszCorrelation mu Lambda omega gamma‖ := by
        gcongr
        exact homegaInsert gamma (Finset.mem_insert_self gamma Lambda)
      _ = _ := one_mul _
  exact (grade_le_exp_gap hK ha).trans_lt (hgap.trans_le hcorr)

/-! ## Fourier extraction from the smoothed Bohr probability -/

/-- The probability mass obtained by convolving `L` samples from `V` with
one sample from `S`. -/
noncomputable def smoothedProbabilityMass
    (V S : Finset (ZMod N)) (L : ℕ) : ZMod N → ℝ :=
  μ_[ℝ] V ∗ᵈ^ L ∗ᵈ μ_[ℝ] S

lemma uniformWeight_eq_nat_smul_mu (S : Finset (ZMod N)) :
    CyclicBohr.uniformWeight S = (N : ℝ) • μ_[ℝ] S := by
  funext x
  by_cases hx : x ∈ S
  · simp [CyclicBohr.uniformWeight, mu_apply, hx, smul_eq_mul]
    ring
  · simp [CyclicBohr.uniformWeight, mu_apply, hx]

lemma smoothedProbabilityWeight_eq_mass
    (V S : Finset (ZMod N)) (L : ℕ) (x : ZMod N) :
    CyclicLocalRieszSmoothing.smoothedProbabilityWeight V S L x =
      (((N : ℝ) * smoothedProbabilityMass V S L x : ℝ) : ℂ) := by
  rw [CyclicLocalRieszSmoothing.smoothedProbabilityWeight_eq_ofReal]
  congr 1
  rw [uniformWeight_eq_nat_smul_mu S, ddconv_smul]
  rfl

lemma smoothedProbabilityMass_nonneg
    (V S : Finset (ZMod N)) (L : ℕ) :
    0 ≤ smoothedProbabilityMass V S L := by
  unfold smoothedProbabilityMass
  exact ddconv_nonneg (iterConv_nonneg mu_nonneg) mu_nonneg

lemma sum_smoothedProbabilityMass
    {V S : Finset (ZMod N)} (hV : V.Nonempty) (hS : S.Nonempty)
    (L : ℕ) :
    ∑ x : ZMod N, smoothedProbabilityMass V S L x = 1 := by
  unfold smoothedProbabilityMass
  rw [sum_ddconv, sum_iterConv, sum_mu ℝ hV, sum_mu ℝ hS]
  simp

/-- The mass-form Riesz correlation is the negative-frequency Fourier
coefficient of the pointwise product of the smoothed probability density
and the Riesz product. -/
lemma weightedRieszCorrelation_smoothed_eq_fourier
    (V S Delta : Finset (ZMod N)) (L : ℕ)
    (omega : ZMod N → ℂ) (gamma : ZMod N) :
    weightedRieszCorrelation (smoothedProbabilityMass V S L)
        Delta omega gamma =
      CyclicFourier.fourier
        (fun x ↦
          CyclicLocalRieszSmoothing.smoothedProbabilityWeight V S L x *
            complexRieszProduct Delta omega x) (-gamma) := by
  rw [CyclicFourier.fourier_neg]
  unfold weightedRieszCorrelation CyclicFourier.average
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hsum :
      ∑ x : ZMod N,
          CyclicBohr.character gamma x *
            (CyclicLocalRieszSmoothing.smoothedProbabilityWeight V S L x *
              complexRieszProduct Delta omega x) =
        (N : ℂ) *
          ∑ x : ZMod N,
            ((smoothedProbabilityMass V S L x *
              rieszProduct Delta omega x : ℝ) : ℂ) *
                CyclicBohr.character gamma x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [smoothedProbabilityWeight_eq_mass]
    unfold complexRieszProduct
    push_cast
    ring
  rw [hsum]
  field_simp

/-- Fourier modulation by a cyclic character translates frequency. -/
lemma fourier_mul_character
    (f : ZMod N → ℂ) (a r : ZMod N) :
    CyclicFourier.fourier
        (fun x ↦ f x * CyclicBohr.character a x) r =
      CyclicFourier.fourier f (r - a) := by
  unfold CyclicFourier.fourier
  apply congrArg CyclicFourier.average
  funext x
  have hchar :
      (starRingEnd ℂ) (CyclicBohr.character r x) *
          CyclicBohr.character a x =
        (starRingEnd ℂ) (CyclicBohr.character (r - a) x) := by
    rw [show CyclicBohr.character r x =
      CyclicBohr.character ((r - a) + a) x by congr 2 <;> abel,
      CyclicBohr.character_add_index, map_mul]
    calc
      ((starRingEnd ℂ) (CyclicBohr.character (r - a) x) *
          (starRingEnd ℂ) (CyclicBohr.character a x)) *
          CyclicBohr.character a x =
        (starRingEnd ℂ) (CyclicBohr.character (r - a) x) *
          ((starRingEnd ℂ) (CyclicBohr.character a x) *
            CyclicBohr.character a x) := by ring
      _ = (starRingEnd ℂ) (CyclicBohr.character (r - a) x) := by
        rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
          CyclicBohr.norm_character]
        norm_num
  calc
    (starRingEnd ℂ) (CyclicBohr.character r x) *
        (f x * CyclicBohr.character a x) =
      ((starRingEnd ℂ) (CyclicBohr.character r x) *
        CyclicBohr.character a x) * f x := by ring
    _ = (starRingEnd ℂ) (CyclicBohr.character (r - a) x) * f x := by
      rw [hchar]

/-- If every smoothed Fourier coefficient on the relevant translate of the
signed span is small, then so is the Riesz correlation. -/
lemma norm_weightedRieszCorrelation_smoothed_le
    (V S Delta : Finset (ZMod N)) (L : ℕ)
    (omega : ZMod N → ℂ) (homega : ∀ r ∈ Delta, ‖omega r‖ ≤ 1)
    (gamma : ZMod N) {theta : ℝ} (htheta : 0 ≤ theta)
    (htail : ∀ t ∈ Delta.addSpan,
      ‖CyclicFourier.fourier
          (CyclicLocalRieszSmoothing.smoothedProbabilityWeight V S L)
          (-gamma - t)‖ ≤ theta) :
    ‖weightedRieszCorrelation (smoothedProbabilityMass V S L)
        Delta omega gamma‖ ≤ theta * 2 ^ Delta.card := by
  rw [weightedRieszCorrelation_smoothed_eq_fourier,
    CyclicLocalRieszSmoothing.fourier_pointwise_mul]
  calc
    ‖∑ s : ZMod N,
        CyclicFourier.fourier
            (CyclicLocalRieszSmoothing.smoothedProbabilityWeight V S L) s *
          CyclicFourier.fourier (complexRieszProduct Delta omega)
            (-gamma - s)‖ ≤
        ∑ s : ZMod N,
          ‖CyclicFourier.fourier
              (CyclicLocalRieszSmoothing.smoothedProbabilityWeight V S L) s *
            CyclicFourier.fourier (complexRieszProduct Delta omega)
              (-gamma - s)‖ := norm_sum_le _ _
    _ ≤ ∑ s : ZMod N, theta *
          ‖CyclicFourier.fourier (complexRieszProduct Delta omega)
            (-gamma - s)‖ := by
      apply Finset.sum_le_sum
      intro s hs
      by_cases hp : CyclicFourier.fourier
          (complexRieszProduct Delta omega) (-gamma - s) = 0
      · simp [hp, htheta]
      · have hspan : -gamma - s ∈ Delta.addSpan := by
          by_contra hnot
          exact hp (fourier_complexRieszProduct_eq_zero_of_not_mem_addSpan
            Delta omega hnot)
        have hsEq : -gamma - (-gamma - s) = s := by abel
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right
          (by simpa only [hsEq] using htail (-gamma - s) hspan)
          (norm_nonneg _)
    _ = theta * ∑ r : ZMod N,
          ‖CyclicFourier.fourier (complexRieszProduct Delta omega) r‖ := by
      have hshift :
          (∑ s : ZMod N,
            ‖CyclicFourier.fourier (complexRieszProduct Delta omega)
              (-gamma - s)‖) =
            ∑ r : ZMod N,
              ‖CyclicFourier.fourier
                (complexRieszProduct Delta omega) r‖ :=
        Fintype.sum_equiv (Equiv.subLeft (-gamma))
          (fun s : ZMod N ↦
            ‖CyclicFourier.fourier (complexRieszProduct Delta omega)
              (-gamma - s)‖)
          (fun r : ZMod N ↦
            ‖CyclicFourier.fourier (complexRieszProduct Delta omega) r‖)
          (fun _ ↦ rfl)
      simpa only [Finset.mul_sum] using
        congrArg (fun z : ℝ ↦ theta * z) hshift
    _ ≤ theta * 2 ^ Delta.card := by
      gcongr
      exact sum_norm_fourier_complexRieszProduct_le Delta omega homega

/-- A correlation larger than the Fourier `L¹` bound forces a coefficient
of the narrow smoothing set above `1/2` on the appropriate signed-span
translate. -/
theorem exists_large_narrowCoefficient_of_large_correlation
    (V S Delta : Finset (ZMod N)) (hV : V.Nonempty) (hS : S.Nonempty)
    (L : ℕ) (omega : ZMod N → ℂ)
    (homega : ∀ r ∈ Delta, ‖omega r‖ ≤ 1)
    (gamma : ZMod N) {a : ℝ} (ha : 0 ≤ a)
    (hnumeric : 2 ^ Delta.card * (1 / 2 : ℝ) ^ L ≤ a)
    (hcorr : a <
      ‖weightedRieszCorrelation (smoothedProbabilityMass V S L)
        Delta omega gamma‖) :
    ∃ t ∈ Delta.addSpan,
      1 / 2 <
        ‖CyclicFourier.fourier
          (CyclicSpectralSmoothing.probabilityWeight V) (-gamma - t)‖ := by
  by_contra hex
  push Not at hex
  have htail : ∀ t ∈ Delta.addSpan,
      ‖CyclicFourier.fourier
          (CyclicLocalRieszSmoothing.smoothedProbabilityWeight V S L)
          (-gamma - t)‖ ≤ (1 / 2 : ℝ) ^ L := by
    intro t ht
    rw [CyclicLocalRieszSmoothing.fourier_smoothedProbabilityWeight
      hV S L (-gamma - t), norm_mul, norm_pow]
    calc
      ‖CyclicFourier.fourier
          (CyclicSpectralSmoothing.probabilityWeight V) (-gamma - t)‖ ^ L *
          ‖CyclicFourier.fourier
            (CyclicSpectralSmoothing.probabilityWeight S) (-gamma - t)‖ ≤
        (1 / 2 : ℝ) ^ L * 1 := by
          exact mul_le_mul
            (pow_le_pow_left₀ (norm_nonneg _) (hex t ht) L)
            (CyclicSpectralSmoothing.norm_fourier_probabilityWeight_le_one
              hS (-gamma - t))
            (norm_nonneg _) (pow_nonneg (by norm_num) L)
      _ = (1 / 2 : ℝ) ^ L := mul_one _
  have hupper := norm_weightedRieszCorrelation_smoothed_le
    V S Delta L omega homega gamma (pow_nonneg (by norm_num) L) htail
  have hreorder : (1 / 2 : ℝ) ^ L * 2 ^ Delta.card =
      2 ^ Delta.card * (1 / 2 : ℝ) ^ L := by ring
  rw [hreorder] at hupper
  exact (not_lt_of_ge (hupper.trans hnumeric)) hcorr

/-! ## The sharp abstract local generator -/

lemma WeightedLocallyDissociated.of_pointwise_domination
    {mu nu : ZMod N → ℝ} {Delta : Finset (ZMod N)}
    {K K' c : ℝ} (hc : 0 ≤ c)
    (hdom : ∀ x, mu x ≤ c * nu x)
    (hnu : WeightedLocallyDissociated nu Delta K)
    (hscale : c * Real.exp K ≤ Real.exp K') :
    WeightedLocallyDissociated mu Delta K' := by
  intro omega homega
  have hp : ∀ x : ZMod N, 0 ≤ rieszProduct Delta omega x :=
    fun x ↦ rieszProduct_nonneg Delta omega homega x
  calc
    weightedMean mu (rieszProduct Delta omega) ≤
        weightedMean (fun x ↦ c * nu x) (rieszProduct Delta omega) := by
      unfold weightedMean
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_right (hdom x) (hp x)
    _ = c * weightedMean nu (rieszProduct Delta omega) := by
      unfold weightedMean
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ ≤ c * Real.exp K :=
      mul_le_mul_of_nonneg_left (hnu omega homega) hc
    _ ≤ Real.exp K' := hscale

lemma one_add_third_mul_exp_half_le_exp
    {eta : ℝ} (heta : 0 ≤ eta) :
    (1 + eta / 3) * Real.exp (eta / 2) ≤ Real.exp eta := by
  have hthird : 1 + eta / 3 ≤ Real.exp (eta / 3) := by
    simpa only [add_comm] using Real.add_one_le_exp (eta / 3)
  calc
    (1 + eta / 3) * Real.exp (eta / 2) ≤
        Real.exp (eta / 3) * Real.exp (eta / 2) := by
      gcongr
    _ = Real.exp (eta / 3 + eta / 2) := (Real.exp_add _ _).symm
    _ ≤ Real.exp eta := by
      apply Real.exp_le_exp.mpr
      linarith

/-- Sharp local Chang--Sanders in an abstract smoothed-carrier form.

The pointwise domination hypothesis is precisely what regularity supplies
for Sanders' measure
`beta_(1+L*rho) * beta_rho * ... * beta_rho`.  Unlike the older generator,
the only numerical smoothing condition is logarithmic in `k`: it asks that
`2^k * 2^-L` fit below one grade. -/
theorem exists_sharp_localChangSanders_generator
    (B X V S Gamma : Finset (ZMod N))
    (hX : X.Nonempty) (hXB : X ⊆ B)
    (hV : V.Nonempty) (hS : S.Nonempty)
    (L k : ℕ) {spectralEta dissEta : ℝ}
    (hspectralEta0 : 0 < spectralEta) (hspectralEta1 : spectralEta ≤ 1)
    (hdissEta : 0 ≤ dissEta)
    (hdom : ∀ x : ZMod N,
      μ_[ℝ] B x ≤
        (1 + dissEta / 3) * smoothedProbabilityMass V S L x)
    (hGamma : Gamma ⊆ CyclicChang.relativeLargeSpectrum X spectralEta)
    (hcutoff :
      2 * (Real.log ((B.card : ℝ) / X.card) + dissEta) /
          spectralEta ^ 2 < (k + 1 : ℕ))
    (hnumeric :
      2 ^ k * (1 / 2 : ℝ) ^ L ≤
        dissEta / (2 * (k + 1 : ℕ))) :
    ∃ Lambda : Finset (ZMod N),
      Lambda ⊆ Gamma ∧
      Lambda.card ≤ k ∧
      Gamma ⊆ Lambda.addSpan +
        (CyclicChang.relativeLargeSpectrum V (1 / 2) ∪
          -CyclicChang.relativeLargeSpectrum V (1 / 2)) := by
  let muPlus := smoothedProbabilityMass V S L
  have hmuPlusSum : ∑ x : ZMod N, muPlus x = 1 := by
    simpa only [muPlus] using sum_smoothedProbabilityMass hV hS L
  have hEntropy : ∀ E : Finset (ZMod N), E ⊆ Gamma →
      WeightedLocallyDissociated muPlus E (dissEta / 2) → E.card ≤ k := by
    intro E hEGamma hEdiss
    have hBweighted :
        WeightedLocallyDissociated (μ_[ℝ] B) E dissEta := by
      apply WeightedLocallyDissociated.of_pointwise_domination
        (show 0 ≤ 1 + dissEta / 3 by positivity)
        (by simpa only [muPlus] using hdom) hEdiss
      exact one_add_third_mul_exp_half_le_exp hdissEta
    have hBdiss : LocallyDissociated B E dissEta :=
      (weightedLocallyDissociated_mu_iff B E dissEta).1 hBweighted
    have hEspec : E ⊆ CyclicChang.relativeLargeSpectrum X spectralEta :=
      hEGamma.trans hGamma
    have hbound := locallyDissociated_card_bound X B hX hXB
      hspectralEta0 hspectralEta1 E hEspec hBdiss
    have hcardReal : (E.card : ℝ) < (k + 1 : ℕ) := hbound.trans_lt hcutoff
    have hcardNat : E.card < k + 1 := by exact_mod_cast hcardReal
    omega
  obtain ⟨Lambda, hLambdaGamma, hLambdaCard, hLambdaDiss, hmaximal⟩ :=
    exists_graded_maximal_dissociated muPlus Gamma hdissEta k
      hmuPlusSum hEntropy
  refine ⟨Lambda, hLambdaGamma, hLambdaCard, ?_⟩
  let Q := CyclicChang.relativeLargeSpectrum V (1 / 2)
  have hQzero : (0 : ZMod N) ∈ Q := by
    apply CyclicLocalChangSanders.zero_mem_relativeLargeSpectrum hV
    norm_num
  intro gamma hgammaGamma
  by_cases hgammaLambda : gamma ∈ Lambda
  · simpa only [add_zero] using
      Finset.add_mem_add (Finset.subset_addSpan hgammaLambda)
        (Finset.mem_union_left (-Q) hQzero)
  · have hfail : ¬ GradedDissociated muPlus dissEta k
        (insert gamma Lambda) :=
      hmaximal gamma (Finset.mem_sdiff.mpr ⟨hgammaGamma, hgammaLambda⟩)
    obtain ⟨omega, homega, hcorr⟩ :=
      exists_large_weightedRieszCorrelation_of_not_insert
        muPlus Lambda hgammaLambda hdissEta k hLambdaDiss hfail
    have hpowCard : (2 : ℝ) ^ Lambda.card ≤ 2 ^ k := by
      exact pow_le_pow_right₀ (by norm_num) hLambdaCard
    have hnumericLambda :
        2 ^ Lambda.card * (1 / 2 : ℝ) ^ L ≤
          dissEta / (2 * (k + 1 : ℕ)) := by
      exact (mul_le_mul_of_nonneg_right hpowCard
        (pow_nonneg (by norm_num) L)).trans hnumeric
    obtain ⟨t, htSpan, htLarge⟩ :=
      exists_large_narrowCoefficient_of_large_correlation
        V S Lambda hV hS L omega homega gamma
        (div_nonneg hdissEta (by positivity)) hnumericLambda
        (by simpa only [muPlus] using hcorr)
    let q : ZMod N := -gamma - t
    have hqQ : q ∈ Q := by
      rw [show Q = CyclicFourier.largeSpectrum
          (CyclicSpectralSmoothing.probabilityWeight V) (1 / 2) by
        exact (CyclicSpectralSmoothing.largeSpectrum_probabilityWeight_eq_relativeLargeSpectrum
          hV (1 / 2)).symm]
      rw [CyclicFourier.mem_largeSpectrum]
      exact htLarge.le
    have hnegT : -t ∈ Lambda.addSpan :=
      CyclicLocalChangSanders.neg_mem_addSpan htSpan
    have hnegQ : -q ∈ Q ∪ -Q := by
      exact Finset.mem_union_right Q (by simpa only [Finset.mem_neg] using
        ⟨q, hqQ, rfl⟩)
    have hdecomp : gamma = -t + -q := by
      dsimp only [q]
      abel
    rw [hdecomp]
    exact Finset.add_mem_add hnegT hnegQ

/-! ## Constructing Sanders' dominating smoothed Bohr probability -/

/-- Every sample contributing to the smoothing convolution stays in the
outer Bohr set.  Consequently the smoothed probability mass is exactly the
reciprocal outer cardinality at every point of the inner Bohr set. -/
lemma smoothedProbabilityMass_eq_inv_card_of_mem_dilate
    (H : CyclicBohr.Set N) {a rho : ℝ} (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (L : ℕ) {x : ZMod N} (hx : x ∈ H.dilate a) :
    smoothedProbabilityMass (H.dilate rho).carrier
        (H.dilate (a + (L : ℝ) * rho)).carrier L x =
      (((H.dilate (a + (L : ℝ) * rho)).carrier.card : ℝ)⁻¹) := by
  let V := (H.dilate rho).carrier
  let S := (H.dilate (a + (L : ℝ) * rho)).carrier
  have hV : V.Nonempty := (H.dilate rho).carrier_nonempty
  have hPi : (Fintype.piFinset fun _ : Fin L ↦ V).Nonempty :=
    Fintype.piFinset_nonempty.mpr fun _ ↦ hV
  unfold smoothedProbabilityMass
  rw [mu_iterConv_ddconv, Finset.expect_apply]
  calc
    ((Fintype.piFinset fun _ : Fin L ↦ V).expect fun u ↦
        (translate (∑ i, u i) (μ_[ℝ] S)) x) =
        (Fintype.piFinset fun _ : Fin L ↦ V).expect
          (fun _ ↦ (S.card : ℝ)⁻¹) := by
      apply Finset.expect_congr rfl
      intro u hu
      rw [translate_apply, mu_apply, if_pos]
      · simp
      · have huV : ∀ i, u i ∈ V := Fintype.mem_piFinset.mp hu
        have hsumSet : (∑ i, u i) ∈
            L • ((H.dilate rho).carrier : Set (ZMod N)) := by
          rw [Set.mem_nsmul]
          refine ⟨fun i ↦ ⟨u i, huV i⟩, ?_⟩
          rw [List.sum_ofFn]
        have hsum : (∑ i, u i) ∈ H.dilate ((L : ℝ) * rho) :=
          CyclicLocalRieszSmoothing.nsmul_dilate_subset H hrho L hsumSet
        exact CyclicBohr.Set.sub_mem_dilate ha
          (mul_nonneg (Nat.cast_nonneg L) hrho) hx hsum
    _ = (S.card : ℝ)⁻¹ := Finset.expect_const hPi _

/-- Cardinal regularity turns the exact inner value above into the
pointwise domination required by the sharp abstract generator. -/
lemma mu_dilate_le_mul_smoothedProbabilityMass
    (H : CyclicBohr.Set N) {a rho c : ℝ}
    (ha : 0 ≤ a) (hrho : 0 ≤ rho) (hc : 0 ≤ c) (L : ℕ)
    (hcard :
      ((H.dilate (a + (L : ℝ) * rho)).carrier.card : ℝ) ≤
        c * (H.dilate a).carrier.card) :
    ∀ x : ZMod N,
      μ_[ℝ] (H.dilate a).carrier x ≤
        c * smoothedProbabilityMass (H.dilate rho).carrier
          (H.dilate (a + (L : ℝ) * rho)).carrier L x := by
  intro x
  by_cases hx : x ∈ (H.dilate a).carrier
  · have hInnerCard : (0 : ℝ) < (H.dilate a).carrier.card := by
      exact_mod_cast (H.dilate a).carrier_nonempty.card_pos
    have hOuterCard :
        (0 : ℝ) < (H.dilate (a + (L : ℝ) * rho)).carrier.card := by
      exact_mod_cast
        (H.dilate (a + (L : ℝ) * rho)).carrier_nonempty.card_pos
    rw [mu_apply, if_pos hx,
      smoothedProbabilityMass_eq_inv_card_of_mem_dilate H ha hrho L
        (show x ∈ H.dilate a from hx)]
    simp only [mul_one]
    have hscaled :
        ((H.dilate (a + (L : ℝ) * rho)).carrier.card : ℝ) *
            ((H.dilate a).carrier.card : ℝ)⁻¹ ≤ c := by
      calc
        ((H.dilate (a + (L : ℝ) * rho)).carrier.card : ℝ) *
            ((H.dilate a).carrier.card : ℝ)⁻¹ ≤
          (c * (H.dilate a).carrier.card) *
            ((H.dilate a).carrier.card : ℝ)⁻¹ := by gcongr
        _ = c := by field_simp
    change ((H.dilate a).carrier.card : ℝ)⁻¹ ≤
      c / ((H.dilate (a + (L : ℝ) * rho)).carrier.card : ℝ)
    rw [le_div_iff₀ hOuterCard]
    simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hscaled
  · rw [mu_apply, if_neg hx]
    simpa only [mul_zero] using mul_nonneg hc
      (smoothedProbabilityMass_nonneg _ _ _ x)

/-! ## The logarithmic smoothing length -/

/-- A deliberately generous smoothing length.  It is linear in the entropy
cutoff, in contrast with the exponentially accurate translation scale used
by the elementary local controller. -/
noncomputable def sharpSmoothingLength (k : ℕ) : ℕ := 4 * (k + 1)

lemma two_mul_succ_le_two_pow_three_mul_add_four (k : ℕ) :
    2 * (k + 1) ≤ 2 ^ (3 * k + 4) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [show 3 * (k + 1) + 4 = (3 * k + 4) + 3 by omega, pow_add]
      norm_num
      omega

/-- The tail `2^k 2^-L` is smaller than one grade when
`L = 4(k+1)`. -/
lemma sharp_smoothing_numeric (k : ℕ) :
    (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ sharpSmoothingLength k ≤
      1 / (2 * (k + 1 : ℕ)) := by
  have hnat := two_mul_succ_le_two_pow_three_mul_add_four k
  have hcast : (2 * (k + 1 : ℕ) : ℝ) ≤ 2 ^ (3 * k + 4) := by
    exact_mod_cast hnat
  have hinv : (1 : ℝ) / 2 ^ (3 * k + 4) ≤
      1 / (2 * (k + 1 : ℕ)) :=
    one_div_le_one_div_of_le (by positivity) hcast
  rw [show sharpSmoothingLength k = k + (3 * k + 4) by
    simp only [sharpSmoothingLength]
    omega, pow_add]
  calc
    (2 : ℝ) ^ k * ((1 / 2 : ℝ) ^ k * (1 / 2 : ℝ) ^ (3 * k + 4)) =
        1 / 2 ^ (3 * k + 4) := by
      norm_num [div_pow]
    _ ≤ 1 / (2 * (k + 1 : ℕ)) := hinv

/-! ## A smoothing set contained in the narrow Bohr scale -/

/-- The exact inner value only uses that every smoothing sample lies in the
narrow Bohr scale.  This form lets that smoothing set itself be a regular
dilate, whose uniform probability has the translation stability needed to
annihilate the auxiliary spectrum. -/
lemma smoothedProbabilityMass_eq_inv_card_of_mem_dilate_of_subset
    (H : CyclicBohr.Set N) (V : Finset (ZMod N))
    {a rho : ℝ} (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hV : V.Nonempty) (hVsub : V ⊆ (H.dilate rho).carrier)
    (L : ℕ) {x : ZMod N} (hx : x ∈ H.dilate a) :
    smoothedProbabilityMass V
        (H.dilate (a + (L : ℝ) * rho)).carrier L x =
      (((H.dilate (a + (L : ℝ) * rho)).carrier.card : ℝ)⁻¹) := by
  let S := (H.dilate (a + (L : ℝ) * rho)).carrier
  have hPi : (Fintype.piFinset fun _ : Fin L ↦ V).Nonempty :=
    Fintype.piFinset_nonempty.mpr fun _ ↦ hV
  unfold smoothedProbabilityMass
  rw [mu_iterConv_ddconv, Finset.expect_apply]
  calc
    ((Fintype.piFinset fun _ : Fin L ↦ V).expect fun u ↦
        (translate (∑ i, u i) (μ_[ℝ] S)) x) =
        (Fintype.piFinset fun _ : Fin L ↦ V).expect
          (fun _ ↦ (S.card : ℝ)⁻¹) := by
      apply Finset.expect_congr rfl
      intro u hu
      rw [translate_apply, mu_apply, if_pos]
      · simp
      · have huV : ∀ i, u i ∈ V := Fintype.mem_piFinset.mp hu
        have hsumSet : (∑ i, u i) ∈
            L • ((H.dilate rho).carrier : Set (ZMod N)) := by
          rw [Set.mem_nsmul]
          refine ⟨fun i ↦ ⟨u i, hVsub (huV i)⟩, ?_⟩
          rw [List.sum_ofFn]
        have hsum : (∑ i, u i) ∈ H.dilate ((L : ℝ) * rho) :=
          CyclicLocalRieszSmoothing.nsmul_dilate_subset H hrho L hsumSet
        exact CyclicBohr.Set.sub_mem_dilate ha
          (mul_nonneg (Nat.cast_nonneg L) hrho) hx hsum
    _ = (S.card : ℝ)⁻¹ := Finset.expect_const hPi _

/-- Generalized cardinal-regularity domination with an arbitrary nonempty
smoothing set inside the narrow Bohr scale. -/
lemma mu_dilate_le_mul_smoothedProbabilityMass_of_subset
    (H : CyclicBohr.Set N) (V : Finset (ZMod N))
    {a rho c : ℝ} (ha : 0 ≤ a) (hrho : 0 ≤ rho) (hc : 0 ≤ c)
    (hV : V.Nonempty) (hVsub : V ⊆ (H.dilate rho).carrier) (L : ℕ)
    (hcard :
      ((H.dilate (a + (L : ℝ) * rho)).carrier.card : ℝ) ≤
        c * (H.dilate a).carrier.card) :
    ∀ x : ZMod N,
      μ_[ℝ] (H.dilate a).carrier x ≤
        c * smoothedProbabilityMass V
          (H.dilate (a + (L : ℝ) * rho)).carrier L x := by
  intro x
  by_cases hx : x ∈ (H.dilate a).carrier
  · have hInnerCard : (0 : ℝ) < (H.dilate a).carrier.card := by
      exact_mod_cast (H.dilate a).carrier_nonempty.card_pos
    have hOuterCard :
        (0 : ℝ) < (H.dilate (a + (L : ℝ) * rho)).carrier.card := by
      exact_mod_cast
        (H.dilate (a + (L : ℝ) * rho)).carrier_nonempty.card_pos
    rw [mu_apply, if_pos hx,
      smoothedProbabilityMass_eq_inv_card_of_mem_dilate_of_subset
        H V ha hrho hV hVsub L (show x ∈ H.dilate a from hx)]
    simp only [mul_one]
    have hscaled :
        ((H.dilate (a + (L : ℝ) * rho)).carrier.card : ℝ) *
            ((H.dilate a).carrier.card : ℝ)⁻¹ ≤ c := by
      calc
        ((H.dilate (a + (L : ℝ) * rho)).carrier.card : ℝ) *
            ((H.dilate a).carrier.card : ℝ)⁻¹ ≤
          (c * (H.dilate a).carrier.card) *
            ((H.dilate a).carrier.card : ℝ)⁻¹ := by gcongr
        _ = c := by field_simp
    change ((H.dilate a).carrier.card : ℝ)⁻¹ ≤
      c / ((H.dilate (a + (L : ℝ) * rho)).carrier.card : ℝ)
    rw [le_div_iff₀ hOuterCard]
    simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hscaled
  · rw [mu_apply, if_neg hx]
    simpa only [mul_zero] using mul_nonneg hc
      (smoothedProbabilityMass_nonneg _ _ _ x)

/-! ## The sharp Bohr spectral controller -/

/-- The radius produced by the sharp controller.  All entropy dependence is
polynomial: the factor `sharpSmoothingLength k` is linear in `k`. -/
noncomputable def sharpControllerRadius
    (H : CyclicBohr.Set N) (k ell : ℕ) (sigma : ℝ) : ℝ :=
  min sigma
    ((400 * (ell : ℝ) * (H.rank : ℝ))⁻¹ *
      (((2 / (sharpSmoothingLength k : ℝ)) *
        (400 * (H.rank : ℝ))⁻¹) * H.radius))

/-- The fully physical sharp local Chang--Sanders controller.

The carrier is the inner member `H_(t-delta)` of a regular pair.  The
smoothed measure uses `L = 4(k+1)` samples from a regular dilate inside
`H_(2 delta/L)`, so its auxiliary spectrum is controlled at a radius which
is inverse-polynomial in the entropy cutoff. -/
theorem exists_sharp_localSpectrum_controller_of_regularCarrier
    (H : CyclicBohr.Set N) (X : Finset (ZMod N)) (k ell : ℕ)
    {t delta spectralEta sigma : ℝ}
    (hHradius : 0 < H.radius) (hHrank : 0 < H.rank)
    (hell : 0 < ell)
    (htlow : 1 / 2 ≤ t) (hthigh : t ≤ 1)
    (hdeltaFormula : delta = (400 * (H.rank : ℝ))⁻¹)
    (hdelta : 0 < delta) (hdeltat : delta < t)
    (hregular :
      10 * (H.dilate (t + delta)).carrier.card ≤
        11 * (H.dilate (t - delta)).carrier.card)
    (hX : X.Nonempty)
    (hXsub : X ⊆ (H.dilate (t - delta)).carrier)
    (hspectralEta0 : 0 < spectralEta)
    (hspectralEta1 : spectralEta ≤ 1) (hsigma : 0 < sigma)
    (hcutoff :
      2 * (Real.log
          (((H.dilate (t - delta)).carrier.card : ℝ) / X.card) +
        Real.log 4) /
        spectralEta ^ 2 < (k + 1 : ℕ)) :
    ∃ C : CyclicBohr.Set N,
      C.rank ≤ H.rank + (k + 1) ∧
      H.frequencies ⊆ C.frequencies ∧
      C.radius = sharpControllerRadius H k ell sigma ∧
      0 < C.radius ∧
      ∀ r ∈ CyclicChang.relativeLargeSpectrum X spectralEta, ∀ x ∈ C,
        ‖1 - CyclicBohr.character r x‖ ≤
          (k + 1 : ℕ) * sigma + 2 / (5 * ell) := by
  let L := sharpSmoothingLength k
  have hLnat : 0 < L := by simp [L, sharpSmoothingLength]
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hLnat
  let a : ℝ := t - delta
  have ha : 0 < a := by simpa only [a] using sub_pos.mpr hdeltat
  let rho : ℝ := 2 * delta / L
  have hrho : 0 < rho := by
    dsimp only [rho]
    positivity
  have houterScale : a + (L : ℝ) * rho = t + delta := by
    dsimp only [a, rho]
    field_simp
    ring
  let Bnarrow : CyclicBohr.Set N := H.dilate rho
  have hBnarrowRadius : 0 < Bnarrow.radius := by
    dsimp only [Bnarrow]
    simp only [CyclicBohr.Set.radius_dilate, abs_of_pos hrho]
    positivity
  have hBnarrowRank : 0 < Bnarrow.rank := by
    simpa only [Bnarrow, CyclicBohr.Set.rank_dilate] using hHrank
  obtain ⟨v, xi, hvlow, hvhigh, hxiFormula, hxi, hxiv, hstableV⟩ :=
    CyclicBohr.exists_uniformWeight_translation_stable_dilate_fine
      Bnarrow ell hBnarrowRadius hBnarrowRank hell
  let V : Finset (ZMod N) := (Bnarrow.dilate v).carrier
  have hV : V.Nonempty := (Bnarrow.dilate v).carrier_nonempty
  have hVsub : V ⊆ (H.dilate rho).carrier := by
    have hmono := CyclicBohr.Set.dilate_mono Bnarrow
      (by linarith : 0 ≤ v) hvhigh
    simpa only [V, Bnarrow, CyclicBohr.carrier_dilate_one] using hmono
  have hregularReal :
      10 * ((H.dilate (t + delta)).carrier.card : ℝ) ≤
        11 * ((H.dilate (t - delta)).carrier.card : ℝ) := by
    exact_mod_cast hregular
  have hcard :
      ((H.dilate (a + (L : ℝ) * rho)).carrier.card : ℝ) ≤
        (4 / 3 : ℝ) * (H.dilate a).carrier.card := by
    rw [houterScale]
    dsimp only [a]
    have hinnerNonneg :
        (0 : ℝ) ≤ (H.dilate (t - delta)).carrier.card := by positivity
    nlinarith
  have hdom : ∀ x : ZMod N,
      μ_[ℝ] (H.dilate a).carrier x ≤
        (1 + (1 : ℝ) / 3) *
          smoothedProbabilityMass V
            (H.dilate (a + (L : ℝ) * rho)).carrier L x := by
    have hraw := mu_dilate_le_mul_smoothedProbabilityMass_of_subset
      H V ha.le hrho.le (by norm_num : (0 : ℝ) ≤ 4 / 3)
      hV hVsub L hcard
    convert hraw using 1 <;> norm_num
  let Gamma := CyclicChang.relativeLargeSpectrum X spectralEta
  have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    exact Real.exp_one_lt_d9.le.trans (by norm_num)
  have hcutoffOne :
      2 * (Real.log (((H.dilate a).carrier.card : ℝ) / X.card) + 1) /
          spectralEta ^ 2 < (k + 1 : ℕ) := by
    apply lt_of_le_of_lt _ (by simpa only [a] using hcutoff)
    gcongr
  obtain ⟨Lambda, hLambdaGamma, hLambdaCard, hspan⟩ :=
    exists_sharp_localChangSanders_generator
      (H.dilate a).carrier X V
      (H.dilate (a + (L : ℝ) * rho)).carrier Gamma
      hX (by simpa only [a] using hXsub) hV
      (H.dilate (a + (L : ℝ) * rho)).carrier_nonempty
      L k hspectralEta0 hspectralEta1 (by norm_num : (0 : ℝ) ≤ 1)
      hdom (by rfl)
      hcutoffOne
      (by simpa only [L] using sharp_smoothing_numeric k)
  let Q := CyclicChang.relativeLargeSpectrum V (1 / 2)
  let W : CyclicBohr.Set N := Bnarrow.dilate xi
  have hQcontrol : ∀ q ∈ Q ∪ -Q, ∀ x ∈ W,
      ‖1 - CyclicBohr.character q x‖ ≤ 2 / (5 * ell) := by
    intro q hq x hx
    have hbase (r : ZMod N) (hr : r ∈ Q) :
        ‖1 - CyclicBohr.character r x‖ ≤ 2 / (5 * ell) := by
      have hraw :=
        CyclicLocalChangSanders.norm_one_sub_character_le_of_mem_relativeLargeSpectrum
          V hV (by norm_num : (0 : ℝ) < 1 / 2) hr
          (hstableV x (by simpa only [W] using hx))
      convert hraw using 1 <;> field_simp
    rcases Finset.mem_union.mp hq with hq | hq
    · exact hbase q hq
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_neg.mp hq
      rw [CyclicBohr.Set.character_neg_index]
      calc
        ‖1 - (starRingEnd ℂ) (CyclicBohr.character r x)‖ =
            ‖1 - CyclicBohr.character r x‖ := by
          simpa using RCLike.norm_conj
            (1 - CyclicBohr.character r x)
        _ ≤ 2 / (5 * ell) := hbase r hr
  obtain ⟨C, hCrank, hWfreqC, hCradius, hCcontrol⟩ :=
    CyclicLocalChangSanders.exists_bohr_controlling_of_span_add_aux
      Gamma Q Lambda W (k + 1) hsigma.le
      (by omega) (by simpa only [Q] using hspan) hQcontrol
  refine ⟨C, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [W, Bnarrow, CyclicBohr.Set.rank_dilate] using hCrank
  · simpa only [W, Bnarrow, CyclicBohr.Set.frequencies_dilate] using hWfreqC
  · rw [hCradius]
    congr 1
    simp only [W, Bnarrow, CyclicBohr.Set.radius_dilate,
      abs_of_pos hxi, abs_of_pos hrho]
    rw [hxiFormula]
    simp only [Bnarrow, CyclicBohr.Set.rank_dilate]
    dsimp only [rho]
    rw [hdeltaFormula]
    dsimp only [L]
    ring
  · rw [hCradius]
    exact lt_min hsigma (by
      dsimp only [W]
      simp only [CyclicBohr.Set.radius_dilate, abs_of_pos hxi]
      positivity)
  · simpa only [Gamma] using hCcontrol

end CyclicSharpLocalChangSanders
end Erdos721
