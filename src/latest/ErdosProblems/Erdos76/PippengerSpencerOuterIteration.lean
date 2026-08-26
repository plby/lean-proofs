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
import ErdosProblems.Erdos76.PippengerSpencerBatchLLL
import ErdosProblems.Erdos76.PippengerSpencerInner
import ErdosProblems.Erdos76.PippengerSpencerInnerLocality
import ErdosProblems.Erdos76.PippengerSpencerInnerMarginal
import ErdosProblems.Erdos76.PippengerSpencerInnerSharpInterface
import ErdosProblems.Erdos76.PippengerSpencerParameters
import ErdosProblems.Erdos76.HypergraphGreedyColoring
import ErdosProblems.Erdos76.PippengerSpencerEdgeColoring
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Outer iteration for Pippenger--Spencer

The only probabilistic input in this file is the explicitly named
`SharpFixedLengthInnerGenerator` hypothesis.  It says that the fixed-length
inner algorithm has the sharp per-edge marginal and its advertised finite
coordinate support.  The hypothesis is not asserted here.

The rest of the file is finitary.  It groups independent inner generators
into a batch, applies McDiarmid and the finite local lemma simultaneously at
all vertices, iterates the resulting degree reduction, and greedily colours
the final residual hypergraph.
-/

open Finset Real
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

open PippengerSpencerEdgeColoring

namespace FiniteHypergraph

universe uV uE

variable {V : Type uV} {E : Type uE}
  [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Fixed-parameter form of the genuinely probabilistic inner-generator
input.  It is deliberately near-regular: a pointwise marginal of order
`1 / D` is not available under a maximum-degree hypothesis alone. -/
def FixedLengthInnerMarginalAt
    (k : ℕ) (zeta eta : ℝ) (L D₀ : ℕ) : Prop :=
  ∀ (V' : Type uV) (E' : Type uE)
      [DecidableEq V'] [Fintype E'] [DecidableEq E'],
    ∀ (H : FiniteHypergraph V' E') (D : ℕ),
      D₀ ≤ D → H.IsUniform k →
      (∀ v ∈ H.vertexSet,
        (1 - eta) * (D : ℝ) ≤ (H.edgeDegree v : ℝ)) →
      (∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) →
      (∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
        (H.edgePairDegree u v : ℝ) < eta * (D : ℝ)) →
      ∃ prob : E' → ℝ,
        (∀ e, 0 ≤ prob e) ∧ (∀ e, prob e ≤ 1) ∧
        ∀ e, (1 - zeta) / (D : ℝ) ≤ H.innerAcceptanceMass L prob e

/-- Sharp fixed-length inner marginal, isolated as the sole unproved
probabilistic hypothesis of the outer argument. -/
def SharpFixedLengthInnerMarginal : Prop :=
  ∀ k : ℕ, 0 < k → ∀ zeta : ℝ, 0 < zeta → zeta < 1 →
    ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧
      ∃ L D₀ : ℕ, 0 < D₀ ∧
        FixedLengthInnerMarginalAt.{0, 0} k zeta eta L D₀

/-- A matching is unchanged by the isolated-edge alteration. -/
lemma isolatedSample_eq_self_of_isMatching
    (H : FiniteHypergraph V E) {M : Finset E} (hM : H.IsMatching M) :
    H.isolatedSample M = M := by
  apply Subset.antisymm (H.isolatedSample_subset M)
  intro e he
  rw [isolatedSample, mem_filter]
  refine ⟨he, ?_⟩
  intro f hf hef
  exact hM he hf hef

/-- Probability mass of one complete fixed-length inner input. -/
def innerTrialMass (L : ℕ) (prob : E → ℝ) (X : Fin L → Finset E) : ℝ :=
  FiniteProduct.productMass (FiniteNibble.bernoulliMass univ prob) X

lemma innerTrialMass_nonneg (L : ℕ) {prob : E → ℝ}
    (hprob0 : ∀ e, 0 ≤ prob e) (hprob1 : ∀ e, prob e ≤ 1)
    (X : Fin L → Finset E) :
    0 ≤ innerTrialMass L prob X := by
  unfold innerTrialMass FiniteProduct.productMass
  exact prod_nonneg fun r _ ↦ FiniteNibble.bernoulliMass_nonneg
    (subset_univ (X r)) (fun e _ ↦ hprob0 e) (fun e _ ↦ hprob1 e)

lemma sum_innerTrialMass (L : ℕ) (prob : E → ℝ) :
    ∑ X : Fin L → Finset E, innerTrialMass L prob X = 1 := by
  change ∑ X : Fin L → Finset E,
      FiniteProduct.mass
        (fun _ : Fin L ↦ FiniteNibble.bernoulliMass univ prob) X = 1
  apply FiniteProduct.sum_mass
  intro r
  simpa using FiniteNibble.sum_bernoulliMass (univ : Finset E) prob

lemma innerAcceptanceMass_nonneg
    (H : FiniteHypergraph V E) (L : ℕ) {prob : E → ℝ}
    (hprob0 : ∀ e, 0 ≤ prob e) (hprob1 : ∀ e, prob e ≤ 1) (e : E) :
    0 ≤ H.innerAcceptanceMass L prob e := by
  unfold innerAcceptanceMass
  exact sum_nonneg fun X _ ↦ mul_nonneg (innerTrialMass_nonneg L hprob0 hprob1 X)
    (by split <;> norm_num)

lemma innerAcceptanceMass_le_one
    (H : FiniteHypergraph V E) (L : ℕ) {prob : E → ℝ}
    (hprob0 : ∀ e, 0 ≤ prob e) (hprob1 : ∀ e, prob e ≤ 1) (e : E) :
    H.innerAcceptanceMass L prob e ≤ 1 := by
  calc
    H.innerAcceptanceMass L prob e ≤
        ∑ X : Fin L → Finset E, innerTrialMass L prob X := by
      unfold innerAcceptanceMass innerTrialMass
      apply sum_le_sum
      intro X _
      have hm := innerTrialMass_nonneg L hprob0 hprob1 X
      split <;> simp_all [innerTrialMass]
    _ = 1 := sum_innerTrialMass L prob

/-- Residual degree after a batch of fixed-length inner matchings. -/
def innerBatchResidualDegree {J : Type*} [Fintype J]
    (H : FiniteHypergraph V E) {L : ℕ}
    (X : J → (Fin L → Finset E)) (v : V) : ℕ :=
  H.batchResidualDegree (fun j ↦ H.innerMatching (X j)) v

/-- Edges retained after a batch of fixed-length inner matchings. -/
def innerBatchResidualEdges {J : Type*} [Fintype J]
    (H : FiniteHypergraph V E) {L : ℕ}
    (X : J → (Fin L → Finset E)) : Finset E :=
  H.batchResidualEdges (fun j ↦ H.innerMatching (X j))

/-- The residual-degree indicator expansion for inner-generated colours. -/
lemma innerBatchResidualDegree_eq_sum_never_accepted
    {J : Type*} [Fintype J] [DecidableEq J]
    (H : FiniteHypergraph V E) {L : ℕ}
    (X : J → (Fin L → Finset E)) (v : V) :
    (H.innerBatchResidualDegree X v : ℝ) =
      ∑ e : E, if v ∈ H.support e ∧
          ∀ j : J, e ∉ H.innerMatching (X j) then 1 else 0 := by
  rw [innerBatchResidualDegree, H.batchResidualDegree_eq_sum_never_accepted]
  apply sum_congr rfl
  intro e _
  congr 1
  apply propext
  apply and_congr_right
  intro _
  apply forall_congr'
  intro j
  rw [H.isolatedSample_eq_self_of_isMatching (H.innerMatching_isMatching (X j))]

lemma sum_innerTrialMass_not_mem_innerMatching
    (H : FiniteHypergraph V E) (L : ℕ) {prob : E → ℝ}
    (e : E) :
    (∑ X : Fin L → Finset E, innerTrialMass L prob X *
        if e ∉ H.innerMatching X then 1 else 0) =
      1 - H.innerAcceptanceMass L prob e := by
  have hsum := sum_innerTrialMass (E := E) L prob
  calc
    (∑ X : Fin L → Finset E, innerTrialMass L prob X *
        if e ∉ H.innerMatching X then 1 else 0) =
        (∑ X : Fin L → Finset E, innerTrialMass L prob X) -
          ∑ X : Fin L → Finset E, innerTrialMass L prob X *
            if e ∈ H.innerMatching X then 1 else 0 := by
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro X _
      by_cases he : e ∈ H.innerMatching X <;> simp [he]
    _ = 1 - H.innerAcceptanceMass L prob e := by
      rw [hsum]
      rfl

lemma sum_product_innerTrialMass_never_accepted
    {J : Type*} [Fintype J] [DecidableEq J]
    (H : FiniteHypergraph V E) (L : ℕ) {prob : E → ℝ} (e : E) :
    (∑ X : J → (Fin L → Finset E),
        FiniteProduct.productMass (innerTrialMass L prob) X *
          if ∀ j, e ∉ H.innerMatching (X j) then 1 else 0) =
      (1 - H.innerAcceptanceMass L prob e) ^ Fintype.card J := by
  have hpoint (X : J → (Fin L → Finset E)) :
      FiniteProduct.productMass (innerTrialMass L prob) X *
          (if ∀ j, e ∉ H.innerMatching (X j) then 1 else 0) =
        ∏ j : J, (innerTrialMass L prob (X j) *
          if e ∉ H.innerMatching (X j) then 1 else 0) := by
    by_cases hall : ∀ j, e ∉ H.innerMatching (X j)
    · rw [if_pos hall]
      simp only [FiniteProduct.productMass, mul_one]
      apply prod_congr rfl
      intro j _
      simp [hall j]
    · rw [if_neg hall, mul_zero]
      push Not at hall
      obtain ⟨j, hj⟩ := hall
      symm
      apply prod_eq_zero (mem_univ j)
      simp [hj]
  calc
    _ = ∑ X : J → (Fin L → Finset E), ∏ j : J,
          (innerTrialMass L prob (X j) *
            if e ∉ H.innerMatching (X j) then 1 else 0) := by
      apply sum_congr rfl
      intro X _
      exact hpoint X
    _ = ∏ _j : J, ∑ Y : Fin L → Finset E,
          innerTrialMass L prob Y *
            if e ∉ H.innerMatching Y then 1 else 0 := by
      symm
      simpa using (Finset.prod_univ_sum
        (fun _j : J ↦ (univ : Finset (Fin L → Finset E)))
        (fun _j : J ↦ fun Y : Fin L → Finset E ↦
          innerTrialMass L prob Y * if e ∉ H.innerMatching Y then 1 else 0))
    _ = ∏ _j : J, (1 - H.innerAcceptanceMass L prob e) := by
      apply prod_congr rfl
      intro j _
      exact H.sum_innerTrialMass_not_mem_innerMatching L e
    _ = _ := by simp

/-- A per-edge inner marginal lower bound gives geometric decay of expected
residual degree across an outer batch. -/
lemma productExpectation_innerBatchResidualDegree_le
    {J : Type*} [Fintype J] [DecidableEq J]
    (H : FiniteHypergraph V E) {L : ℕ} {prob : E → ℝ}
    (hprob0 : ∀ e, 0 ≤ prob e) (hprob1 : ∀ e, prob e ≤ 1)
    {a : ℝ} (ha0 : 0 ≤ a)
    (haccept : ∀ e, a ≤ H.innerAcceptanceMass L prob e) (v : V) :
    FiniteProduct.productExpectation (innerTrialMass L prob)
        (fun X : J → (Fin L → Finset E) ↦
          (H.innerBatchResidualDegree X v : ℝ)) ≤
      (H.edgeDegree v : ℝ) * (1 - a) ^ Fintype.card J := by
  unfold FiniteProduct.productExpectation
  rw [show (∑ X : J → (Fin L → Finset E),
      FiniteProduct.productMass (innerTrialMass L prob) X *
        (H.innerBatchResidualDegree X v : ℝ)) =
      ∑ X : J → (Fin L → Finset E), ∑ e : E,
        FiniteProduct.productMass (innerTrialMass L prob) X *
          if v ∈ H.support e ∧ ∀ j, e ∉ H.innerMatching (X j) then 1 else 0 by
    apply sum_congr rfl
    intro X _
    rw [H.innerBatchResidualDegree_eq_sum_never_accepted]
    rw [mul_sum]]
  rw [sum_comm]
  calc
    (∑ e : E, ∑ X : J → (Fin L → Finset E),
        FiniteProduct.productMass (innerTrialMass L prob) X *
          if v ∈ H.support e ∧ ∀ j, e ∉ H.innerMatching (X j) then 1 else 0) =
        ∑ e : E, if v ∈ H.support e then
          (1 - H.innerAcceptanceMass L prob e) ^ Fintype.card J else 0 := by
      apply sum_congr rfl
      intro e _
      by_cases hev : v ∈ H.support e
      · rw [if_pos hev]
        simpa [hev] using H.sum_product_innerTrialMass_never_accepted (J := J) L e
      · simp [hev]
    _ ≤ ∑ e : E, if v ∈ H.support e then
          (1 - a) ^ Fintype.card J else 0 := by
      apply sum_le_sum
      intro e _
      by_cases hev : v ∈ H.support e
      · simp only [hev, if_true]
        exact pow_le_pow_left₀
          (sub_nonneg.mpr (H.innerAcceptanceMass_le_one L hprob0 hprob1 e))
          (sub_le_sub_left (haccept e) 1) _
      · simp [hev]
    _ = (H.edgeDegree v : ℝ) * (1 - a) ^ Fintype.card J := by
      rw [← sum_filter]
      simp only [sum_const, card_filter, nsmul_eq_mul]
      congr 1
      norm_cast
      simp [FiniteHypergraph.edgeDegree]

/-- A per-edge inner marginal upper bound gives the matching lower geometric
bound on the expected residual degree.  This is the second half needed to
keep the residual hypergraph near-regular throughout the outer iteration. -/
lemma productExpectation_innerBatchResidualDegree_ge
    {J : Type*} [Fintype J] [DecidableEq J]
    (H : FiniteHypergraph V E) {L : ℕ} {prob : E → ℝ}
    (hprob0 : ∀ e, 0 ≤ prob e) (hprob1 : ∀ e, prob e ≤ 1)
    {b : ℝ} (hb1 : b ≤ 1)
    (haccept : ∀ e, H.innerAcceptanceMass L prob e ≤ b) (v : V) :
    (H.edgeDegree v : ℝ) * (1 - b) ^ Fintype.card J ≤
      FiniteProduct.productExpectation (innerTrialMass L prob)
        (fun X : J → (Fin L → Finset E) ↦
          (H.innerBatchResidualDegree X v : ℝ)) := by
  unfold FiniteProduct.productExpectation
  rw [show (∑ X : J → (Fin L → Finset E),
      FiniteProduct.productMass (innerTrialMass L prob) X *
        (H.innerBatchResidualDegree X v : ℝ)) =
      ∑ X : J → (Fin L → Finset E), ∑ e : E,
        FiniteProduct.productMass (innerTrialMass L prob) X *
          if v ∈ H.support e ∧ ∀ j, e ∉ H.innerMatching (X j) then 1 else 0 by
    apply sum_congr rfl
    intro X _
    rw [H.innerBatchResidualDegree_eq_sum_never_accepted]
    rw [mul_sum]]
  rw [sum_comm]
  calc
    (H.edgeDegree v : ℝ) * (1 - b) ^ Fintype.card J =
        ∑ e : E, if v ∈ H.support e then
          (1 - b) ^ Fintype.card J else 0 := by
      rw [← sum_filter]
      simp only [sum_const, card_filter, nsmul_eq_mul]
      congr 1
      norm_cast
      simp [FiniteHypergraph.edgeDegree]
    _ ≤ ∑ e : E, if v ∈ H.support e then
          (1 - H.innerAcceptanceMass L prob e) ^ Fintype.card J else 0 := by
      apply sum_le_sum
      intro e _
      by_cases hev : v ∈ H.support e
      · simp only [hev, if_true]
        exact pow_le_pow_left₀ (sub_nonneg.mpr hb1)
          (sub_le_sub_left (haccept e) 1) _
      · simp [hev]
    _ = ∑ e : E, ∑ X : J → (Fin L → Finset E),
        FiniteProduct.productMass (innerTrialMass L prob) X *
          if v ∈ H.support e ∧ ∀ j, e ∉ H.innerMatching (X j) then 1 else 0 := by
      apply sum_congr rfl
      intro e _
      by_cases hev : v ∈ H.support e
      · rw [if_pos hev]
        simpa [hev] using
          (H.sum_product_innerTrialMass_never_accepted (J := J) L e).symm
      · simp [hev]

/-- Replacing one complete inner input changes an inner-batch residual degree
by at most one. -/
lemma abs_innerBatchResidualDegree_update_sub_le_one
    {J : Type*} [Fintype J] [DecidableEq J]
    (H : FiniteHypergraph V E) {L : ℕ}
    (X : J → (Fin L → Finset E)) (j : J)
    (Y : Fin L → Finset E) (v : V) :
    |(H.innerBatchResidualDegree (Function.update X j Y) v : ℝ) -
      (H.innerBatchResidualDegree X v : ℝ)| ≤ 1 := by
  have hfun :
      (fun i ↦ H.innerMatching ((Function.update X j Y) i)) =
        Function.update (fun i ↦ H.innerMatching (X i)) j
          (H.innerMatching Y) := by
    funext i
    by_cases hij : i = j
    · subst i
      simp
    · simp [Function.update, hij]
  unfold innerBatchResidualDegree
  rw [hfun]
  exact H.abs_batchResidualDegree_update_sub_le_one
    (fun i ↦ H.innerMatching (X i)) j (H.innerMatching Y) v

/-- McDiarmid upper tail for a batch of complete inner-generator colours. -/
theorem productUpperTailMass_innerBatchResidualDegree_threshold_le
    {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    (H : FiniteHypergraph V E) {L : ℕ} (v : V)
    (prob : E → ℝ)
    (hprob0 : ∀ e, 0 ≤ prob e) (hprob1 : ∀ e, prob e ≤ 1)
    {t B : ℝ} (ht : 0 ≤ t)
    (hB : FiniteProduct.productExpectation (innerTrialMass L prob)
        (fun X : J → (Fin L → Finset E) ↦
          (H.innerBatchResidualDegree X v : ℝ)) + t ≤ B) :
    FiniteProduct.productUpperTailMass (innerTrialMass L prob)
        (fun X : J → (Fin L → Finset E) ↦
          (H.innerBatchResidualDegree X v : ℝ)) B ≤
      Real.exp (-2 * t ^ 2 / (Fintype.card J : ℝ)) := by
  have hcard : (0 : ℝ) < Fintype.card J := by exact_mod_cast Fintype.card_pos
  let F : (J → (Fin L → Finset E)) → ℝ := fun X ↦
    (H.innerBatchResidualDegree X v : ℝ)
  have hmc : FiniteProduct.productUpperTailMass (innerTrialMass L prob) F
        (FiniteProduct.productExpectation (innerTrialMass L prob) F + t) ≤
      Real.exp (-2 * t ^ 2 / (Fintype.card J : ℝ)) := by
    simpa [F] using FiniteProduct.productUpperTailMass_le_mcdiarmid
      (J := J) (A := Fin L → Finset E)
      (innerTrialMass L prob)
      (fun X : J → (Fin L → Finset E) ↦
        (H.innerBatchResidualDegree X v : ℝ))
      (fun _ : J ↦ (1 : ℝ))
      (innerTrialMass_nonneg L hprob0 hprob1)
      (sum_innerTrialMass L prob)
      (fun j X Y ↦ H.abs_innerBatchResidualDegree_update_sub_le_one X j Y v)
      ht (by simpa using hcard)
  change FiniteProduct.productUpperTailMass (innerTrialMass L prob) F B ≤ _
  calc
    FiniteProduct.productUpperTailMass (innerTrialMass L prob) F B ≤
        FiniteProduct.productUpperTailMass (innerTrialMass L prob) F
          (FiniteProduct.productExpectation (innerTrialMass L prob) F + t) := by
      unfold FiniteProduct.productUpperTailMass
      apply sum_le_sum_of_subset_of_nonneg
      · intro X hX
        simp only [mem_filter, mem_univ, true_and] at hX ⊢
        exact hB.trans hX
      · intro X _ _
        unfold FiniteProduct.productMass
        exact prod_nonneg fun j _ ↦ innerTrialMass_nonneg L hprob0 hprob1 (X j)
    _ ≤ _ := hmc

/-- Two-sided McDiarmid estimate for a batch of complete inner-generator
trials, in the exact event-mass form used by the finite local lemma. -/
theorem eventMass_innerBatchResidualDegree_abs_sub_expectation_le
    {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    (H : FiniteHypergraph V E) {L : ℕ} (v : V)
    (prob : E → ℝ)
    (hprob0 : ∀ e, 0 ≤ prob e) (hprob1 : ∀ e, prob e ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) :
    FiniteLocalLemma.eventMass
        (FiniteProduct.productMass (innerTrialMass L prob))
        (fun X : J → (Fin L → Finset E) ↦
          t ≤ |(H.innerBatchResidualDegree X v : ℝ) -
            FiniteProduct.productExpectation (innerTrialMass L prob)
              (fun Y : J → (Fin L → Finset E) ↦
                (H.innerBatchResidualDegree Y v : ℝ))|) ≤
      2 * Real.exp (-2 * t ^ 2 / (Fintype.card J : ℝ)) := by
  have hcard : (0 : ℝ) < Fintype.card J := by exact_mod_cast Fintype.card_pos
  let F : (J → (Fin L → Finset E)) → ℝ := fun X ↦
    (H.innerBatchResidualDegree X v : ℝ)
  let w : (Fin L → Finset E) → ℝ := innerTrialMass L prob
  have hmass0 : ∀ X : J → (Fin L → Finset E),
      0 ≤ FiniteProduct.productMass w X := by
    intro X
    unfold FiniteProduct.productMass
    exact prod_nonneg fun j _ ↦ innerTrialMass_nonneg L hprob0 hprob1 (X j)
  have hu : FiniteProduct.productUpperTailMass w F
        (FiniteProduct.productExpectation w F + t) ≤
      Real.exp (-2 * t ^ 2 / (Fintype.card J : ℝ)) := by
    simpa [show (∑ _j : J, (1 : ℝ) ^ 2) = (Fintype.card J : ℝ) by simp]
      using FiniteProduct.productUpperTailMass_le_mcdiarmid
        (J := J) (A := Fin L → Finset E) w F (fun _ : J ↦ (1 : ℝ))
        (innerTrialMass_nonneg L hprob0 hprob1) (sum_innerTrialMass L prob)
        (fun j X Y ↦ H.abs_innerBatchResidualDegree_update_sub_le_one X j Y v)
        ht (by simpa using hcard)
  have hl : FiniteProduct.productLowerTailMass w F
        (FiniteProduct.productExpectation w F - t) ≤
      Real.exp (-2 * t ^ 2 / (Fintype.card J : ℝ)) := by
    simpa [show (∑ _j : J, (1 : ℝ) ^ 2) = (Fintype.card J : ℝ) by simp]
      using FiniteProduct.productLowerTailMass_le_mcdiarmid
        (J := J) (A := Fin L → Finset E) w F (fun _ : J ↦ (1 : ℝ))
        (innerTrialMass_nonneg L hprob0 hprob1) (sum_innerTrialMass L prob)
        (fun j X Y ↦ H.abs_innerBatchResidualDegree_update_sub_le_one X j Y v)
        ht (by simpa using hcard)
  change FiniteLocalLemma.eventMass (FiniteProduct.productMass w)
      (fun X ↦ t ≤ |F X - FiniteProduct.productExpectation w F|) ≤ _
  rw [FiniteLocalLemma.eventMass, ← Finset.sum_filter]
  calc
    (∑ X with t ≤ |F X - FiniteProduct.productExpectation w F|,
        FiniteProduct.productMass w X) ≤
        ∑ X, ((if FiniteProduct.productExpectation w F + t ≤ F X then
              FiniteProduct.productMass w X else 0) +
            if F X ≤ FiniteProduct.productExpectation w F - t then
              FiniteProduct.productMass w X else 0) := by
      rw [Finset.sum_filter]
      apply sum_le_sum
      intro X _
      by_cases hbad : t ≤ |F X - FiniteProduct.productExpectation w F|
      · rcases le_abs.mp hbad with hupper | hlower
        · have hupper' : FiniteProduct.productExpectation w F + t ≤ F X := by
            linarith
          simp only [hbad, hupper', if_true]
          split_ifs <;> simp [hmass0 X]
        · have hlower' : F X ≤ FiniteProduct.productExpectation w F - t := by
            linarith
          simp only [hbad, hlower', if_true]
          split_ifs <;> simp [hmass0 X]
      · simp only [hbad, if_false]
        split_ifs <;> simp [hmass0 X]
    _ =
        FiniteProduct.productUpperTailMass w F
            (FiniteProduct.productExpectation w F + t) +
          FiniteProduct.productLowerTailMass w F
            (FiniteProduct.productExpectation w F - t) := by
      rw [sum_add_distrib]
      simp only [FiniteProduct.productUpperTailMass,
        FiniteProduct.productLowerTailMass, ← Finset.sum_filter]
    _ ≤ Real.exp (-2 * t ^ 2 / (Fintype.card J : ℝ)) +
          Real.exp (-2 * t ^ 2 / (Fintype.card J : ℝ)) := add_le_add hu hl
    _ = 2 * Real.exp (-2 * t ^ 2 / (Fintype.card J : ℝ)) := by ring

/-! ### Local-lemma batching of fixed-length inner generators -/

/-- Flatten a batch of complete length-`L` inner inputs. -/
def flattenInnerBatch {J : Type*} [Fintype J] [DecidableEq J]
    {L : ℕ} (X : J → (Fin L → Finset E)) : Finset ((J × Fin L) × E) :=
  flattenBatch (Function.uncurry X)

@[simp] lemma mem_flattenInnerBatch
    {J : Type*} [Fintype J] [DecidableEq J]
    {L : ℕ} (X : J → (Fin L → Finset E)) (j : J) (i : Fin L) (e : E) :
    ((j, i), e) ∈ flattenInnerBatch X ↔ e ∈ X j i := by
  simp [flattenInnerBatch]

/-- Flattening complete inner inputs preserves their iterated product mass. -/
lemma bernoulliMass_flattenInnerBatch
    {J : Type*} [Fintype J] [DecidableEq J]
    {L : ℕ} (prob : E → ℝ) (X : J → (Fin L → Finset E)) :
    FiniteNibble.bernoulliMass univ
        (fun z : (J × Fin L) × E ↦ prob z.2) (flattenInnerBatch X) =
      FiniteProduct.productMass (innerTrialMass L prob) X := by
  rw [flattenInnerBatch, bernoulliMass_flattenBatch]
  unfold FiniteProduct.productMass innerTrialMass
  rw [Fintype.prod_prod_type]
  apply prod_congr rfl
  intro j _
  rfl

/-- Equivalence between nested inner batches and their flattened coordinate
subsets. -/
def innerBatchFinsetEquiv
    {J : Type*} [Fintype J] [DecidableEq J] {L : ℕ} :
    (J → (Fin L → Finset E)) ≃ Finset ((J × Fin L) × E) :=
  (Equiv.curry J (Fin L) (Finset E)).symm.trans batchFinsetEquiv

@[simp] lemma innerBatchFinsetEquiv_apply
    {J : Type*} [Fintype J] [DecidableEq J] {L : ℕ}
    (X : J → (Fin L → Finset E)) :
    innerBatchFinsetEquiv X = flattenInnerBatch X := rfl

/-- Residual degree computed directly from flattened complete inner inputs. -/
def flattenedInnerBatchResidualDegree
    {J : Type*} [Fintype J] (H : FiniteHypergraph V E) (L : ℕ)
    (Z : Finset ((J × Fin L) × E)) (v : V) : ℕ :=
  H.innerBatchResidualDegree (fun j i ↦ batchAt Z (j, i)) v

@[simp] lemma flattenedInnerBatchResidualDegree_flattenInnerBatch
    {J : Type*} [Fintype J] [DecidableEq J]
    (H : FiniteHypergraph V E) {L : ℕ}
    (X : J → (Fin L → Finset E)) (v : V) :
    H.flattenedInnerBatchResidualDegree L (flattenInnerBatch X) v =
      H.innerBatchResidualDegree X v := by
  unfold flattenedInnerBatchResidualDegree innerBatchResidualDegree
  congr 2
  funext j
  congr 1
  funext i
  ext e
  simp

/-- Coordinates capable of influencing an inner-batch residual-degree event
at `v`. -/
def innerBatchVertexInfluenceSupport
    {J : Type*} [Fintype J] (H : FiniteHypergraph V E) (L : ℕ) (v : V) :
    Finset ((J × Fin L) × E) :=
  (univ : Finset (J × Fin L)).product (H.vertexConflictBall (2 * L + 1) v)

@[simp] lemma mem_innerBatchVertexInfluenceSupport
    {J : Type*} [Fintype J]
    (H : FiniteHypergraph V E) (L : ℕ) (v : V) (z : (J × Fin L) × E) :
    z ∈ H.innerBatchVertexInfluenceSupport L v ↔
      z.2 ∈ H.vertexConflictBall (2 * L + 1) v := by
  simp [innerBatchVertexInfluenceSupport]

/-- Vertex dependency neighbourhood for length-`L` inner batches. -/
def innerBatchVertexDependency (H : FiniteHypergraph V E) (L : ℕ)
    (v : ↑H.vertexSet) : Finset ↑H.vertexSet :=
  (univ : Finset ↑H.vertexSet).filter fun w ↦
    v ≠ w ∧ ¬ Disjoint (H.vertexConflictBall (2 * L + 1) v.1)
      (H.vertexConflictBall (2 * L + 1) w.1)

@[simp] lemma mem_innerBatchVertexDependency
    (H : FiniteHypergraph V E) (L : ℕ) (v w : ↑H.vertexSet) :
    w ∈ H.innerBatchVertexDependency L v ↔
      v ≠ w ∧ ¬ Disjoint (H.vertexConflictBall (2 * L + 1) v.1)
        (H.vertexConflictBall (2 * L + 1) w.1) := by
  simp [innerBatchVertexDependency]

lemma innerBatchVertexDependency_card_le
    {H : FiniteHypergraph V E} {k D L : ℕ}
    (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (v : ↑H.vertexSet) :
    (H.innerBatchVertexDependency L v).card ≤
      (D * (k * D + 1) ^ (4 * L + 2)) * k := by
  let imageVertices : Finset V :=
    (H.innerBatchVertexDependency L v).image Subtype.val
  have hcard : imageVertices.card = (H.innerBatchVertexDependency L v).card :=
    card_image_of_injective _ Subtype.val_injective
  have hsub : imageVertices ⊆ H.vertexConflictBallVertices (4 * L + 2) v.1 := by
    intro w hw
    obtain ⟨w', hwDep, rfl⟩ := mem_image.mp hw
    have hoverlap := (H.mem_innerBatchVertexDependency L v w').mp hwDep |>.2
    have hmem := H.mem_vertexConflictBallVertices_of_overlap
      (2 * L + 1) v.1 w'.1 hoverlap
    simpa [show (2 * L + 1) + (2 * L + 1) = 4 * L + 2 by omega] using hmem
  rw [← hcard]
  exact (card_le_card hsub).trans
    (H.vertexConflictBallVertices_card_le hunif hdeg v.2 (4 * L + 2))

lemma innerBatchInfluence_contains_overlaps
    {J : Type*} [Fintype J]
    (H : FiniteHypergraph V E) (L : ℕ) :
    FiniteNibble.ContainsSupportOverlaps
      (fun v : ↑H.vertexSet ↦
        H.innerBatchVertexInfluenceSupport (J := J) L v.1)
      (H.innerBatchVertexDependency L) := by
  intro v w hvw hoverlap
  rw [H.mem_innerBatchVertexDependency]
  refine ⟨hvw, ?_⟩
  obtain ⟨z, hzv, hzw⟩ := not_disjoint_iff.mp hoverlap
  rw [H.mem_innerBatchVertexInfluenceSupport] at hzv hzw
  exact not_disjoint_iff.mpr ⟨z.2, hzv, hzw⟩

lemma mem_iff_of_innerBatch_agreesOn
    {J : Type*} [Fintype J]
    (H : FiniteHypergraph V E) (L : ℕ) (v : V)
    {Z T : Finset ((J × Fin L) × E)}
    (hZT : FiniteNibble.AgreesOn
      (H.innerBatchVertexInfluenceSupport (J := J) L v) Z T)
    {z : (J × Fin L) × E}
    (hz : z ∈ H.innerBatchVertexInfluenceSupport (J := J) L v) :
    z ∈ Z ↔ z ∈ T := by
  unfold FiniteNibble.AgreesOn at hZT
  have hmem := congrArg (fun S : Finset ((J × Fin L) × E) ↦ z ∈ S) hZT
  have hmem' : (z ∈ Z) = (z ∈ T) := by
    simpa only [mem_inter, hz, and_true] using hmem
  exact eq_iff_iff.mp hmem'

lemma innerMatching_slice_iff_of_agreesOn
    {J : Type*} [Fintype J]
    (H : FiniteHypergraph V E) (L : ℕ) (v : V)
    {Z T : Finset ((J × Fin L) × E)}
    (hZT : FiniteNibble.AgreesOn
      (H.innerBatchVertexInfluenceSupport (J := J) L v) Z T)
    (e : E) (hev : v ∈ H.support e) (j : J) :
    e ∈ H.innerMatching (fun i ↦ batchAt Z (j, i)) ↔
      e ∈ H.innerMatching (fun i ↦ batchAt T (j, i)) := by
  apply H.innerState_mem_iff_of_sample_agreement (le_refl L)
  intro i f hf
  simp only [mem_batchAt]
  apply H.mem_iff_of_innerBatch_agreesOn L v hZT
  rw [H.mem_innerBatchVertexInfluenceSupport]
  rw [H.mem_vertexConflictBall]
  exact ⟨e, hev, hf⟩

lemma innerBatchResidualDegree_eq_of_acceptance_iff
    {J : Type*} [Fintype J]
    (H : FiniteHypergraph V E) {L : ℕ}
    (X Y : J → (Fin L → Finset E)) (v : V)
    (haccept : ∀ (e : E), v ∈ H.support e → ∀ j : J,
      (e ∈ H.innerMatching (X j) ↔ e ∈ H.innerMatching (Y j))) :
    H.innerBatchResidualDegree X v = H.innerBatchResidualDegree Y v := by
  apply Nat.cast_injective (R := ℝ)
  rw [H.innerBatchResidualDegree_eq_sum_never_accepted,
    H.innerBatchResidualDegree_eq_sum_never_accepted]
  apply sum_congr rfl
  intro e _
  by_cases hev : v ∈ H.support e
  · have hall :
        (∀ j : J, e ∉ H.innerMatching (X j)) ↔
        (∀ j : J, e ∉ H.innerMatching (Y j)) := by
      apply forall_congr'
      intro j
      exact not_congr (haccept e hev j)
    by_cases hX : ∀ j : J, e ∉ H.innerMatching (X j)
    · have hY := hall.mp hX
      simp [hev, hX, hY]
    · have hY : ¬ ∀ j : J, e ∉ H.innerMatching (Y j) :=
        fun h ↦ hX (hall.mpr h)
      simp [hev, hX, hY]
  · simp [hev]

lemma flattenedInnerBatchResidualDegree_eq_of_agreesOn
    {J : Type*} [Fintype J]
    (H : FiniteHypergraph V E) (L : ℕ) (v : V)
    {Z T : Finset ((J × Fin L) × E)}
    (hZT : FiniteNibble.AgreesOn
      (H.innerBatchVertexInfluenceSupport (J := J) L v) Z T) :
    H.flattenedInnerBatchResidualDegree L Z v =
      H.flattenedInnerBatchResidualDegree L T v := by
  unfold flattenedInnerBatchResidualDegree
  apply H.innerBatchResidualDegree_eq_of_acceptance_iff
  intro e hev j
  exact H.innerMatching_slice_iff_of_agreesOn L v hZT e hev j

/-- The residual-degree threshold event is local in the explicit flattened
coordinate support. -/
lemma flattenedInnerResidualDegreeBad_eventDependsOn
    {J : Type*} [Fintype J]
    (H : FiniteHypergraph V E) (L : ℕ)
    (threshold : ↑H.vertexSet → ℕ) (v : ↑H.vertexSet) :
    FiniteNibble.EventDependsOn
      (H.innerBatchVertexInfluenceSupport (J := J) L v.1)
      (fun Z : Finset ((J × Fin L) × E) ↦
        threshold v ≤ H.flattenedInnerBatchResidualDegree L Z v.1) := by
  intro Z T hZT
  change (threshold v ≤ H.flattenedInnerBatchResidualDegree L Z v.1) ↔
    threshold v ≤ H.flattenedInnerBatchResidualDegree L T v.1
  rw [H.flattenedInnerBatchResidualDegree_eq_of_agreesOn L v.1 hZT]

/-- Event mass is preserved between the nested-family and flattened
presentations of complete inner batches. -/
lemma eventMass_flattenedInnerResidualDegreeBad_eq
    {J : Type*} [Fintype J] [DecidableEq J]
    (H : FiniteHypergraph V E) (L : ℕ) (prob : E → ℝ)
    (threshold : ↑H.vertexSet → ℕ) (v : ↑H.vertexSet) :
    FiniteLocalLemma.eventMass
        (fun Z : Finset ((J × Fin L) × E) ↦
          FiniteNibble.bernoulliMass univ
            (fun z : (J × Fin L) × E ↦ prob z.2) Z)
        (fun Z ↦ threshold v ≤
          H.flattenedInnerBatchResidualDegree L Z v.1) =
      FiniteLocalLemma.eventMass
        (FiniteProduct.productMass (innerTrialMass L prob))
        (fun X : J → (Fin L → Finset E) ↦
          (threshold v : ℝ) ≤ (H.innerBatchResidualDegree X v.1 : ℝ)) := by
  unfold FiniteLocalLemma.eventMass
  symm
  apply Fintype.sum_equiv (innerBatchFinsetEquiv (E := E) (J := J) (L := L))
  intro X
  simp only [innerBatchFinsetEquiv_apply]
  have hd := H.flattenedInnerBatchResidualDegree_flattenInnerBatch X v.1
  have hm := bernoulliMass_flattenInnerBatch prob X
  by_cases hb : threshold v ≤ H.innerBatchResidualDegree X v.1
  · have hbR : (threshold v : ℝ) ≤ (H.innerBatchResidualDegree X v.1 : ℝ) := by
      exact_mod_cast hb
    simp [hb, hbR, hd, hm]
  · have hbR : ¬ (threshold v : ℝ) ≤ (H.innerBatchResidualDegree X v.1 : ℝ) := by
      exact_mod_cast hb
    simp [hb, hbR, hd, hm]

/-- The event that a residual degree is far from its exact mean is local in
the same finite coordinate support as either one-sided threshold event. -/
lemma flattenedInnerResidualDegreeCenteredBad_eventDependsOn
    {J : Type*} [Fintype J]
    (H : FiniteHypergraph V E) (L : ℕ) (prob : E → ℝ) (t : ℝ)
    (v : ↑H.vertexSet) :
    FiniteNibble.EventDependsOn
      (H.innerBatchVertexInfluenceSupport (J := J) L v.1)
      (fun Z : Finset ((J × Fin L) × E) ↦
        t ≤ |(H.flattenedInnerBatchResidualDegree L Z v.1 : ℝ) -
          FiniteProduct.productExpectation (innerTrialMass L prob)
            (fun X : J → (Fin L → Finset E) ↦
              (H.innerBatchResidualDegree X v.1 : ℝ))|) := by
  intro Z T hZT
  change
    (t ≤ |(H.flattenedInnerBatchResidualDegree L Z v.1 : ℝ) -
      FiniteProduct.productExpectation (innerTrialMass L prob)
        (fun X : J → (Fin L → Finset E) ↦
          (H.innerBatchResidualDegree X v.1 : ℝ))|) ↔
    t ≤ |(H.flattenedInnerBatchResidualDegree L T v.1 : ℝ) -
      FiniteProduct.productExpectation (innerTrialMass L prob)
        (fun X : J → (Fin L → Finset E) ↦
          (H.innerBatchResidualDegree X v.1 : ℝ))|
  have hd := H.flattenedInnerBatchResidualDegree_eq_of_agreesOn L v.1 hZT
  simpa only [hd]

/-- Flattening preserves the mass of the centered two-sided residual-degree
event. -/
lemma eventMass_flattenedInnerResidualDegreeCenteredBad_eq
    {J : Type*} [Fintype J] [DecidableEq J]
    (H : FiniteHypergraph V E) (L : ℕ) (prob : E → ℝ) (t : ℝ)
    (v : ↑H.vertexSet) :
    FiniteLocalLemma.eventMass
        (fun Z : Finset ((J × Fin L) × E) ↦
          FiniteNibble.bernoulliMass univ
            (fun z : (J × Fin L) × E ↦ prob z.2) Z)
        (fun Z ↦ t ≤
          |(H.flattenedInnerBatchResidualDegree L Z v.1 : ℝ) -
            FiniteProduct.productExpectation (innerTrialMass L prob)
              (fun X : J → (Fin L → Finset E) ↦
                (H.innerBatchResidualDegree X v.1 : ℝ))|) =
      FiniteLocalLemma.eventMass
        (FiniteProduct.productMass (innerTrialMass L prob))
        (fun X : J → (Fin L → Finset E) ↦ t ≤
          |(H.innerBatchResidualDegree X v.1 : ℝ) -
            FiniteProduct.productExpectation (innerTrialMass L prob)
              (fun Y : J → (Fin L → Finset E) ↦
                (H.innerBatchResidualDegree Y v.1 : ℝ))|) := by
  unfold FiniteLocalLemma.eventMass
  symm
  apply Fintype.sum_equiv (innerBatchFinsetEquiv (E := E) (J := J) (L := L))
  intro X
  simp only [innerBatchFinsetEquiv_apply]
  have hd := H.flattenedInnerBatchResidualDegree_flattenInnerBatch X v.1
  have hm := bernoulliMass_flattenInnerBatch prob X
  let mean : ℝ := FiniteProduct.productExpectation (innerTrialMass L prob)
    (fun Y : J → (Fin L → Finset E) ↦
      (H.innerBatchResidualDegree Y v.1 : ℝ))
  by_cases hb : t ≤ |(H.innerBatchResidualDegree X v.1 : ℝ) - mean|
  · have hb' : t ≤
        |(H.flattenedInnerBatchResidualDegree L (flattenInnerBatch X) v.1 : ℝ) -
          mean| := by
      simpa only [hd] using hb
    simp [mean, hb, hb', hm]
  · have hb' : ¬ t ≤
        |(H.flattenedInnerBatchResidualDegree L (flattenInnerBatch X) v.1 : ℝ) -
          mean| := by
      simpa only [hd] using hb
    simp [mean, hb, hb', hm]

/-- A symmetric finite-LLL batch: every active vertex simultaneously has
residual degree strictly within `t` of its exact expectation. -/
theorem exists_innerBatchResidualDegree_abs_sub_expectation_lt_of_lll
    {J : Type*} [Fintype J] [Nonempty J]
    (H : FiniteHypergraph V E) (L : ℕ) (prob : E → ℝ)
    (hprob0 : ∀ e, 0 ≤ prob e) (hprob1 : ∀ e, prob e ≤ 1)
    {t x : ℝ} {d : ℕ}
    (ht : 0 ≤ t) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hdegree : ∀ v : ↑H.vertexSet,
      (H.innerBatchVertexDependency L v).card ≤ d)
    (hparameter : 2 * Real.exp (-2 * t ^ 2 / (Fintype.card J : ℝ)) ≤
      x * (1 - x) ^ d) :
    ∃ X : J → (Fin L → Finset E), ∀ v : ↑H.vertexSet,
      |(H.innerBatchResidualDegree X v.1 : ℝ) -
        FiniteProduct.productExpectation (innerTrialMass L prob)
          (fun Y : J → (Fin L → Finset E) ↦
            (H.innerBatchResidualDegree Y v.1 : ℝ))| < t := by
  letI : DecidableEq J := Classical.decEq J
  let flatProb : ((J × Fin L) × E) → ℝ := fun z ↦ prob z.2
  let flatMass : Finset ((J × Fin L) × E) → ℝ := fun Z ↦
    FiniteNibble.bernoulliMass univ flatProb Z
  let mean : ↑H.vertexSet → ℝ := fun v ↦
    FiniteProduct.productExpectation (innerTrialMass L prob)
      (fun X : J → (Fin L → Finset E) ↦
        (H.innerBatchResidualDegree X v.1 : ℝ))
  let bad : ↑H.vertexSet → Finset ((J × Fin L) × E) → Prop := fun v Z ↦
    t ≤ |(H.flattenedInnerBatchResidualDegree L Z v.1 : ℝ) - mean v|
  have hmass0 : ∀ Z, 0 ≤ flatMass Z := by
    intro Z
    exact FiniteNibble.bernoulliMass_nonneg (subset_univ Z)
      (fun z _ ↦ hprob0 z.2) (fun z _ ↦ hprob1 z.2)
  have hmass : ∑ Z, flatMass Z = 1 := by
    simpa [flatMass] using FiniteNibble.sum_bernoulliMass
      (univ : Finset ((J × Fin L) × E)) flatProb
  have hindep : FiniteLocalLemma.IndependentOutside flatMass bad
      (H.innerBatchVertexDependency L) := by
    apply FiniteNibble.independentOutside_of_eventDependsOn flatProb
      (fun v : ↑H.vertexSet ↦
        H.innerBatchVertexInfluenceSupport (J := J) L v.1)
    · intro v
      simpa [flatMass, bad, mean] using
        H.flattenedInnerResidualDegreeCenteredBad_eventDependsOn
          (J := J) L prob t v
    · exact H.innerBatchInfluence_contains_overlaps (J := J) L
  have hmarginal : ∀ v, FiniteLocalLemma.eventMass flatMass (bad v) ≤
      2 * Real.exp (-2 * t ^ 2 / (Fintype.card J : ℝ)) := by
    intro v
    rw [show FiniteLocalLemma.eventMass flatMass (bad v) =
        FiniteLocalLemma.eventMass
          (FiniteProduct.productMass (innerTrialMass L prob))
          (fun X : J → (Fin L → Finset E) ↦ t ≤
            |(H.innerBatchResidualDegree X v.1 : ℝ) -
              FiniteProduct.productExpectation (innerTrialMass L prob)
                (fun Y : J → (Fin L → Finset E) ↦
                  (H.innerBatchResidualDegree Y v.1 : ℝ))|) by
      simpa [flatMass, flatProb, bad, mean] using
        H.eventMass_flattenedInnerResidualDegreeCenteredBad_eq
          (J := J) L prob t v]
    exact H.eventMass_innerBatchResidualDegree_abs_sub_expectation_le
      v.1 prob hprob0 hprob1 ht
  obtain ⟨Z, hZ⟩ := FiniteLocalLemma.exists_avoiding_all_of_independentOutside
    flatMass hmass0 hmass bad (H.innerBatchVertexDependency L)
    (by positivity) hx0 hx1 hparameter hdegree hindep hmarginal
  refine ⟨fun j i ↦ batchAt Z (j, i), ?_⟩
  intro v
  exact lt_of_not_ge (hZ v)

/-- A checked one-batch reduction from two-sided pointwise inner marginals.
The two displayed geometric inequalities are the only scalar bookkeeping
needed to turn concentration around the exact mean into integral lower and
upper residual-degree bounds. -/
theorem exists_innerBatchResidualDegree_between_of_twoSidedMarginal
    {m L degreeLowIn degreeIn degreeLowOut degreeOut d : ℕ}
    (H : FiniteHypergraph V E) (prob : E → ℝ)
    (hprob0 : ∀ e, 0 ≤ prob e) (hprob1 : ∀ e, prob e ≤ 1)
    {a b t x : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (hacceptLow : ∀ e, a ≤ H.innerAcceptanceMass L prob e)
    (hacceptHigh : ∀ e, H.innerAcceptanceMass L prob e ≤ b)
    (hm : 0 < m)
    (hdegreeLow : ∀ v ∈ H.vertexSet, degreeLowIn ≤ H.edgeDegree v)
    (hdegreeHigh : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ degreeIn)
    (ht : 0 ≤ t) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hmeanLow : (degreeLowOut : ℝ) ≤
      (degreeLowIn : ℝ) * (1 - b) ^ m - t)
    (hmeanHigh : (degreeIn : ℝ) * (1 - a) ^ m + t < degreeOut + 1)
    (hdependency : ∀ v : ↑H.vertexSet,
      (H.innerBatchVertexDependency L v).card ≤ d)
    (hparameter : 2 * Real.exp (-2 * t ^ 2 / (m : ℝ)) ≤
      x * (1 - x) ^ d) :
    ∃ X : Fin m → (Fin L → Finset E), ∀ v ∈ H.vertexSet,
      degreeLowOut ≤ H.innerBatchResidualDegree X v ∧
        H.innerBatchResidualDegree X v ≤ degreeOut := by
  letI : DecidableEq (Fin m) := Classical.decEq (Fin m)
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨X, hX⟩ :=
    H.exists_innerBatchResidualDegree_abs_sub_expectation_lt_of_lll
      (J := Fin m) L prob hprob0 hprob1 ht hx0 hx1 hdependency
      (by simpa using hparameter)
  refine ⟨X, ?_⟩
  intro v hv
  let mean : ℝ := FiniteProduct.productExpectation (innerTrialMass L prob)
    (fun Y : Fin m → (Fin L → Finset E) ↦
      (H.innerBatchResidualDegree Y v : ℝ))
  have hcenter : |(H.innerBatchResidualDegree X v : ℝ) - mean| < t := by
    simpa [mean] using hX ⟨v, hv⟩
  have hmeanLower :
      (degreeLowIn : ℝ) * (1 - b) ^ m ≤ mean := by
    calc
      (degreeLowIn : ℝ) * (1 - b) ^ m ≤
          (H.edgeDegree v : ℝ) * (1 - b) ^ m := by
        gcongr
        exact_mod_cast hdegreeLow v hv
      _ ≤ mean := by
        simpa [mean] using
          H.productExpectation_innerBatchResidualDegree_ge
            (J := Fin m) hprob0 hprob1 hb1 hacceptHigh v
  have hmeanUpper : mean ≤ (degreeIn : ℝ) * (1 - a) ^ m := by
    calc
      mean ≤ (H.edgeDegree v : ℝ) * (1 - a) ^ m := by
        simpa [mean] using
          H.productExpectation_innerBatchResidualDegree_le
            (J := Fin m) hprob0 hprob1 ha0 hacceptLow v
      _ ≤ (degreeIn : ℝ) * (1 - a) ^ m := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hdegreeHigh v hv
        · exact pow_nonneg (sub_nonneg.mpr ha1) _
  have hcenterLower : mean - t < (H.innerBatchResidualDegree X v : ℝ) := by
    have := (abs_lt.mp hcenter).1
    linarith
  have hcenterUpper : (H.innerBatchResidualDegree X v : ℝ) < mean + t := by
    have := (abs_lt.mp hcenter).2
    linarith
  constructor
  · have hstrict : (degreeLowOut : ℝ) <
        (H.innerBatchResidualDegree X v : ℝ) := by
      calc
        (degreeLowOut : ℝ) ≤
            (degreeLowIn : ℝ) * (1 - b) ^ m - t := hmeanLow
        _ ≤ mean - t := sub_le_sub_right hmeanLower t
        _ < (H.innerBatchResidualDegree X v : ℝ) := hcenterLower
    have hstrictNat : degreeLowOut < H.innerBatchResidualDegree X v := by
      exact_mod_cast hstrict
    exact hstrictNat.le
  · have hstrict : (H.innerBatchResidualDegree X v : ℝ) < degreeOut + 1 := by
      calc
        (H.innerBatchResidualDegree X v : ℝ) < mean + t := hcenterUpper
        _ ≤ (degreeIn : ℝ) * (1 - a) ^ m + t := by
          simpa [add_comm] using add_le_add_right hmeanUpper t
        _ < degreeOut + 1 := hmeanHigh
    have hstrictNat : H.innerBatchResidualDegree X v < degreeOut + 1 := by
      exact_mod_cast hstrict
    omega

/-- One outer batch of fixed-length inner generators, obtained from the
symmetric finite local lemma. -/
theorem exists_innerBatchResidualDegree_lt_of_lll
    {J : Type*} [Fintype J] [Nonempty J]
    (H : FiniteHypergraph V E) (L : ℕ) (prob : E → ℝ)
    (hprob0 : ∀ e, 0 ≤ prob e) (hprob1 : ∀ e, prob e ≤ 1)
    {a : ℝ} (ha0 : 0 ≤ a)
    (haccept : ∀ e, a ≤ H.innerAcceptanceMass L prob e)
    (threshold : ↑H.vertexSet → ℕ) {t x : ℝ} {d : ℕ}
    (ht : 0 ≤ t) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hthreshold : ∀ v : ↑H.vertexSet,
      (H.edgeDegree v.1 : ℝ) * (1 - a) ^ Fintype.card J + t ≤ threshold v)
    (hdegree : ∀ v : ↑H.vertexSet,
      (H.innerBatchVertexDependency L v).card ≤ d)
    (hparameter : Real.exp (-2 * t ^ 2 / (Fintype.card J : ℝ)) ≤
      x * (1 - x) ^ d) :
    ∃ X : J → (Fin L → Finset E), ∀ v : ↑H.vertexSet,
      H.innerBatchResidualDegree X v.1 < threshold v := by
  letI : DecidableEq J := Classical.decEq J
  let flatProb : ((J × Fin L) × E) → ℝ := fun z ↦ prob z.2
  let flatMass : Finset ((J × Fin L) × E) → ℝ := fun Z ↦
    FiniteNibble.bernoulliMass univ flatProb Z
  let bad : ↑H.vertexSet → Finset ((J × Fin L) × E) → Prop := fun v Z ↦
    threshold v ≤ H.flattenedInnerBatchResidualDegree L Z v.1
  have hmass0 : ∀ Z, 0 ≤ flatMass Z := by
    intro Z
    exact FiniteNibble.bernoulliMass_nonneg (subset_univ Z)
      (fun z _ ↦ hprob0 z.2) (fun z _ ↦ hprob1 z.2)
  have hmass : ∑ Z, flatMass Z = 1 := by
    simpa [flatMass] using FiniteNibble.sum_bernoulliMass
      (univ : Finset ((J × Fin L) × E)) flatProb
  have hindep : FiniteLocalLemma.IndependentOutside flatMass bad
      (H.innerBatchVertexDependency L) := by
    apply FiniteNibble.independentOutside_of_eventDependsOn flatProb
      (fun v : ↑H.vertexSet ↦
        H.innerBatchVertexInfluenceSupport (J := J) L v.1)
    · intro v
      simpa [flatMass, bad] using
        H.flattenedInnerResidualDegreeBad_eventDependsOn (J := J) L threshold v
    · exact H.innerBatchInfluence_contains_overlaps (J := J) L
  have hmarginal : ∀ v, FiniteLocalLemma.eventMass flatMass (bad v) ≤
      Real.exp (-2 * t ^ 2 / (Fintype.card J : ℝ)) := by
    intro v
    rw [show FiniteLocalLemma.eventMass flatMass (bad v) =
        FiniteLocalLemma.eventMass
          (FiniteProduct.productMass (innerTrialMass L prob))
          (fun X : J → (Fin L → Finset E) ↦
            (threshold v : ℝ) ≤ (H.innerBatchResidualDegree X v.1 : ℝ)) by
      simpa [flatMass, flatProb, bad] using
        H.eventMass_flattenedInnerResidualDegreeBad_eq L prob threshold v]
    unfold FiniteLocalLemma.eventMass
    rw [← Finset.sum_filter]
    apply H.productUpperTailMass_innerBatchResidualDegree_threshold_le
      v.1 prob hprob0 hprob1 ht
    calc
      FiniteProduct.productExpectation (innerTrialMass L prob)
            (fun X : J → (Fin L → Finset E) ↦
              (H.innerBatchResidualDegree X v.1 : ℝ)) + t ≤
          (H.edgeDegree v.1 : ℝ) * (1 - a) ^ Fintype.card J + t :=
        by
          have hexp := H.productExpectation_innerBatchResidualDegree_le
            (J := J) hprob0 hprob1 ha0 haccept v.1
          linarith
      _ ≤ (threshold v : ℝ) := hthreshold v
  obtain ⟨Z, hZ⟩ := FiniteLocalLemma.exists_avoiding_all_of_independentOutside
    flatMass hmass0 hmass bad (H.innerBatchVertexDependency L)
    (Real.exp_nonneg _) hx0 hx1 hparameter hdegree hindep hmarginal
  refine ⟨fun j i ↦ batchAt Z (j, i), ?_⟩
  intro v
  exact Nat.lt_of_not_ge (hZ v)

/-! ### Deterministic colour splicing -/

/-- The hypergraph induced by the edges left after a batch. -/
def batchResidualHypergraph {J : Type*} [Fintype J]
    (H : FiniteHypergraph V E) (X : J → Finset E) :
    FiniteHypergraph V ↑(H.batchResidualEdges X) :=
  H.restrictTo H.vertexSet (H.batchResidualEdges X) fun e _ ↦
    H.support_subset_vertexSet e

@[simp] lemma batchResidualHypergraph_vertexSet
    {J : Type*} [Fintype J]
    (H : FiniteHypergraph V E) (X : J → Finset E) :
    (H.batchResidualHypergraph X).vertexSet = H.vertexSet := rfl

@[simp] lemma batchResidualHypergraph_support
    {J : Type*} [Fintype J]
    (H : FiniteHypergraph V E) (X : J → Finset E)
    (e : ↑(H.batchResidualEdges X)) :
    (H.batchResidualHypergraph X).support e = H.support e.1 := rfl

lemma batchResidualHypergraph_isUniform
    {J : Type*} [Fintype J] {H : FiniteHypergraph V E}
    {X : J → Finset E} {k : ℕ} (hunif : H.IsUniform k) :
    (H.batchResidualHypergraph X).IsUniform k :=
  H.restrictTo_isUniform hunif

/-- A residual degree is exactly the corresponding degree in the induced
residual hypergraph. -/
lemma edgeDegree_batchResidualHypergraph
    {J : Type*} [Fintype J]
    (H : FiniteHypergraph V E) (X : J → Finset E) (v : V) :
    (H.batchResidualHypergraph X).edgeDegree v = H.batchResidualDegree X v := by
  unfold batchResidualHypergraph batchResidualDegree edgeDegree
  change ((univ : Finset ↑(H.batchResidualEdges X)).filter
      (fun e ↦ v ∈ H.support e.1)).card =
    ((H.batchResidualEdges X).filter (fun e ↦ v ∈ H.support e)).card
  rw [show (univ : Finset ↑(H.batchResidualEdges X)) =
      (H.batchResidualEdges X).attach by ext e; simp]
  rw [Finset.filter_attach (fun e ↦ v ∈ H.support e)
    (H.batchResidualEdges X)]
  simp

/-- Splice the matching colours used by a nonempty batch with a proper
colouring of the induced residual hypergraph.  This is the deterministic
one-step operation used by the outer iteration. -/
def extendBatchColoring {m q : ℕ} (hm : 0 < m)
    (H : FiniteHypergraph V E) (X : Fin m → Finset E)
    (c : (H.batchResidualHypergraph X).EdgeColoring q) :
    H.EdgeColoring (m + q) := by
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  refine SimpleGraph.Coloring.mk (fun e ↦
    if he : e ∈ H.batchResidualEdges X then
      finSumFinEquiv (Sum.inr (c ⟨e, he⟩))
    else
      finSumFinEquiv (Sum.inl (H.batchOwner X e))) ?_
  intro e f hef
  by_cases heR : e ∈ H.batchResidualEdges X
  · by_cases hfR : f ∈ H.batchResidualEdges X
    · simp only [heR, hfR, dite_true]
      intro hcolor
      have hsubne : (⟨e, heR⟩ : ↑(H.batchResidualEdges X)) ≠ ⟨f, hfR⟩ := by
        intro h
        exact hef.1 (congrArg Subtype.val h)
      apply c.valid ⟨hsubne, hef.2⟩
      exact Sum.inr.inj (finSumFinEquiv.injective hcolor)
    · simp only [heR, hfR, dite_true, dite_false]
      intro hcolor
      exact Sum.inr_ne_inl (finSumFinEquiv.injective hcolor)
  · by_cases hfR : f ∈ H.batchResidualEdges X
    · simp only [heR, hfR, dite_true, dite_false]
      intro hcolor
      exact Sum.inl_ne_inr (finSumFinEquiv.injective hcolor)
    · simp only [heR, hfR, dite_false]
      have heA : e ∈ H.batchAcceptedEdges X := by
        simpa [batchResidualEdges] using heR
      have hfA : f ∈ H.batchAcceptedEdges X := by
        simpa [batchResidualEdges] using hfR
      intro hcolor
      have howners : H.batchOwner X e = H.batchOwner X f :=
        Sum.inl.inj (finSumFinEquiv.injective hcolor)
      let j := H.batchOwner X e
      have heC : e ∈ H.batchColorClass X j :=
        (H.mem_batchColorClass X j e).mpr ⟨heA, rfl⟩
      have hfC : f ∈ H.batchColorClass X j :=
        (H.mem_batchColorClass X j f).mpr ⟨hfA, howners.symm⟩
      exact hef.2 (H.batchColorClass_isMatching X j heC hfC hef.1)

theorem nonempty_edgeColoring_add_batch
    {m q : ℕ} (hm : 0 < m) (H : FiniteHypergraph V E)
    (X : Fin m → Finset E)
    (hc : Nonempty ((H.batchResidualHypergraph X).EdgeColoring q)) :
    Nonempty (H.EdgeColoring (m + q)) := by
  obtain ⟨c⟩ := hc
  exact ⟨H.extendBatchColoring hm X c⟩

/-- A batch of `J` matching colours covers at most `|J|` edges at any one
vertex. -/
lemma batchCoveredAt_card_le_card
    {J : Type*} [Fintype J]
    (H : FiniteHypergraph V E) (X : J → Finset E) (v : V) :
    (H.batchCoveredAt X v).card ≤ Fintype.card J := by
  have hcovered : H.batchCoveredAt X v =
      (univ : Finset J).biUnion fun j ↦
        (H.isolatedSample (X j)).filter fun e ↦ v ∈ H.support e := by
    ext e
    simp only [batchCoveredAt, batchAcceptedEdges, mem_filter, mem_biUnion,
      mem_univ, true_and]
    tauto
  rw [hcovered]
  calc
    ((univ : Finset J).biUnion fun j ↦
        (H.isolatedSample (X j)).filter fun e ↦ v ∈ H.support e).card ≤
        ∑ j : J, ((H.isolatedSample (X j)).filter fun e ↦
          v ∈ H.support e).card := card_biUnion_le
    _ ≤ ∑ _j : J, 1 := sum_le_sum fun j _ ↦
      H.card_filter_isolatedSample_mem_support_le_one (X j) v
    _ = Fintype.card J := by simp

/-- Deterministic lower residual-degree bound for a batch. -/
lemma edgeDegree_sub_card_le_batchResidualDegree
    {J : Type*} [Fintype J]
    (H : FiniteHypergraph V E) (X : J → Finset E) (v : V) :
    H.edgeDegree v - Fintype.card J ≤ H.batchResidualDegree X v := by
  have hsplit := H.batchResidualDegree_add_coveredAt X v
  have hcover := H.batchCoveredAt_card_le_card X v
  omega

/-! ### Restricting batches from a fresh regular completion -/

/-- Pull a set of completion edges back along the preserved original-edge
embedding. -/
def restrictCompletionMatching
    (H : FiniteHypergraph V E) (D k q : ℕ) (hk : 0 < k)
    (hdegree : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (M : Finset (CompletionEdge H D k q hdegree)) : Finset E :=
  univ.filter fun e ↦ originalEdgeEmbedding H D q hk hdegree e ∈ M

@[simp] lemma mem_restrictCompletionMatching
    (H : FiniteHypergraph V E) (D k q : ℕ) (hk : 0 < k)
    (hdegree : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (M : Finset (CompletionEdge H D k q hdegree)) (e : E) :
    e ∈ H.restrictCompletionMatching D k q hk hdegree M ↔
      originalEdgeEmbedding H D q hk hdegree e ∈ M := by
  simp [restrictCompletionMatching]

/-- A matching in the completion restricts to a matching of original edges. -/
lemma restrictCompletionMatching_isMatching
    (H : FiniteHypergraph V E) (D k q : ℕ) [NeZero q] (hk : 0 < k)
    (hdegree : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    {M : Finset (CompletionEdge H D k q hdegree)}
    (hM : (regularCompletion H D k q hdegree).IsMatching M) :
    H.IsMatching (H.restrictCompletionMatching D k q hk hdegree M) := by
  intro e he f hf hef
  have heM := (H.mem_restrictCompletionMatching D k q hk hdegree M e).mp he
  have hfM := (H.mem_restrictCompletionMatching D k q hk hdegree M f).mp hf
  have hembed : originalEdgeEmbedding H D q hk hdegree e ≠
      originalEdgeEmbedding H D q hk hdegree f :=
    (originalEdgeEmbedding H D q hk hdegree).injective.ne hef
  have hdis := hM heM hfM hembed
  rw [Finset.disjoint_left]
  intro v hve hvf
  have hve' := distinguishedVertex_mem_originalEdge
    (q := q) hk hdegree hve
  have hvf' := distinguishedVertex_mem_originalEdge
    (q := q) hk hdegree hvf
  have hvtx : distinguishedVertex (q := q) H hk
        ⟨v, H.support_subset_vertexSet e hve⟩ =
      distinguishedVertex H hk
        ⟨v, H.support_subset_vertexSet f hvf⟩ := by
    simp [distinguishedVertex]
  exact (Finset.disjoint_left.mp hdis) hve' (hvtx.symm ▸ hvf')

/-- Restrict every matching in a completion batch to the preserved original
edges. -/
def restrictCompletionBatch
    {J : Type*} [Fintype J]
    (H : FiniteHypergraph V E) (D k q : ℕ) (hk : 0 < k)
    (hdegree : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (M : J → Finset (CompletionEdge H D k q hdegree)) : J → Finset E :=
  fun j ↦ H.restrictCompletionMatching D k q hk hdegree (M j)

/-- Residual degree cannot increase when a completion batch is restricted to
original edges. -/
lemma batchResidualDegree_restrictCompletionBatch_le
    {J : Type*} [Fintype J]
    (H : FiniteHypergraph V E) (D k q : ℕ) [NeZero q] (hk : 0 < k)
    (hdegree : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (M : J → Finset (CompletionEdge H D k q hdegree))
    (hM : ∀ j, (regularCompletion H D k q hdegree).IsMatching (M j))
    (v : ↑H.vertexSet) :
    H.batchResidualDegree
        (H.restrictCompletionBatch D k q hk hdegree M) v.1 ≤
      (regularCompletion H D k q hdegree).batchResidualDegree M
        (distinguishedVertex H hk v) := by
  let HC := regularCompletion H D k q hdegree
  let emb := originalEdgeEmbedding H D q hk hdegree
  let X := H.restrictCompletionBatch D k q hk hdegree M
  have hXM : ∀ j, H.IsMatching (X j) := fun j ↦
    H.restrictCompletionMatching_isMatching D k q hk hdegree (hM j)
  unfold batchResidualDegree
  rw [← card_image_of_injective _ emb.injective]
  apply card_le_card
  intro g hg
  obtain ⟨e, he, rfl⟩ := mem_image.mp hg
  rw [mem_filter] at he ⊢
  refine ⟨?_, ?_⟩
  · rw [batchResidualEdges, mem_sdiff] at he ⊢
    refine ⟨mem_univ _, ?_⟩
    intro heAcc
    obtain ⟨j, hej⟩ := (HC.mem_batchAcceptedEdges M (emb e)).mp heAcc
    have hejM : emb e ∈ M j := by
      simpa [HC.isolatedSample_eq_self_of_isMatching (hM j)] using hej
    have hejX : e ∈ X j := by
      simpa [X, restrictCompletionBatch, emb] using hejM
    have hejIso : e ∈ H.isolatedSample (X j) := by
      simpa [H.isolatedSample_eq_self_of_isMatching (hXM j)] using hejX
    exact he.1.2 ((H.mem_batchAcceptedEdges X e).mpr ⟨j, hejIso⟩)
  · have hmem := distinguishedVertex_mem_originalEdge
      (q := q) hk hdegree he.2
    change distinguishedVertex H hk v ∈
      tradeSupport H D k q hdegree e (zeroColumn hk)
    simpa [distinguishedVertex] using hmem

/-! ### Abstract finite outer iteration -/

/-- Palette size produced by `s` successive batches, followed by the safe
greedy residual colouring.  The head-recursive form makes the dependent
hypergraph induction definitionally transparent. -/
def outerColorCount (k : ℕ) (degreeCap batchSize : ℕ → ℕ) : ℕ → ℕ
  | 0 => k * degreeCap 0 + 1
  | s + 1 => batchSize 0 +
      outerColorCount k (fun i ↦ degreeCap (i + 1))
        (fun i ↦ batchSize (i + 1)) s

lemma outerColorCount_eq_sum (k : ℕ) (degreeCap batchSize : ℕ → ℕ)
    (s : ℕ) :
    outerColorCount k degreeCap batchSize s =
      (∑ i ∈ range s, batchSize i) + k * degreeCap s + 1 := by
  induction s generalizing degreeCap batchSize with
  | zero => simp [outerColorCount]
  | succ s ih =>
      rw [outerColorCount, ih]
      rw [sum_range_succ']
      omega

/-- A universally available degree-reducing batch at fixed numerical
parameters.  The absolute codegree envelope is intentionally kept unchanged:
restriction to residual edges can only decrease codegrees. -/
def HasBatchReduction
    (k degreeLowIn degreeIn degreeLowOut degreeOut m : ℕ)
    (pairBound : ℝ) : Prop :=
  ∀ (V' : Type uV) (E' : Type uE)
      [DecidableEq V'] [Fintype E'] [DecidableEq E'],
    ∀ H : FiniteHypergraph V' E',
      H.IsUniform k →
      (∀ v ∈ H.vertexSet, degreeLowIn ≤ H.edgeDegree v) →
      (∀ v ∈ H.vertexSet, H.edgeDegree v ≤ degreeIn) →
      (∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
        (H.edgePairDegree u v : ℝ) < pairBound) →
      ∃ X : Fin m → Finset E', ∀ v ∈ H.vertexSet,
        degreeLowOut ≤ H.batchResidualDegree X v ∧
          H.batchResidualDegree X v ≤ degreeOut

/-- The source-faithful two-sided fixed-length marginal supplies one
near-regular batch reduction.  Unlike the lower-only compatibility theorem
below, both degree bounds are obtained from concentration about the exact
mean, so no deterministic loss of one edge per colour is incurred. -/
theorem hasBatchReduction_of_twoSidedFixedLengthInnerMarginal
    {k degreeLowIn degreeIn degreeLowOut degreeOut m L D₀ d : ℕ}
    {zeta eta pairBound t x : ℝ}
    (hgenerator :
      TwoSidedFixedLengthInnerMarginalAt.{uV, uE} k zeta eta L D₀)
    (hm : 0 < m) (hD₀ : D₀ ≤ degreeIn) (hDinTwo : 2 ≤ degreeIn)
    (hzeta0 : 0 ≤ zeta) (hzeta1 : zeta ≤ 1)
    (hlowerNear : (1 - eta) * (degreeIn : ℝ) ≤ degreeLowIn)
    (hpairNear : pairBound ≤ eta * (degreeIn : ℝ))
    (ht : 0 ≤ t) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hmeanLow : (degreeLowOut : ℝ) ≤
      (degreeLowIn : ℝ) *
        (1 - (1 + zeta) / (degreeIn : ℝ)) ^ m - t)
    (hmeanHigh : (degreeIn : ℝ) *
        (1 - (1 - zeta) / (degreeIn : ℝ)) ^ m + t < degreeOut + 1)
    (hdep : (degreeIn * (k * degreeIn + 1) ^ (4 * L + 2)) * k ≤ d)
    (hll : 2 * Real.exp (-2 * t ^ 2 / (m : ℝ)) ≤
      x * (1 - x) ^ d) :
    HasBatchReduction.{uV, uE} k degreeLowIn degreeIn
      degreeLowOut degreeOut m pairBound := by
  intro V' E' _ _ _ H hunif hdegreeLower hdegree hpair
  have hnearLower : ∀ v ∈ H.vertexSet,
      (1 - eta) * (degreeIn : ℝ) ≤ (H.edgeDegree v : ℝ) := by
    intro v hv
    exact hlowerNear.trans (by exact_mod_cast hdegreeLower v hv)
  have hnearPair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      (H.edgePairDegree u v : ℝ) < eta * (degreeIn : ℝ) := by
    intro u hu v hv huv
    exact (hpair u hu v hv huv).trans_le hpairNear
  obtain ⟨prob, hprob0, hprob1, haccept⟩ :=
    hgenerator V' E' H degreeIn hD₀ hunif hnearLower hdegree hnearPair
  let a : ℝ := (1 - zeta) / (degreeIn : ℝ)
  let b : ℝ := (1 + zeta) / (degreeIn : ℝ)
  have hDinR : (0 : ℝ) < degreeIn := by exact_mod_cast (by omega : 0 < degreeIn)
  have ha0 : 0 ≤ a := div_nonneg (sub_nonneg.mpr hzeta1) hDinR.le
  have ha1 : a ≤ 1 := by
    apply (div_le_one hDinR).2
    have hdegreeOne : (1 : ℝ) ≤ degreeIn := by
      exact_mod_cast (by omega : 1 ≤ degreeIn)
    linarith
  have hb1 : b ≤ 1 := by
    apply (div_le_one hDinR).2
    have hdegreeTwo : (2 : ℝ) ≤ degreeIn := by exact_mod_cast hDinTwo
    linarith
  have hdependency : ∀ v : ↑H.vertexSet,
      (H.innerBatchVertexDependency L v).card ≤ d := fun v ↦
    (H.innerBatchVertexDependency_card_le hunif hdegree v).trans hdep
  obtain ⟨innerX, hres⟩ :=
    H.exists_innerBatchResidualDegree_between_of_twoSidedMarginal
      prob hprob0 hprob1 ha0 ha1 hb1
      (fun e ↦ (haccept e).1) (fun e ↦ (haccept e).2)
      hm hdegreeLower hdegree ht hx0 hx1
      (by simpa [b] using hmeanLow) (by simpa [a] using hmeanHigh)
      hdependency (by simpa using hll)
  let X : Fin m → Finset E' := fun j ↦ H.innerMatching (innerX j)
  refine ⟨X, ?_⟩
  intro v hv
  simpa [X, innerBatchResidualDegree] using hres v hv

/-- Freshly complete the current residual original hypergraph to an exact
`D`-regular hypergraph, run a fixed-length batch there, and restrict its
matching colours back to the embedded original edges.  Consequently the
outer recursion needs only a maximum-degree invariant. -/
theorem hasBatchReduction_via_regularCompletion
    {k degreeIn degreeOut m L D₀ d : ℕ}
    {zeta eta pairBound t x : ℝ}
    (hgenerator :
      ExactRegularTwoSidedFixedLengthInnerMarginalAt.{0, 0}
        k zeta eta L D₀)
    (hk : 0 < k) (hm : 0 < m) (hD₀ : D₀ ≤ degreeIn)
    (hDinTwo : 2 ≤ degreeIn)
    (heta0 : 0 ≤ eta) (hetaD : 1 < eta * (degreeIn : ℝ))
    (hzeta0 : 0 ≤ zeta) (hzeta1 : zeta ≤ 1)
    (hpairNear : pairBound ≤ eta * (degreeIn : ℝ))
    (ht : 0 ≤ t) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hmeanHigh : (degreeIn : ℝ) *
        (1 - (1 - zeta) / (degreeIn : ℝ)) ^ m + t ≤ degreeOut + 1)
    (hdep : (degreeIn * (k * degreeIn + 1) ^ (4 * L + 2)) * k ≤ d)
    (hll : Real.exp (-2 * t ^ 2 / (m : ℝ)) ≤
      x * (1 - x) ^ d) :
    HasBatchReduction.{0, 0} k 0 degreeIn 0 degreeOut m pairBound := by
  intro V' E' _ _ _ H hunif _hdegreeLower hdegree hpair
  obtain ⟨q, hqge, hqprime⟩ := Nat.exists_infinite_primes (max k degreeIn)
  letI : Fact q.Prime := ⟨hqprime⟩
  letI : NeZero q := ⟨hqprime.ne_zero⟩
  have hkq : k ≤ q := (le_max_left _ _).trans hqge
  have hDq : degreeIn ≤ q := (le_max_right _ _).trans hqge
  let HC := regularCompletion H degreeIn k q hdegree
  have hunifC : HC.IsUniform k := regularCompletion_isUniform hdegree hunif
  have hregC : ∀ z ∈ HC.vertexSet, HC.edgeDegree z = degreeIn := by
    intro z _
    simpa [HC] using edgeDegree_regularCompletion hdegree z
  have hdegreeC : ∀ z ∈ HC.vertexSet, HC.edgeDegree z ≤ degreeIn := by
    intro z hz
    exact (hregC z hz).le
  have hpairC : ∀ z ∈ HC.vertexSet, ∀ z' ∈ HC.vertexSet, z ≠ z' →
      (HC.edgePairDegree z z' : ℝ) < eta * (degreeIn : ℝ) := by
    intro z _ z' _ hzz'
    by_cases howner : z.1 = z'.1
    · have hle := edgePairDegree_regularCompletion_le_one_same_owner
        hkq hDq hdegree hzz' howner
      have hleR : (HC.edgePairDegree z z' : ℝ) ≤ 1 := by
        exact_mod_cast hle
      exact hleR.trans_lt hetaD
    · have hle := edgePairDegree_regularCompletion_le_of_owner_ne
        hdegree howner
      have hleR : (HC.edgePairDegree z z' : ℝ) ≤
          H.edgePairDegree z.1.1 z'.1.1 := by
        exact_mod_cast hle
      exact hleR.trans_lt
        ((hpair z.1.1 z.1.2 z'.1.1 z'.1.2 (by
          intro heq
          exact howner (Subtype.ext heq))).trans_le hpairNear)
  obtain ⟨prob, hprob0, hprob1, haccept⟩ :=
    hgenerator _ _ HC degreeIn hD₀ hunifC hregC hpairC
  let a : ℝ := (1 - zeta) / (degreeIn : ℝ)
  have hDinR : (0 : ℝ) < degreeIn := by
    exact_mod_cast (by omega : 0 < degreeIn)
  have ha0 : 0 ≤ a := div_nonneg (sub_nonneg.mpr hzeta1) hDinR.le
  have ha1 : a ≤ 1 := by
    apply (div_le_one hDinR).2
    have hdegreeOne : (1 : ℝ) ≤ degreeIn := by
      exact_mod_cast (by omega : 1 ≤ degreeIn)
    linarith
  let threshold : ↑HC.vertexSet → ℕ := fun _ ↦ degreeOut + 1
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hthreshold : ∀ z : ↑HC.vertexSet,
      (HC.edgeDegree z.1 : ℝ) * (1 - a) ^ Fintype.card (Fin m) + t ≤
        threshold z := by
    intro z
    rw [show HC.edgeDegree z.1 = degreeIn by
      simpa [HC] using edgeDegree_regularCompletion hdegree z.1]
    simpa [a, threshold] using hmeanHigh
  obtain ⟨innerX, hres⟩ := HC.exists_innerBatchResidualDegree_lt_of_lll
    (J := Fin m) L prob hprob0 hprob1 ha0
    (fun e ↦ (haccept e).1) threshold ht hx0 hx1 hthreshold
    (fun z ↦ (HC.innerBatchVertexDependency_card_le hunifC hdegreeC z).trans hdep)
    (by simpa using hll)
  let M : Fin m → Finset (CompletionEdge H degreeIn k q hdegree) :=
    fun j ↦ HC.innerMatching (innerX j)
  have hM : ∀ j, HC.IsMatching (M j) := fun j ↦ by
    simpa [M, HC] using
      (HC.innerMatching_isMatching (innerX j))
  let X : Fin m → Finset E' :=
    H.restrictCompletionBatch degreeIn k q hk hdegree M
  refine ⟨X, ?_⟩
  intro v hv
  constructor
  · exact Nat.zero_le _
  · have hrestrict := H.batchResidualDegree_restrictCompletionBatch_le
      degreeIn k q hk hdegree M hM ⟨v, hv⟩
    have hcomplete := hres
      ⟨distinguishedVertex H hk ⟨v, hv⟩, by simp [HC]⟩
    change HC.batchResidualDegree M (distinguishedVertex H hk ⟨v, hv⟩) <
      degreeOut + 1 at hcomplete
    have hlt : H.batchResidualDegree X v < degreeOut + 1 := by
      exact hrestrict.trans_lt hcomplete
    omega

/-- A direct assembly interface: the sharp inner marginal plus the displayed
finite numerical conditions supplies one near-regular batch reduction. -/
theorem hasBatchReduction_of_fixedLengthInnerMarginal
    {k degreeLowIn degreeIn degreeLowOut degreeOut m L D₀ d : ℕ}
    {zeta eta pairBound t x : ℝ}
    (hgenerator : FixedLengthInnerMarginalAt.{uV, uE} k zeta eta L D₀)
    (hm : 0 < m) (hD₀ : D₀ ≤ degreeIn) (hDin : 0 < degreeIn)
    (hzeta0 : 0 ≤ zeta) (hzeta1 : zeta ≤ 1)
    (hlowerNear : (1 - eta) * (degreeIn : ℝ) ≤ degreeLowIn)
    (hpairNear : pairBound ≤ eta * (degreeIn : ℝ))
    (hlowerOut : degreeLowOut ≤ degreeLowIn - m)
    (ht : 0 ≤ t) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hmean : (degreeIn : ℝ) *
          (1 - (1 - zeta) / (degreeIn : ℝ)) ^ m + t ≤ degreeOut + 1)
    (hdep : (degreeIn * (k * degreeIn + 1) ^ (4 * L + 2)) * k ≤ d)
    (hll : Real.exp (-2 * t ^ 2 / (m : ℝ)) ≤ x * (1 - x) ^ d) :
    HasBatchReduction.{uV, uE} k degreeLowIn degreeIn
      degreeLowOut degreeOut m pairBound := by
  intro V' E' _ _ _ H hunif hdegreeLower hdegree hpair
  have hnearLower : ∀ v ∈ H.vertexSet,
      (1 - eta) * (degreeIn : ℝ) ≤ (H.edgeDegree v : ℝ) := by
    intro v hv
    exact hlowerNear.trans (by exact_mod_cast hdegreeLower v hv)
  have hnearPair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      (H.edgePairDegree u v : ℝ) < eta * (degreeIn : ℝ) := by
    intro u hu v hv huv
    exact (hpair u hu v hv huv).trans_le hpairNear
  obtain ⟨prob, hprob0, hprob1, haccept⟩ :=
    hgenerator V' E' H degreeIn hD₀ hunif hnearLower hdegree hnearPair
  let a : ℝ := (1 - zeta) / (degreeIn : ℝ)
  have hDinR : (0 : ℝ) < degreeIn := by exact_mod_cast hDin
  have ha0 : 0 ≤ a := div_nonneg (sub_nonneg.mpr hzeta1) hDinR.le
  have ha1 : a ≤ 1 := by
    apply (div_le_one hDinR).2
    have hdegreeOne : (1 : ℝ) ≤ degreeIn := by exact_mod_cast hDin
    linarith
  let threshold : ↑H.vertexSet → ℕ := fun _ ↦ degreeOut + 1
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hthreshold : ∀ v : ↑H.vertexSet,
      (H.edgeDegree v.1 : ℝ) * (1 - a) ^ Fintype.card (Fin m) + t ≤
        threshold v := by
    intro v
    have hbase : 0 ≤ 1 - a := sub_nonneg.mpr ha1
    have hdegR : (H.edgeDegree v.1 : ℝ) ≤ degreeIn := by
      exact_mod_cast hdegree v.1 v.2
    calc
      (H.edgeDegree v.1 : ℝ) * (1 - a) ^ Fintype.card (Fin m) + t ≤
          (degreeIn : ℝ) * (1 - a) ^ m + t := by
        simp only [Fintype.card_fin]
        gcongr
      _ ≤ (degreeOut + 1 : ℕ) := by simpa [a] using hmean
      _ = threshold v := rfl
  obtain ⟨innerX, hres⟩ := H.exists_innerBatchResidualDegree_lt_of_lll
    (J := Fin m) L prob hprob0 hprob1 ha0 (by simpa [a] using haccept)
    threshold ht hx0 hx1 hthreshold
    (fun v ↦ (H.innerBatchVertexDependency_card_le hunif hdegree v).trans hdep)
    (by simpa using hll)
  let X : Fin m → Finset E' := fun j ↦ H.innerMatching (innerX j)
  refine ⟨X, ?_⟩
  intro v hv
  constructor
  · calc
      degreeLowOut ≤ degreeLowIn - m := hlowerOut
      _ ≤ H.edgeDegree v - m := Nat.sub_le_sub_right (hdegreeLower v hv) m
      _ ≤ H.batchResidualDegree X v := by
        simpa [X] using H.edgeDegree_sub_card_le_batchResidualDegree X v
  · have hlt := hres ⟨v, hv⟩
    change H.batchResidualDegree X v < degreeOut + 1 at hlt
    omega

/-- Finitely many universally available batch reductions iterate.  The final
residual hypergraph is coloured greedily with `k * degreeCap s + 1` colours,
and each earlier batch contributes exactly `batchSize i` matching colours. -/
theorem exists_edgeColoring_of_batchReductions
    (k s : ℕ) (degreeFloor degreeCap batchSize : ℕ → ℕ)
    (pairBound : ℝ)
    (hsize : ∀ i, i < s → 0 < batchSize i)
    (hbatch : ∀ i, i < s →
      HasBatchReduction.{uV, uE} k
        (degreeFloor i) (degreeCap i)
        (degreeFloor (i + 1)) (degreeCap (i + 1))
        (batchSize i) pairBound)
    (H : FiniteHypergraph V E) (hunif : H.IsUniform k)
    (hdegreeLower : ∀ v ∈ H.vertexSet, degreeFloor 0 ≤ H.edgeDegree v)
    (hdegree : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ degreeCap 0)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      (H.edgePairDegree u v : ℝ) < pairBound) :
    Nonempty (H.EdgeColoring (outerColorCount k degreeCap batchSize s)) := by
  induction s generalizing E degreeFloor degreeCap batchSize with
  | zero =>
      simpa [outerColorCount] using
        H.exists_edgeColoring_uniform_degree hunif hdegree
  | succ s ih =>
      have hm0 : 0 < batchSize 0 := hsize 0 (Nat.zero_lt_succ s)
      obtain ⟨X, hX⟩ := hbatch 0 (Nat.zero_lt_succ s)
        V E H hunif hdegreeLower hdegree hpair
      let R : Finset E := H.batchResidualEdges X
      let HR : FiniteHypergraph V ↑R := H.batchResidualHypergraph X
      have hunifR : HR.IsUniform k := H.batchResidualHypergraph_isUniform hunif
      have hdegreeLowerR : ∀ v ∈ HR.vertexSet,
          degreeFloor (0 + 1) ≤ HR.edgeDegree v := by
        intro v hv
        rw [show HR.edgeDegree v = H.batchResidualDegree X v by
          simpa [HR] using H.edgeDegree_batchResidualHypergraph X v]
        exact (hX v (by simpa [HR] using hv)).1
      have hdegreeR : ∀ v ∈ HR.vertexSet,
          HR.edgeDegree v ≤ degreeCap (0 + 1) := by
        intro v hv
        rw [show HR.edgeDegree v = H.batchResidualDegree X v by
          simpa [HR] using H.edgeDegree_batchResidualHypergraph X v]
        exact (hX v (by simpa [HR] using hv)).2
      have hpairR : ∀ u ∈ HR.vertexSet, ∀ v ∈ HR.vertexSet, u ≠ v →
          (HR.edgePairDegree u v : ℝ) < pairBound := by
        intro u hu v hv huv
        calc
          (HR.edgePairDegree u v : ℝ) ≤ H.edgePairDegree u v := by
            exact_mod_cast H.edgePairDegree_restrictTo_le
              H.vertexSet (H.batchResidualEdges X)
              (fun e _ ↦ H.support_subset_vertexSet e) u v
          _ < pairBound := hpair u hu v hv huv
      have hsizeTail : ∀ i, i < s → 0 < batchSize (i + 1) := by
        intro i hi
        exact hsize (i + 1) (by omega)
      have hbatchTail : ∀ i, i < s →
          HasBatchReduction.{uV, uE} k
            (degreeFloor (i + 1)) (degreeCap (i + 1))
            (degreeFloor (i + 1 + 1)) (degreeCap (i + 1 + 1))
            (batchSize (i + 1)) pairBound := by
        intro i hi
        exact hbatch (i + 1) (by omega)
      have hcR : Nonempty (HR.EdgeColoring
          (outerColorCount k (fun i ↦ degreeCap (i + 1))
            (fun i ↦ batchSize (i + 1)) s)) :=
        ih (fun i ↦ degreeFloor (i + 1))
          (fun i ↦ degreeCap (i + 1)) (fun i ↦ batchSize (i + 1))
          hsizeTail hbatchTail HR hunifR hdegreeLowerR hdegreeR hpairR
      exact H.nonempty_edgeColoring_add_batch hm0 X hcR

/-- Maximum-degree-only outer iteration.  Each reduction may be obtained by
fresh regular completion, so the original residual hypergraph need not remain
near-regular. -/
theorem exists_edgeColoring_of_completedBatchReductions
    (k s : ℕ) (degreeCap batchSize : ℕ → ℕ) (pairBound : ℝ)
    (hsize : ∀ i, i < s → 0 < batchSize i)
    (hbatch : ∀ i, i < s →
      HasBatchReduction.{uV, uE} k 0 (degreeCap i) 0 (degreeCap (i + 1))
        (batchSize i) pairBound)
    (H : FiniteHypergraph V E) (hunif : H.IsUniform k)
    (hdegree : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ degreeCap 0)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      (H.edgePairDegree u v : ℝ) < pairBound) :
    Nonempty (H.EdgeColoring (outerColorCount k degreeCap batchSize s)) := by
  apply exists_edgeColoring_of_batchReductions k s (fun _ ↦ 0)
    degreeCap batchSize pairBound hsize hbatch H hunif
  · intro v _
    exact Nat.zero_le _
  · exact hdegree
  · exact hpair

/-- Fully assembled finite schedule theorem.  Every hypothesis after the
fixed-length marginal is a scalar inequality; all hypergraph probability,
locality, LLL, restriction, iteration, and residual colouring are discharged
by this theorem. -/
theorem exists_edgeColoring_of_fixedLengthMarginal_schedule
    {k L D₀ s : ℕ} {zeta eta pairBound : ℝ}
    (hgenerator : FixedLengthInnerMarginalAt.{uV, uE} k zeta eta L D₀)
    (degreeFloor degreeCap batchSize depDegree : ℕ → ℕ)
    (deviation lllChoice : ℕ → ℝ)
    (hzeta0 : 0 ≤ zeta) (hzeta1 : zeta ≤ 1)
    (hsize : ∀ i, i < s → 0 < batchSize i)
    (hD₀ : ∀ i, i < s → D₀ ≤ degreeCap i)
    (hcapPos : ∀ i, i < s → 0 < degreeCap i)
    (hlowerNear : ∀ i, i < s →
      (1 - eta) * (degreeCap i : ℝ) ≤ degreeFloor i)
    (hpairNear : ∀ i, i < s →
      pairBound ≤ eta * (degreeCap i : ℝ))
    (hlowerStep : ∀ i, i < s →
      degreeFloor (i + 1) ≤ degreeFloor i - batchSize i)
    (hdev : ∀ i, i < s → 0 ≤ deviation i)
    (hx0 : ∀ i, i < s → 0 ≤ lllChoice i)
    (hx1 : ∀ i, i < s → lllChoice i < 1)
    (hmean : ∀ i, i < s →
      (degreeCap i : ℝ) *
          (1 - (1 - zeta) / (degreeCap i : ℝ)) ^ batchSize i +
            deviation i ≤ degreeCap (i + 1) + 1)
    (hdep : ∀ i, i < s →
      (degreeCap i * (k * degreeCap i + 1) ^ (4 * L + 2)) * k ≤
        depDegree i)
    (hll : ∀ i, i < s →
      Real.exp (-2 * deviation i ^ 2 / (batchSize i : ℝ)) ≤
        lllChoice i * (1 - lllChoice i) ^ depDegree i)
    (H : FiniteHypergraph V E) (hunif : H.IsUniform k)
    (hdegreeLower : ∀ v ∈ H.vertexSet, degreeFloor 0 ≤ H.edgeDegree v)
    (hdegree : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ degreeCap 0)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      (H.edgePairDegree u v : ℝ) < pairBound) :
    Nonempty (H.EdgeColoring (outerColorCount k degreeCap batchSize s)) := by
  apply exists_edgeColoring_of_batchReductions k s degreeFloor degreeCap batchSize
    pairBound hsize
  · intro i hi
    exact hasBatchReduction_of_fixedLengthInnerMarginal hgenerator
      (hsize i hi) (hD₀ i hi) (hcapPos i hi) hzeta0 hzeta1
      (hlowerNear i hi) (hpairNear i hi) (hlowerStep i hi)
      (hdev i hi) (hx0 i hi) (hx1 i hi) (hmean i hi) (hdep i hi) (hll i hi)
  · exact hunif
  · exact hdegreeLower
  · exact hdegree
  · exact hpair

/-- Source-faithful finite schedule assembly using a two-sided inner marginal
and two-sided residual-degree concentration. -/
theorem exists_edgeColoring_of_twoSidedFixedLengthMarginal_schedule
    {k L D₀ s : ℕ} {zeta eta pairBound : ℝ}
    (hgenerator :
      TwoSidedFixedLengthInnerMarginalAt.{uV, uE} k zeta eta L D₀)
    (degreeFloor degreeCap batchSize depDegree : ℕ → ℕ)
    (deviation lllChoice : ℕ → ℝ)
    (hzeta0 : 0 ≤ zeta) (hzeta1 : zeta ≤ 1)
    (hsize : ∀ i, i < s → 0 < batchSize i)
    (hD₀ : ∀ i, i < s → D₀ ≤ degreeCap i)
    (hcapTwo : ∀ i, i < s → 2 ≤ degreeCap i)
    (hlowerNear : ∀ i, i < s →
      (1 - eta) * (degreeCap i : ℝ) ≤ degreeFloor i)
    (hpairNear : ∀ i, i < s →
      pairBound ≤ eta * (degreeCap i : ℝ))
    (hdev : ∀ i, i < s → 0 ≤ deviation i)
    (hx0 : ∀ i, i < s → 0 ≤ lllChoice i)
    (hx1 : ∀ i, i < s → lllChoice i < 1)
    (hmeanLow : ∀ i, i < s →
      (degreeFloor (i + 1) : ℝ) ≤ (degreeFloor i : ℝ) *
          (1 - (1 + zeta) / (degreeCap i : ℝ)) ^ batchSize i -
        deviation i)
    (hmeanHigh : ∀ i, i < s →
      (degreeCap i : ℝ) *
          (1 - (1 - zeta) / (degreeCap i : ℝ)) ^ batchSize i +
        deviation i < degreeCap (i + 1) + 1)
    (hdep : ∀ i, i < s →
      (degreeCap i * (k * degreeCap i + 1) ^ (4 * L + 2)) * k ≤
        depDegree i)
    (hll : ∀ i, i < s →
      2 * Real.exp (-2 * deviation i ^ 2 / (batchSize i : ℝ)) ≤
        lllChoice i * (1 - lllChoice i) ^ depDegree i)
    (H : FiniteHypergraph V E) (hunif : H.IsUniform k)
    (hdegreeLower : ∀ v ∈ H.vertexSet, degreeFloor 0 ≤ H.edgeDegree v)
    (hdegree : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ degreeCap 0)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      (H.edgePairDegree u v : ℝ) < pairBound) :
    Nonempty (H.EdgeColoring (outerColorCount k degreeCap batchSize s)) := by
  apply exists_edgeColoring_of_batchReductions k s degreeFloor degreeCap batchSize
    pairBound hsize
  · intro i hi
    exact hasBatchReduction_of_twoSidedFixedLengthInnerMarginal hgenerator
      (hsize i hi) (hD₀ i hi) (hcapTwo i hi) hzeta0 hzeta1
      (hlowerNear i hi) (hpairNear i hi)
      (hdev i hi) (hx0 i hi) (hx1 i hi)
      (hmeanLow i hi) (hmeanHigh i hi) (hdep i hi) (hll i hi)
  · exact hunif
  · exact hdegreeLower
  · exact hdegree
  · exact hpair

/-- Fully assembled finite schedule theorem using a fresh exact-regular
completion before every batch.  Only maximum degree and absolute codegree are
carried by the original residual hypergraph. -/
theorem exists_edgeColoring_of_completedMarginal_schedule
    {k L D₀ s : ℕ} {zeta eta pairBound : ℝ}
    (hgenerator :
      ExactRegularTwoSidedFixedLengthInnerMarginalAt.{0, 0}
        k zeta eta L D₀)
    (hk : 0 < k) (degreeCap batchSize depDegree : ℕ → ℕ)
    (deviation lllChoice : ℕ → ℝ)
    (hzeta0 : 0 ≤ zeta) (hzeta1 : zeta ≤ 1)
    (hsize : ∀ i, i < s → 0 < batchSize i)
    (hD₀ : ∀ i, i < s → D₀ ≤ degreeCap i)
    (hcapTwo : ∀ i, i < s → 2 ≤ degreeCap i)
    (heta0 : 0 ≤ eta)
    (hetaCap : ∀ i, i < s → 1 < eta * (degreeCap i : ℝ))
    (hpairNear : ∀ i, i < s →
      pairBound ≤ eta * (degreeCap i : ℝ))
    (hdev : ∀ i, i < s → 0 ≤ deviation i)
    (hx0 : ∀ i, i < s → 0 ≤ lllChoice i)
    (hx1 : ∀ i, i < s → lllChoice i < 1)
    (hmeanHigh : ∀ i, i < s →
      (degreeCap i : ℝ) *
          (1 - (1 - zeta) / (degreeCap i : ℝ)) ^ batchSize i +
        deviation i ≤ degreeCap (i + 1) + 1)
    (hdep : ∀ i, i < s →
      (degreeCap i * (k * degreeCap i + 1) ^ (4 * L + 2)) * k ≤
        depDegree i)
    (hll : ∀ i, i < s →
      Real.exp (-2 * deviation i ^ 2 / (batchSize i : ℝ)) ≤
        lllChoice i * (1 - lllChoice i) ^ depDegree i)
    {V₀ E₀ : Type} [DecidableEq V₀] [Fintype E₀] [DecidableEq E₀]
    (H : FiniteHypergraph V₀ E₀) (hunif : H.IsUniform k)
    (hdegree : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ degreeCap 0)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      (H.edgePairDegree u v : ℝ) < pairBound) :
    Nonempty (H.EdgeColoring (outerColorCount k degreeCap batchSize s)) := by
  apply exists_edgeColoring_of_completedBatchReductions k s degreeCap batchSize
    pairBound hsize
  · intro i hi
    exact hasBatchReduction_via_regularCompletion hgenerator hk
      (hsize i hi) (hD₀ i hi) (hcapTwo i hi) heta0 (hetaCap i hi)
      hzeta0 hzeta1 (hpairNear i hi) (hdev i hi) (hx0 i hi) (hx1 i hi)
      (hmeanHigh i hi) (hdep i hi) (hll i hi)
  · exact hunif
  · exact hdegree
  · exact hpair

/-! ### Scalar estimates used when constructing outer schedules -/

lemma pow_one_sub_le_exp_neg_mul {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (m : ℕ) :
    (1 - a) ^ m ≤ Real.exp (-a * (m : ℝ)) := by
  calc
    (1 - a) ^ m ≤ (Real.exp (-a)) ^ m :=
      pow_le_pow_left₀ (sub_nonneg.mpr ha1) (Real.one_sub_le_exp_neg a) m
    _ = Real.exp (-a * (m : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- Elementary conversion from a small symmetric-LLL marginal to the
`x(1-x)^d` interface, with `x = 2p`. -/
lemma lll_parameter_of_four_mul_add_one_le_one
    {p : ℝ} {d : ℕ} (hp : 0 ≤ p)
    (hsmall : 4 * p * ((d : ℝ) + 1) ≤ 1) :
    p ≤ (2 * p) * (1 - 2 * p) ^ d := by
  have hpHalf : 2 * p ≤ 1 := by
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith [mul_nonneg hp (show 0 ≤ (d : ℝ) + 1 by positivity)]
  have hbern : 1 + (d : ℝ) * (-2 * p) ≤ (1 - 2 * p) ^ d := by
    simpa [sub_eq_add_neg, mul_assoc] using
      (one_add_mul_le_pow (a := -2 * p) (by nlinarith) d)
  have hhalf : (1 / 2 : ℝ) ≤ (1 - 2 * p) ^ d := by
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith [hbern, mul_nonneg hp hd]
  calc
    p = (2 * p) * (1 / 2 : ℝ) := by ring
    _ ≤ (2 * p) * (1 - 2 * p) ^ d :=
      mul_le_mul_of_nonneg_left hhalf (mul_nonneg (by norm_num) hp)

lemma innerDependencyDegree_le_polynomial
    (k L D : ℕ) (hD : 0 < D) :
    (D * (k * D + 1) ^ (4 * L + 2)) * k ≤
      (k * (k + 1) ^ (4 * L + 2)) * D ^ (4 * L + 3) := by
  have hbase : k * D + 1 ≤ (k + 1) * D := by
    rw [Nat.add_mul, one_mul]
    exact Nat.add_le_add_left (by omega) (k * D)
  calc
    (D * (k * D + 1) ^ (4 * L + 2)) * k ≤
        (D * ((k + 1) * D) ^ (4 * L + 2)) * k := by
      gcongr
    _ = (k * (k + 1) ^ (4 * L + 2)) * D ^ (4 * L + 3) := by
      rw [mul_pow]
      ring

/-- The exponential McDiarmid tail eventually satisfies the exact symmetric
LLL parameter inequality for the inner-batch vertex dependency polynomial. -/
theorem exists_inner_lll_parameter
    (k L : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ D₁ : ℕ, ∀ D : ℕ, D₁ ≤ D → 0 < D →
      let p := Real.exp (-c * (D : ℝ))
      let d := (D * (k * D + 1) ^ (4 * L + 2)) * k
      p ≤ (2 * p) * (1 - 2 * p) ^ d := by
  let C₀ : ℝ := (k * (k + 1) ^ (4 * L + 2) : ℕ)
  obtain ⟨D₁, hD₁⟩ :=
    PippengerSpencerParameters.exists_exp_tail_mul_polynomial_le_one
      c (2 * (C₀ + 1)) (4 * L + 3) hc
  refine ⟨D₁, ?_⟩
  intro D hlarge hD
  dsimp only
  apply lll_parameter_of_four_mul_add_one_le_one (Real.exp_nonneg _)
  have hraw := hD₁ D hlarge
  have hpolyNat := innerDependencyDegree_le_polynomial k L D hD
  have hpoly :
      (((D * (k * D + 1) ^ (4 * L + 2)) * k : ℕ) : ℝ) + 1 ≤
        (C₀ + 1) * (D : ℝ) ^ (4 * L + 3) := by
    have hDpow : (1 : ℝ) ≤ (D : ℝ) ^ (4 * L + 3) := by
      exact one_le_pow₀ (by exact_mod_cast hD)
    have hcast :
        (((D * (k * D + 1) ^ (4 * L + 2)) * k : ℕ) : ℝ) ≤
          C₀ * (D : ℝ) ^ (4 * L + 3) := by
      dsimp [C₀]
      exact_mod_cast hpolyNat
    calc
      (((D * (k * D + 1) ^ (4 * L + 2)) * k : ℕ) : ℝ) + 1 ≤
          C₀ * (D : ℝ) ^ (4 * L + 3) + 1 := by gcongr
      _ ≤ C₀ * (D : ℝ) ^ (4 * L + 3) +
          (D : ℝ) ^ (4 * L + 3) := by gcongr
      _ = (C₀ + 1) * (D : ℝ) ^ (4 * L + 3) := by ring
  calc
    4 * Real.exp (-c * (D : ℝ)) *
          ((((D * (k * D + 1) ^ (4 * L + 2)) * k : ℕ) : ℝ) + 1) ≤
        4 * Real.exp (-c * (D : ℝ)) *
          ((C₀ + 1) * (D : ℝ) ^ (4 * L + 3)) := by gcongr
    _ ≤ 2 * Real.exp (-c * (D : ℝ)) *
          (2 * (C₀ + 1) * (D : ℝ) ^ (4 * L + 3) + 1) := by
      have hp := Real.exp_nonneg (-c * (D : ℝ))
      nlinarith
    _ ≤ 1 := hraw

/-! ### Ceil-geometric scalar recurrences -/

/-- Integer degree caps obtained by rounding the contraction `q` upward at
each outer round. -/
def ceilGeometricCap (q : ℝ) (D : ℕ) : ℕ → ℕ
  | 0 => D
  | i + 1 => ⌈q * ceilGeometricCap q D i⌉₊

@[simp] lemma ceilGeometricCap_zero (q : ℝ) (D : ℕ) :
    ceilGeometricCap q D 0 = D := rfl

@[simp] lemma ceilGeometricCap_succ (q : ℝ) (D i : ℕ) :
    ceilGeometricCap q D (i + 1) = ⌈q * ceilGeometricCap q D i⌉₊ := rfl

/-- Upward rounding keeps the cap above the exact geometric trajectory. -/
lemma geometric_le_ceilGeometricCap
    {q : ℝ} (hq : 0 ≤ q) (D i : ℕ) :
    q ^ i * (D : ℝ) ≤ (ceilGeometricCap q D i : ℝ) := by
  induction i with
  | zero => simp
  | succ i ih =>
      calc
        q ^ (i + 1) * (D : ℝ) = q * (q ^ i * (D : ℝ)) := by ring
        _ ≤ q * (ceilGeometricCap q D i : ℝ) :=
          mul_le_mul_of_nonneg_left ih hq
        _ ≤ (⌈q * ceilGeometricCap q D i⌉₊ : ℕ) :=
          Nat.le_ceil (q * (ceilGeometricCap q D i : ℝ))
        _ = (ceilGeometricCap q D (i + 1) : ℕ) := rfl

/-- The accumulated upward-rounding error is at most the infinite geometric
tail `(1-q)⁻¹`. -/
lemma natCast_ceilGeometricCap_le
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (D i : ℕ) :
    (ceilGeometricCap q D i : ℝ) ≤ q ^ i * (D : ℝ) + (1 - q)⁻¹ := by
  have hB0 : 0 ≤ (1 - q)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hq1.le)
  induction i with
  | zero => simp [hB0]
  | succ i ih =>
      have hceil := Nat.ceil_lt_add_one
        (mul_nonneg hq0 (Nat.cast_nonneg (ceilGeometricCap q D i)))
      calc
        (ceilGeometricCap q D (i + 1) : ℝ) ≤
            q * (ceilGeometricCap q D i : ℝ) + 1 := by
          simpa using hceil.le
        _ ≤ q * (q ^ i * (D : ℝ) + (1 - q)⁻¹) + 1 := by
          gcongr
        _ = q ^ (i + 1) * (D : ℝ) + (1 - q)⁻¹ := by
          have hne : 1 - q ≠ 0 := sub_ne_zero.mpr hq1.ne'
          field_simp
          ring

/-- Sum of all rounded caps over a fixed number of rounds. -/
lemma sum_natCast_ceilGeometricCap_le
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (D s : ℕ) :
    ∑ i ∈ range s, (ceilGeometricCap q D i : ℝ) ≤
      (1 - q)⁻¹ * (D : ℝ) + s * (1 - q)⁻¹ := by
  calc
    ∑ i ∈ range s, (ceilGeometricCap q D i : ℝ) ≤
        ∑ i ∈ range s, (q ^ i * (D : ℝ) + (1 - q)⁻¹) := by
      apply sum_le_sum
      intro i _
      exact natCast_ceilGeometricCap_le hq0 hq1 D i
    _ = (∑ i ∈ range s, q ^ i) * (D : ℝ) + s * (1 - q)⁻¹ := by
      rw [sum_add_distrib, Finset.sum_mul]
      simp
    _ ≤ (1 - q)⁻¹ * (D : ℝ) + s * (1 - q)⁻¹ := by
      gcongr
      exact PippengerSpencerParameters.sum_range_geometric_le_inv s hq0 hq1

/-- Total floor-rounded batch allocation along the ceil-geometric cap
trajectory. -/
lemma sum_floor_mul_ceilGeometricCap_le
    {theta q : ℝ} (htheta : 0 ≤ theta)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (D s : ℕ) :
    (∑ i ∈ range s, ⌊theta * ceilGeometricCap q D i⌋₊ : ℕ) ≤
      theta * ((1 - q)⁻¹ * (D : ℝ) + s * (1 - q)⁻¹) := by
  rw [Nat.cast_sum]
  calc
    ∑ i ∈ range s, (⌊theta * ceilGeometricCap q D i⌋₊ : ℝ) ≤
        ∑ i ∈ range s, theta * (ceilGeometricCap q D i : ℝ) := by
      apply sum_le_sum
      intro i _
      exact Nat.floor_le (mul_nonneg htheta (Nat.cast_nonneg _))
    _ = theta * ∑ i ∈ range s, (ceilGeometricCap q D i : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ theta * ((1 - q)⁻¹ * (D : ℝ) + s * (1 - q)⁻¹) :=
      mul_le_mul_of_nonneg_left
        (sum_natCast_ceilGeometricCap_le hq0 hq1 D s) htheta

/-- One-step contraction for a floor-sized batch.  The parameter `sigma`
absorbs the single unit lost when rounding the batch size down. -/
lemma floor_batch_mean_le_ceil_contraction
    {theta rho sigma q zeta : ℝ} {C : ℕ}
    (hC : 0 < C) (htheta : 0 ≤ theta) (hrho : 0 ≤ rho)
    (hzeta0 : 0 ≤ zeta) (hzeta1 : zeta ≤ 1)
    (hsigma : (1 - zeta) / (C : ℝ) ≤ sigma)
    (hrate : Real.exp (-((1 - zeta) * theta - sigma)) + rho ≤ q) :
    (C : ℝ) *
          (1 - (1 - zeta) / (C : ℝ)) ^ ⌊theta * (C : ℝ)⌋₊ +
        rho * (C : ℝ) ≤ ⌈q * (C : ℝ)⌉₊ := by
  let a : ℝ := (1 - zeta) / (C : ℝ)
  let m : ℕ := ⌊theta * (C : ℝ)⌋₊
  have hCR : (0 : ℝ) < C := by exact_mod_cast hC
  have ha0 : 0 ≤ a := div_nonneg (sub_nonneg.mpr hzeta1) hCR.le
  have ha1 : a ≤ 1 := by
    apply (div_le_one hCR).2
    have hCone : (1 : ℝ) ≤ C := by exact_mod_cast hC
    linarith
  have hfloor : theta * (C : ℝ) - 1 < (m : ℝ) := by
    have h := Nat.lt_floor_add_one (theta * (C : ℝ))
    dsimp [m]
    change theta * (C : ℝ) < (m : ℝ) + 1 at h
    linarith
  have halgebra : a * (theta * (C : ℝ) - 1) =
      (1 - zeta) * theta - a := by
    dsimp [a]
    field_simp
  have hexponent : (1 - zeta) * theta - sigma ≤ a * (m : ℝ) := by
    have hmul : a * (theta * (C : ℝ) - 1) ≤ a * (m : ℝ) :=
      mul_le_mul_of_nonneg_left hfloor.le ha0
    rw [halgebra] at hmul
    have haSigma : a ≤ sigma := by simpa [a] using hsigma
    linarith
  have hpow := pow_one_sub_le_exp_neg_mul ha0 ha1 m
  calc
    (C : ℝ) * (1 - (1 - zeta) / (C : ℝ)) ^ m + rho * (C : ℝ) ≤
        (C : ℝ) * Real.exp (-a * (m : ℝ)) + rho * (C : ℝ) := by
      dsimp [a]
      gcongr
    _ ≤ (C : ℝ) * Real.exp (-((1 - zeta) * theta - sigma)) +
          rho * (C : ℝ) := by
      gcongr
      simpa [neg_mul] using neg_le_neg hexponent
    _ = (Real.exp (-((1 - zeta) * theta - sigma)) + rho) * (C : ℝ) := by
      ring
    _ ≤ q * (C : ℝ) :=
      mul_le_mul_of_nonneg_right hrate (Nat.cast_nonneg C)
    _ ≤ (⌈q * (C : ℝ)⌉₊ : ℕ) := Nat.le_ceil (q * (C : ℝ))

/-- A linear-in-the-cap exponential upper bound for the McDiarmid tail of a
floor-sized batch. -/
lemma floor_batch_tail_le_exp_linear
    {theta rho : ℝ} {C : ℕ}
    (htheta : 0 < theta) (hrho : 0 ≤ rho)
    (hm : 0 < ⌊theta * (C : ℝ)⌋₊) :
    Real.exp (-2 * (rho * (C : ℝ)) ^ 2 /
        (⌊theta * (C : ℝ)⌋₊ : ℝ)) ≤
      Real.exp (-(2 * rho ^ 2 / theta) * (C : ℝ)) := by
  let m : ℕ := ⌊theta * (C : ℝ)⌋₊
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmle : (m : ℝ) ≤ theta * (C : ℝ) := by
    dsimp [m]
    exact Nat.floor_le (mul_nonneg htheta.le (Nat.cast_nonneg C))
  have hmdiv : (m : ℝ) / theta ≤ (C : ℝ) := by
    exact (div_le_iff₀ htheta).2 (by simpa [mul_comm] using hmle)
  have hcoef : 0 ≤ 2 * rho ^ 2 * (C : ℝ) := by positivity
  have hmul : (2 * rho ^ 2 / theta * (C : ℝ)) * (m : ℝ) ≤
      2 * (rho * (C : ℝ)) ^ 2 := by
    calc
      (2 * rho ^ 2 / theta * (C : ℝ)) * (m : ℝ) =
          (2 * rho ^ 2 * (C : ℝ)) * ((m : ℝ) / theta) := by
        field_simp
      _ ≤ (2 * rho ^ 2 * (C : ℝ)) * (C : ℝ) :=
        mul_le_mul_of_nonneg_left hmdiv hcoef
      _ = 2 * (rho * (C : ℝ)) ^ 2 := by ring
  have hratio : 2 * rho ^ 2 / theta * (C : ℝ) ≤
      2 * (rho * (C : ℝ)) ^ 2 / (m : ℝ) :=
    (le_div_iff₀ hmR).2 hmul
  apply Real.exp_le_exp.mpr
  calc
    -2 * (rho * (C : ℝ)) ^ 2 / (m : ℝ) =
        -(2 * (rho * (C : ℝ)) ^ 2 / (m : ℝ)) := by ring
    _ ≤ -(2 * rho ^ 2 / theta * (C : ℝ)) := neg_le_neg hratio
    _ = -(2 * rho ^ 2 / theta) * (C : ℝ) := by ring

/-! ### Pure scalar schedule interface -/

/-- Pure numerical certificate for the fresh-completion outer iteration. -/
structure CompletedOuterSchedule
    (k L D₀ : ℕ) (zeta eta epsilon delta : ℝ) (D : ℕ) where
  rounds : ℕ
  degreeCap : ℕ → ℕ
  batchSize : ℕ → ℕ
  depDegree : ℕ → ℕ
  deviation : ℕ → ℝ
  lllChoice : ℕ → ℝ
  cap_zero : degreeCap 0 = D
  size_pos : ∀ i, i < rounds → 0 < batchSize i
  threshold_large : ∀ i, i < rounds → D₀ ≤ degreeCap i
  cap_two : ∀ i, i < rounds → 2 ≤ degreeCap i
  eta_cap : ∀ i, i < rounds → 1 < eta * (degreeCap i : ℝ)
  pair_near : ∀ i, i < rounds →
    delta * (D : ℝ) ≤ eta * (degreeCap i : ℝ)
  deviation_nonneg : ∀ i, i < rounds → 0 ≤ deviation i
  choice_nonneg : ∀ i, i < rounds → 0 ≤ lllChoice i
  choice_lt_one : ∀ i, i < rounds → lllChoice i < 1
  mean_step : ∀ i, i < rounds →
    (degreeCap i : ℝ) *
        (1 - (1 - zeta) / (degreeCap i : ℝ)) ^ batchSize i +
      deviation i ≤ degreeCap (i + 1) + 1
  dependency_step : ∀ i, i < rounds →
    (degreeCap i * (k * degreeCap i + 1) ^ (4 * L + 2)) * k ≤ depDegree i
  lll_step : ∀ i, i < rounds →
    Real.exp (-2 * deviation i ^ 2 / (batchSize i : ℝ)) ≤
      lllChoice i * (1 - lllChoice i) ^ depDegree i
  color_bound :
    (outerColorCount k degreeCap batchSize rounds : ℝ) ≤
      (1 + epsilon) * (D : ℝ)

/-- Given fixed contraction parameters with strict colour-budget slack, all
integer rounding and local-lemma conditions hold for sufficiently large
initial degree. -/
theorem exists_completedOuterSchedule_of_rates
    {k L D₀ s : ℕ} {zeta eta epsilon theta rho q : ℝ}
    (hepsilon : 0 < epsilon) (heta : 0 < eta)
    (hzeta0 : 0 ≤ zeta) (hzeta1 : zeta < 1)
    (htheta : 0 < theta) (hrho : 0 < rho)
    (hq0 : 0 < q) (hq1 : q < 1)
    (hrate : Real.exp (-((1 - zeta) * theta - rho)) + rho ≤ q)
    (hbudget : theta * (1 - q)⁻¹ + (k : ℝ) * q ^ s < 1 + epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ D₁ : ℕ,
      ∀ D : ℕ, D₁ ≤ D →
        Nonempty (CompletedOuterSchedule k L D₀ zeta eta epsilon delta D) := by
  let cLLL : ℝ := 2 * rho ^ 2 / theta
  have hcLLL : 0 < cLLL := by positivity
  obtain ⟨Dlll, hDlll⟩ := exists_inner_lll_parameter k L cLLL hcLLL
  obtain ⟨Ctheta, hCtheta⟩ := exists_nat_gt (1 / theta)
  obtain ⟨Crho, hCrho⟩ := exists_nat_gt ((1 - zeta) / rho)
  obtain ⟨Ceta, hCeta⟩ := exists_nat_gt (1 / eta)
  obtain ⟨Ctail, hCtail⟩ := exists_nat_gt (1 / cLLL)
  let C₀ : ℕ := max D₀ (max Dlll (max 2 (max Ctheta (max Crho (max Ceta Ctail)))))
  have hD₀C : D₀ ≤ C₀ := by
    exact le_max_left _ _
  have hDlllC : Dlll ≤ C₀ := by
    exact (le_max_left Dlll
      (max 2 (max Ctheta (max Crho (max Ceta Ctail))))).trans
        (le_max_right D₀ _)
  have htwoC : 2 ≤ C₀ := by
    exact (le_max_left 2 (max Ctheta (max Crho (max Ceta Ctail)))).trans
      ((le_max_right Dlll _).trans (le_max_right D₀ _))
  have hCthetaC : Ctheta ≤ C₀ := by
    exact (le_max_left Ctheta (max Crho (max Ceta Ctail))).trans
      ((le_max_right 2 _).trans
        ((le_max_right Dlll _).trans (le_max_right D₀ _)))
  have hCrhoC : Crho ≤ C₀ := by
    exact (le_max_left Crho (max Ceta Ctail)).trans
      ((le_max_right Ctheta _).trans
        ((le_max_right 2 _).trans
          ((le_max_right Dlll _).trans (le_max_right D₀ _))))
  have hCetaC : Ceta ≤ C₀ := by
    exact (le_max_left Ceta Ctail).trans
      ((le_max_right Crho _).trans
        ((le_max_right Ctheta _).trans
          ((le_max_right 2 _).trans
            ((le_max_right Dlll _).trans (le_max_right D₀ _)))))
  have hCtailC : Ctail ≤ C₀ := by
    exact (le_max_right Ceta Ctail).trans
      ((le_max_right Crho _).trans
        ((le_max_right Ctheta _).trans
          ((le_max_right 2 _).trans
            ((le_max_right Dlll _).trans (le_max_right D₀ _)))))
  have hthetaC : 1 < theta * (C₀ : ℝ) := by
    have h := (div_lt_iff₀ htheta).mp hCtheta
    have hcast : (Ctheta : ℝ) ≤ C₀ := by exact_mod_cast hCthetaC
    nlinarith
  have hrhoC : 1 - zeta < rho * (C₀ : ℝ) := by
    have h := (div_lt_iff₀ hrho).mp hCrho
    have hcast : (Crho : ℝ) ≤ C₀ := by exact_mod_cast hCrhoC
    nlinarith
  have hetaC : 1 < eta * (C₀ : ℝ) := by
    have h := (div_lt_iff₀ heta).mp hCeta
    have hcast : (Ceta : ℝ) ≤ C₀ := by exact_mod_cast hCetaC
    nlinarith
  have htailC : 1 < cLLL * (C₀ : ℝ) := by
    have h := (div_lt_iff₀ hcLLL).mp hCtail
    have hcast : (Ctail : ℝ) ≤ C₀ := by exact_mod_cast hCtailC
    nlinarith
  have hqpow : 0 < q ^ s := pow_pos hq0 s
  let delta : ℝ := eta * q ^ s / 2
  have hdelta : 0 < delta := by positivity
  let main : ℝ := theta * (1 - q)⁻¹ + (k : ℝ) * q ^ s
  let slack : ℝ := 1 + epsilon - main
  have hslack : 0 < slack := by simpa [slack, main] using sub_pos.mpr hbudget
  let B : ℝ := (1 - q)⁻¹
  let additive : ℝ := theta * (s : ℝ) * B + (k : ℝ) * B + 1
  obtain ⟨Dcap, hDcap⟩ := exists_nat_gt ((C₀ : ℝ) / q ^ s)
  obtain ⟨Dcolor, hDcolor⟩ := exists_nat_gt (additive / slack)
  let D₁ := max Dcap Dcolor
  refine ⟨delta, hdelta, D₁, ?_⟩
  intro D hD
  have hDcaple : Dcap ≤ D := (le_max_left _ _).trans hD
  have hDcolorle : Dcolor ≤ D := (le_max_right _ _).trans hD
  have hlargeGeom : (C₀ : ℝ) < q ^ s * (D : ℝ) := by
    have hquot : (C₀ : ℝ) / q ^ s < (D : ℝ) :=
      hDcap.trans_le (by exact_mod_cast hDcaple)
    have := (div_lt_iff₀ hqpow).1 hquot
    simpa [mul_comm] using this
  have hlargeColor : additive < slack * (D : ℝ) := by
    have hquot : additive / slack < (D : ℝ) :=
      hDcolor.trans_le (by exact_mod_cast hDcolorle)
    have := (div_lt_iff₀ hslack).1 hquot
    simpa [mul_comm] using this
  let cap : ℕ → ℕ := ceilGeometricCap q D
  let batch : ℕ → ℕ := fun i ↦ ⌊theta * (cap i : ℝ)⌋₊
  let dep : ℕ → ℕ := fun i ↦
    (cap i * (k * cap i + 1) ^ (4 * L + 2)) * k
  let dev : ℕ → ℝ := fun i ↦ rho * (cap i : ℝ)
  let choice : ℕ → ℝ := fun i ↦
    2 * Real.exp (-cLLL * (cap i : ℝ))
  have hcapLarge : ∀ i, i < s → C₀ ≤ cap i := by
    intro i hi
    have hpowle : q ^ s ≤ q ^ i :=
      pow_le_pow_of_le_one hq0.le hq1.le (Nat.le_of_lt hi)
    have hgeom : q ^ s * (D : ℝ) ≤ q ^ i * (D : ℝ) := by gcongr
    have hcap := geometric_le_ceilGeometricCap hq0.le D i
    have hreal : (C₀ : ℝ) < (cap i : ℝ) := hlargeGeom.trans_le (hgeom.trans hcap)
    exact_mod_cast hreal.le
  refine ⟨{
    rounds := s
    degreeCap := cap
    batchSize := batch
    depDegree := dep
    deviation := dev
    lllChoice := choice
    cap_zero := by simp [cap]
    size_pos := ?_
    threshold_large := ?_
    cap_two := ?_
    eta_cap := ?_
    pair_near := ?_
    deviation_nonneg := ?_
    choice_nonneg := ?_
    choice_lt_one := ?_
    mean_step := ?_
    dependency_step := ?_
    lll_step := ?_
    color_bound := ?_
  }⟩
  · intro i hi
    change 0 < ⌊theta * (cap i : ℝ)⌋₊
    rw [Nat.floor_pos]
    have hcast : (C₀ : ℝ) ≤ cap i := by exact_mod_cast hcapLarge i hi
    exact (hthetaC.trans_le (mul_le_mul_of_nonneg_left hcast htheta.le)).le
  · intro i hi
    exact hD₀C.trans (hcapLarge i hi)
  · intro i hi
    exact htwoC.trans (hcapLarge i hi)
  · intro i hi
    have hcast : (C₀ : ℝ) ≤ cap i := by exact_mod_cast hcapLarge i hi
    exact hetaC.trans_le (mul_le_mul_of_nonneg_left hcast heta.le)
  · intro i hi
    have hpowle : q ^ s ≤ q ^ i :=
      pow_le_pow_of_le_one hq0.le hq1.le (Nat.le_of_lt hi)
    have hcap := geometric_le_ceilGeometricCap hq0.le D i
    dsimp [delta]
    have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
    have heta0 : 0 ≤ eta := heta.le
    nlinarith [mul_le_mul_of_nonneg_right hpowle hD0,
      mul_le_mul_of_nonneg_left hcap heta0]
  · intro i _
    exact mul_nonneg hrho.le (Nat.cast_nonneg _)
  · intro i _
    exact mul_nonneg (by norm_num) (Real.exp_nonneg _)
  · intro i hi
    have hcast : (C₀ : ℝ) ≤ cap i := by exact_mod_cast hcapLarge i hi
    have htail : 1 < cLLL * (cap i : ℝ) :=
      htailC.trans_le (mul_le_mul_of_nonneg_left hcast hcLLL.le)
    have hexp : Real.exp (-cLLL * (cap i : ℝ)) < 1 / 2 := by
      calc
        Real.exp (-cLLL * (cap i : ℝ)) < Real.exp (-1) := by
          exact Real.exp_lt_exp.mpr (by linarith)
        _ < 1 / 2 := Real.exp_neg_one_lt_half
    dsimp [choice]
    linarith
  · intro i hi
    have hCi : 0 < cap i :=
      lt_of_lt_of_le (by norm_num) (htwoC.trans (hcapLarge i hi))
    have hcast : (C₀ : ℝ) ≤ cap i := by exact_mod_cast hcapLarge i hi
    have hsigma : (1 - zeta) / (cap i : ℝ) ≤ rho := by
      apply (div_le_iff₀ (by exact_mod_cast hCi)).2
      exact hrhoC.le.trans
        (mul_le_mul_of_nonneg_left hcast hrho.le)
    have hstep :
        (cap i : ℝ) *
              (1 - (1 - zeta) / (cap i : ℝ)) ^ batch i + dev i ≤
            cap (i + 1) := by
      simpa [cap, batch, dev] using
        floor_batch_mean_le_ceil_contraction hCi htheta.le hrho.le hzeta0
          hzeta1.le hsigma hrate
    exact hstep.trans (by norm_num)
  · intro i _
    rfl
  · intro i hi
    have hm : 0 < batch i := by
      change 0 < ⌊theta * (cap i : ℝ)⌋₊
      rw [Nat.floor_pos]
      have hcast : (C₀ : ℝ) ≤ cap i := by exact_mod_cast hcapLarge i hi
      exact (hthetaC.trans_le (mul_le_mul_of_nonneg_left hcast htheta.le)).le
    have htail := floor_batch_tail_le_exp_linear htheta hrho.le hm
    have hp := hDlll (cap i) (hDlllC.trans (hcapLarge i hi))
      (lt_of_lt_of_le (by norm_num) (htwoC.trans (hcapLarge i hi)))
    dsimp only at hp
    calc
      Real.exp (-2 * dev i ^ 2 / (batch i : ℝ)) ≤
          Real.exp (-cLLL * (cap i : ℝ)) := by
        simpa [dev, batch, cLLL] using htail
      _ ≤ (2 * Real.exp (-cLLL * (cap i : ℝ))) *
          (1 - 2 * Real.exp (-cLLL * (cap i : ℝ))) ^ dep i := by
        simpa [dep] using hp
      _ = choice i * (1 - choice i) ^ dep i := by rfl
  · rw [outerColorCount_eq_sum]
    have hbatch := sum_floor_mul_ceilGeometricCap_le htheta.le hq0.le hq1 D s
    have hcapS := natCast_ceilGeometricCap_le hq0.le hq1 D s
    have htotal :
        ((∑ i ∈ range s, batch i) + k * cap s + 1 : ℕ) ≤
          main * (D : ℝ) + additive := by
      push_cast
      calc
        (∑ i ∈ range s, (batch i : ℝ)) + (k : ℝ) * (cap s : ℝ) + 1 ≤
            theta * (B * (D : ℝ) + (s : ℝ) * B) +
              (k : ℝ) * (q ^ s * (D : ℝ) + B) + 1 := by
          gcongr
          · simpa [batch, cap, B] using hbatch
        _ = main * (D : ℝ) + additive := by
          simp [main, additive, B]
          ring
    have hmain : main + slack = 1 + epsilon := by simp [slack]
    calc
      (((∑ i ∈ range s, batch i) + k * cap s + 1 : ℕ) : ℝ) ≤
          main * (D : ℝ) + additive := htotal
      _ = additive + main * (D : ℝ) := by ring
      _ ≤ slack * (D : ℝ) + main * (D : ℝ) :=
        by simpa [add_comm] using add_le_add_left hlargeColor.le (main * (D : ℝ))
      _ = main * (D : ℝ) + slack * (D : ℝ) := by ring
      _ = (1 + epsilon) * (D : ℝ) := by rw [← hmain]; ring

/-- The remaining analytic scheduling statement after fresh regular
completion has removed every hypergraph lower-degree invariant. -/
def CompletedOuterSchedulePrinciple : Prop :=
  ∀ k : ℕ, 0 < k → ∀ epsilon zeta eta : ℝ,
    0 < epsilon → 0 < zeta → zeta < 1 →
    zeta ≤ epsilon / 8 → zeta ≤ 1 / 2 → 0 < eta →
    ∀ L D₀ : ℕ, 0 < D₀ →
      ∃ delta : ℝ, 0 < delta ∧ ∃ D₁ : ℕ,
        ∀ D : ℕ, D₁ ≤ D →
          Nonempty (CompletedOuterSchedule k L D₀ zeta eta epsilon delta D)

/-- A small contraction rate with a prescribed amount of colour-budget
slack.  This isolates the quadratic estimate for `exp` from the outer
quantifier bookkeeping. -/
lemma exists_small_outer_contraction
    {a b : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b) :
    ∃ theta rho q : ℝ,
      0 < theta ∧ 0 < rho ∧ 0 < q ∧ q < 1 ∧
      Real.exp (-(a * theta - rho)) + rho ≤ q ∧
      theta * (1 - q)⁻¹ ≤ a⁻¹ + b / 4 := by
  let theta : ℝ := min (a / 100) (b * a ^ 2 / 100) / 2
  have htheta : 0 < theta := by
    dsimp [theta]
    exact div_pos (lt_min (div_pos ha (by norm_num)) (by positivity)) (by norm_num)
  have hthetaA : theta ≤ a / 200 := by
    have hmin := min_le_left (a / 100) (b * a ^ 2 / 100)
    dsimp [theta]
    linarith
  have hthetaB : theta ≤ b * a ^ 2 / 200 := by
    have hmin := min_le_right (a / 100) (b * a ^ 2 / 100)
    dsimp [theta]
    linarith
  have htheta_lt_a : theta < a := by nlinarith
  have htheta_le_one : theta ≤ 1 / 200 := by nlinarith
  let rho : ℝ := theta ^ 2
  have hrho : 0 < rho := by dsimp [rho]; positivity
  let x : ℝ := a * theta - rho
  have hxFactor : x = theta * (a - theta) := by
    simp [x, rho]
    ring
  have hx : 0 < x := by rw [hxFactor]; positivity
  have hxTheta : x ≤ theta := by
    have hatheta : a * theta ≤ theta := by
      simpa using mul_le_mul_of_nonneg_right ha1 htheta.le
    dsimp [x, rho]
    nlinarith [sq_nonneg theta]
  have hxOne : |x| ≤ 1 := by
    rw [abs_of_pos hx]
    linarith
  let q : ℝ := 1 - x + x ^ 2 + rho
  let u : ℝ := x - x ^ 2 - rho
  have hqU : q = 1 - u := by simp [q, u]; ring
  have hxSq : x ^ 2 ≤ theta ^ 2 := by nlinarith
  have huLower : theta * (a - 3 * theta) ≤ u := by
    simp [u, x, rho]
    nlinarith [hxSq]
  have haThreeTheta : 0 < a - 3 * theta := by nlinarith
  have hu : 0 < u := (mul_pos htheta haThreeTheta).trans_le huLower
  have huTheta : u ≤ theta := by
    have huX : u ≤ x := by dsimp [u]; nlinarith [sq_nonneg x, hrho.le]
    exact huX.trans hxTheta
  have huOne : u < 1 := lt_of_le_of_lt huTheta (by linarith)
  have hq0 : 0 < q := by rw [hqU]; linarith
  have hq1 : q < 1 := by rw [hqU]; linarith
  have hexpError := Real.abs_exp_sub_one_sub_id_le (x := -x) (by simpa using hxOne)
  have hexpUpper : Real.exp (-x) ≤ 1 - x + x ^ 2 := by
    have hle : Real.exp (-x) - 1 + x ≤ x ^ 2 := by
      have := (le_abs_self (Real.exp (-x) - 1 + x)).trans
        (by simpa [sub_eq_add_neg] using hexpError)
      simpa using this
    linarith
  have hrate : Real.exp (-(a * theta - rho)) + rho ≤ q := by
    have := add_le_add_right hexpUpper rho
    simpa [x, q] using this
  have hbaTheta : b * a * theta ≤ b * a ^ 2 / 200 := by
    have hmul := mul_le_mul_of_nonneg_left hthetaA (mul_nonneg hb.le ha.le)
    nlinarith
  have hcore : a ≤ (1 + b * a / 4) * (a - 3 * theta) := by
    nlinarith [hthetaB, hbaTheta, mul_pos hb ha]
  have hRcore : 1 ≤ (a⁻¹ + b / 4) * (a - 3 * theta) := by
    have hdiv := (div_le_div_iff_of_pos_right ha).2 hcore
    calc
      1 = a / a := by field_simp
      _ ≤ ((1 + b * a / 4) * (a - 3 * theta)) / a := hdiv
      _ = (a⁻¹ + b / 4) * (a - 3 * theta) := by field_simp
  have hR0 : 0 ≤ a⁻¹ + b / 4 := by positivity
  have hthetaRu : theta ≤ (a⁻¹ + b / 4) * u := by
    calc
      theta = theta * 1 := by ring
      _ ≤ theta * ((a⁻¹ + b / 4) * (a - 3 * theta)) :=
        mul_le_mul_of_nonneg_left hRcore htheta.le
      _ = (a⁻¹ + b / 4) * (theta * (a - 3 * theta)) := by ring
      _ ≤ (a⁻¹ + b / 4) * u :=
        mul_le_mul_of_nonneg_left huLower hR0
  have hbatchBudget : theta * (1 - q)⁻¹ ≤ a⁻¹ + b / 4 := by
    have hdiv : theta / u ≤ a⁻¹ + b / 4 :=
      (div_le_iff₀ hu).2 (by simpa [mul_comm] using hthetaRu)
    rw [hqU]
    simpa [div_eq_mul_inv] using hdiv
  exact ⟨theta, rho, q, htheta, hrho, hq0, hq1, hrate, hbatchBudget⟩

/-- The pure scalar scheduling principle.  The proof chooses a sufficiently
small batch rate, absorbs the quadratic exponential error into the cap
contraction, and then runs a fixed number of rounds until the greedy residual
term fits into the remaining colour budget. -/
theorem completedOuterSchedulePrinciple : CompletedOuterSchedulePrinciple := by
  intro k hk epsilon zeta eta hepsilon hzeta0 hzeta1
    hzetaEpsilon hzetaHalf heta L D₀ _hD₀
  let a : ℝ := 1 - zeta
  have ha : 0 < a := by simpa [a] using sub_pos.mpr hzeta1
  have ha1 : a ≤ 1 := by dsimp [a]; linarith
  have hzetaProduct : zeta * (1 + epsilon) < epsilon := by
    by_cases hepsOne : epsilon ≤ 1
    · have hone : 1 + epsilon ≤ 2 := by linarith
      have hprod : zeta * (1 + epsilon) ≤ (epsilon / 8) * 2 :=
        mul_le_mul hzetaEpsilon hone (by positivity) (by positivity)
      nlinarith
    · have hone : 1 < epsilon := lt_of_not_ge hepsOne
      have hprod : zeta * (1 + epsilon) ≤ (1 / 2 : ℝ) * (1 + epsilon) :=
        mul_le_mul_of_nonneg_right hzetaHalf (by positivity)
      nlinarith
  have hinvBudget : a⁻¹ < 1 + epsilon := by
    apply (inv_lt_iff_one_lt_mul₀' ha).2
    dsimp [a]
    nlinarith [hzetaProduct]
  let b : ℝ := 1 + epsilon - a⁻¹
  have hb : 0 < b := by simpa [b] using sub_pos.mpr hinvBudget
  obtain ⟨theta, rho, q, htheta, hrho, hq0, hq1, hrateA, hbatchBudget⟩ :=
    exists_small_outer_contraction ha ha1 hb
  have hrate : Real.exp (-((1 - zeta) * theta - rho)) + rho ≤ q := by
    simpa [a] using hrateA
  have htarget : 0 < b / (4 * ((k : ℝ) + 1)) := by positivity
  obtain ⟨s, hs⟩ := exists_pow_lt_of_lt_one htarget hq1
  have hkReal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hresidual : (k : ℝ) * q ^ s < b / 4 := by
    have hfirst : (k : ℝ) * q ^ s <
        (k : ℝ) * (b / (4 * ((k : ℝ) + 1))) :=
      mul_lt_mul_of_pos_left hs hkReal
    have htargetPos : 0 < b / (4 * ((k : ℝ) + 1)) := htarget
    calc
      (k : ℝ) * q ^ s <
          (k : ℝ) * (b / (4 * ((k : ℝ) + 1))) := hfirst
      _ < ((k : ℝ) + 1) * (b / (4 * ((k : ℝ) + 1))) := by
        gcongr
        norm_num
      _ = b / 4 := by field_simp
  have hinvAdd : a⁻¹ + b = 1 + epsilon := by simp [b]
  have hbHalf : b / 2 < b := by linarith only [hb]
  have hbudget : theta * (1 - q)⁻¹ + (k : ℝ) * q ^ s < 1 + epsilon := by
    calc
      theta * (1 - q)⁻¹ + (k : ℝ) * q ^ s =
          (k : ℝ) * q ^ s + theta * (1 - q)⁻¹ := by ring
      _ ≤ (k : ℝ) * q ^ s + (a⁻¹ + b / 4) :=
        add_le_add_right hbatchBudget ((k : ℝ) * q ^ s)
      _ < b / 4 + (a⁻¹ + b / 4) :=
        add_lt_add_left hresidual (a⁻¹ + b / 4)
      _ = (a⁻¹ + b / 4) + b / 4 := by ring
      _ = a⁻¹ + b / 2 := by ring
      _ = b / 2 + a⁻¹ := by ring
      _ < b + a⁻¹ := add_lt_add_left hbHalf a⁻¹
      _ = a⁻¹ + b := by ring
      _ = 1 + epsilon := hinvAdd
  exact exists_completedOuterSchedule_of_rates
    (k := k) (L := L) (D₀ := D₀) (s := s)
    (zeta := zeta) (eta := eta) (epsilon := epsilon)
    (theta := theta) (rho := rho) (q := q)
    hepsilon heta hzeta0.le hzeta1 htheta hrho hq0 hq1 hrate hbudget

/-- Final finite assembly from the exact-regular sharp inner marginal and the
pure fresh-completion scalar schedule. -/
theorem sharpExactRegularTwoSidedFixedLengthInnerMarginal_to_nearRegular_of_completedSchedule
    (hinner : SharpExactRegularTwoSidedFixedLengthInnerMarginal)
    (hschedule : CompletedOuterSchedulePrinciple) :
    NearRegularPippengerSpencerEdgeColoring := by
  intro k hk epsilon hepsilon
  let zeta : ℝ := min (epsilon / 8) (1 / 2)
  have hzeta0 : 0 < zeta := lt_min (div_pos hepsilon (by norm_num)) (by norm_num)
  have hzeta1 : zeta < 1 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨eta, heta0, _heta1, L, D₀, hD₀, hgenerator⟩ :=
    hinner k hk zeta hzeta0 hzeta1
  obtain ⟨delta, hdelta, D₁, hschedules⟩ :=
    hschedule k hk epsilon zeta eta hepsilon hzeta0 hzeta1
      (min_le_left _ _) (min_le_right _ _) heta0 L D₀ hD₀
  refine ⟨delta, hdelta, D₁, ?_⟩
  intro V' E' _ _ _ H D hDlarge hunif _hdegreeLower hdegree hpair
  obtain ⟨S⟩ := hschedules D hDlarge
  have hdegreeCap : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ S.degreeCap 0 := by
    simpa [S.cap_zero] using hdegree
  have hc := exists_edgeColoring_of_completedMarginal_schedule
    hgenerator hk S.degreeCap S.batchSize S.depDegree S.deviation S.lllChoice
    hzeta0.le hzeta1.le S.size_pos S.threshold_large S.cap_two heta0.le
    S.eta_cap S.pair_near S.deviation_nonneg S.choice_nonneg S.choice_lt_one
    S.mean_step S.dependency_step S.lll_step H hunif hdegreeCap hpair
  refine ⟨outerColorCount k S.degreeCap S.batchSize S.rounds, ?_, S.color_bound, hc⟩
  rw [outerColorCount_eq_sum]
  omega

/-- The exact-regular sharp fixed-length two-sided inner marginal implies the
near-regular Pippenger--Spencer edge-colouring theorem.  All outer scheduling
and fresh regular-completion bookkeeping has been discharged above. -/
theorem sharpExactRegularTwoSidedFixedLengthInnerMarginal_to_nearRegular
    (hinner : SharpExactRegularTwoSidedFixedLengthInnerMarginal) :
    NearRegularPippengerSpencerEdgeColoring :=
  sharpExactRegularTwoSidedFixedLengthInnerMarginal_to_nearRegular_of_completedSchedule
    hinner completedOuterSchedulePrinciple

/-- Compatibility wrapper for the earlier, stronger near-regular inner
marginal interface. -/
theorem sharpTwoSidedFixedLengthInnerMarginal_to_nearRegular_of_completedSchedule
    (hinner : SharpTwoSidedFixedLengthInnerMarginal)
    (hschedule : CompletedOuterSchedulePrinciple) :
    NearRegularPippengerSpencerEdgeColoring :=
  sharpExactRegularTwoSidedFixedLengthInnerMarginal_to_nearRegular_of_completedSchedule
    (sharpTwoSidedFixedLengthInnerMarginal_to_exactRegular hinner) hschedule

/-- Compatibility wrapper for the earlier, stronger near-regular inner
marginal interface. -/
theorem sharpTwoSidedFixedLengthInnerMarginal_to_nearRegular
    (hinner : SharpTwoSidedFixedLengthInnerMarginal) :
    NearRegularPippengerSpencerEdgeColoring :=
  sharpExactRegularTwoSidedFixedLengthInnerMarginal_to_nearRegular
    (sharpTwoSidedFixedLengthInnerMarginal_to_exactRegular hinner)

/-- A completely numerical certificate which can be fed to
`exists_edgeColoring_of_fixedLengthMarginal_schedule`. -/
structure FixedLengthOuterSchedule
    (k L D₀ : ℕ) (zeta eta epsilon delta : ℝ) (D : ℕ) where
  rounds : ℕ
  degreeFloor : ℕ → ℕ
  degreeCap : ℕ → ℕ
  batchSize : ℕ → ℕ
  depDegree : ℕ → ℕ
  deviation : ℕ → ℝ
  lllChoice : ℕ → ℝ
  cap_zero : degreeCap 0 = D
  initialFloor_le : (degreeFloor 0 : ℝ) ≤ (1 - delta) * (D : ℝ)
  size_pos : ∀ i, i < rounds → 0 < batchSize i
  threshold_large : ∀ i, i < rounds → D₀ ≤ degreeCap i
  cap_pos : ∀ i, i < rounds → 0 < degreeCap i
  lower_near : ∀ i, i < rounds →
    (1 - eta) * (degreeCap i : ℝ) ≤ degreeFloor i
  pair_near : ∀ i, i < rounds →
    delta * (D : ℝ) ≤ eta * (degreeCap i : ℝ)
  lower_step : ∀ i, i < rounds →
    degreeFloor (i + 1) ≤ degreeFloor i - batchSize i
  deviation_nonneg : ∀ i, i < rounds → 0 ≤ deviation i
  choice_nonneg : ∀ i, i < rounds → 0 ≤ lllChoice i
  choice_lt_one : ∀ i, i < rounds → lllChoice i < 1
  mean_step : ∀ i, i < rounds →
    (degreeCap i : ℝ) *
        (1 - (1 - zeta) / (degreeCap i : ℝ)) ^ batchSize i + deviation i ≤
      degreeCap (i + 1) + 1
  dependency_step : ∀ i, i < rounds →
    (degreeCap i * (k * degreeCap i + 1) ^ (4 * L + 2)) * k ≤ depDegree i
  lll_step : ∀ i, i < rounds →
    Real.exp (-2 * deviation i ^ 2 / (batchSize i : ℝ)) ≤
      lllChoice i * (1 - lllChoice i) ^ depDegree i
  color_bound :
    (outerColorCount k degreeCap batchSize rounds : ℝ) ≤
      (1 + epsilon) * (D : ℝ)

/-- Pure analytic statement still needed after the checked finite argument.
It contains no hypergraphs or probability spaces. -/
def SharpOuterSchedulePrinciple : Prop :=
  ∀ k : ℕ, 0 < k → ∀ epsilon zeta eta : ℝ,
    0 < epsilon → 0 < zeta → zeta < 1 → 0 < eta → eta < 1 →
    ∀ L D₀ : ℕ, 0 < D₀ →
      ∃ delta : ℝ, 0 < delta ∧ ∃ D₁ : ℕ,
        ∀ D : ℕ, D₁ ≤ D →
          Nonempty (FixedLengthOuterSchedule k L D₀ zeta eta epsilon delta D)

/-- Exact final assembly, conditional only on the sharp inner marginal and
the separately pure scalar schedule principle. -/
theorem sharpFixedLengthInnerMarginal_to_nearRegular_of_schedulePrinciple
    (hinner : SharpFixedLengthInnerMarginal)
    (hschedule : SharpOuterSchedulePrinciple) :
    NearRegularPippengerSpencerEdgeColoring := by
  intro k hk epsilon hepsilon
  let zeta : ℝ := min (epsilon / 8) (1 / 2)
  have hzeta0 : 0 < zeta := lt_min (div_pos hepsilon (by norm_num)) (by norm_num)
  have hzeta1 : zeta < 1 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨eta, heta0, heta1, L, D₀, hD₀, hgenerator⟩ :=
    hinner k hk zeta hzeta0 hzeta1
  obtain ⟨delta, hdelta, D₁, hschedules⟩ :=
    hschedule k hk epsilon zeta eta hepsilon hzeta0 hzeta1 heta0 heta1 L D₀ hD₀
  refine ⟨delta, hdelta, D₁, ?_⟩
  intro V' E' _ _ _ H D hDlarge hunif hdegreeLower hdegree hpair
  obtain ⟨S⟩ := hschedules D hDlarge
  have hdegreeFloor : ∀ v ∈ H.vertexSet,
      S.degreeFloor 0 ≤ H.edgeDegree v := by
    intro v hv
    exact_mod_cast S.initialFloor_le.trans (hdegreeLower v hv)
  have hdegreeCap : ∀ v ∈ H.vertexSet,
      H.edgeDegree v ≤ S.degreeCap 0 := by
    simpa [S.cap_zero] using hdegree
  have hc := exists_edgeColoring_of_fixedLengthMarginal_schedule
    hgenerator S.degreeFloor S.degreeCap S.batchSize S.depDegree
    S.deviation S.lllChoice hzeta0.le hzeta1.le S.size_pos S.threshold_large
    S.cap_pos S.lower_near S.pair_near S.lower_step S.deviation_nonneg
    S.choice_nonneg S.choice_lt_one S.mean_step S.dependency_step S.lll_step
    H hunif hdegreeFloor hdegreeCap hpair
  refine ⟨outerColorCount k S.degreeCap S.batchSize S.rounds, ?_, S.color_bound, hc⟩
  rw [outerColorCount_eq_sum]
  omega

end FiniteHypergraph

end

end Erdos76
