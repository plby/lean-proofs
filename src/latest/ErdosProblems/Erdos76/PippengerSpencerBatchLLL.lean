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
import ErdosProblems.Erdos76.PippengerSpencerBatchConcentration
import ErdosProblems.Erdos76.PippengerSpencerLocality

/-!
# A local-lemma batch for Pippenger--Spencer

This file joins the three independent ingredients of the outer nibble:

* the geometric expectation bound for a residual vertex degree;
* its one-sided McDiarmid estimate;
* locality of the residual-degree event in the flattened Bernoulli coordinates.

The first part records explicitly that a Bernoulli subset of `J × E` is the
same finite probability space as a `J`-indexed family of Bernoulli subsets of
`E`.  This bridge lets the concentration theorem, stated on the family model,
provide the marginal hypothesis for the finite local lemma, stated on the
flattened model.
-/

open Finset Real
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

namespace FiniteHypergraph

variable {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Flatten a family of finite subsets into its incidence subset of `J × E`. -/
def flattenBatch {J : Type*} [Fintype J] [DecidableEq J]
    (X : J → Finset E) : Finset (J × E) :=
  (Finset.univ : Finset (J × E)).filter fun z ↦ z.2 ∈ X z.1

@[simp] lemma mem_flattenBatch {J : Type*} [Fintype J] [DecidableEq J]
    (X : J → Finset E) (z : J × E) :
    z ∈ flattenBatch X ↔ z.2 ∈ X z.1 := by
  simp [flattenBatch]

@[simp] lemma batchAt_flattenBatch {J : Type*} [Fintype J] [DecidableEq J]
    (X : J → Finset E) (j : J) :
    batchAt (flattenBatch X) j = X j := by
  ext e
  simp

@[simp] lemma flattenBatch_batchAt {J : Type*} [Fintype J] [DecidableEq J]
    (Z : Finset (J × E)) :
    flattenBatch (fun j ↦ batchAt Z j) = Z := by
  ext z
  simp

/-- Equivalence between the family and flattened presentations of a batch. -/
def batchFinsetEquiv {J : Type*} [Fintype J] [DecidableEq J] :
    (J → Finset E) ≃ Finset (J × E) where
  toFun := flattenBatch
  invFun Z := fun j ↦ batchAt Z j
  left_inv X := by funext j; exact batchAt_flattenBatch X j
  right_inv := flattenBatch_batchAt

/-- On the full finite coordinate space, Bernoulli mass is the product of
the coordinatewise selected/unselected factors. -/
lemma bernoulliMass_univ_eq_prod_ite
    {A : Type*} [Fintype A] [DecidableEq A]
    (prob : A → ℝ) (S : Finset A) :
    FiniteNibble.bernoulliMass Finset.univ prob S =
      ∏ a : A, if a ∈ S then prob a else 1 - prob a := by
  rw [FiniteNibble.bernoulliMass]
  calc
    (∏ a ∈ S, prob a) * ∏ a ∈ (Finset.univ : Finset A) \ S, (1 - prob a) =
        (∏ a : A, if a ∈ S then prob a else 1) *
          ∏ a : A, if a ∈ (Finset.univ : Finset A) \ S then 1 - prob a else 1 := by
      rw [Finset.prod_ite_mem, Finset.prod_ite_mem]
      simp
    _ = ∏ a : A,
          (if a ∈ S then prob a else 1) *
            (if a ∈ (Finset.univ : Finset A) \ S then 1 - prob a else 1) := by
      rw [Finset.prod_mul_distrib]
    _ = ∏ a : A, if a ∈ S then prob a else 1 - prob a := by
      apply Finset.prod_congr rfl
      intro a _
      by_cases ha : a ∈ S <;> simp [ha]

/-- Flattening preserves the complete Bernoulli product mass. -/
lemma bernoulliMass_flattenBatch
    {J : Type*} [Fintype J] [DecidableEq J]
    (prob : E → ℝ) (X : J → Finset E) :
    FiniteNibble.bernoulliMass Finset.univ (fun z : J × E ↦ prob z.2)
        (flattenBatch X) =
      FiniteProduct.productMass
        (FiniteNibble.bernoulliMass Finset.univ prob) X := by
  rw [bernoulliMass_univ_eq_prod_ite]
  rw [Fintype.prod_prod_type]
  unfold FiniteProduct.productMass
  apply Finset.prod_congr rfl
  intro j _
  rw [bernoulliMass_univ_eq_prod_ite]
  apply Finset.prod_congr rfl
  intro e _
  simp

/-- Event masses agree under the family/flattened batch equivalence. -/
lemma eventMass_flattenBatch
    {J : Type*} [Fintype J] [DecidableEq J]
    (prob : E → ℝ) (event : Finset (J × E) → Prop) :
    FiniteLocalLemma.eventMass
        (fun Z : Finset (J × E) ↦
          FiniteNibble.bernoulliMass Finset.univ (fun z : J × E ↦ prob z.2) Z)
        event =
      FiniteLocalLemma.eventMass
        (FiniteProduct.productMass
          (FiniteNibble.bernoulliMass Finset.univ prob))
        (fun X : J → Finset E ↦ event (flattenBatch X)) := by
  unfold FiniteLocalLemma.eventMass
  symm
  apply Fintype.sum_equiv (batchFinsetEquiv (E := E))
  intro X
  change (if event (flattenBatch X) then
      FiniteProduct.productMass (FiniteNibble.bernoulliMass Finset.univ prob) X else 0) =
    if event (flattenBatch X) then
      FiniteNibble.bernoulliMass Finset.univ (fun z : J × E ↦ prob z.2)
        (flattenBatch X) else 0
  by_cases h : event (flattenBatch X)
  · rw [if_pos h, if_pos h, bernoulliMass_flattenBatch]
  · rw [if_neg h, if_neg h]

/-- The flattened residual degree agrees with the original batch definition. -/
lemma flattenedBatchResidualDegree_flattenBatch
    {J : Type*} [Fintype J] [DecidableEq J]
    (H : FiniteHypergraph V E) (X : J → Finset E) (v : V) :
    H.flattenedBatchResidualDegree (flattenBatch X) v =
      H.batchResidualDegree X v := by
  change H.batchResidualDegree
      (fun j ↦ batchAt (flattenBatch X) j) v = H.batchResidualDegree X v
  congr 1
  funext j
  exact batchAt_flattenBatch X j

/-- The marginal mass of a flattened residual-degree bad event is exactly
the corresponding event mass in the product-of-trials presentation. -/
lemma eventMass_flattenedResidualDegreeBad_eq
    {J : Type*} [Fintype J] [DecidableEq J]
    (H : FiniteHypergraph V E) (prob : E → ℝ)
    (threshold : ↥H.vertexSet → ℕ) (v : ↥H.vertexSet) :
    FiniteLocalLemma.eventMass
        (fun Z : Finset (J × E) ↦
          FiniteNibble.bernoulliMass Finset.univ (fun z : J × E ↦ prob z.2) Z)
        (H.flattenedResidualDegreeBad threshold v) =
      FiniteLocalLemma.eventMass
        (FiniteProduct.productMass
          (FiniteNibble.bernoulliMass Finset.univ prob))
        (fun X : J → Finset E ↦
          (threshold v : ℝ) ≤ (H.batchResidualDegree X v.1 : ℝ)) := by
  rw [eventMass_flattenBatch]
  unfold FiniteLocalLemma.eventMass
  apply Finset.sum_congr rfl
  intro X _
  have hdegree := H.flattenedBatchResidualDegree_flattenBatch X v.1
  by_cases hbad : threshold v ≤ H.batchResidualDegree X v.1
  · have hbadR : (threshold v : ℝ) ≤ (H.batchResidualDegree X v.1 : ℝ) := by
      exact_mod_cast hbad
    simp [FiniteHypergraph.flattenedResidualDegreeBad, hdegree, hbad, hbadR]
  · have hbadR : ¬ (threshold v : ℝ) ≤ (H.batchResidualDegree X v.1 : ℝ) := by
      exact_mod_cast hbad
    simp [FiniteHypergraph.flattenedResidualDegreeBad, hdegree, hbad, hbadR]

/-- One Pippenger--Spencer batch: a uniform one-trial acceptance lower bound,
McDiarmid concentration, and the symmetric local lemma give one batch whose
residual degree is below the prescribed threshold at every active vertex. -/
theorem exists_batchResidualDegree_lt_of_lll
    {J : Type*} [Fintype J] [Nonempty J]
    (H : FiniteHypergraph V E) (prob : E → ℝ)
    (hprob0 : ∀ e, 0 ≤ prob e) (hprob1 : ∀ e, prob e ≤ 1)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (haccept : ∀ e, a ≤ FiniteNibble.trialAcceptanceMass H prob e)
    (threshold : ↥H.vertexSet → ℕ) {t x : ℝ} {d : ℕ}
    (ht : 0 ≤ t) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hthreshold : ∀ v : ↥H.vertexSet,
      (H.edgeDegree v.1 : ℝ) * (1 - a) ^ Fintype.card J + t ≤ threshold v)
    (hdegree : ∀ v : ↥H.vertexSet,
      (H.vertexInfluenceDependency v).card ≤ d)
    (hparameter : Real.exp (-2 * t ^ 2 / (Fintype.card J : ℝ)) ≤
      x * (1 - x) ^ d) :
    ∃ X : J → Finset E, ∀ v : ↥H.vertexSet,
      H.batchResidualDegree X v.1 < threshold v := by
  letI : DecidableEq J := Classical.decEq J
  let flatProb : J × E → ℝ := fun z ↦ prob z.2
  let flatMass : Finset (J × E) → ℝ := fun Z ↦
    FiniteNibble.bernoulliMass Finset.univ flatProb Z
  let bad : ↥H.vertexSet → Finset (J × E) → Prop :=
    H.flattenedResidualDegreeBad threshold
  have hmass0 : ∀ Z, 0 ≤ flatMass Z := by
    intro Z
    exact FiniteNibble.bernoulliMass_nonneg (subset_univ Z)
      (fun z _ ↦ hprob0 z.2) (fun z _ ↦ hprob1 z.2)
  have hmass : ∑ Z, flatMass Z = 1 := by
    simpa [flatMass] using
      (FiniteNibble.sum_bernoulliMass (Finset.univ : Finset (J × E)) flatProb)
  have hindep : FiniteLocalLemma.IndependentOutside flatMass bad
      H.vertexInfluenceDependency := by
    simpa [flatMass, flatProb, bad] using
      H.flattenedResidualDegreeBad_independentOutside flatProb threshold
  have hmarginal : ∀ v, FiniteLocalLemma.eventMass flatMass (bad v) ≤
      Real.exp (-2 * t ^ 2 / (Fintype.card J : ℝ)) := by
    intro v
    rw [show FiniteLocalLemma.eventMass flatMass (bad v) =
        FiniteLocalLemma.eventMass
          (FiniteProduct.productMass
            (FiniteNibble.bernoulliMass Finset.univ prob))
          (fun X : J → Finset E ↦
            (threshold v : ℝ) ≤ (H.batchResidualDegree X v.1 : ℝ)) by
      simpa [flatMass, flatProb, bad] using
        H.eventMass_flattenedResidualDegreeBad_eq prob threshold v]
    apply H.eventMass_product_batchResidualDegree_ge_le v.1
      (FiniteNibble.bernoulliMass Finset.univ prob)
    · intro S
      exact FiniteNibble.bernoulliMass_nonneg (subset_univ S)
        (fun e _ ↦ hprob0 e) (fun e _ ↦ hprob1 e)
    · simpa using
        (FiniteNibble.sum_bernoulliMass (Finset.univ : Finset E) prob)
    · exact ht
    · calc
        FiniteProduct.productExpectation
              (FiniteNibble.bernoulliMass Finset.univ prob)
              (fun X : J → Finset E ↦ (H.batchResidualDegree X v.1 : ℝ)) + t ≤
            (H.edgeDegree v.1 : ℝ) * (1 - a) ^ Fintype.card J + t :=
          by
            simpa [add_comm] using
              (add_le_add_right
                (FiniteNibble.productExpectation_batchResidualDegree_le H
                  (J := J) hprob0 hprob1 ha0 ha1 haccept v.1) t)
        _ ≤ (threshold v : ℝ) := hthreshold v
  obtain ⟨Z, hZ⟩ := FiniteLocalLemma.exists_avoiding_all_of_independentOutside
    flatMass hmass0 hmass bad H.vertexInfluenceDependency
    (Real.exp_nonneg _) hx0 hx1 hparameter hdegree hindep hmarginal
  refine ⟨fun j ↦ batchAt Z j, ?_⟩
  intro v
  have hnot := hZ v
  change ¬ threshold v ≤ H.flattenedBatchResidualDegree Z v.1 at hnot
  change H.flattenedBatchResidualDegree Z v.1 < threshold v
  exact Nat.lt_of_not_ge hnot

/-- Constant sampling specialization.  Uniformity and the maximum vertex
degree hypothesis supply both the elementary acceptance bound and the
polynomial dependency-degree bound. -/
theorem exists_batchResidualDegree_const_lt_of_lll
    {J : Type*} [Fintype J] [Nonempty J]
    {H : FiniteHypergraph V E} {k D : ℕ}
    (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    {prob : ℝ} (hprob0 : 0 ≤ prob) (hprob1 : prob ≤ 1)
    (ha0 : 0 ≤ prob - ((k * D : ℕ) : ℝ) * prob ^ 2)
    (ha1 : prob - ((k * D : ℕ) : ℝ) * prob ^ 2 ≤ 1)
    (threshold : ↥H.vertexSet → ℕ) {t x : ℝ}
    (ht : 0 ≤ t) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hthreshold : ∀ v : ↥H.vertexSet,
      (H.edgeDegree v.1 : ℝ) *
          (1 - (prob - ((k * D : ℕ) : ℝ) * prob ^ 2)) ^ Fintype.card J + t ≤
        threshold v)
    (hparameter : Real.exp (-2 * t ^ 2 / (Fintype.card J : ℝ)) ≤
      x * (1 - x) ^ ((D * (k * D + 1) ^ 2) * k)) :
    ∃ X : J → Finset E, ∀ v : ↥H.vertexSet,
      H.batchResidualDegree X v.1 < threshold v := by
  letI : DecidableEq J := Classical.decEq J
  apply H.exists_batchResidualDegree_lt_of_lll (fun _ ↦ prob)
    (fun _ ↦ hprob0) (fun _ ↦ hprob1) ha0 ha1
    (fun e ↦ FiniteNibble.trialAcceptanceMass_const_ge
      hunif hdeg hprob0 hprob1 e)
    threshold ht hx0 hx1 hthreshold
    (fun v ↦ H.vertexInfluenceDependency_card_le hunif hdeg v)
    hparameter

end FiniteHypergraph

end

end Erdos76
