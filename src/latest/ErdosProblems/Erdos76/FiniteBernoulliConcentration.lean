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
import ErdosProblems.Erdos76.Kahn
import ErdosProblems.Erdos76.FiniteBernoulliVariance
import Mathlib.Tactic

/-!
# Simultaneous finite Bernoulli degree and codegree concentration

This file packages the variance calculation for the incidence sets of a
finite hypergraph.  A single sample is extracted for which only a controlled
number of vertices and distinct ordered vertex pairs have a large deviation.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

namespace FiniteHypergraph

variable {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Indexed edges incident with a specified vertex. -/
def incidentEdges (H : FiniteHypergraph V E) (v : V) : Finset E :=
  (univ : Finset E).filter fun e ↦ v ∈ H.support e

/-- Indexed edges incident with both specified vertices. -/
def pairIncidentEdges (H : FiniteHypergraph V E) (u v : V) : Finset E :=
  (univ : Finset E).filter fun e ↦ u ∈ H.support e ∧ v ∈ H.support e

@[simp] lemma card_incidentEdges (H : FiniteHypergraph V E) (v : V) :
    (H.incidentEdges v).card = H.edgeDegree v := rfl

@[simp] lemma card_pairIncidentEdges (H : FiniteHypergraph V E) (u v : V) :
    (H.pairIncidentEdges u v).card = H.edgePairDegree u v := rfl

/-- Degree in a selected subfamily of indexed edges. -/
def sampledEdgeDegree (H : FiniteHypergraph V E) (S : Finset E) (v : V) : ℕ :=
  (S.filter fun e ↦ v ∈ H.support e).card

/-- Codegree in a selected subfamily of indexed edges. -/
def sampledEdgePairDegree (H : FiniteHypergraph V E) (S : Finset E)
    (u v : V) : ℕ :=
  (S.filter fun e ↦ u ∈ H.support e ∧ v ∈ H.support e).card

/-- Expected sampled degree under independent, non-identical edge selection. -/
def expectedSampledEdgeDegree (H : FiniteHypergraph V E) (p : E → ℝ) (v : V) : ℝ :=
  ∑ e ∈ H.incidentEdges v, p e

/-- Expected sampled codegree under independent, non-identical edge selection. -/
def expectedSampledEdgePairDegree (H : FiniteHypergraph V E) (p : E → ℝ)
    (u v : V) : ℝ :=
  ∑ e ∈ H.pairIncidentEdges u v, p e

lemma centeredSum_incidentEdges (H : FiniteHypergraph V E) (p : E → ℝ)
    (S : Finset E) (v : V) :
    FiniteNibble.centeredSum univ p (H.incidentEdges v) S =
      (H.sampledEdgeDegree S v : ℝ) - H.expectedSampledEdgeDegree p v := by
  simp [FiniteNibble.centeredSum, FiniteNibble.bernoulliIndicator,
    sampledEdgeDegree, expectedSampledEdgeDegree, incidentEdges,
    sum_sub_distrib, ← sum_filter, filter_filter, and_comm]
  congr 1
  ext e
  simp [and_comm]

lemma centeredSum_pairIncidentEdges (H : FiniteHypergraph V E) (p : E → ℝ)
    (S : Finset E) (u v : V) :
    FiniteNibble.centeredSum univ p (H.pairIncidentEdges u v) S =
      (H.sampledEdgePairDegree S u v : ℝ) -
        H.expectedSampledEdgePairDegree p u v := by
  simp [FiniteNibble.centeredSum, FiniteNibble.bernoulliIndicator,
    sampledEdgePairDegree, expectedSampledEdgePairDegree, pairIncidentEdges,
    sum_sub_distrib, ← sum_filter, filter_filter, and_assoc, and_left_comm, and_comm]
  congr 1
  ext e
  simp [and_comm]

@[simp] lemma expectedSampledEdgeDegree_const (H : FiniteHypergraph V E)
    (tau : ℝ) (v : V) :
    H.expectedSampledEdgeDegree (fun _ ↦ tau) v =
      tau * (H.edgeDegree v : ℝ) := by
  simp [expectedSampledEdgeDegree, mul_comm]

@[simp] lemma expectedSampledEdgePairDegree_const (H : FiniteHypergraph V E)
    (tau : ℝ) (u v : V) :
    H.expectedSampledEdgePairDegree (fun _ ↦ tau) u v =
      tau * (H.edgePairDegree u v : ℝ) := by
  simp [expectedSampledEdgePairDegree, mul_comm]

/-- Distinct ordered pairs from the declared vertex set.  Ordered pairs are
convenient for subsequent incidence sums; the inequality in either order is
the same codegree assertion. -/
abbrev DistinctVertexPair (H : FiniteHypergraph V E) :=
  {q : (↥H.vertexSet × ↥H.vertexSet) // q.1 ≠ q.2}

end FiniteHypergraph

namespace FiniteNibble

variable {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Vertices whose sampled incident degree has squared error at least `a²`. -/
def badDegreeVertices (H : FiniteHypergraph V E) (p : E → ℝ) (a : ℝ)
    (S : Finset E) : Finset ↥H.vertexSet :=
  (univ : Finset ↥H.vertexSet).filter fun v ↦
    a ^ 2 ≤ centeredSum univ p (H.incidentEdges v) S ^ 2

/-- Distinct ordered vertex pairs whose sampled codegree has squared error at
least `b²`. -/
def badCodegreePairs (H : FiniteHypergraph V E) (p : E → ℝ) (b : ℝ)
    (S : Finset E) : Finset H.DistinctVertexPair :=
  (univ : Finset H.DistinctVertexPair).filter fun q ↦
    b ^ 2 ≤ centeredSum univ p (H.pairIncidentEdges q.1.1 q.1.2) S ^ 2

/-- The Chebyshev budget for bad vertex degrees. -/
def degreeDeviationBudget (H : FiniteHypergraph V E) (p : E → ℝ) (a : ℝ) : ℝ :=
  (a ^ 2)⁻¹ * ∑ v : ↥H.vertexSet,
    ∑ e ∈ H.incidentEdges v, p e * (1 - p e)

/-- The Chebyshev budget for bad distinct ordered vertex-pair codegrees. -/
def codegreeDeviationBudget (H : FiniteHypergraph V E) (p : E → ℝ)
    (b : ℝ) : ℝ :=
  (b ^ 2)⁻¹ * ∑ q : H.DistinctVertexPair,
    ∑ e ∈ H.pairIncidentEdges q.1.1 q.1.2, p e * (1 - p e)

private lemma card_badDegreeVertices_eq_deviationCount
    (H : FiniteHypergraph V E) (p : E → ℝ) (a : ℝ) (S : Finset E) :
    (badDegreeVertices H p a S).card =
      deviationCount univ p (fun v : ↥H.vertexSet ↦ H.incidentEdges v) a S := rfl

private lemma card_badCodegreePairs_eq_deviationCount
    (H : FiniteHypergraph V E) (p : E → ℝ) (b : ℝ) (S : Finset E) :
    (badCodegreePairs H p b S).card =
      deviationCount univ p
        (fun q : H.DistinctVertexPair ↦ H.pairIncidentEdges q.1.1 q.1.2) b S := rfl

lemma sum_bernoulliMass_mul_card_badDegreeVertices_le
    (H : FiniteHypergraph V E) {p : E → ℝ} {a : ℝ}
    (hp₀ : ∀ e, 0 ≤ p e) (hp₁ : ∀ e, p e ≤ 1) (ha : 0 < a) :
    ∑ S : Finset E,
        bernoulliMass univ p S * (badDegreeVertices H p a S).card ≤
      degreeDeviationBudget H p a := by
  simpa [card_badDegreeVertices_eq_deviationCount, degreeDeviationBudget] using
    (sum_bernoulliMass_mul_deviationCount_le
      (U := (univ : Finset E))
      (A := fun v : ↥H.vertexSet ↦ H.incidentEdges v)
      (fun _ ↦ subset_univ _) (fun e _ ↦ hp₀ e) (fun e _ ↦ hp₁ e) ha)

lemma sum_bernoulliMass_mul_card_badCodegreePairs_le
    (H : FiniteHypergraph V E) {p : E → ℝ} {b : ℝ}
    (hp₀ : ∀ e, 0 ≤ p e) (hp₁ : ∀ e, p e ≤ 1) (hb : 0 < b) :
    ∑ S : Finset E,
        bernoulliMass univ p S * (badCodegreePairs H p b S).card ≤
      codegreeDeviationBudget H p b := by
  simpa [card_badCodegreePairs_eq_deviationCount, codegreeDeviationBudget] using
    (sum_bernoulliMass_mul_deviationCount_le
      (U := (univ : Finset E))
      (A := fun q : H.DistinctVertexPair ↦ H.pairIncidentEdges q.1.1 q.1.2)
      (fun _ ↦ subset_univ _) (fun e _ ↦ hp₀ e) (fun e _ ↦ hp₁ e) hb)

private lemma exists_two_outputs_le_twice_max_bound
    {Omega : Type*} [Fintype Omega] (mass X Y : Omega → ℝ) (BX BY : ℝ)
    (hmass : ∀ omega, 0 ≤ mass omega) (hsum : ∑ omega, mass omega = 1)
    (hX₀ : ∀ omega, 0 ≤ X omega) (hY₀ : ∀ omega, 0 ≤ Y omega)
    (hBX₀ : 0 ≤ BX) (hBY₀ : 0 ≤ BY)
    (hEX : ∑ omega, mass omega * X omega ≤ BX)
    (hEY : ∑ omega, mass omega * Y omega ≤ BY) :
    ∃ omega, X omega ≤ 2 * max BX 1 ∧ Y omega ≤ 2 * max BY 1 := by
  let CX : ℝ := max BX 1
  let CY : ℝ := max BY 1
  let output : Omega → ℝ := fun omega ↦ CX⁻¹ * X omega + CY⁻¹ * Y omega
  have hCX : 0 < CX := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hCY : 0 < CY := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hmean : ∑ omega, mass omega * output omega ≤ 2 := by
    calc
      ∑ omega, mass omega * output omega =
          ∑ omega, (CX⁻¹ * (mass omega * X omega) +
            CY⁻¹ * (mass omega * Y omega)) := by
        apply sum_congr rfl
        intro omega _
        simp only [output]
        ring
      _ =
          CX⁻¹ * (∑ omega, mass omega * X omega) +
            CY⁻¹ * (∑ omega, mass omega * Y omega) := by
        simp only [sum_add_distrib, ← mul_sum]
      _ ≤ CX⁻¹ * BX + CY⁻¹ * BY :=
        add_le_add
          (mul_le_mul_of_nonneg_left hEX (inv_nonneg.mpr hCX.le))
          (mul_le_mul_of_nonneg_left hEY (inv_nonneg.mpr hCY.le))
      _ ≤ 1 + 1 := by
        apply add_le_add
        · calc
            CX⁻¹ * BX ≤ CX⁻¹ * CX :=
              mul_le_mul_of_nonneg_left (le_max_left _ _) (inv_nonneg.mpr hCX.le)
            _ = 1 := inv_mul_cancel₀ hCX.ne'
        · calc
            CY⁻¹ * BY ≤ CY⁻¹ * CY :=
              mul_le_mul_of_nonneg_left (le_max_left _ _) (inv_nonneg.mpr hCY.le)
            _ = 1 := inv_mul_cancel₀ hCY.ne'
      _ = 2 := by norm_num
  obtain ⟨omega, homega⟩ :=
    exists_output_ge_average mass (fun x ↦ -output x) hmass hsum
  have hout : output omega ≤ 2 := by
    have havg : output omega ≤ ∑ x, mass x * output x := by
      simpa only [mul_neg, sum_neg_distrib, neg_le_neg_iff] using homega
    exact havg.trans hmean
  refine ⟨omega, ?_, ?_⟩
  · have hscaled : CX⁻¹ * X omega ≤ 2 := by
      calc
        CX⁻¹ * X omega ≤ output omega := by
          exact le_add_of_nonneg_right (mul_nonneg (inv_nonneg.mpr hCY.le) (hY₀ omega))
        _ ≤ 2 := hout
    calc
      X omega = CX * (CX⁻¹ * X omega) := by
        rw [← mul_assoc, mul_inv_cancel₀ hCX.ne', one_mul]
      _ ≤ CX * 2 := mul_le_mul_of_nonneg_left hscaled hCX.le
      _ = 2 * max BX 1 := by simp [CX, mul_comm]
  · have hscaled : CY⁻¹ * Y omega ≤ 2 := by
      calc
        CY⁻¹ * Y omega ≤ output omega := by
          exact le_add_of_nonneg_left (mul_nonneg (inv_nonneg.mpr hCX.le) (hX₀ omega))
        _ ≤ 2 := hout
    calc
      Y omega = CY * (CY⁻¹ * Y omega) := by
        rw [← mul_assoc, mul_inv_cancel₀ hCY.ne', one_mul]
      _ ≤ CY * 2 := mul_le_mul_of_nonneg_left hscaled hCY.le
      _ = 2 * max BY 1 := by simp [CY, mul_comm]

lemma sampledEdgeDegree_close_of_not_mem_bad
    (H : FiniteHypergraph V E) {p : E → ℝ} {a : ℝ} (ha : 0 < a)
    (S : Finset E) (v : ↥H.vertexSet) (hv : v ∉ badDegreeVertices H p a S) :
    |(H.sampledEdgeDegree S v : ℝ) - H.expectedSampledEdgeDegree p v| < a := by
  have hsq :
      (FiniteNibble.centeredSum univ p (H.incidentEdges v) S) ^ 2 < a ^ 2 := by
    simpa [badDegreeVertices] using hv
  rw [H.centeredSum_incidentEdges] at hsq
  rw [abs_lt]
  constructor <;> nlinarith

lemma sampledEdgePairDegree_lt_expected_add_of_not_mem_bad
    (H : FiniteHypergraph V E) {p : E → ℝ} {b : ℝ} (hb : 0 < b)
    (S : Finset E) (q : H.DistinctVertexPair)
    (hq : q ∉ badCodegreePairs H p b S) :
    (H.sampledEdgePairDegree S q.1.1 q.1.2 : ℝ) <
      H.expectedSampledEdgePairDegree p q.1.1 q.1.2 + b := by
  have hsq :
      (FiniteNibble.centeredSum univ p
        (H.pairIncidentEdges q.1.1 q.1.2) S) ^ 2 < b ^ 2 := by
    simpa [badCodegreePairs] using hq
  rw [H.centeredSum_pairIncidentEdges] at hsq
  nlinarith [sq_nonneg ((H.sampledEdgePairDegree S q.1.1 q.1.2 : ℝ) -
    H.expectedSampledEdgePairDegree p q.1.1 q.1.2 + b)]

/-- One finite Bernoulli round simultaneously concentrates incident degrees
and distinct-pair codegrees, apart from explicitly bounded exceptional sets.
The factor two is the cost of extracting both conclusions from one sample;
`max budget 1` also covers zero-variance experiments uniformly. -/
lemma exists_sample_degree_codegree_concentration
    (H : FiniteHypergraph V E) {p : E → ℝ} {a b : ℝ}
    (hp₀ : ∀ e, 0 ≤ p e) (hp₁ : ∀ e, p e ≤ 1) (ha : 0 < a) (hb : 0 < b) :
    ∃ S : Finset E,
      ((badDegreeVertices H p a S).card : ℝ) ≤
          2 * max (degreeDeviationBudget H p a) 1 ∧
      ((badCodegreePairs H p b S).card : ℝ) ≤
          2 * max (codegreeDeviationBudget H p b) 1 ∧
      (∀ v : ↥H.vertexSet, v ∉ badDegreeVertices H p a S →
        |(H.sampledEdgeDegree S v : ℝ) - H.expectedSampledEdgeDegree p v| < a) ∧
      (∀ q : H.DistinctVertexPair, q ∉ badCodegreePairs H p b S →
        (H.sampledEdgePairDegree S q.1.1 q.1.2 : ℝ) <
          H.expectedSampledEdgePairDegree p q.1.1 q.1.2 + b) := by
  let mass : Finset E → ℝ := fun S ↦ bernoulliMass univ p S
  let X : Finset E → ℝ := fun S ↦ (badDegreeVertices H p a S).card
  let Y : Finset E → ℝ := fun S ↦ (badCodegreePairs H p b S).card
  have hmass : ∀ S, 0 ≤ mass S := fun S ↦
    bernoulliMass_nonneg (subset_univ S) (fun e _ ↦ hp₀ e) (fun e _ ↦ hp₁ e)
  have hsum : ∑ S, mass S = 1 := by
    simpa [mass] using sum_bernoulliMass (univ : Finset E) p
  have hdegreeBudget₀ : 0 ≤ degreeDeviationBudget H p a := by
    exact mul_nonneg (inv_nonneg.mpr (sq_nonneg a))
      (sum_nonneg fun v _ ↦ sum_nonneg fun e he ↦
        mul_nonneg (hp₀ e) (sub_nonneg.mpr (hp₁ e)))
  have hcodegreeBudget₀ : 0 ≤ codegreeDeviationBudget H p b := by
    exact mul_nonneg (inv_nonneg.mpr (sq_nonneg b))
      (sum_nonneg fun q _ ↦ sum_nonneg fun e he ↦
        mul_nonneg (hp₀ e) (sub_nonneg.mpr (hp₁ e)))
  obtain ⟨S, hdegree, hcodegree⟩ := exists_two_outputs_le_twice_max_bound
    mass X Y (degreeDeviationBudget H p a) (codegreeDeviationBudget H p b)
    hmass hsum (fun _ ↦ Nat.cast_nonneg _) (fun _ ↦ Nat.cast_nonneg _)
    hdegreeBudget₀ hcodegreeBudget₀
    (by simpa [mass, X] using
      sum_bernoulliMass_mul_card_badDegreeVertices_le H hp₀ hp₁ ha)
    (by simpa [mass, Y] using
      sum_bernoulliMass_mul_card_badCodegreePairs_le H hp₀ hp₁ hb)
  refine ⟨S, hdegree, hcodegree, ?_, ?_⟩
  · intro v hv
    exact sampledEdgeDegree_close_of_not_mem_bad H ha S v hv
  · intro q hq
    exact sampledEdgePairDegree_lt_expected_add_of_not_mem_bad H hb S q hq

/-- Constant-rate specialization, displaying the expected degree and
codegree through the existing integer `edgeDegree` and `edgePairDegree`
parameters. -/
lemma exists_constant_sample_degree_codegree_concentration
    (H : FiniteHypergraph V E) {tau a b : ℝ}
    (htau₀ : 0 ≤ tau) (htau₁ : tau ≤ 1) (ha : 0 < a) (hb : 0 < b) :
    ∃ S : Finset E,
      ((badDegreeVertices H (fun _ ↦ tau) a S).card : ℝ) ≤
          2 * max (degreeDeviationBudget H (fun _ ↦ tau) a) 1 ∧
      ((badCodegreePairs H (fun _ ↦ tau) b S).card : ℝ) ≤
          2 * max (codegreeDeviationBudget H (fun _ ↦ tau) b) 1 ∧
      (∀ v : ↥H.vertexSet, v ∉ badDegreeVertices H (fun _ ↦ tau) a S →
        |(H.sampledEdgeDegree S v : ℝ) -
          tau * (H.edgeDegree v : ℝ)| < a) ∧
      (∀ q : H.DistinctVertexPair,
        q ∉ badCodegreePairs H (fun _ ↦ tau) b S →
        (H.sampledEdgePairDegree S q.1.1 q.1.2 : ℝ) <
          tau * (H.edgePairDegree q.1.1 q.1.2 : ℝ) + b) := by
  simpa using exists_sample_degree_codegree_concentration H
    (p := fun _ ↦ tau) (fun _ ↦ htau₀) (fun _ ↦ htau₁) ha hb

end FiniteNibble

end

end Erdos76
