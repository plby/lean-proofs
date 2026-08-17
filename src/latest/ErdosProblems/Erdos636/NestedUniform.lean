/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

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

import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

/-!
# Nested uniform fixed-size samples

Choose `D₁` uniformly among the `2d`-subsets of a finite set `U`, and,
conditional on `D₁`, choose `D` uniformly among the `d`-subsets of `D₁`.
This file proves by exact fiber counting that the marginal distribution of
`D` is uniform among the `d`-subsets of `U`.

The feasibility assumption is `2 * d ≤ U.card`.  It ensures that the outer
layer is nonempty.  Every inner layer is nonempty automatically, since its
ambient set has cardinality `2 * d`.
-/

open scoped BigOperators

namespace Erdos636
namespace NestedUniform

open Classical Finset

variable {α : Type*}

/-- The uniform layer of all `d`-subsets of `U`. -/
def layer (U : Finset α) (d : ℕ) : Finset (Finset α) :=
  U.powersetCard d

@[simp] theorem mem_layer {U D : Finset α} {d : ℕ} :
    D ∈ layer U d ↔ D ⊆ U ∧ D.card = d := by
  simp [layer, and_comm]

@[simp] theorem card_layer (U : Finset α) (d : ℕ) :
    (layer U d).card = U.card.choose d := by
  simp [layer, Finset.card_powersetCard]

theorem layer_nonempty_iff (U : Finset α) (d : ℕ) :
    (layer U d).Nonempty ↔ d ≤ U.card := by
  exact Finset.powersetCard_nonempty

/-- A pair consisting of an outer set and a selected inner set. -/
abbrev NestedSample (α : Type*) := Σ _ : Finset α, Finset α

/-- The pairs which can occur in the two-stage experiment. -/
def nestedSamples (U : Finset α) (d : ℕ) : Finset (NestedSample α) :=
  (layer U (2 * d)).sigma fun D₁ ↦ layer D₁ d

@[simp] theorem mem_nestedSamples {U D₁ D : Finset α} {d : ℕ} :
    (⟨D₁, D⟩ : NestedSample α) ∈ nestedSamples U d ↔
      D₁ ⊆ U ∧ D₁.card = 2 * d ∧ D ⊆ D₁ ∧ D.card = d := by
  simp [nestedSamples, and_assoc]

/-- Every `d`-set in the target layer has the same number of admissible
`2d`-set extensions. -/
theorem card_outer_fiber {U D : Finset α} {d : ℕ}
    (hD : D ∈ layer U d) :
    ((layer U (2 * d)).filter fun D₁ ↦ D ⊆ D₁).card =
      (U.card - d).choose d := by
  rw [layer, Finset.card_filter_powersetCard_subset D U (2 * d)]
  · rw [(mem_layer.mp hD).2]
    congr 1
    omega
  · exact (mem_layer.mp hD).1
  · rw [(mem_layer.mp hD).2]
    omega

/-- Exact weighted fiber-counting identity.  It is the algebraic core of
the nested-uniform marginal law. -/
theorem sum_nested_eq_choose_nsmul_sum {M : Type*} [AddCommMonoid M]
    (U : Finset α) (d : ℕ) (f : Finset α → M) :
    (∑ D₁ ∈ layer U (2 * d), ∑ D ∈ layer D₁ d, f D) =
      (U.card - d).choose d • ∑ D ∈ layer U d, f D := by
  have hinner (D₁ : Finset α) (hD₁ : D₁ ∈ layer U (2 * d)) :
      layer D₁ d = (layer U d).filter fun D ↦ D ⊆ D₁ := by
    ext D
    have hsub : D₁ ⊆ U := (mem_layer.mp hD₁).1
    simp only [mem_layer, Finset.mem_filter]
    constructor
    · rintro ⟨hDD₁, hcard⟩
      exact ⟨⟨hDD₁.trans hsub, hcard⟩, hDD₁⟩
    · rintro ⟨⟨_hDU, hcard⟩, hDD₁⟩
      exact ⟨hDD₁, hcard⟩
  calc
    (∑ D₁ ∈ layer U (2 * d), ∑ D ∈ layer D₁ d, f D) =
        ∑ D₁ ∈ layer U (2 * d),
          ∑ D ∈ (layer U d).filter fun D ↦ D ⊆ D₁, f D := by
      apply Finset.sum_congr rfl
      intro D₁ hD₁
      rw [hinner D₁ hD₁]
    _ = ∑ D₁ ∈ layer U (2 * d),
          ∑ D ∈ layer U d, if D ⊆ D₁ then f D else 0 := by
      simp_rw [Finset.sum_filter]
    _ = ∑ D ∈ layer U d,
          ∑ D₁ ∈ layer U (2 * d), if D ⊆ D₁ then f D else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ D ∈ layer U d, (U.card - d).choose d • f D := by
      apply Finset.sum_congr rfl
      intro D hD
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const]
      rw [card_outer_fiber hD]
    _ = (U.card - d).choose d • ∑ D ∈ layer U d, f D := by
      rw [Finset.smul_sum]

/-- Real-valued form of the exact weighted fiber-counting identity. -/
theorem sum_nested_eq_choose_mul_sum (U : Finset α) (d : ℕ)
    (f : Finset α → ℝ) :
    (∑ D₁ ∈ layer U (2 * d), ∑ D ∈ layer D₁ d, f D) =
      (U.card - d).choose d * ∑ D ∈ layer U d, f D := by
  simpa [nsmul_eq_mul] using sum_nested_eq_choose_nsmul_sum U d f

/-- The same counting identity written directly over the sigma-type of
admissible nested samples. -/
theorem sum_nestedSamples_snd_eq_choose_nsmul_sum {M : Type*}
    [AddCommMonoid M] (U : Finset α) (d : ℕ) (f : Finset α → M) :
    (∑ p ∈ nestedSamples U d, f p.2) =
      (U.card - d).choose d • ∑ D ∈ layer U d, f D := by
  rw [nestedSamples, Finset.sum_sigma]
  exact sum_nested_eq_choose_nsmul_sum U d f

/-- Exact number of pairs in the nested experiment. -/
theorem card_nestedSamples (U : Finset α) (d : ℕ) :
    (nestedSamples U d).card =
      (U.card - d).choose d * U.card.choose d := by
  simpa [nestedSamples, card_layer] using
    sum_nested_eq_choose_nsmul_sum U d (fun _ ↦ (1 : ℕ))

/-- The same sample-space count factored as “number of outer choices times
number of inner choices”.  This is why uniformity on admissible pairs is
exactly the sequential conditional-uniform experiment. -/
theorem card_nestedSamples_eq_outer_mul_inner (U : Finset α) (d : ℕ) :
    (nestedSamples U d).card =
      U.card.choose (2 * d) * (2 * d).choose d := by
  rw [nestedSamples, Finset.card_sigma]
  calc
    (∑ D₁ ∈ layer U (2 * d), (layer D₁ d).card) =
        ∑ _D₁ ∈ layer U (2 * d), (2 * d).choose d := by
      apply Finset.sum_congr rfl
      intro D₁ hD₁
      rw [card_layer, (mem_layer.mp hD₁).2]
    _ = (layer U (2 * d)).card * (2 * d).choose d := by simp
    _ = U.card.choose (2 * d) * (2 * d).choose d := by rw [card_layer]

/-- The standard feasibility condition makes both sampling stages nonempty. -/
theorem nestedSamples_nonempty (U : Finset α) (d : ℕ)
    (hfeasible : 2 * d ≤ U.card) :
    (nestedSamples U d).Nonempty := by
  rw [← Finset.card_pos, card_nestedSamples_eq_outer_mul_inner]
  exact Nat.mul_pos (Nat.choose_pos hfeasible) (Nat.choose_pos (by omega))

/-- The ordinary probability of an event under a uniform fixed-size sample. -/
noncomputable def layerProbability (U : Finset α) (d : ℕ)
    (event : Finset α → Prop) [DecidablePred event] : ℝ :=
  (((layer U d).filter event).card : ℝ) / (layer U d).card

/-- The probability of an event in the second coordinate of the two-stage
experiment.  Since all outer and inner layers have constant cardinality,
this is exactly the sequential conditional-uniform probability. -/
noncomputable def nestedProbability (U : Finset α) (d : ℕ)
    (event : Finset α → Prop) [DecidablePred event] : ℝ :=
  (((nestedSamples U d).filter fun p ↦ event p.2).card : ℝ) /
    (nestedSamples U d).card

/-- Event-count version of the marginal law, before dividing by the sample
space cardinalities. -/
theorem card_nested_event (U : Finset α) (d : ℕ)
    (event : Finset α → Prop) [DecidablePred event] :
    ((nestedSamples U d).filter fun p ↦ event p.2).card =
      (U.card - d).choose d * ((layer U d).filter event).card := by
  calc
    ((nestedSamples U d).filter fun p ↦ event p.2).card =
        ∑ p ∈ nestedSamples U d, if event p.2 then 1 else 0 :=
      Finset.card_filter _ _
    _ = (U.card - d).choose d •
        ∑ D ∈ layer U d, if event D then 1 else 0 :=
      sum_nestedSamples_snd_eq_choose_nsmul_sum U d
        (fun D ↦ if event D then (1 : ℕ) else 0)
    _ = (U.card - d).choose d * ((layer U d).filter event).card := by
      rw [Finset.card_filter]
      exact nsmul_eq_mul _ _

/-- The marginal `D` is uniform among all `d`-subsets of `U`. -/
theorem nestedProbability_eq_layerProbability (U : Finset α) (d : ℕ)
    (hfeasible : 2 * d ≤ U.card) (event : Finset α → Prop)
    [DecidablePred event] :
    nestedProbability U d event = layerProbability U d event := by
  rw [nestedProbability, layerProbability, card_nested_event,
    card_nestedSamples, card_layer]
  have hchoose : 0 < (U.card - d).choose d := by
    exact Nat.choose_pos (by omega)
  have hchooseReal : (0 : ℝ) < (U.card - d).choose d := by
    exact_mod_cast hchoose
  simp only [Nat.cast_mul]
  exact mul_div_mul_left _ _ hchooseReal.ne'

/-- Uniform expectation on one fixed-size layer. -/
noncomputable def layerExpectation (U : Finset α) (d : ℕ)
    (f : Finset α → ℝ) : ℝ :=
  (layer U d).expect f

/-- Iterated expectation for the two-stage conditional-uniform experiment. -/
noncomputable def nestedExpectation (U : Finset α) (d : ℕ)
    (f : Finset α → ℝ) : ℝ :=
  (nestedSamples U d).expect fun p ↦ f p.2

/-- The literal iterated expectation: first average over uniform `2d`-sets,
then average over uniform `d`-subsets of the chosen outer set. -/
noncomputable def iteratedExpectation (U : Finset α) (d : ℕ)
    (f : Finset α → ℝ) : ℝ :=
  (layer U (2 * d)).expect fun D₁ ↦ (layer D₁ d).expect f

/-- Uniform expectation on admissible pairs equals literal two-stage
conditional-uniform expectation. -/
theorem iteratedExpectation_eq_nestedExpectation (U : Finset α) (d : ℕ)
    (hfeasible : 2 * d ≤ U.card) (f : Finset α → ℝ) :
    iteratedExpectation U d f = nestedExpectation U d f := by
  rw [iteratedExpectation, nestedExpectation]
  rw [Finset.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card,
    card_nestedSamples_eq_outer_mul_inner, card_layer]
  simp_rw [Finset.expect_eq_sum_div_card]
  have hinner : 0 < (2 * d).choose d := Nat.choose_pos (by omega)
  have houter : 0 < U.card.choose (2 * d) := Nat.choose_pos hfeasible
  have hsumdiv :
      (∑ D₁ ∈ layer U (2 * d),
          (∑ D ∈ layer D₁ d, f D) / (layer D₁ d).card) =
        (∑ D₁ ∈ layer U (2 * d), ∑ D ∈ layer D₁ d, f D) /
          (2 * d).choose d := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro D₁ hD₁
    rw [card_layer, (mem_layer.mp hD₁).2]
  rw [hsumdiv, nestedSamples, Finset.sum_sigma]
  simp only [Nat.cast_mul]
  have hinnerReal : (0 : ℝ) < (2 * d).choose d := by exact_mod_cast hinner
  have houterReal : (0 : ℝ) < U.card.choose (2 * d) := by exact_mod_cast houter
  field_simp

/-- Expectation form of the marginal law. -/
theorem nestedExpectation_eq_layerExpectation (U : Finset α) (d : ℕ)
    (hfeasible : 2 * d ≤ U.card) (f : Finset α → ℝ) :
    nestedExpectation U d f = layerExpectation U d f := by
  rw [nestedExpectation, layerExpectation]
  rw [Finset.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card,
    card_nestedSamples, card_layer]
  have hfactor : 0 < (U.card - d).choose d :=
    Nat.choose_pos (by omega)
  have hsum :
      (∑ p ∈ nestedSamples U d, f p.2) =
        ((U.card - d).choose d : ℕ) * ∑ D ∈ layer U d, f D := by
    simpa [nsmul_eq_mul] using
      sum_nestedSamples_snd_eq_choose_nsmul_sum U d f
  rw [hsum]
  simp only [Nat.cast_mul]
  have hfactorReal : (0 : ℝ) < (U.card - d).choose d := by
    exact_mod_cast hfactor
  exact mul_div_mul_left _ _ hfactorReal.ne'

/-- The literal two-stage expectation has the uniform `d`-set marginal. -/
theorem iteratedExpectation_eq_layerExpectation (U : Finset α) (d : ℕ)
    (hfeasible : 2 * d ≤ U.card) (f : Finset α → ℝ) :
    iteratedExpectation U d f = layerExpectation U d f := by
  rw [iteratedExpectation_eq_nestedExpectation U d hfeasible f]
  exact nestedExpectation_eq_layerExpectation U d hfeasible f

/-- Probability is expectation of the event indicator on one layer. -/
theorem layerProbability_eq_layerExpectation_indicator (U : Finset α) (d : ℕ)
    (event : Finset α → Prop) [DecidablePred event] :
    layerProbability U d event =
      layerExpectation U d (fun D ↦ if event D then (1 : ℝ) else 0) := by
  rw [layerProbability, layerExpectation, Finset.expect_eq_sum_div_card,
    Finset.card_filter]
  congr 1
  norm_cast

/-- Probability is expectation of the second-coordinate event indicator on
the joint nested sample space. -/
theorem nestedProbability_eq_nestedExpectation_indicator (U : Finset α) (d : ℕ)
    (event : Finset α → Prop) [DecidablePred event] :
    nestedProbability U d event =
      nestedExpectation U d (fun D ↦ if event D then (1 : ℝ) else 0) := by
  rw [nestedProbability, nestedExpectation, Finset.expect_eq_sum_div_card,
    Finset.card_filter]
  congr 1
  norm_cast

/-- The literal sequential probability, expressed as the outer average of
the conditional uniform inner probabilities. -/
noncomputable def iteratedProbability (U : Finset α) (d : ℕ)
    (event : Finset α → Prop) [DecidablePred event] : ℝ :=
  (layer U (2 * d)).expect fun D₁ ↦ layerProbability D₁ d event

/-- The explicit sequential probability agrees with the uniform probability
on admissible nested pairs. -/
theorem iteratedProbability_eq_nestedProbability (U : Finset α) (d : ℕ)
    (hfeasible : 2 * d ≤ U.card) (event : Finset α → Prop)
    [DecidablePred event] :
    iteratedProbability U d event = nestedProbability U d event := by
  rw [iteratedProbability, nestedProbability_eq_nestedExpectation_indicator]
  have hpoint (D₁ : Finset α) :
      layerProbability D₁ d event =
        layerExpectation D₁ d (fun D ↦ if event D then (1 : ℝ) else 0) :=
    layerProbability_eq_layerExpectation_indicator D₁ d event
  simp_rw [hpoint]
  exact iteratedExpectation_eq_nestedExpectation U d hfeasible _

/-- Probability form of the exact two-stage marginal law. -/
theorem iteratedProbability_eq_layerProbability (U : Finset α) (d : ℕ)
    (hfeasible : 2 * d ≤ U.card) (event : Finset α → Prop)
    [DecidablePred event] :
    iteratedProbability U d event = layerProbability U d event := by
  rw [iteratedProbability_eq_nestedProbability U d hfeasible event]
  exact nestedProbability_eq_layerProbability U d hfeasible event

end NestedUniform
end Erdos636
