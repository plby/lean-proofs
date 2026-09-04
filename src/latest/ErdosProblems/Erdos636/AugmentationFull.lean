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

import ErdosProblems.Erdos636.AntiConcentration
import ErdosProblems.Erdos636.CollisionCounting
import ErdosProblems.Erdos636.HalfSample
import ErdosProblems.Erdos636.Switching
import ErdosProblems.Erdos636.TailExpectation
import ErdosProblems.Erdos636.TuranEdges

/-!
# The full exposure in the Kwan--Sudakov augmentation argument

This file packages the finite probabilistic content of Claim 4.9.  The
ground space is a set `D₁` of cardinality `2s`, and the random choice is a
uniform `s`-subset of `D₁`.  `PartialExposureData` records only the objects
which have already been fixed at the partial-exposure stage: a switching
path, the values whose collisions have to be controlled, the geometric and
degree exceptional events, and the exact affine half-sample identity for
the endpoint rise.

The main theorem is deliberately quantitative and finite.  Four explicit
failure bounds are required to have sum less than `1/2`.  Half-sample
symmetry supplies an endpoint-rise event of probability at least `1/2`, so
one outcome simultaneously has few geometric exceptions, few collision-bad
indices, few degree exceptions, and a bounded large-jump budget.  The
deterministic switching lemma is then applied to that same outcome.

Pairwise collision probabilities are the only analytic inputs to the
package.  `collisionProbability_le_of_pairEmbedding` below records the
exact adapter from the balanced-slice anti-concentration theorem.  In the
graph application those bounds come from the incidence-difference
coefficients furnished by the partial exposure.
-/

open Classical
open scoped BigOperators

namespace Erdos636
namespace AugmentationFull

open Erdos88.Concentration

universe u v

noncomputable section

/-- The uniform half-sample space used in the full exposure. -/
abbrev Sample (D : Type u) [Fintype D] (s : ℕ) := HalfSample.Slice D s

/-- Data fixed before the final uniform-half exposure.

`path ω i` is the base edge-count path after the half-sample `ω` is
revealed.  `value i x ω` is the integer extension value attached to
candidate `x` at time `i`.  The two predicates name the exceptional events
in parts (i) and (iii) of Claim 4.9.  The final two fields are the exact
affine representation of the endpoint rise used by half-sample symmetry. -/
structure PartialExposureData (D : Type u) [Fintype D]
    (X : Type v) (s τ : ℕ) where
  candidates : Finset X
  path : Sample D s → ℕ → ℝ
  value : ℕ → X → Sample D s → ℤ
  geometricBad : ℕ → Sample D s → Prop
  degreeBad : X → Sample D s → Prop
  endpointCoeff : D → ℝ
  endpointOffset : ℝ
  endpointIdentity : ∀ ω,
    path ω τ - path ω 0 =
      endpointOffset + HalfSample.sliceSum endpointCoeff ω

/-- The one-step increment of the exposed switching path. -/
def increment {D : Type u} [Fintype D] {X : Type v} {s τ : ℕ}
    (P : PartialExposureData D X s τ) (ω : Sample D s) (i : ℕ) : ℝ :=
  P.path ω (i + 1) - P.path ω i

/-- The sum of absolute increments at least `ρ`.  This dominates
`Switching.largeIncrementSum`, which retains only positive increments
strictly larger than `ρ`. -/
def tailBudget {D : Type u} [Fintype D] {X : Type v} {s τ : ℕ}
    (P : PartialExposureData D X s τ) (ρ : ℝ) (ω : Sample D s) : ℝ :=
  ∑ i ∈ Finset.range τ,
    if ρ ≤ |increment P ω i| then |increment P ω i| else 0

/-- An index is collision-bad when its collision graph has at least `E`
oriented edges. -/
def collisionBad {D : Type u} [Fintype D] {X : Type v}
    [LinearOrder X] [DecidableEq X] {s τ : ℕ}
    (P : PartialExposureData D X s τ) (E : ℝ)
    (i : ℕ) (ω : Sample D s) : Prop :=
  E ≤ (CollisionCounting.collisionEdges P.candidates (P.value i) ω).card

/-- Normalized expectation commutes with a finite sum. -/
lemma uniformExpectation_sum {Ω ι : Type*} [Fintype Ω] [Nonempty Ω]
    (I : Finset ι) (f : ι → Ω → ℝ) :
    uniformExpectation (fun ω ↦ ∑ i ∈ I, f i ω) =
      ∑ i ∈ I, uniformExpectation (f i) := by
  classical
  simp only [uniformExpectation, Finset.sum_div]
  rw [Finset.sum_comm]

/-- The normalized Markov bound in the form needed for the large-jump
budget. -/
lemma uniformProbability_le_of_expectation_le
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (Y : Ω → ℝ) (t B : ℝ) (ht : 0 < t)
    (hY : ∀ ω, 0 ≤ Y ω)
    (hmean : uniformExpectation Y ≤ B) :
    uniformProbability (fun ω ↦ t ≤ Y ω) ≤ B / t := by
  classical
  have hcard : (0 : ℝ) < Fintype.card Ω := by
    exact_mod_cast Fintype.card_pos
  have hmarkov := counting_markov Y t ht hY
  rw [uniformExpectation] at hmean
  rw [uniformProbability]
  calc
    ((Finset.univ.filter fun ω ↦ t ≤ Y ω).card : ℝ) /
          Fintype.card Ω ≤
        ((∑ ω, Y ω) / t) / Fintype.card Ω := by
      apply div_le_div_of_nonneg_right _ hcard.le
      exact (le_div_iff₀ ht).2 hmarkov
    _ = ((∑ ω, Y ω) / Fintype.card Ω) / t := by field_simp
    _ ≤ B / t := div_le_div_of_nonneg_right hmean ht.le

/-- If `A` has probability at least `q`, while `B` has probability strictly
less than `q`, some outcome lies in `A \ B`. -/
lemma exists_good_not_bad {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (A B : Ω → Prop) (q : ℝ)
    (hA : q ≤ uniformProbability A)
    (hB : uniformProbability B < q) :
    ∃ ω, A ω ∧ ¬ B ω := by
  by_contra h
  push Not at h
  have hmono : uniformProbability A ≤ uniformProbability B :=
    uniformProbability_mono (fun ω hAω ↦ h ω hAω)
  linarith

/-- Pointwise comparison passes to normalized finite expectation. -/
lemma uniformExpectation_mono {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {f g : Ω → ℝ} (hfg : ∀ ω, f ω ≤ g ω) :
    uniformExpectation f ≤ uniformExpectation g := by
  rw [uniformExpectation]
  have hcard : (0 : ℝ) ≤ Fintype.card Ω := by positivity
  apply div_le_div_of_nonneg_right _ hcard
  exact Finset.sum_le_sum fun ω _hω ↦ hfg ω

/-- The expectation of a Boolean indicator is normalized counting
probability. -/
lemma uniformExpectation_indicator {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (A : Ω → Prop) :
    uniformExpectation (fun ω ↦ if A ω then 1 else 0) =
      uniformProbability A := by
  classical
  rw [uniformExpectation, uniformProbability]
  congr 1
  simp

/-- Quantitative subtraction form of the union bound: removing an event of
probability at most `r` from an event of probability at least `q` leaves
probability at least `q-r`. -/
lemma sub_le_uniformProbability_and_not
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (A B : Ω → Prop) (q r : ℝ)
    (hA : q ≤ uniformProbability A)
    (hB : uniformProbability B ≤ r) :
    q - r ≤ uniformProbability (fun ω ↦ A ω ∧ ¬ B ω) := by
  let C : Ω → Prop := fun ω ↦ A ω ∧ ¬ B ω
  let : DecidablePred A := Classical.decPred A
  let : DecidablePred B := Classical.decPred B
  let : DecidablePred C := Classical.decPred C
  change q - r ≤ uniformProbability C
  let f : Ω → ℝ := fun ω ↦ if A ω then 1 else 0
  let g : Ω → ℝ := fun ω ↦
    (if C ω then 1 else 0) + (if B ω then 1 else 0)
  have hfg : ∀ ω, f ω ≤ g ω := by
    intro ω
    dsimp only [f, g, C]
    by_cases hAω : A ω <;> by_cases hBω : B ω <;> simp_all
  have hmean := uniformExpectation_mono hfg
  dsimp only [f, g] at hmean
  rw [uniformExpectation_add] at hmean
  have hAindicator := uniformExpectation_indicator A
  have hBindicator := uniformExpectation_indicator B
  have hCindicator := uniformExpectation_indicator C
  have hmean' : uniformProbability A ≤
      uniformProbability C + uniformProbability B := by
    calc
      uniformProbability A =
          uniformExpectation (fun ω ↦ if A ω then 1 else 0) :=
        hAindicator.symm
      _ ≤
          uniformExpectation (fun ω ↦ if C ω then 1 else 0) +
            uniformExpectation (fun ω ↦ if B ω then 1 else 0) := hmean
      _ = uniformProbability C + uniformProbability B := by
        rw [hCindicator, hBindicator]
  linarith

/-- In particular, a half-probability endpoint event survives four combined
failure events of total probability at most one quarter with probability at
least one quarter. -/
theorem one_quarter_le_uniformProbability_and_not
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (endpoint failure : Ω → Prop)
    (hendpoint : (1 : ℝ) / 2 ≤ uniformProbability endpoint)
    (hfailure : uniformProbability failure ≤ 1 / 4) :
    (1 : ℝ) / 4 ≤
      uniformProbability (fun ω ↦ endpoint ω ∧ ¬ failure ω) := by
  have h := sub_le_uniformProbability_and_not
    endpoint failure (1 / 2) (1 / 4) hendpoint hfailure
  norm_num at h ⊢
  exact h

/-- The simultaneous good-exposure event appearing in Claim 4.9. -/
def FullExposureEvent
    {D : Type u} [Fintype D] {X : Type v}
    [LinearOrder X] [DecidableEq X] {s τ : ℕ}
    (P : PartialExposureData D X s τ)
    (lam E rho κ tGeom tCollision tDegree : ℝ)
    (ω : Sample D s) : Prop :=
  lam ≤ P.path ω τ - P.path ω 0 ∧
    (CollisionCounting.eventCount (Finset.range (τ + 1))
      P.geometricBad ω : ℝ) < tGeom ∧
    (CollisionCounting.eventCount (Finset.range (τ + 1))
      (collisionBad P E) ω : ℝ) < tCollision ∧
    (CollisionCounting.eventCount P.candidates P.degreeBad ω : ℝ) <
      tDegree ∧
    tailBudget P rho ω < κ

/-- Probability form of the full-exposure package.  This is the exact
`1/2 - 1/4 = 1/4` calculation used before an outcome is fixed. -/
theorem one_quarter_le_uniformProbability_fullExposureEvent
    {D : Type u} [Fintype D] {X : Type v}
    [LinearOrder X] [DecidableEq X] {s τ : ℕ}
    [Nonempty (Sample D s)]
    (P : PartialExposureData D X s τ)
    (lam E rho κ tGeom tCollision tDegree : ℝ)
    (hendpoint : (1 : ℝ) / 2 ≤ uniformProbability (fun ω : Sample D s ↦
      lam ≤ P.path ω τ - P.path ω 0))
    (hfailure : uniformProbability (fun ω : Sample D s ↦
      tGeom ≤ CollisionCounting.eventCount (Finset.range (τ + 1))
          P.geometricBad ω ∨
      tCollision ≤ CollisionCounting.eventCount (Finset.range (τ + 1))
          (collisionBad P E) ω ∨
      tDegree ≤ CollisionCounting.eventCount P.candidates P.degreeBad ω ∨
      κ ≤ tailBudget P rho ω) ≤ 1 / 4) :
    (1 : ℝ) / 4 ≤ uniformProbability
      (FullExposureEvent P lam E rho κ tGeom tCollision tDegree) := by
  have h := one_quarter_le_uniformProbability_and_not
    (fun ω : Sample D s ↦ lam ≤ P.path ω τ - P.path ω 0)
    (fun ω : Sample D s ↦
      tGeom ≤ CollisionCounting.eventCount (Finset.range (τ + 1))
          P.geometricBad ω ∨
      tCollision ≤ CollisionCounting.eventCount (Finset.range (τ + 1))
          (collisionBad P E) ω ∨
      tDegree ≤ CollisionCounting.eventCount P.candidates P.degreeBad ω ∨
      κ ≤ tailBudget P rho ω) hendpoint hfailure
  refine h.trans (uniformProbability_mono ?_)
  intro ω hω
  rcases hω with ⟨hendpointω, hfailω⟩
  push Not at hfailω
  rcases hfailω with ⟨hgeomω, hcollisionω, hdegreeω, htailω⟩
  exact ⟨hendpointω, hgeomω, hcollisionω, hdegreeω, htailω⟩

/-- The positive-large-increment budget is bounded by the absolute tail
budget from the moment estimate. -/
lemma largeIncrementSum_le_tailBudget
    {D : Type u} [Fintype D] {X : Type v} {s τ : ℕ}
    (P : PartialExposureData D X s τ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (ω : Sample D s) :
    Switching.largeIncrementSum (P.path ω) ρ τ ≤ tailBudget P ρ ω := by
  classical
  unfold Switching.largeIncrementSum tailBudget
  apply Finset.sum_le_sum
  intro i hi
  rw [Switching.largeIncrement]
  split_ifs with hlarge htail
  · have hpos : 0 < increment P ω i := hρ.trans_lt hlarge
    rw [abs_of_pos hpos]
    rfl
  · exact (htail (hlarge.le.trans (le_abs_self _))).elim
  · positivity
  · positivity

/-- Tail expectation for the total switching budget. -/
lemma uniformExpectation_tailBudget_le
    {D : Type u} [Fintype D] [DecidableEq D]
    {X : Type v} {s τ : ℕ} (hcard : Fintype.card D = 2 * s)
    (P : PartialExposureData D X s τ) {v Q : ℝ}
    (hv : 0 < v) (hQ : 0 < Q)
    (hsecond : ∀ i < τ,
      uniformExpectation (fun ω : Sample D s ↦ (increment P ω i) ^ 2) ≤ v) :
    uniformExpectation (tailBudget P (Q * Real.sqrt v)) ≤
      τ * (Real.sqrt v / Q) := by
  let : Nonempty (Sample D s) := HalfSample.sliceNonempty hcard
  change uniformExpectation (fun ω : Sample D s ↦
    ∑ i ∈ Finset.range τ,
      if Q * Real.sqrt v ≤ |increment P ω i| then
        |increment P ω i| else 0) ≤ _
  rw [uniformExpectation_sum]
  calc
    ∑ i ∈ Finset.range τ,
        uniformExpectation (fun ω : Sample D s ↦
          if Q * Real.sqrt v ≤ |increment P ω i| then
            |increment P ω i| else 0) ≤
        ∑ _i ∈ Finset.range τ, Real.sqrt v / Q := by
      apply Finset.sum_le_sum
      intro i hi
      exact TailExpectation.truncatedAbsExpectation_mul_sqrt_le_of_sq
        (fun ω : Sample D s ↦ increment P ω i) v Q hv hQ
          (hsecond i (Finset.mem_range.mp hi))
    _ = τ * (Real.sqrt v / Q) := by simp

/-- Adapter from balanced-slice anti-concentration to the pairwise collision
hypothesis of the full exposure.  Each candidate pair has its own
coefficient population and target value in the graph application. -/
lemma collisionProbability_le_of_pairEmbedding
    {I : Type*} [Fintype I] [DecidableEq I]
    {K : Type*} [Fintype K] {s : ℕ}
    [Nonempty (Erdos88.Fourier.BoolSlice I s)]
    (p : Erdos88.Fourier.PairEmbedding K I)
    (a : I → ℝ) (c B : ℝ)
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 2)
    (hsel : c * Fintype.card I ≤ s)
    (hunsel : c * Fintype.card I ≤ Fintype.card I - s)
    (hB : 1 ≤ B)
    (hlower : ∀ k, 1 ≤ |a (p (k, false)) - a (p (k, true))|)
    (hupper : ∀ k, |a (p (k, false)) - a (p (k, true))| ≤ B)
    (hK : 0 < Fintype.card K) (x : ℝ) :
    Erdos88.Fourier.finProbability (Erdos88.Fourier.BoolSlice I s)
        (fun ω ↦ AntiConcentration.sliceLinear s a ω = x) ≤
      16 * B * Real.exp 1 *
        Real.sqrt (Real.pi /
          ((c ^ 3 / 256) * Fintype.card K / (4 * Real.pi ^ 2))) := by
  exact AntiConcentration.slice_point_probability_le_of_pairs
    p s a c B hc0 hc1 hsel hunsel hB hlower hupper hK x

/-- **Finite full-exposure theorem (Claim 4.9).**

The conclusion supplies one half-sample on which the five properties used
in the paper hold simultaneously, followed by the separated switching
subsequence.  Parts (i), (ii), and (iii) are represented by the first three
event-count inequalities, part (iv) by `hrise`, and part (v) by the tail
budget.  All constants and all failure thresholds occur explicitly. -/
theorem exists_fullExposure_switching
    {D : Type u} [Fintype D] [DecidableEq D]
    {X : Type v} [LinearOrder X] [DecidableEq X]
    {s τ m : ℕ} (hcard : Fintype.card D = 2 * s)
    (P : PartialExposureData D X s τ)
    {lam sigma v Q κ E : ℝ}
    {tGeom tCollision tDegree : ℝ}
    {pGeom pCollision pDegree : ℝ}
    (hv : 0 < v) (hQ : 0 < Q) (hκ : 0 < κ) (hE : 0 < E)
    (htGeom : 0 < tGeom) (htCollision : 0 < tCollision)
    (htDegree : 0 < tDegree)
    (hm : 1 ≤ m) (hsigma : 0 < sigma)
    (hmeanRise : lam ≤
      P.endpointOffset + (∑ d, P.endpointCoeff d) / 2)
    (hgeom : ∀ i < τ + 1,
      uniformProbability (P.geometricBad i) ≤ pGeom)
    (hcollision : ∀ i < τ + 1,
      ∀ x ∈ P.candidates, ∀ y ∈ P.candidates, x ≠ y →
        uniformProbability (fun ω ↦ P.value i x ω = P.value i y ω) ≤
          pCollision)
    (hdegree : ∀ x ∈ P.candidates,
      uniformProbability (P.degreeBad x) ≤ pDegree)
    (hsecond : ∀ i < τ,
      uniformExpectation (fun ω : Sample D s ↦ (increment P ω i) ^ 2) ≤ v)
    (hfailure :
      (τ + 1 : ℕ) * pGeom / tGeom +
          (τ + 1 : ℕ) * (P.candidates.card.choose 2 * pCollision / E) /
            tCollision +
          P.candidates.card * pDegree / tDegree +
          (τ * (Real.sqrt v / Q)) / κ < 1 / 2)
    (hbudget : (m : ℝ) * (Q * Real.sqrt v + sigma) + κ ≤ lam) :
    ∃ ω : Sample D s, ∃ idx : Fin (m + 1) → ℕ,
      (CollisionCounting.eventCount (Finset.range (τ + 1))
          P.geometricBad ω : ℝ) < tGeom ∧
      (CollisionCounting.eventCount (Finset.range (τ + 1))
          (collisionBad P E) ω : ℝ) < tCollision ∧
      (CollisionCounting.eventCount P.candidates P.degreeBad ω : ℝ) <
        tDegree ∧
      tailBudget P (Q * Real.sqrt v) ω < κ ∧
      lam ≤ P.path ω τ - P.path ω 0 ∧
      StrictMono idx ∧ idx 0 = 0 ∧ idx (Fin.last m) = τ ∧
      ∀ j : Fin m,
        sigma ≤ P.path ω (idx j.succ) - P.path ω (idx j.castSucc) := by
  let : Nonempty (Sample D s) := HalfSample.sliceNonempty hcard
  let geomFail : Sample D s → Prop := fun ω ↦
    tGeom ≤ CollisionCounting.eventCount (Finset.range (τ + 1))
      P.geometricBad ω
  let collisionFail : Sample D s → Prop := fun ω ↦
    tCollision ≤ CollisionCounting.eventCount (Finset.range (τ + 1))
      (collisionBad P E) ω
  let degreeFail : Sample D s → Prop := fun ω ↦
    tDegree ≤ CollisionCounting.eventCount P.candidates P.degreeBad ω
  let tailFail : Sample D s → Prop := fun ω ↦
    κ ≤ tailBudget P (Q * Real.sqrt v) ω
  let endpointGood : Sample D s → Prop := fun ω ↦
    lam ≤ P.path ω τ - P.path ω 0
  have hgeomProb : uniformProbability geomFail ≤
      (τ + 1 : ℕ) * pGeom / tGeom := by
    simpa [geomFail] using
      (CollisionCounting.uniformProbability_eventCount_ge_le
        (Finset.range (τ + 1)) P.geometricBad pGeom tGeom htGeom
        (fun i hi ↦ hgeom i (Finset.mem_range.mp hi)))
  have hcollisionOne : ∀ i < τ + 1,
      uniformProbability (collisionBad P E i) ≤
        P.candidates.card.choose 2 * pCollision / E := by
    intro i hi
    change uniformProbability (fun ω ↦ E ≤
      ((CollisionCounting.collisionEdges
        P.candidates (P.value i) ω).card : ℝ)) ≤ _
    exact CollisionCounting.uniformProbability_card_collisionEdges_ge_le
      P.candidates (P.value i) pCollision E hE (hcollision i hi)
  have hcollisionProb : uniformProbability collisionFail ≤
      (τ + 1 : ℕ) *
        (P.candidates.card.choose 2 * pCollision / E) / tCollision := by
    simpa [collisionFail] using
      (CollisionCounting.uniformProbability_eventCount_ge_le
        (Finset.range (τ + 1)) (collisionBad P E)
        (P.candidates.card.choose 2 * pCollision / E)
        tCollision htCollision
        (fun i hi ↦ hcollisionOne i (Finset.mem_range.mp hi)))
  have hdegreeProb : uniformProbability degreeFail ≤
      P.candidates.card * pDegree / tDegree := by
    exact CollisionCounting.uniformProbability_eventCount_ge_le
      P.candidates P.degreeBad pDegree tDegree htDegree hdegree
  have htailMean : uniformExpectation (tailBudget P (Q * Real.sqrt v)) ≤
      τ * (Real.sqrt v / Q) :=
    uniformExpectation_tailBudget_le hcard P hv hQ hsecond
  have htailNonneg : ∀ ω, 0 ≤ tailBudget P (Q * Real.sqrt v) ω := by
    intro ω
    apply Finset.sum_nonneg
    intro i hi
    split_ifs <;> positivity
  have htailProb : uniformProbability tailFail ≤
      (τ * (Real.sqrt v / Q)) / κ :=
    uniformProbability_le_of_expectation_le
      (tailBudget P (Q * Real.sqrt v)) κ _ hκ htailNonneg htailMean
  let risk : Sample D s → ℝ := fun ω ↦
    (if geomFail ω then 1 else 0) +
      (if collisionFail ω then 1 else 0) +
      (if degreeFail ω then 1 else 0) +
      (if tailFail ω then 1 else 0)
  have hindicator (A : Sample D s → Prop) :
      uniformExpectation (fun ω ↦ if A ω then 1 else 0) =
        uniformProbability A := by
    classical
    rw [uniformExpectation, uniformProbability]
    congr 1
    simp
  have hriskMean : uniformExpectation risk ≤
      (τ + 1 : ℕ) * pGeom / tGeom +
          (τ + 1 : ℕ) * (P.candidates.card.choose 2 * pCollision / E) /
            tCollision +
          P.candidates.card * pDegree / tDegree +
          (τ * (Real.sqrt v / Q)) / κ := by
    rw [show uniformExpectation risk =
        uniformProbability geomFail + uniformProbability collisionFail +
          uniformProbability degreeFail + uniformProbability tailFail by
      simp only [risk, uniformExpectation_add, hindicator]]
    linarith
  have hriskNonneg : ∀ ω, 0 ≤ risk ω := by
    intro ω
    dsimp only [risk]
    split_ifs <;> norm_num
  have hriskProb : uniformProbability (fun ω ↦ (1 : ℝ) ≤ risk ω) ≤
      (τ + 1 : ℕ) * pGeom / tGeom +
          (τ + 1 : ℕ) * (P.candidates.card.choose 2 * pCollision / E) /
            tCollision +
          P.candidates.card * pDegree / tDegree +
          (τ * (Real.sqrt v / Q)) / κ := by
    simpa only [div_one] using
      (uniformProbability_le_of_expectation_le risk 1 _
        (by norm_num) hriskNonneg hriskMean)
  have hbadProb :
      uniformProbability (fun ω ↦
        geomFail ω ∨ collisionFail ω ∨ degreeFail ω ∨ tailFail ω) < 1 / 2 := by
    calc
      uniformProbability (fun ω ↦
          geomFail ω ∨ collisionFail ω ∨ degreeFail ω ∨ tailFail ω) ≤
          uniformProbability (fun ω ↦ (1 : ℝ) ≤ risk ω) := by
        apply uniformProbability_mono
        intro ω hω
        rcases hω with hω | hω | hω | hω
        · dsimp only [risk]
          rw [if_pos hω]
          split_ifs <;> norm_num
        · dsimp only [risk]
          rw [if_pos hω]
          split_ifs <;> norm_num
        · dsimp only [risk]
          rw [if_pos hω]
          split_ifs <;> norm_num
        · dsimp only [risk]
          rw [if_pos hω]
          split_ifs <;> norm_num
      _ ≤ (τ + 1 : ℕ) * pGeom / tGeom +
          (τ + 1 : ℕ) * (P.candidates.card.choose 2 * pCollision / E) /
            tCollision +
          P.candidates.card * pDegree / tDegree +
          (τ * (Real.sqrt v / Q)) / κ := hriskProb
      _ < 1 / 2 := hfailure
  have hhalf : (1 : ℝ) / 2 ≤
      uniformProbability (fun ω : Sample D s ↦
        (∑ d, P.endpointCoeff d) / 2 ≤
          HalfSample.sliceSum P.endpointCoeff ω) := by
    simpa [HalfSample.sliceProbability, Erdos88.Fourier.finProbability,
      uniformProbability] using
        HalfSample.one_half_le_sliceProbability_ge_half_total
          hcard P.endpointCoeff
  have hendpointMono :
      uniformProbability (fun ω : Sample D s ↦
        (∑ d, P.endpointCoeff d) / 2 ≤
          HalfSample.sliceSum P.endpointCoeff ω) ≤
        uniformProbability endpointGood := by
    apply uniformProbability_mono
    intro ω hω
    dsimp only [endpointGood]
    rw [P.endpointIdentity]
    linarith
  have hendpoint : (1 : ℝ) / 2 ≤ uniformProbability endpointGood :=
    hhalf.trans hendpointMono
  obtain ⟨ω, hωendpoint, hωbad⟩ := exists_good_not_bad
    endpointGood
    (fun ω ↦ geomFail ω ∨ collisionFail ω ∨ degreeFail ω ∨ tailFail ω)
    (1 / 2) hendpoint hbadProb
  push Not at hωbad
  rcases hωbad with ⟨hωgeom', hωcollision', hωdegree', hωtail'⟩
  have hωgeom :
      (CollisionCounting.eventCount (Finset.range (τ + 1))
        P.geometricBad ω : ℝ) < tGeom := by
    exact lt_of_not_ge (by simpa [geomFail] using hωgeom')
  have hωcollision :
      (CollisionCounting.eventCount (Finset.range (τ + 1))
        (collisionBad P E) ω : ℝ) < tCollision := by
    exact lt_of_not_ge (by simpa [collisionFail] using hωcollision')
  have hωdegree :
      (CollisionCounting.eventCount P.candidates P.degreeBad ω : ℝ) <
        tDegree := by
    exact lt_of_not_ge (by simpa [degreeFail] using hωdegree')
  have hωtail : tailBudget P (Q * Real.sqrt v) ω < κ := by
    exact lt_of_not_ge (by simpa [tailFail] using hωtail')
  have hrho : 0 < Q * Real.sqrt v := mul_pos hQ (Real.sqrt_pos.2 hv)
  have hlarge : Switching.largeIncrementSum (P.path ω)
      (Q * Real.sqrt v) τ ≤ κ := by
    exact (largeIncrementSum_le_tailBudget P hrho.le ω).trans hωtail.le
  obtain ⟨idx, hidx, hzero, hlast, hstep⟩ :=
    Switching.separatedSwitchingSubsequence
      (P.path ω) hm hrho hsigma hωendpoint hlarge hbudget
  exact ⟨ω, idx, hωgeom, hωcollision, hωdegree, hωtail,
    hωendpoint, hidx, hzero, hlast, hstep⟩

/-! ## Turán thinning and separated windows -/

/-- Collision graph of a finite candidate family at a fixed exposure and
switching time. -/
def valueCollisionGraph {A B : Type*} (C : Finset A) (f : A → B) :
    SimpleGraph {x // x ∈ C} :=
  SimpleGraph.mk
    (fun x y ↦ x ≠ y ∧ f x = f y)
    ⟨by
      intro x y h
      exact ⟨h.1.symm, h.2.symm⟩⟩
    ⟨by intro x h; exact h.1 rfl⟩

@[simp] lemma valueCollisionGraph_adj
    {A B : Type*} {C : Finset A} {f : A → B}
    {x y : {x // x ∈ C}} :
    (valueCollisionGraph C f).Adj x y ↔ x ≠ y ∧ f x = f y := by
  simp [valueCollisionGraph]

/-- Turán thinning of a collision graph.  The output family is a subset of
`C` on which `f` is injective, with the exact total-edge lower bound. -/
theorem exists_injective_subfamily_card_sq_le
    {A : Type*} [DecidableEq A] (C : Finset A)
    {B : Type*} (f : A → B) :
    ∃ Y : Finset A, Y ⊆ C ∧ Set.InjOn f (Y : Set A) ∧
      C.card ^ 2 ≤ Y.card *
        (C.card + 2 * (valueCollisionGraph C f).edgeFinset.card) := by
  classical
  let H := valueCollisionGraph C f
  let : DecidableRel H.Adj := Classical.decRel _
  obtain ⟨S, hSind, hbound⟩ :=
    exists_indepSet_card_sq_le_card_mul_card_add_twice_edges H
  let Y : Finset A := S.image Subtype.val
  have hYsub : Y ⊆ C := by
    intro x hx
    obtain ⟨y, _hy, rfl⟩ := Finset.mem_image.mp hx
    exact y.2
  have hYcard : Y.card = S.card := by
    exact Finset.card_image_of_injective S Subtype.val_injective
  have hYinj : Set.InjOn f (Y : Set A) := by
    intro x hx y hy hxy
    obtain ⟨x', hx'S, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y', hy'S, rfl⟩ := Finset.mem_image.mp hy
    apply congrArg Subtype.val
    by_contra hne
    exact hSind hx'S hy'S hne
      (valueCollisionGraph_adj.mpr ⟨hne, hxy⟩)
  refine ⟨Y, hYsub, hYinj, ?_⟩
  simpa [H, hYcard] using hbound

/-- A numerical collision-edge budget gives the corresponding clean
injective-family estimate. -/
theorem exists_injective_subfamily_card_sq_le_of_edges_le
    {A : Type*} [DecidableEq A] (C : Finset A)
    {B : Type*} (f : A → B) (edgeBudget : ℕ)
    (hedges : (valueCollisionGraph C f).edgeFinset.card ≤ edgeBudget) :
    ∃ Y : Finset A, Y ⊆ C ∧ Set.InjOn f (Y : Set A) ∧
      C.card ^ 2 ≤ Y.card * (C.card + 2 * edgeBudget) := by
  obtain ⟨Y, hYC, hYinj, hY⟩ :=
    exists_injective_subfamily_card_sq_le C f
  refine ⟨Y, hYC, hYinj, hY.trans ?_⟩
  exact Nat.mul_le_mul_left Y.card
    (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hedges) C.card)

/-- Consecutive rises of size `sigma` in a finite chain imply pairwise
`sigma`-separation. -/
lemma sigma_le_abs_sub_of_chain
    {m : ℕ} (q : Fin (m + 1) → ℝ) {sigma : ℝ}
    (hsigma : 0 < sigma)
    (hstep : ∀ j : Fin m, sigma ≤ q j.succ - q j.castSucc)
    {i j : Fin (m + 1)} (hij : i ≠ j) :
    sigma ≤ |q i - q j| := by
  have hqStrict : StrictMono q := by
    rw [Fin.strictMono_iff_lt_succ]
    intro k
    linarith [hstep k]
  have hforward : ∀ {a b : Fin (m + 1)}, a < b →
      sigma ≤ |q a - q b| := by
    intro a b hab
    have ham : a.val < m := by omega
    let k : Fin m := ⟨a.val, ham⟩
    have hkcast : k.castSucc = a := by apply Fin.ext; rfl
    have hksucc : k.succ ≤ b := by
      rw [Fin.mk_le_mk]
      exact Nat.succ_le_of_lt (Fin.val_fin_lt.mpr hab)
    have hmono : q k.succ ≤ q b := hqStrict.monotone hksucc
    have hs := hstep k
    rw [hkcast] at hs
    have habq : q a ≤ q b := hqStrict.monotone hab.le
    rw [abs_of_nonpos (sub_nonpos.mpr habq)]
    linarith
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hforward hij
  · simpa [abs_sub_comm] using hforward hji

/-- Good candidates in the selected exposure. -/
def goodCandidates {D : Type u} [Fintype D] {X : Type v}
    [DecidableEq X] {s τ : ℕ} (P : PartialExposureData D X s τ)
    (ω : Sample D s) : Finset X :=
  P.candidates.filter fun x ↦ ¬ P.degreeBad x ω

/-- Convert the collision-good event produced by
`exists_fullExposure_switching` into the natural-number edge budget used by
Turán thinning.  The comparison hypothesis is the deterministic relabeling
of unordered graph edges by increasing ordered pairs. -/
lemma valueCollisionGraph_card_le_of_not_collisionBad
    {D : Type u} [Fintype D]
    {X : Type v} [LinearOrder X] [DecidableEq X]
    {s τ i edgeBudget : ℕ}
    (P : PartialExposureData D X s τ) (ω : Sample D s) (E : ℝ)
    (hgood : ¬ collisionBad P E i ω)
    (hcompare :
      (valueCollisionGraph (goodCandidates P ω)
        (fun x ↦ P.value i x ω)).edgeFinset.card ≤
          (CollisionCounting.collisionEdges
            P.candidates (P.value i) ω).card)
    (hE : E ≤ edgeBudget + 1) :
    (valueCollisionGraph (goodCandidates P ω)
      (fun x ↦ P.value i x ω)).edgeFinset.card ≤ edgeBudget := by
  have hcollision :
      ((CollisionCounting.collisionEdges
        P.candidates (P.value i) ω).card : ℝ) < E := by
    exact lt_of_not_ge hgood
  have hcompareReal :
      ((valueCollisionGraph (goodCandidates P ω)
        (fun x ↦ P.value i x ω)).edgeFinset.card : ℝ) ≤
          (CollisionCounting.collisionEdges
            P.candidates (P.value i) ω).card := by
    exact_mod_cast hcompare
  have hltReal :
      ((valueCollisionGraph (goodCandidates P ω)
        (fun x ↦ P.value i x ω)).edgeFinset.card : ℝ) < edgeBudget + 1 :=
    hcompareReal.trans_lt (hcollision.trans_le hE)
  have hltNat :
      (valueCollisionGraph (goodCandidates P ω)
        (fun x ↦ P.value i x ω)).edgeFinset.card < edgeBudget + 1 := by
    exact_mod_cast hltReal
  omega

/-- **Separated-window output of the full exposure.**

At each retained good switching time, Turán removes all remaining
collisions.  The surviving candidates lie in a radius-`R` window about the
switching centre.  Consecutive switching separation and `2R < sigma` make
the centres, and hence the windows, pairwise separated.  This statement is
generic in the actual integer extension value, so `Augmentation.lean` can
instantiate it with its canonical graph edge-count increment. -/
theorem exists_injective_separated_windows
    {D : Type u} [Fintype D]
    {X : Type v} [DecidableEq X]
    {s τ m edgeBudget : ℕ}
    (P : PartialExposureData D X s τ) (ω : Sample D s)
    (idx : Fin (m + 1) → ℕ) (J : Finset (Fin (m + 1)))
    {sigma R : ℝ}
    (hsigma : 0 < sigma) (hR : 2 * R < sigma)
    (hidx : StrictMono idx) (hlast : idx (Fin.last m) = τ)
    (hstep : ∀ j : Fin m,
      sigma ≤ P.path ω (idx j.succ) - P.path ω (idx j.castSucc))
    (hgoodIndex : ∀ j ∈ J, ¬ P.geometricBad (idx j) ω)
    (hwindow : ∀ i ≤ τ, ∀ x ∈ P.candidates,
      ¬ P.geometricBad i ω → ¬ P.degreeBad x ω →
        |(P.value i x ω : ℝ) - P.path ω i| ≤ R)
    (hedges : ∀ j ∈ J,
      (valueCollisionGraph (goodCandidates P ω)
        (fun x ↦ P.value (idx j) x ω)).edgeFinset.card ≤ edgeBudget) :
    ∃ Y : Fin (m + 1) → Finset X,
      (∀ j ∈ J, Y j ⊆ goodCandidates P ω) ∧
      (∀ j ∈ J,
        Set.InjOn (fun x ↦ P.value (idx j) x ω) (Y j : Set X)) ∧
      (∀ j ∈ J,
        (goodCandidates P ω).card ^ 2 ≤
          (Y j).card * ((goodCandidates P ω).card + 2 * edgeBudget)) ∧
      (∀ j ∈ J, ∀ x ∈ Y j,
        |(P.value (idx j) x ω : ℝ) - P.path ω (idx j)| ≤ R) ∧
      (∀ j ∈ J, ∀ k ∈ J, j ≠ k →
        2 * R < |P.path ω (idx j) - P.path ω (idx k)|) := by
  classical
  have hidxLe : ∀ j : Fin (m + 1), idx j ≤ τ := by
    intro j
    rw [← hlast]
    exact hidx.monotone (Fin.le_last j)
  let Y : Fin (m + 1) → Finset X := fun j ↦
    if hj : j ∈ J then
      Classical.choose (exists_injective_subfamily_card_sq_le_of_edges_le
        (goodCandidates P ω) (fun x ↦ P.value (idx j) x ω)
          edgeBudget (hedges j hj))
    else ∅
  have hY (j : Fin (m + 1)) (hj : j ∈ J) :
      Y j ⊆ goodCandidates P ω ∧
      Set.InjOn (fun x ↦ P.value (idx j) x ω) (Y j : Set X) ∧
      (goodCandidates P ω).card ^ 2 ≤
        (Y j).card * ((goodCandidates P ω).card + 2 * edgeBudget) := by
    dsimp only [Y]
    rw [dif_pos hj]
    exact Classical.choose_spec
      (exists_injective_subfamily_card_sq_le_of_edges_le
        (goodCandidates P ω) (fun x ↦ P.value (idx j) x ω)
          edgeBudget (hedges j hj))
  refine ⟨Y, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    exact (hY j hj).1
  · intro j hj
    exact (hY j hj).2.1
  · intro j hj
    exact (hY j hj).2.2
  · intro j hj x hx
    apply hwindow (idx j) (hidxLe j) x
    · exact (Finset.mem_filter.mp ((hY j hj).1 hx)).1
    · exact hgoodIndex j hj
    · exact (Finset.mem_filter.mp ((hY j hj).1 hx)).2
  · intro j hj k hk hjk
    exact hR.trans_le (sigma_le_abs_sub_of_chain
      (fun a ↦ P.path ω (idx a)) hsigma hstep hjk)

end

end AugmentationFull
end Erdos636
