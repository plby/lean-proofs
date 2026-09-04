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

import ErdosProblems.Erdos636.Augmentation
import ErdosProblems.Erdos636.AugmentationGraphFullIdentity
import ErdosProblems.Erdos636.AugmentationGraphFullProbability
import ErdosProblems.Erdos636.AugmentationGraphFullState

/-!
# The graph-valued full exposure for Erdős Problem 636

This file is the graph-facing boundary of Kwan--Sudakov Claim 4.9.  The
abstract probability calculation is in `AugmentationFull.lean`; here its
half-slice is decoded as an actual deletion set and its successful event is
transported to the canonical augmentation image.

The distinction between the two probability spaces matters.  Conditional
on an outer set `D₁` of cardinality `2 nD`, `AugmentationFull.Sample D₁ nD`
is a Boolean-function representation of a uniform half of `D₁`, whereas
`NestedUniform.layerProbability D₁ nD` is the finset representation used by
the balanced-augmentation endpoint.  The equivalence below proves that no
independence or asymptotic approximation is hidden in this change of model.
-/

open Classical SimpleGraph
open scoped BigOperators

namespace Erdos636
namespace AugmentationGraphFull

open Erdos88.Concentration

universe u v

noncomputable section

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## The canonical high-to-low graph path -/

/-- Reverse the degree-sorted state path.  The selector enumerates low to
high; Kwan--Sudakov need high to low, since deleting half of `D₁` then
makes the expected literal edge-count path increase.  Values after time `n`
are irrelevant and are fixed to the low endpoint. -/
noncomputable def reversedCellState
    {A : Type*} [DecidableEq A]
    {source candidates : Finset A} {bad : A → Prop} {degree : A → ℤ}
    {n gap badBudget : ℕ}
    (S : AugmentationGraphFullState.SelectedSwitchingData
      source candidates bad degree n gap badBudget)
    (i : ℕ) : Finset A :=
  if hi : i < n + 1 then S.state (Fin.rev ⟨i, hi⟩) else S.state 0

@[simp] lemma reversedCellState_zero
    {A : Type*} [DecidableEq A]
    {source candidates : Finset A} {bad : A → Prop} {degree : A → ℤ}
    {n gap badBudget : ℕ}
    (S : AugmentationGraphFullState.SelectedSwitchingData
      source candidates bad degree n gap badBudget) :
    reversedCellState S 0 = S.high := by
  simp [reversedCellState]

@[simp] lemma reversedCellState_last
    {A : Type*} [DecidableEq A]
    {source candidates : Finset A} {bad : A → Prop} {degree : A → ℤ}
    {n gap badBudget : ℕ}
    (S : AugmentationGraphFullState.SelectedSwitchingData
      source candidates bad degree n gap badBudget) :
    reversedCellState S n = S.low := by
  rw [reversedCellState, dif_pos (by omega)]
  have hlast : (⟨n, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext rfl
  rw [hlast, Fin.rev_last, S.state_zero]

lemma reversedCellState_subset_source
    {A : Type*} [DecidableEq A]
    {source candidates : Finset A} {bad : A → Prop} {degree : A → ℤ}
    {n gap badBudget : ℕ}
    (S : AugmentationGraphFullState.SelectedSwitchingData
      source candidates bad degree n gap badBudget)
    {i : ℕ} (hi : i ≤ n) : reversedCellState S i ⊆ source := by
  rw [reversedCellState, dif_pos (by omega)]
  exact S.state_subset_source _

@[simp] lemma card_reversedCellState
    {A : Type*} [DecidableEq A]
    {source candidates : Finset A} {bad : A → Prop} {degree : A → ℤ}
    {n gap badBudget : ℕ}
    (S : AugmentationGraphFullState.SelectedSwitchingData
      source candidates bad degree n gap badBudget)
    {i : ℕ} (hi : i ≤ n) : (reversedCellState S i).card = n := by
  rw [reversedCellState, dif_pos (by omega)]
  exact S.card_state _

lemma reversedCellState_disjoint_candidates
    {A : Type*} [DecidableEq A]
    {source candidates : Finset A} {bad : A → Prop} {degree : A → ℤ}
    {n gap badBudget : ℕ}
    (S : AugmentationGraphFullState.SelectedSwitchingData
      source candidates bad degree n gap badBudget)
    {i : ℕ} (hi : i ≤ n) :
    Disjoint (reversedCellState S i) candidates := by
  exact S.source_away_candidates.mono_left
    (reversedCellState_subset_source S hi)

/-- Decode the inner Fourier half-slice as an ambient vertex finset. -/
def sampleFinset (D₁ : Finset V) (nD : ℕ)
    (omega : AugmentationFull.Sample D₁ nD) : Finset V :=
  Augmentation.mapSubtypeFinset D₁ omega.1

@[simp] lemma sampleFinset_mem_layer (D₁ : Finset V) (nD : ℕ)
    (omega : AugmentationFull.Sample D₁ nD) :
    sampleFinset D₁ nD omega ∈ NestedUniform.layer D₁ nD := by
  rw [NestedUniform.mem_layer]
  exact ⟨Augmentation.mapSubtypeFinset_subset D₁ omega.1,
    (Augmentation.card_mapSubtypeFinset D₁ omega.1).trans omega.2⟩

lemma sampleFinset_subset (D₁ : Finset V) (nD : ℕ)
    (omega : AugmentationFull.Sample D₁ nD) :
    sampleFinset D₁ nD omega ⊆ D₁ := by
  exact (NestedUniform.mem_layer.mp (sampleFinset_mem_layer D₁ nD omega)).1

@[simp] lemma card_sampleFinset (D₁ : Finset V) (nD : ℕ)
    (omega : AugmentationFull.Sample D₁ nD) :
    (sampleFinset D₁ nD omega).card = nD := by
  exact (NestedUniform.mem_layer.mp (sampleFinset_mem_layer D₁ nD omega)).2

/-- The concrete inner-success event needed by the nested-uniform argument. -/
def innerGood (G : SimpleGraph V) (W U₀ : Finset V)
    (M : Finset (Finset V)) (nZ : ℕ) (L : ℝ) (D : Finset V) : Prop :=
  L ≤ ((Augmentation.augmentationEdgeValues G W U₀ D M nZ).card : ℝ)

/-- The strengthened inner event needed by the outer switching argument.
Besides its cardinality it retains the actual value family and a common
real window, so it can be used directly as a `SeparatedWindows.piece`. -/
def innerWindowGood (G : SimpleGraph V) (W U₀ : Finset V)
    (M : Finset (Finset V)) (nZ : ℕ) (L center radius : ℝ)
    (D : Finset V) : Prop :=
  ∃ piece : Finset ℕ,
    piece ⊆ Augmentation.augmentationEdgeValues G W U₀ D M nZ ∧
    L ≤ (piece.card : ℝ) ∧
    ∀ e ∈ piece, |(e : ℝ) - center| ≤ radius

lemma innerWindowGood.innerGood
    {G : SimpleGraph V} {W U₀ : Finset V}
    {M : Finset (Finset V)} {nZ : ℕ} {L center radius : ℝ}
    {D : Finset V}
    (h : innerWindowGood G W U₀ M nZ L center radius D) :
    innerGood G W U₀ M nZ L D := by
  rcases h with ⟨piece, hpiece, hcard, _hwindow⟩
  exact hcard.trans (by exact_mod_cast Finset.card_le_card hpiece)

/-- Move a witnessed augmentation piece from an auxiliary centre to a
canonical centre, enlarging the radius by the certified centre error.  In
applications the old centre may depend on the outer half-reservoir and its
selected switching state, while the new centre depends only on the final
deletion set. -/
lemma innerWindowGood_recenter
    {G : SimpleGraph V} {W U₀ : Finset V}
    {M : Finset (Finset V)} {nZ : ℕ}
    {L oldCenter oldRadius newCenter newRadius : ℝ} {D : Finset V}
    (hgood : innerWindowGood G W U₀ M nZ L oldCenter oldRadius D)
    (hcenter : |oldCenter - newCenter| + oldRadius ≤ newRadius) :
    innerWindowGood G W U₀ M nZ L newCenter newRadius D := by
  rcases hgood with ⟨piece, hsub, hcard, hwindow⟩
  refine ⟨piece, hsub, hcard, ?_⟩
  intro e he
  calc
    |(e : ℝ) - newCenter| =
        |((e : ℝ) - oldCenter) + (oldCenter - newCenter)| := by ring_nf
    _ ≤ |(e : ℝ) - oldCenter| + |oldCenter - newCenter| := abs_add_le _ _
    _ ≤ oldRadius + |oldCenter - newCenter| := by
      gcongr
      exact hwindow e he
    _ = |oldCenter - newCenter| + oldRadius := by ring
    _ ≤ newRadius := hcenter

/-- Probability-level recentering on one uniform layer.  Only deletion sets
in the sampled layer need satisfy the centre-error estimate. -/
theorem layerProbability_innerWindowGood_recenter
    (G : SimpleGraph V) (W U₀ D₁ : Finset V)
    (M : Finset (Finset V)) (nD nZ : ℕ) (L oldRadius newRadius q : ℝ)
    (oldCenter newCenter : Finset V → ℝ)
    (hprob : q ≤ NestedUniform.layerProbability D₁ nD
      (fun D ↦ innerWindowGood G W U₀ M nZ L
        (oldCenter D) oldRadius D))
    (hcenter : ∀ D ∈ NestedUniform.layer D₁ nD,
      |oldCenter D - newCenter D| + oldRadius ≤ newRadius) :
    q ≤ NestedUniform.layerProbability D₁ nD
      (fun D ↦ innerWindowGood G W U₀ M nZ L
        (newCenter D) newRadius D) := by
  apply hprob.trans
  unfold NestedUniform.layerProbability
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Finset.card_le_card (by
      intro D hD
      rw [Finset.mem_filter] at hD ⊢
      exact ⟨hD.1, innerWindowGood_recenter hD.2 (hcenter D hD.1)⟩)
  · positivity

/-! ## Canonical graph-valued exposure data -/

/-- The vertex union of a family of matching cells. -/
def cellUnion (Z : Finset (Finset V)) : Finset V := Z.biUnion id

lemma cellUnion_disjoint_right_of_away
    {Z M : Finset (Finset V)} {B : Finset V}
    (hZM : Z ⊆ M) (haway : ∀ x ∈ M, Disjoint x B) :
    Disjoint (cellUnion Z) B := by
  rw [cellUnion, Finset.disjoint_biUnion_left]
  intro x hx
  exact haway x (hZM hx)

lemma cellUnion_disjoint_cell_of_pairwise
    {Z M : Finset (Finset V)} {x : Finset V}
    (hpair : (M : Set (Finset V)).PairwiseDisjoint id)
    (hZM : Z ⊆ M) (hxM : x ∈ M) (hxZ : x ∉ Z) :
    Disjoint (cellUnion Z) x := by
  rw [cellUnion, Finset.disjoint_biUnion_left]
  intro y hy
  have hyM := hZM hy
  have hyx : y ≠ x := by
    intro h
    exact hxZ (h ▸ hy)
  exact hpair hyM hxM hyx

/-- The graph exposed at switching time `i`, before the final candidate cell
is adjoined. -/
def exposedBase {J : Type*} (W U₀ D : Finset V)
    (state : J → Finset (Finset V)) (i : J) : Finset V :=
  (W ∪ (U₀ \ D)) ∪ cellUnion (state i)

/-- The literal induced edge count after adjoining candidate `x`. -/
def exposedValue {J : Type*} (G : SimpleGraph V) (W U₀ D : Finset V)
    (state : J → Finset (Finset V)) (i : J) (x : Finset V) : ℕ :=
  Erdos88.inducedEdges G (exposedBase W U₀ D state i ∪ x)

/-- The literal real edge-count path associated with a family of cell
states. -/
def literalGraphPath (G : SimpleGraph V) (W U₀ D : Finset V)
    (state : ℕ → Finset (Finset V)) (i : ℕ) : ℝ :=
  AugmentationGraphFullIdentity.literalPath G W U₀ D (cellUnion (state i))

/-- The literal base path translated by the deterministic contribution of
the one candidate cell which will later be adjoined.  Translation leaves
all increments and the endpoint affine identity unchanged, but it is
essential for centering an `(nS + 1)`-cell augmentation while the switching
state itself contains only `nS` cells. -/
def translatedLiteralGraphPath (G : SimpleGraph V) (W U₀ D : Finset V)
    (state : ℕ → Finset (Finset V)) (pathShift : ℝ) (i : ℕ) : ℝ :=
  literalGraphPath G W U₀ D state i + pathShift

/-- Canonical centre used by the window event: the literal edge count at
the high-degree initial state, after the actual deletion `D`. -/
def augmentationCenter (G : SimpleGraph V) (W U₀ D : Finset V)
    (state : ℕ → Finset (Finset V)) : ℝ :=
  literalGraphPath G W U₀ D state 0

/-- Candidate-degree failure on the inner half-slice.  It is deliberately
independent of switching time; one deletion-degree concentration estimate
therefore controls all time indices simultaneously. -/
def degreeDeviationBad (G : SimpleGraph V) (D₁ : Finset V) (nD : ℕ)
    (T : ℝ) (x : Finset V) (omega : AugmentationFull.Sample D₁ nD) : Prop :=
  T ≤ |(degreeInto G
      (AugmentationGraphFullIdentity.halfDeletion D₁ nD omega) x : ℝ) -
    (degreeInto G D₁ x : ℝ) / 2|

theorem uniformProbability_degreeDeviationBad_le
    (G : SimpleGraph V) (D₁ x : Finset V) (nD K : ℕ) (T : ℝ)
    (hhalf : D₁.card = 2 * nD) (hnD : 0 < nD)
    (hK : 0 < K) (hT : 0 ≤ T) (hxK : x.card ≤ K) :
    uniformProbability (degreeDeviationBad G D₁ nD T x) ≤
      2 * Real.exp (-T ^ 2 / (2 * nD * (4 * K) ^ 2)) := by
  have hcard : Fintype.card D₁ = 2 * nD := by simpa using hhalf
  have htail :=
    AugmentationGraphFullProbability.halfSlice_sum_two_sided_probability
      hcard hnD
      (fun u : D₁ ↦
        (AugmentationGraphFullIdentity.reservoirIncidence G D₁ x u : ℝ))
      (K : ℝ) T (by positivity) hT (by
        intro u
        exact_mod_cast
          AugmentationGraphFullIdentity.abs_reservoirIncidence_le_of_card_le
            G D₁ x K hxK u)
  have hsum : (∑ u : D₁,
      (AugmentationGraphFullIdentity.reservoirIncidence G D₁ x u : ℝ)) =
      (degreeInto G D₁ x : ℝ) := by
    exact_mod_cast
      AugmentationGraphFullIdentity.sum_reservoirIncidence_eq_degreeInto G D₁ x
  change uniformProbability (fun omega : HalfSample.Slice D₁ nD ↦
      T ≤ |(degreeInto G
        (AugmentationGraphFullIdentity.halfDeletion D₁ nD omega) x : ℝ) -
        (degreeInto G D₁ x : ℝ) / 2|) ≤ _
  simpa only [
    AugmentationGraphFullIdentity.halfSliceSum_incidenceVector_eq_degreeInto_halfDeletion,
    hsum] using htail

/-- Closed-form candidate-collision probability from the diversity and
degree-window information retained by `PartialGood`. -/
theorem uniformProbability_literalCandidateCollision_le
    (G : SimpleGraph V) (W U₀ D₁ Z x y : Finset V) (nD K : ℕ)
    (center radius c theta : ℝ)
    (hhalf : D₁.card = 2 * nD) (hnD : 0 < nD)
    (hK : 1 ≤ K) (hc0 : 0 < c) (hc1 : c ≤ 1 / 2)
    (htheta : 0 < theta)
    (hsel : c * D₁.card ≤ nD)
    (hunsel : c * D₁.card ≤ D₁.card - nD)
    (hxK : x.card ≤ K) (hyK : y.card ≤ K)
    (hxgood : AugmentationGraphPartial.DegreeGood G D₁ x center radius)
    (hygood : AugmentationGraphPartial.DegreeGood G D₁ y center radius)
    (hdiverse : theta * D₁.card ≤ incidenceDiffMass G D₁ x y)
    (hsmallWindow : 2 * radius < theta / 2 * D₁.card)
    (hD₁U₀ : D₁ ⊆ U₀) (hWU₀ : Disjoint W U₀)
    (hWZ : Disjoint W Z) (hU₀Z : Disjoint U₀ Z)
    (hWx : Disjoint W x) (hU₀x : Disjoint U₀ x) (hZx : Disjoint Z x)
    (hWy : Disjoint W y) (hU₀y : Disjoint U₀ y) (hZy : Disjoint Z y) :
    uniformProbability (fun omega : AugmentationFull.Sample D₁ nD ↦
      Erdos88.inducedEdges G
          (AugmentationGraphFullIdentity.literalState W U₀
            (AugmentationGraphFullIdentity.halfDeletion D₁ nD omega) Z ∪ x) =
        Erdos88.inducedEdges G
          (AugmentationGraphFullIdentity.literalState W U₀
            (AugmentationGraphFullIdentity.halfDeletion D₁ nD omega) Z ∪ y)) ≤
      AntiConcentration.variancePointMassConstant c (theta ^ 2 / 4) K /
        Real.sqrt (D₁.card : ℝ) := by
  classical
  let a : D₁ → ℤ := fun u ↦
    AugmentationGraphFullIdentity.reservoirIncidence G D₁ y u -
      AugmentationGraphFullIdentity.reservoirIncidence G D₁ x u
  have hI : 0 < Fintype.card D₁ := by simp only [Fintype.card_coe, hhalf]; omega
  have hs : nD ≤ Fintype.card D₁ := by simp only [Fintype.card_coe, hhalf]; omega
  have hbounded : ∀ u, |a u| ≤ (K : ℤ) := by
    intro u
    exact AugmentationGraphFullIdentity.abs_reservoirIncidence_sub_le_of_card_le
      G D₁ x y K hxK hyK u
  have hsum : (∑ u : D₁, (a u : ℝ)) =
      (degreeInto G D₁ y : ℝ) - degreeInto G D₁ x := by
    change (∑ u : D₁,
      AugmentationGraphFullIdentity.replacementCoeff G D₁ x y u) = _
    exact AugmentationGraphFullIdentity.sum_replacementCoeff_eq_degreeInto_sub
      G D₁ x y
  let mu : ℝ := (∑ u : D₁, (a u : ℝ)) / Fintype.card D₁
  have hmean : (Fintype.card D₁ : ℝ) * mu = ∑ u, (a u : ℝ) := by
    dsimp only [mu]
    field_simp
  have hl1 : theta * Fintype.card D₁ ≤ ∑ u, |(a u : ℝ)| := by
    rw [Fintype.card_coe]
    change theta * D₁.card ≤
      ∑ u, |AugmentationGraphFullIdentity.replacementCoeff G D₁ x y u|
    rw [AugmentationGraphFullIdentity.sum_abs_replacementCoeff_eq_incidenceDiffMass]
    exact hdiverse
  have hdiff : |(degreeInto G D₁ y : ℝ) - degreeInto G D₁ x| ≤
      2 * radius := by
    rw [AugmentationGraphPartial.DegreeGood, abs_le] at hxgood hygood
    rw [abs_le]
    constructor <;> linarith [hxgood.1, hxgood.2, hygood.1, hygood.2]
  have hsmall : |∑ u, (a u : ℝ)| < theta / 2 * Fintype.card D₁ := by
    rw [hsum, Fintype.card_coe]
    exact hdiff.trans_lt hsmallWindow
  let target : ℝ :=
    ((AugmentationGraphFullIdentity.candidateOffsetInt G W U₀ Z y -
      AugmentationGraphFullIdentity.candidateOffsetInt G W U₀ Z x : ℤ) : ℝ)
  have hanti :=
    AugmentationGraphFullProbability.halfSlice_point_probability_le_of_integer_l1_small_sum
      a mu c theta K nD hs hc0 hc1 htheta hK hI hbounded hmean hl1 hsmall
        (by simpa only [Fintype.card_coe] using hsel)
        (by simpa only [Fintype.card_coe] using hunsel) target
  have hevent : (fun omega : AugmentationFull.Sample D₁ nD ↦
      Erdos88.inducedEdges G
          (AugmentationGraphFullIdentity.literalState W U₀
            (AugmentationGraphFullIdentity.halfDeletion D₁ nD omega) Z ∪ x) =
        Erdos88.inducedEdges G
          (AugmentationGraphFullIdentity.literalState W U₀
            (AugmentationGraphFullIdentity.halfDeletion D₁ nD omega) Z ∪ y)) =
      (fun omega ↦ HalfSample.sliceSum (fun u ↦ (a u : ℝ)) omega = target) := by
    funext omega
    apply propext
    change _ ↔ HalfSample.sliceSum
      (AugmentationGraphFullIdentity.replacementCoeff G D₁ x y) omega = _
    exact AugmentationGraphFullIdentity.literalCandidateCollision_iff
      G W U₀ D₁ Z x y nD omega hD₁U₀ hWU₀ hWZ hU₀Z
      hWx hU₀x hZx hWy hU₀y hZy
  rw [hevent]
  simpa only [Fintype.card_coe] using hanti

/-- Canonical `PartialExposureData` whose integer value is an actual induced
edge count.  The path and its affine endpoint certificate are kept explicit:
they are furnished by the signed replacement identity once the low/high
switching cells have been selected from `PartialGood`.

Unlike the earlier abstract boundary, this constructor fixes the only field
which enters the augmentation image (`value`) definitionally, so there is no
surrogate edge-count hypothesis downstream. -/
def canonicalPartialExposureData
    (G : SimpleGraph V) (W U₀ D₁ : Finset V)
    (nD tau : ℕ) (state : ℕ → Finset (Finset V))
    (candidates : Finset (Finset V))
    (path : AugmentationFull.Sample D₁ nD → ℕ → ℝ)
    (geometricBad : ℕ → AugmentationFull.Sample D₁ nD → Prop)
    (degreeBad : Finset V → AugmentationFull.Sample D₁ nD → Prop)
    (endpointCoeff : D₁ → ℝ) (endpointOffset : ℝ)
    (endpointIdentity : ∀ omega,
      path omega tau - path omega 0 = endpointOffset +
        HalfSample.sliceSum endpointCoeff omega) :
    AugmentationFull.PartialExposureData D₁ (Finset V) nD tau where
  candidates := candidates
  path := path
  value := fun i x omega ↦
    (exposedValue G W U₀ (sampleFinset D₁ nD omega) state i x : ℤ)
  geometricBad := geometricBad
  degreeBad := degreeBad
  endpointCoeff := endpointCoeff
  endpointOffset := endpointOffset
  endpointIdentity := endpointIdentity

/-- The fully graph-valued partial exposure on a high-to-low cell path.
Its path, extension values, degree failures, endpoint coefficient, and
endpoint offset are all fixed canonically by the graph. -/
noncomputable def canonicalGraphExposureData
    (G : SimpleGraph V) (W U₀ D₁ : Finset V) (nD tau : ℕ)
    (state : ℕ → Finset (Finset V))
    (candidates : Finset (Finset V))
    (pathShift geometricThreshold degreeThreshold : ℝ)
    (hD₁U₀ : D₁ ⊆ U₀) (hWU₀ : Disjoint W U₀)
    (hWzero : Disjoint W (cellUnion (state 0)))
    (hWlast : Disjoint W (cellUnion (state tau)))
    (hUzero : Disjoint U₀ (cellUnion (state 0)))
    (hUlast : Disjoint U₀ (cellUnion (state tau))) :
    AugmentationFull.PartialExposureData D₁ (Finset V) nD tau :=
  canonicalPartialExposureData G W U₀ D₁ nD tau state candidates
    (fun omega i ↦ translatedLiteralGraphPath G W U₀
      (AugmentationGraphFullIdentity.halfDeletion D₁ nD omega) state
        pathShift i)
    (fun i omega ↦ degreeDeviationBad G D₁ nD geometricThreshold
      (cellUnion (state i)) omega)
    (degreeDeviationBad G D₁ nD degreeThreshold)
    (AugmentationGraphFullIdentity.replacementCoeff G D₁
      (cellUnion (state tau)) (cellUnion (state 0)))
    (AugmentationGraphFullIdentity.endpointOffsetInt G W U₀
      (cellUnion (state 0)) (cellUnion (state tau)))
    (by
      intro omega
      have h := AugmentationGraphFullIdentity.literalEndpoint_affine G W U₀ D₁
        (cellUnion (state 0)) (cellUnion (state tau)) nD omega hD₁U₀
        hWU₀ hWzero hWlast hUzero hUlast
      change
        (AugmentationGraphFullIdentity.literalPath G W U₀
              (AugmentationGraphFullIdentity.halfDeletion D₁ nD omega)
              (cellUnion (state tau)) + pathShift) -
            (AugmentationGraphFullIdentity.literalPath G W U₀
              (AugmentationGraphFullIdentity.halfDeletion D₁ nD omega)
              (cellUnion (state 0)) + pathShift) = _
      linarith)

@[simp] lemma canonicalPartialExposureData_candidates
    (G : SimpleGraph V) (W U₀ D₁ : Finset V)
    (nD tau : ℕ) (state : ℕ → Finset (Finset V))
    (candidates : Finset (Finset V))
    (path : AugmentationFull.Sample D₁ nD → ℕ → ℝ)
    (geometricBad : ℕ → AugmentationFull.Sample D₁ nD → Prop)
    (degreeBad : Finset V → AugmentationFull.Sample D₁ nD → Prop)
    (endpointCoeff : D₁ → ℝ) (endpointOffset : ℝ)
    (endpointIdentity : ∀ omega,
      path omega tau - path omega 0 = endpointOffset +
        HalfSample.sliceSum endpointCoeff omega) :
    (canonicalPartialExposureData G W U₀ D₁ nD tau state candidates path
      geometricBad degreeBad endpointCoeff endpointOffset
      endpointIdentity).candidates = candidates := rfl

@[simp] lemma canonicalPartialExposureData_value
    (G : SimpleGraph V) (W U₀ D₁ : Finset V)
    (nD tau : ℕ) (state : ℕ → Finset (Finset V))
    (candidates : Finset (Finset V))
    (path : AugmentationFull.Sample D₁ nD → ℕ → ℝ)
    (geometricBad : ℕ → AugmentationFull.Sample D₁ nD → Prop)
    (degreeBad : Finset V → AugmentationFull.Sample D₁ nD → Prop)
    (endpointCoeff : D₁ → ℝ) (endpointOffset : ℝ)
    (endpointIdentity : ∀ omega,
      path omega tau - path omega 0 = endpointOffset +
        HalfSample.sliceSum endpointCoeff omega)
    (i : ℕ) (x : Finset V) (omega : AugmentationFull.Sample D₁ nD) :
    (canonicalPartialExposureData G W U₀ D₁ nD tau state candidates path
      geometricBad degreeBad endpointCoeff endpointOffset
      endpointIdentity).value i x omega =
      (exposedValue G W U₀ (sampleFinset D₁ nD omega) state i x : ℤ) := rfl

@[simp] lemma cellUnion_insert (x : Finset V) (Z : Finset (Finset V)) :
    cellUnion (insert x Z) = x ∪ cellUnion Z := by
  simp [cellUnion]

/-- Every value produced by one switching state and one new matching cell
belongs to the canonical augmentation image. -/
lemma exposedValue_mem_augmentationEdgeValues
    {J : Type*}
    (G : SimpleGraph V) (W U₀ D : Finset V)
    (M : Finset (Finset V)) (nS : ℕ)
    (state : J → Finset (Finset V)) (i : J) (x : Finset V)
    (hstate : state i ⊆ M) (hcard : (state i).card = nS)
    (hxM : x ∈ M) (hxstate : x ∉ state i) :
    exposedValue G W U₀ D state i x ∈
      Augmentation.augmentationEdgeValues G W U₀ D M (nS + 1) := by
  rw [Augmentation.mem_augmentationEdgeValues]
  refine ⟨insert x (state i), ?_, ?_, ?_⟩
  · exact Finset.insert_subset hxM hstate
  · simp [hxstate, hcard]
  · simp only [exposedValue, exposedBase, cellUnion_insert]
    congr 1
    ext v
    simp only [cellUnion, Finset.mem_union, Finset.mem_biUnion,
      Finset.mem_insert]
    aesop

/-- Disjoint injective value families at several switching states all count
inside one and the same canonical augmentation image. -/
theorem sum_card_le_augmentationEdgeValues
    {J : Type v} [DecidableEq J]
    (G : SimpleGraph V) (W U₀ D : Finset V)
    (M : Finset (Finset V)) (nS : ℕ)
    (state : J → Finset (Finset V))
    (Y : J → Finset (Finset V)) (I : Finset J)
    (hstate : ∀ j ∈ I, state j ⊆ M)
    (hstateCard : ∀ j ∈ I, (state j).card = nS)
    (hYM : ∀ j ∈ I, Y j ⊆ M)
    (haway : ∀ j ∈ I, ∀ x ∈ Y j, x ∉ state j)
    (hinj : ∀ j ∈ I, Set.InjOn
      (fun x ↦ Erdos88.inducedEdges G
        (((W ∪ (U₀ \ D)) ∪ cellUnion (state j)) ∪ x))
      (Y j : Set (Finset V)))
    (hcross : ∀ j ∈ I, ∀ k ∈ I, j ≠ k →
      Disjoint
        ((Y j).image fun x ↦ Erdos88.inducedEdges G
          (((W ∪ (U₀ \ D)) ∪ cellUnion (state j)) ∪ x))
        ((Y k).image fun x ↦ Erdos88.inducedEdges G
          (((W ∪ (U₀ \ D)) ∪ cellUnion (state k)) ∪ x))) :
    ∑ j ∈ I, (Y j).card ≤
      (Augmentation.augmentationEdgeValues G W U₀ D M (nS + 1)).card := by
  classical
  let E : J → Finset ℕ := fun j ↦
    (Y j).image fun x ↦ Erdos88.inducedEdges G
      (((W ∪ (U₀ \ D)) ∪ cellUnion (state j)) ∪ x)
  have hEcard : ∀ j ∈ I, (E j).card = (Y j).card := by
    intro j hj
    change ((Y j).image (fun x ↦ Erdos88.inducedEdges G
      (((W ∪ (U₀ \ D)) ∪ cellUnion (state j)) ∪ x))).card = _
    rw [Finset.card_image_iff.mpr]
    intro x hx y hy hxy
    exact hinj j hj (by simpa using hx) (by simpa using hy) hxy
  have hEdisj : (I : Set J).PairwiseDisjoint E := by
    intro j hj k hk hjk
    exact hcross j hj k hk hjk
  have hEsub : I.biUnion E ⊆
      Augmentation.augmentationEdgeValues G W U₀ D M (nS + 1) := by
    intro e he
    obtain ⟨j, hj, hej⟩ := Finset.mem_biUnion.mp he
    obtain ⟨x, hxY, rfl⟩ := Finset.mem_image.mp hej
    exact exposedValue_mem_augmentationEdgeValues G W U₀ D M nS
      state j x (hstate j hj) (hstateCard j hj)
      (hYM j hj hxY) (haway j hj x hxY)
  calc
    ∑ j ∈ I, (Y j).card = ∑ j ∈ I, (E j).card := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hEcard j hj]
    _ = (I.biUnion E).card := (Finset.card_biUnion hEdisj).symm
    _ ≤ (Augmentation.augmentationEdgeValues G W U₀ D M
        (nS + 1)).card := Finset.card_le_card hEsub

/-- Window form of `sum_card_le_augmentationEdgeValues`, matching the output
of `AugmentationFull.exists_injective_separated_windows`. -/
theorem sum_card_le_augmentationEdgeValues_of_windows
    {J : Type v} [DecidableEq J]
    (G : SimpleGraph V) (W U₀ D : Finset V)
    (M : Finset (Finset V)) (nS : ℕ)
    (state : J → Finset (Finset V))
    (Y : J → Finset (Finset V)) (I : Finset J)
    (center : J → ℝ) (R : ℝ)
    (hstate : ∀ j ∈ I, state j ⊆ M)
    (hstateCard : ∀ j ∈ I, (state j).card = nS)
    (hYM : ∀ j ∈ I, Y j ⊆ M)
    (haway : ∀ j ∈ I, ∀ x ∈ Y j, x ∉ state j)
    (hinj : ∀ j ∈ I, Set.InjOn
      (fun x ↦ Erdos88.inducedEdges G
        (exposedBase W U₀ D state j ∪ x))
      (Y j : Set (Finset V)))
    (hwindow : ∀ j ∈ I, ∀ e ∈
      Augmentation.edgeValues G (exposedBase W U₀ D state j) (Y j),
      |(e : ℝ) - center j| ≤ R)
    (hsep : ∀ j ∈ I, ∀ k ∈ I, j ≠ k →
      2 * R < |center j - center k|) :
    ∑ j ∈ I, (Y j).card ≤
      (Augmentation.augmentationEdgeValues G W U₀ D M (nS + 1)).card := by
  have hdisj := Augmentation.edgeValues_pairwiseDisjoint_of_real_windows
    G I (fun j ↦ exposedBase W U₀ D state j) Y center R hwindow hsep
  apply sum_card_le_augmentationEdgeValues
    G W U₀ D M nS state Y I hstate hstateCard hYM haway hinj
  intro j hj k hk hjk
  exact hdisj hj hk hjk

/-- The concrete union of value families retained at switching times. -/
def switchingPiece {J : Type v} [DecidableEq J]
    (G : SimpleGraph V) (W U₀ D : Finset V)
    (state : J → Finset (Finset V))
    (Y : J → Finset (Finset V)) (I : Finset J) : Finset ℕ :=
  I.biUnion fun j ↦ Augmentation.edgeValues G
    (exposedBase W U₀ D state j) (Y j)

/-- Window-separated, internally injective switching families form one
literal canonical augmentation piece. -/
theorem switchingPiece_spec
    {J : Type v} [DecidableEq J]
    (G : SimpleGraph V) (W U₀ D : Finset V)
    (M : Finset (Finset V)) (nS : ℕ)
    (state : J → Finset (Finset V))
    (Y : J → Finset (Finset V)) (I : Finset J)
    (center : J → ℝ) (R globalCenter globalRadius : ℝ)
    (hstate : ∀ j ∈ I, state j ⊆ M)
    (hstateCard : ∀ j ∈ I, (state j).card = nS)
    (hYM : ∀ j ∈ I, Y j ⊆ M)
    (haway : ∀ j ∈ I, ∀ x ∈ Y j, x ∉ state j)
    (hinj : ∀ j ∈ I, Set.InjOn
      (fun x ↦ Erdos88.inducedEdges G
        (exposedBase W U₀ D state j ∪ x))
      (Y j : Set (Finset V)))
    (hwindow : ∀ j ∈ I, ∀ e ∈
      Augmentation.edgeValues G (exposedBase W U₀ D state j) (Y j),
      |(e : ℝ) - center j| ≤ R)
    (hsep : ∀ j ∈ I, ∀ k ∈ I, j ≠ k →
      2 * R < |center j - center k|)
    (hglobal : ∀ j ∈ I, |center j - globalCenter| + R ≤ globalRadius) :
    switchingPiece G W U₀ D state Y I ⊆
        Augmentation.augmentationEdgeValues G W U₀ D M (nS + 1) ∧
      (switchingPiece G W U₀ D state Y I).card =
        ∑ j ∈ I, (Y j).card ∧
      ∀ e ∈ switchingPiece G W U₀ D state Y I,
        |(e : ℝ) - globalCenter| ≤ globalRadius := by
  classical
  let E : J → Finset ℕ := fun j ↦
    Augmentation.edgeValues G (exposedBase W U₀ D state j) (Y j)
  have hEcard : ∀ j ∈ I, (E j).card = (Y j).card := by
    intro j hj
    change ((Y j).image (fun x ↦
      Erdos88.inducedEdges G (exposedBase W U₀ D state j ∪ x))).card = _
    rw [Finset.card_image_iff.mpr]
    intro x hx y hy hxy
    exact hinj j hj (by simpa using hx) (by simpa using hy) hxy
  have hEdisj : (I : Set J).PairwiseDisjoint E := by
    have hdisj := Augmentation.edgeValues_pairwiseDisjoint_of_real_windows
      G I (fun j ↦ exposedBase W U₀ D state j) Y center R hwindow hsep
    intro j hj k hk hjk
    exact hdisj hj hk hjk
  have hsub : I.biUnion E ⊆
      Augmentation.augmentationEdgeValues G W U₀ D M (nS + 1) := by
    intro e he
    obtain ⟨j, hj, hej⟩ := Finset.mem_biUnion.mp he
    obtain ⟨x, hxY, rfl⟩ := Augmentation.mem_edgeValues.mp hej
    exact exposedValue_mem_augmentationEdgeValues G W U₀ D M nS
      state j x (hstate j hj) (hstateCard j hj)
      (hYM j hj hxY) (haway j hj x hxY)
  have hcard : (I.biUnion E).card = ∑ j ∈ I, (Y j).card := by
    rw [Finset.card_biUnion hEdisj]
    apply Finset.sum_congr rfl
    intro j hj
    exact hEcard j hj
  have hcommon : ∀ e ∈ I.biUnion E,
      |(e : ℝ) - globalCenter| ≤ globalRadius := by
    intro e he
    obtain ⟨j, hj, hej⟩ := Finset.mem_biUnion.mp he
    have hw := hwindow j hj e (by simpa [E] using hej)
    calc
      |(e : ℝ) - globalCenter| =
          |((e : ℝ) - center j) + (center j - globalCenter)| := by ring_nf
      _ ≤ |(e : ℝ) - center j| + |center j - globalCenter| :=
        abs_add_le _ _
      _ ≤ R + |center j - globalCenter| := by gcongr
      _ = |center j - globalCenter| + R := by ring
      _ ≤ globalRadius := hglobal j hj
  simpa [switchingPiece, E] using And.intro hsub (And.intro hcard hcommon)

/-! ## Retaining good switching indices -/

/-- Pulling a bad predicate back along an injective path cannot increase its
count.  This is the exact finite bookkeeping behind deleting the exceptional
times in Claim 4.9. -/
lemma card_filter_bad_comp_le_eventCount
    {Omega : Type*} [Fintype Omega]
    (omega : Omega) (tau r : ℕ) (idx : Fin r → ℕ)
    (hidx : Function.Injective idx) (hidxLe : ∀ j, idx j ≤ tau)
    (bad : ℕ → Omega → Prop) :
    ((Finset.univ : Finset (Fin r)).filter fun j ↦ bad (idx j) omega).card ≤
      CollisionCounting.eventCount (Finset.range (tau + 1)) bad omega := by
  classical
  let B : Finset (Fin r) :=
    (Finset.univ : Finset (Fin r)).filter fun j ↦ bad (idx j) omega
  have hcard : (B.image idx).card = B.card :=
    Finset.card_image_of_injective B hidx
  rw [← hcard]
  apply Finset.card_le_card
  intro i hi
  obtain ⟨j, hjB, rfl⟩ := Finset.mem_image.mp hi
  simp only [CollisionCounting.eventCount, Finset.mem_filter]
  exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hidxLe j)),
    (Finset.mem_filter.mp hjB).2⟩

/-- After deleting times bad for either of two reasons, at least
`r - (b₀+b₁)` switching indices remain. -/
lemma sub_add_le_card_filter_two_good
    {Omega : Type*} [Fintype Omega]
    (omega : Omega) (tau r b₀ b₁ : ℕ) (idx : Fin r → ℕ)
    (hidx : Function.Injective idx) (hidxLe : ∀ j, idx j ≤ tau)
    (bad₀ bad₁ : ℕ → Omega → Prop)
    (hbad₀ : CollisionCounting.eventCount
      (Finset.range (tau + 1)) bad₀ omega ≤ b₀)
    (hbad₁ : CollisionCounting.eventCount
      (Finset.range (tau + 1)) bad₁ omega ≤ b₁) :
    r - (b₀ + b₁) ≤
      ((Finset.univ : Finset (Fin r)).filter fun j ↦
        ¬ bad₀ (idx j) omega ∧ ¬ bad₁ (idx j) omega).card := by
  classical
  let B₀ : Finset (Fin r) :=
    (Finset.univ : Finset (Fin r)).filter fun j ↦ bad₀ (idx j) omega
  let B₁ : Finset (Fin r) :=
    (Finset.univ : Finset (Fin r)).filter fun j ↦ bad₁ (idx j) omega
  let B : Finset (Fin r) :=
    (Finset.univ : Finset (Fin r)).filter fun j ↦
      bad₀ (idx j) omega ∨ bad₁ (idx j) omega
  let J : Finset (Fin r) :=
    (Finset.univ : Finset (Fin r)).filter fun j ↦
      ¬ bad₀ (idx j) omega ∧ ¬ bad₁ (idx j) omega
  have hB₀ : B₀.card ≤ b₀ :=
    (card_filter_bad_comp_le_eventCount omega tau r idx hidx hidxLe
      bad₀).trans hbad₀
  have hB₁ : B₁.card ≤ b₁ :=
    (card_filter_bad_comp_le_eventCount omega tau r idx hidx hidxLe
      bad₁).trans hbad₁
  have hBsub : B ⊆ B₀ ∪ B₁ := by
    intro j hj
    simp only [B, B₀, B₁, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union] at hj ⊢
    exact hj
  have hBcard : B.card ≤ b₀ + b₁ := by
    calc
      B.card ≤ (B₀ ∪ B₁).card := Finset.card_le_card hBsub
      _ ≤ B₀.card + B₁.card := Finset.card_union_le _ _
      _ ≤ b₀ + b₁ := Nat.add_le_add hB₀ hB₁
  have hpartition : J.card + B.card = r := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin r)))
      (p := fun j ↦ bad₀ (idx j) omega ∨ bad₁ (idx j) omega)
    have hB : ((Finset.univ : Finset (Fin r)).filter fun j ↦
        bad₀ (idx j) omega ∨ bad₁ (idx j) omega) = B := rfl
    have hJ : ((Finset.univ : Finset (Fin r)).filter fun j ↦
        ¬ (bad₀ (idx j) omega ∨ bad₁ (idx j) omega)) = J := by
      ext j
      simp only [J, Finset.mem_filter, Finset.mem_univ, true_and, not_or]
    rw [hB, hJ] at h
    simp only [Finset.card_univ, Fintype.card_fin] at h
    omega
  change r - (b₀ + b₁) ≤ J.card
  omega

/-! ## A full event creates a large canonical augmentation image -/

/-- Deterministic graph endpoint of the full exposure.

All inequalities in the statement are finite.  `badGeom`, `badCollision`,
and `badDegree` are integer budgets; `piece` is the Turán survivor size and
`L` is the required total image size.  The two numerical hypotheses at the
end are exactly the multiplication estimates used after deleting bad times
and bad candidate cells. -/
theorem fullExposureEvent_implies_innerWindowGood
    {D : Type v} [Fintype D]
    [LinearOrder (Finset V)]
    (G : SimpleGraph V) (W U₀ Dset : Finset V)
    (M : Finset (Finset V)) (nD nS tau m : ℕ)
    (P : AugmentationFull.PartialExposureData D (Finset V) nD tau)
    (omega : AugmentationFull.Sample D nD)
    (state : ℕ → Finset (Finset V))
    (lam E rho kappa sigma R globalCenter globalRadius : ℝ)
    (badGeom badCollision badDegree edgeBudget piece L : ℕ)
    (hm : 1 ≤ m) (hrho : 0 < rho) (hsigma : 0 < sigma)
    (hR : 2 * R < sigma)
    (hbudget : (m : ℝ) * (rho + sigma) + kappa ≤ lam)
    (hfull : AugmentationFull.FullExposureEvent P lam E rho kappa
      (badGeom + 1) (badCollision + 1) (badDegree + 1) omega)
    (hcandidates : P.candidates ⊆ M)
    (hstate : ∀ i ≤ tau, state i ⊆ M)
    (hstateCard : ∀ i ≤ tau, (state i).card = nS)
    (haway : ∀ i ≤ tau, ∀ x ∈ P.candidates, x ∉ state i)
    (hvalue : ∀ i ≤ tau, ∀ x ∈ P.candidates,
      P.value i x omega =
        (Erdos88.inducedEdges G (exposedBase W U₀ Dset state i ∪ x) : ℤ))
    (hwindow : ∀ i ≤ tau, ∀ x ∈ P.candidates,
      ¬ P.geometricBad i omega → ¬ P.degreeBad x omega →
        |(P.value i x omega : ℝ) - P.path omega i| ≤ R)
    (hglobal : ∀ i ≤ tau, ¬ P.geometricBad i omega →
      |P.path omega i - globalCenter| + R ≤ globalRadius)
    (hcompare : ∀ i ≤ tau,
      (AugmentationFull.valueCollisionGraph
        (AugmentationFull.goodCandidates P omega)
        (fun x ↦ P.value i x omega)).edgeFinset.card ≤
      (CollisionCounting.collisionEdges
        P.candidates (P.value i) omega).card)
    (hE : E ≤ edgeBudget + 1)
    (hcandidateSurvivors : badDegree < P.candidates.card)
    (hpiece : piece * (P.candidates.card + 2 * edgeBudget) ≤
      (P.candidates.card - badDegree) ^ 2)
    (hL : L ≤ ((m + 1) - (badGeom + badCollision)) * piece) :
    innerWindowGood G W U₀ M (nS + 1) L globalCenter globalRadius Dset := by
  classical
  rcases hfull with ⟨hrise, hgeomReal, hcollisionReal, hdegreeReal, htail⟩
  have hgeomNat : CollisionCounting.eventCount
      (Finset.range (tau + 1)) P.geometricBad omega ≤ badGeom := by
    have hlt : CollisionCounting.eventCount
        (Finset.range (tau + 1)) P.geometricBad omega < badGeom + 1 := by
      exact_mod_cast hgeomReal
    omega
  have hcollisionNat : CollisionCounting.eventCount
      (Finset.range (tau + 1)) (AugmentationFull.collisionBad P E) omega ≤
        badCollision := by
    have hlt : CollisionCounting.eventCount
        (Finset.range (tau + 1)) (AugmentationFull.collisionBad P E) omega <
          badCollision + 1 := by
      exact_mod_cast hcollisionReal
    omega
  have hdegreeNat : CollisionCounting.eventCount P.candidates P.degreeBad omega ≤
      badDegree := by
    have hlt : CollisionCounting.eventCount P.candidates P.degreeBad omega <
        badDegree + 1 := by
      exact_mod_cast hdegreeReal
    omega
  have hlarge : Switching.largeIncrementSum (P.path omega) rho tau ≤ kappa :=
    (AugmentationFull.largeIncrementSum_le_tailBudget P hrho.le omega).trans
      htail.le
  obtain ⟨idx, hidx, hidxZero, hidxLast, hstep⟩ :=
    Switching.separatedSwitchingSubsequence (P.path omega) hm hrho hsigma
      hrise hlarge hbudget
  have hidxLe : ∀ j : Fin (m + 1), idx j ≤ tau := by
    intro j
    rw [← hidxLast]
    exact hidx.monotone (Fin.le_last j)
  let J : Finset (Fin (m + 1)) :=
    (Finset.univ : Finset (Fin (m + 1))).filter fun j ↦
      ¬ P.geometricBad (idx j) omega ∧
        ¬ AugmentationFull.collisionBad P E (idx j) omega
  have hJcard : (m + 1) - (badGeom + badCollision) ≤ J.card := by
    exact sub_add_le_card_filter_two_good omega tau (m + 1)
      badGeom badCollision idx hidx.injective hidxLe P.geometricBad
      (AugmentationFull.collisionBad P E) hgeomNat hcollisionNat
  have hgoodCard : P.candidates.card - badDegree ≤
      (AugmentationFull.goodCandidates P omega).card := by
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := P.candidates) (p := fun x ↦ P.degreeBad x omega)
    change
      (P.candidates.filter fun x ↦ P.degreeBad x omega).card +
        (AugmentationFull.goodCandidates P omega).card =
          P.candidates.card at hpartition
    change (P.candidates.filter fun x ↦ P.degreeBad x omega).card ≤
      badDegree at hdegreeNat
    omega
  have hgoodPos : 0 < (AugmentationFull.goodCandidates P omega).card := by
    have : 0 < P.candidates.card - badDegree := by omega
    omega
  have hgoodIndex : ∀ j ∈ J, ¬ P.geometricBad (idx j) omega := by
    intro j hj
    exact (Finset.mem_filter.mp hj).2.1
  have hcollisionIndex : ∀ j ∈ J,
      ¬ AugmentationFull.collisionBad P E (idx j) omega := by
    intro j hj
    exact (Finset.mem_filter.mp hj).2.2
  have hedges : ∀ j ∈ J,
      (AugmentationFull.valueCollisionGraph
        (AugmentationFull.goodCandidates P omega)
        (fun x ↦ P.value (idx j) x omega)).edgeFinset.card ≤ edgeBudget := by
    intro j hj
    exact AugmentationFull.valueCollisionGraph_card_le_of_not_collisionBad
      P omega E (hcollisionIndex j hj) (hcompare (idx j) (hidxLe j)) hE
  obtain ⟨Y, hYsub, hYinj, hYTuran, hYwindow, hYsep⟩ :=
    AugmentationFull.exists_injective_separated_windows
      P omega idx J hsigma hR hidx hidxLast hstep hgoodIndex hwindow hedges
  have hYpiece : ∀ j ∈ J, piece ≤ (Y j).card := by
    intro j hj
    let C := (AugmentationFull.goodCandidates P omega).card
    let den := C + 2 * edgeBudget
    have hC : P.candidates.card - badDegree ≤ C := hgoodCard
    have hden : den ≤ P.candidates.card + 2 * edgeBudget := by
      dsimp only [den, C]
      exact Nat.add_le_add_right
        (Finset.card_le_card (Finset.filter_subset _ _)) _
    have hpieceC : piece * den ≤ C ^ 2 := by
      calc
        piece * den ≤ piece * (P.candidates.card + 2 * edgeBudget) :=
          Nat.mul_le_mul_left piece hden
        _ ≤ (P.candidates.card - badDegree) ^ 2 := hpiece
        _ ≤ C ^ 2 := Nat.pow_le_pow_left hC 2
    have htur : C ^ 2 ≤ (Y j).card * den := hYTuran j hj
    have hdenPos : 0 < den := by
      dsimp only [den, C]
      omega
    by_contra hnot
    have hlt : (Y j).card * den < piece * den :=
      Nat.mul_lt_mul_of_pos_right (Nat.lt_of_not_ge hnot) hdenPos
    omega
  have hsumLower : L ≤ ∑ j ∈ J, (Y j).card := by
    calc
      L ≤ ((m + 1) - (badGeom + badCollision)) * piece := hL
      _ ≤ J.card * piece := Nat.mul_le_mul_right piece hJcard
      _ = ∑ _j ∈ J, piece := by simp
      _ ≤ ∑ j ∈ J, (Y j).card := Finset.sum_le_sum hYpiece
  let S : Finset ℕ := switchingPiece G W U₀ Dset
    (fun j ↦ state (idx j)) Y J
  have hspec := switchingPiece_spec G W U₀ Dset M nS
    (fun j ↦ state (idx j)) Y J (fun j ↦ P.path omega (idx j))
      R globalCenter globalRadius
      (by
        intro j hj
        exact hstate (idx j) (hidxLe j))
      (by
        intro j hj
        exact hstateCard (idx j) (hidxLe j))
      (by
        intro j hj x hx
        exact hcandidates (Finset.mem_filter.mp (hYsub j hj hx)).1)
      (by
        intro j hj x hx
        exact haway (idx j) (hidxLe j) x
          (Finset.mem_filter.mp (hYsub j hj hx)).1)
      (by
        intro j hj x hx y hy hxy
        apply hYinj j hj hx hy
        calc
          P.value (idx j) x omega =
              (Erdos88.inducedEdges G
                (exposedBase W U₀ Dset state (idx j) ∪ x) : ℤ) :=
            hvalue (idx j) (hidxLe j) x
              (Finset.mem_filter.mp (hYsub j hj hx)).1
          _ = (Erdos88.inducedEdges G
                (exposedBase W U₀ Dset state (idx j) ∪ y) : ℤ) := by
            exact_mod_cast hxy
          _ = P.value (idx j) y omega :=
            (hvalue (idx j) (hidxLe j) y
              (Finset.mem_filter.mp (hYsub j hj hy)).1).symm)
      (by
        intro j hj e he
        obtain ⟨x, hx, rfl⟩ := Augmentation.mem_edgeValues.mp he
        have hw := hYwindow j hj x hx
        rw [hvalue (idx j) (hidxLe j) x
          (Finset.mem_filter.mp (hYsub j hj hx)).1] at hw
        norm_cast at hw ⊢)
      hYsep
      (by
        intro j hj
        exact hglobal (idx j) (hidxLe j) (hgoodIndex j hj))
  refine ⟨S, ?_, ?_, ?_⟩
  · exact hspec.1
  · rw [hspec.2.1]
    exact_mod_cast hsumLower
  · exact hspec.2.2

/-- Concrete graph specialization of the deterministic full-exposure
endpoint.  The abstract exposure data, exact value identity, and collision
comparison are constructed internally; the remaining premises are literal
finite graph conditions and numerical budgets. -/
theorem canonicalFullExposureEvent_implies_innerWindowGood
    [LinearOrder (Finset V)]
    (G : SimpleGraph V) (W U₀ D₁ : Finset V)
    (M source candidates : Finset (Finset V))
    (nD nS tau m : ℕ) (state : ℕ → Finset (Finset V))
    (pathShift geometricThreshold degreeThreshold lam E rho kappa sigma R
      globalRadius : ℝ)
    (globalCenter : Finset V → ℝ)
    (badGeom badCollision badDegree edgeBudget piece L : ℕ)
    (hD₁U₀ : D₁ ⊆ U₀) (hWU₀ : Disjoint W U₀)
    (hsourceM : source ⊆ M) (hcandidatesM : candidates ⊆ M)
    (hpair : (M : Set (Finset V)).PairwiseDisjoint id)
    (hawayM : ∀ x ∈ M, Disjoint x (W ∪ U₀))
    (hstateSource : ∀ i ≤ tau, state i ⊆ source)
    (hstateCard : ∀ i ≤ tau, (state i).card = nS)
    (hstateAway : ∀ i ≤ tau, ∀ x ∈ candidates, x ∉ state i)
    (hliteralWindow : ∀ omega : AugmentationFull.Sample D₁ nD,
      ∀ i ≤ tau, ∀ x ∈ candidates,
      ¬ degreeDeviationBad G D₁ nD degreeThreshold x omega →
        |(Erdos88.inducedEdges G
            (exposedBase W U₀
              (AugmentationGraphFullIdentity.halfDeletion D₁ nD omega)
              state i ∪ x) : ℝ) -
          translatedLiteralGraphPath G W U₀
            (AugmentationGraphFullIdentity.halfDeletion D₁ nD omega)
            state pathShift i| ≤ R)
    (hglobal : ∀ omega : AugmentationFull.Sample D₁ nD,
      ∀ i ≤ tau,
      ¬ degreeDeviationBad G D₁ nD geometricThreshold
          (cellUnion (state i)) omega →
      |translatedLiteralGraphPath G W U₀
          (AugmentationGraphFullIdentity.halfDeletion D₁ nD omega) state
            pathShift i -
        globalCenter
          (AugmentationGraphFullIdentity.halfDeletion D₁ nD omega)| + R ≤
        globalRadius)
    (hm : 1 ≤ m) (hrho : 0 < rho) (hsigma : 0 < sigma)
    (hR : 2 * R < sigma)
    (hbudget : (m : ℝ) * (rho + sigma) + kappa ≤ lam)
    (hE : E ≤ edgeBudget + 1)
    (hcandidateSurvivors : badDegree < candidates.card)
    (hpiece : piece * (candidates.card + 2 * edgeBudget) ≤
      (candidates.card - badDegree) ^ 2)
    (hL : L ≤ ((m + 1) - (badGeom + badCollision)) * piece)
    (omega : AugmentationFull.Sample D₁ nD)
    (hfull : AugmentationFull.FullExposureEvent
      (canonicalGraphExposureData G W U₀ D₁ nD tau state candidates
        pathShift geometricThreshold degreeThreshold hD₁U₀ hWU₀
        (cellUnion_disjoint_right_of_away
          ((hstateSource 0 (by omega)).trans hsourceM)
          (fun x hx ↦ (hawayM x hx).mono_right Finset.subset_union_left) |>.symm)
        (cellUnion_disjoint_right_of_away
          ((hstateSource tau le_rfl).trans hsourceM)
          (fun x hx ↦ (hawayM x hx).mono_right Finset.subset_union_left) |>.symm)
        (cellUnion_disjoint_right_of_away
          ((hstateSource 0 (by omega)).trans hsourceM)
          (fun x hx ↦ (hawayM x hx).mono_right Finset.subset_union_right) |>.symm)
        (cellUnion_disjoint_right_of_away
          ((hstateSource tau le_rfl).trans hsourceM)
          (fun x hx ↦ (hawayM x hx).mono_right Finset.subset_union_right) |>.symm))
      lam E rho kappa (badGeom + 1) (badCollision + 1) (badDegree + 1)
      omega) :
    innerWindowGood G W U₀ M (nS + 1) L
      (globalCenter
        (AugmentationGraphFullIdentity.halfDeletion D₁ nD omega))
      globalRadius
      (AugmentationGraphFullIdentity.halfDeletion D₁ nD omega) := by
  classical
  let hWzero : Disjoint W (cellUnion (state 0)) :=
    (cellUnion_disjoint_right_of_away
      ((hstateSource 0 (by omega)).trans hsourceM)
      (fun x hx ↦ (hawayM x hx).mono_right Finset.subset_union_left)).symm
  let hWlast : Disjoint W (cellUnion (state tau)) :=
    (cellUnion_disjoint_right_of_away
      ((hstateSource tau le_rfl).trans hsourceM)
      (fun x hx ↦ (hawayM x hx).mono_right Finset.subset_union_left)).symm
  let hUzero : Disjoint U₀ (cellUnion (state 0)) :=
    (cellUnion_disjoint_right_of_away
      ((hstateSource 0 (by omega)).trans hsourceM)
      (fun x hx ↦ (hawayM x hx).mono_right Finset.subset_union_right)).symm
  let hUlast : Disjoint U₀ (cellUnion (state tau)) :=
    (cellUnion_disjoint_right_of_away
      ((hstateSource tau le_rfl).trans hsourceM)
      (fun x hx ↦ (hawayM x hx).mono_right Finset.subset_union_right)).symm
  let P := canonicalGraphExposureData G W U₀ D₁ nD tau state candidates
    pathShift geometricThreshold degreeThreshold hD₁U₀ hWU₀ hWzero hWlast
      hUzero hUlast
  apply fullExposureEvent_implies_innerWindowGood G W U₀
    (AugmentationGraphFullIdentity.halfDeletion D₁ nD omega) M nD nS tau m
    P omega state lam E rho kappa sigma R
    (globalCenter
      (AugmentationGraphFullIdentity.halfDeletion D₁ nD omega))
    globalRadius badGeom badCollision badDegree edgeBudget piece L
    hm hrho hsigma hR hbudget
  · simpa only [P, hWzero, hWlast, hUzero, hUlast] using hfull
  · simpa [P, canonicalGraphExposureData,
      canonicalPartialExposureData] using hcandidatesM
  · intro i hi
    exact (hstateSource i hi).trans hsourceM
  · exact hstateCard
  · intro i hi x hx
    exact hstateAway i hi x hx
  · intro i hi x hx
    rfl
  · intro i hi x hx _hgeom hdegree
    change |(Erdos88.inducedEdges G
        (exposedBase W U₀ (sampleFinset D₁ nD omega) state i ∪ x) : ℝ) -
      translatedLiteralGraphPath G W U₀
        (AugmentationGraphFullIdentity.halfDeletion D₁ nD omega) state
          pathShift i| ≤ R
    rw [show sampleFinset D₁ nD omega =
      AugmentationGraphFullIdentity.halfDeletion D₁ nD omega from rfl]
    exact hliteralWindow omega i hi x hx hdegree
  · intro i hi hgeom
    change ¬ degreeDeviationBad G D₁ nD geometricThreshold
      (cellUnion (state i)) omega at hgeom
    change |translatedLiteralGraphPath G W U₀
        (AugmentationGraphFullIdentity.halfDeletion D₁ nD omega) state
          pathShift i -
        globalCenter
          (AugmentationGraphFullIdentity.halfDeletion D₁ nD omega)| + R ≤
      globalRadius
    exact hglobal omega i hi hgeom
  · intro i hi
    let : Nonempty (AugmentationFull.Sample D₁ nD) := ⟨omega⟩
    let C := AugmentationFull.goodCandidates P omega
    let f : Finset V → ℤ := fun x ↦ P.value i x omega
    have hbridge :=
      AugmentationGraphFullState.valueCollisionGraph_edgeFinset_card_le_collisionEdges
        C f
    have heq : CollisionCounting.collisionEdges C (fun x (_ : Unit) ↦ f x) () =
        CollisionCounting.collisionEdges C (P.value i) omega := by
      rfl
    rw [heq] at hbridge
    have hmono : CollisionCounting.collisionEdges C (P.value i) omega ⊆
        CollisionCounting.collisionEdges P.candidates (P.value i) omega :=
      AugmentationGraphFullState.collisionEdges_mono
        (Finset.filter_subset _ _) (P.value i) omega
    exact hbridge.trans (Finset.card_le_card hmono)
  · exact hE
  · exact hcandidateSurvivors
  · exact hpiece
  · exact hL

/-- Exact transport of any deletion-set event from the Fourier half-slice to
the uniform finset layer. -/
theorem uniformProbability_sampleFinset_eq_layerProbability
    (D₁ : Finset V) (nD : ℕ)
    (hhalf : 2 * nD = D₁.card)
    (event : Finset V → Prop) [DecidablePred event] :
    uniformProbability
        (fun omega : AugmentationFull.Sample D₁ nD ↦
          event (sampleFinset D₁ nD omega)) =
      NestedUniform.layerProbability D₁ nD event := by
  let : Nonempty (AugmentationFull.Sample D₁ nD) :=
    HalfSample.sliceNonempty (by simpa using hhalf.symm)
  let : Nonempty
      (Erdos88.BooleanSlices.BooleanSlicePoint D₁ nD) :=
    SliceMoments.nonempty_booleanSlicePoint D₁ nD (by omega)
  let E : AugmentationFull.Sample D₁ nD ≃
      Erdos88.Fourier.BoolSlice D₁ nD :=
    (Erdos88.Fourier.boolSliceEquivFinsetLen D₁ nD).symm
  let : Nonempty (Erdos88.Fourier.BoolSlice D₁ nD) :=
    (Equiv.nonempty_congr E).mp inferInstance
  have hsample := Augmentation.finProbability_equiv E
    (fun omega ↦ event (Augmentation.boolSliceDeletion D₁ nD omega))
  have hdecode : ∀ omega : AugmentationFull.Sample D₁ nD,
      Augmentation.boolSliceDeletion D₁ nD (E omega) =
        sampleFinset D₁ nD omega := by
    intro omega
    change Augmentation.mapSubtypeFinset D₁
        ((Erdos88.Fourier.boolSliceEquivFinsetLen D₁ nD (E omega)).1) =
      Augmentation.mapSubtypeFinset D₁ omega.1
    have hround : Erdos88.Fourier.boolSliceEquivFinsetLen D₁ nD (E omega) =
        omega := Equiv.apply_symm_apply
          (Erdos88.Fourier.boolSliceEquivFinsetLen D₁ nD) omega
    rw [hround]
  have hevent :
      (fun omega : AugmentationFull.Sample D₁ nD ↦
          event (sampleFinset D₁ nD omega)) =
        (fun omega ↦ event
          (Augmentation.boolSliceDeletion D₁ nD (E omega))) := by
    funext omega
    rw [hdecode]
  calc
    uniformProbability
        (fun omega : AugmentationFull.Sample D₁ nD ↦
          event (sampleFinset D₁ nD omega)) =
        Erdos88.Fourier.finProbability (Erdos88.Fourier.BoolSlice D₁ nD)
        (fun omega ↦ event (Augmentation.boolSliceDeletion D₁ nD omega)) := by
      rw [hevent]
      simpa only [uniformProbability, Erdos88.Fourier.finProbability] using hsample
    _ = NestedUniform.layerProbability D₁ nD event :=
      Augmentation.finProbability_boolSliceDeletion_eq_layerProbability
        D₁ nD event

/-! ## The closed graph-valued conditional probability theorem -/

/-- Uniform second-moment budget for every literal one-cell switch. -/
def graphSwitchVariance (K : ℕ) (meanRadius : ℝ) (nD : ℕ) : ℝ :=
  ((K : ℝ) ^ 2 + meanRadius ^ 2) * nD

/-- Point-collision risk supplied by diversity on the outer reservoir. -/
def graphCollisionRisk (c theta : ℝ) (K : ℕ) (D₁ : Finset V) : ℝ :=
  AntiConcentration.variancePointMassConstant c (theta ^ 2 / 4) K /
    Real.sqrt (D₁.card : ℝ)

/-- Deletion-degree tail risk for one candidate cell. -/
def graphDegreeRisk (degreeThreshold : ℝ) (nD K : ℕ) : ℝ :=
  2 * Real.exp
    (-degreeThreshold ^ 2 / (2 * nD * (4 * K) ^ 2))

/-- **Concrete graph full-exposure theorem (Kwan--Sudakov Claim 4.9).**

This is the graph-facing finite theorem: it has no abstract exposure datum,
event implication, endpoint-probability premise, failure-probability premise,
or second-moment premise.  The state path is oriented high-to-low: at step
`i`, `stepHigh i` is removed and `stepLow i` is inserted.  The exact literal
edge-count identities then give both the endpoint symmetry and the sharp
half-slice second moment.  Candidate collisions and deletion degrees are
bounded directly from diversity and cell size.

The conclusion retains an actual piece of canonical augmentation values in a
common window around the caller-supplied deletion-only centre.  In particular,
that centre is independent of the intermediate reservoir `D₁` and of the
switching state selected from it. -/
theorem one_third_le_layerProbability_innerWindowGood_of_graphData
    [LinearOrder (Finset V)]
    (G : SimpleGraph V) (W U₀ D₁ : Finset V)
    (M candidates : Finset (Finset V))
    (nD nS tau m K : ℕ) (state : ℕ → Finset (Finset V))
    (canonicalCenter : Finset V → ℝ)
    (stepRest stepLow stepHigh : ℕ → Finset V)
    (degreeCenter degreeRadius c theta pathShift geometricThreshold
      degreeThreshold meanRadius
      lam E Q kappa sigma R globalRadius : ℝ)
    (badGeom badCollision badDegree edgeBudget piece L : ℕ)
    (hhalf : D₁.card = 2 * nD) (hnD : 0 < nD) (hnS : 0 < nS)
    (hK : 1 ≤ K)
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) (htheta : 0 < theta)
    (hsel : c * D₁.card ≤ nD)
    (hunsel : c * D₁.card ≤ D₁.card - nD)
    (hgeometricThreshold : 0 ≤ geometricThreshold)
    (hdegreeThreshold : 0 ≤ degreeThreshold)
    (hmeanRadius : 0 ≤ meanRadius)
    (hQ : 0 < Q) (hkappa : 0 < kappa) (hEpos : 0 < E)
    (hD₁U₀ : D₁ ⊆ U₀) (hWU₀ : Disjoint W U₀)
    (hcandidatesM : candidates ⊆ M)
    (hpair : (M : Set (Finset V)).PairwiseDisjoint id)
    (hawayM : ∀ x ∈ M, Disjoint x (W ∪ U₀))
    (hcellK : ∀ x ∈ M, x.card ≤ K)
    (hstateM : ∀ i ≤ tau, state i ⊆ M)
    (hstateCard : ∀ i ≤ tau, (state i).card = nS)
    (hstateAway : ∀ i ≤ tau, ∀ x ∈ candidates, x ∉ state i)
    (hcandidateGood : ∀ x ∈ candidates,
      AugmentationGraphPartial.DegreeGood G D₁ x degreeCenter degreeRadius)
    (hcandidateDiverse : ∀ x ∈ candidates, ∀ y ∈ candidates, x ≠ y →
      theta * D₁.card ≤ incidenceDiffMass G D₁ x y)
    (hsmallWindow : 2 * degreeRadius < theta / 2 * D₁.card)
    (hstepNext : ∀ i < tau,
      cellUnion (state (i + 1)) = stepRest i ∪ stepLow i)
    (hstepCurrent : ∀ i < tau,
      cellUnion (state i) = stepRest i ∪ stepHigh i)
    (hstepWR : ∀ i < tau, Disjoint W (stepRest i))
    (hstepWLow : ∀ i < tau, Disjoint W (stepLow i))
    (hstepWHigh : ∀ i < tau, Disjoint W (stepHigh i))
    (hstepUR : ∀ i < tau, Disjoint U₀ (stepRest i))
    (hstepULow : ∀ i < tau, Disjoint U₀ (stepLow i))
    (hstepUHigh : ∀ i < tau, Disjoint U₀ (stepHigh i))
    (hstepRLow : ∀ i < tau, Disjoint (stepRest i) (stepLow i))
    (hstepRHigh : ∀ i < tau, Disjoint (stepRest i) (stepHigh i))
    (hstepLowK : ∀ i < tau, (stepLow i).card ≤ K)
    (hstepHighK : ∀ i < tau, (stepHigh i).card ≤ K)
    (hstepMean : ∀ i < tau,
      |(AugmentationGraphFullIdentity.switchOffsetInt G W U₀
          (stepRest i) (stepLow i) (stepHigh i) : ℝ) +
        ((degreeInto G D₁ (stepHigh i) : ℝ) -
          degreeInto G D₁ (stepLow i)) / 2| ≤
        meanRadius * Real.sqrt nD)
    (hmeanRise : lam ≤
      (AugmentationGraphFullIdentity.endpointOffsetInt G W U₀
        (cellUnion (state 0)) (cellUnion (state tau)) : ℝ) +
      ((degreeInto G D₁ (cellUnion (state 0)) : ℝ) -
        degreeInto G D₁ (cellUnion (state tau))) / 2)
    (hliteralWindow : ∀ omega : AugmentationFull.Sample D₁ nD,
      ∀ i ≤ tau, ∀ x ∈ candidates,
      ¬ degreeDeviationBad G D₁ nD degreeThreshold x omega →
        |(Erdos88.inducedEdges G
            (exposedBase W U₀
              (AugmentationGraphFullIdentity.halfDeletion D₁ nD omega)
              state i ∪ x) : ℝ) -
          translatedLiteralGraphPath G W U₀
            (AugmentationGraphFullIdentity.halfDeletion D₁ nD omega)
            state pathShift i| ≤ R)
    (hglobal : ∀ omega : AugmentationFull.Sample D₁ nD,
      ∀ i ≤ tau,
      ¬ degreeDeviationBad G D₁ nD geometricThreshold
          (cellUnion (state i)) omega →
      |translatedLiteralGraphPath G W U₀
          (AugmentationGraphFullIdentity.halfDeletion D₁ nD omega) state
            pathShift i -
        canonicalCenter
          (AugmentationGraphFullIdentity.halfDeletion D₁ nD omega)| + R ≤
        globalRadius)
    (hm : 1 ≤ m) (hsigma : 0 < sigma) (hR : 2 * R < sigma)
    (hbudget : (m : ℝ) *
        (Q * Real.sqrt (graphSwitchVariance K meanRadius nD) + sigma) +
          kappa ≤ lam)
    (hE : E ≤ edgeBudget + 1)
    (hcandidateSurvivors : badDegree < candidates.card)
    (hpiece : piece * (candidates.card + 2 * edgeBudget) ≤
      (candidates.card - badDegree) ^ 2)
    (hL : L ≤ ((m + 1) - (badGeom + badCollision)) * piece)
    (hrisk :
      (tau + 1 : ℕ) *
          graphDegreeRisk geometricThreshold nD (K * nS) /
            (badGeom + 1 : ℕ) +
        (tau + 1 : ℕ) *
            (candidates.card.choose 2 * graphCollisionRisk c theta K D₁ / E) /
              (badCollision + 1 : ℕ) +
        candidates.card * graphDegreeRisk degreeThreshold nD K /
            (badDegree + 1 : ℕ) +
        (tau * (Real.sqrt (graphSwitchVariance K meanRadius nD) / Q)) /
            kappa ≤ 1 / 6) :
    (1 : ℝ) / 3 ≤ NestedUniform.layerProbability D₁ nD
      (fun D ↦ innerWindowGood G W U₀ M (nS + 1) L
        (canonicalCenter D) globalRadius D) := by
  classical
  let hWzero : Disjoint W (cellUnion (state 0)) :=
    (cellUnion_disjoint_right_of_away
      (hstateM 0 (by omega))
      (fun x hx ↦ (hawayM x hx).mono_right Finset.subset_union_left)).symm
  let hWlast : Disjoint W (cellUnion (state tau)) :=
    (cellUnion_disjoint_right_of_away
      (hstateM tau le_rfl)
      (fun x hx ↦ (hawayM x hx).mono_right Finset.subset_union_left)).symm
  let hUzero : Disjoint U₀ (cellUnion (state 0)) :=
    (cellUnion_disjoint_right_of_away
      (hstateM 0 (by omega))
      (fun x hx ↦ (hawayM x hx).mono_right Finset.subset_union_right)).symm
  let hUlast : Disjoint U₀ (cellUnion (state tau)) :=
    (cellUnion_disjoint_right_of_away
      (hstateM tau le_rfl)
      (fun x hx ↦ (hawayM x hx).mono_right Finset.subset_union_right)).symm
  let P := canonicalGraphExposureData G W U₀ D₁ nD tau state candidates
    pathShift geometricThreshold degreeThreshold hD₁U₀ hWU₀ hWzero hWlast
      hUzero hUlast
  let : Nonempty (AugmentationFull.Sample D₁ nD) :=
    HalfSample.sliceNonempty (by simpa using hhalf)
  let variance := graphSwitchVariance K meanRadius nD
  let collisionRisk := graphCollisionRisk c theta K D₁
  let degreeRisk := graphDegreeRisk degreeThreshold nD K
  let geometricRisk := graphDegreeRisk geometricThreshold nD (K * nS)
  have hv : 0 < variance := by
    dsimp only [variance, graphSwitchVariance]
    positivity
  have hgeom : ∀ i < tau + 1,
      uniformProbability (P.geometricBad i) ≤ geometricRisk := by
    intro i hi
    have hi' : i ≤ tau := by omega
    have hcard : (cellUnion (state i)).card ≤ K * nS := by
      calc
        (cellUnion (state i)).card ≤ (state i).card * K := by
          exact Finset.card_biUnion_le_card_mul (state i) id K
            (fun x hx ↦ hcellK x (hstateM i hi' hx))
        _ = K * nS := by rw [hstateCard i hi']; simp [Nat.mul_comm]
    change uniformProbability
        (degreeDeviationBad G D₁ nD geometricThreshold
          (cellUnion (state i))) ≤ geometricRisk
    exact uniformProbability_degreeDeviationBad_le G D₁
      (cellUnion (state i)) nD (K * nS) geometricThreshold hhalf hnD
      (by positivity) hgeometricThreshold hcard
  have hcollision : ∀ i < tau + 1,
      ∀ x ∈ P.candidates, ∀ y ∈ P.candidates, x ≠ y →
        uniformProbability (fun omega ↦ P.value i x omega = P.value i y omega) ≤
          collisionRisk := by
    intro i hi x hx y hy hxy
    have hi' : i ≤ tau := by omega
    have hxC : x ∈ candidates := by simpa [P, canonicalGraphExposureData,
      canonicalPartialExposureData] using hx
    have hyC : y ∈ candidates := by simpa [P, canonicalGraphExposureData,
      canonicalPartialExposureData] using hy
    have hxM := hcandidatesM hxC
    have hyM := hcandidatesM hyC
    have hWZ : Disjoint W (cellUnion (state i)) :=
      (cellUnion_disjoint_right_of_away
        (hstateM i hi')
        (fun z hz ↦ (hawayM z hz).mono_right Finset.subset_union_left)).symm
    have hUZ : Disjoint U₀ (cellUnion (state i)) :=
      (cellUnion_disjoint_right_of_away
        (hstateM i hi')
        (fun z hz ↦ (hawayM z hz).mono_right Finset.subset_union_right)).symm
    have hWx : Disjoint W x :=
      ((hawayM x hxM).mono_right Finset.subset_union_left).symm
    have hUx : Disjoint U₀ x :=
      ((hawayM x hxM).mono_right Finset.subset_union_right).symm
    have hWy : Disjoint W y :=
      ((hawayM y hyM).mono_right Finset.subset_union_left).symm
    have hUy : Disjoint U₀ y :=
      ((hawayM y hyM).mono_right Finset.subset_union_right).symm
    have hZx : Disjoint (cellUnion (state i)) x :=
      cellUnion_disjoint_cell_of_pairwise hpair (hstateM i hi') hxM
        (hstateAway i hi' x hxC)
    have hZy : Disjoint (cellUnion (state i)) y :=
      cellUnion_disjoint_cell_of_pairwise hpair (hstateM i hi') hyM
        (hstateAway i hi' y hyC)
    have hc := uniformProbability_literalCandidateCollision_le G W U₀ D₁
      (cellUnion (state i)) x y nD K degreeCenter degreeRadius c theta hhalf
      hnD hK hc0 hc1 htheta hsel hunsel (hcellK x hxM) (hcellK y hyM)
      (hcandidateGood x hxC) (hcandidateGood y hyC)
      (hcandidateDiverse x hxC y hyC hxy) hsmallWindow hD₁U₀ hWU₀
      hWZ hUZ hWx hUx hZx hWy hUy hZy
    have hevent : (fun omega : AugmentationFull.Sample D₁ nD ↦
        P.value i x omega = P.value i y omega) =
      (fun omega ↦
        Erdos88.inducedEdges G
            (AugmentationGraphFullIdentity.literalState W U₀
              (AugmentationGraphFullIdentity.halfDeletion D₁ nD omega)
              (cellUnion (state i)) ∪ x) =
          Erdos88.inducedEdges G
            (AugmentationGraphFullIdentity.literalState W U₀
              (AugmentationGraphFullIdentity.halfDeletion D₁ nD omega)
              (cellUnion (state i)) ∪ y)) := by
      funext omega
      apply propext
      have hdecode : sampleFinset D₁ nD omega =
          AugmentationGraphFullIdentity.halfDeletion D₁ nD omega := rfl
      change (exposedValue G W U₀ (sampleFinset D₁ nD omega) state i x : ℤ) =
          exposedValue G W U₀ (sampleFinset D₁ nD omega) state i y ↔ _
      rw [hdecode]
      change (Erdos88.inducedEdges G
          (AugmentationGraphFullIdentity.literalState W U₀
            (AugmentationGraphFullIdentity.halfDeletion D₁ nD omega)
            (cellUnion (state i)) ∪ x) : ℤ) =
        Erdos88.inducedEdges G
          (AugmentationGraphFullIdentity.literalState W U₀
            (AugmentationGraphFullIdentity.halfDeletion D₁ nD omega)
            (cellUnion (state i)) ∪ y) ↔ _
      norm_cast
    rw [hevent]
    exact hc
  have hdegree : ∀ x ∈ P.candidates,
      uniformProbability (P.degreeBad x) ≤ degreeRisk := by
    intro x hx
    have hxC : x ∈ candidates := by simpa [P, canonicalGraphExposureData,
      canonicalPartialExposureData] using hx
    change uniformProbability (degreeDeviationBad G D₁ nD degreeThreshold x) ≤
      degreeRisk
    exact uniformProbability_degreeDeviationBad_le G D₁ x nD K
      degreeThreshold hhalf hnD (by omega) hdegreeThreshold
      (hcellK x (hcandidatesM hxC))
  have hsecond : ∀ i < tau,
      uniformExpectation (fun omega : AugmentationFull.Sample D₁ nD ↦
        (AugmentationFull.increment P omega i) ^ 2) ≤ variance := by
    intro i hi
    change uniformExpectation
      (fun omega : AugmentationFull.Sample D₁ nD ↦
        (translatedLiteralGraphPath G W U₀
            (AugmentationGraphFullIdentity.halfDeletion D₁ nD omega)
            state pathShift (i + 1) -
          translatedLiteralGraphPath G W U₀
            (AugmentationGraphFullIdentity.halfDeletion D₁ nD omega)
            state pathShift i) ^ 2) ≤ variance
    simp only [translatedLiteralGraphPath, add_sub_add_right_eq_sub]
    simp only [literalGraphPath]
    rw [show cellUnion (state (i + 1)) = stepRest i ∪ stepLow i from hstepNext i hi,
      show cellUnion (state i) = stepRest i ∪ stepHigh i from hstepCurrent i hi]
    exact AugmentationGraphFullIdentity.uniformExpectation_literalSwitch_sq_le
      G W U₀ D₁ (stepRest i) (stepLow i) (stepHigh i) nD K meanRadius
      hhalf hnD hD₁U₀ hWU₀ (hstepWR i hi) (hstepWLow i hi)
      (hstepWHigh i hi) (hstepUR i hi) (hstepULow i hi)
      (hstepUHigh i hi) (hstepRLow i hi) (hstepRHigh i hi)
      (hstepLowK i hi) (hstepHighK i hi) hmeanRadius (hstepMean i hi)
  have hmeanRiseP : lam ≤ P.endpointOffset +
      (∑ d, P.endpointCoeff d) / 2 := by
    change lam ≤
      (AugmentationGraphFullIdentity.endpointOffsetInt G W U₀
        (cellUnion (state 0)) (cellUnion (state tau)) : ℝ) +
      (∑ d : D₁, AugmentationGraphFullIdentity.replacementCoeff G D₁
        (cellUnion (state tau)) (cellUnion (state 0)) d) / 2
    rw [AugmentationGraphFullIdentity.sum_replacementCoeff_eq_degreeInto_sub]
    exact hmeanRise
  have hfull :=
    AugmentationGraphFullProbability.one_third_le_uniformProbability_fullExposureEvent_of_itemBounds
      (by simpa using hhalf) P lam E variance Q kappa
        (badGeom + 1) (badCollision + 1) (badDegree + 1)
        hv hQ hkappa hEpos (by positivity) (by positivity) (by positivity)
        hmeanRiseP geometricRisk collisionRisk degreeRisk hgeom hcollision
          hdegree hsecond
        (by
          have hPcandidates : P.candidates = candidates := rfl
          simpa only [hPcandidates, variance, geometricRisk, collisionRisk,
            degreeRisk, Nat.cast_add, Nat.cast_one] using hrisk)
  have hmono : uniformProbability
      (AugmentationFull.FullExposureEvent P lam E
        (Q * Real.sqrt variance) kappa (badGeom + 1) (badCollision + 1)
          (badDegree + 1)) ≤
      uniformProbability (fun omega : AugmentationFull.Sample D₁ nD ↦
        innerWindowGood G W U₀ M (nS + 1) L
          (canonicalCenter
            (AugmentationGraphFullIdentity.halfDeletion D₁ nD omega))
          globalRadius
          (AugmentationGraphFullIdentity.halfDeletion D₁ nD omega)) := by
    apply uniformProbability_mono
    intro omega hfullOmega
    exact canonicalFullExposureEvent_implies_innerWindowGood G W U₀ D₁ M M
      candidates nD nS tau m state pathShift geometricThreshold degreeThreshold lam E
      (Q * Real.sqrt variance) kappa sigma R globalRadius canonicalCenter
      badGeom badCollision badDegree edgeBudget piece L hD₁U₀ hWU₀
      Finset.Subset.rfl hcandidatesM
      hpair hawayM hstateM hstateCard hstateAway hliteralWindow hglobal hm
      (mul_pos hQ (Real.sqrt_pos.2 hv)) hsigma hR
      (by simpa [variance] using hbudget) hE hcandidateSurvivors hpiece hL omega
      (by simpa [P] using hfullOmega)
  have hsample : (1 : ℝ) / 3 ≤ uniformProbability
      (fun omega : AugmentationFull.Sample D₁ nD ↦
        innerWindowGood G W U₀ M (nS + 1) L
          (canonicalCenter (sampleFinset D₁ nD omega))
          globalRadius (sampleFinset D₁ nD omega)) := by
    have hdecode : ∀ omega : AugmentationFull.Sample D₁ nD,
        sampleFinset D₁ nD omega =
          AugmentationGraphFullIdentity.halfDeletion D₁ nD omega := by
      intro omega
      rfl
    have hevent : (fun omega : AugmentationFull.Sample D₁ nD ↦
        innerWindowGood G W U₀ M (nS + 1) L
          (canonicalCenter
            (AugmentationGraphFullIdentity.halfDeletion D₁ nD omega))
          globalRadius
          (AugmentationGraphFullIdentity.halfDeletion D₁ nD omega)) =
        (fun omega ↦ innerWindowGood G W U₀ M (nS + 1) L
          (canonicalCenter (sampleFinset D₁ nD omega))
          globalRadius (sampleFinset D₁ nD omega)) := by
      funext omega
      rw [hdecode]
    rw [← hevent]
    exact hfull.trans hmono
  rw [uniformProbability_sampleFinset_eq_layerProbability D₁ nD hhalf.symm
    (fun D ↦ innerWindowGood G W U₀ M (nS + 1) L
      (canonicalCenter D) globalRadius D)] at hsample
  exact hsample

/-! ## The quantitative `1/2 - 1/6 = 1/3` full-exposure calculation -/

/-- If the endpoint-rise event has probability at least one half and all
other failures together have probability at most one sixth, the full event
has conditional probability at least one third. -/
theorem one_third_le_uniformProbability_fullExposureEvent
    {D : Type v} [Fintype D]
    {X : Type*} [LinearOrder X] [DecidableEq X]
    {s tau : ℕ} [Nonempty (AugmentationFull.Sample D s)]
    (P : AugmentationFull.PartialExposureData D X s tau)
    (lam E rho kappa tGeom tCollision tDegree : ℝ)
    (hendpoint : (1 : ℝ) / 2 ≤ uniformProbability
      (fun omega : AugmentationFull.Sample D s ↦
        lam ≤ P.path omega tau - P.path omega 0))
    (hfailure : uniformProbability
      (fun omega : AugmentationFull.Sample D s ↦
        tGeom ≤ CollisionCounting.eventCount (Finset.range (tau + 1))
            P.geometricBad omega ∨
        tCollision ≤ CollisionCounting.eventCount (Finset.range (tau + 1))
            (AugmentationFull.collisionBad P E) omega ∨
        tDegree ≤ CollisionCounting.eventCount P.candidates P.degreeBad omega ∨
        kappa ≤ AugmentationFull.tailBudget P rho omega) ≤ 1 / 6) :
    (1 : ℝ) / 3 ≤ uniformProbability
      (AugmentationFull.FullExposureEvent P lam E rho kappa
        tGeom tCollision tDegree) := by
  let failure : AugmentationFull.Sample D s → Prop := fun omega ↦
    tGeom ≤ CollisionCounting.eventCount (Finset.range (tau + 1))
        P.geometricBad omega ∨
    tCollision ≤ CollisionCounting.eventCount (Finset.range (tau + 1))
        (AugmentationFull.collisionBad P E) omega ∨
    tDegree ≤ CollisionCounting.eventCount P.candidates P.degreeBad omega ∨
    kappa ≤ AugmentationFull.tailBudget P rho omega
  have hsub := AugmentationFull.sub_le_uniformProbability_and_not
    (fun omega : AugmentationFull.Sample D s ↦
      lam ≤ P.path omega tau - P.path omega 0)
    failure (1 / 2) (1 / 6) hendpoint (by simpa [failure] using hfailure)
  have hmono : uniformProbability
      (fun omega : AugmentationFull.Sample D s ↦
        lam ≤ P.path omega tau - P.path omega 0 ∧ ¬ failure omega) ≤
      uniformProbability (AugmentationFull.FullExposureEvent P lam E rho
        kappa tGeom tCollision tDegree) := by
    apply uniformProbability_mono
    intro omega homega
    rcases homega with ⟨hrise, hnot⟩
    simp only [failure, not_or, not_le] at hnot
    exact ⟨hrise, hnot.1, hnot.2.1, hnot.2.2.1, hnot.2.2.2⟩
  norm_num at hsub ⊢
  exact hsub.trans hmono

/-- Graph-valued form of the preceding theorem.  A pointwise deterministic
proof that the full-exposure event creates `L` distinct canonical
augmentation values transports the `1/3` probability bound to the actual
uniform layer of deletion sets. -/
theorem one_third_le_layerProbability_innerGood_of_fullExposure
    [LinearOrder (Finset V)]
    (G : SimpleGraph V) (W U₀ D₁ : Finset V)
    (M : Finset (Finset V)) (nD nZ tau : ℕ) (L : ℝ)
    (hhalf : D₁.card = 2 * nD)
    (P : AugmentationFull.PartialExposureData D₁ (Finset V) nD tau)
    (lam E rho kappa tGeom tCollision tDegree : ℝ)
    (hendpoint : (1 : ℝ) / 2 ≤ uniformProbability
      (fun omega : AugmentationFull.Sample D₁ nD ↦
        lam ≤ P.path omega tau - P.path omega 0))
    (hfailure : uniformProbability
      (fun omega : AugmentationFull.Sample D₁ nD ↦
        tGeom ≤ CollisionCounting.eventCount (Finset.range (tau + 1))
            P.geometricBad omega ∨
        tCollision ≤ CollisionCounting.eventCount (Finset.range (tau + 1))
            (AugmentationFull.collisionBad P E) omega ∨
        tDegree ≤ CollisionCounting.eventCount P.candidates P.degreeBad omega ∨
        kappa ≤ AugmentationFull.tailBudget P rho omega) ≤ 1 / 6)
    (hcreates : ∀ omega : AugmentationFull.Sample D₁ nD,
      AugmentationFull.FullExposureEvent P lam E rho kappa
          tGeom tCollision tDegree omega →
        innerGood G W U₀ M nZ L (sampleFinset D₁ nD omega)) :
    (1 : ℝ) / 3 ≤ NestedUniform.layerProbability D₁ nD
      (innerGood G W U₀ M nZ L) := by
  let : Nonempty (AugmentationFull.Sample D₁ nD) :=
    HalfSample.sliceNonempty (by simpa using hhalf)
  have hfull := one_third_le_uniformProbability_fullExposureEvent
    P lam E rho kappa tGeom tCollision tDegree hendpoint hfailure
  have htransport : uniformProbability
      (AugmentationFull.FullExposureEvent P lam E rho kappa
        tGeom tCollision tDegree) ≤
      uniformProbability (fun omega : AugmentationFull.Sample D₁ nD ↦
        innerGood G W U₀ M nZ L (sampleFinset D₁ nD omega)) := by
    exact uniformProbability_mono hcreates
  rw [uniformProbability_sampleFinset_eq_layerProbability
    D₁ nD hhalf.symm (innerGood G W U₀ M nZ L)] at htransport
  exact hfull.trans htransport

/-- Final two-stage probability composition.  This is the exact finite
`(3/4) * (1/3) = 1/4` step: the marginal law of the inner deletion set is
uniform on the `nD`-layer of `U₀`. -/
theorem one_fourth_le_layerProbability_innerGood_of_outer_inner
    (G : SimpleGraph V) (W U₀ : Finset V)
    (M : Finset (Finset V)) (nD nZ : ℕ) (L : ℝ)
    (outerGood : Finset V → Prop) [DecidablePred outerGood]
    (hfeasible : 2 * nD ≤ U₀.card)
    (houter : (3 / 4 : ℝ) ≤
      NestedUniform.layerProbability U₀ (2 * nD) outerGood)
    (hinner : ∀ D₁ ∈ NestedUniform.layer U₀ (2 * nD), outerGood D₁ →
      (1 / 3 : ℝ) ≤ NestedUniform.layerProbability D₁ nD
        (innerGood G W U₀ M nZ L)) :
    (1 / 4 : ℝ) ≤ NestedUniform.layerProbability U₀ nD
      (innerGood G W U₀ M nZ L) := by
  exact Augmentation.one_fourth_le_layerProbability_of_nested
    U₀ nD outerGood (innerGood G W U₀ M nZ L)
      hfeasible houter hinner

/-- Window-preserving version of the exact nested `3/4 * 1/3 = 1/4`
composition.  The centre may depend on the final deletion set; this is the
form used by the shared-deletion/marked-packing layer. -/
theorem one_fourth_le_layerProbability_innerWindowGood_of_outer_inner
    (G : SimpleGraph V) (W U₀ : Finset V)
    (M : Finset (Finset V)) (nD nZ : ℕ) (L radius : ℝ)
    (center : Finset V → ℝ)
    (outerGood : Finset V → Prop) [DecidablePred outerGood]
    (hfeasible : 2 * nD ≤ U₀.card)
    (houter : (3 / 4 : ℝ) ≤
      NestedUniform.layerProbability U₀ (2 * nD) outerGood)
    (hinner : ∀ D₁ ∈ NestedUniform.layer U₀ (2 * nD), outerGood D₁ →
      (1 / 3 : ℝ) ≤ NestedUniform.layerProbability D₁ nD
        (fun D ↦ innerWindowGood G W U₀ M nZ L (center D) radius D)) :
    (1 / 4 : ℝ) ≤ NestedUniform.layerProbability U₀ nD
      (fun D ↦ innerWindowGood G W U₀ M nZ L (center D) radius D) := by
  exact Augmentation.one_fourth_le_layerProbability_of_nested
    U₀ nD outerGood
      (fun D ↦ innerWindowGood G W U₀ M nZ L (center D) radius D)
      hfeasible houter hinner

end

end AugmentationGraphFull
end Erdos636
