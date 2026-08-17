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

import ErdosProblems.Erdos636.AugmentationIdentity
import ErdosProblems.Erdos636.AugmentationGraphPartial
import ErdosProblems.Erdos636.HalfSample
import ErdosProblems.Erdos636.HalfSampleVariance

/-!
# Exact identities for the graph-valued full exposure

This file contains the algebraic part of the balanced full exposure.  A
point of the half-slice of `D₁` is decoded as an ambient deletion set `D`.
The path is the literal induced-edge count of

`(W ∪ (U₀ \ D)) ∪ Z`.

The endpoint, every one-cell switch, and every collision between candidate
extensions are expressed as an affine function of the same half-slice
incidence statistic.  Thus later probability arguments do not need to
assume an abstract endpoint or collision identity.
-/

open Classical SimpleGraph
open scoped BigOperators

namespace Erdos636
namespace AugmentationGraphFullIdentity

universe u

noncomputable section

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Cross-incidences can be counted from either endpoint class. -/
lemma degreeInto_comm (G : SimpleGraph V) (A B : Finset V) :
    degreeInto G A B = degreeInto G B A := by
  classical
  simp only [degreeInto, Erdos88.neighborsIn, Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  simp only [G.adj_comm a b]

/-- The incidence vector of a cell on a reservoir.  This is definitionally
the graph-partial-exposure incidence vector; it is kept here as a local
name so the exact identities remain usable independently of probability
packaging. -/
def reservoirIncidence (G : SimpleGraph V) (D₁ x : Finset V)
    (u : D₁) : ℤ :=
  incidence G x u.1

/-- The identity-layer coefficient is definitionally the coefficient used
by the graph partial exposure. -/
@[simp] lemma reservoirIncidence_eq_partialIncidence
    (G : SimpleGraph V) (D₁ x : Finset V) (u : D₁) :
    reservoirIncidence G D₁ x u =
      AugmentationGraphPartial.incidenceVector G D₁ x u :=
  rfl

/-- Full-reservoir coefficient sum, imported from the graph partial
exposure without any change of convention. -/
lemma sum_reservoirIncidence_eq_degreeInto
    (G : SimpleGraph V) (D₁ x : Finset V) :
    ∑ u : D₁, reservoirIncidence G D₁ x u = degreeInto G D₁ x := by
  simpa using
    AugmentationGraphPartial.sum_incidenceVector_eq_degreeInto G D₁ x

/-- A cell incidence coordinate is bounded by the size of the cell. -/
lemma abs_reservoirIncidence_le_of_card_le
    (G : SimpleGraph V) (D₁ x : Finset V) (K : ℕ)
    (hxK : x.card ≤ K) (u : D₁) :
    |reservoirIncidence G D₁ x u| ≤ (K : ℤ) := by
  change |(incidence G x u.1 : ℤ)| ≤ (K : ℤ)
  rw [abs_of_nonneg (by simp)]
  exact_mod_cast (incidence_le_card G x u.1).trans hxK

/-- Difference coefficients of two `K`-bounded cells are still bounded by
`K`, rather than by the coarser `2K`, because both incidences lie in
`[0,K]`. -/
lemma abs_reservoirIncidence_sub_le_of_card_le
    (G : SimpleGraph V) (D₁ X Y : Finset V) (K : ℕ)
    (hXK : X.card ≤ K) (hYK : Y.card ≤ K) (u : D₁) :
    |reservoirIncidence G D₁ Y u - reservoirIncidence G D₁ X u| ≤
      (K : ℤ) := by
  have hX0 : (0 : ℤ) ≤ reservoirIncidence G D₁ X u := by
    simp [reservoirIncidence]
  have hY0 : (0 : ℤ) ≤ reservoirIncidence G D₁ Y u := by
    simp [reservoirIncidence]
  have hX := abs_reservoirIncidence_le_of_card_le G D₁ X K hXK u
  have hY := abs_reservoirIncidence_le_of_card_le G D₁ Y K hYK u
  rw [abs_of_nonneg hX0] at hX
  rw [abs_of_nonneg hY0] at hY
  rw [abs_le]
  omega

/-! ## Decoding the inner half-slice -/

/-- Decode a half-slice of the subtype `D₁` as an ambient vertex set. -/
def halfDeletion (D₁ : Finset V) (nD : ℕ)
    (omega : HalfSample.Slice D₁ nD) : Finset V :=
  omega.1.map (Function.Embedding.subtype fun v : V ↦ v ∈ D₁)

/-- The half-deletion decoder agrees definitionally with the decoder used
by the graph partial exposure. -/
@[simp] lemma halfDeletion_eq_partialMap (D₁ : Finset V) (nD : ℕ)
    (omega : HalfSample.Slice D₁ nD) :
    halfDeletion D₁ nD omega =
      AugmentationGraphPartial.mapSubtypeFinset D₁ omega.1 :=
  rfl

@[simp] lemma card_halfDeletion (D₁ : Finset V) (nD : ℕ)
    (omega : HalfSample.Slice D₁ nD) :
    (halfDeletion D₁ nD omega).card = nD := by
  rw [halfDeletion, Finset.card_map]
  exact omega.2

lemma halfDeletion_subset (D₁ : Finset V) (nD : ℕ)
    (omega : HalfSample.Slice D₁ nD) :
    halfDeletion D₁ nD omega ⊆ D₁ :=
  by
    intro v hv
    obtain ⟨u, _hu, rfl⟩ := Finset.mem_map.mp hv
    exact u.2

lemma halfDeletion_subset_of_subset {D₁ U₀ : Finset V}
    (hD₁U₀ : D₁ ⊆ U₀) (nD : ℕ)
    (omega : HalfSample.Slice D₁ nD) :
    halfDeletion D₁ nD omega ⊆ U₀ :=
  (halfDeletion_subset D₁ nD omega).trans hD₁U₀

/-! ## Incidence statistics on a half-slice -/

/-- A sum of one matching-cell incidence vector over the decoded deletion
set is exactly the graph degree sum into that deletion set. -/
lemma halfSliceSum_incidenceVector_eq_degreeInto_halfDeletion
    (G : SimpleGraph V) (D₁ x : Finset V) (nD : ℕ)
    (omega : HalfSample.Slice D₁ nD) :
    HalfSample.sliceSum
        (fun u : D₁ ↦
          (reservoirIncidence G D₁ x u : ℝ)) omega =
      degreeInto G (halfDeletion D₁ nD omega) x := by
  classical
  simp only [HalfSample.sliceSum, reservoirIncidence]
  norm_cast
  rw [degreeInto_comm G (halfDeletion D₁ nD omega) x]
  simp only [degreeInto, halfDeletion]
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro u hu
  simp [incidence, Erdos88.neighborsIn, SimpleGraph.adj_comm]

/-- The signed deletion statistic attached to an ordered pair of cells.
The orientation is `Y - X`; it is the orientation occurring when `X` is
inserted in place of `Y`. -/
def replacementCoeff (G : SimpleGraph V) (D₁ X Y : Finset V)
    (u : D₁) : ℝ :=
  ((reservoirIncidence G D₁ Y u -
      reservoirIncidence G D₁ X u : ℤ) : ℝ)

/-- Uniform coordinate bound used by the increment second-moment estimate. -/
lemma abs_replacementCoeff_le_of_card_le
    (G : SimpleGraph V) (D₁ X Y : Finset V) (K : ℕ)
    (hXK : X.card ≤ K) (hYK : Y.card ≤ K) (u : D₁) :
    |replacementCoeff G D₁ X Y u| ≤ (K : ℝ) := by
  rw [replacementCoeff, ← Int.cast_abs]
  exact_mod_cast
    abs_reservoirIncidence_sub_le_of_card_le G D₁ X Y K hXK hYK u

/-- The total replacement coefficient is the full-reservoir degree
difference. -/
lemma sum_replacementCoeff_eq_degreeInto_sub
    (G : SimpleGraph V) (D₁ X Y : Finset V) :
    ∑ u, replacementCoeff G D₁ X Y u =
      (degreeInto G D₁ Y : ℝ) - degreeInto G D₁ X := by
  calc
    ∑ u, replacementCoeff G D₁ X Y u =
        (∑ u, (reservoirIncidence G D₁ Y u : ℝ)) -
          ∑ u, (reservoirIncidence G D₁ X u : ℝ) := by
      simp [replacementCoeff, Finset.sum_sub_distrib]
    _ = (degreeInto G D₁ Y : ℝ) - degreeInto G D₁ X := by
      have hY : (∑ u, (reservoirIncidence G D₁ Y u : ℝ)) =
          (degreeInto G D₁ Y : ℝ) := by
        exact_mod_cast sum_reservoirIncidence_eq_degreeInto G D₁ Y
      have hX : (∑ u, (reservoirIncidence G D₁ X u : ℝ)) =
          (degreeInto G D₁ X : ℝ) := by
        exact_mod_cast sum_reservoirIncidence_eq_degreeInto G D₁ X
      rw [hY, hX]

/-- Equal full-reservoir degrees center the replacement coefficient. -/
lemma sum_replacementCoeff_eq_zero_of_degree_eq
    (G : SimpleGraph V) (D₁ X Y : Finset V)
    (hdegree : degreeInto G D₁ X = degreeInto G D₁ Y) :
    ∑ u, replacementCoeff G D₁ X Y u = 0 := by
  rw [sum_replacementCoeff_eq_degreeInto_sub, hdegree, sub_self]

/-- Its `l1` mass is exactly the diversity quantity retained by
`AugmentationGraphPartial.PartialGood`. -/
lemma sum_abs_replacementCoeff_eq_incidenceDiffMass
    (G : SimpleGraph V) (D₁ X Y : Finset V) :
    ∑ u, |replacementCoeff G D₁ X Y u| =
      incidenceDiffMass G D₁ X Y := by
  calc
    ∑ u, |replacementCoeff G D₁ X Y u| =
        incidenceDiffMass G D₁ Y X := by
      simpa [replacementCoeff, reservoirIncidence,
        AugmentationGraphPartial.incidenceVector] using
        AugmentationGraphPartial.sum_abs_incidenceVector_sub_eq_incidenceDiffMass
          G D₁ Y X
    _ = incidenceDiffMass G D₁ X Y := by
      exact_mod_cast incidenceDiffMass_comm G D₁ Y X

/-- The half-slice linear statistic for `replacementCoeff X Y` is exactly
`deg_D(Y) - deg_D(X)`. -/
lemma sliceSum_replacementCoeff
    (G : SimpleGraph V) (D₁ X Y : Finset V) (nD : ℕ)
    (omega : HalfSample.Slice D₁ nD) :
    HalfSample.sliceSum (replacementCoeff G D₁ X Y) omega =
      (degreeInto G (halfDeletion D₁ nD omega) Y : ℝ) -
        degreeInto G (halfDeletion D₁ nD omega) X := by
  classical
  calc
    HalfSample.sliceSum (replacementCoeff G D₁ X Y) omega =
        HalfSample.sliceSum
            (fun u : D₁ ↦ (reservoirIncidence G D₁ Y u : ℝ)) omega -
          HalfSample.sliceSum
            (fun u : D₁ ↦ (reservoirIncidence G D₁ X u : ℝ)) omega := by
      simp [replacementCoeff, HalfSample.sliceSum, Finset.sum_sub_distrib]
    _ = (degreeInto G (halfDeletion D₁ nD omega) Y : ℝ) -
          degreeInto G (halfDeletion D₁ nD omega) X := by
      rw [halfSliceSum_incidenceVector_eq_degreeInto_halfDeletion,
        halfSliceSum_incidenceVector_eq_degreeInto_halfDeletion]

/-! ## Literal graph path -/

/-- The fixed base remaining after the inner deletion. -/
def deletionBase (W U₀ D : Finset V) : Finset V :=
  W ∪ (U₀ \ D)

/-- The exposed graph at a switching state `Z`. -/
def literalState (W U₀ D Z : Finset V) : Finset V :=
  deletionBase W U₀ D ∪ Z

/-- The literal natural-valued induced-edge path at a state `Z`. -/
def literalPathNat (G : SimpleGraph V) (W U₀ D Z : Finset V) : ℕ :=
  Erdos88.inducedEdges G (literalState W U₀ D Z)

/-- The real-valued version used by the separated-switching package. -/
def literalPath (G : SimpleGraph V) (W U₀ D Z : Finset V) : ℝ :=
  literalPathNat G W U₀ D Z

@[simp] lemma literalPath_eq_cast (G : SimpleGraph V)
    (W U₀ D Z : Finset V) :
    literalPath G W U₀ D Z =
      (Erdos88.inducedEdges G ((W ∪ (U₀ \ D)) ∪ Z) : ℝ) :=
  rfl

/-- Oriented crossing-edge cardinality in the degree-sum convention used by
the incidence vectors. -/
lemma card_interedges_eq_degreeInto (G : SimpleGraph V)
    (A B : Finset V) :
    (G.interedges A B).card = degreeInto G A B := by
  rw [degreeInto_comm G A B,
    degreeInto_eq_card_interedges G B A]

private lemma disjoint_sdiff_left {A B D : Finset V}
    (hAB : Disjoint A B) : Disjoint (A \ D) B := by
  exact hAB.mono_left Finset.sdiff_subset

private lemma disjoint_sdiff_right {A B D : Finset V}
    (hAB : Disjoint A B) : Disjoint A (B \ D) := by
  exact hAB.mono_right Finset.sdiff_subset

/-! ## Endpoint identity -/

/-- The deterministic part of the change from endpoint `Z₀` to endpoint
`Z₁`, before the random deletion statistic is added. -/
def endpointOffsetInt (G : SimpleGraph V)
    (W U₀ Z₀ Z₁ : Finset V) : ℤ :=
  (Erdos88.inducedEdges G Z₁ : ℤ) - Erdos88.inducedEdges G Z₀ +
    ((G.interedges W Z₁).card : ℤ) - (G.interedges W Z₀).card +
    (degreeInto G U₀ Z₁ : ℤ) - degreeInto G U₀ Z₀

/-- Exact integer endpoint identity for the literal graph path. -/
theorem literalEndpoint_difference_int
    (G : SimpleGraph V) (W U₀ D Z₀ Z₁ : Finset V)
    (hDU : D ⊆ U₀)
    (hWU : Disjoint W U₀)
    (hWZ₀ : Disjoint W Z₀) (hWZ₁ : Disjoint W Z₁)
    (hUZ₀ : Disjoint U₀ Z₀) (hUZ₁ : Disjoint U₀ Z₁) :
    (literalPathNat G W U₀ D Z₁ : ℤ) -
        literalPathNat G W U₀ D Z₀ =
      endpointOffsetInt G W U₀ Z₀ Z₁ +
        ((degreeInto G D Z₀ : ℤ) - degreeInto G D Z₁) := by
  have hWU' : Disjoint W (U₀ \ D) := disjoint_sdiff_right hWU
  have hUZ₀' : Disjoint (U₀ \ D) Z₀ := disjoint_sdiff_left hUZ₀
  have hUZ₁' : Disjoint (U₀ \ D) Z₁ := disjoint_sdiff_left hUZ₁
  simp only [literalPathNat, literalState, deletionBase]
  rw [inducedEdges_augmentation_state G hWU' hWZ₁ hUZ₁',
    inducedEdges_augmentation_state G hWU' hWZ₀ hUZ₀']
  rw [card_interedges_eq_degreeInto G (U₀ \ D) Z₁,
    card_interedges_eq_degreeInto G (U₀ \ D) Z₀]
  push_cast
  rw [
    degreeInto_sdiff_int_of_subset G hDU,
    degreeInto_sdiff_int_of_subset G hDU]
  simp only [endpointOffsetInt]
  ring

/-- Canonical affine endpoint certificate on a half deletion set.  This is
the exact `endpointIdentity` required by `PartialExposureData`. -/
theorem literalEndpoint_affine
    (G : SimpleGraph V) (W U₀ D₁ Z₀ Z₁ : Finset V) (nD : ℕ)
    (omega : HalfSample.Slice D₁ nD)
    (hD₁U₀ : D₁ ⊆ U₀)
    (hWU : Disjoint W U₀)
    (hWZ₀ : Disjoint W Z₀) (hWZ₁ : Disjoint W Z₁)
    (hUZ₀ : Disjoint U₀ Z₀) (hUZ₁ : Disjoint U₀ Z₁) :
    literalPath G W U₀ (halfDeletion D₁ nD omega) Z₁ -
        literalPath G W U₀ (halfDeletion D₁ nD omega) Z₀ =
      (endpointOffsetInt G W U₀ Z₀ Z₁ : ℝ) +
        HalfSample.sliceSum (replacementCoeff G D₁ Z₁ Z₀) omega := by
  have hint := literalEndpoint_difference_int G W U₀
    (halfDeletion D₁ nD omega) Z₀ Z₁
    (halfDeletion_subset_of_subset hD₁U₀ nD omega)
    hWU hWZ₀ hWZ₁ hUZ₀ hUZ₁
  rw [sliceSum_replacementCoeff]
  simp only [literalPath]
  exact_mod_cast hint

/-! ## One-cell switching increment -/

/-- Deterministic part of the switch which inserts `X` and removes `Y`,
leaving the common state `R` fixed. -/
def switchOffsetInt (G : SimpleGraph V)
    (W U₀ R X Y : Finset V) : ℤ :=
  ((G.interedges W X).card : ℤ) - (G.interedges W Y).card +
    (degreeInto G U₀ X : ℤ) - degreeInto G U₀ Y +
    ((Erdos88.inducedEdges G (R ∪ X) : ℤ) -
      Erdos88.inducedEdges G (R ∪ Y))

/-- Exact integer one-cell switching identity after deletion. -/
theorem literalSwitch_difference_int
    (G : SimpleGraph V) (W U₀ D R X Y : Finset V)
    (hDU : D ⊆ U₀)
    (hWU : Disjoint W U₀)
    (hWR : Disjoint W R) (hWX : Disjoint W X)
    (hWY : Disjoint W Y)
    (hUR : Disjoint U₀ R) (hUX : Disjoint U₀ X)
    (hUY : Disjoint U₀ Y)
    (hRX : Disjoint R X) (hRY : Disjoint R Y) :
    (literalPathNat G W U₀ D (R ∪ X) : ℤ) -
        literalPathNat G W U₀ D (R ∪ Y) =
      switchOffsetInt G W U₀ R X Y +
        ((degreeInto G D Y : ℤ) - degreeInto G D X) := by
  have hWU' : Disjoint W (U₀ \ D) := disjoint_sdiff_right hWU
  have hUR' : Disjoint (U₀ \ D) R := disjoint_sdiff_left hUR
  have hUX' : Disjoint (U₀ \ D) X := disjoint_sdiff_left hUX
  have hUY' : Disjoint (U₀ \ D) Y := disjoint_sdiff_left hUY
  have hBR : Disjoint (deletionBase W U₀ D) R := by
    exact Finset.disjoint_union_left.mpr ⟨hWR, hUR'⟩
  have hBX : Disjoint (deletionBase W U₀ D) X := by
    exact Finset.disjoint_union_left.mpr ⟨hWX, hUX'⟩
  have hBY : Disjoint (deletionBase W U₀ D) Y := by
    exact Finset.disjoint_union_left.mpr ⟨hWY, hUY'⟩
  simp only [literalPathNat, literalState]
  rw [inducedEdges_switch_difference G
      hBR hBX hBY hRX hRY]
  rw [deletionBase,
    card_interedges_union_left_of_disjoint G hWU' X,
    card_interedges_union_left_of_disjoint G hWU' Y,
    card_interedges_eq_degreeInto G (U₀ \ D) X,
    card_interedges_eq_degreeInto G (U₀ \ D) Y]
  push_cast
  rw [
    degreeInto_sdiff_int_of_subset G hDU,
    degreeInto_sdiff_int_of_subset G hDU]
  simp only [switchOffsetInt]
  ring

/-- Affine half-slice form of a one-cell switching increment. -/
theorem literalSwitch_affine
    (G : SimpleGraph V) (W U₀ D₁ R X Y : Finset V) (nD : ℕ)
    (omega : HalfSample.Slice D₁ nD)
    (hD₁U₀ : D₁ ⊆ U₀)
    (hWU : Disjoint W U₀)
    (hWR : Disjoint W R) (hWX : Disjoint W X)
    (hWY : Disjoint W Y)
    (hUR : Disjoint U₀ R) (hUX : Disjoint U₀ X)
    (hUY : Disjoint U₀ Y)
    (hRX : Disjoint R X) (hRY : Disjoint R Y) :
    literalPath G W U₀ (halfDeletion D₁ nD omega) (R ∪ X) -
        literalPath G W U₀ (halfDeletion D₁ nD omega) (R ∪ Y) =
      (switchOffsetInt G W U₀ R X Y : ℝ) +
        HalfSample.sliceSum (replacementCoeff G D₁ X Y) omega := by
  have hint := literalSwitch_difference_int G W U₀
    (halfDeletion D₁ nD omega) R X Y
    (halfDeletion_subset_of_subset hD₁U₀ nD omega)
    hWU hWR hWX hWY hUR hUX hUY hRX hRY
  rw [sliceSum_replacementCoeff]
  simp only [literalPath]
  exact_mod_cast hint

/-- The graph-specialized half-slice second-moment estimate for a backward
one-cell switch.  The displayed increment is `low - high` when `X = low`
and `Y = high`.  Its deterministic hypothesis bounds the actual mean: the
literal offset plus one half of the full-reservoir degree difference. -/
theorem uniformExpectation_literalSwitch_sq_le
    (G : SimpleGraph V) (W U₀ D₁ R X Y : Finset V) (nD K : ℕ)
    (R₀ : ℝ)
    (hcard : D₁.card = 2 * nD) (hnD : 0 < nD)
    (hD₁U₀ : D₁ ⊆ U₀)
    (hWU₀ : Disjoint W U₀)
    (hWR : Disjoint W R) (hWX : Disjoint W X)
    (hWY : Disjoint W Y)
    (hU₀R : Disjoint U₀ R) (hU₀X : Disjoint U₀ X)
    (hU₀Y : Disjoint U₀ Y)
    (hRX : Disjoint R X) (hRY : Disjoint R Y)
    (hXK : X.card ≤ K) (hYK : Y.card ≤ K)
    (hR₀ : 0 ≤ R₀)
    (hoffsetMean : |(switchOffsetInt G W U₀ R X Y : ℝ) +
      ((degreeInto G D₁ Y : ℝ) - degreeInto G D₁ X) / 2| ≤
        R₀ * Real.sqrt nD) :
    Erdos88.Concentration.uniformExpectation
      (fun omega : HalfSample.Slice D₁ nD ↦
        (literalPath G W U₀ (halfDeletion D₁ nD omega) (R ∪ X) -
          literalPath G W U₀ (halfDeletion D₁ nD omega) (R ∪ Y)) ^ 2) ≤
      (((K : ℝ) ^ 2 + R₀ ^ 2) * nD) := by
  have hcard' : Fintype.card D₁ = 2 * nD := by
    simpa using hcard
  let _ := HalfSample.sliceNonempty hcard'
  have hcoeff : ∀ u : D₁,
      |replacementCoeff G D₁ X Y u| ≤ (K : ℝ) :=
    abs_replacementCoeff_le_of_card_le G D₁ X Y K hXK hYK
  have hmeanBound : |(switchOffsetInt G W U₀ R X Y : ℝ) +
      (∑ u : D₁, replacementCoeff G D₁ X Y u) / 2| ≤
        R₀ * Real.sqrt nD := by
    rw [sum_replacementCoeff_eq_degreeInto_sub]
    exact hoffsetMean
  have hsecond := HalfSampleVariance.uniformExpectation_add_sliceSum_sq_le_of_mean_pos
    hcard' hnD (replacementCoeff G D₁ X Y) (K : ℝ)
      (by positivity) hcoeff
      (switchOffsetInt G W U₀ R X Y : ℝ) R₀ hR₀ hmeanBound
  calc
    Erdos88.Concentration.uniformExpectation
        (fun omega : HalfSample.Slice D₁ nD ↦
          (literalPath G W U₀ (halfDeletion D₁ nD omega) (R ∪ X) -
            literalPath G W U₀ (halfDeletion D₁ nD omega) (R ∪ Y)) ^ 2) =
      Erdos88.Concentration.uniformExpectation
        (fun omega : HalfSample.Slice D₁ nD ↦
          ((switchOffsetInt G W U₀ R X Y : ℝ) +
            HalfSample.sliceSum (replacementCoeff G D₁ X Y) omega) ^ 2) := by
          congr 1
          funext omega
          rw [literalSwitch_affine G W U₀ D₁ R X Y nD omega
            hD₁U₀ hWU₀ hWR hWX hWY hU₀R hU₀X hU₀Y hRX hRY]
    _ ≤ (((K : ℝ) ^ 2 + R₀ ^ 2) * nD) := hsecond

/-! ## Candidate extensions and collisions -/

/-- The deterministic contribution of adjoining candidate `x` to state
`Z`, before subtracting its incidences into the deletion set. -/
def candidateOffsetInt (G : SimpleGraph V)
    (W U₀ Z x : Finset V) : ℤ :=
  (Erdos88.inducedEdges G x : ℤ) +
    (G.interedges W x).card + degreeInto G U₀ x +
    (G.interedges Z x).card

/-- Exact contribution of adjoining one candidate cell to a literal state. -/
theorem literalCandidateExtension_sub_base_int
    (G : SimpleGraph V) (W U₀ D Z x : Finset V)
    (hDU : D ⊆ U₀)
    (hWU : Disjoint W U₀)
    (hWZ : Disjoint W Z) (hUZ : Disjoint U₀ Z)
    (hWx : Disjoint W x) (hUx : Disjoint U₀ x)
    (hZx : Disjoint Z x) :
    (Erdos88.inducedEdges G (literalState W U₀ D Z ∪ x) : ℤ) -
        literalPathNat G W U₀ D Z =
      candidateOffsetInt G W U₀ Z x - degreeInto G D x := by
  have hWU' : Disjoint W (U₀ \ D) := disjoint_sdiff_right hWU
  have hUZ' : Disjoint (U₀ \ D) Z := disjoint_sdiff_left hUZ
  have hUx' : Disjoint (U₀ \ D) x := disjoint_sdiff_left hUx
  have hBZ : Disjoint (deletionBase W U₀ D) Z := by
    exact Finset.disjoint_union_left.mpr ⟨hWZ, hUZ'⟩
  have hBx : Disjoint (deletionBase W U₀ D) x := by
    exact Finset.disjoint_union_left.mpr ⟨hWx, hUx'⟩
  simp only [literalState, literalPathNat]
  rw [show (deletionBase W U₀ D ∪ Z) ∪ x =
      deletionBase W U₀ D ∪ (Z ∪ x) by
        simp only [Finset.union_assoc]]
  rw [inducedEdges_add_matching_cell G hBZ hBx hZx]
  rw [deletionBase,
    card_interedges_union_left_of_disjoint G hWU' x,
    card_interedges_eq_degreeInto G (U₀ \ D) x]
  push_cast
  rw [
    degreeInto_sdiff_int_of_subset G hDU]
  simp only [candidateOffsetInt]
  ring

/-- Affine half-slice form of one candidate extension. -/
theorem literalCandidateExtension_affine
    (G : SimpleGraph V) (W U₀ D₁ Z x : Finset V) (nD : ℕ)
    (omega : HalfSample.Slice D₁ nD)
    (hD₁U₀ : D₁ ⊆ U₀)
    (hWU : Disjoint W U₀)
    (hWZ : Disjoint W Z) (hUZ : Disjoint U₀ Z)
    (hWx : Disjoint W x) (hUx : Disjoint U₀ x)
    (hZx : Disjoint Z x) :
    (Erdos88.inducedEdges G
        (literalState W U₀ (halfDeletion D₁ nD omega) Z ∪ x) : ℝ) -
        literalPath G W U₀ (halfDeletion D₁ nD omega) Z =
      (candidateOffsetInt G W U₀ Z x : ℝ) -
        HalfSample.sliceSum
          (fun u : D₁ ↦
            (reservoirIncidence G D₁ x u : ℝ)) omega := by
  have hint := literalCandidateExtension_sub_base_int G W U₀
    (halfDeletion D₁ nD omega) Z x
    (halfDeletion_subset_of_subset hD₁U₀ nD omega)
    hWU hWZ hUZ hWx hUx hZx
  rw [halfSliceSum_incidenceVector_eq_degreeInto_halfDeletion]
  simp only [literalPath]
  exact_mod_cast hint

/-- Exact collision difference between two candidates at one fixed state. -/
theorem literalCandidateCollision_difference_int
    (G : SimpleGraph V) (W U₀ D Z x y : Finset V)
    (hDU : D ⊆ U₀)
    (hWU : Disjoint W U₀)
    (hWZ : Disjoint W Z) (hUZ : Disjoint U₀ Z)
    (hWx : Disjoint W x) (hUx : Disjoint U₀ x)
    (hZx : Disjoint Z x)
    (hWy : Disjoint W y) (hUy : Disjoint U₀ y)
    (hZy : Disjoint Z y) :
    (Erdos88.inducedEdges G (literalState W U₀ D Z ∪ x) : ℤ) -
        Erdos88.inducedEdges G (literalState W U₀ D Z ∪ y) =
      candidateOffsetInt G W U₀ Z x -
        candidateOffsetInt G W U₀ Z y +
        ((degreeInto G D y : ℤ) - degreeInto G D x) := by
  have hx := literalCandidateExtension_sub_base_int G W U₀ D Z x
    hDU hWU hWZ hUZ hWx hUx hZx
  have hy := literalCandidateExtension_sub_base_int G W U₀ D Z y
    hDU hWU hWZ hUZ hWy hUy hZy
  linarith

/-- Candidate collision difference as an affine half-slice statistic. -/
theorem literalCandidateCollision_affine
    (G : SimpleGraph V) (W U₀ D₁ Z x y : Finset V) (nD : ℕ)
    (omega : HalfSample.Slice D₁ nD)
    (hD₁U₀ : D₁ ⊆ U₀)
    (hWU : Disjoint W U₀)
    (hWZ : Disjoint W Z) (hUZ : Disjoint U₀ Z)
    (hWx : Disjoint W x) (hUx : Disjoint U₀ x)
    (hZx : Disjoint Z x)
    (hWy : Disjoint W y) (hUy : Disjoint U₀ y)
    (hZy : Disjoint Z y) :
    (Erdos88.inducedEdges G
        (literalState W U₀ (halfDeletion D₁ nD omega) Z ∪ x) : ℝ) -
        Erdos88.inducedEdges G
          (literalState W U₀ (halfDeletion D₁ nD omega) Z ∪ y) =
      ((candidateOffsetInt G W U₀ Z x -
          candidateOffsetInt G W U₀ Z y : ℤ) : ℝ) +
        HalfSample.sliceSum (replacementCoeff G D₁ x y) omega := by
  have hint := literalCandidateCollision_difference_int G W U₀
    (halfDeletion D₁ nD omega) Z x y
    (halfDeletion_subset_of_subset hD₁U₀ nD omega)
    hWU hWZ hUZ hWx hUx hZx hWy hUy hZy
  rw [sliceSum_replacementCoeff]
  exact_mod_cast hint

/-- Equality of the two literal candidate extensions is exactly a point
event for the incidence linear statistic. -/
theorem literalCandidateCollision_iff
    (G : SimpleGraph V) (W U₀ D₁ Z x y : Finset V) (nD : ℕ)
    (omega : HalfSample.Slice D₁ nD)
    (hD₁U₀ : D₁ ⊆ U₀)
    (hWU : Disjoint W U₀)
    (hWZ : Disjoint W Z) (hUZ : Disjoint U₀ Z)
    (hWx : Disjoint W x) (hUx : Disjoint U₀ x)
    (hZx : Disjoint Z x)
    (hWy : Disjoint W y) (hUy : Disjoint U₀ y)
    (hZy : Disjoint Z y) :
    Erdos88.inducedEdges G
        (literalState W U₀ (halfDeletion D₁ nD omega) Z ∪ x) =
      Erdos88.inducedEdges G
        (literalState W U₀ (halfDeletion D₁ nD omega) Z ∪ y) ↔
    HalfSample.sliceSum (replacementCoeff G D₁ x y) omega =
      ((candidateOffsetInt G W U₀ Z y -
          candidateOffsetInt G W U₀ Z x : ℤ) : ℝ) := by
  have hdiff := literalCandidateCollision_affine G W U₀ D₁ Z x y nD omega
    hD₁U₀ hWU hWZ hUZ hWx hUx hZx hWy hUy hZy
  constructor
  · intro hxy
    rw [hxy] at hdiff
    simp only [sub_self] at hdiff
    push_cast at hdiff ⊢
    linarith
  · intro hsum
    have hreal :
        (Erdos88.inducedEdges G
            (literalState W U₀ (halfDeletion D₁ nD omega) Z ∪ x) : ℝ) =
          Erdos88.inducedEdges G
            (literalState W U₀ (halfDeletion D₁ nD omega) Z ∪ y) := by
      rw [hsum] at hdiff
      push_cast at hdiff
      linarith
    exact_mod_cast hreal

end

end AugmentationGraphFullIdentity
end Erdos636
