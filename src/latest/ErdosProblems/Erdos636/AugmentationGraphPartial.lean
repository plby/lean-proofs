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

import ErdosProblems.Erdos636.AugmentationPartial
import ErdosProblems.Erdos636.NestedUniform
import ErdosProblems.Erdos636.SlicePersistence
import ErdosProblems.Erdos636.Structural

/-!
# The graph partial exposure in the Kwan--Sudakov augmentation

This file instantiates the finite partial-exposure selector with the
incidence vectors of a uniform matching.  The random object is an outer
`2 n_D`-subset `D₁` of the structural reservoir `U₀`.  The good event keeps
two disjoint matching subfamilies of prescribed size, retains pairwise
incidence diversity in one of them, controls degree deviations in both,
and bounds the collision graph of the other.

The event itself is independent of the later switching time.  Thus the
same outer deletion can be averaged over, fixed once, and then used at all
times of the switching path.
-/

open Classical SimpleGraph
open scoped BigOperators

namespace Erdos636
namespace AugmentationGraphPartial

open Erdos88.Concentration
open Erdos88.Fourier

universe u v

noncomputable section

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## Outer-slice decoding -/

/-- Map a finset of reservoir-subtype vertices back to ambient vertices. -/
def mapSubtypeFinset (U₀ : Finset V) (D : Finset U₀) : Finset V :=
  D.map (Function.Embedding.subtype fun v : V ↦ v ∈ U₀)

@[simp] lemma card_mapSubtypeFinset (U₀ : Finset V) (D : Finset U₀) :
    (mapSubtypeFinset U₀ D).card = D.card := by
  exact Finset.card_map _

lemma mapSubtypeFinset_subset (U₀ : Finset V) (D : Finset U₀) :
    mapSubtypeFinset U₀ D ⊆ U₀ := by
  intro v hv
  obtain ⟨u, _hu, rfl⟩ := Finset.mem_map.mp hv
  exact u.2

/-- Decode a Fourier Boolean slice on `U₀` as an ambient vertex set. -/
def sampleFinset (U₀ : Finset V) (s : ℕ) (omega : BoolSlice U₀ s) :
    Finset V :=
  mapSubtypeFinset U₀ (SlicePersistence.sampleFinset s omega)

@[simp] lemma card_sampleFinset (U₀ : Finset V) (s : ℕ)
    (omega : BoolSlice U₀ s) :
    (sampleFinset U₀ s omega).card = s := by
  rw [sampleFinset, card_mapSubtypeFinset,
    SlicePersistence.card_sampleFinset]

lemma sampleFinset_subset (U₀ : Finset V) (s : ℕ)
    (omega : BoolSlice U₀ s) :
    sampleFinset U₀ s omega ⊆ U₀ :=
  mapSubtypeFinset_subset U₀ _

/-- Fourier slices on the reservoir subtype and finset-valued layer points
are exactly equivalent. -/
def boolSliceEquivBooleanSlicePoint (U₀ : Finset V) (s : ℕ) :
    BoolSlice U₀ s ≃
      Erdos88.BooleanSlices.BooleanSlicePoint U₀ s :=
  (boolSliceEquivFinsetLen U₀ s).trans
    { toFun := fun D ↦ ⟨mapSubtypeFinset U₀ D.1, by
        rw [Erdos88.BooleanSlices.mem_booleanSlice]
        exact ⟨mapSubtypeFinset_subset U₀ D.1,
          (card_mapSubtypeFinset U₀ D.1).trans D.2⟩⟩
      invFun := fun D ↦
        ⟨Erdos88.BooleanSlices.finsetLift U₀ D.1, by
          rw [Erdos88.BooleanSlices.card_finsetLift U₀ D.1
            (Erdos88.BooleanSlices.mem_booleanSlice.mp D.2).1]
          exact (Erdos88.BooleanSlices.mem_booleanSlice.mp D.2).2⟩
      left_inv := by
        intro D
        apply Subtype.ext
        apply Finset.map_injective
          (Function.Embedding.subtype fun v : V ↦ v ∈ U₀)
        rw [Erdos88.BooleanSlices.map_finsetLift]
        · rfl
        · exact mapSubtypeFinset_subset U₀ D.1
      right_inv := by
        intro D
        apply Subtype.ext
        exact Erdos88.BooleanSlices.map_finsetLift U₀ D.1
          (Erdos88.BooleanSlices.mem_booleanSlice.mp D.2).1 }

/-- The repository's two names for the ambient fixed-cardinality layer are
definitionally the same finset, but their packaged point types use distinct
definitions. -/
def booleanSlicePointEquivLayer (U₀ : Finset V) (s : ℕ) :
    Erdos88.BooleanSlices.BooleanSlicePoint U₀ s ≃
      {D // D ∈ NestedUniform.layer U₀ s} where
  toFun D := ⟨D.1, by
    simpa [Erdos88.BooleanSlices.booleanSlice, NestedUniform.layer] using D.2⟩
  invFun D := ⟨D.1, by
    simpa [Erdos88.BooleanSlices.booleanSlice, NestedUniform.layer] using D.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] lemma boolSliceEquivBooleanSlicePoint_val
    (U₀ : Finset V) (s : ℕ) (omega : BoolSlice U₀ s) :
    (boolSliceEquivBooleanSlicePoint U₀ s omega).1 =
      sampleFinset U₀ s omega :=
  rfl

/-- The normalized Boolean-slice probability is the normalized finset-layer
probability after decoding. -/
lemma uniformProbability_sampleFinset_eq_layerProbability
    (U₀ : Finset V) (s : ℕ)
    [Nonempty (BoolSlice U₀ s)]
    [Nonempty (Erdos88.BooleanSlices.BooleanSlicePoint U₀ s)]
    (event : Finset V → Prop) :
    uniformProbability
        (fun omega : BoolSlice U₀ s ↦ event (sampleFinset U₀ s omega)) =
      NestedUniform.layerProbability U₀ s event := by
  classical
  letI : Nonempty {D // D ∈ NestedUniform.layer U₀ s} :=
    ⟨booleanSlicePointEquivLayer U₀ s
      (Classical.choice (inferInstance : Nonempty
        (Erdos88.BooleanSlices.BooleanSlicePoint U₀ s)))⟩
  change uniformProbability
      (fun omega : BoolSlice U₀ s ↦
        event ((((boolSliceEquivBooleanSlicePoint U₀ s).trans
          (booleanSlicePointEquivLayer U₀ s)) omega).1)) = _
  rw [SlicePersistence.uniformProbability_equiv
    ((boolSliceEquivBooleanSlicePoint U₀ s).trans
      (booleanSlicePointEquivLayer U₀ s)) (fun D ↦ event D.1)]
  simp only [uniformProbability, NestedUniform.layerProbability]
  congr 1
  · rw [Finset.univ_eq_attach, NestedUniform.layer]
    simpa using congrArg Finset.card
      (Finset.filter_attach event (U₀.powersetCard s))
  · rw [Fintype.card_coe, NestedUniform.card_layer]

/-- The real degree window used at the partial exposure. -/
def DegreeGood (G : SimpleGraph V) (D₁ x : Finset V)
    (center radius : ℝ) : Prop :=
  |(degreeInto G D₁ x : ℝ) - center| ≤ radius

/-- A fixed classical order on the finite type of vertex cells.  It is used
only to orient each unordered collision pair once. -/
noncomputable def cellLinearOrder : LinearOrder (Finset V) :=
  LinearOrder.lift' (Fintype.equivFin (Finset V))
    (Fintype.equivFin (Finset V)).injective

/-- The collision edges between cells, using the fixed orientation above. -/
noncomputable def cellCollisionEdges (S₀ : Finset (Finset V))
    (value : Finset V → ℕ) : Finset (Finset V × Finset V) := by
  letI : LinearOrder (Finset V) := cellLinearOrder
  exact CollisionCounting.collisionEdges S₀ (fun x (_ : Unit) ↦ value x) ()

/-- The complete graph-facing good event for the outer exposure.

The witnesses `S₀` and `X₀` are included in the event so downstream code
does not have to make a second finite choice after fixing `D₁`. -/
def PartialGood (G : SimpleGraph V) (M : Finset (Finset V))
    (s₀ : ℕ) (diversityThreshold center radius tS tX tCollision : ℝ)
    (D₁ : Finset V) : Prop :=
  ∃ S₀ X₀ : Finset (Finset V),
    S₀ ⊆ M ∧ X₀ ⊆ M ∧ S₀.card = s₀ ∧ X₀.card = s₀ ∧
    Disjoint S₀ X₀ ∧
    (∀ x ∈ X₀, ∀ y ∈ X₀, x ≠ y →
      diversityThreshold ≤ incidenceDiffMass G D₁ x y) ∧
    ((S₀.filter fun x ↦ ¬ DegreeGood G D₁ x center radius).card : ℝ) < tS ∧
    ((X₀.filter fun x ↦ ¬ DegreeGood G D₁ x center radius).card : ℝ) < tX ∧
    ((cellCollisionEdges S₀ (degreeInto G D₁)).card : ℝ) < tCollision

/-- An explicitly time-indexed spelling of `PartialGood`.  It is
definitionally independent of the index: one outer sample works for every
switching time. -/
def PartialGoodAt {T : Type v} (G : SimpleGraph V)
    (M : Finset (Finset V)) (s₀ : ℕ)
    (diversityThreshold center radius tS tX tCollision : ℝ)
    (_time : T) (D₁ : Finset V) : Prop :=
  PartialGood G M s₀ diversityThreshold center radius tS tX tCollision D₁

@[simp] lemma partialGoodAt_iff {T : Type v} (G : SimpleGraph V)
    (M : Finset (Finset V)) (s₀ : ℕ)
    (diversityThreshold center radius tS tX tCollision : ℝ)
    (time : T) (D₁ : Finset V) :
    PartialGoodAt G M s₀ diversityThreshold center radius tS tX tCollision
        time D₁ ↔
      PartialGood G M s₀ diversityThreshold center radius tS tX tCollision
        D₁ :=
  Iff.rfl

/-! ## Deterministic family selection and extraction -/

/-- Split off two disjoint subfamilies of the same prescribed size. -/
lemma exists_two_disjoint_subsets_card_eq
    {A : Type*} [DecidableEq A] (M : Finset A) (s₀ : ℕ)
    (hcard : 2 * s₀ ≤ M.card) :
    ∃ S₀ X₀ : Finset A,
      S₀ ⊆ M ∧ X₀ ⊆ M ∧ S₀.card = s₀ ∧ X₀.card = s₀ ∧
        Disjoint S₀ X₀ := by
  obtain ⟨S₀, hS₀M, hS₀card⟩ :=
    Finset.exists_subset_card_eq (show s₀ ≤ M.card by omega)
  have hremain : s₀ ≤ (M \ S₀).card := by
    rw [Finset.card_sdiff_of_subset hS₀M, hS₀card]
    omega
  obtain ⟨X₀, hX₀remain, hX₀card⟩ :=
    Finset.exists_subset_card_eq hremain
  refine ⟨S₀, X₀, hS₀M, hX₀remain.trans Finset.sdiff_subset,
    hS₀card, hX₀card, ?_⟩
  rw [Finset.disjoint_left]
  intro x hxS hxX
  exact (Finset.mem_sdiff.mp (hX₀remain hxX)).2 hxS

/-- The cells surviving the degree window inside a finite family. -/
def goodCells (G : SimpleGraph V) (D₁ : Finset V)
    (center radius : ℝ) (X : Finset (Finset V)) : Finset (Finset V) :=
  X.filter fun x ↦ DegreeGood G D₁ x center radius

lemma card_sub_lt_add_card_goodCells
    (G : SimpleGraph V) (D₁ : Finset V) (center radius t : ℝ)
    (X : Finset (Finset V))
    (hbad : ((X.filter fun x ↦ ¬ DegreeGood G D₁ x center radius).card : ℝ) < t) :
    (X.card : ℝ) < t + (goodCells G D₁ center radius X).card := by
  have hsplit : X.card =
      (X.filter fun x ↦ ¬ DegreeGood G D₁ x center radius).card +
        (goodCells G D₁ center radius X).card := by
    rw [goodCells]
    classical
    have h := Finset.card_filter_add_card_filter_not
      (s := X) (p := fun x ↦ DegreeGood G D₁ x center radius)
    omega
  calc
    (X.card : ℝ) =
        (X.filter fun x ↦ ¬ DegreeGood G D₁ x center radius).card +
          (goodCells G D₁ center radius X).card := by exact_mod_cast hsplit
    _ < t + (goodCells G D₁ center radius X).card :=
      by linarith

/-! ## Incidence-vector identities -/

/-- The incidence vector of one matching cell, restricted to `U₀`. -/
def incidenceVector (G : SimpleGraph V) (U₀ x : Finset V)
    (u : U₀) : ℤ :=
  incidence G x u.1

/-- Summing the incidence vector over the reservoir gives the structural
degree sum. -/
lemma sum_incidenceVector_eq_degreeInto
    (G : SimpleGraph V) (U₀ x : Finset V) :
    ∑ u : U₀, incidenceVector G U₀ x u = degreeInto G U₀ x := by
  simp only [incidenceVector, incidence, degreeInto,
    Erdos88.neighborsIn, Finset.card_filter]
  push_cast
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  rw [← (Finset.attach_eq_univ (s := U₀))]
  simpa using Finset.sum_attach U₀
    (fun u ↦ if G.Adj v u then (1 : ℕ) else 0)

/-- The real `l1` distance between two incidence vectors is precisely the
restricted incidence-difference mass. -/
lemma sum_abs_incidenceVector_sub_eq_incidenceDiffMass
    (G : SimpleGraph V) (U₀ x y : Finset V) :
    (∑ u : U₀,
        |(((incidenceVector G U₀ x u - incidenceVector G U₀ y u : ℤ) : ℝ))|) =
      incidenceDiffMass G U₀ x y := by
  rw [incidenceDiffMass]
  push_cast
  rw [Finset.sum_subtype U₀ (fun _ ↦ Iff.rfl)]
  apply Finset.sum_congr rfl
  intro u hu
  simp [incidenceVector, incidenceDiffTerm]

/-- Every coordinate of a `k`-vertex cell's incidence vector lies in
`[0,k]`. -/
lemma abs_incidenceVector_le_of_card_le
    (G : SimpleGraph V) (U₀ x : Finset V) (K : ℕ)
    (hxK : x.card ≤ K) (u : U₀) :
    |incidenceVector G U₀ x u| ≤ (K : ℤ) := by
  change |(incidence G x u.1 : ℤ)| ≤ (K : ℤ)
  rw [abs_of_nonneg (by positivity)]
  exact_mod_cast (incidence_le_card G x u.1).trans hxK

/-- The difference of two `[0,K]` incidence coordinates has absolute value
at most `K`. -/
lemma abs_incidenceVector_sub_le_of_card_le
    (G : SimpleGraph V) (U₀ x y : Finset V) (K : ℕ)
    (hxK : x.card ≤ K) (hyK : y.card ≤ K) (u : U₀) :
    |incidenceVector G U₀ x u - incidenceVector G U₀ y u| ≤ (K : ℤ) := by
  have hx0 : (0 : ℤ) ≤ incidenceVector G U₀ x u := by
    simp [incidenceVector]
  have hy0 : (0 : ℤ) ≤ incidenceVector G U₀ y u := by
    simp [incidenceVector]
  have hx := abs_incidenceVector_le_of_card_le G U₀ x K hxK u
  have hy := abs_incidenceVector_le_of_card_le G U₀ y K hyK u
  rw [abs_of_nonneg hx0] at hx
  rw [abs_of_nonneg hy0] at hy
  rw [abs_le]
  omega

/-- A real coefficient sum on the selected coordinates of a Boolean slice. -/
def sliceSum {I : Type*} [Fintype I] [DecidableEq I]
    (ell : ℕ) (a : I → ℝ) (omega : BoolSlice I ell) : ℝ :=
  ∑ i ∈ SlicePersistence.sampleFinset ell omega, a i

lemma incidenceSum_eq_sliceSum {I : Type*} [Fintype I] [DecidableEq I]
    (ell : ℕ) (a : I → ℤ) (omega : BoolSlice I ell) :
    AugmentationPartial.incidenceSum ell a omega =
      sliceSum ell (fun i ↦ (a i : ℝ)) omega := by
  classical
  simp only [AugmentationPartial.incidenceSum,
    AntiConcentration.sliceLinear, sliceSum]
  calc
    (∑ i, (a i : ℝ) * if omega.1 i = true then 1 else 0) =
        ∑ i, if i ∈ SlicePersistence.sampleFinset ell omega then
          (a i : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hmem : i ∈ SlicePersistence.sampleFinset ell omega
      · simp [hmem, SlicePersistence.mem_sampleFinset.mp hmem]
      · have hfalse : ¬ omega.1 i := by
          simpa only [SlicePersistence.mem_sampleFinset] using hmem
        simp [hmem, hfalse]
    _ = ∑ i ∈ SlicePersistence.sampleFinset ell omega, (a i : ℝ) := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext i
        simp
      · simp

lemma sliceSum_incidenceVector_eq_degreeInto_sampleFinset
    (G : SimpleGraph V) (U₀ x : Finset V) (s : ℕ)
    (omega : BoolSlice U₀ s) :
    sliceSum s (fun u : U₀ ↦ (incidenceVector G U₀ x u : ℝ)) omega =
      degreeInto G (sampleFinset U₀ s omega) x := by
  classical
  simp only [sliceSum, sampleFinset, mapSubtypeFinset, incidenceVector,
    incidence, degreeInto, Erdos88.neighborsIn, Finset.card_filter]
  push_cast
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.sum_map]
  rfl

lemma incidenceSum_incidenceVector_eq_degreeInto_sampleFinset
    (G : SimpleGraph V) (U₀ x : Finset V) (s : ℕ)
    (omega : BoolSlice U₀ s) :
    AugmentationPartial.incidenceSum s (incidenceVector G U₀ x) omega =
      degreeInto G (sampleFinset U₀ s omega) x := by
  rw [incidenceSum_eq_sliceSum,
    sliceSum_incidenceVector_eq_degreeInto_sampleFinset]

lemma sliceSum_abs_incidenceVector_sub_eq_incidenceDiffMass_sampleFinset
    (G : SimpleGraph V) (U₀ x y : Finset V) (s : ℕ)
    (omega : BoolSlice U₀ s) :
    sliceSum s (fun u : U₀ ↦
        |(((incidenceVector G U₀ x u - incidenceVector G U₀ y u : ℤ) : ℝ))|)
        omega =
      incidenceDiffMass G (sampleFinset U₀ s omega) x y := by
  classical
  simp only [sliceSum, sampleFinset, mapSubtypeFinset, incidenceVector,
    incidenceDiffMass]
  push_cast
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro u hu
  simp [incidenceDiffTerm]

section OneBucketLinear

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Exact first moment of a coefficient sum on a Boolean slice. -/
theorem uniformExpectation_sliceSum [Nonempty I]
    (ell : ℕ) (hell : ell ≤ Fintype.card I) (a : I → ℝ)
    [Nonempty (BoolSlice I ell)] :
    uniformExpectation (sliceSum ell a) =
      (ell : ℝ) / Fintype.card I * ∑ i, a i := by
  let E := SlicePersistence.boolSliceEquivBooleanSlicePoint
    (V := I) ell
  let f : Erdos88.BooleanSlices.BooleanSlicePoint
      (Finset.univ : Finset I) ell → ℝ := fun D ↦ ∑ i ∈ D.1, a i
  letI : Nonempty
      (Erdos88.BooleanSlices.BooleanSlicePoint
        (Finset.univ : Finset I) ell) :=
    SliceMoments.nonempty_booleanSlicePoint Finset.univ ell (by simpa using hell)
  have hpoint (omega : BoolSlice I ell) : sliceSum ell a omega = f (E omega) := by
    rfl
  have hmean : uniformExpectation (sliceSum ell a) = uniformExpectation f := by
    have hfun : sliceSum ell a = fun omega ↦ f (E omega) := by
      funext omega
      exact hpoint omega
    rw [hfun]
    exact SlicePersistence.uniformExpectation_equiv E f
  have h := SliceMoments.expectation_sum_booleanSlicePoint
    (Finset.univ : Finset I) ell a (by simpa using hell)
      (Finset.univ_nonempty : (Finset.univ : Finset I).Nonempty)
  rw [Fintype.expect_eq_sum_div_card] at h
  rw [hmean]
  simpa [f, uniformExpectation] using h

/-- The one-bucket signed statistic is the ordinary sum over the selected
Boolean-slice coordinates. -/
lemma productLinear_boolSliceEquivOneBucketSigned
    (ell : ℕ) (hell : ell ≤ Fintype.card I) (a : I → ℝ)
    (omega : BoolSlice I ell) :
    AugmentationPartial.productLinear (SlicePersistence.oneBucket I) a
        (SlicePersistence.boolSliceEquivOneBucketSigned ell hell omega) =
      sliceSum ell a omega := by
  classical
  simp only [AugmentationPartial.productLinear, sliceSum]
  have hvalue (i : I) :
      Erdos88.BooleanSlices.productSignedSliceValue
          (SlicePersistence.oneBucket I)
          (SlicePersistence.boolSliceEquivOneBucketSigned ell hell omega) i =
        if i ∈ SlicePersistence.sampleFinset ell omega then 1 else 0 := by
    change (if i ∈ SlicePersistence.sampleFinset ell omega then 1
      else if i ∈ (∅ : Finset I) then -1 else 0) =
        if i ∈ SlicePersistence.sampleFinset ell omega then 1 else 0
    simp
  calc
    (∑ i, a i * Erdos88.BooleanSlices.productSignedSliceValue
        (SlicePersistence.oneBucket I)
        (SlicePersistence.boolSliceEquivOneBucketSigned ell hell omega) i) =
        ∑ i, if i ∈ SlicePersistence.sampleFinset ell omega then a i else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hvalue]
      split_ifs <;> ring
    _ = ∑ i ∈ SlicePersistence.sampleFinset ell omega, a i := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext i
        simp
      · simp

/-- Two-sided bounded-difference concentration for a bounded coefficient
sum on an ordinary uniform fixed-cardinality slice. -/
theorem boolSlice_sum_two_sided_probability
    (ell : ℕ) (hell : ell ≤ Fintype.card I) (hellPos : 0 < ell)
    (a : I → ℝ) (B t : ℝ) (hB : 0 < B) (ht : 0 ≤ t)
    (hbounded : ∀ i, |a i| ≤ B) [Nonempty (BoolSlice I ell)] :
    uniformProbability (fun omega : BoolSlice I ell ↦
        t ≤ |sliceSum ell a omega - uniformExpectation (sliceSum ell a)|) ≤
      2 * Real.exp (-t ^ 2 / (2 * ell * (4 * B) ^ 2)) := by
  classical
  let P := SlicePersistence.oneBucket I
  let plus : Fin 1 → ℕ := fun _ ↦ ell
  let minus : Fin 1 → ℕ := fun _ ↦ 0
  let E := SlicePersistence.boolSliceEquivOneBucketSigned
    (V := I) ell hell
  letI : Nonempty
      (Erdos88.BooleanSlices.ProductSignedSlicePoint P plus minus) :=
    ⟨E (Classical.choice (inferInstance : Nonempty (BoolSlice I ell)))⟩
  let e : ∀ k : Fin 1, Fin (P.fiber k).card ≃ ↑(P.fiber k) :=
    fun k ↦ by
      simpa only [Fintype.card_coe] using
        (Fintype.equivFin ↑(P.fiber k)).symm
  have hcount : ∀ k, plus k + minus k ≤ (P.fiber k).card := by
    intro k
    simpa [P, plus, minus, SlicePersistence.oneBucket_fiber] using hell
  have htail := AugmentationPartial.productLinear_two_sided_probability
    P plus minus hcount e a B t (by simpa [plus, minus] using hellPos)
      hB ht hbounded
  have hstat (omega : BoolSlice I ell) :
      AugmentationPartial.productLinear (plus := plus) (minus := minus)
          P a (E omega) =
        sliceSum ell a omega := by
    simpa [P, E] using
      productLinear_boolSliceEquivOneBucketSigned ell hell a omega
  have hmean : uniformExpectation
      (AugmentationPartial.productLinear (plus := plus) (minus := minus) P a) =
        uniformExpectation (sliceSum ell a) := by
    rw [← SlicePersistence.uniformExpectation_equiv E
      (AugmentationPartial.productLinear (plus := plus) (minus := minus) P a)]
    apply congrArg uniformExpectation
    funext omega
    exact hstat omega
  let Q := fun S : Erdos88.BooleanSlices.ProductSignedSlicePoint P plus minus ↦
    t ≤ |AugmentationPartial.productLinear (plus := plus) (minus := minus)
        P a S -
      uniformExpectation (sliceSum ell a)|
  have hprob : uniformProbability (fun omega : BoolSlice I ell ↦
      t ≤ |sliceSum ell a omega - uniformExpectation (sliceSum ell a)|) =
      uniformProbability Q := by
    have hevent : (fun omega : BoolSlice I ell ↦
        t ≤ |sliceSum ell a omega - uniformExpectation (sliceSum ell a)|) =
        fun omega ↦ Q (E omega) := by
      funext omega
      simp only [Q, hstat]
    rw [hevent]
    exact SlicePersistence.uniformProbability_equiv E Q
  rw [hprob]
  rw [hmean] at htail
  simpa [Q, plus, minus] using htail

end OneBucketLinear

/-! ## Graph instantiation of Claim 4.8 -/

/-- The explicit Azuma--Hoeffding failure bound for one diversity or degree
test on the outer `2 n_D`-slice. -/
def outerLinearFailure (nD K : ℕ) (t : ℝ) : ℝ :=
  2 * Real.exp (-t ^ 2 / (2 * (2 * nD) * (4 * K) ^ 2))

/-- **Graph-specific balanced partial exposure (Kwan--Sudakov Claim 4.8).**

The hypotheses are exactly finite graph data.  In particular, the two
probability estimates passed to the abstract selector are proved here from
bounded incidence coordinates, equal reservoir degrees, and pairwise
incidence diversity.  The only numerical premise is the displayed explicit
four-term budget; in the final assembly it is discharged after choosing the
fixed constants and increasing the natural threshold.

The conclusion is a probability statement on actual ambient `2 n_D`-sets,
not merely an existential choice of one set. -/
theorem three_fourths_le_layerProbability_partialGood_thresholds
    (G : SimpleGraph V) (U₀ : Finset V) (M : Finset (Finset V))
    (K nD s₀ d₀ : ℕ) (c theta divDev degreeDev : ℝ)
    (tS tX tCollision : ℝ)
    (hnD : 0 < nD) (hK : 1 ≤ K)
    (hfeasible : 2 * nD ≤ U₀.card)
    (hfamilies : 2 * s₀ ≤ M.card)
    (hcell : ∀ x ∈ M, x.card ≤ K)
    (hdegree₀ : ∀ x ∈ M, degreeInto G U₀ x = d₀)
    (hdiversity : ∀ x ∈ M, ∀ y ∈ M, x ≠ y →
      theta * U₀.card ≤ incidenceDiffMass G U₀ x y)
    (hc₀ : 0 < c) (hc₁ : c ≤ 1 / 2) (htheta : 0 < theta)
    (hselected : c * U₀.card ≤ ((2 * nD : ℕ) : ℝ))
    (hunselected : c * U₀.card ≤ ((U₀.card - 2 * nD : ℕ) : ℝ))
    (hdivDev : 0 < divDev) (hdegreeDev : 0 < degreeDev)
    (htS : 0 < tS) (htX : 0 < tX) (htCollision : 0 < tCollision)
    (hbudget :
      let pDiv := outerLinearFailure nD K divDev
      let pDegree := outerLinearFailure nD K degreeDev
      let pCollision :=
        AntiConcentration.variancePointMassConstant
            c (theta ^ 2 / 4) (2 * K) /
          Real.sqrt (U₀.card : ℝ)
      s₀.choose 2 * pDiv +
          s₀ * pDegree / tS +
          s₀ * pDegree / tX +
          s₀.choose 2 * pCollision / tCollision ≤ 1 / 4) :
    3 / 4 ≤ NestedUniform.layerProbability U₀ (2 * nD)
      (PartialGood G M s₀
        ((2 * nD : ℕ) * theta - divDev)
        (((2 * nD : ℕ) : ℝ) / U₀.card * d₀)
        degreeDev tS tX tCollision) := by
  classical
  have hU₀pos : 0 < U₀.card := by omega
  letI : Nonempty U₀ := by
    obtain ⟨u, hu⟩ := Finset.card_pos.mp hU₀pos
    exact ⟨⟨u, hu⟩⟩
  letI : LinearOrder (Finset V) := cellLinearOrder
  letI : Nonempty
      (Erdos88.BooleanSlices.BooleanSlicePoint U₀ (2 * nD)) :=
    SliceMoments.nonempty_booleanSlicePoint U₀ (2 * nD) hfeasible
  let E := boolSliceEquivBooleanSlicePoint U₀ (2 * nD)
  letI : Nonempty (BoolSlice U₀ (2 * nD)) :=
    E.nonempty_congr.mpr inferInstance
  obtain ⟨S₀, X₀, hS₀M, hX₀M, hS₀card, hX₀card, hdisjoint⟩ :=
    exists_two_disjoint_subsets_card_eq M s₀ hfamilies
  let diversityThreshold : ℝ := ((2 * nD : ℕ) : ℝ) * theta - divDev
  let center : ℝ := ((2 * nD : ℕ) : ℝ) / U₀.card * d₀
  let diverse : Finset V → Finset V → BoolSlice U₀ (2 * nD) → Prop :=
    fun x y omega ↦ diversityThreshold ≤
      incidenceDiffMass G (sampleFinset U₀ (2 * nD) omega) x y
  let degreeGood : Finset V → BoolSlice U₀ (2 * nD) → Prop :=
    fun x omega ↦ DegreeGood G (sampleFinset U₀ (2 * nD) omega)
      x center degreeDev
  let pDiv := outerLinearFailure nD K divDev
  let pDegree := outerLinearFailure nD K degreeDev
  -- The preceding total boundedness is awkward outside `M`; use a
  -- coefficient vector which is explicitly zero there.
  let aM : Finset V → U₀ → ℤ := fun x u ↦
    if x ∈ M then incidenceVector G U₀ x u else 0
  have haM_on {x : Finset V} (hx : x ∈ M) : aM x = incidenceVector G U₀ x := by
    funext u
    simp [aM, hx]
  have haMbounded : ∀ q : Finset V, ∀ u : U₀, |aM q u| ≤ (K : ℤ) := by
    intro q u
    by_cases hq : q ∈ M
    · rw [haM_on hq]
      exact abs_incidenceVector_le_of_card_le G U₀ q K (hcell q hq) u
    · simp [aM, hq]
  have hequal : ∀ i ∈ S₀, ∀ j ∈ S₀, i ≠ j →
      ∑ u, aM i u = ∑ u, aM j u := by
    intro i hi j hj _hij
    rw [haM_on (hS₀M hi), haM_on (hS₀M hj),
      sum_incidenceVector_eq_degreeInto,
      sum_incidenceVector_eq_degreeInto,
      hdegree₀ i (hS₀M hi), hdegree₀ j (hS₀M hj)]
  have hlone : ∀ i ∈ S₀, ∀ j ∈ S₀, i ≠ j →
      theta * Fintype.card U₀ ≤
        ∑ u, |(((aM i u - aM j u : ℤ) : ℝ))| := by
    intro i hi j hj hij
    rw [haM_on (hS₀M hi), haM_on (hS₀M hj),
      sum_abs_incidenceVector_sub_eq_incidenceDiffMass]
    simpa using hdiversity i (hS₀M hi) j (hS₀M hj) hij
  have hdiverseProb : ∀ i ∈ X₀, ∀ j ∈ X₀, i ≠ j →
      uniformProbability (fun omega ↦ ¬ diverse i j omega) ≤ pDiv := by
    intro i hi j hj hij
    let q : U₀ → ℝ := fun u ↦
      |(((incidenceVector G U₀ i u - incidenceVector G U₀ j u : ℤ) : ℝ))|
    have hqbound : ∀ u, |q u| ≤ (K : ℝ) := by
      intro u
      rw [abs_of_nonneg (abs_nonneg _)]
      exact_mod_cast abs_incidenceVector_sub_le_of_card_le G U₀ i j K
        (hcell i (hX₀M hi)) (hcell j (hX₀M hj)) u
    have htail := boolSlice_sum_two_sided_probability
      (I := U₀) (2 * nD) (by simpa using hfeasible) (by omega)
      q K divDev (by exact_mod_cast hK) hdivDev.le hqbound
    have hmean : ((2 * nD : ℕ) : ℝ) * theta ≤
        uniformExpectation (sliceSum (2 * nD) q) := by
      rw [uniformExpectation_sliceSum (2 * nD)
        (by simpa using hfeasible) q]
      have hmass : theta * Fintype.card U₀ ≤ ∑ u, q u := by
        dsimp only [q]
        rw [sum_abs_incidenceVector_sub_eq_incidenceDiffMass]
        simpa using hdiversity i (hX₀M hi) j (hX₀M hj) hij
      have hcardReal : (0 : ℝ) < Fintype.card U₀ := by positivity
      calc
        ((2 * nD : ℕ) : ℝ) * theta =
            ((2 * nD : ℕ) : ℝ) / Fintype.card U₀ *
              (theta * Fintype.card U₀) := by field_simp
        _ ≤ ((2 * nD : ℕ) : ℝ) / Fintype.card U₀ * ∑ u, q u := by
          gcongr
    calc
      uniformProbability (fun omega ↦ ¬ diverse i j omega) ≤
          uniformProbability (fun omega ↦ divDev ≤
            |sliceSum (2 * nD) q omega -
              uniformExpectation (sliceSum (2 * nD) q)|) := by
        apply uniformProbability_mono
        intro omega hbad
        have hsample : sliceSum (2 * nD) q omega =
            incidenceDiffMass G (sampleFinset U₀ (2 * nD) omega) i j :=
          sliceSum_abs_incidenceVector_sub_eq_incidenceDiffMass_sampleFinset
            G U₀ i j (2 * nD) omega
        have hsmall : sliceSum (2 * nD) q omega < diversityThreshold := by
          rw [hsample]
          exact lt_of_not_ge hbad
        have hgap : divDev ≤
            uniformExpectation (sliceSum (2 * nD) q) -
              sliceSum (2 * nD) q omega := by
          dsimp only [diversityThreshold] at hsmall
          linarith
        exact hgap.trans (by
          simpa only [neg_sub] using
            (neg_le_abs (sliceSum (2 * nD) q omega -
              uniformExpectation (sliceSum (2 * nD) q))))
      _ ≤ pDiv := by simpa [pDiv, outerLinearFailure] using htail
  have hdegreeProb : ∀ i ∈ S₀ ∪ X₀,
      uniformProbability (fun omega ↦ ¬ degreeGood i omega) ≤ pDegree := by
    intro i hi
    have hiM : i ∈ M := by
      rcases Finset.mem_union.mp hi with hiS | hiX
      · exact hS₀M hiS
      · exact hX₀M hiX
    let q : U₀ → ℝ := fun u ↦ incidence G i u.1
    have hqbound : ∀ u, |q u| ≤ (K : ℝ) := by
      intro u
      change |(incidence G i u.1 : ℝ)| ≤ (K : ℝ)
      rw [abs_of_nonneg (by positivity)]
      exact_mod_cast (incidence_le_card G i u.1).trans (hcell i hiM)
    have htail := boolSlice_sum_two_sided_probability
      (I := U₀) (2 * nD) (by simpa using hfeasible) (by omega)
      q K degreeDev (by exact_mod_cast hK) hdegreeDev.le hqbound
    have hmean : uniformExpectation (sliceSum (2 * nD) q) = center := by
      rw [uniformExpectation_sliceSum (2 * nD)
        (by simpa using hfeasible) q]
      have hsum : ∑ u, q u = d₀ := by
        dsimp only [q]
        have hz := sum_incidenceVector_eq_degreeInto G U₀ i
        rw [hdegree₀ i hiM] at hz
        have hz' : ∑ u : U₀, (incidence G i u.1 : ℤ) = (d₀ : ℤ) := by
          simpa [incidenceVector] using hz
        exact_mod_cast hz'
      rw [hsum]
      simp [center]
    calc
      uniformProbability (fun omega ↦ ¬ degreeGood i omega) ≤
          uniformProbability (fun omega ↦ degreeDev ≤
            |sliceSum (2 * nD) q omega -
              uniformExpectation (sliceSum (2 * nD) q)|) := by
        apply uniformProbability_mono
        intro omega hbad
        have hsample : sliceSum (2 * nD) q omega =
            degreeInto G (sampleFinset U₀ (2 * nD) omega) i := by
          simpa [q, incidenceVector] using
            sliceSum_incidenceVector_eq_degreeInto_sampleFinset
              G U₀ i (2 * nD) omega
        rw [hmean, hsample]
        exact (not_le.mp hbad).le
      _ ≤ pDegree := by simpa [pDegree, outerLinearFailure] using htail
  have hsymm : ∀ i j omega, diverse i j omega ↔ diverse j i omega := by
    intro i j omega
    dsimp only [diverse]
    rw [incidenceDiffMass_comm G
      (sampleFinset U₀ (2 * nD) omega) i j]
  have hraw₀ :=
    AugmentationPartial.one_sub_incidence_budget_le_partialExposure_probability
      S₀ X₀ hdisjoint aM K (2 * nD) c theta hc₀ hc₁ htheta hK
      (by simpa using hU₀pos) haMbounded hequal hlone
      (by simpa using hselected) (by
        calc
          c * (Fintype.card U₀ : ℝ) ≤ ((U₀.card - 2 * nD : ℕ) : ℝ) := by
            simpa using hunselected
          _ = (Fintype.card U₀ : ℝ) - ((2 * nD : ℕ) : ℝ) := by
            rw [Nat.cast_sub hfeasible]
            simp)
      diverse degreeGood pDiv pDegree tS tX tCollision
      htS htX htCollision hdiverseProb (by
        intro i hi
        apply hdegreeProb i
        simpa only [Finset.mem_union] using hi) hsymm
  have hraw : 3 / 4 ≤ uniformProbability
      (fun omega : BoolSlice U₀ (2 * nD) ↦
        (∀ i ∈ X₀, ∀ j ∈ X₀, i ≠ j → diverse i j omega) ∧
        ((S₀.filter fun i ↦ ¬ degreeGood i omega).card : ℝ) < tS ∧
        ((X₀.filter fun i ↦ ¬ degreeGood i omega).card : ℝ) < tX ∧
        ((CollisionCounting.collisionEdges S₀
          (fun i omega ↦ AugmentationPartial.incidenceSum
            (2 * nD) (aM i) omega) omega).card : ℝ) < tCollision) := by
    apply le_trans (show 3 / 4 ≤ 1 -
      (X₀.card.choose 2 * pDiv +
        S₀.card * pDegree / tS +
        X₀.card * pDegree / tX +
        S₀.card.choose 2 *
          (AntiConcentration.variancePointMassConstant
              c (theta ^ 2 / 4) (2 * K) /
            Real.sqrt (Fintype.card U₀ : ℝ)) / tCollision) by
        have hb : X₀.card.choose 2 * pDiv +
            S₀.card * pDegree / tS +
            X₀.card * pDegree / tX +
            S₀.card.choose 2 *
              (AntiConcentration.variancePointMassConstant
                  c (theta ^ 2 / 4) (2 * K) /
                Real.sqrt (Fintype.card U₀ : ℝ)) / tCollision ≤ 1 / 4 := by
          simpa [hS₀card, hX₀card, pDiv, pDegree] using hbudget
        linarith)
    simpa using hraw₀
  have hdecoded : 3 / 4 ≤ uniformProbability
      (fun omega : BoolSlice U₀ (2 * nD) ↦
        PartialGood G M s₀ diversityThreshold center degreeDev
          tS tX tCollision
          (sampleFinset U₀ (2 * nD) omega)) := by
    apply hraw.trans
    apply uniformProbability_mono
    intro omega hgood
    rcases hgood with ⟨hdiv, hbadS, hbadX, hcoll⟩
    refine ⟨S₀, X₀, hS₀M, hX₀M, hS₀card, hX₀card, hdisjoint,
      hdiv, hbadS, hbadX, ?_⟩
    have hvalue (x : Finset V) (hx : x ∈ S₀) :
        AugmentationPartial.incidenceSum (2 * nD) (aM x) omega =
          degreeInto G (sampleFinset U₀ (2 * nD) omega) x := by
      rw [haM_on (hS₀M hx)]
      exact incidenceSum_incidenceVector_eq_degreeInto_sampleFinset
        G U₀ x (2 * nD) omega
    have hedge : cellCollisionEdges S₀
        (degreeInto G (sampleFinset U₀ (2 * nD) omega)) =
        CollisionCounting.collisionEdges S₀
          (fun x omega ↦ AugmentationPartial.incidenceSum
            (2 * nD) (aM x) omega) omega := by
      rw [cellCollisionEdges]
      ext ij
      rcases ij with ⟨i, j⟩
      simp only [CollisionCounting.mem_collisionEdges]
      constructor
      · rintro ⟨hi, hj, hne, hlt, heq⟩
        refine ⟨hi, hj, hne, hlt, ?_⟩
        calc
          AugmentationPartial.incidenceSum (2 * nD) (aM i) omega =
              degreeInto G (sampleFinset U₀ (2 * nD) omega) i := hvalue i hi
          _ = degreeInto G (sampleFinset U₀ (2 * nD) omega) j := by
            exact_mod_cast heq
          _ = AugmentationPartial.incidenceSum (2 * nD) (aM j) omega :=
            (hvalue j hj).symm
      · rintro ⟨hi, hj, hne, hlt, heq⟩
        refine ⟨hi, hj, hne, hlt, ?_⟩
        apply Nat.cast_injective (R := ℝ)
        calc
          (degreeInto G (sampleFinset U₀ (2 * nD) omega) i : ℝ) =
              AugmentationPartial.incidenceSum (2 * nD) (aM i) omega :=
            (hvalue i hi).symm
          _ = AugmentationPartial.incidenceSum (2 * nD) (aM j) omega := heq
          _ = degreeInto G (sampleFinset U₀ (2 * nD) omega) j := hvalue j hj
    rw [hedge]
    exact hcoll
  rw [uniformProbability_sampleFinset_eq_layerProbability] at hdecoded
  simpa [diversityThreshold, center] using hdecoded

/-- Structural-witness specialization.  All graph-theoretic incidence,
uniformity, and equal-degree hypotheses are discharged by the witness; the
remaining premises are explicit sampling-balance and numerical estimates. -/
theorem three_fourths_le_layerProbability_partialGood_structuralWitness_thresholds
    {scale nW ell K : ℕ} {alpha aDisc aDiv b : ℝ}
    {G : SimpleGraph V}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (nD s₀ : ℕ) (c theta divDev degreeDev : ℝ)
    (tS tX tCollision : ℝ)
    (hnD : 0 < nD)
    (hfeasible : 2 * nD ≤ S.U0.card)
    (hfamilies : 2 * s₀ ≤ S.matching.card)
    (hnormalizedDiversity : theta * S.U0.card ≤ aDiv * scale)
    (hc₀ : 0 < c) (hc₁ : c ≤ 1 / 2) (htheta : 0 < theta)
    (hselected : c * S.U0.card ≤ ((2 * nD : ℕ) : ℝ))
    (hunselected : c * S.U0.card ≤
      ((S.U0.card - 2 * nD : ℕ) : ℝ))
    (hdivDev : 0 < divDev) (hdegreeDev : 0 < degreeDev)
    (htS : 0 < tS) (htX : 0 < tX) (htCollision : 0 < tCollision)
    (hbudget :
      let pDiv := outerLinearFailure nD K divDev
      let pDegree := outerLinearFailure nD K degreeDev
      let pCollision :=
        AntiConcentration.variancePointMassConstant
            c (theta ^ 2 / 4) (2 * K) /
          Real.sqrt (S.U0.card : ℝ)
      s₀.choose 2 * pDiv +
          s₀ * pDegree / tS +
          s₀ * pDegree / tX +
          s₀.choose 2 * pCollision / tCollision ≤ 1 / 4) :
    3 / 4 ≤ NestedUniform.layerProbability S.U0 (2 * nD)
      (PartialGood G S.matching s₀
        ((2 * nD : ℕ) * theta - divDev)
        (((2 * nD : ℕ) : ℝ) / S.U0.card * S.d0)
        degreeDev tS tX tCollision) := by
  apply three_fourths_le_layerProbability_partialGood_thresholds
    G S.U0 S.matching K nD s₀ S.d0 c theta divDev degreeDev
      tS tX tCollision hnD
      (S.k_pos.trans S.k_le)
      hfeasible hfamilies
  · intro x hx
    exact (S.matching_uniform x hx).le.trans S.k_le
  · exact S.degree_U0
  · intro x hx y hy hxy
    exact hnormalizedDiversity.trans (S.diverse x hx y hy hxy)
  · exact hc₀
  · exact hc₁
  · exact htheta
  · exact hselected
  · exact hunselected
  · exact hdivDev
  · exact hdegreeDev
  · exact htS
  · exact htX
  · exact htCollision
  · exact hbudget

/-- Compatibility form with all three exceptional-count thresholds equal to
`sqrt nD`.  Quantitative applications should prefer the threshold-parameterized
theorem above. -/
theorem three_fourths_le_layerProbability_partialGood_structuralWitness
    {scale nW ell K : ℕ} {alpha aDisc aDiv b : ℝ}
    {G : SimpleGraph V}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (nD s₀ : ℕ) (c theta divDev degreeDev : ℝ)
    (hnD : 0 < nD)
    (hfeasible : 2 * nD ≤ S.U0.card)
    (hfamilies : 2 * s₀ ≤ S.matching.card)
    (hnormalizedDiversity : theta * S.U0.card ≤ aDiv * scale)
    (hc₀ : 0 < c) (hc₁ : c ≤ 1 / 2) (htheta : 0 < theta)
    (hselected : c * S.U0.card ≤ ((2 * nD : ℕ) : ℝ))
    (hunselected : c * S.U0.card ≤
      ((S.U0.card - 2 * nD : ℕ) : ℝ))
    (hdivDev : 0 < divDev) (hdegreeDev : 0 < degreeDev)
    (hbudget :
      let pDiv := outerLinearFailure nD K divDev
      let pDegree := outerLinearFailure nD K degreeDev
      let pCollision :=
        AntiConcentration.variancePointMassConstant
            c (theta ^ 2 / 4) (2 * K) /
          Real.sqrt (S.U0.card : ℝ)
      s₀.choose 2 * pDiv +
          s₀ * pDegree / Real.sqrt (nD : ℝ) +
          s₀ * pDegree / Real.sqrt (nD : ℝ) +
          s₀.choose 2 * pCollision / Real.sqrt (nD : ℝ) ≤ 1 / 4) :
    3 / 4 ≤ NestedUniform.layerProbability S.U0 (2 * nD)
      (PartialGood G S.matching s₀
        ((2 * nD : ℕ) * theta - divDev)
        (((2 * nD : ℕ) : ℝ) / S.U0.card * S.d0)
        degreeDev (Real.sqrt nD) (Real.sqrt nD) (Real.sqrt nD)) := by
  apply three_fourths_le_layerProbability_partialGood_structuralWitness_thresholds
    S nD s₀ c theta divDev degreeDev
      (Real.sqrt nD) (Real.sqrt nD) (Real.sqrt nD)
      hnD hfeasible hfamilies hnormalizedDiversity hc₀ hc₁ htheta
      hselected hunselected hdivDev hdegreeDev
  · exact Real.sqrt_pos.2 (by exact_mod_cast hnD)
  · exact Real.sqrt_pos.2 (by exact_mod_cast hnD)
  · exact Real.sqrt_pos.2 (by exact_mod_cast hnD)
  · exact hbudget

end


end AugmentationGraphPartial
end Erdos636
