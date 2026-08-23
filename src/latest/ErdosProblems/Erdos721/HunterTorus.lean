/- leanprover/lean4:v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import ErdosProblems.Erdos721.HunterAnnulus
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.AddCircle

/-!
# The finite-dimensional unit torus used by Hunter

This file packages the centered representative, integer characters, and the
normalized Haar measure on `(R/Z)^D`.  In particular, every continuous
surjective additive homomorphism between these tori preserves the normalized
volume.  This is the measure-theoretic replacement for several coordinate
equidistribution calculations in the paper.
-/

namespace Erdos721.HunterTorus

open Filter Function MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal MeasureTheory NNReal Pointwise Topology

/-- Hunter's `D`-dimensional torus. -/
abbrev Torus (D : ℕ) := Fin D → AddCircle (1 : ℝ)

/-- The centered representative in `[-1/2,1/2)`. -/
noncomputable def centeredCoord (x : AddCircle (1 : ℝ)) : ℝ :=
  (AddCircle.equivIco 1 (-(1 / 2 : ℝ)) x : ℝ)

/-- Coordinatewise centered representative, regarded as a Euclidean vector. -/
noncomputable def centeredLift {D : ℕ} (x : Torus D) :
    EuclideanSpace ℝ (Fin D) :=
  WithLp.toLp 2 fun i ↦ centeredCoord (x i)

/-- Projection of a Euclidean vector to the unit torus. -/
def project {D : ℕ} (x : EuclideanSpace ℝ (Fin D)) : Torus D :=
  fun i ↦ (x i : AddCircle (1 : ℝ))

@[simp] lemma project_zero {D : ℕ} :
    project (0 : EuclideanSpace ℝ (Fin D)) = 0 := by
  rfl

@[simp] lemma project_neg {D : ℕ} (x : EuclideanSpace ℝ (Fin D)) :
    project (-x) = -project x := by
  funext i
  simp [project]

@[simp] lemma project_add {D : ℕ}
    (x y : EuclideanSpace ℝ (Fin D)) :
    project (x + y) = project x + project y := by
  funext i
  simp [project]

@[simp] lemma project_centeredLift {D : ℕ} (x : Torus D) :
    project (centeredLift x) = x := by
  funext i
  exact AddCircle.coe_equivIco

lemma centeredCoord_mem (x : AddCircle (1 : ℝ)) :
    centeredCoord x ∈ Set.Ico (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) :=
  (AddCircle.equivIco 1 (-(1 / 2 : ℝ)) x).2

lemma abs_centeredCoord_le_half (x : AddCircle (1 : ℝ)) :
    |centeredCoord x| ≤ 1 / 2 := by
  have hx := centeredCoord_mem x
  rw [abs_le]
  constructor <;> norm_num at hx ⊢ <;> linarith

lemma centeredLift_project {D : ℕ} (x : EuclideanSpace ℝ (Fin D))
    (hx : ∀ i, x i ∈ Set.Ico (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) :
    centeredLift (project x) = x := by
  ext i
  change centeredCoord ((x i : ℝ) : AddCircle (1 : ℝ)) = x i
  have hi : x i ∈ Set.Ico (-(1 / 2 : ℝ))
      (-(1 / 2 : ℝ) + 1) := by
    convert hx i using 1 <;> norm_num
  exact AddCircle.equivIco_coe_of_mem hi

/-- An integer character of the torus, written additively. -/
def integerDot {D : ℕ} (ξ : Fin D → ℤ) :
    Torus D →+ AddCircle (1 : ℝ) where
  toFun x := ∑ i, (ξ i) • x i
  map_zero' := by simp
  map_add' x y := by
    simp only [Pi.add_apply, zsmul_add, Finset.sum_add_distrib]

@[simp] lemma integerDot_apply {D : ℕ} (ξ : Fin D → ℤ) (x : Torus D) :
    integerDot ξ x = ∑ i, (ξ i) • x i := rfl

lemma continuous_integerDot {D : ℕ} (ξ : Fin D → ℤ) :
    Continuous (integerDot ξ) := by
  change Continuous (fun x : Torus D ↦ ∑ i, (ξ i) • x i)
  fun_prop

/-- A finite family of integer characters. -/
def phaseHom {D m : ℕ} (ξ : Fin m → Fin D → ℤ) :
    Torus D →+ Torus m where
  toFun x j := integerDot (ξ j) x
  map_zero' := by ext; simp
  map_add' x y := by ext; simp [Finset.sum_add_distrib]

@[simp] lemma phaseHom_apply {D m : ℕ} (ξ : Fin m → Fin D → ℤ)
    (x : Torus D) (j : Fin m) :
    phaseHom ξ x j = integerDot (ξ j) x := rfl

lemma continuous_phaseHom {D m : ℕ} (ξ : Fin m → Fin D → ℤ) :
    Continuous (phaseHom ξ) := by
  apply continuous_pi
  intro j
  exact continuous_integerDot (ξ j)

/-- The default product volume on the unit torus has total mass one. -/
lemma volume_univ (D : ℕ) :
    volume (Set.univ : Set (Torus D)) = 1 := by
  rw [volume_pi, Measure.pi_univ]
  simp only [AddCircle.measure_univ, ENNReal.ofReal_one,
    Finset.prod_const_one]

/-- Local normalized-volume instance used in Haar uniqueness arguments. -/
noncomputable def probabilityVolume (D : ℕ) :
    IsProbabilityMeasure (volume : Measure (Torus D)) where
  measure_univ := volume_univ D

/-- A continuous surjective additive torus homomorphism preserves normalized
Haar volume. -/
theorem measurePreserving_of_continuous_surjective {D m : ℕ}
    (f : Torus D →+ Torus m) (hf : Continuous f)
    (hsurj : Surjective f) : MeasurePreserving f := by
  letI : IsProbabilityMeasure (volume : Measure (Torus D)) :=
    probabilityVolume D
  letI : IsProbabilityMeasure (volume : Measure (Torus m)) :=
    probabilityVolume m
  letI : IsProbabilityMeasure (Measure.map f
      (volume : Measure (Torus D))) :=
    Measure.isProbabilityMeasure_map hf.measurable.aemeasurable
  letI : (Measure.map f (volume : Measure (Torus D))).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map_of_isFiniteMeasure
      (volume : Measure (Torus D)) f hf hsurj
  refine ⟨hf.measurable, ?_⟩
  exact Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure
    (Measure.map f (volume : Measure (Torus D)))
    (volume : Measure (Torus m))

theorem measurePreserving_phaseHom {D m : ℕ}
    (ξ : Fin m → Fin D → ℤ) (hsurj : Surjective (phaseHom ξ)) :
    MeasurePreserving (phaseHom ξ) :=
  measurePreserving_of_continuous_surjective (phaseHom ξ)
    (continuous_phaseHom ξ) hsurj

/-- A measure-preserving map cannot decrease the measure of a compact set
when one passes to its image. -/
lemma measure_le_measure_image_of_compact {D m : ℕ}
    {f : Torus D → Torus m} (hf : MeasurePreserving f)
    (hcont : Continuous f)
    {S : Set (Torus D)} (hS : IsCompact S) :
    volume S ≤ volume (f '' S) := by
  rw [← hf.map_eq, Measure.map_apply hf.measurable
    (hS.image hcont).measurableSet]
  exact measure_mono (subset_preimage_image f S)

/-- Coordinate product of closed metric balls around zero. -/
def centeredBox (D : ℕ) (r : ℝ) : Set (Torus D) :=
  Set.pi Set.univ fun _ ↦ Metric.closedBall 0 r

lemma centeredBox_compact (D : ℕ) (r : ℝ) :
    IsCompact (centeredBox D r) := by
  exact isCompact_univ_pi fun _ ↦ isCompact_closedBall _ _

lemma volume_centeredBox {D : ℕ} {r : ℝ} (hr0 : 0 ≤ r)
    (hr : 2 * r ≤ 1) :
    volume (centeredBox D r) = ENNReal.ofReal (2 * r) ^ D := by
  rw [centeredBox, volume_pi_pi]
  simp_rw [AddCircle.volume_closedBall, min_eq_right hr]
  rw [Fin.prod_const]

end Erdos721.HunterTorus
