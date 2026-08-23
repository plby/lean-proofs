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

import ErdosProblems.Erdos989.Upper
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Periodic jittered selections at a fixed radius

This file supplies the exact deterministic link between the finite product used by the
fixed-radius probabilistic construction and the infinite jittered point set.  The essential
fact is that a disk whose diameter is strictly smaller than the period contains at most one
selected cell from each residue class.  Consequently its infinite disk count is literally a
sum of independent one-coordinate indicators on the finite period.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace Erdos989
namespace FixedRadiusUpper

open GlobalSelection

noncomputable section

/-- The selected point in an integer cell for a periodic midpoint-grid assignment. -/
def periodicPoint (L q : ℕ) (ω : PeriodCell L → GridCandidate q)
    (cell : PlaneCell) : Plane :=
  selectedPoint (latticeLocation (midpointOffset q)) (periodicSelection L q ω) cell

@[simp] theorem periodicPoint_apply_zero (L q : ℕ)
    (ω : PeriodCell L → GridCandidate q) (cell : PlaneCell) :
    periodicPoint L q ω cell 0 =
      (cell.1 : ℝ) + (midpointOffset q (ω (periodClass L cell))).1 := by
  rfl

@[simp] theorem periodicPoint_apply_one (L q : ℕ)
    (ω : PeriodCell L → GridCandidate q) (cell : PlaneCell) :
    periodicPoint L q ω cell 1 =
      (cell.2 : ℝ) + (midpointOffset q (ω (periodClass L cell))).2 := by
  rfl

/-- Equality of period classes is coordinatewise congruence modulo the period. -/
theorem periodClass_eq_iff_dvd_sub (L : ℕ) (cell cell' : PlaneCell) :
    periodClass L cell = periodClass L cell' ↔
      (L : ℤ) ∣ cell'.1 - cell.1 ∧ (L : ℤ) ∣ cell'.2 - cell.2 := by
  constructor
  · intro h
    have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    exact ⟨(ZMod.intCast_eq_intCast_iff_dvd_sub cell.1 cell'.1 L).mp hx,
      (ZMod.intCast_eq_intCast_iff_dvd_sub cell.2 cell'.2 L).mp hy⟩
  · rintro ⟨hx, hy⟩
    apply Prod.ext
    · exact (ZMod.intCast_eq_intCast_iff_dvd_sub cell.1 cell'.1 L).mpr hx
    · exact (ZMod.intCast_eq_intCast_iff_dvd_sub cell.2 cell'.2 L).mpr hy

/-- Two points in the same closed disk are at distance at most its diameter. -/
theorem dist_le_two_mul_radius_of_mem_closedBall {p p' center : Plane} {radius : ℝ}
    (hp : p ∈ Metric.closedBall center radius)
    (hp' : p' ∈ Metric.closedBall center radius) :
    dist p p' ≤ 2 * radius := by
  rw [Metric.mem_closedBall] at hp hp'
  calc
    dist p p' ≤ dist p center + dist center p' := dist_triangle _ _ _
    _ = dist p center + dist p' center := by rw [dist_comm center p']
    _ ≤ radius + radius := add_le_add hp hp'
    _ = 2 * radius := by ring

/-- If the period is larger than the disk diameter, reduction modulo the period is injective
on the cells whose periodic selected points lie in that disk. -/
theorem periodClass_injOn_periodicPointsInClosedBall
    {L q : ℕ} {ω : PeriodCell L → GridCandidate q}
    {center : Plane} {radius : ℝ}
    (hperiod : 2 * radius < (L : ℝ)) :
    Set.InjOn (periodClass L)
      {cell | periodicPoint L q ω cell ∈ Metric.closedBall center radius} := by
  intro cell hcell cell' hcell' hclass
  have hdvd := (periodClass_eq_iff_dvd_sub L cell cell').mp hclass
  have hpoints : dist (periodicPoint L q ω cell) (periodicPoint L q ω cell') ≤
      2 * radius := dist_le_two_mul_radius_of_mem_closedBall hcell hcell'
  have hchoice : ω (periodClass L cell) = ω (periodClass L cell') := congrArg ω hclass
  have hx : cell.1 = cell'.1 := by
    by_contra hne
    have hsub : cell'.1 - cell.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have hint : (L : ℤ) ≤ |cell'.1 - cell.1| := Int.le_abs_of_dvd hsub hdvd.1
    have hreal : (L : ℝ) ≤ |(cell'.1 : ℝ) - (cell.1 : ℝ)| := by
      exact_mod_cast hint
    have hcoord :
        |(cell'.1 : ℝ) - (cell.1 : ℝ)| ≤
          dist (periodicPoint L q ω cell) (periodicPoint L q ω cell') := by
      have happ := PiLp.dist_apply_le
        (periodicPoint L q ω cell) (periodicPoint L q ω cell') (0 : Fin 2)
      rw [Real.dist_eq] at happ
      simpa [hchoice, abs_sub_comm] using happ
    linarith
  have hy : cell.2 = cell'.2 := by
    by_contra hne
    have hsub : cell'.2 - cell.2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have hint : (L : ℤ) ≤ |cell'.2 - cell.2| := Int.le_abs_of_dvd hsub hdvd.2
    have hreal : (L : ℝ) ≤ |(cell'.2 : ℝ) - (cell.2 : ℝ)| := by
      exact_mod_cast hint
    have hcoord :
        |(cell'.2 : ℝ) - (cell.2 : ℝ)| ≤
          dist (periodicPoint L q ω cell) (periodicPoint L q ω cell') := by
      have happ := PiLp.dist_apply_le
        (periodicPoint L q ω cell) (periodicPoint L q ω cell') (1 : Fin 2)
      rw [Real.dist_eq] at happ
      simpa [hchoice, abs_sub_comm] using happ
    linarith
  exact Prod.ext hx hy

/-- The finite-product indicator attached to one residue class: it records whether choosing
`u` in that class places one of its periodic copies in the prescribed disk.  The period
assumption used below makes that copy unique, but uniqueness is not needed in the definition. -/
noncomputable def periodHit (L q : ℕ) (center : Plane) (radius : ℝ)
    (i : PeriodCell L) (u : GridCandidate q) : Bool := by
  classical
  exact if ∃ cell : PlaneCell,
    periodClass L cell = i ∧
      latticeLocation (midpointOffset q) cell u ∈ Metric.closedBall center radius
    then true else false

@[simp] theorem periodHit_eq_true_iff (L q : ℕ) (center : Plane) (radius : ℝ)
    (i : PeriodCell L) (u : GridCandidate q) :
    periodHit L q center radius i u = true ↔
      ∃ cell : PlaneCell, periodClass L cell = i ∧
        latticeLocation (midpointOffset q) cell u ∈ Metric.closedBall center radius := by
  classical
  simp [periodHit]

@[simp] theorem periodHit_coe_iff (L q : ℕ) (center : Plane) (radius : ℝ)
    (i : PeriodCell L) (u : GridCandidate q) :
    (periodHit L q center radius i u : Prop) ↔
      ∃ cell : PlaneCell, periodClass L cell = i ∧
        latticeLocation (midpointOffset q) cell u ∈ Metric.closedBall center radius := by
  exact periodHit_eq_true_iff L q center radius i u

/-- The cells selected by a periodic assignment in one disk form a finite set. -/
theorem periodicPointsInClosedBall_finite
    {L q : ℕ} (hq : 0 < q) (ω : PeriodCell L → GridCandidate q)
    (center : Plane) (radius : ℝ) :
    {cell : PlaneCell |
      periodicPoint L q ω cell ∈ Metric.closedBall center radius}.Finite := by
  have hoffset := midpointOffset_in_halfOpenUnitSquare hq
  have hloc : CandidateTableLocallyFinite (latticeLocation (midpointOffset q)) :=
    latticeLocation_candidateTableLocallyFinite fun u ↦
      ⟨(hoffset u).1, (hoffset u).2.1.le,
        (hoffset u).2.2.1, (hoffset u).2.2.2.le⟩
  simpa [periodicPoint] using
    selectedPoint_compact_preimage_finite hloc (periodicSelection L q ω)
      (Metric.closedBall center radius) (isCompact_closedBall center radius)

/-- The residue classes hit by a periodic selection are exactly the image of the selected
integer cells under reduction modulo the period. -/
theorem image_periodClass_periodicPointsInClosedBall
    (L q : ℕ) (ω : PeriodCell L → GridCandidate q)
    (center : Plane) (radius : ℝ) :
    periodClass L ''
        {cell : PlaneCell |
          periodicPoint L q ω cell ∈ Metric.closedBall center radius} =
      {i : PeriodCell L | periodHit L q center radius i (ω i)} := by
  classical
  ext i
  constructor
  · rintro ⟨cell, hcell, rfl⟩
    change periodHit L q center radius (periodClass L cell)
      (ω (periodClass L cell)) = true
    exact (periodHit_eq_true_iff _ _ _ _ _ _).2 ⟨cell, rfl, hcell⟩
  · intro hi
    change periodHit L q center radius i (ω i) = true at hi
    rw [periodHit_eq_true_iff] at hi
    obtain ⟨cell, hclass, hcell⟩ := hi
    refine ⟨cell, ?_, hclass⟩
    simpa [periodicPoint, selectedPoint, periodicSelection, hclass] using hcell

/-- When the disk diameter is below the period, its infinite periodic count is exactly the
sum of one indicator for each coordinate of the finite product probability space. -/
theorem selectedDiskCount_periodic_eq_sum_periodHit
    {L q : ℕ} [NeZero L] (hq : 0 < q) (ω : PeriodCell L → GridCandidate q)
    (center : Plane) (radius : ℝ) (hperiod : 2 * radius < (L : ℝ)) :
    selectedDiskCount (latticeLocation (midpointOffset q))
        (periodicSelection L q ω) center radius =
      ∑ i : PeriodCell L,
        if periodHit L q center radius i (ω i) then 1 else 0 := by
  classical
  let B : Set PlaneCell :=
    {cell | periodicPoint L q ω cell ∈ Metric.closedBall center radius}
  have hBfinite : B.Finite := periodicPointsInClosedBall_finite hq ω center radius
  have hinj : Set.InjOn (periodClass L) B :=
    periodClass_injOn_periodicPointsInClosedBall hperiod
  have hcardImage : B.ncard = (periodClass L '' B).ncard :=
    hinj.bijOn_image.ncard_eq
  have himage : periodClass L '' B =
      {i : PeriodCell L | periodHit L q center radius i (ω i)} := by
    simpa [B] using
      image_periodClass_periodicPointsInClosedBall L q ω center radius
  change B.ncard = _
  rw [hcardImage, himage]
  let H : Set (PeriodCell L) :=
    {i | periodHit L q center radius i (ω i)}
  have hH : H.Finite := Set.toFinite H
  change H.ncard = _
  calc
    H.ncard =
        ((Finset.univ : Finset (PeriodCell L)).filter fun i ↦
          periodHit L q center radius i (ω i) = true).card := by
      rw [Set.ncard_eq_toFinset_card H hH, hH.toFinset_ofPred]
    _ = ∑ i : PeriodCell L,
          if periodHit L q center radius i (ω i) then 1 else 0 := by
      symm
      simpa using
        (Finset.sum_boole (R := ℕ)
          (fun i : PeriodCell L ↦ periodHit L q center radius i (ω i) = true)
          Finset.univ)

/-! ## Active residue classes and boundary cells -/

/-- An integer cell is a midpoint-grid boundary cell if two candidates in that same cell lie
on opposite sides of the disk boundary. -/
def IsMidpointBoundaryCell (q : ℕ) (center : Plane) (radius : ℝ)
    (cell : PlaneCell) : Prop :=
  ∃ u v : GridCandidate q,
    latticeLocation (midpointOffset q) cell u ∈ Metric.closedBall center radius ∧
      latticeLocation (midpointOffset q) cell v ∉ Metric.closedBall center radius

/-- Residue classes whose disk indicator genuinely depends on their candidate. -/
noncomputable def periodActive (L q : ℕ) [NeZero L]
    (center : Plane) (radius : ℝ) : Finset (PeriodCell L) := by
  classical
  exact Finset.univ.filter fun i ↦
    ∃ u v : GridCandidate q,
      periodHit L q center radius i u = true ∧
        periodHit L q center radius i v = false

@[simp] theorem mem_periodActive {L q : ℕ} [NeZero L]
    (center : Plane) (radius : ℝ) (i : PeriodCell L) :
    i ∈ periodActive L q center radius ↔
      ∃ u v : GridCandidate q,
        periodHit L q center radius i u = true ∧
          periodHit L q center radius i v = false := by
  classical
  simp [periodActive]

/-- Outside the active set the hit indicator is independent of the chosen candidate. -/
theorem periodHit_eq_of_not_mem_periodActive
    {L q : ℕ} [NeZero L] {center : Plane} {radius : ℝ}
    {i : PeriodCell L} (hi : i ∉ periodActive L q center radius)
    (u v : GridCandidate q) :
    periodHit L q center radius i u = periodHit L q center radius i v := by
  by_contra hne
  have hactive : ∃ a b : GridCandidate q,
      periodHit L q center radius i a = true ∧
        periodHit L q center radius i b = false := by
    cases hu : periodHit L q center radius i u with
    | false =>
        cases hv : periodHit L q center radius i v with
        | false => exact (hne (hu.trans hv.symm)).elim
        | true => exact ⟨v, u, hv, hu⟩
    | true =>
        cases hv : periodHit L q center radius i v with
        | false => exact ⟨u, v, hu, hv⟩
        | true => exact (hne (hu.trans hv.symm)).elim
  exact hi ((mem_periodActive center radius i).2 hactive)

/-- Every active residue class has a representative integer cell which is cut by the disk
boundary. -/
theorem exists_midpointBoundaryCell_of_mem_periodActive
    {L q : ℕ} [NeZero L] {center : Plane} {radius : ℝ}
    {i : PeriodCell L} (hi : i ∈ periodActive L q center radius) :
    ∃ cell : PlaneCell,
      periodClass L cell = i ∧ IsMidpointBoundaryCell q center radius cell := by
  rcases (mem_periodActive center radius i).1 hi with ⟨u, v, hu, hv⟩
  rw [periodHit_eq_true_iff] at hu
  obtain ⟨cell, hclass, hmem⟩ := hu
  refine ⟨cell, hclass, u, v, hmem, ?_⟩
  intro hmemv
  have hvtrue : periodHit L q center radius i v = true :=
    (periodHit_eq_true_iff _ _ _ _ _ _).2 ⟨cell, hclass, hmemv⟩
  rw [hv] at hvtrue
  exact Bool.noConfusion hvtrue

/-- Midpoint-grid boundary cells are finite: each has at least one candidate in the disk, and
the whole candidate table is locally finite. -/
theorem finite_midpointBoundaryCells {q : ℕ} (hq : 0 < q)
    (center : Plane) (radius : ℝ) :
    {cell : PlaneCell | IsMidpointBoundaryCell q center radius cell}.Finite := by
  have hoffset := midpointOffset_in_halfOpenUnitSquare hq
  have hloc : CandidateTableLocallyFinite (latticeLocation (midpointOffset q)) :=
    latticeLocation_candidateTableLocallyFinite fun u ↦
      ⟨(hoffset u).1, (hoffset u).2.1.le,
        (hoffset u).2.2.1, (hoffset u).2.2.2.le⟩
  apply (hloc center radius).subset
  rintro cell ⟨u, v, hu, hv⟩
  exact ⟨u, hu⟩

/-- Choose a boundary-cell representative of an active residue class. -/
noncomputable def activeBoundaryCell {L q : ℕ} [NeZero L]
    (center : Plane) (radius : ℝ)
    (i : ↥(periodActive L q center radius)) : PlaneCell :=
  Classical.choose (exists_midpointBoundaryCell_of_mem_periodActive i.2)

theorem periodClass_activeBoundaryCell {L q : ℕ} [NeZero L]
    (center : Plane) (radius : ℝ)
    (i : ↥(periodActive L q center radius)) :
    periodClass L (activeBoundaryCell center radius i) = i.1 :=
  (Classical.choose_spec
    (exists_midpointBoundaryCell_of_mem_periodActive i.2)).1

theorem activeBoundaryCell_isBoundary {L q : ℕ} [NeZero L]
    (center : Plane) (radius : ℝ)
    (i : ↥(periodActive L q center radius)) :
    IsMidpointBoundaryCell q center radius (activeBoundaryCell center radius i) :=
  (Classical.choose_spec
    (exists_midpointBoundaryCell_of_mem_periodActive i.2)).2

/-- Distinct active residue classes choose distinct boundary cells, since reducing the chosen
cell modulo the period recovers the original residue class. -/
theorem activeBoundaryCell_injective {L q : ℕ} [NeZero L]
    (center : Plane) (radius : ℝ) :
    Function.Injective
      (activeBoundaryCell (L := L) (q := q) center radius) := by
  intro i j hij
  apply Subtype.ext
  calc
    i.1 = periodClass L (activeBoundaryCell center radius i) :=
      (periodClass_activeBoundaryCell center radius i).symm
    _ = periodClass L (activeBoundaryCell center radius j) := congrArg _ hij
    _ = j.1 := periodClass_activeBoundaryCell center radius j

/-- Hence the number of active coordinates in the finite product is bounded by the number of
midpoint-grid boundary cells in the plane.  A separate geometric area estimate bounds the
latter linearly in the radius. -/
theorem card_periodActive_le_ncard_midpointBoundaryCells
    {L q : ℕ} [NeZero L] (hq : 0 < q)
    (center : Plane) (radius : ℝ) :
    (periodActive L q center radius).card ≤
      Set.ncard {cell : PlaneCell | IsMidpointBoundaryCell q center radius cell} := by
  let B : Set PlaneCell :=
    {cell | IsMidpointBoundaryCell q center radius cell}
  have hBfinite : B.Finite := finite_midpointBoundaryCells hq center radius
  letI : Fintype B := hBfinite.fintype
  let f : ↥(periodActive L q center radius) → B := fun i ↦
    ⟨activeBoundaryCell center radius i,
      activeBoundaryCell_isBoundary center radius i⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact activeBoundaryCell_injective center radius (congrArg Subtype.val hij)
  have hcard := Fintype.card_le_of_injective f hf
  simpa [B] using hcard

/-! ## Removing deterministic coordinates from a centered sum -/

/-- In a difference of two finite sums, coordinates on which the two summands agree may be
discarded. -/
theorem sum_sub_sum_eq_sum_active_of_eq_off
    {I : Type*} [Fintype I] (active : Finset I) (a b : I → ℝ)
    (hoff : ∀ i ∉ active, a i = b i) :
    (∑ i, a i) - ∑ i, b i =
      (∑ i ∈ active, a i) - ∑ i ∈ active, b i := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  symm
  apply Finset.sum_subset (Finset.subset_univ active)
  intro i hi hinot
  rw [hoff i hinot, sub_self]

/-- Hoeffding's inequality for the actual infinite periodic disk count.  Only active residue
classes contribute to the variance proxy; all other coordinates are deterministic and cancel
from the centered sum. -/
theorem periodicDiskCount_hoeffding
    {L q : ℕ} [NeZero L] [NeZero q]
    (center : Plane) (radius t : ℝ)
    (hperiod : 2 * radius < (L : ℝ)) (ht : 0 ≤ t) :
    letI : MeasurableSpace (GridCandidate q) := ⊤
    let ν : PeriodCell L → Measure (GridCandidate q) := fun _ ↦
      (PMF.uniformOfFintype (GridCandidate q)).toMeasure
    let μ : Measure (PeriodCell L → GridCandidate q) := Measure.pi ν
    μ.real {ω | t ≤
        |(selectedDiskCount (latticeLocation (midpointOffset q))
              (periodicSelection L q ω) center radius : ℝ) -
          ∑ i : PeriodCell L,
            ∫ u, (if periodHit L q center radius i u then (1 : ℝ) else 0) ∂ν i|} ≤
      2 * Real.exp
        (-t ^ 2 /
          (2 * (((periodActive L q center radius).card : ℝ) / 4))) := by
  letI : MeasurableSpace (GridCandidate q) := ⊤
  let ν : PeriodCell L → Measure (GridCandidate q) := fun _ ↦
    (PMF.uniformOfFintype (GridCandidate q)).toMeasure
  let μ : Measure (PeriodCell L → GridCandidate q) := Measure.pi ν
  let active : Finset (PeriodCell L) := periodActive L q center radius
  let hit : PeriodCell L → GridCandidate q → Bool :=
    periodHit L q center radius
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hcenter (ω : PeriodCell L → GridCandidate q) :
      (selectedDiskCount (latticeLocation (midpointOffset q))
            (periodicSelection L q ω) center radius : ℝ) -
          ∑ i : PeriodCell L,
            ∫ u, (if hit i u then (1 : ℝ) else 0) ∂ν i =
        (∑ i ∈ active, if hit i (ω i) then (1 : ℝ) else 0) -
          ∑ i ∈ active,
            ∫ u, (if hit i u then (1 : ℝ) else 0) ∂ν i := by
    have hcountNat :=
      selectedDiskCount_periodic_eq_sum_periodHit hq ω center radius hperiod
    have hcountReal :
        (selectedDiskCount (latticeLocation (midpointOffset q))
              (periodicSelection L q ω) center radius : ℝ) =
          ∑ i : PeriodCell L,
            if hit i (ω i) then (1 : ℝ) else 0 := by
      exact_mod_cast hcountNat
    rw [hcountReal]
    apply sum_sub_sum_eq_sum_active_of_eq_off active
    intro i hi
    let u₀ : GridCandidate q := Classical.choice inferInstance
    have hconst (u : GridCandidate q) : hit i u = hit i u₀ := by
      exact periodHit_eq_of_not_mem_periodActive hi u u₀
    have hfun :
        (fun u : GridCandidate q ↦ if hit i u then (1 : ℝ) else 0) =
          fun _ ↦ if hit i u₀ then (1 : ℝ) else 0 := by
      funext u
      rw [hconst u]
    rw [hconst (ω i), hfun]
    simp [ν]
  have hhoeff :=
    finiteProduct_indicator_hoeffding active hit t ht
  simpa only [active, hit, μ, ν, hcenter] using hhoeff

/-- Expected disk count in the finite periodic product, written as a scalar independent of
the local measurable-space notation used by the concentration theorem. -/
noncomputable def periodExpectedDiskCount
    (L q : ℕ) [NeZero L] [NeZero q] (center : Plane) (radius : ℝ) : ℝ := by
  letI : MeasurableSpace (GridCandidate q) := ⊤
  let ν : PeriodCell L → Measure (GridCandidate q) := fun _ ↦
    (PMF.uniformOfFintype (GridCandidate q)).toMeasure
  exact ∑ i : PeriodCell L,
    ∫ u, (if periodHit L q center radius i u then (1 : ℝ) else 0) ∂ν i

/-- The mean of a Boolean indicator under the uniform law on a nonempty finite type is its
fraction of successful values. -/
theorem integral_uniformOfFintype_boolIndicator
    {Q : Type*} [Fintype Q] [Nonempty Q] (hit : Q → Bool) :
    letI : MeasurableSpace Q := ⊤
    ∫ u, (if hit u then (1 : ℝ) else 0)
        ∂(PMF.uniformOfFintype Q).toMeasure =
      (((Finset.univ : Finset Q).filter fun u ↦ hit u = true).card : ℝ) /
        Fintype.card Q := by
  letI : MeasurableSpace Q := ⊤
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul]
  rw [← Finset.mul_sum, Finset.sum_boole]
  simp [div_eq_mul_inv, mul_comm]

/-- The concentration bound with the expectation packaged as `periodExpectedDiskCount`. -/
theorem periodicDiskCount_hoeffding_expected
    {L q : ℕ} [NeZero L] [NeZero q]
    (center : Plane) (radius t : ℝ)
    (hperiod : 2 * radius < (L : ℝ)) (ht : 0 ≤ t) :
    letI : MeasurableSpace (GridCandidate q) := ⊤
    let ν : PeriodCell L → Measure (GridCandidate q) := fun _ ↦
      (PMF.uniformOfFintype (GridCandidate q)).toMeasure
    let μ : Measure (PeriodCell L → GridCandidate q) := Measure.pi ν
    μ.real {ω | t ≤
        |(selectedDiskCount (latticeLocation (midpointOffset q))
              (periodicSelection L q ω) center radius : ℝ) -
          periodExpectedDiskCount L q center radius|} ≤
      2 * Real.exp
        (-t ^ 2 /
          (2 * (((periodActive L q center radius).card : ℝ) / 4))) := by
  simpa only [periodExpectedDiskCount] using
    periodicDiskCount_hoeffding center radius t hperiod ht

/-- A finite union bound turns the pointwise periodic Hoeffding estimates into one assignment
which simultaneously controls any prescribed finite family of disks. -/
theorem exists_periodicSelection_with_finite_deviation_bounds
    {L q : ℕ} [NeZero L] [NeZero q]
    {E : Type*} [Fintype E]
    (center : E → Plane) (radius threshold : E → ℝ)
    (hperiod : ∀ e, 2 * radius e < (L : ℝ))
    (hthreshold : ∀ e, 0 ≤ threshold e)
    (hsum :
      (∑ e : E,
        2 * Real.exp
          (-(threshold e) ^ 2 /
            (2 * (((periodActive L q (center e) (radius e)).card : ℝ) / 4)))) < 1) :
    ∃ ω : PeriodCell L → GridCandidate q, ∀ e,
      |(selectedDiskCount (latticeLocation (midpointOffset q))
            (periodicSelection L q ω) (center e) (radius e) : ℝ) -
        periodExpectedDiskCount L q (center e) (radius e)| < threshold e := by
  letI : MeasurableSpace (GridCandidate q) := ⊤
  let ν : PeriodCell L → Measure (GridCandidate q) := fun _ ↦
    (PMF.uniformOfFintype (GridCandidate q)).toMeasure
  let μ : Measure (PeriodCell L → GridCandidate q) := Measure.pi ν
  let bad : E → Set (PeriodCell L → GridCandidate q) := fun e ↦
    {ω | threshold e ≤
      |(selectedDiskCount (latticeLocation (midpointOffset q))
            (periodicSelection L q ω) (center e) (radius e) : ℝ) -
        periodExpectedDiskCount L q (center e) (radius e)|}
  let p : E → ℝ := fun e ↦
    2 * Real.exp
      (-(threshold e) ^ 2 /
        (2 * (((periodActive L q (center e) (radius e)).card : ℝ) / 4)))
  have hbad : ∀ e, μ.real (bad e) ≤ p e := by
    intro e
    simpa only [μ, ν, bad, p] using
      periodicDiskCount_hoeffding_expected (center e) (radius e) (threshold e)
        (hperiod e) (hthreshold e)
  obtain ⟨ω, hω⟩ := exists_avoiding_finite_events μ bad p hbad (by simpa [p] using hsum)
  refine ⟨ω, fun e ↦ ?_⟩
  have he := hω e
  simpa only [bad, Set.mem_setOf_eq, not_le] using he

end

end FixedRadiusUpper
end Erdos989
