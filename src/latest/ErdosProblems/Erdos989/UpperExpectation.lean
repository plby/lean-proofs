/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos989.UpperPeriodic
import ErdosProblems.Erdos989.UpperQuadrature

/-!
# Identifying the periodic-product expectation with midpoint quadrature

When the period exceeds the disk diameter, a fixed candidate in a fixed residue class has at
most one periodic copy in the disk.  Thus residue-class/candidate hits are in bijection with all
midpoint-grid candidates in the disk.  This identifies the product expectation with the
normalized midpoint-grid count, to which `midpoint_grid_disk_quadrature` applies.
-/

namespace Erdos989
namespace FixedRadiusUpper

noncomputable section

open MeasureTheory Real Set
open GlobalSelection

/-- Reduction modulo the period, together with the unchanged candidate, is injective on all
candidate midpoints in a disk whose diameter is smaller than the period. -/
theorem periodClass_prod_injOn_candidateMidpointHitSet
    {L q : ℕ} [NeZero L] {center : Plane} {radius : ℝ}
    (hperiod : 2 * radius < (L : ℝ)) :
    Set.InjOn (fun a : PlaneCell × GridCandidate q ↦ (periodClass L a.1, a.2))
      (candidateMidpointHitSet q center radius) := by
  rintro ⟨cell, u⟩ hcell ⟨cell', u'⟩ hcell' heq
  have hclass : periodClass L cell = periodClass L cell' := congrArg Prod.fst heq
  have hu : u = u' := congrArg Prod.snd heq
  let ω : PeriodCell L → GridCandidate q := fun _ ↦ u
  have hcellPeriodic :
      periodicPoint L q ω cell ∈ Metric.closedBall center radius := by
    simpa [candidateMidpointHitSet, periodicPoint, selectedPoint,
      periodicSelection, ω] using hcell
  have hcell'Periodic :
      periodicPoint L q ω cell' ∈ Metric.closedBall center radius := by
    simpa [candidateMidpointHitSet, periodicPoint, selectedPoint,
      periodicSelection, ω, hu] using hcell'
  have hcells : cell = cell' :=
    periodClass_injOn_periodicPointsInClosedBall hperiod
      hcellPeriodic hcell'Periodic hclass
  exact Prod.ext hcells hu

/-- Candidate midpoints in the disk are in bijection with the finite set of
residue-class/candidate pairs whose periodic hit indicator is true. -/
theorem ncard_candidateMidpointHitSet_eq_periodHitPairs
    {L q : ℕ} [NeZero L] {center : Plane} {radius : ℝ}
    (hperiod : 2 * radius < (L : ℝ)) :
    (candidateMidpointHitSet q center radius).ncard =
      Set.ncard {p : PeriodCell L × GridCandidate q |
        periodHit L q center radius p.1 p.2} := by
  apply Set.ncard_congr
    (fun a _ ↦ (periodClass L a.1, a.2))
  · rintro ⟨cell, u⟩ hcell
    change periodHit L q center radius (periodClass L cell) u = true
    rw [periodHit_eq_true_iff]
    exact ⟨cell, rfl, hcell⟩
  · intro a b ha hb hab
    exact periodClass_prod_injOn_candidateMidpointHitSet hperiod ha hb hab
  · rintro ⟨i, u⟩ hp
    change periodHit L q center radius i u = true at hp
    rw [periodHit_eq_true_iff] at hp
    obtain ⟨cell, hclass, hcell⟩ := hp
    exact ⟨(cell, u), hcell, by simp [hclass]⟩

/-- The number of hit pairs is the sum, over residue classes, of the number of successful
candidates in that class. -/
theorem ncard_periodHitPairs_eq_sum_card
    {L q : ℕ} [NeZero L] (center : Plane) (radius : ℝ) :
    Set.ncard {p : PeriodCell L × GridCandidate q |
        periodHit L q center radius p.1 p.2} =
      ∑ i : PeriodCell L,
        ((Finset.univ : Finset (GridCandidate q)).filter fun u ↦
          periodHit L q center radius i u = true).card := by
  classical
  let H : Set (PeriodCell L × GridCandidate q) :=
    {p | periodHit L q center radius p.1 p.2}
  have hH : H.Finite := Set.toFinite H
  change H.ncard = _
  calc
    H.ncard =
        ∑ p : PeriodCell L × GridCandidate q,
          if periodHit L q center radius p.1 p.2 then 1 else 0 := by
      rw [Set.ncard_eq_toFinset_card H hH, hH.toFinset_ofPred]
      symm
      exact Finset.sum_boole (R := ℕ)
        (fun p : PeriodCell L × GridCandidate q ↦
          periodHit L q center radius p.1 p.2 = true)
        Finset.univ
    _ = ∑ i : PeriodCell L, ∑ u : GridCandidate q,
          if periodHit L q center radius i u then 1 else 0 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ i : PeriodCell L,
        ((Finset.univ : Finset (GridCandidate q)).filter fun u ↦
          periodHit L q center radius i u = true).card := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_boole _ _

/-- The finite periodic expectation is exactly the normalized full midpoint-grid count. -/
theorem periodExpectedDiskCount_eq_candidateMidpointHitSet
    {L q : ℕ} [NeZero L] [NeZero q]
    (center : Plane) (radius : ℝ)
    (hperiod : 2 * radius < (L : ℝ)) :
    periodExpectedDiskCount L q center radius =
      (((candidateMidpointHitSet q center radius).ncard : ℕ) : ℝ) /
        (q : ℝ) ^ 2 := by
  let : MeasurableSpace (GridCandidate q) := ⊤
  let ν : PeriodCell L → Measure (GridCandidate q) := fun _ ↦
    (PMF.uniformOfFintype (GridCandidate q)).toMeasure
  have hpairs := ncard_candidateMidpointHitSet_eq_periodHitPairs
    (L := L) (q := q) (center := center) (radius := radius) hperiod
  have hsum := ncard_periodHitPairs_eq_sum_card
    (L := L) (q := q) center radius
  have hcardQ : (Fintype.card (GridCandidate q) : ℝ) = (q : ℝ) ^ 2 := by
    simp [GridCandidate, Fintype.card_prod]
    ring
  rw [periodExpectedDiskCount]
  simp_rw [integral_uniformOfFintype_boolIndicator]
  rw [hcardQ, ← Finset.sum_div]
  congr 1
  exact_mod_cast (hpairs.trans hsum).symm

/-- Therefore the periodic expectation differs from the disk area by the explicit midpoint
quadrature error. -/
theorem periodExpectedDiskCount_sub_area_le
    {L q : ℕ} [NeZero L] [NeZero q]
    (center : Plane) {radius : ℝ}
    (hperiod : 2 * radius < (L : ℝ))
    (hradius : Real.sqrt 2 / (2 * q) ≤ radius) :
    |periodExpectedDiskCount L q center radius - Real.pi * radius ^ 2| ≤
      16 * radius / q + 16 / (q : ℝ) ^ 2 := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  rw [periodExpectedDiskCount_eq_candidateMidpointHitSet center radius hperiod]
  exact midpoint_grid_disk_quadrature hq center hradius

end

end FixedRadiusUpper
end Erdos989
