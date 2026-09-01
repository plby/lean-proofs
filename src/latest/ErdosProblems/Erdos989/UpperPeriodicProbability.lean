/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos989.UpperPeriodic
import ErdosProblems.Erdos989.UpperGeometry
import ErdosProblems.Erdos989.UpperProbability

/-!
# Concentration for the periodic jitter model

The disk count depends only on the residue classes whose candidates straddle
the circle.  This file rewrites the centered full count as a centered sum over
those active classes and applies Hoeffding with the linear boundary-cell
estimate.
-/

namespace Erdos989
namespace FixedRadiusUpper

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open GlobalSelection UpperGeometry

/-- Every midpoint candidate lies in its half-open integer unit cell. -/
theorem midpoint_location_mem_unitCell {q : ℕ} (hq : 0 < q)
    (cell : PlaneCell) (u : GridCandidate q) :
    latticeLocation (midpointOffset q) cell u ∈ unitCell cell := by
  apply Set.mem_pi.mpr
  intro i hi
  have hoff := midpointOffset_in_halfOpenUnitSquare hq u
  fin_cases i
  · simpa [UpperGeometry.unitCell, UpperGeometry.coordinateUnitCell,
      UpperGeometry.cellLower] using
      (show (cell.1 : ℝ) ≤
          (cell.1 : ℝ) + (midpointOffset q u).1 ∧
        (cell.1 : ℝ) + (midpointOffset q u).1 < (cell.1 : ℝ) + 1 by
          constructor <;> linarith [hoff.1, hoff.2.1])
  · simpa [UpperGeometry.unitCell, UpperGeometry.coordinateUnitCell,
      UpperGeometry.cellLower] using
      (show (cell.2 : ℝ) ≤
          (cell.2 : ℝ) + (midpointOffset q u).2 ∧
        (cell.2 : ℝ) + (midpointOffset q u).2 < (cell.2 : ℝ) + 1 by
          constructor <;> linarith [hoff.2.2.1, hoff.2.2.2])

/-- A midpoint-grid boundary cell is a genuine geometric boundary cell. -/
theorem isDiskBoundaryCell_of_isMidpointBoundaryCell {q : ℕ} (hq : 0 < q)
    {center : Plane} {radius : ℝ} {cell : PlaneCell}
    (hcell : IsMidpointBoundaryCell q center radius cell) :
    IsDiskBoundaryCell center radius cell := by
  rcases hcell with ⟨u, v, hu, hv⟩
  exact ⟨latticeLocation (midpointOffset q) cell u,
    midpoint_location_mem_unitCell hq cell u,
    latticeLocation (midpointOffset q) cell v,
    midpoint_location_mem_unitCell hq cell v, hu, hv⟩

/-- The active-coordinate count inherits the annulus area estimate. -/
theorem card_periodActive_real_le_annulus
    {L q : ℕ} [NeZero L] (hq : 0 < q)
    (center : Plane) {radius : ℝ} (hr : Real.sqrt 2 ≤ radius) :
    ((periodActive L q center radius).card : ℝ) ≤
      4 * Real.pi * Real.sqrt 2 * radius := by
  have hnat := card_periodActive_le_ncard_midpointBoundaryCells
    (L := L) hq center radius
  have hmidfinite := finite_midpointBoundaryCells hq center radius
  have hsubset :
      {cell : PlaneCell | IsMidpointBoundaryCell q center radius cell} ⊆
        {cell : PlaneCell | IsDiskBoundaryCell center radius cell} := by
    intro cell hcell
    exact isDiskBoundaryCell_of_isMidpointBoundaryCell hq hcell
  have hncard := Set.ncard_le_ncard hsubset (boundaryCellSet_finite center radius)
  have hgeom := ncard_boundaryCellSet_le (center := center) hr
  have hcast : ((periodActive L q center radius).card : ℝ) ≤
      ({cell : PlaneCell | IsDiskBoundaryCell center radius cell}.ncard : ℝ) := by
    exact_mod_cast (show
    ((periodActive L q center radius).card : ℕ) ≤
      {cell : PlaneCell | IsDiskBoundaryCell center radius cell}.ncard from
        hnat.trans hncard)
  exact hcast.trans hgeom

/-- If no residue class straddles the circle, the periodic disk count is
deterministic and therefore equals its finite-product expectation. -/
theorem periodicDiskCount_eq_expected_of_periodActive_eq_empty
    {L q : ℕ} [NeZero L] [NeZero q]
    (center : Plane) (radius : ℝ)
    (hperiod : 2 * radius < (L : ℝ))
    (hactive : periodActive L q center radius = ∅)
    (ω : PeriodCell L → GridCandidate q) :
    (selectedDiskCount (latticeLocation (midpointOffset q))
        (periodicSelection L q ω) center radius : ℝ) =
      periodExpectedDiskCount L q center radius := by
  classical
  let : MeasurableSpace (GridCandidate q) := ⊤
  let ν : PeriodCell L → Measure (GridCandidate q) := fun _ ↦
    (PMF.uniformOfFintype (GridCandidate q)).toMeasure
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hcountNat :=
    selectedDiskCount_periodic_eq_sum_periodHit hq ω center radius hperiod
  have hcountReal :
      (selectedDiskCount (latticeLocation (midpointOffset q))
          (periodicSelection L q ω) center radius : ℝ) =
        ∑ i : PeriodCell L,
          if periodHit L q center radius i (ω i) then (1 : ℝ) else 0 := by
    exact_mod_cast hcountNat
  rw [hcountReal]
  change (∑ i : PeriodCell L,
      if periodHit L q center radius i (ω i) then (1 : ℝ) else 0) =
    ∑ i : PeriodCell L,
      ∫ u, (if periodHit L q center radius i u then (1 : ℝ) else 0) ∂ν i
  apply Finset.sum_congr rfl
  intro i hi
  have hi : i ∉ periodActive L q center radius := by simp [hactive]
  let u0 : GridCandidate q := Classical.choice inferInstance
  have hconst (u : GridCandidate q) :
      periodHit L q center radius i u = periodHit L q center radius i u0 :=
    periodHit_eq_of_not_mem_periodActive hi u u0
  have hfun : (fun u : GridCandidate q ↦
      if periodHit L q center radius i u then (1 : ℝ) else 0) =
      fun _ ↦ if periodHit L q center radius i u0 then (1 : ℝ) else 0 := by
    funext u
    rw [hconst u]
  rw [hconst (ω i), hfun]
  simp [ν]

/-- The explicit single-disk tail estimate used by the finite center net.
The constants are intentionally generous, leaving room for the two nearby
radii in the net sandwich. -/
theorem periodicDiskCount_tail_le
    {L q : ℕ} [NeZero L] [NeZero q]
    {r rho : ℝ} (hr : 8 ≤ r)
    (hrhoLower : Real.sqrt 2 ≤ rho) (hrhoUpper : rho ≤ 9 * r / 8)
    (center : Plane) (hperiod : 2 * rho < (L : ℝ)) :
    letI : MeasurableSpace (GridCandidate q) := ⊤
    let ν : PeriodCell L → Measure (GridCandidate q) := fun _ ↦
      (PMF.uniformOfFintype (GridCandidate q)).toMeasure
    let μ : Measure (PeriodCell L → GridCandidate q) := Measure.pi ν
    μ.real {ω | 30 * Real.sqrt (r * Real.log r) ≤
        |(selectedDiskCount (latticeLocation (midpointOffset q))
              (periodicSelection L q ω) center rho : ℝ) -
          periodExpectedDiskCount L q center rho|} ≤
      2 * Real.exp (-(50 / 3) * Real.log r) := by
  let : MeasurableSpace (GridCandidate q) := ⊤
  let ν : PeriodCell L → Measure (GridCandidate q) := fun _ ↦
    (PMF.uniformOfFintype (GridCandidate q)).toMeasure
  let μ : Measure (PeriodCell L → GridCandidate q) := Measure.pi ν
  let M : ℕ := (periodActive L q center rho).card
  let t : ℝ := 30 * Real.sqrt (r * Real.log r)
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hlog0 : 0 ≤ Real.log r := Real.log_nonneg (by linarith)
  have hprod0 : 0 ≤ r * Real.log r := mul_nonneg hr0.le hlog0
  have ht0 : 0 ≤ t := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have htpos : 0 < t := by
    have hlogpos : 0 < Real.log r := Real.log_pos (by linarith)
    exact mul_pos (by norm_num) (Real.sqrt_pos.2 (mul_pos hr0 hlogpos))
  by_cases hMzero : M = 0
  · have hactive : periodActive L q center rho = ∅ := by
      apply Finset.card_eq_zero.mp
      exact hMzero
    have hset :
        {ω : PeriodCell L → GridCandidate q | t ≤
          |(selectedDiskCount (latticeLocation (midpointOffset q))
                (periodicSelection L q ω) center rho : ℝ) -
            periodExpectedDiskCount L q center rho|} = ∅ := by
      ext ω
      have hdet := periodicDiskCount_eq_expected_of_periodActive_eq_empty
        center rho hperiod hactive ω
      simp [hdet, not_le_of_gt htpos]
    change μ.real _ ≤ _
    rw [show (30 : ℝ) * Real.sqrt (r * Real.log r) = t by rfl, hset]
    rw [measureReal_empty]
    positivity
  · have hMposNat : 0 < M := Nat.pos_of_ne_zero hMzero
    have hMpos : 0 < (M : ℝ) := by exact_mod_cast hMposNat
    have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
    have hMgeom : (M : ℝ) ≤ 48 * rho := by
      dsimp [M]
      exact (card_periodActive_real_le_annulus hq center hrhoLower).trans
        (by
          have hcoef : 4 * Real.pi * Real.sqrt 2 ≤ 48 := by
            calc
              4 * Real.pi * Real.sqrt 2 ≤ 4 * 4 * 2 := by
                gcongr
                · exact Real.pi_le_four
                · norm_num
              _ ≤ 48 := by norm_num
          exact mul_le_mul_of_nonneg_right hcoef
            ((Real.sqrt_nonneg 2).trans hrhoLower))
    have hMbound : (M : ℝ) ≤ 54 * r := by
      calc
        (M : ℝ) ≤ 48 * rho := hMgeom
        _ ≤ 48 * (9 * r / 8) := by gcongr
        _ = 54 * r := by ring
    have htSq : t ^ 2 = 900 * (r * Real.log r) := by
      dsimp [t]
      rw [mul_pow, Real.sq_sqrt hprod0]
      norm_num
    have hdenom : 0 < 2 * ((M : ℝ) / 4) := by positivity
    have hquot : (50 / 3 : ℝ) * Real.log r ≤
        t ^ 2 / (2 * ((M : ℝ) / 4)) := by
      rw [le_div_iff₀ hdenom, htSq]
      have hmul : (M : ℝ) * Real.log r ≤ 54 * r * Real.log r :=
        mul_le_mul_of_nonneg_right hMbound hlog0
      nlinarith
    have hexponent :
        -(t ^ 2 / (2 * ((M : ℝ) / 4))) ≤
          -(50 / 3 : ℝ) * Real.log r := by
      nlinarith
    have htail := @periodicDiskCount_hoeffding_expected L q
      (inferInstance : NeZero L) (inferInstance : NeZero q)
      center rho t hperiod ht0
    change μ.real _ ≤ _
    calc
      μ.real {ω | t ≤
          |(selectedDiskCount (latticeLocation (midpointOffset q))
                (periodicSelection L q ω) center rho : ℝ) -
            periodExpectedDiskCount L q center rho|}
          ≤ 2 * Real.exp
              (-t ^ 2 / (2 * (((periodActive L q center rho).card : ℝ) / 4))) :=
        by simpa [μ, ν] using htail
      _ ≤ 2 * Real.exp (-(50 / 3) * Real.log r) := by
        dsimp [M] at hexponent
        gcongr
        simpa only [neg_div] using hexponent

end

end FixedRadiusUpper
end Erdos989
