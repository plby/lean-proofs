/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos989.FixedRadiusUpper
import ErdosProblems.Erdos989.UpperExpectation
import ErdosProblems.Erdos989.UpperNet
import ErdosProblems.Erdos989.UpperPeriodicProbability
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The unconditional fixed-scale upper construction for Erdős problem 989

This file combines the periodic midpoint model, concentration, midpoint
quadrature, and the finite torus net.  The resulting admissible point set may
depend on the prescribed radius, while the constant is universal.
-/

namespace Erdos989
namespace FixedRadiusUpper

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open GlobalSelection UpperGeometry

/-- The infinite point set selected by one periodic midpoint assignment. -/
def periodicPointSet (L q : ℕ) (ω : PeriodCell L → GridCandidate q) : Set Plane :=
  Set.range (selectedPoint (latticeLocation (midpointOffset q))
    (periodicSelection L q ω))

theorem periodicPointSet_admissible
    {L q : ℕ} (hq : 0 < q) (ω : PeriodCell L → GridCandidate q) :
    IsAdmissible (periodicPointSet L q ω) := by
  let x := periodicSelection L q ω
  let z := selectedPoint (latticeLocation (midpointOffset q)) x
  have hoffset := midpointOffset_in_halfOpenUnitSquare hq
  have hinj : Function.Injective z :=
    selectedPoint_injective_of_cell_separated
      (latticeLocation_cell_separated hoffset) x
  have hloc : CandidateTableLocallyFinite (latticeLocation (midpointOffset q)) :=
    latticeLocation_candidateTableLocallyFinite fun u ↦
      ⟨(hoffset u).1, (hoffset u).2.1.le,
        (hoffset u).2.2.1, (hoffset u).2.2.2.le⟩
  have hinfinite : (Set.range z).Infinite := Set.infinite_range_of_injective hinj
  have hcompact : ∀ K : Set Plane, IsCompact K → (Set.range z ∩ K).Finite := by
    intro K hK
    rw [range_inter_eq_image_preimage]
    exact (selectedPoint_compact_preimage_finite hloc x K hK).image z
  exact ⟨hinfinite, hcompact⟩

/-- For the actual range point set, core `diskError` is exactly the selected
index error used by the periodic probability model. -/
theorem diskError_periodicPointSet_eq
    {L q : ℕ} (hq : 0 < q) (ω : PeriodCell L → GridCandidate q)
    (center : Plane) (radius : ℝ) :
    diskError (periodicPointSet L q ω) center radius =
      |(selectedDiskCount (latticeLocation (midpointOffset q))
          (periodicSelection L q ω) center radius : ℝ) -
        Real.pi * radius ^ 2| := by
  let x := periodicSelection L q ω
  have hinj : Function.Injective
      (selectedPoint (latticeLocation (midpointOffset q)) x) :=
    selectedPoint_injective_of_cell_separated
      (latticeLocation_cell_separated
        (midpointOffset_in_halfOpenUnitSquare hq)) x
  unfold diskError diskCount periodicPointSet
  rw [range_disk_error_eq_selectedDiskError hinj]
  rfl

/-- Periodicity of the selected indices gives periodicity of the actual
range-set disk error. -/
theorem diskError_periodicPointSet_periodTranslation
    {L q : ℕ} (hq : 0 < q) (ω : PeriodCell L → GridCandidate q)
    (center : Plane) (radius : ℝ) (k : PlaneCell) :
    diskError (periodicPointSet L q ω)
        (center + periodTranslation L k) radius =
      diskError (periodicPointSet L q ω) center radius := by
  rw [diskError_periodicPointSet_eq hq, diskError_periodicPointSet_eq hq,
    selectedDiskCount_periodTranslation]

/-- Bounds on the inner and outer test radii. -/
theorem centerNetEventRadius_bounds {r : ℝ} (hr : 8 ≤ r)
    (e : CenterNetEvent (radiusPeriodLength r) (radiusGridSize r)) :
    Real.sqrt 2 ≤ centerNetEventRadius r (radiusGridSize r) e ∧
      centerNetEventRadius r (radiusGridSize r) e ≤ 9 * r / 8 := by
  have hr2 : 2 ≤ r := by linarith
  have heta := sqrt_two_div_radiusGridSize_le_one hr2
  have hsqrt : Real.sqrt 2 ≤ 2 := by norm_num
  have heta0 : 0 ≤ Real.sqrt 2 / (radiusGridSize r : ℝ) := by positivity
  simp only [centerNetEventRadius]
  split_ifs <;> constructor <;> nlinarith

theorem centerNetEventRadius_quadrature_lower {r : ℝ} (hr : 8 ≤ r)
    (e : CenterNetEvent (radiusPeriodLength r) (radiusGridSize r)) :
    Real.sqrt 2 / (2 * radiusGridSize r) ≤
      centerNetEventRadius r (radiusGridSize r) e := by
  have hb := (centerNetEventRadius_bounds hr e).1
  have hq : 0 < (radiusGridSize r : ℝ) := by
    exact_mod_cast radiusGridSize_pos (by linarith : 0 < r)
  have hdiv : Real.sqrt 2 / (2 * radiusGridSize r) ≤ Real.sqrt 2 := by
    have hdenom : 1 ≤ (2 : ℝ) * radiusGridSize r := by
      have : 1 ≤ (radiusGridSize r : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (Nat.ne_of_gt (radiusGridSize_pos (by linarith : 0 < r)))
      nlinarith
    exact (div_le_iff₀ (by positivity : 0 < (2 : ℝ) * radiusGridSize r)).2
      (by nlinarith [Real.sqrt_nonneg 2])
  exact hdiv.trans hb

/-- The deterministic midpoint quadrature error is at most `20` on every
inner/outer net disk at a radius at least eight. -/
theorem centerNetEvent_quadrature_error_le_twenty {r : ℝ} (hr : 8 ≤ r)
    (e : CenterNetEvent (radiusPeriodLength r) (radiusGridSize r)) :
    16 * centerNetEventRadius r (radiusGridSize r) e / radiusGridSize r +
        16 / (radiusGridSize r : ℝ) ^ 2 ≤ 20 := by
  let q := radiusGridSize r
  let rho := centerNetEventRadius r q e
  have hqpos : 0 < (q : ℝ) := by
    exact_mod_cast radiusGridSize_pos (by linarith : 0 < r)
  have hqge : r ≤ (q : ℝ) := radius_le_radiusGridSize r
  have hrho : rho ≤ 9 * r / 8 := (centerNetEventRadius_bounds hr e).2
  have hratio : rho / q ≤ 9 / 8 := by
    rw [div_le_iff₀ hqpos]
    nlinarith
  have hq8 : 8 ≤ (q : ℝ) := hr.trans hqge
  have hinvSq : 16 / (q : ℝ) ^ 2 ≤ 1 / 4 := by
    rw [div_le_iff₀ (sq_pos_of_pos hqpos)]
    nlinarith [sq_nonneg ((q : ℝ) - 8)]
  have hfirst : 16 * rho / (q : ℝ) ≤ 18 := by
    calc
      16 * rho / (q : ℝ) = 16 * (rho / (q : ℝ)) := by ring
      _ ≤ 16 * (9 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_left hratio (by norm_num)
      _ = 18 := by norm_num
  change 16 * rho / (q : ℝ) + 16 / (q : ℝ) ^ 2 ≤ 20
  calc
    16 * rho / (q : ℝ) + 16 / (q : ℝ) ^ 2 ≤ 18 + 1 / 4 :=
      add_le_add hfirst hinvSq
    _ ≤ 20 := by norm_num

/-- Both radii in the net are controlled by one periodic assignment. -/
theorem exists_periodic_assignment_good_on_centerNet {r : ℝ} (hr : 8 ≤ r) :
    let q := radiusGridSize r
    let L := radiusPeriodLength r
    let _ : NeZero q :=
      ⟨Nat.ne_of_gt (radiusGridSize_pos (by linarith : 0 < r))⟩
    let _ : NeZero L :=
      ⟨Nat.ne_of_gt (radiusPeriodLength_pos (by linarith : 0 ≤ r))⟩
    ∃ ω : PeriodCell L → GridCandidate q,
      ∀ e : CenterNetEvent L q,
        |(selectedDiskCount (latticeLocation (midpointOffset q))
              (periodicSelection L q ω) (centerNetEventCenter q e)
                (centerNetEventRadius r q e) : ℝ) -
          periodExpectedDiskCount L q (centerNetEventCenter q e)
            (centerNetEventRadius r q e)| <
          30 * Real.sqrt (r * Real.log r) := by
  let q := radiusGridSize r
  let L := radiusPeriodLength r
  have hq : 0 < q := radiusGridSize_pos (by linarith)
  have hL : 0 < L := radiusPeriodLength_pos (by linarith)
  let : NeZero q := ⟨Nat.ne_of_gt hq⟩
  let : NeZero L := ⟨Nat.ne_of_gt hL⟩
  let : MeasurableSpace (GridCandidate q) := ⊤
  let ν : PeriodCell L → Measure (GridCandidate q) := fun _ ↦
    (PMF.uniformOfFintype (GridCandidate q)).toMeasure
  let μ : Measure (PeriodCell L → GridCandidate q) := Measure.pi ν
  let bad : CenterNetEvent L q → Set (PeriodCell L → GridCandidate q) := fun e ↦
    {ω | 30 * Real.sqrt (r * Real.log r) ≤
      |(selectedDiskCount (latticeLocation (midpointOffset q))
            (periodicSelection L q ω) (centerNetEventCenter q e)
              (centerNetEventRadius r q e) : ℝ) -
        periodExpectedDiskCount L q (centerNetEventCenter q e)
          (centerNetEventRadius r q e)|}
  have hr2 : 2 ≤ r := by linarith
  have hbad : ∀ e, μ.real (bad e) ≤
      2 * Real.exp (-(50 / 3) * Real.log r) := by
    intro e
    have hb := centerNetEventRadius_bounds hr e
    simpa [μ, ν, bad, q, L] using
      (periodicDiskCount_tail_le (L := L) (q := q) hr hb.1 hb.2
        (centerNetEventCenter q e)
        (centerNetEventRadius_diameter_lt_period hr2 e))
  obtain ⟨ω, hω⟩ := exists_avoiding_periodic_net_events μ hr2 bad
    (by simpa [q, L] using card_centerNetEvent_radius_le hr2) hbad
  refine ⟨ω, fun e ↦ ?_⟩
  have := hω e
  simpa [bad, not_le] using this

/-- Net-disk discrepancy for the selected range set. -/
theorem exists_admissible_with_centerNet_bounds {r : ℝ} (hr : 8 ≤ r) :
    let q := radiusGridSize r
    let L := radiusPeriodLength r
    ∃ ω : PeriodCell L → GridCandidate q,
      IsAdmissible (periodicPointSet L q ω) ∧
      ∀ e : CenterNetEvent L q,
        diskError (periodicPointSet L q ω) (centerNetEventCenter q e)
            (centerNetEventRadius r q e) ≤
          30 * Real.sqrt (r * Real.log r) + 20 := by
  let q := radiusGridSize r
  let L := radiusPeriodLength r
  have hq : 0 < q := radiusGridSize_pos (by linarith)
  have hL : 0 < L := radiusPeriodLength_pos (by linarith)
  let : NeZero q := ⟨Nat.ne_of_gt hq⟩
  let : NeZero L := ⟨Nat.ne_of_gt hL⟩
  obtain ⟨ω, hω⟩ := exists_periodic_assignment_good_on_centerNet hr
  refine ⟨ω, periodicPointSet_admissible hq ω, ?_⟩
  intro e
  let center := centerNetEventCenter q e
  let rho := centerNetEventRadius r q e
  have hperiod := centerNetEventRadius_diameter_lt_period
    (show 2 ≤ r by linarith) e
  have hquad := periodExpectedDiskCount_sub_area_le
    (L := L) (q := q) center hperiod
      (centerNetEventRadius_quadrature_lower hr e)
  have hquad20 := centerNetEvent_quadrature_error_le_twenty hr e
  rw [diskError_periodicPointSet_eq hq]
  calc
    |(selectedDiskCount (latticeLocation (midpointOffset q))
          (periodicSelection L q ω) center rho : ℝ) - Real.pi * rho ^ 2|
        ≤ |(selectedDiskCount (latticeLocation (midpointOffset q))
              (periodicSelection L q ω) center rho : ℝ) -
            periodExpectedDiskCount L q center rho| +
          |periodExpectedDiskCount L q center rho - Real.pi * rho ^ 2| := by
            calc
              |(selectedDiskCount (latticeLocation (midpointOffset q))
                    (periodicSelection L q ω) center rho : ℝ) -
                  Real.pi * rho ^ 2| =
                  |((selectedDiskCount (latticeLocation (midpointOffset q))
                      (periodicSelection L q ω) center rho : ℝ) -
                    periodExpectedDiskCount L q center rho) +
                    (periodExpectedDiskCount L q center rho -
                      Real.pi * rho ^ 2)| := by
                        congr 1
                        ring
              _ ≤ |(selectedDiskCount (latticeLocation (midpointOffset q))
                      (periodicSelection L q ω) center rho : ℝ) -
                    periodExpectedDiskCount L q center rho| +
                  |periodExpectedDiskCount L q center rho -
                    Real.pi * rho ^ 2| := abs_add_le _ _
    _ ≤ 30 * Real.sqrt (r * Real.log r) +
          (16 * rho / q + 16 / (q : ℝ) ^ 2) :=
      add_le_add (hω e).le hquad
    _ ≤ 30 * Real.sqrt (r * Real.log r) + 20 := by
      gcongr

/-- A fixed prescribed radius admits an admissible set with uniform disk
error `70 √(r log r)`. -/
theorem exists_admissible_fixedRadius_sqrtLog {r : ℝ} (hr : 8 ≤ r) :
    ∃ A : Set Plane, IsAdmissible A ∧ ∀ x : Plane,
      diskError A x r ≤ 70 * Real.sqrt (r * Real.log r) := by
  let q := radiusGridSize r
  let L := radiusPeriodLength r
  have hq : 0 < q := radiusGridSize_pos (by linarith)
  have hL : 0 < L := radiusPeriodLength_pos (by linarith)
  let : NeZero q := ⟨Nat.ne_of_gt hq⟩
  let : NeZero L := ⟨Nat.ne_of_gt hL⟩
  obtain ⟨ω, hA, hnet⟩ := exists_admissible_with_centerNet_bounds hr
  let A := periodicPointSet L q ω
  refine ⟨A, hA, ?_⟩
  intro x
  obtain ⟨u, k, hnear⟩ :=
    exists_centerNetPoint_add_periodTranslation_near hL hq x
  let inner : CenterNetEvent L q := (u, false)
  let outer : CenterNetEvent L q := (u, true)
  have hinner0 := hnet inner
  have houter0 := hnet outer
  have hinner : diskError A
      (centerNetPoint q u + periodTranslation L k)
        (r - Real.sqrt 2 / q) ≤
      30 * Real.sqrt (r * Real.log r) + 20 := by
    rw [show A = periodicPointSet L q ω by rfl,
      diskError_periodicPointSet_periodTranslation hq]
    simpa [inner, centerNetEventCenter, centerNetEventRadius] using hinner0
  have houter : diskError A
      (centerNetPoint q u + periodTranslation L k)
        (r + Real.sqrt 2 / q) ≤
      30 * Real.sqrt (r * Real.log r) + 20 := by
    rw [show A = periodicPointSet L q ω by rfl,
      diskError_periodicPointSet_periodTranslation hq]
    simpa [outer, centerNetEventCenter, centerNetEventRadius] using houter0
  have heta : Real.sqrt 2 / q ≤ r := by
    exact (sqrt_two_div_radiusGridSize_le_one (show 2 ≤ r by linarith)).trans
      (by linarith)
  have htransfer := diskError_le_of_centerNet_inner_outer hA hq heta hnear hinner houter
  have hshell : Real.pi *
      (2 * r * (Real.sqrt 2 / q) + (Real.sqrt 2 / q) ^ 2) ≤ 20 := by
    have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
    have hrq : r ≤ (q : ℝ) := radius_le_radiusGridSize r
    have heta0 : 0 ≤ Real.sqrt 2 / (q : ℝ) := by positivity
    have heta1 : Real.sqrt 2 / (q : ℝ) ≤ 1 :=
      sqrt_two_div_radiusGridSize_le_one (show 2 ≤ r by linarith)
    have hrEta : r * (Real.sqrt 2 / (q : ℝ)) ≤ Real.sqrt 2 := by
      have hratio : r / (q : ℝ) ≤ 1 := (div_le_one hqR).2 hrq
      calc
        r * (Real.sqrt 2 / (q : ℝ)) =
            (r / (q : ℝ)) * Real.sqrt 2 := by ring
        _ ≤ 1 * Real.sqrt 2 :=
          mul_le_mul_of_nonneg_right hratio (Real.sqrt_nonneg 2)
        _ = Real.sqrt 2 := one_mul _
    have hsqrt : Real.sqrt 2 ≤ 2 := by norm_num
    have hetaSq : (Real.sqrt 2 / (q : ℝ)) ^ 2 ≤ 1 := by
      have h := (sq_le_sq₀ heta0 (by norm_num : (0 : ℝ) ≤ 1)).2 heta1
      norm_num at h ⊢
      exact h
    have hinside :
        2 * r * (Real.sqrt 2 / (q : ℝ)) +
            (Real.sqrt 2 / (q : ℝ)) ^ 2 ≤ 5 := by
      nlinarith
    calc
      Real.pi * (2 * r * (Real.sqrt 2 / q) +
          (Real.sqrt 2 / q) ^ 2) ≤ 4 * 5 := by
            exact mul_le_mul Real.pi_le_four hinside (by positivity) (by norm_num)
      _ = 20 := by norm_num
  have hsqrtOne : 1 ≤ Real.sqrt (r * Real.log r) := by
    rw [Real.one_le_sqrt]
    have hlog : 1 ≤ Real.log r := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      exact Real.exp_one_lt_three.le.trans (by linarith)
    nlinarith
  calc
    diskError A x r ≤
        30 * Real.sqrt (r * Real.log r) + 20 +
          Real.pi * (2 * r * (Real.sqrt 2 / q) +
            (Real.sqrt 2 / q) ^ 2) := htransfer
    _ ≤ 30 * Real.sqrt (r * Real.log r) + 20 + 20 := by gcongr
    _ ≤ 70 * Real.sqrt (r * Real.log r) := by nlinarith

/-- Beck's fixed-scale upper estimate, in the exact quantifier order used by
`Erdos989.HasSqrtLogUpperConstruction`. -/
theorem hasSqrtLogUpperConstruction : HasSqrtLogUpperConstruction := by
  refine ⟨70, by norm_num, 8, ?_⟩
  intro r hr
  exact exists_admissible_fixedRadius_sqrtLog hr

end

end FixedRadiusUpper
end Erdos989

#print axioms Erdos989.FixedRadiusUpper.hasSqrtLogUpperConstruction
