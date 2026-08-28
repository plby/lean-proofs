import Wikipedia.HopfProblem.CuspBoundaryTopVanishingPeriodsBasic
import Wikipedia.HopfProblem.SpecialPeriodsCuspFamilyAction

/-!
# Joint base coordinates on the original logarithmic period cover

For the literal varying period equivalence of `CuspFamily.Data`, the
independently prescribed central collapse has base coordinates equal to
the first two real period coordinates modulo integers. The statement is
joint in the logarithmic base and all four real coordinates. Its only
extra bound is the genuine small-drift bound for the frozen correction;
the final existence theorem derives a uniform radius for that bound.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.CuspBoundaryTopVanishing

open ToricCharts ToricSpace CuspUniformization CuspRetraction
open CuspControlledRetraction CuspCollapse CuspCentralHomology
open PeriodTorusHigherHomology SpecialPeriods.CuspFamily

/-- The actual period equivalence has logarithmic coefficients first and
integer-period coefficients second. -/
theorem periodEquiv_split (D : Data) (s : LogBase D.radius) (x : RealPlane₄) :
    D.periods.periodEquiv s x =
      realToComplex ![x 2, x 3] +
        logarithmicPeriod D.correction (s : ℂ) *ᵥ realToComplex ![x 0, x 1] := by
  rw [HolomorphicPeriodMap.periodEquiv_coordinates, ← D.point_leftBlock s]
  ext i
  fin_cases i <;>
    simp [Data.periods_point, PeriodPoint.leftBlock, realToComplex,
      dotProduct, Fin.sum_univ_two] <;> ring

/-- The original logarithmic-cover representative of all four real periods. -/
def periodLogCover (D : Data) (s : LogBase D.radius) (x : RealPlane₄) :
    LogCover D.radius :=
  ⟨((s : ℂ), D.periods.periodEquiv s x), s.2⟩

@[simp] theorem periodLogCover_coe (D : Data) (s : LogBase D.radius) (x : RealPlane₄) :
    (periodLogCover D s x : ℂ × ComplexPlane₂) =
      ((s : ℂ), D.periods.periodEquiv s x) := rfl

/-- The same actual toric representative in any containing punctured closed tube. -/
def periodPointPunctured (D : Data) (η : ℝ) (s : LogBase D.radius)
    (hη : ‖exponential (s : ℂ)‖ ≤ η) (x : RealPlane₄) : PuncturedClosedTube η :=
  ⟨⟨totalExponentialPoint (periodLogCover D s x), by
      rw [time_totalExponentialPoint]
      exact hη⟩, by
    change time (totalExponentialPoint (periodLogCover D s x)) ≠ 0
    rw [time_totalExponentialPoint]
    exact exponential_ne_zero (s : ℂ)⟩

@[simp] theorem periodPointPunctured_coe (D : Data) (η : ℝ) (s : LogBase D.radius)
    (hη : ‖exponential (s : ℂ)‖ ≤ η) (x : RealPlane₄) :
    ((periodPointPunctured D η s hη x).1 : Space) =
      totalExponentialPoint (periodLogCover D s x) := rfl

/-- Compatibility with the actual punctured cusp quotient, not a model quotient. -/
theorem periodPointPunctured_quotient (D : Data) (η : ℝ) (hηr : η < D.radius)
    (s : LogBase D.radius) (hη : ‖exponential (s : ℂ)‖ ≤ η) (x : RealPlane₄) :
    (closedQuotientMap D.correction hηr (periodPointPunctured D η s hη x).1).1 =
      (puncturedCuspCover D.correction D.radius (periodLogCover D s x)).1 := rfl

theorem periodPointPunctured_eq_markedPoint (D : Data) (η : ℝ)
    (s : LogBase D.radius) (hη : ‖exponential (s : ℂ)‖ ≤ η) (x : RealPlane₄) :
    periodPointPunctured D η s hη x =
      markedPointPunctured D.correction η (s : ℂ) hη ![x 2, x 3] ![x 0, x 1] := by
  apply Subtype.ext
  apply Subtype.ext
  change exponentialPoint (exponential (s : ℂ)) (D.periods.periodEquiv s x) = _
  rw [periodEquiv_split]
  rfl

/-- Exact joint base-coordinate identity on the original period cover. -/
theorem baseTorusProjection_straightened_periodPoint
    (D : Data) (η : ℝ) (s : LogBase D.radius)
    (hη : ‖exponential (s : ℂ)‖ ≤ η)
    (hR0 : entryNorm (driftMatrix (frozen D.correction) (exponential (s : ℂ))) ≤
      -Real.log ‖exponential (s : ℂ)‖ / 4) (x : RealPlane₄) :
    baseTorusProjection D.correction D.radius D.radius_pos
      (centralProject D.correction D.radius D.radius_pos
        (straightenedPrescribedCollapse D.correction η (periodPointPunctured D η s hη x))) =
      coordinateProjection 2 ![x 0, x 1] := by
  rw [periodPointPunctured_eq_markedPoint]
  exact baseTorusProjection_straightened_markedPoint
    D.correction D.radius D.radius_pos η s hη
    (D.logarithmic_height s) (D.logarithmic_drift s) hR0 ![x 2, x 3] ![x 0, x 1]

/-- The displayed pair consists of the actual two additive-circle coordinates. -/
theorem baseTorusProjection_straightened_periodPoint_coordinates
    (D : Data) (η : ℝ) (s : LogBase D.radius)
    (hη : ‖exponential (s : ℂ)‖ ≤ η)
    (hR0 : entryNorm (driftMatrix (frozen D.correction) (exponential (s : ℂ))) ≤
      -Real.log ‖exponential (s : ℂ)‖ / 4) (x : RealPlane₄) :
    baseTorusProjection D.correction D.radius D.radius_pos
      (centralProject D.correction D.radius D.radius_pos
        (straightenedPrescribedCollapse D.correction η (periodPointPunctured D η s hη x))) =
      ![(x 0 : AddCircle (1 : ℝ)), (x 1 : AddCircle (1 : ℝ))] := by
  rw [baseTorusProjection_straightened_periodPoint D η s hη hR0]
  ext i
  fin_cases i <;> rfl

/-- The first base coordinate is the literal gamma coordinate modulo integers. -/
theorem baseTorusProjection_straightened_periodPoint_zero
    (D : Data) (η : ℝ) (s : LogBase D.radius)
    (hη : ‖exponential (s : ℂ)‖ ≤ η)
    (hR0 : entryNorm (driftMatrix (frozen D.correction) (exponential (s : ℂ))) ≤
      -Real.log ‖exponential (s : ℂ)‖ / 4) (x : RealPlane₄) :
    baseTorusProjection D.correction D.radius D.radius_pos
      (centralProject D.correction D.radius D.radius_pos
        (straightenedPrescribedCollapse D.correction η (periodPointPunctured D η s hη x))) 0 =
      (x 0 : AddCircle (1 : ℝ)) := by
  rw [baseTorusProjection_straightened_periodPoint D η s hη hR0]
  rfl

/-- The gamma-zero locus is sent into the actual zero-first-coordinate base circle. -/
theorem baseTorusProjection_straightened_periodPoint_gamma_zero
    (D : Data) (η : ℝ) (s : LogBase D.radius)
    (hη : ‖exponential (s : ℂ)‖ ≤ η)
    (hR0 : entryNorm (driftMatrix (frozen D.correction) (exponential (s : ℂ))) ≤
      -Real.log ‖exponential (s : ℂ)‖ / 4) (x : RealPlane₄)
    (hγ : (x 0 : AddCircle (1 : ℝ)) = 0) :
    baseTorusProjection D.correction D.radius D.radius_pos
      (centralProject D.correction D.radius D.radius_pos
        (straightenedPrescribedCollapse D.correction η (periodPointPunctured D η s hη x))) 0 =
      0 := by
  rw [baseTorusProjection_straightened_periodPoint_zero D η s hη hR0, hγ]

/-- A genuine common frozen radius supplies the pointwise inverse bound. -/
theorem baseTorusProjection_straightened_periodPoint_of_smallDrift
    (D : Data) (δ : ℝ) (hR0 : SmallDrift (frozen D.correction) δ)
    (η : ℝ) (s : LogBase D.radius) (hδ : ‖exponential (s : ℂ)‖ < δ)
    (hη : ‖exponential (s : ℂ)‖ ≤ η) (x : RealPlane₄) :
    baseTorusProjection D.correction D.radius D.radius_pos
      (centralProject D.correction D.radius D.radius_pos
        (straightenedPrescribedCollapse D.correction η (periodPointPunctured D η s hη x))) =
      coordinateProjection 2 ![x 0, x 1] :=
  baseTorusProjection_straightened_periodPoint D η s hη
    (hR0 _ (norm_pos_iff.mpr (exponential_ne_zero _)) hδ) x

/-- The geometric identity holds on a uniform punctured neighborhood derived
from the original cusp data; no frozen-radius assumption remains outside it. -/
theorem exists_period_base_radius (D : Data) :
    ∃ δ : ℝ, 0 < δ ∧ δ < D.radius ∧ δ < 1 ∧
      ∀ (η : ℝ) (s : LogBase D.radius), ‖exponential (s : ℂ)‖ < δ →
        ∀ (hη : ‖exponential (s : ℂ)‖ ≤ η) (x : RealPlane₄),
          baseTorusProjection D.correction D.radius D.radius_pos
            (centralProject D.correction D.radius D.radius_pos
              (straightenedPrescribedCollapse D.correction η
                (periodPointPunctured D η s hη x))) =
            coordinateProjection 2 ![x 0, x 1] := by
  obtain ⟨δ, hδ, hδr, hδ1, _, hR0⟩ :=
    exists_common_frozen_radius D.correction D.radius_pos
      (fun i j => (D.holomorphic i j).continuousOn)
  exact ⟨δ, hδ, hδr, hδ1,
    fun η s hs hη x =>
      baseTorusProjection_straightened_periodPoint_of_smallDrift D δ hR0 η s hs hη x⟩

end Wikipedia.HopfProblem.CuspBoundaryTopVanishing
