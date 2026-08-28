import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapProductSection
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTranslations

/-!
# Exact cancellation of the linear gauge on the actual elliptic cap section

The original section fibre has real coordinates `(s/m) • twist + (0,k)`.
Adding the gauge at its actual reversed boundary time `-s` cancels its
twist component exactly in the lattice quotient, leaving the fixed
positive coordinate three-torus. This is a literal equality of maps,
not merely an equality of homology classes.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticGaugeLinearization

open Elliptic Elliptic.HigherHomology SpecialPeriods EllipticCapProduct
open PeriodTorusHigherHomology

/-- At every real time, the original section has this exact real lift. -/
theorem capSectionFibre_coordinateProjection (j : Kind) (s : ℝ) (k : FibreCoordinates) :
    capSectionFibre j s (coordinateProjection 3 k) =
      standardLattice.mkQ ((s / (j.order : ℝ)) • realCast j.twist + Fin.cons 0 k) := by
  rw [capSectionFibre_apply, splitFlatTorusHomeomorph_symm_coordinateProjection,
    splitRealCoordinates_symm_apply]

/-- The actual reversed-time linear gauge cancels the section's twist
coordinate exactly, for every point of the three-torus. -/
theorem capSectionFibre_linearGauge_cancel (j : Kind) (s : ℝ) (y : ProductTorus 3) :
    capSectionFibre j s y +
        standardLattice.mkQ ((-s / (j.order : ℝ)) • realCast j.twist) =
      capSectionFibre j 0 y := by
  obtain ⟨k, rfl⟩ := coordinateProjection_surjective 3 y
  rw [capSectionFibre_coordinateProjection, capSectionFibre_zero_coordinateProjection,
    ← map_add]
  apply congrArg standardLattice.mkQ
  rw [neg_div, neg_smul]
  abel

/-- Fixed-time cancellation as an equality of genuine continuous maps. -/
theorem capSectionFibre_linearGauge_cancel_map (j : Kind) (s : ℝ) :
    (rightTranslation
      (standardLattice.mkQ ((-s / (j.order : ℝ)) • realCast j.twist))).comp
        (capSectionFibre j s) = capSectionFibre j 0 := by
  apply ContinuousMap.ext
  intro y
  exact capSectionFibre_linearGauge_cancel j s y

/-- The complete cancelled section cylinder, with both real time and the
actual three-torus point retained in its defining formula. -/
def capSectionLinearGaugeCancelledCylinder (j : Kind) :
    C(ℝ × ProductTorus 3, RealTorus₄) where
  toFun p := capSectionFibre j p.1 p.2 +
    standardLattice.mkQ ((-p.1 / (j.order : ℝ)) • realCast j.twist)
  continuous_toFun := by
    have he : (fun p : ℝ × ProductTorus 3 => capSectionFibre j p.1 p.2 +
        standardLattice.mkQ ((-p.1 / (j.order : ℝ)) • realCast j.twist)) =
        (fun p => capSectionFibre j 0 p.2) :=
      funext (fun p => capSectionFibre_linearGauge_cancel j p.1 p.2)
    rw [he]
    exact (capSectionFibre j 0).continuous.comp continuous_snd

@[simp] theorem capSectionLinearGaugeCancelledCylinder_apply
    (j : Kind) (s : ℝ) (y : ProductTorus 3) :
    capSectionLinearGaugeCancelledCylinder j (s, y) = capSectionFibre j 0 y :=
  capSectionFibre_linearGauge_cancel j s y

/-- The complete actual cancelled cylinder is independent of the real time. -/
theorem capSectionLinearGaugeCancelledCylinder_eq (j : Kind) :
    capSectionLinearGaugeCancelledCylinder j =
      (capSectionFibre j 0).comp
        (ContinuousMap.snd : C(ℝ × ProductTorus 3, ProductTorus 3)) := by
  apply ContinuousMap.ext
  intro p
  exact capSectionFibre_linearGauge_cancel j p.1 p.2

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticGaugeLinearization
