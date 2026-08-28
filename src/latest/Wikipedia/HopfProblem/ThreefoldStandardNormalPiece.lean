import Wikipedia.HopfProblem.CuspCircleNormalTrivializationStandard
import Wikipedia.HopfProblem.StandardSixSphereCircleModelTubeHomeomorph

/-!
# The actual normal piece as a literal piece of the standard six-sphere

These maps identify the original fixed-curve neighbourhood with the actual
equatorial tube in the standard sphere. The original compact normal disk
corresponds to normal radius one half, inside the same open chart, and its
unchanged boundary parametrization has the exact standard boundary formula.

Only the normal piece is identified here. No map on the complementary piece
or identification of the whole threefold is asserted.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.StandardNormalPiece

open CuspCircleNormalTrivialization StandardSixSphereCircleModel

attribute [local instance] SpecialPeriods.Threefold.chartedSpace

/-- The actual open normal neighbourhood maps to the original equatorial sphere chart. -/
def openHomeomorph : fixedCurveNeighborhood ≃ₜ ↥(Tube.openTube 1) :=
  standardNeighborhoodDiffeomorph.toHomeomorph.symm.trans (Tube.openHomeomorph 1 le_rfl)

@[simp] theorem openHomeomorph_parametrization (p : StandardOpenNormalProduct) :
    (openHomeomorph (standardNeighborhoodDiffeomorph p)).val.val =
      Tube.ambient p.1 (p.2 : RealFour.Space) := by
  change (Tube.openHomeomorph 1 le_rfl
    (standardNeighborhoodDiffeomorph.symm (standardNeighborhoodDiffeomorph p))).val.val = _
  rw [Diffeomorph.symm_apply_apply]
  rfl

/-- The normal coordinate is the original normal chart coordinate, not a new marking. -/
@[simp] theorem openHomeomorph_normal (x : fixedCurveNeighborhood) :
    normal (openHomeomorph x).val.val =
      ((standardNeighborhoodDiffeomorph.symm x).2 : RealFour.Space) :=
  Tube.normal_ambient _ _

/-- The original fixed curve maps exactly to the literal equatorial two-sphere. -/
theorem openHomeomorph_mem_equator_iff (x : fixedCurveNeighborhood) :
    (openHomeomorph x).val ∈ equator ↔
      (x : Space) ∈ CuspGeometry.doubleCurve 1 := by
  change normal (openHomeomorph x).val.val = 0 ↔ _
  rw [openHomeomorph_normal]
  exact standardNeighborhoodDiffeomorph_inverse_normal_zero_iff x

/-- Half-scaling of the standard closed disk; the base and all normal directions are retained. -/
def closedProductHomeomorph : StandardClosedNormalProduct ≃ₜ Tube.ClosedDomain (1 / 2) :=
  (Homeomorph.refl _).prodCongr
    (Radial.closedBallHomeomorph (E := RealFour.Space) (1 / 2) (by norm_num))

/-- The original compact normal piece is homeomorphic to a literal closed tube in `S⁶`. -/
def closedHomeomorph : closedDiskNeighborhood ≃ₜ ↥(Tube.closedTube (1 / 2)) :=
  standardClosedDiskNeighborhoodHomeomorph.symm.trans
    (closedProductHomeomorph.trans (Tube.closedHomeomorph (1 / 2) (by norm_num)))

@[simp] theorem closedHomeomorph_parametrization (p : StandardClosedNormalProduct) :
    (closedHomeomorph (standardClosedDiskNeighborhoodHomeomorph p)).val.val =
      Tube.ambient p.1 ((1 / 2 : ℝ) • (p.2 : RealFour.Space)) := by
  change (Tube.closedHomeomorph (1 / 2) (by norm_num) (closedProductHomeomorph
    (standardClosedDiskNeighborhoodHomeomorph.symm
      (standardClosedDiskNeighborhoodHomeomorph p)))).val.val = _
  rw [Homeomorph.symm_apply_apply]
  rfl

/-- The literal inclusion of the original compact piece into its original open neighbourhood. -/
def closedIntoOpen (x : closedDiskNeighborhood) : fixedCurveNeighborhood :=
  ⟨x.val, closedDiskNeighborhood_subset_open x.property⟩

@[simp] theorem closedIntoOpen_coe (x : closedDiskNeighborhood) :
    (closedIntoOpen x : Space) = x.val := rfl

theorem closedIntoOpen_parametrization (p : StandardClosedNormalProduct) :
    closedIntoOpen (standardClosedDiskNeighborhoodHomeomorph p) =
      standardNeighborhoodDiffeomorph (standardClosedIntoOpen p) :=
  Subtype.ext (standardClosedDiskMap_eq_open_chart p)

/-- The closed identification is the restriction of the same original open chart. -/
theorem openHomeomorph_closedIntoOpen (x : closedDiskNeighborhood) :
    (openHomeomorph (closedIntoOpen x)).val = (closedHomeomorph x).val := by
  obtain ⟨p, rfl⟩ := standardClosedDiskNeighborhoodHomeomorph.surjective x
  apply Subtype.ext
  rw [closedIntoOpen_parametrization, openHomeomorph_parametrization,
    closedHomeomorph_parametrization]
  rfl

/-- The preexisting actual boundary marking becomes precisely the standard sphere marking. -/
theorem closedHomeomorph_boundary (p : StandardNormalBoundary) :
    (closedHomeomorph (standardClosedDiskNeighborhoodHomeomorph
      (standardBoundaryIntoClosedDisk p))).val =
        (boundaryPoint (1 / 2) (by norm_num) (by norm_num) p).val := by
  apply Subtype.ext
  rw [closedHomeomorph_parametrization, boundaryPoint_val_val]
  change Tube.ambient p.1 ((1 / 2 : ℝ) • (p.2 : RealFour.Space)) =
    boundaryAmbient (1 / 2) p
  simp only [Tube.ambient, Tube.baseFactor, boundaryAmbient, boundaryBaseRadius,
    norm_smul, Real.norm_eq_abs, normalSphere_norm, mul_one]
  norm_num

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.StandardNormalPiece
