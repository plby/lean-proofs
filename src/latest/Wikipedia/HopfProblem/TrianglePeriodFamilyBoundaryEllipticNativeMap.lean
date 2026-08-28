import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticNativeRoot
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticGaugeCylinder
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryFibreEquivariance
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusEllipticHomotopy

/-!
# The original elliptic boundary map in native logarithmic coordinates

Choose the already constructed small logarithmic parameter and retain its
actual norm and real phase.  The original radius-and-phase boundary map
then has the exact inverse-Cayley and logarithmic-gauge representative.
Its fibre equivariance follows from that actual descended map.  The proved
whole lifted square consequently gives a genuine homotopy to the normalized
boundary curve, with the full original gauge unchanged.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary

open SpecialPeriods SpecialPeriods.Triangle Elliptic Elliptic.LogGauge
open SpecialPeriods.EllipticFilling SpecialPeriods.Threefold
open SpecialPeriods.Threefold.EllipticGeometry ThreefoldOverlapMappingTorus
open SingularMayerVietoris PeriodTorusHigherHomology

local notation "Dsp" =>
  regularData specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂

attribute [local instance] specialRegularFamilyChartedSpace specialEllipticPieceChartedSpace
  specialFullFillingChartedSpace

/-- The literal punctured-piece boundary at the original logarithmic root,
with a further fixed real phase for the later slit-cover comparison. -/
def nativeBoundaryInclusion (j : Kind) (τ : ℝ) :
    C(ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary j, PuncturedPiece (some j)) :=
  ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryInclusionAt j
    (nativeBoundaryRootRadius j) (nativeBoundaryRootPhase j + τ)

/-- The unchanged original map into the actual regular family. -/
def nativeRegularBoundaryMap (j : Kind) (τ : ℝ) :
    C(ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary j, (Dsp).Space) :=
  ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToRegularFamilyAt j
    (nativeBoundaryRootRadius j) (nativeBoundaryRootPhase j + τ)

/-- On every real-cylinder point this is exactly the original native
family quotient at the literal logarithmic root. -/
theorem nativeBoundaryInclusion_mk (j : Kind) (τ t : ℝ) (x : RealTorus₄) :
    ((nativeBoundaryInclusion j τ (MappingTorus.mk (flatTorusAffine j j.twist) (t, x))).val :
      SpecialEllipticPiece j).val =
        (specialLocalData j).quotient j.twist (mainTwist_admissible j)
          (nativeClockwiseRoot j (-(t + τ)), x) := by
  have h := ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryInclusionAt_mk j
    (nativeBoundaryRootRadius j) (nativeBoundaryRootPhase j + τ) t x
  have hr : root j.order (specialBaseCover.radius (some j)) (nativeBoundaryRootRadius j)
      (((t + (nativeBoundaryRootPhase j + τ)) / j.order : ℝ) :
        ThreefoldOverlapMappingTorus.Circle) =
        nativeClockwiseRoot j (-(t + τ)) := by
    rw [show t + (nativeBoundaryRootPhase j + τ) =
      (t + τ) + nativeBoundaryRootPhase j by ring]
    exact nativeBoundaryRoot_eq j (t + τ)
  exact h.trans (congrArg ((specialLocalData j).quotient j.twist (mainTwist_admissible j))
    (Prod.ext hr rfl))

/-- The actual original attaching map applies exactly the existing
logarithmic gauge to every point of this native family cylinder. -/
theorem nativeRegularBoundaryMap_gauge (j : Kind) (τ t : ℝ) (x : RealTorus₄) :
    nativeRegularBoundaryMap j τ (MappingTorus.mk (flatTorusAffine j j.twist) (t, x)) =
      regularMap specialPeriodMap j specialPeriodMap_generator₁ specialPeriodMap_generator₂
        (gaugeMap (specialLocalData j).periods j.twist (nativeGaugeFamilyStar j τ (t, x))) := by
  let y := nativeBoundaryInclusion j τ (MappingTorus.mk (flatTorusAffine j j.twist) (t, x))
  change puncturedPieceToRegular (some j) y = _
  rw [ThreefoldOverlapMappingTorus.Elliptic.puncturedPieceToRegular_elliptic]
  have hx : (specialFullFillingProjection j (y.val : SpecialEllipticPiece j).val : ℂ) ≠ 0 :=
    (ThreefoldOverlapMappingTorus.Elliptic.specialPiece_regular_iff j y.val).mp y.property
  have hstar : (⟨(y.val : SpecialEllipticPiece j).val, hx⟩ :
      MainFillingStar specialPeriodMap j specialPeriodMap_generator₁ specialPeriodMap_generator₂) =
      fillingStarProject (specialLocalData j) j.twist (mainTwist_admissible j)
        (nativeGaugeFamilyStar j τ (t, x)) := by
    apply Subtype.ext
    exact nativeBoundaryInclusion_mk j τ t x
  change smallOverlap specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂
    specialBaseCover j y.val = _
  rw [smallOverlap_apply_mainStar specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂ specialBaseCover j y.val hx, hstar]
  change (tautologicalOverlapBiholomorph specialPeriodMap j specialPeriodMap_generator₁
    specialPeriodMap_generator₂
    (fillingToTautologicalBiholomorph (specialLocalData j) j.twist (mainTwist_admissible j)
      (fillingStarProject (specialLocalData j) j.twist (mainTwist_admissible j)
        (nativeGaugeFamilyStar j τ (t, x))))).val = _
  rw [fillingToTautologicalBiholomorph_project]
  exact congrArg Subtype.val (tautologicalOverlapBiholomorph_project specialPeriodMap j
    specialPeriodMap_generator₁ specialPeriodMap_generator₂
    (gaugeMap (specialLocalData j).periods j.twist (nativeGaugeFamilyStar j τ (t, x))))

/-- The literal full native boundary formula in the original real-period
coordinates, with the complete actual logarithmic translation. -/
theorem nativeRegularBoundaryMap_mk (j : Kind) (τ t : ℝ) (x : RealTorus₄) :
    nativeRegularBoundaryMap j τ (MappingTorus.mk (flatTorusAffine j j.twist) (t, x)) =
      (Dsp).quotient (nativeShiftedBase j τ t, nativeGaugeCylinder j τ (t, x)) := by
  rw [nativeRegularBoundaryMap_gauge]
  rfl

/-- The actual original boundary coefficient is unchanged by the proved
radius-and-phase homotopy to these native coordinates. -/
theorem boundaryRegularHomologyMap_native (j : Kind) (τ : ℝ) (n : ℕ) :
    boundaryRegularHomologyMap (some j) n =
      singularHomologyMap (nativeRegularBoundaryMap j τ) n :=
  ThreefoldOverlapMappingTorus.Elliptic.boundaryRegularHomologyMap_at j
    (nativeBoundaryRootRadius j) (nativeBoundaryRootPhase j + τ) n

/-- Equivariance of the entire native gauge is forced by the actual
boundary map and the proven native base deck transformation. -/
theorem nativeGaugeCylinder_deck (j : Kind) (τ : ℝ) (k : ℤ) (p : ℝ × RealTorus₄) :
    nativeGaugeCylinder j τ (MappingTorus.deck (flatTorusAffine j j.twist) k p) =
      triangleTorusHomeomorph (ellipticGenerator j ^ (-k)) (nativeGaugeCylinder j τ p) := by
  exact fibreMap_deck_of_actual Dsp (flatTorusAffine j j.twist)
    (nativeRegularBoundaryMap j τ) (nativeShiftedBase j τ) (nativeGaugeCylinder j τ)
    (ellipticGenerator j) (fun p => nativeRegularBoundaryMap_mk j τ p.1 p.2)
    (nativeShiftedBase_translate j τ) k p

/-- The endpoint of the actual lifted base homotopy, with its original
time-dependent fibre gauge still present. -/
def normalizedEllipticBoundaryMap (j : Kind) (τ : ℝ) :
    C(ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary j, (Dsp).Space) :=
  familyBoundaryMap Dsp (flatTorusAffine j j.twist)
    (baseHomotopySlice (nativeShiftedSquareLift j τ) 1) (nativeGaugeCylinder j τ)
    (ellipticGenerator j) (nativeShiftedSquareLift_translate j τ 1)
    (nativeGaugeCylinder_deck j τ)

/-- The original native boundary and this normalized-curve map are
genuinely homotopic as maps of the entire actual mapping torus. -/
theorem nativeRegularBoundaryMap_homotopic_normalized (j : Kind) (τ : ℝ) :
    (nativeRegularBoundaryMap j τ).Homotopic (normalizedEllipticBoundaryMap j τ) :=
  actualBoundary_homotopic_of_base Dsp (flatTorusAffine j j.twist)
    (nativeRegularBoundaryMap j τ) (nativeShiftedBase j τ) (nativeGaugeCylinder j τ)
    (ellipticGenerator j) (fun p => nativeRegularBoundaryMap_mk j τ p.1 p.2)
    (nativeShiftedBase_translate j τ) (nativeShiftedSquareLift j τ)
    (nativeShiftedSquareLift_zero j τ) (nativeShiftedSquareLift_translate j τ)

/-- Equality of the literal global attachment coefficient and the map
whose slit-cover geometry is now explicit, in every actual homology degree. -/
theorem boundaryRegularHomologyMap_normalized (j : Kind) (τ : ℝ) (n : ℕ) :
    boundaryRegularHomologyMap (some j) n =
      singularHomologyMap (normalizedEllipticBoundaryMap j τ) n :=
  (boundaryRegularHomologyMap_native j τ n).trans
    (homotopic_homologyMap (nativeRegularBoundaryMap_homotopic_normalized j τ) n)

/-- Every representative of the normalized boundary still has its
original full gauge and the actual lifted final base point. -/
theorem normalizedEllipticBoundaryMap_mk (j : Kind) (τ t : ℝ) (x : RealTorus₄) :
    normalizedEllipticBoundaryMap j τ (MappingTorus.mk (flatTorusAffine j j.twist) (t, x)) =
      (Dsp).quotient (nativeShiftedSquareLift j τ (1, t), nativeGaugeCylinder j τ (t, x)) := rfl

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary
