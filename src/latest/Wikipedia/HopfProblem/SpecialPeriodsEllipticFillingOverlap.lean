import Wikipedia.HopfProblem.SpecialPeriodsEllipticFillingOverlapTopology
import Wikipedia.HopfProblem.EllipticLogGauge

/-!
# Full punctured elliptic fillings over the actual compact triangle base

The actual untwisted quotient is biholomorphic to the entire regular
family over the punctured elliptic neighborhood.  Composing with the
proved logarithmic gauge gives the full punctured overlap for the main
affine filling.  Its map to the compact base is exactly the inverse of
the original elliptic quotient chart applied to the filling coordinate.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling

open Elliptic Elliptic.LogGauge TrianglePeriodFamily

local notation "IF" => modelWithCornersSelf ℂ FamilyModel

variable (P : HolomorphicPeriodMap ℂ ℍ) (j : Kind)
    (h₁ : ∀ z : ℍ, P.point (Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (Triangle.generatorTwoSL • z) = (P.point z).step₂)

theorem regularMapToOverlap_isLocalDiffeomorph :
    letI := (localPeriods P j).totalChartedSpace
    letI := (regularData P h₁ h₂).chartedSpace (regularCovering P h₁ h₂)
    IsLocalDiffeomorph IF IF ω (regularMapToOverlap P j h₁ h₂) := by
  let := (localPeriods P j).totalChartedSpace
  let := (regularData P h₁ h₂).chartedSpace (regularCovering P h₁ h₂)
  exact isLocalDiffeomorph_codRestrictOpens IF IF
    (regularMap_isLocalDiffeomorph P j h₁ h₂) (regularOverlap P j h₁ h₂)
    (regularMap_mem_overlap P j h₁ h₂)

/-- Local biholomorphy descends through the actual finite covering
projection.  The target retains its inherited regular-family atlas. -/
theorem tautologicalToOverlap_isLocalDiffeomorph :
    letI := starChartedSpace (localData P h₁ h₂ j) 0 (Matrix.mulVec_zero j.matrix)
    letI := (regularData P h₁ h₂).chartedSpace (regularCovering P h₁ h₂)
    IsLocalDiffeomorph IF IF ω (tautologicalToOverlap P j h₁ h₂) := by
  let L := localData P h₁ h₂ j
  let := L.periods.totalChartedSpace
  let := L.periods.totalSpace_isManifold
  let := starAction L 0 (Matrix.mulVec_zero j.matrix)
  let := starChartedSpace L 0 (Matrix.mulVec_zero j.matrix)
  let := (regularData P h₁ h₂).chartedSpace (regularCovering P h₁ h₂)
  have hq : IsLocalDiffeomorph IF IF ω (starProject L 0 (Matrix.mulVec_zero j.matrix)) :=
    CoveringQuotient.project_isLocalDiffeomorph
      (starCoveringMap L 0 (Matrix.mulVec_zero j.matrix))
      (starAction_holomorphic L 0 (Matrix.mulVec_zero j.matrix))
  intro y
  obtain ⟨x, rfl⟩ := starProject_surjective L 0 (Matrix.mulVec_zero j.matrix) y
  exact localDiffeomorphAt_of_comp (hq x)
    (regularMapToOverlap_isLocalDiffeomorph P j h₁ h₂ x)

/-- The full actual untwisted punctured quotient is biholomorphic to
the literal whole overlap in the regular triangle period family. -/
def tautologicalOverlapBiholomorph :
    letI := starChartedSpace (localData P h₁ h₂ j) 0 (Matrix.mulVec_zero j.matrix)
    letI := (regularData P h₁ h₂).chartedSpace (regularCovering P h₁ h₂)
    Diffeomorph IF IF (TautologicalStar (localData P h₁ h₂ j))
      (regularOverlap P j h₁ h₂) ω := by
  let := starChartedSpace (localData P h₁ h₂ j) 0 (Matrix.mulVec_zero j.matrix)
  let := (regularData P h₁ h₂).chartedSpace (regularCovering P h₁ h₂)
  exact (tautologicalToOverlap_isLocalDiffeomorph P j h₁ h₂).diffeomorphOfBijective
    (tautologicalToOverlap_bijective P j h₁ h₂)

@[simp] theorem tautologicalOverlapBiholomorph_project
    (x : FamilyStar (localPeriods P j)) :
    tautologicalOverlapBiholomorph P j h₁ h₂
        (starProject (localData P h₁ h₂ j) 0 (Matrix.mulVec_zero j.matrix) x) =
      regularMapToOverlap P j h₁ h₂ x := rfl

/-- Both quotient constructions use the same original powered Cayley
coordinate on their full punctured bases. -/
theorem tautologicalOverlapBiholomorph_coordinate
    (x : TautologicalStar (localData P h₁ h₂ j)) :
    Triangle.ellipticFullChart j
        (triangleRegularToOrbit ((regularData P h₁ h₂).projection
          (tautologicalOverlapBiholomorph P j h₁ h₂ x).val)) =
      ((starProjection (localData P h₁ h₂ j) 0 (Matrix.mulVec_zero j.matrix) x : Disc) : ℂ) := by
  obtain ⟨y, rfl⟩ := starProject_surjective (localData P h₁ h₂ j) 0
    (Matrix.mulVec_zero j.matrix) x
  change Triangle.ellipticFullChart j
      (triangleRegularToOrbit (baseQuotient j ⟨y.1.1, y.2⟩)) = (y.1.1 : ℂ) ^ j.order
  exact ellipticFullChart_baseQuotient j ⟨y.1.1, y.2⟩

/-- The literal complement of the central fibre of the actual main
elliptic filling. -/
abbrev MainFillingStar :=
  FillingStar (localData P h₁ h₂ j) j.twist (mainTwist_admissible j)

/-- The actual logarithmic gauge followed by the full local-to-global
quotient comparison.  Neither the local periods nor the overlap map are
inputs to this construction. -/
def puncturedFillingBiholomorph :
    letI := fillingChartedSpace P h₁ h₂ j
    letI := (regularData P h₁ h₂).chartedSpace (regularCovering P h₁ h₂)
    Diffeomorph IF IF (MainFillingStar P j h₁ h₂) (regularOverlap P j h₁ h₂) ω := by
  let L := localData P h₁ h₂ j
  let := fillingChartedSpace P h₁ h₂ j
  let := starChartedSpace L 0 (Matrix.mulVec_zero j.matrix)
  let := (regularData P h₁ h₂).chartedSpace (regularCovering P h₁ h₂)
  exact (mainFillingToTautologicalBiholomorph L).trans
    (tautologicalOverlapBiholomorph P j h₁ h₂)

theorem puncturedFillingBiholomorph_coordinate (x : MainFillingStar P j h₁ h₂) :
    Triangle.ellipticFullChart j
        (triangleRegularToOrbit ((regularData P h₁ h₂).projection
          (puncturedFillingBiholomorph P j h₁ h₂ x).val)) =
      (fillingProjection P h₁ h₂ j x.val : ℂ) := by
  let L := localData P h₁ h₂ j
  have h := tautologicalOverlapBiholomorph_coordinate P j h₁ h₂
    (mainFillingToTautologicalBiholomorph L x)
  have hb := congrArg (fun z : BaseStar => ((z : Disc) : ℂ))
    (mainFillingToTautologicalBiholomorph_base L x)
  exact h.trans hb

/-- The actual regular family projection into the compact base, using
the already established inclusions of the two orbit quotients. -/
def regularCompactProjection : (regularData P h₁ h₂).Space → TriangleCompactifiedOrbitSpace :=
  fun x => triangleOpenInclusion (triangleRegularToOrbit ((regularData P h₁ h₂).projection x))

/-- Exact commutation over the compact triangle base.  In particular any
smaller coordinate disc can be used by literally restricting this full
overlap, without reparametrizing its root coordinate. -/
theorem puncturedFillingBiholomorph_base (x : MainFillingStar P j h₁ h₂) :
    regularCompactProjection P h₁ h₂ (puncturedFillingBiholomorph P j h₁ h₂ x).val =
      (Triangle.ellipticCompactifiedChart j).symm
        (fillingProjection P h₁ h₂ j x.val : ℂ) := by
  let y := puncturedFillingBiholomorph P j h₁ h₂ x
  have hs : regularCompactProjection P h₁ h₂ y.val ∈
      (Triangle.ellipticCompactifiedChart j).source :=
    (regularBasePatch_mem_iff_compactifiedChart j _).mp y.property
  have hc : Triangle.ellipticCompactifiedChart j
        (regularCompactProjection P h₁ h₂ y.val) =
      (fillingProjection P h₁ h₂ j x.val : ℂ) := by
    rw [regularCompactProjection, Triangle.ellipticCompactifiedChart_openInclusion]
    exact puncturedFillingBiholomorph_coordinate P j h₁ h₂ x
  exact ((Triangle.ellipticCompactifiedChart j).left_inv hs).symm.trans
    (congrArg (Triangle.ellipticCompactifiedChart j).symm hc)

end Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling
