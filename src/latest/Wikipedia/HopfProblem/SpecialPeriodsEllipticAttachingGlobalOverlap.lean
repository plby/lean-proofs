import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingFibres
import Wikipedia.HopfProblem.EllipticLogGaugeFundamentalGroupGauge
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldEllipticOverlaps

/-!
# The actual elliptic attaching loops in the regular family

We evaluate the already constructed small-overlap biholomorphism on the
literal logarithmic meridian and fibre-translation loops.  The logarithmic
gauge cancels their negative-logarithmic starting coordinate.  The remaining
local-to-global map uses the original inverse Cayley chart and leaves the
real torus coordinate unchanged.  Thus the meridian is the zero section
over the actual upstairs root path, and the fibre loop is the original
integer-period loop at its initial point, with no change of lattice basis.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped unitInterval

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry

open Elliptic Elliptic.LogGauge EllipticFilling CuspUniformization TrianglePeriodFamily

attribute [local instance] specialRegularFamilyChartedSpace specialEllipticPieceChartedSpace

/-- The actual point of the regular upper-half-plane cover along the root path. -/
def attachingUpstairsPoint (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im) (t : I) :
    TriangleRegularPoint :=
  localBase j (logMeridianRootStar (j := j) s₀ hs₀ t)

theorem attachingUpstairsPoint_continuous (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    Continuous (attachingUpstairsPoint j s₀ hs₀) :=
  (localBase_continuous j).comp (logMeridianRootStar_continuous s₀ hs₀)

@[simp] theorem attachingUpstairsPoint_val (j : Kind) (s₀ : ℂ)
    (hs₀ : 0 < s₀.im) (t : I) :
    (attachingUpstairsPoint j s₀ hs₀ t : ℍ) =
      ((Triangle.ellipticNeighborhoodChart j).symm (logMeridianRoot j s₀ hs₀ t) : ℍ) := rfl

theorem attachingUpstairsPoint_mem_neighborhood (j : Kind) (s₀ : ℂ)
    (hs₀ : 0 < s₀.im) (t : I) :
    (attachingUpstairsPoint j s₀ hs₀ t : ℍ) ∈ Triangle.ellipticNeighborhood j :=
  localBase_mem_neighborhood j _

/-- The root path ends at exactly the chosen elliptic deck generator. -/
theorem attachingUpstairsPoint_one (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    attachingUpstairsPoint j s₀ hs₀ 1 =
      Triangle.ellipticGenerator j • attachingUpstairsPoint j s₀ hs₀ 0 := by
  have hr : logMeridianRootStar (j := j) s₀ hs₀ 1 =
      puncturedRotation j (logMeridianRootStar (j := j) s₀ hs₀ 0) :=
    Subtype.ext (logMeridianRoot_one j s₀ hs₀)
  unfold attachingUpstairsPoint
  rw [hr, localBase_rotation]

/-- The exact logarithmic coordinate at the common attaching basepoint. -/
theorem attachingFlatBase_eq_negativeLog (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im) :
    attachingFlatBase j s₀ hs₀ =
      ((specialLocalData j).periods.periodEquiv (logMeridianRoot j s₀ hs₀ 0)).symm
        (-s₀ • periodVector (specialLocalData j).periods j.twist
          (logMeridianRoot j s₀ hs₀ 0)) := by
  change ((specialLocalData j).periods.periodEquiv _).symm
    (-logMeridianParameter j s₀ 0 • periodVector (specialLocalData j).periods j.twist _) = _
  rw [logMeridianParameter_zero]

/-- The existing full punctured overlap is the existing logarithmic gauge
followed by the original untwisted quotient comparison. -/
theorem specialPuncturedOverlap_eq_gauge (j : Kind)
    (x : MainFillingStar specialPeriodMap j specialPeriodMap_generator₁
      specialPeriodMap_generator₂) :
    (puncturedFillingBiholomorph specialPeriodMap j specialPeriodMap_generator₁
      specialPeriodMap_generator₂ x).val =
      (tautologicalOverlapBiholomorph specialPeriodMap j specialPeriodMap_generator₁
        specialPeriodMap_generator₂
        (fillingToTautologicalBiholomorph (specialLocalData j) j.twist
          (mainTwist_admissible j) x)).val := rfl

/-- In the regular family, the actual logarithmic attaching meridian is
the zero section over the actual upstairs root trajectory. -/
theorem smallOverlap_attachingLoop (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) (t : I) :
    smallOverlap specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂
      specialBaseCover j (attachingLoop j s₀ hs₀ hr t) =
        (regularData specialPeriodMap specialPeriodMap_generator₁
          specialPeriodMap_generator₂).quotient (attachingUpstairsPoint j s₀ hs₀ t, 0) := by
  rw [smallOverlap_apply_mainStar specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂ specialBaseCover j _
    (parameter_attachingLoop_ne_zero j s₀ hs₀ hr t), specialPuncturedOverlap_eq_gauge]
  change (tautologicalOverlapBiholomorph specialPeriodMap j specialPeriodMap_generator₁
    specialPeriodMap_generator₂
    (fillingToTautologicalBiholomorph (specialLocalData j) j.twist (mainTwist_admissible j)
      (logMeridianFillingPoint (specialLocalData j) j.twist
        (mainTwist_admissible j) s₀ hs₀ t))).val = _
  rw [fillingToTautological_logMeridian]
  change (tautologicalOverlapBiholomorph specialPeriodMap j specialPeriodMap_generator₁
    specialPeriodMap_generator₂
    (starProject (specialLocalData j) 0 (Matrix.mulVec_zero j.matrix)
      (zeroSection (specialLocalData j).periods (logMeridianRootStar (j := j) s₀ hs₀ t)))).val = _
  exact congrArg Subtype.val (tautologicalOverlapBiholomorph_project specialPeriodMap j
    specialPeriodMap_generator₁ specialPeriodMap_generator₂
    (zeroSection (specialLocalData j).periods (logMeridianRootStar (j := j) s₀ hs₀ t)))

/-- The fibre attaching loop keeps the same integral coordinates in the
actual regular family; the logarithmic displacement cancels exactly. -/
theorem smallOverlap_attachingFibreLoop (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j))
    (w : Lattice) (t : I) :
    smallOverlap specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂
      specialBaseCover j (attachingFibreLoop j s₀ hs₀ hr w t) =
        (regularData specialPeriodMap specialPeriodMap_generator₁
          specialPeriodMap_generator₂).quotient (attachingUpstairsPoint j s₀ hs₀ 0,
            standardLattice.mkQ ((t : ℝ) • realCast w)) := by
  rw [smallOverlap_apply_mainStar specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂ specialBaseCover j _
    (parameter_attachingFibreLoop_ne_zero j s₀ hs₀ hr w t), specialPuncturedOverlap_eq_gauge]
  change (tautologicalOverlapBiholomorph specialPeriodMap j specialPeriodMap_generator₁
    specialPeriodMap_generator₂
    (fillingToTautologicalBiholomorph (specialLocalData j) j.twist (mainTwist_admissible j)
      (fibreTranslationFillingPoint (specialLocalData j) j.twist (mainTwist_admissible j)
        (logMeridianRootStar (j := j) s₀ hs₀ 0) (attachingFlatBase j s₀ hs₀) w t))).val = _
  rw [attachingFlatBase_eq_negativeLog]
  have hg := fillingToTautological_fibreTranslation (specialLocalData j) j.twist
    (mainTwist_admissible j) (logMeridianRootStar (j := j) s₀ hs₀ 0) w s₀
    (logMeridianRoot_zero j s₀ hs₀).symm t
  refine (congrArg (fun q : TautologicalStar (specialLocalData j) =>
    (tautologicalOverlapBiholomorph specialPeriodMap j specialPeriodMap_generator₁
      specialPeriodMap_generator₂ q).val) hg).trans ?_
  refine (congrArg Subtype.val (tautologicalOverlapBiholomorph_project specialPeriodMap j
    specialPeriodMap_generator₁ specialPeriodMap_generator₂
    (fibreTranslationFamilyStar (specialLocalData j)
      (logMeridianRootStar (j := j) s₀ hs₀ 0) 0 w t))).trans ?_
  change (regularData specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂).quotient (attachingUpstairsPoint j s₀ hs₀ 0,
        standardLattice.mkQ (0 + (t : ℝ) • realCast w)) = _
  rw [zero_add]

/-- The exact meridian formula for the overlap used by the global threefold. -/
theorem specialEllipticOverlap_attachingLoop (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) (t : I) :
    specialEllipticOverlap j (attachingLoop j s₀ hs₀ hr t) =
      (regularData specialPeriodMap specialPeriodMap_generator₁
        specialPeriodMap_generator₂).quotient (attachingUpstairsPoint j s₀ hs₀ t, 0) :=
  smallOverlap_attachingLoop j s₀ hs₀ hr t

/-- The exact fibre formula for the overlap used by the global threefold. -/
theorem specialEllipticOverlap_attachingFibreLoop (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j))
    (w : Lattice) (t : I) :
    specialEllipticOverlap j (attachingFibreLoop j s₀ hs₀ hr w t) =
      (regularData specialPeriodMap specialPeriodMap_generator₁
        specialPeriodMap_generator₂).quotient (attachingUpstairsPoint j s₀ hs₀ 0,
          standardLattice.mkQ ((t : ℝ) • realCast w)) :=
  smallOverlap_attachingFibreLoop j s₀ hs₀ hr w t

/-- The attaching basepoint lands on the actual zero section, exactly. -/
theorem specialEllipticOverlap_attachingBasepoint (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) :
    specialEllipticOverlap j (attachingBasepoint j s₀ hs₀ hr) =
      (regularData specialPeriodMap specialPeriodMap_generator₁
        specialPeriodMap_generator₂).quotient (attachingUpstairsPoint j s₀ hs₀ 0, 0) :=
  specialEllipticOverlap_attachingLoop j s₀ hs₀ hr 0

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry
