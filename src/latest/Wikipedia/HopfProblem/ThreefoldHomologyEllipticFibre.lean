import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusEllipticCap
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusHomology
import Wikipedia.HopfProblem.ThreefoldHomologyFinitenessElliptic
import Wikipedia.HopfProblem.EllipticHigherHomologyRetraction

/-!
# The actual elliptic boundary fibre maps to the original finite cover

The real period coordinate of the original punctured overlap survives
the radial retraction of the actual small elliptic filling.  On the
boundary fibre the retracted map is therefore the literal finite
covering of the central surface.  The following equalities transport
this fact to native integral singular homology in every degree.

There is no assigned attachment matrix and no change of fibre basis.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.EllipticFibre

open SingularMayerVietoris PeriodTorusHigherHomology ThreefoldOverlapMappingTorus
open Wikipedia.HopfProblem.Elliptic
open Elliptic.HigherHomology EllipticFilling Finiteness

/-- The actual finite quotient map, expressed in the original real-period coordinates. -/
def centralRealCover (j : Elliptic.Kind) :
    C(RealTorus₄, ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface j) :=
  (periodCover j (specialLocalData j).centralPeriod j.twist
    (Elliptic.mainTwist_admissible j)).comp
      ⟨flatTorusPeriodHomeomorph (specialLocalData j).centralPeriod.val,
        (flatTorusPeriodHomeomorph (specialLocalData j).centralPeriod.val).continuous⟩

@[simp] theorem centralRealCover_apply (j : Elliptic.Kind) (x : RealTorus₄) :
    centralRealCover j x =
      Elliptic.surfaceProjection j (specialLocalData j).centralPeriod j.twist
        (Elliptic.mainTwist_admissible j)
        (flatTorusPeriodHomeomorph (specialLocalData j).centralPeriod.val x) := rfl

/-- On the actual time-zero boundary fibre, the cap map is the original finite quotient. -/
theorem centralBoundary_fibre (j : Elliptic.Kind) :
    (ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToCentral j).comp
        (MappingTorus.HomologyCover.fibreInclusion (monodromy (some j))) =
      centralRealCover j := by
  apply ContinuousMap.ext
  intro x
  exact ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToCentral_mk j 0 x

/-- This is an equality of the literal maps into the original small filling and central surface. -/
theorem fibreToFilling_centralRetraction (j : Elliptic.Kind) :
    (EllipticGeometry.pieceSurfaceRetraction j).comp (fibreToFilling (some j)) =
      centralRealCover j := by
  rw [fibreToFilling, boundaryToFilling_elliptic]
  exact centralBoundary_fibre j

/-- The real-period homeomorphism transports actual homology, in every degree. -/
def centralPeriodHomologyEquiv (j : Elliptic.Kind) (n : ℕ) :
    SingularHomology RealTorus₄ n ≃ₗ[ℤ]
      SingularHomology (specialLocalData j).centralPeriod.val.Torus n :=
  homeomorphHomologyEquiv
    (flatTorusPeriodHomeomorph (specialLocalData j).centralPeriod.val) n

@[simp] theorem centralPeriodHomologyEquiv_toLinearMap (j : Elliptic.Kind) (n : ℕ) :
    (centralPeriodHomologyEquiv j n).toLinearMap =
      singularHomologyMap
        ⟨flatTorusPeriodHomeomorph (specialLocalData j).centralPeriod.val,
          (flatTorusPeriodHomeomorph (specialLocalData j).centralPeriod.val).continuous⟩ n := rfl

/-- The actual retracted fibre homology map is the genuine central finite-cover map. -/
theorem fibreToFilling_homology_retraction (j : Elliptic.Kind) (n : ℕ) :
    (ellipticPieceRetractionHomologyEquiv j n).toLinearMap.comp
        (singularHomologyMap (fibreToFilling (some j)) n) =
      (singularHomologyMap (periodCover j (specialLocalData j).centralPeriod j.twist
        (Elliptic.mainTwist_admissible j)) n).comp
          (centralPeriodHomologyEquiv j n).toLinearMap := by
  have h₁ := singularHomologyMap_comp (fibreToFilling (some j))
    (EllipticGeometry.pieceSurfaceRetraction j) n
  have h₀ := congrArg (fun f : C(RealTorus₄, SpecialCentralSurface j) =>
    singularHomologyMap f n) (fibreToFilling_centralRetraction j)
  have h₂ := singularHomologyMap_comp
    (⟨flatTorusPeriodHomeomorph (specialLocalData j).centralPeriod.val,
      (flatTorusPeriodHomeomorph (specialLocalData j).centralPeriod.val).continuous⟩ :
      C(RealTorus₄, (specialLocalData j).centralPeriod.val.Torus))
    (periodCover j (specialLocalData j).centralPeriod j.twist
      (Elliptic.mainTwist_admissible j)) n
  exact h₁.symm.trans (h₀.trans h₂)

/-- All-degree attachment compatibility on the original Wang fibre classes. -/
theorem boundaryFilling_fibre_retraction (j : Elliptic.Kind) (n : ℕ)
    (a : SingularHomology RealTorus₄ n) :
    ellipticPieceRetractionHomologyEquiv j n
        (boundaryFillingHomologyMap (some j) n
          (MappingTorusHomology.fibreHomologyMap (monodromy (some j)) n a)) =
      singularHomologyMap (periodCover j (specialLocalData j).centralPeriod j.twist
        (Elliptic.mainTwist_admissible j)) n (centralPeriodHomologyEquiv j n a) := by
  have hf := LinearMap.congr_fun (boundaryFillingHomologyMap_fibre (some j) n) a
  change boundaryFillingHomologyMap (some j) n
    (MappingTorusHomology.fibreHomologyMap (monodromy (some j)) n a) =
      singularHomologyMap (fibreToFilling (some j)) n a at hf
  rw [hf]
  exact LinearMap.congr_fun (fibreToFilling_homology_retraction j n) a

/-- Undoing the actual retraction retains the exact original filling coefficient. -/
theorem boundaryFilling_fibre (j : Elliptic.Kind) (n : ℕ)
    (a : SingularHomology RealTorus₄ n) :
    boundaryFillingHomologyMap (some j) n
        (MappingTorusHomology.fibreHomologyMap (monodromy (some j)) n a) =
      (ellipticPieceRetractionHomologyEquiv j n).symm
        (singularHomologyMap (periodCover j (specialLocalData j).centralPeriod j.twist
          (Elliptic.mainTwist_admissible j)) n (centralPeriodHomologyEquiv j n a)) := by
  apply (ellipticPieceRetractionHomologyEquiv j n).injective
  rw [boundaryFilling_fibre_retraction, LinearEquiv.apply_symm_apply]

/-- The actual fibre-to-filling map kills exactly the classes killed by that finite cover. -/
theorem fibreToFilling_homology_eq_zero_iff (j : Elliptic.Kind) (n : ℕ)
    (a : SingularHomology RealTorus₄ n) :
    singularHomologyMap (fibreToFilling (some j)) n a = 0 ↔
      singularHomologyMap (periodCover j (specialLocalData j).centralPeriod j.twist
        (Elliptic.mainTwist_admissible j)) n (centralPeriodHomologyEquiv j n a) = 0 := by
  have h := LinearMap.congr_fun (fibreToFilling_homology_retraction j n) a
  change ellipticPieceRetractionHomologyEquiv j n
    (singularHomologyMap (fibreToFilling (some j)) n a) =
      singularHomologyMap (periodCover j (specialLocalData j).centralPeriod j.twist
        (Elliptic.mainTwist_admissible j)) n (centralPeriodHomologyEquiv j n a) at h
  rw [← h]
  exact (ellipticPieceRetractionHomologyEquiv j n).map_eq_zero_iff.symm

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.EllipticFibre
