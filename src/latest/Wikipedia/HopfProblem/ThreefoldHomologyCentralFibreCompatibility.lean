import Wikipedia.HopfProblem.ThreefoldHomologyCapEliminationFibre
import Wikipedia.HopfProblem.ThreefoldHomologyEllipticFibre
import Wikipedia.HopfProblem.ThreefoldHomologyDeltaSweepCentralCover
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCommonFibre

/-!
# The original regular fibre and the actual central elliptic finite covers

The original boundary maps agree pointwise in the glued threefold.  Their
actual regular fibre maps are the common normalized marked fibre map on
homology.  The genuine central deformation retraction then identifies the
filling fibre map with the original central finite cover followed by the
original central inclusion.  This gives the full global equality in every
degree, without a choice of homology splitting or a Wang-only comparison.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.CentralFibreCompatibility

open SingularMayerVietoris PeriodTorusHigherHomology ThreefoldOverlapMappingTorus
open TrianglePeriodFamily TrianglePeriodFamily.Homology TrianglePeriodFamily.Boundary
open CapElimination EllipticFilling Finiteness

/-- The two literal boundary fibres agree in the original glued space. -/
theorem globalFibre_maps_agree (i : Puncture) :
    originalRegularInclusion.comp (fibreToRegularFamily i) =
      (originalPieceInclusion (some i)).comp (fibreToFilling i) := by
  have h := congrArg
    (fun f : C(Boundary i, Space) =>
      f.comp (MappingTorus.HomologyCover.fibreInclusion (monodromy i)))
    (boundary_maps_agree i)
  simpa only [fibreToRegularFamily, fibreToFilling, ContinuousMap.comp_assoc] using h

/-- The actual normalized regular fibre has the same global homology map through any filling. -/
theorem regularFibreIntoSpace_homology_filling (i : Puncture) (n : ℕ) :
    singularHomologyMap regularFibreIntoSpace n =
      (singularHomologyMap (originalPieceInclusion (some i)) n).comp
        (singularHomologyMap (fibreToFilling i) n) := by
  rw [regularFibreIntoSpace_homology,
    ← fibreToRegularFamily_homology_common i n,
    ← singularHomologyMap_comp, globalFibre_maps_agree, singularHomologyMap_comp]

/-- The actual cap retraction sends the original fibre map to the original central cover. -/
theorem fibreToFilling_homology_centralRetraction (j : Elliptic.Kind) (n : ℕ) :
    (ellipticPieceRetractionHomologyEquiv j n).toLinearMap.comp
        (singularHomologyMap (fibreToFilling (some j)) n) =
      singularHomologyMap (EllipticFibre.centralRealCover j) n := by
  have h := congrArg (fun f : C(RealTorus₄, SpecialCentralSurface j) =>
    singularHomologyMap f n) (EllipticFibre.fibreToFilling_centralRetraction j)
  exact (singularHomologyMap_comp (fibreToFilling (some j))
    (EllipticGeometry.pieceSurfaceRetraction j) n).symm.trans h

/-- Undoing that genuine retraction is exactly the actual central-surface inclusion. -/
theorem fibreToFilling_homology_central (j : Elliptic.Kind) (n : ℕ) :
    singularHomologyMap (fibreToFilling (some j)) n =
      (singularHomologyMap (EllipticGeometry.centralSurfaceIntoPiece j) n).comp
        (singularHomologyMap (EllipticFibre.centralRealCover j) n) := by
  apply LinearMap.ext
  intro a
  have h := congrArg (ellipticPieceRetractionHomologyEquiv j n).symm
    (LinearMap.congr_fun (fibreToFilling_homology_centralRetraction j n) a)
  change singularHomologyMap (fibreToFilling (some j)) n a =
    (ellipticPieceRetractionHomologyEquiv j n).symm
      (singularHomologyMap (EllipticFibre.centralRealCover j) n a)
  exact ((ellipticPieceRetractionHomologyEquiv j n).symm_apply_apply _).symm.trans h

/-- The delta-action API uses the same original central-surface inclusion into the threefold. -/
theorem centralInclusionMap_eq (j : Elliptic.Kind) :
    DeltaSweep.centralInclusionMap j =
      (originalPieceInclusion (some (some j))).comp
        (EllipticGeometry.centralSurfaceIntoPiece j) := rfl

/-- The delta-action finite cover retains exactly the same real-period coordinates. -/
theorem centralFlatPeriodCover_eq (j : Elliptic.Kind) :
    DeltaSweep.centralFlatPeriodCover j = EllipticFibre.centralRealCover j := rfl

/-- The full global regular-fibre map factors through either original central finite cover. -/
theorem regularFibreIntoSpace_homology_eq_central (j : Elliptic.Kind) (n : ℕ) :
    singularHomologyMap regularFibreIntoSpace n =
      (singularHomologyMap (DeltaSweep.centralInclusionMap j) n).comp
        (singularHomologyMap (DeltaSweep.centralFlatPeriodCover j) n) := by
  have hi : singularHomologyMap (DeltaSweep.centralInclusionMap j) n =
      (singularHomologyMap (originalPieceInclusion (some (some j))) n).comp
        (singularHomologyMap (EllipticGeometry.centralSurfaceIntoPiece j) n) :=
    singularHomologyMap_comp (EllipticGeometry.centralSurfaceIntoPiece j)
      (originalPieceInclusion (some (some j))) n
  apply LinearMap.ext
  intro a
  calc
    singularHomologyMap regularFibreIntoSpace n a =
        singularHomologyMap (originalPieceInclusion (some (some j))) n
          (singularHomologyMap (fibreToFilling (some j)) n a) :=
      LinearMap.congr_fun (regularFibreIntoSpace_homology_filling (some j) n) a
    _ = singularHomologyMap (originalPieceInclusion (some (some j))) n
        (singularHomologyMap (EllipticGeometry.centralSurfaceIntoPiece j) n
          (singularHomologyMap (EllipticFibre.centralRealCover j) n a)) :=
      congrArg (singularHomologyMap (originalPieceInclusion (some (some j))) n)
        (LinearMap.congr_fun (fibreToFilling_homology_central j n) a)
    _ = singularHomologyMap (DeltaSweep.centralInclusionMap j) n
        (singularHomologyMap (DeltaSweep.centralFlatPeriodCover j) n a) :=
      (LinearMap.congr_fun hi (singularHomologyMap (EllipticFibre.centralRealCover j) n a)).symm

/-- Pointwise compatibility keeps the actual marked fibre class and both genuine geometric maps. -/
theorem regularFibreIntoSpace_homology_eq_central_apply (j : Elliptic.Kind) (n : ℕ)
    (a : SingularHomology RealTorus₄ n) :
    singularHomologyMap regularFibreIntoSpace n a =
      singularHomologyMap (DeltaSweep.centralInclusionMap j) n
        (singularHomologyMap (DeltaSweep.centralFlatPeriodCover j) n a) :=
  LinearMap.congr_fun (regularFibreIntoSpace_homology_eq_central j n) a

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.CentralFibreCompatibility
