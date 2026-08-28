import Wikipedia.HopfProblem.ThreefoldHomologyStarEquivalences
import Wikipedia.HopfProblem.SingularMayerVietoris

/-!
# The star maps are the actual singular Mayer–Vietoris maps

Each commuting square is proved from the literal geometric maps.  The
finite-product identifications therefore retain the positive regular
component, the three negative filling components, and the actual sum of
the four maps into the constructed threefold.
-/

noncomputable section

open scoped ContinuousMap

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology

open SingularMayerVietoris PeriodTorusHigherHomology

/-- The regular-coordinate equivalence preserves the actual ambient inclusion. -/
theorem starRegularHomologyEquiv_ambient (n : ℕ) :
    (singularHomologyMap originalRegularInclusion n).comp
        (starRegularHomologyEquiv n).toLinearMap =
      singularHomologyMap (subtypeInclusion (liftedPatch none : Set Space)) n := by
  change (singularHomologyMap originalRegularInclusion n).comp
      (singularHomologyMap (originalRegularPatchHomeomorph.symm :
        C(liftedPatch none, SpecialRegularFamily)) n) = _
  rw [← singularHomologyMap_comp]
  apply congrArg (fun f : C(liftedPatch none, Space) => singularHomologyMap f n)
  apply ContinuousMap.ext
  intro x
  exact congrArg Subtype.val (originalRegularPatchHomeomorph.apply_symm_apply x)

/-- The actual filling-sum map on one component. -/
theorem starFillingsToSpaceHomologyMap_single (n : ℕ) (i : Puncture)
    (a : SingularHomology (localPiece (some i)) n) :
    starFillingsToSpaceHomologyMap n (Pi.single i a) =
      singularHomologyMap (originalPieceInclusion (some i)) n a := by
  have h := starRightHomologyMap_single n i (0 : SingularHomology SpecialRegularFamily n) a
  change singularHomologyMap originalRegularInclusion n 0 +
      starFillingsToSpaceHomologyMap n (Pi.single i a) =
    singularHomologyMap originalRegularInclusion n 0 +
      singularHomologyMap (originalPieceInclusion (some i)) n a at h
  simpa only [map_zero, zero_add] using h

/-- The filling-coordinate equivalence preserves the actual ambient inclusion. -/
theorem starFillingsHomologyEquiv_ambient (n : ℕ) :
    (starFillingsToSpaceHomologyMap n).comp
        (starFillingsHomologyEquiv n).toLinearMap =
      singularHomologyMap (subtypeInclusion (starFillings : Set Space)) n := by
  apply starFillingsHomology_hom_ext n
  intro i a
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    starFillingsHomologyEquiv_inclusion, starFillingsToSpaceHomologyMap_single]
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, fillingToStar_ambient]

/-- On each actual overlap component the left cover inclusion is the
original overlap-to-regular-family map. -/
theorem starRegularHomologyEquiv_overlapToStar (n : ℕ) (i : Puncture)
    (a : SingularHomology (RegularOverlap i) n) :
    starRegularHomologyEquiv n
        (singularHomologyMap starOverlapToRegularPatch n
          (singularHomologyMap (overlapToStar i) n a)) =
      singularHomologyMap (overlapToRegularFamily i) n a := by
  rw [starRegularHomologyEquiv_apply, ← LinearMap.comp_apply,
    ← singularHomologyMap_comp]
  change singularHomologyMap starOverlapToRegular n
    (singularHomologyMap (overlapToStar i) n a) = _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
    starOverlapToRegular_overlapToStar]

/-- The right cover inclusion sends each overlap component to precisely
its original filling component. -/
theorem starFillingsHomologyEquiv_overlapToStar (n : ℕ) (i : Puncture)
    (a : SingularHomology (RegularOverlap i) n) :
    starFillingsHomologyEquiv n
        (singularHomologyMap starOverlapToFillings n
          (singularHomologyMap (overlapToStar i) n a)) =
      Pi.single i (singularHomologyMap (overlapToFilling i) n a) := by
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
    starOverlapToFillings_overlapToStar, singularHomologyMap_comp,
    LinearMap.comp_apply, starFillingsHomologyEquiv_inclusion]

/-- The finite-product signed overlap map is exactly the genuine
singular Mayer–Vietoris map under the actual homeomorphisms. -/
theorem starLeftHomologyMap_comparison (n : ℕ) :
    (starLeftHomologyMap n).comp (starOverlapHomologyEquiv n).toLinearMap =
      (starPairHomologyEquiv n).toLinearMap.comp
        (leftHomologyMap (liftedPatch none : Set Space) (starFillings : Set Space) n) := by
  apply starOverlapHomology_hom_ext n
  intro i a
  have hr : starPairHomologyEquiv n
      (leftHomologyMap (liftedPatch none : Set Space) (starFillings : Set Space) n
        (singularHomologyMap (overlapToStar i) n a)) =
      (singularHomologyMap (overlapToRegularFamily i) n a,
        Pi.single i (-singularHomologyMap (overlapToFilling i) n a)) := by
    have hraw := leftHomologyMap_apply (liftedPatch none : Set Space)
      (starFillings : Set Space) n (singularHomologyMap (overlapToStar i) n a)
    refine (congrArg (starPairHomologyEquiv n) hraw).trans ?_
    change (starRegularHomologyEquiv n
        (singularHomologyMap starOverlapToRegularPatch n
          (singularHomologyMap (overlapToStar i) n a)),
      starFillingsHomologyEquiv n
        (-singularHomologyMap starOverlapToFillings n
          (singularHomologyMap (overlapToStar i) n a))) = _
    rw [map_neg, starRegularHomologyEquiv_overlapToStar,
      starFillingsHomologyEquiv_overlapToStar, Pi.single_neg]
  exact (congrArg (starLeftHomologyMap n)
    (starOverlapHomologyEquiv_inclusion n i a)).trans
      ((starLeftHomologyMap_single n i a).trans hr.symm)

/-- The map into the actual global homology is the native sum of
the two cover inclusions, with all original filling components retained. -/
theorem starRightHomologyMap_comparison (n : ℕ) :
    (starRightHomologyMap n).comp (starPairHomologyEquiv n).toLinearMap =
      rightHomologyMap (liftedPatch none : Set Space) (starFillings : Set Space) n := by
  apply LinearMap.ext
  intro a
  change singularHomologyMap originalRegularInclusion n
      (starRegularHomologyEquiv n a.1) +
    starFillingsToSpaceHomologyMap n (starFillingsHomologyEquiv n a.2) = _
  rw [rightHomologyMap_apply]
  exact congrArg₂ (· + ·)
    (LinearMap.congr_fun (starRegularHomologyEquiv_ambient n) a.1)
    (LinearMap.congr_fun (starFillingsHomologyEquiv_ambient n) a.2)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology
