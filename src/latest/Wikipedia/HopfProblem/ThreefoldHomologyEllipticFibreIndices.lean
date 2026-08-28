import Wikipedia.HopfProblem.ThreefoldHomologyEllipticFibre
import Wikipedia.HopfProblem.EllipticHigherHomologyCoverIndices
import Wikipedia.HopfProblem.EllipticHigherHomologyCoverIndicesTop

/-!
# Integral indices of the actual elliptic fibre attachments

The native small-filling homology quotiented by the image of its actual
boundary fibre is transported to the already computed genuine finite
covering cokernel.  In degrees two and three this gives index one at
the order-three filling and index two at the order-four filling.  In
degree four the index is the actual number of sheets.

These are statements about the literal original filling coefficient.
They do not assign a matrix to arbitrary projective splitting choices.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.EllipticFibre

open SingularMayerVietoris PeriodTorusHigherHomology ThreefoldOverlapMappingTorus
open Wikipedia.HopfProblem.Elliptic
open Elliptic.HigherHomology EllipticFilling Finiteness

private def quotientEqAddEquiv {M : Type*} [AddCommGroup M] [Module ℤ M]
    (p q : Submodule ℤ M) (h : p = q) : (M ⧸ p) ≃+ (M ⧸ q) := by
  subst q
  exact AddEquiv.refl _

private theorem quotientEqAddEquiv_mk {M : Type*} [AddCommGroup M] [Module ℤ M]
    (p q : Submodule ℤ M) (h : p = q) (a : M) :
    quotientEqAddEquiv p q h (Submodule.Quotient.mk a) = Submodule.Quotient.mk a := by
  subst q
  rfl

/-- The actual retracted image is exactly the actual central finite-cover image. -/
theorem fibreToFilling_retracted_range (j : Elliptic.Kind) (n : ℕ) :
    LinearMap.range ((ellipticPieceRetractionHomologyEquiv j n).toLinearMap.comp
        (singularHomologyMap (fibreToFilling (some j)) n)) =
      LinearMap.range (singularHomologyMap
        (periodCover j (specialLocalData j).centralPeriod j.twist
          (mainTwist_admissible j)) n) := by
  rw [fibreToFilling_homology_retraction]
  exact cover_range_comp_of_surjective _ _ (centralPeriodHomologyEquiv j n).surjective

/-- The native actual fibre-attachment cokernel, without replacement of its image. -/
def fibreCapCokernelPeriodEquiv (j : Elliptic.Kind) (n : ℕ) :
    (SingularHomology (localPiece (some (some j))) n ⧸
      LinearMap.range (singularHomologyMap (fibreToFilling (some j)) n)) ≃ₗ[ℤ]
      (SingularHomology (SpecialCentralSurface j) n ⧸
        LinearMap.range (singularHomologyMap
          (periodCover j (specialLocalData j).centralPeriod j.twist
            (mainTwist_admissible j)) n)) := by
  let e := coverCokernelCoordinatesEquiv
    (singularHomologyMap (fibreToFilling (some j)) n)
    (ellipticPieceRetractionHomologyEquiv j n)
  let h := quotientEqAddEquiv _ _ (fibreToFilling_retracted_range j n)
  exact (e.toAddEquiv.trans h).toIntLinearEquiv

@[simp] theorem fibreCapCokernelPeriodEquiv_mk (j : Elliptic.Kind) (n : ℕ)
    (a : SingularHomology (localPiece (some (some j))) n) :
    fibreCapCokernelPeriodEquiv j n (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (ellipticPieceRetractionHomologyEquiv j n a) := by
  change quotientEqAddEquiv _ _ (fibreToFilling_retracted_range j n)
    (Submodule.Quotient.mk (ellipticPieceRetractionHomologyEquiv j n a)) = _
  exact quotientEqAddEquiv_mk _ _ _ _

/-- The actual second fibre-attachment cokernel is its proved one-or-two residue module. -/
def fibreCapH2CokernelEquiv (j : Elliptic.Kind) :
    (SingularHomology (localPiece (some (some j))) 2 ⧸
      LinearMap.range (singularHomologyMap (fibreToFilling (some j)) 2)) ≃ₗ[ℤ]
      ZMod (fibreNormIndex j) :=
  ((fibreCapCokernelPeriodEquiv j 2).toAddEquiv.trans
    (surfacePeriodCoverH2CokernelEquivZMod j
      (specialLocalData j).centralPeriod).toAddEquiv).toIntLinearEquiv

@[simp] theorem fibreCapH2CokernelEquiv_mk (j : Elliptic.Kind)
    (a : SingularHomology (localPiece (some (some j))) 2) :
    fibreCapH2CokernelEquiv j (Submodule.Quotient.mk a) =
      (surfaceH2Equiv j (specialLocalData j).centralPeriod
        (ellipticPieceRetractionHomologyEquiv j 2 a) 1 : ZMod (fibreNormIndex j)) := by
  change surfacePeriodCoverH2CokernelEquivZMod j (specialLocalData j).centralPeriod
    (fibreCapCokernelPeriodEquiv j 2 (Submodule.Quotient.mk a)) = _
  rw [fibreCapCokernelPeriodEquiv_mk, surfacePeriodCoverH2CokernelEquivZMod_mk]

/-- The genuine degree-three attachment has the same computed integral quotient. -/
def fibreCapH3CokernelEquiv (j : Elliptic.Kind) :
    (SingularHomology (localPiece (some (some j))) 3 ⧸
      LinearMap.range (singularHomologyMap (fibreToFilling (some j)) 3)) ≃ₗ[ℤ]
      ZMod (fibreNormIndex j) :=
  ((fibreCapCokernelPeriodEquiv j 3).toAddEquiv.trans
    (surfacePeriodCoverH3CokernelEquivZMod j
      (specialLocalData j).centralPeriod).toAddEquiv).toIntLinearEquiv

@[simp] theorem fibreCapH3CokernelEquiv_mk (j : Elliptic.Kind)
    (a : SingularHomology (localPiece (some (some j))) 3) :
    fibreCapH3CokernelEquiv j (Submodule.Quotient.mk a) =
      (surfaceH3Equiv j (specialLocalData j).centralPeriod
        (ellipticPieceRetractionHomologyEquiv j 3 a) 1 : ZMod (fibreNormIndex j)) := by
  change surfacePeriodCoverH3CokernelEquivZMod j (specialLocalData j).centralPeriod
    (fibreCapCokernelPeriodEquiv j 3 (Submodule.Quotient.mk a)) = _
  rw [fibreCapCokernelPeriodEquiv_mk, surfacePeriodCoverH3CokernelEquivZMod_mk]

/-- The top fibre-attachment quotient retains the actual elliptic covering order. -/
def fibreCapH4CokernelEquiv (j : Elliptic.Kind) :
    (SingularHomology (localPiece (some (some j))) 4 ⧸
      LinearMap.range (singularHomologyMap (fibreToFilling (some j)) 4)) ≃ₗ[ℤ]
      ZMod j.order :=
  ((fibreCapCokernelPeriodEquiv j 4).toAddEquiv.trans
    (surfacePeriodCoverH4CokernelEquivZMod j
      (specialLocalData j).centralPeriod).toAddEquiv).toIntLinearEquiv

@[simp] theorem fibreCapH4CokernelEquiv_mk (j : Elliptic.Kind)
    (a : SingularHomology (localPiece (some (some j))) 4) :
    fibreCapH4CokernelEquiv j (Submodule.Quotient.mk a) =
      (surfaceH4Equiv j (specialLocalData j).centralPeriod
        (ellipticPieceRetractionHomologyEquiv j 4 a) : ZMod j.order) := by
  change surfacePeriodCoverH4CokernelEquivZMod j (specialLocalData j).centralPeriod
    (fibreCapCokernelPeriodEquiv j 4 (Submodule.Quotient.mk a)) = _
  rw [fibreCapCokernelPeriodEquiv_mk, surfacePeriodCoverH4CokernelEquivZMod_apply_mk]

theorem fibreCap_h2_range_index (j : Elliptic.Kind) :
    (LinearMap.range (singularHomologyMap (fibreToFilling (some j)) 2)).toAddSubgroup.index =
      fibreNormIndex j :=
  (Nat.card_congr (fibreCapH2CokernelEquiv j).toEquiv).trans (Nat.card_zmod _)

theorem fibreCap_h3_range_index (j : Elliptic.Kind) :
    (LinearMap.range (singularHomologyMap (fibreToFilling (some j)) 3)).toAddSubgroup.index =
      fibreNormIndex j :=
  (Nat.card_congr (fibreCapH3CokernelEquiv j).toEquiv).trans (Nat.card_zmod _)

theorem fibreCap_h4_range_index (j : Elliptic.Kind) :
    (LinearMap.range (singularHomologyMap (fibreToFilling (some j)) 4)).toAddSubgroup.index =
      j.order :=
  (Nat.card_congr (fibreCapH4CokernelEquiv j).toEquiv).trans (Nat.card_zmod _)

/-- The actual order-three fibre attachment is onto in degree two. -/
theorem fibreCap_h2_surjective_three :
    Function.Surjective (singularHomologyMap (fibreToFilling (some .three)) 2) := by
  intro a
  obtain ⟨b, hb⟩ := surfacePeriodCover_h2_surjective_three
    (specialLocalData .three).centralPeriod (ellipticPieceRetractionHomologyEquiv .three 2 a)
  refine ⟨(centralPeriodHomologyEquiv .three 2).symm b, ?_⟩
  apply (ellipticPieceRetractionHomologyEquiv .three 2).injective
  have h := LinearMap.congr_fun (fibreToFilling_homology_retraction .three 2)
    ((centralPeriodHomologyEquiv .three 2).symm b)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    hb] using h

/-- The same genuine surjectivity holds in degree three. -/
theorem fibreCap_h3_surjective_three :
    Function.Surjective (singularHomologyMap (fibreToFilling (some .three)) 3) := by
  intro a
  obtain ⟨b, hb⟩ := surfacePeriodCover_h3_surjective_three
    (specialLocalData .three).centralPeriod (ellipticPieceRetractionHomologyEquiv .three 3 a)
  refine ⟨(centralPeriodHomologyEquiv .three 3).symm b, ?_⟩
  apply (ellipticPieceRetractionHomologyEquiv .three 3).injective
  have h := LinearMap.congr_fun (fibreToFilling_homology_retraction .three 3)
    ((centralPeriodHomologyEquiv .three 3).symm b)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    hb] using h

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.EllipticFibre
