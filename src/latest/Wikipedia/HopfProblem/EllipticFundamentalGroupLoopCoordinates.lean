import Wikipedia.HopfProblem.EllipticFundamentalGroupCoordinates
import Wikipedia.HopfProblem.EllipticFundamentalGroupAction

/-!
# Explicit coordinates on the actual elliptic fundamental groups

The actual surface and filling fundamental groups inherit the unique
affine normal forms through the established deck-group isomorphisms.
Their multiplication and inversion are consequently the proved coordinate
formulas, not an assumed presentation.

The group isomorphism removes the opposite-group convention by inversion.
Accordingly, the endpoint of a lifted loop is the action of the inverse
of its assigned normal form. This sign convention is stated explicitly.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic

section Surface

variable (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates)

/-- The unique normal-form coordinates of the actual surface fundamental
group, obtained through its genuine affine universal cover. -/
def surfaceFundamentalGroupCoordinateEquiv :
    FundamentalGroup (Surface j p v hv) (affineCoverProjection j p v hv y) ≃
      Lattice × Fin j.order :=
  (surfaceFundamentalGroupDeckEquiv j p v hv y).toEquiv.trans
    (deckNormalFormEquiv j v hv).symm

/-- Multiplication in the actual surface fundamental group has the
monodromy-and-carry coordinate formula. -/
theorem surfaceFundamentalGroupCoordinateEquiv_mul
    (γ δ : FundamentalGroup (Surface j p v hv) (affineCoverProjection j p v hv y)) :
    surfaceFundamentalGroupCoordinateEquiv j p v hv y (γ * δ) =
      coordinateProduct j v (surfaceFundamentalGroupCoordinateEquiv j p v hv y γ)
        (surfaceFundamentalGroupCoordinateEquiv j p v hv y δ) := by
  change (deckNormalFormEquiv j v hv).symm
    (surfaceFundamentalGroupDeckEquiv j p v hv y (γ * δ)) = _
  rw [map_mul]
  exact deckNormalFormEquiv_symm_mul j v hv _ _

theorem surfaceFundamentalGroupCoordinateEquiv_inv
    (γ : FundamentalGroup (Surface j p v hv) (affineCoverProjection j p v hv y)) :
    surfaceFundamentalGroupCoordinateEquiv j p v hv y γ⁻¹ =
      coordinateInverse j v (surfaceFundamentalGroupCoordinateEquiv j p v hv y γ) := by
  change (deckNormalFormEquiv j v hv).symm
    (surfaceFundamentalGroupDeckEquiv j p v hv y γ⁻¹) = _
  rw [map_inv]
  exact deckNormalFormEquiv_symm_inv j v hv _

/-- Reconstructing the normal form gives exactly the deck element assigned
to the loop class. -/
theorem surfaceFundamentalGroupCoordinateEquiv_normalForm
    (γ : FundamentalGroup (Surface j p v hv) (affineCoverProjection j p v hv y)) :
    deckNormalForm j v (surfaceFundamentalGroupCoordinateEquiv j p v hv y γ) =
      surfaceFundamentalGroupDeckEquiv j p v hv y γ :=
  (deckNormalFormEquiv j v hv).apply_symm_apply _

theorem surfaceFundamentalGroupCoordinateEquiv_unique_normalForm
    (γ : FundamentalGroup (Surface j p v hv) (affineCoverProjection j p v hv y)) :
    ∃! a : Lattice × Fin j.order,
      surfaceFundamentalGroupDeckEquiv j p v hv y γ = deckNormalForm j v a := by
  refine ⟨surfaceFundamentalGroupCoordinateEquiv j p v hv y γ,
    (surfaceFundamentalGroupCoordinateEquiv_normalForm j p v hv y γ).symm, ?_⟩
  intro a ha
  apply deckNormalForm_injective j v hv
  exact ha.symm.trans (surfaceFundamentalGroupCoordinateEquiv_normalForm j p v hv y γ).symm

/-- The inverse coordinate marking acts on the chosen lift to produce the
endpoint of the lifted loop. Inversion here is required by the opposite
group appearing in monodromy of a left deck action. -/
theorem surfaceFundamentalGroupCoordinateEquiv_monodromy
    (γ : FundamentalGroup (Surface j p v hv) (affineCoverProjection j p v hv y)) :
    let a := coordinateInverse j v (surfaceFundamentalGroupCoordinateEquiv j p v hv y γ)
    realCast a.1 + (flatAffine j v)^[a.2.val] y =
      ((affineCoverProjection_isQuotientCoveringMap j p v hv).isCoveringMap.monodromy γ
        ⟨y, rfl⟩ : RealCoordinates) := by
  dsimp only
  have h := surfaceFundamentalGroupDeckEquiv_monodromy j p v hv y γ
  rw [← surfaceFundamentalGroupCoordinateEquiv_normalForm j p v hv y γ,
    deckNormalForm_inv_coordinates j v hv.1] at h
  change affineNormalForm j v
    (coordinateInverse j v (surfaceFundamentalGroupCoordinateEquiv j p v hv y γ)).1
    (coordinateInverse j v (surfaceFundamentalGroupCoordinateEquiv j p v hv y γ)).2.val y = _ at h
  rw [affineNormalForm_apply] at h
  exact h

end Surface

section Filling

variable (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) (y : RealCoordinates)

/-- Normal-form coordinates of the actual filling fundamental group,
through the established deformation retraction onto its central surface. -/
def fillingFundamentalGroupCoordinateEquiv :
    FundamentalGroup (Filling j v hv)
      (centralFibreInclusion j v hv (affineCoverProjection j (centralPeriod j) v hv y)) ≃
        Lattice × Fin j.order :=
  (fillingFundamentalGroupDeckEquiv j v hv y).toEquiv.trans
    (deckNormalFormEquiv j v hv).symm

theorem fillingFundamentalGroupCoordinateEquiv_mul
    (γ δ : FundamentalGroup (Filling j v hv)
      (centralFibreInclusion j v hv (affineCoverProjection j (centralPeriod j) v hv y))) :
    fillingFundamentalGroupCoordinateEquiv j v hv y (γ * δ) =
      coordinateProduct j v (fillingFundamentalGroupCoordinateEquiv j v hv y γ)
        (fillingFundamentalGroupCoordinateEquiv j v hv y δ) := by
  change (deckNormalFormEquiv j v hv).symm
    (fillingFundamentalGroupDeckEquiv j v hv y (γ * δ)) = _
  rw [map_mul]
  exact deckNormalFormEquiv_symm_mul j v hv _ _

theorem fillingFundamentalGroupCoordinateEquiv_inv
    (γ : FundamentalGroup (Filling j v hv)
      (centralFibreInclusion j v hv (affineCoverProjection j (centralPeriod j) v hv y))) :
    fillingFundamentalGroupCoordinateEquiv j v hv y γ⁻¹ =
      coordinateInverse j v (fillingFundamentalGroupCoordinateEquiv j v hv y γ) := by
  change (deckNormalFormEquiv j v hv).symm
    (fillingFundamentalGroupDeckEquiv j v hv y γ⁻¹) = _
  rw [map_inv]
  exact deckNormalFormEquiv_symm_inv j v hv _

theorem fillingFundamentalGroupCoordinateEquiv_normalForm
    (γ : FundamentalGroup (Filling j v hv)
      (centralFibreInclusion j v hv (affineCoverProjection j (centralPeriod j) v hv y))) :
    deckNormalForm j v (fillingFundamentalGroupCoordinateEquiv j v hv y γ) =
      fillingFundamentalGroupDeckEquiv j v hv y γ :=
  (deckNormalFormEquiv j v hv).apply_symm_apply _

theorem fillingFundamentalGroupCoordinateEquiv_unique_normalForm
    (γ : FundamentalGroup (Filling j v hv)
      (centralFibreInclusion j v hv (affineCoverProjection j (centralPeriod j) v hv y))) :
    ∃! a : Lattice × Fin j.order,
      fillingFundamentalGroupDeckEquiv j v hv y γ = deckNormalForm j v a := by
  refine ⟨fillingFundamentalGroupCoordinateEquiv j v hv y γ,
    (fillingFundamentalGroupCoordinateEquiv_normalForm j v hv y γ).symm, ?_⟩
  intro a ha
  apply deckNormalForm_injective j v hv
  exact ha.symm.trans (fillingFundamentalGroupCoordinateEquiv_normalForm j v hv y γ).symm

/-- Including a loop from the central surface leaves its normal-form
coordinates unchanged. -/
theorem fillingFundamentalGroupCoordinateEquiv_surface
    (γ : FundamentalGroup (Surface j (centralPeriod j) v hv)
      (affineCoverProjection j (centralPeriod j) v hv y)) :
    fillingFundamentalGroupCoordinateEquiv j v hv y
      (fillingSurfaceFundamentalGroupEquiv j v hv
        (affineCoverProjection j (centralPeriod j) v hv y) γ) =
      surfaceFundamentalGroupCoordinateEquiv j (centralPeriod j) v hv y γ := by
  change (deckNormalFormEquiv j v hv).symm
    (surfaceFundamentalGroupDeckEquiv j (centralPeriod j) v hv y
      ((fillingSurfaceFundamentalGroupEquiv j v hv
        (affineCoverProjection j (centralPeriod j) v hv y)).symm
        (fillingSurfaceFundamentalGroupEquiv j v hv
          (affineCoverProjection j (centralPeriod j) v hv y) γ))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

end Filling

end Wikipedia.HopfProblem.Elliptic
