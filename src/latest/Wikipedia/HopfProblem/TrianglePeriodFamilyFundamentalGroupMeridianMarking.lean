import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupMeridianLifts

/-!
# The constructed source meridians are a joint free basis

The actual normalized projection sends the two jointly based geometric
loops to the two explicit planar semicircle loops. The proved planar
free marking therefore gives an equivalence of actual fundamental
groups with the free group on two letters, with exact generator values.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians

open SpecialPeriods SpecialPeriods.Triangle FreeMeridianMarking

private def pointedHomeomorphFundamentalGroupEquiv
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {x : X} {y : Y} (h : e x = y) :
    FundamentalGroup X x ≃* FundamentalGroup Y y where
  __ := FundamentalGroup.mapOfEq ⟨e, e.continuous⟩ h
  invFun := FundamentalGroup.mapOfEq ⟨e.symm, e.symm.continuous⟩
    ((congrArg e.symm h).symm.trans (e.symm_apply_apply x))
  left_inv γ := by
    change FundamentalGroup.mapOfEq ⟨e.symm, e.symm.continuous⟩
      ((congrArg e.symm h).symm.trans (e.symm_apply_apply x))
      (FundamentalGroup.mapOfEq ⟨e, e.continuous⟩ h γ) = γ
    rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.mapOfEq_apply]
    obtain ⟨γ⟩ := γ
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    exact e.symm_apply_apply (γ t)
  right_inv γ := by
    change FundamentalGroup.mapOfEq ⟨e, e.continuous⟩ h
      (FundamentalGroup.mapOfEq ⟨e.symm, e.symm.continuous⟩
        ((congrArg e.symm h).symm.trans (e.symm_apply_apply x)) γ) = γ
    rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.mapOfEq_apply]
    obtain ⟨γ⟩ := γ
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    exact e.apply_symm_apply (γ t)

/-- The actual regular-plane homeomorphism, at the canonical lifted basepoint. -/
def compatibleBasePlaneEquiv :
    FundamentalGroup TriangleRegularQuotient
      (triangleRegularProject normalizedRegularMeridianBasepoint) ≃*
        FundamentalGroup TwicePuncturedPlane meridianBasepoint :=
  pointedHomeomorphFundamentalGroupEquiv triangleRegularPlaneHomeomorph
    normalizedRegularMeridianBasepoint_coordinate

@[simp] theorem compatibleBasePlaneEquiv_apply
    (γ : FundamentalGroup TriangleRegularQuotient
      (triangleRegularProject normalizedRegularMeridianBasepoint)) :
    compatibleBasePlaneEquiv γ =
      FundamentalGroup.mapOfEq
        ⟨triangleRegularPlaneHomeomorph, triangleRegularPlaneHomeomorph.continuous⟩
        normalizedRegularMeridianBasepoint_coordinate γ := rfl

/-- The image classes are computed from exact equality of the actual paths. -/
theorem compatibleBasePlaneEquiv_meridianClass (b : Bool) :
    compatibleBasePlaneEquiv (compatibleRegularMeridianClass b) =
      orientedClass normalizationReversesMeridians b := by
  rw [compatibleBasePlaneEquiv_apply, FundamentalGroup.mapOfEq_apply,
    ← compatiblePlanarMeridian_class]
  apply congrArg Path.Homotopic.Quotient.mk
  apply Path.ext
  funext t
  exact compatibleRegularMeridian_coordinate b t

/-- The two actual geometric source meridians are a genuine joint free basis. -/
def compatibleRegularFundamentalGroupEquiv :
    FundamentalGroup TriangleRegularQuotient
      (triangleRegularProject normalizedRegularMeridianBasepoint) ≃* FreeGroup Bool :=
  compatibleBasePlaneEquiv.trans (orientedEquiv normalizationReversesMeridians)

@[simp] theorem compatibleRegularFundamentalGroupEquiv_meridianClass (b : Bool) :
    compatibleRegularFundamentalGroupEquiv (compatibleRegularMeridianClass b) =
      FreeGroup.of b := by
  change orientedEquiv normalizationReversesMeridians
    (compatibleBasePlaneEquiv (compatibleRegularMeridianClass b)) = _
  rw [compatibleBasePlaneEquiv_meridianClass, orientedEquiv_orientedClass]

@[simp] theorem compatibleRegularFundamentalGroupEquiv_symm_of (b : Bool) :
    compatibleRegularFundamentalGroupEquiv.symm (FreeGroup.of b) =
      compatibleRegularMeridianClass b := by
  apply compatibleRegularFundamentalGroupEquiv.injective
  rw [MulEquiv.apply_symm_apply, compatibleRegularFundamentalGroupEquiv_meridianClass]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians
