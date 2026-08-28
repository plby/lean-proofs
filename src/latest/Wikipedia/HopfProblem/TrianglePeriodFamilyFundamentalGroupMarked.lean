import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupFree
import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupMeridianMarking

/-!
# The source-marked fundamental group of the actual regular period family

The proved joint free basis has actual inverse-generator lifts. Its
action on the genuine fibre lattice is therefore exactly `A₁` and `A₂`.
The previously constructed split extension now gives the actual family
fundamental group with this fixed, period-independent semidirect action.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped Matrix

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians

open SpecialPeriods SpecialPeriods.Triangle

/-- The free group reads the two geometrically specified triangle generators. -/
def sourceFreeTriangleHom : FreeGroup Bool →* TriangleGroup :=
  FreeGroup.lift compatibleMeridianGenerator

@[simp] theorem sourceFreeTriangleHom_of (b : Bool) :
    sourceFreeTriangleHom (FreeGroup.of b) = compatibleMeridianGenerator b :=
  FreeGroup.lift_apply_of

/-- The source's two integral matrices, extended freely to all words. -/
def sourceFreeLatticeAction : FreeGroup Bool →* MulAut (Multiplicative Lattice) :=
  triangleLatticeMulAutHom.comp sourceFreeTriangleHom

@[simp] theorem sourceFreeLatticeAction_of (b : Bool) :
    sourceFreeLatticeAction (FreeGroup.of b) =
      triangleLatticeMulAutHom (compatibleMeridianGenerator b) := by
  change triangleLatticeMulAutHom (sourceFreeTriangleHom (FreeGroup.of b)) = _
  rw [sourceFreeTriangleHom_of]

@[simp] theorem sourceFreeLatticeAction_first (v : Multiplicative Lattice) :
    (sourceFreeLatticeAction (FreeGroup.of false) v).toAdd = A₁ *ᵥ v.toAdd := by
  rw [sourceFreeLatticeAction_of, triangleLatticeMulAutHom_toAdd]
  exact congrArg (fun A : LatticeMatrix => A *ᵥ v.toAdd)
    triangleDualRepresentation_generator₁_matrix

@[simp] theorem sourceFreeLatticeAction_second (v : Multiplicative Lattice) :
    (sourceFreeLatticeAction (FreeGroup.of true) v).toAdd = A₂ *ᵥ v.toAdd := by
  rw [sourceFreeLatticeAction_of, triangleLatticeMulAutHom_toAdd]
  exact congrArg (fun A : LatticeMatrix => A *ᵥ v.toAdd)
    triangleDualRepresentation_generator₂_matrix

end Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians

namespace Wikipedia.HopfProblem.TrianglePeriodFamily

open SpecialPeriods SpecialPeriods.Triangle Meridians

variable (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (Triangle.generatorTwoSL • z) = (P.point z).step₂)

local notation "Dreg" => regularData P h₁ h₂
local notation "hqreg" => regularCovering P h₁ h₂
local notation "breg" => normalizedRegularMeridianBasepoint

/-- Actual covering transport of the proved free basis, with no endpoint assumption. -/
theorem compatibleMeridian_deckTransport (b : Bool) :
    (Dreg).deckTransportHom hqreg breg (compatibleRegularMeridianClass b) =
      compatibleMeridianGenerator b :=
  (Dreg).deckTransportHom_eq_of_inverse_endpoint hqreg breg _ _
    (compatibleRegularMeridian_monodromy b)

theorem compatibleMeridian_latticeTransport (b : Bool) :
    (Dreg).latticeTransportHom hqreg breg (compatibleRegularMeridianClass b) =
      triangleDualRepresentation (compatibleMeridianGenerator b) :=
  (Dreg).latticeTransportHom_eq_of_inverse_endpoint hqreg breg _ _
    (compatibleRegularMeridian_monodromy b)

@[simp] theorem compatibleMeridian_latticeTransport_first :
    ((Dreg).latticeTransportHom hqreg breg (compatibleRegularMeridianClass false) :
      LatticeMatrix) = A₁ := by
  rw [compatibleMeridian_latticeTransport]
  exact triangleDualRepresentation_generator₁_matrix

@[simp] theorem compatibleMeridian_latticeTransport_second :
    ((Dreg).latticeTransportHom hqreg breg (compatibleRegularMeridianClass true) :
      LatticeMatrix) = A₂ := by
  rw [compatibleMeridian_latticeTransport]
  exact triangleDualRepresentation_generator₂_matrix

/-- The actual family action in the proved geometric free basis. -/
def markedRegularFundamentalGroupAction : FreeGroup Bool →* MulAut (Multiplicative Lattice) :=
  (Dreg).freeFundamentalGroupAction hqreg breg compatibleRegularFundamentalGroupEquiv

@[simp] theorem markedRegularFundamentalGroupAction_of (b : Bool) :
    markedRegularFundamentalGroupAction P h₁ h₂ (FreeGroup.of b) =
      triangleLatticeMulAutHom (compatibleMeridianGenerator b) := by
  change triangleLatticeMulAutHom ((Dreg).deckTransportHom hqreg breg
    (compatibleRegularFundamentalGroupEquiv.symm (FreeGroup.of b))) = _
  rw [compatibleRegularFundamentalGroupEquiv_symm_of, compatibleMeridian_deckTransport]

/-- Equality for every free word follows from the two proved generator computations. -/
theorem markedRegularFundamentalGroupAction_eq :
    markedRegularFundamentalGroupAction P h₁ h₂ = sourceFreeLatticeAction := by
  apply FreeGroup.ext_hom
  intro b
  rw [markedRegularFundamentalGroupAction_of, sourceFreeLatticeAction_of]

/-- This changes only the proved-equal action, preserving both group coordinates. -/
def markedSemidirectReparametrization :
    (Multiplicative Lattice) ⋊[markedRegularFundamentalGroupAction P h₁ h₂]
      (FreeGroup Bool) ≃*
        (Multiplicative Lattice) ⋊[sourceFreeLatticeAction] (FreeGroup Bool) := by
  refine SemidirectProduct.congr (MulEquiv.refl _) (MulEquiv.refl _) ?_
  intro w
  apply MulEquiv.ext
  intro v
  change markedRegularFundamentalGroupAction P h₁ h₂ w v = sourceFreeLatticeAction w v
  rw [markedRegularFundamentalGroupAction_eq]

@[simp] theorem markedSemidirectReparametrization_right
    (x : (Multiplicative Lattice) ⋊[markedRegularFundamentalGroupAction P h₁ h₂]
      (FreeGroup Bool)) :
    (markedSemidirectReparametrization P h₁ h₂ x).right = x.right :=
  SemidirectProduct.congr_apply_right _ _ _ x

@[simp] theorem markedSemidirectReparametrization_inl (v : Multiplicative Lattice) :
    markedSemidirectReparametrization P h₁ h₂ (SemidirectProduct.inl v) =
      SemidirectProduct.inl v := rfl

@[simp] theorem markedSemidirectReparametrization_inr (w : FreeGroup Bool) :
    markedSemidirectReparametrization P h₁ h₂ (SemidirectProduct.inr w) =
      SemidirectProduct.inr w := rfl

/-- The actual regular period-family group with the fixed source matrix action. -/
def markedRegularFundamentalGroupEquiv :
    FundamentalGroup (Dreg).Space ((Dreg).fundamentalGroupBasepoint breg) ≃*
      (Multiplicative Lattice) ⋊[sourceFreeLatticeAction] (FreeGroup Bool) :=
  ((Dreg).fundamentalGroupFreeSemidirectEquiv hqreg breg
    compatibleRegularFundamentalGroupEquiv).trans (markedSemidirectReparametrization P h₁ h₂)

@[simp] theorem markedRegularFundamentalGroupEquiv_lattice (v : Multiplicative Lattice) :
    markedRegularFundamentalGroupEquiv P h₁ h₂ ((Dreg).latticeFundamentalGroupHom breg v) =
      SemidirectProduct.inl v := by
  change markedSemidirectReparametrization P h₁ h₂
    ((Dreg).fundamentalGroupFreeSemidirectEquiv hqreg breg
      compatibleRegularFundamentalGroupEquiv ((Dreg).latticeFundamentalGroupHom breg v)) = _
  exact (congrArg (markedSemidirectReparametrization P h₁ h₂)
    ((Dreg).fundamentalGroupFreeSemidirectEquiv_lattice hqreg breg
      compatibleRegularFundamentalGroupEquiv v)).trans
        (markedSemidirectReparametrization_inl P h₁ h₂ v)

/-- The two section loops are the two free letters, simultaneously and with the
same source-column lattice marking used in the matrix computations. -/
@[simp] theorem markedRegularFundamentalGroupEquiv_meridian (b : Bool) :
    markedRegularFundamentalGroupEquiv P h₁ h₂
      ((Dreg).sectionFundamentalGroupHom breg (compatibleRegularMeridianClass b)) =
        SemidirectProduct.inr (FreeGroup.of b) := by
  change markedSemidirectReparametrization P h₁ h₂
    ((Dreg).fundamentalGroupFreeSemidirectEquiv hqreg breg
      compatibleRegularFundamentalGroupEquiv
        ((Dreg).sectionFundamentalGroupHom breg (compatibleRegularMeridianClass b))) = _
  have hs := congrArg (markedSemidirectReparametrization P h₁ h₂)
    ((Dreg).fundamentalGroupFreeSemidirectEquiv_section hqreg breg
      compatibleRegularFundamentalGroupEquiv (compatibleRegularMeridianClass b))
  exact hs.trans ((congrArg (fun w : FreeGroup Bool =>
    markedSemidirectReparametrization P h₁ h₂ (SemidirectProduct.inr w))
      (compatibleRegularFundamentalGroupEquiv_meridianClass b)).trans
        (markedSemidirectReparametrization_inr P h₁ h₂ (FreeGroup.of b)))

@[simp] theorem markedRegularFundamentalGroupEquiv_projection
    (γ : FundamentalGroup (Dreg).Space ((Dreg).fundamentalGroupBasepoint breg)) :
    (markedRegularFundamentalGroupEquiv P h₁ h₂ γ).right =
      compatibleRegularFundamentalGroupEquiv ((Dreg).projectionFundamentalGroupHom breg γ) := by
  change (markedSemidirectReparametrization P h₁ h₂
    ((Dreg).fundamentalGroupFreeSemidirectEquiv hqreg breg
      compatibleRegularFundamentalGroupEquiv γ)).right = _
  exact (markedSemidirectReparametrization_right P h₁ h₂ _).trans
    ((Dreg).fundamentalGroupFreeSemidirectEquiv_projection hqreg breg
      compatibleRegularFundamentalGroupEquiv γ)

end Wikipedia.HopfProblem.TrianglePeriodFamily
