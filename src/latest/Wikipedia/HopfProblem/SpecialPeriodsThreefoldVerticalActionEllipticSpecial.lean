import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionEllipticHolomorphic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionEllipticCharts
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticCover

/-!
# Vertical translation on the genuine small elliptic pieces

The actual special affine filling flow preserves its original powered
root coordinate.  It therefore restricts to the selected small filling,
with its inherited complex atlas, including the central fibre.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Elliptic

open Wikipedia.HopfProblem.Elliptic EllipticFilling

local notation "IF" => modelWithCornersSelf ℂ FamilyModel
local notation "I₁" => modelWithCornersSelf ℂ ℂ

attribute [local instance] specialFullFillingChartedSpace specialEllipticPieceChartedSpace

/-- Vertical translation on the original full special affine filling. -/
def specialFullFlow (j : Kind) (s : ℂ) : SpecialFullFilling j → SpecialFullFilling j :=
  flow (specialLocalData j) j.twist (mainTwist_admissible j) s

@[simp] theorem specialFullFlow_quotient (j : Kind) (s : ℂ)
    (x : (specialLocalData j).TotalSpace) :
    specialFullFlow j s ((specialLocalData j).quotient j.twist (mainTwist_admissible j) x) =
      (specialLocalData j).quotient j.twist (mainTwist_admissible j)
        (Period.flow (specialLocalData j).periods s x) := rfl

@[simp] theorem specialFullFlow_projection (j : Kind) (s : ℂ)
    (x : SpecialFullFilling j) :
    specialFullFillingProjection j (specialFullFlow j s x) =
      specialFullFillingProjection j x :=
  flow_projection (specialLocalData j) j.twist (mainTwist_admissible j) s x

theorem specialFullFlow_joint_holomorphic (j : Kind) :
    ContMDiff ((IF).prod I₁) IF ω
      (fun x : SpecialFullFilling j × ℂ => specialFullFlow j x.2 x.1) :=
  jointFlow_holomorphic (specialLocalData j) j.twist (mainTwist_admissible j)

theorem specialFullFlow_holomorphic (j : Kind) (s : ℂ) :
    ContMDiff IF IF ω (specialFullFlow j s) :=
  flow_holomorphic (specialLocalData j) j.twist (mainTwist_admissible j) s

/-- Literal vertical translation in the unchanged full-filling chart
inverses, for the actual global special periods. -/
theorem specialFullFlow_chart_symm (j : Kind) (s : ℂ) (y : SpecialFullFilling j)
    (u : FamilyModel) :
    specialFullFlow j s ((chartAt FamilyModel y).symm u) =
      (chartAt FamilyModel y).symm (u.1, u.2 + Period.vector s) :=
  flow_chart_symm (specialLocalData j) j.twist (mainTwist_admissible j) s y u

/-- The actual small filling is invariant under every vertical
translation, since its defining parameter is unchanged. -/
def specialFlow (j : Kind) (s : ℂ) (x : EllipticGeometry.LocalSpace j) :
    EllipticGeometry.LocalSpace j :=
  ⟨specialFullFlow j s x.val, by
    change ‖(specialFullFillingProjection j (specialFullFlow j s x.val) : ℂ)‖ <
      specialBaseCover.radius (some j)
    rw [specialFullFlow_projection]
    exact x.property⟩

@[simp] theorem specialFlow_coe (j : Kind) (s : ℂ) (x : EllipticGeometry.LocalSpace j) :
    (specialFlow j s x : SpecialFullFilling j) = specialFullFlow j s x.val := rfl

@[simp] theorem specialFlow_parameter (j : Kind) (s : ℂ)
    (x : EllipticGeometry.LocalSpace j) :
    EllipticGeometry.parameter j (specialFlow j s x) = EllipticGeometry.parameter j x :=
  congrArg (Subtype.val : Disc → ℂ) (specialFullFlow_projection j s x.val)

@[simp] theorem specialFlow_projectionToBase (j : Kind) (s : ℂ)
    (x : EllipticGeometry.LocalSpace j) :
    specialEllipticPieceProjectionToBase j (specialFlow j s x) =
      specialEllipticPieceProjectionToBase j x := by
  change (punctureChart (some j)).symm (EllipticGeometry.parameter j (specialFlow j s x)) =
    (punctureChart (some j)).symm (EllipticGeometry.parameter j x)
  rw [specialFlow_parameter]

theorem specialFlow_mem_overlap_source_iff (j : Kind) (s : ℂ)
    (x : EllipticGeometry.LocalSpace j) :
    specialFlow j s x ∈ (specialEllipticOverlap j).source ↔
      x ∈ (specialEllipticOverlap j).source := by
  rw [specialEllipticOverlap_source]
  change specialEllipticPieceProjectionToBase j (specialFlow j s x) ∈ regularPatch ↔
    specialEllipticPieceProjectionToBase j x ∈ regularPatch
  rw [specialFlow_projectionToBase]

/-- In the genuine root-and-period cover the flow is exactly addition
in the second complex fibre coordinate. -/
@[simp] theorem specialFlow_localCover (j : Kind) (s : ℂ)
    (x : HolomorphicForms.EllipticCover.Cover j) :
    specialFlow j s (HolomorphicForms.EllipticCover.localCover j x) =
      HolomorphicForms.EllipticCover.localCover j (Period.vectorFlow s x) := by
  apply Subtype.ext
  exact flow_quotient_quotientMap (specialLocalData j) j.twist
    (mainTwist_admissible j) s ((x.1 : Disc), x.2)

theorem specialFlow_joint_holomorphic (j : Kind) :
    ContMDiff ((IF).prod I₁) IF ω
      (fun x : EllipticGeometry.LocalSpace j × ℂ => specialFlow j x.2 x.1) := by
  have hi : ContMDiff ((IF).prod I₁) ((IF).prod I₁) ω
      (fun x : EllipticGeometry.LocalSpace j × ℂ =>
        ((x.1 : SpecialFullFilling j), x.2)) :=
    (contMDiff_subtype_val.comp contMDiff_fst).prodMk contMDiff_snd
  have h := (specialFullFlow_joint_holomorphic j).comp hi
  intro x
  have he : ContMDiffAt ((IF).prod I₁) IF ω
      (fun y : EllipticGeometry.LocalSpace j × ℂ =>
        (specialFlow j y.2 y.1 : SpecialFullFilling j)) x ↔
      ContMDiffAt ((IF).prod I₁) IF ω
        (fun y : EllipticGeometry.LocalSpace j × ℂ => specialFlow j y.2 y.1) x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (h x)

theorem specialFlow_holomorphic (j : Kind) (s : ℂ) :
    ContMDiff IF IF ω (specialFlow j s) := by
  have h : ContMDiff IF IF ω
      (fun x : EllipticGeometry.LocalSpace j => specialFullFlow j s x.val) :=
    (specialFullFlow_holomorphic j s).comp contMDiff_subtype_val
  intro x
  have he : ContMDiffAt IF IF ω
      (fun y : EllipticGeometry.LocalSpace j => (specialFlow j s y : SpecialFullFilling j)) x ↔
      ContMDiffAt IF IF ω (specialFlow j s) x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (h x)

@[simp] theorem specialFlow_zero (j : Kind) (x : EllipticGeometry.LocalSpace j) :
    specialFlow j 0 x = x :=
  Subtype.ext (flow_zero (specialLocalData j) j.twist (mainTwist_admissible j) x.val)

theorem specialFlow_add (j : Kind) (s t : ℂ) (x : EllipticGeometry.LocalSpace j) :
    specialFlow j (s + t) x = specialFlow j s (specialFlow j t x) :=
  Subtype.ext (flow_add (specialLocalData j) j.twist (mainTwist_admissible j) s t x.val)

@[simp] theorem specialFlow_int_cast (j : Kind) (n : ℤ)
    (x : EllipticGeometry.LocalSpace j) : specialFlow j (n : ℂ) x = x :=
  Subtype.ext (flow_int_cast (specialLocalData j) j.twist (mainTwist_admissible j) n x.val)

/-- Translation and its opposite preserve the same actual small piece
and are holomorphic for its original open-submanifold atlas. -/
def specialFlowBiholomorph (j : Kind) (s : ℂ) :
    Diffeomorph IF IF (EllipticGeometry.LocalSpace j) (EllipticGeometry.LocalSpace j) ω where
  toFun := specialFlow j s
  invFun := specialFlow j (-s)
  left_inv x := by rw [← specialFlow_add, neg_add_cancel, specialFlow_zero]
  right_inv x := by rw [← specialFlow_add, add_neg_cancel, specialFlow_zero]
  contMDiff_toFun := specialFlow_holomorphic j s
  contMDiff_invFun := specialFlow_holomorphic j (-s)

@[simp] theorem specialFlowBiholomorph_apply (j : Kind) (s : ℂ)
    (x : EllipticGeometry.LocalSpace j) : specialFlowBiholomorph j s x = specialFlow j s x := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Elliptic
