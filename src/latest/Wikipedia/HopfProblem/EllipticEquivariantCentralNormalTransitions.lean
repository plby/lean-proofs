import Wikipedia.HopfProblem.EllipticEquivariantCentralNormalQuotient
import Wikipedia.HopfProblem.EllipticEquivariantCentralNormalAction

/-!
# Changes of genuine normal coordinates for equivariant periods

Differentiating invariance of the actual quotient covering identifies its
derivatives at two deck-related lifts. The independently computed transverse
derivative of the native family action then gives the exact character change
on the actual quotient by the central inclusion tangent image.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.Elliptic.Equivariant.Data

variable {j : Kind} (D : Equivariant.Data j)

local notation "IS" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ FamilyModel

/-- The derivative of actual covering invariance, in the supplied
varying-period atlas and its genuine covering quotient atlas. -/
theorem fillingDerivativeEquiv_comp_action (v : Lattice)
    (hv : AdmissibleTwist j v) (g : CyclicGroup j) (a : D.TotalSpace) :
    letI := D.periods.totalChartedSpace
    letI := D.chartedSpace v hv
    letI := D.action v hv.1
    ∀ w : FamilyModel,
      D.fillingDerivativeEquiv v hv (g • a)
          (mfderiv IF IF (fun y : D.TotalSpace => g • y) a w) =
        D.fillingDerivativeEquiv v hv a w := by
  let := D.periods.totalChartedSpace
  let := D.chartedSpace v hv
  let := D.action v hv.1
  have he : D.quotient v hv ∘ (fun y : D.TotalSpace => g • y) = D.quotient v hv := by
    funext y
    exact (D.quotientCoveringMap v hv).map_smul g
  have hgerm : (D.quotient v hv ∘ (fun y : D.TotalSpace => g • y)) =ᶠ[𝓝 a]
      D.quotient v hv := Filter.Eventually.of_forall (congrFun he)
  have hd := hgerm.mfderiv_eq (I := IF) (I' := IF)
  rw [mfderiv_comp a
    ((D.quotient_holomorphic v hv).mdifferentiableAt (by simp))
    ((D.action_holomorphic v hv.1 g).mdifferentiableAt (by simp))] at hd
  intro w
  exact (D.fillingDerivativeEquiv_apply v hv (g • a)
    (mfderiv IF IF (fun y : D.TotalSpace => g • y) a w)).trans
      ((congrArg (fun L : FamilyModel →L[ℂ] FamilyModel => L w) hd).trans
        (D.fillingDerivativeEquiv_apply v hv a w).symm)

/-- Coordinates supplied by two actual lifts of the same surface point
transform by the normal character on the very same genuine normal vector. -/
theorem normalCoordinateAtLift_change (v : Lattice)
    (hv : AdmissibleTwist j v) (a b : D.centralPeriod.val.Torus)
    (x : Surface j D.centralPeriod v hv)
    (ha : surfaceProjection j D.centralPeriod v hv a = x)
    (hb : surfaceProjection j D.centralPeriod v hv b = x) (g : CyclicGroup j) :
    letI := affineAction j D.centralPeriod v hv.1
    g • a = b → ∀ n : D.CentralNormalFibre v hv x,
      D.normalCoordinateAtLift v hv b x hb n = (normalCharacter j g : ℂ) *
        D.normalCoordinateAtLift v hv a x ha n := by
  let := D.periods.totalChartedSpace
  let := D.chartedSpace v hv
  let := affineAction j D.centralPeriod v hv.1
  let := D.action v hv.1
  intro hab n
  subst b
  let S : Submodule ℂ FamilyModel := (mfderiv IS IF (D.centralFibreInclusion v hv) x).range
  obtain ⟨w, rfl⟩ := S.mkQ_surjective n
  have he : (D.fillingDerivativeEquiv v hv (g • D.centralInclusion a)).symm w =
      mfderiv IF IF (fun y : D.TotalSpace => g • y) (D.centralInclusion a)
        ((D.fillingDerivativeEquiv v hv (D.centralInclusion a)).symm w) := by
    have hc := D.fillingDerivativeEquiv_comp_action v hv g (D.centralInclusion a)
      ((D.fillingDerivativeEquiv v hv (D.centralInclusion a)).symm w)
    have hc' := hc.trans
      ((D.fillingDerivativeEquiv v hv (D.centralInclusion a)).apply_symm_apply w)
    exact (D.fillingDerivativeEquiv v hv (g • D.centralInclusion a)).injective
      (((D.fillingDerivativeEquiv v hv (g • D.centralInclusion a)).apply_symm_apply w).trans
        hc'.symm)
  have hcb := congrArg (fun y : D.TotalSpace =>
    ((D.fillingDerivativeEquiv v hv y).symm w).1) (D.centralInclusion_smul v hv.1 g a)
  exact (D.normalCoordinateAtLift_mk v hv (g • a) x hb w).trans <| hcb.trans <|
    (congrArg Prod.fst he).trans <|
      (D.familyAction_mfderiv_fst v hv.1 g (D.centralInclusion a) _).trans <|
        congrArg (fun z : ℂ => (normalCharacter j g : ℂ) * z)
          (D.normalCoordinateAtLift_mk v hv a x ha w).symm

end Wikipedia.HopfProblem.Elliptic.Equivariant.Data
