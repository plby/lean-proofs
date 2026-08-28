import Wikipedia.HopfProblem.EllipticBundleNormalQuotient

/-!
# Actual changes of normal tangent coordinates

The filling covering is invariant under its deck action. Differentiating
this identity relates the two actual covering differentials. Combining it
with the transverse derivative of the family action gives the exact change
between scalar coordinates on the genuine normal tangent quotient.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.Elliptic

local notation "IS" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ FamilyModel

/-- Differentiated invariance of the actual ambient covering projection. -/
theorem fillingDerivativeEquiv_comp_action (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (g : CyclicGroup j) (a : Family j) :
    letI := (familyPeriods j).totalChartedSpace
    letI := familyAction j v hv.1
    ∀ w : FamilyModel,
      fillingDerivativeEquiv j v hv (g • a)
          (mfderiv IF IF (fun y : Family j => g • y) a w) =
        fillingDerivativeEquiv j v hv a w := by
  let := (familyPeriods j).totalChartedSpace
  let := familyAction j v hv.1
  have he : fillingQuotient j v hv ∘ (fun y : Family j => g • y) =
      fillingQuotient j v hv := by
    funext y
    exact (fillingQuotient_isQuotientCoveringMap j v hv).map_smul g
  have hgerm : (fillingQuotient j v hv ∘ (fun y : Family j => g • y)) =ᶠ[𝓝 a]
      fillingQuotient j v hv := Filter.Eventually.of_forall (congrFun he)
  have hd := hgerm.mfderiv_eq (I := IF) (I' := IF)
  rw [mfderiv_comp a
    ((fillingQuotient_holomorphic j v hv).mdifferentiableAt (by simp))
    ((familyAction_holomorphic j v hv.1 g).mdifferentiableAt (by simp))] at hd
  intro w
  exact (fillingDerivativeEquiv_apply j v hv (g • a)
    (mfderiv IF IF (fun y : Family j => g • y) a w)).trans
      ((congrArg (fun L : FamilyModel →L[ℂ] FamilyModel => L w) hd).trans
        (fillingDerivativeEquiv_apply j v hv a w).symm)

/-- Scalar coordinates coming from two actual covering lifts transform by
the normal character.  Both sides evaluate the same genuine quotient vector. -/
theorem normalCoordinateAtLift_change (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (a b : (centralPeriod j).val.Torus)
    (x : Surface j (centralPeriod j) v hv)
    (ha : surfaceProjection j (centralPeriod j) v hv a = x)
    (hb : surfaceProjection j (centralPeriod j) v hv b = x) (g : CyclicGroup j) :
    letI := affineAction j (centralPeriod j) v hv.1
    g • a = b → ∀ n : CentralNormalFibre j v hv x,
      normalCoordinateAtLift j v hv b x hb n = (normalCharacter j g : ℂ) *
        normalCoordinateAtLift j v hv a x ha n := by
  let := (familyPeriods j).totalChartedSpace
  let := affineAction j (centralPeriod j) v hv.1
  let := familyAction j v hv.1
  intro hab n
  subst b
  let S : Submodule ℂ FamilyModel := (mfderiv IS IF (centralFibreInclusion j v hv) x).range
  obtain ⟨w, rfl⟩ := S.mkQ_surjective n
  have he : (fillingDerivativeEquiv j v hv (g • centralInclusion j a)).symm w =
      mfderiv IF IF (fun y : Family j => g • y) (centralInclusion j a)
        ((fillingDerivativeEquiv j v hv (centralInclusion j a)).symm w) := by
    have hc := fillingDerivativeEquiv_comp_action j v hv g (centralInclusion j a)
      ((fillingDerivativeEquiv j v hv (centralInclusion j a)).symm w)
    have hc' := hc.trans
      ((fillingDerivativeEquiv j v hv (centralInclusion j a)).apply_symm_apply w)
    exact (fillingDerivativeEquiv j v hv (g • centralInclusion j a)).injective
      (((fillingDerivativeEquiv j v hv (g • centralInclusion j a)).apply_symm_apply w).trans
        hc'.symm)
  have hcb := congrArg (fun y : Family j =>
    ((fillingDerivativeEquiv j v hv y).symm w).1) (centralInclusion_smul j v hv.1 g a)
  exact (normalCoordinateAtLift_mk j v hv (g • a) x hb w).trans <| hcb.trans <|
    (congrArg Prod.fst he).trans <|
      (familyAction_mfderiv_fst j v hv.1 g (centralInclusion j a) _).trans <|
        congrArg (fun z : ℂ => (normalCharacter j g : ℂ) * z)
          (normalCoordinateAtLift_mk j v hv a x ha w).symm

end Wikipedia.HopfProblem.Elliptic
