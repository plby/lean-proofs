import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixedCoordinates
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticRestriction
import Wikipedia.HopfProblem.ToricAxisCharts

/-!
# The genuine tangent representation along the middle toric axes

The representation below is computed by differentiating the exact
equivariance of the actual coordinate covering into the threefold.
Its conjugating linear equivalence is the differential of that covering,
and not a separately chosen linear model.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates

open ToricCharts ToricFan HolomorphicDifferentialForms

local notation "E₃" => CoordinateSpace 3
local notation "I₃" => modelWithCornersSelf ℂ E₃
local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

theorem coordinateAction_holomorphic (u : ℂˣ) :
    ContMDiff I₃ I₃ ω (coordinateAction u) := by
  intro z
  have he : ContMDiffAt I₃ I₃ ω
      ((Subtype.val : Domain → E₃) ∘ coordinateAction u) z ↔
      ContMDiffAt I₃ I₃ ω (coordinateAction u) z :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (((diagonal u).contDiff.contMDiff.comp contMDiff_subtype_val) z)

/-- The derivative in the original inherited open-coordinate atlas is
exactly the displayed diagonal linear map. -/
theorem coordinateAction_mfderiv (u : ℂˣ) (z : Domain) :
    mfderiv I₃ I₃ (coordinateAction u) z = diagonal u := by
  have hc := (coordinateAction_holomorphic u).mdifferentiableAt (by simp) (x := z)
  have hv := (hasMFDerivAt_openSubtypeVal (E := E₃) Domain z).mdifferentiableAt
  have ht := (hasMFDerivAt_openSubtypeVal (E := E₃) Domain
    (coordinateAction u z)).mdifferentiableAt
  have hd : MDifferentiableAt I₃ I₃ (diagonal u) (z : E₃) :=
    (show ContMDiff I₃ I₃ ω (diagonal u) from
      (diagonal u).contDiff.contMDiff).mdifferentiableAt (by simp)
  have hfun : (Subtype.val : Domain → E₃) ∘ coordinateAction u =
      diagonal u ∘ (Subtype.val : Domain → E₃) := rfl
  have h := (mfderiv_comp z ht hc).symm.trans
    ((mfderiv_congr (I := I₃) (I' := I₃) (x := z) hfun).trans
      (mfderiv_comp z hd hv))
  rw [mfderiv_openSubtypeVal, mfderiv_openSubtypeVal, ContinuousLinearMap.mfderiv_eq] at h
  ext v
  exact congrArg (fun L : E₃ →L[ℂ] E₃ => L v) h

/-- The exact chain rule for the actual global action and original
coordinate cover, before specializing to a fixed point. -/
theorem action_derivative_square (u : ℂˣ) (a : Triangle) (z : Domain) (v : E₃) :
    mfderiv IF IF (actionBiholomorph u) (globalMap a z) (tangentEquiv a z v) =
      tangentEquiv a (coordinateAction u z) (diagonal u v) := by
  have hf := (globalMap_holomorphic a).mdifferentiableAt (by simp) (x := z)
  have ha := (actionBiholomorph u).contMDiff.mdifferentiableAt (by simp)
    (x := globalMap a z)
  have hc := (coordinateAction_holomorphic u).mdifferentiableAt (by simp) (x := z)
  have hg := (globalMap_holomorphic a).mdifferentiableAt (by simp)
    (x := coordinateAction u z)
  have hfun : actionBiholomorph u ∘ globalMap a = globalMap a ∘ coordinateAction u :=
    funext (globalMap_coordinateAction u a)
  have h := (mfderiv_comp z ha hf).symm.trans
    ((mfderiv_congr (I := I₃) (I' := IF) (x := z) hfun).trans
      (mfderiv_comp z hg hc))
  rw [coordinateAction_mfderiv] at h
  exact congrArg (fun L : E₃ →L[ℂ] (ℂ × ComplexPlane₂) => L v) h

theorem coordinateAction_eq_self (u : ℂˣ) (z : Domain)
    (hz : (z : E₃) 0 = 0 ∧ (z : E₃) 2 = 0) : coordinateAction u z = z := by
  apply Subtype.ext
  rw [coordinateAction_coe, diagonal_apply]
  ext j
  fin_cases j <;> simp [hz.1, hz.2]

/-- The native tangent action at an actual fixed axis point is conjugate
by the genuine coordinate derivative to weights `(-1,0,1)`. -/
theorem action_tangent_weights (u : ℂˣ) (a : Triangle) (z : Domain)
    (hz : (z : E₃) 0 = 0 ∧ (z : E₃) 2 = 0) (v : E₃) :
    mfderiv IF IF (actionBiholomorph u) (globalMap a z) (tangentEquiv a z v) =
      tangentEquiv a z ![(u : ℂ)⁻¹ * v 0, v 1, (u : ℂ) * v 2] := by
  rw [action_derivative_square, coordinateAction_eq_self u z hz, diagonal_apply]

/-- Genuine eigenvectors in the original tangent space, obtained from
the actual coordinate differential. -/
def tangentBasis (a : Triangle) (z : Domain) (j : Fin 3) :
    TangentSpace IF (globalMap a z) := tangentEquiv a z (Pi.single j 1)

theorem tangentBasis_ne_zero (a : Triangle) (z : Domain) (j : Fin 3) :
    tangentBasis a z j ≠ 0 := by
  intro h
  have he : Pi.single j (1 : ℂ) = (0 : E₃) := (tangentEquiv a z).injective (by
    simpa only [tangentBasis, map_zero] using h)
  have hj := congrFun he j
  simp at hj

theorem action_tangentBasis_zero (u : ℂˣ) (a : Triangle) (z : Domain)
    (hz : (z : E₃) 0 = 0 ∧ (z : E₃) 2 = 0) :
    mfderiv IF IF (actionBiholomorph u) (globalMap a z) (tangentBasis a z 0) =
      (u : ℂ)⁻¹ • tangentBasis a z 0 := by
  rw [tangentBasis, action_tangent_weights u a z hz, ← map_smul]
  congr 1
  ext j
  fin_cases j <;> simp

theorem action_tangentBasis_one (u : ℂˣ) (a : Triangle) (z : Domain)
    (hz : (z : E₃) 0 = 0 ∧ (z : E₃) 2 = 0) :
    mfderiv IF IF (actionBiholomorph u) (globalMap a z) (tangentBasis a z 1) =
      tangentBasis a z 1 := by
  rw [tangentBasis, action_tangent_weights u a z hz]
  congr 1
  ext j
  fin_cases j <;> simp

theorem action_tangentBasis_two (u : ℂˣ) (a : Triangle) (z : Domain)
    (hz : (z : E₃) 0 = 0 ∧ (z : E₃) 2 = 0) :
    mfderiv IF IF (actionBiholomorph u) (globalMap a z) (tangentBasis a z 2) =
      (u : ℂ) • tangentBasis a z 2 := by
  rw [tangentBasis, action_tangent_weights u a z hz, ← map_smul]
  congr 1
  ext j
  fin_cases j <;> simp

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates
