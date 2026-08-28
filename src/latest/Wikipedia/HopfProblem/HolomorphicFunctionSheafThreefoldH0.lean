import Wikipedia.HopfProblem.HolomorphicFunctionSheafThreefold
import Wikipedia.HopfProblem.HolomorphicFunctionSheaf

/-!
# Genuine degree-zero sheaf cohomology of the actual threefold

`ThreefoldH0` is mathlib's `Ext`-defined degree-zero cohomology of the
actual additive holomorphic function sheaf, not a name for a chosen
one-dimensional vector space.  Its natural complex module is identified
with actual global sections and then, by evaluation, with `ℂ`.
No assertion about higher cohomology is made.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf

open SpecialPeriods

attribute [local instance] Threefold.chartedSpace

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- Genuine degree-zero cohomology of the actual holomorphic function sheaf. -/
abbrev ThreefoldH0 := H0 IF Threefold.Space

/-- The actual degree-zero cohomology comparison followed by actual evaluation. -/
def threefoldH0EvalEquiv (x : Threefold.Space) : ThreefoldH0 ≃ₗ[ℂ] ℂ :=
  (h0GlobalLinearEquiv IF Threefold.Space).trans
    (threefoldGlobalSectionsEvalEquiv x).toLinearEquiv

@[simp] theorem threefoldH0EvalEquiv_apply (x : Threefold.Space) (η : ThreefoldH0) :
    threefoldH0EvalEquiv x η =
      h0GlobalAddEquiv IF Threefold.Space η (toTopOpen Threefold.Space x) := rfl

/-- The cohomology class corresponding to the actual constant section. -/
def threefoldH0Constant (c : ℂ) : ThreefoldH0 :=
  (h0GlobalLinearEquiv IF Threefold.Space).symm
    (algebraMap ℂ ThreefoldGlobalSections c)

@[simp] theorem threefoldH0EvalEquiv_constant (x : Threefold.Space) (c : ℂ) :
    threefoldH0EvalEquiv x (threefoldH0Constant c) = c := by
  change threefoldGlobalSectionsEvalEquiv x
    (h0GlobalLinearEquiv IF Threefold.Space
      ((h0GlobalLinearEquiv IF Threefold.Space).symm
        (algebraMap ℂ ThreefoldGlobalSections c))) = c
  rw [LinearEquiv.apply_symm_apply, AlgEquiv.commutes]
  rfl

/-- The inverse identification is the class of the literal constant section. -/
@[simp] theorem threefoldH0EvalEquiv_symm_apply (x : Threefold.Space) (c : ℂ) :
    (threefoldH0EvalEquiv x).symm c = threefoldH0Constant c := by
  apply (threefoldH0EvalEquiv x).injective
  rw [LinearEquiv.apply_symm_apply, threefoldH0EvalEquiv_constant]

/-- The actual `Ext`-defined holomorphic sheaf cohomology in degree zero
has complex dimension one. -/
theorem threefoldH0_finrank : Module.finrank ℂ ThreefoldH0 = 1 := by
  rw [(h0GlobalLinearEquiv IF Threefold.Space).finrank_eq]
  exact threefoldGlobalSections_finrank

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf
