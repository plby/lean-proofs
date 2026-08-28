import Wikipedia.HopfProblem.HolomorphicFunctionSheafGlobal
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFunctions

/-!
# Global sections of the holomorphic sheaf on the actual threefold

The genuine sheaf is placed on the constructed threefold with its native
glued complex atlas. Its global-section algebra is identified with `ℂ`
by actual evaluation, using the previously proved compact maximum principle
for actual holomorphic functions on this same manifold.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf

open SpecialPeriods

attribute [local instance] Threefold.chartedSpace

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- The actual holomorphic function sheaf on the constructed threefold. -/
abbrev threefoldSheaf := sheaf IF Threefold.Space

/-- Genuine global sections on the top open set of the actual threefold. -/
abbrev ThreefoldGlobalSections := GlobalSections IF Threefold.Space

/-- Evaluation identifies the actual global-section algebra with `ℂ`. -/
def threefoldGlobalSectionsEvalEquiv (x : Threefold.Space) :
    ThreefoldGlobalSections ≃ₐ[ℂ] ℂ :=
  (globalSectionsAlgEquiv IF Threefold.Space).trans
    (Threefold.holomorphicFunctionEvalEquiv x)

@[simp] theorem threefoldGlobalSectionsEvalEquiv_apply
    (x : Threefold.Space) (f : ThreefoldGlobalSections) :
    threefoldGlobalSectionsEvalEquiv x f = f (toTopOpen Threefold.Space x) := rfl

/-- The inverse equivalence is the literal constant sheaf section. -/
@[simp] theorem threefoldGlobalSectionsEvalEquiv_symm_apply
    (x : Threefold.Space) (c : ℂ) :
    (threefoldGlobalSectionsEvalEquiv x).symm c = algebraMap ℂ ThreefoldGlobalSections c := by
  apply (threefoldGlobalSectionsEvalEquiv x).injective
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.commutes]
  rfl

/-- Every genuine global holomorphic sheaf section is constant. -/
theorem threefold_globalSection_eq_constant (f : ThreefoldGlobalSections)
    (x : Threefold.Space) :
    f = algebraMap ℂ ThreefoldGlobalSections (f (toTopOpen Threefold.Space x)) := by
  exact ((threefoldGlobalSectionsEvalEquiv x).symm_apply_apply f).symm.trans
    (threefoldGlobalSectionsEvalEquiv_symm_apply x _)

/-- The dimension statement concerns the genuine global-section space
of the actual holomorphic function sheaf. -/
theorem threefoldGlobalSections_finrank : Module.finrank ℂ ThreefoldGlobalSections = 1 := by
  rw [(globalSectionsAlgEquiv IF Threefold.Space).toLinearEquiv.finrank_eq]
  exact Threefold.holomorphicFunction_finrank

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf
