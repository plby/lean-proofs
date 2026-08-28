import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Smooth linear projections onto finite-dimensional real subspaces -/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

def finiteSubmoduleProjection (p : Submodule ℝ E) : E →L[ℝ] p :=
  p.subtype.leftInverse.toContinuousLinearMap

theorem finiteSubmoduleProjection_apply (p : Submodule ℝ E) (x : p) :
    finiteSubmoduleProjection p x.val = x :=
  LinearMap.leftInverse_apply_of_inj p.ker_subtype x

theorem contDiff_finiteSubmoduleProjection (p : Submodule ℝ E) :
    ContDiff ℝ ∞ (finiteSubmoduleProjection p) :=
  (finiteSubmoduleProjection p).contDiff

theorem hasFDerivAt_finiteSubmoduleProjection (p : Submodule ℝ E) (x : E) :
    HasFDerivAt (finiteSubmoduleProjection p) (finiteSubmoduleProjection p) x :=
  (finiteSubmoduleProjection p).hasFDerivAt

theorem finiteLinearMap_contDiff (f : E →ₗ[ℝ] F) : ContDiff ℝ ∞ f :=
  f.toContinuousLinearMap.contDiff

omit [FiniteDimensional ℝ E] in
theorem realFDeriv_eq_of_hasFDerivAt {f : E → F} {D : E →L[ℝ] F} {x : E}
    (h : HasFDerivAt f D x) : fderiv ℝ f x = D := h.fderiv

/-- Scalar multiplication packaged as an operator, with its explicit nonzero inverse. -/
def realScalarOperator (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ) :
    E →L[ℝ] E := c • 1

theorem realScalarOperator_isInvertible (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (hc : c ≠ 0) : (realScalarOperator E c).IsInvertible := by
  refine ⟨ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := E) (Units.mk0 c hc), ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  rfl

end Wikipedia.HomotopyGroupsOfSpheres
