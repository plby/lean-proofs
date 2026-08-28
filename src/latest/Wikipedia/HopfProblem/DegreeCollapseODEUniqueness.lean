import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Geometry.Manifold.MFDeriv.Tangent

/-!
# Uniqueness of ordinary curves from a smooth autonomous field

The native uniqueness theorem in the model space removes the need to
supply an extra global Lipschitz constant. This will identify the actual
Picard endpoint with any previously constructed local flow.
-/

noncomputable section

open Set Function Manifold
open scoped ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SmoothODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Smooth autonomous ordinary ODEs have unique solutions on an open interval. -/
theorem ordinary_curve_eqOn_of_contDiff {v : E → E} (hv : ContDiff ℝ 1 v)
    {γ η : ℝ → E} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (v (γ t)) t)
    (hη : ∀ t ∈ Ioo a b, HasDerivAt η (v (η t)) t)
    (heq : γ t₀ = η t₀) : EqOn γ η (Ioo a b) := by
  let V : (x : E) → TangentSpace 𝓘(ℝ, E) x := fun x => v x
  have hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) E)) :=
    (tangentBundleModelSpaceDiffeomorph 𝓘(ℝ, E) 1).symm.contMDiff.comp
      (contDiff_id.prodMk hv).contMDiff
  have hγM : IsMIntegralCurveOn γ V (Ioo a b) := by
    intro t ht
    exact (hγ t ht).hasFDerivAt.hasMFDerivAt.hasMFDerivWithinAt
  have hηM : IsMIntegralCurveOn η V (Ioo a b) := by
    intro t ht
    exact (hη t ht).hasFDerivAt.hasMFDerivAt.hasMFDerivWithinAt
  exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless ht₀ hV hγM hηM heq

end Wikipedia.HopfProblem.DegreeCollapse.SmoothODE
