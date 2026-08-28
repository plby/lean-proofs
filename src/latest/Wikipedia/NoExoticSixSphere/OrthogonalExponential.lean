import Wikipedia.NoExoticSixSphere.OrthogonalLieGroup
import Wikipedia.NoExoticSixSphere.OrthogonalCompactness
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The actual orthogonal exponential

Exponentiating a skew-adjoint continuous-linear operator gives an orthogonal
operator. The map is smooth for the Cayley atlas, and each scalar line gives
an actual smooth one-parameter subgroup with the usual ambient derivative.
-/

open scoped Manifold ContDiff

namespace NoExoticSixSphere.OrthogonalExponential

noncomputable section

open GLOrthonormalization CayleyTransform OrthogonalSmoothness OrthogonalCompactness

variable {n : ℕ}

local instance : NormedAlgebra ℚ (Vector n →L[ℝ] Vector n) :=
  NormedAlgebra.restrictScalars ℚ ℝ (Vector n →L[ℝ] Vector n)

theorem exp_norm (K : SkewOperators n) (x : Vector n) :
    ‖NormedSpace.exp (K : Vector n →L[ℝ] Vector n) x‖ = ‖x‖ := by
  apply (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mpr _ x
  change star (NormedSpace.exp (K : Vector n →L[ℝ] Vector n)) *
    NormedSpace.exp (K : Vector n →L[ℝ] Vector n) = 1
  exact Unitary.star_mul_self_of_mem (NormedSpace.exp_mem_unitary_of_mem_skewAdjoint K.2)

noncomputable def exp (K : SkewOperators n) : OrthogonalOperators n :=
  ⟨⟨NormedSpace.exp (K : Vector n →L[ℝ] Vector n),
    normPreserving_isInvertible _ (exp_norm K)⟩, exp_norm K⟩

theorem exp_operator (K : SkewOperators n) :
    (exp K).1.1 = NormedSpace.exp (K : Vector n →L[ℝ] Vector n) := rfl

theorem exp_zero : exp (0 : SkewOperators n) = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  exact NormedSpace.exp_zero

theorem exp_add_of_commute (K L : SkewOperators n)
    (h : Commute (K : Vector n →L[ℝ] Vector n) (L : Vector n →L[ℝ] Vector n)) :
    exp (K + L) = exp K * exp L := by
  apply Subtype.ext
  apply Subtype.ext
  exact NormedSpace.exp_add_of_commute h

theorem exp_add_smul (K : SkewOperators n) (s t : ℝ) :
    exp ((s + t) • K) = exp (s • K) * exp (t • K) := by
  rw [add_smul]
  apply exp_add_of_commute
  exact ((Commute.refl (K : Vector n →L[ℝ] Vector n)).smul_left s).smul_right t

theorem exp_neg (K : SkewOperators n) : exp (-K) = (exp K)⁻¹ := by
  apply mul_left_cancel (a := exp K)
  rw [mul_inv_cancel]
  rw [← exp_add_of_commute K (-K) (Commute.refl _).neg_right, add_neg_cancel, exp_zero]

theorem contDiff_exp_operator :
    ContDiff ℝ ∞ (fun K : SkewOperators n ↦ (exp K).1.1) := by
  rw [contDiff_iff_contDiffAt]
  intro K
  have ha : ContDiffAt ℝ ∞
      (NormedSpace.exp : (Vector n →L[ℝ] Vector n) → (Vector n →L[ℝ] Vector n))
      (K : Vector n →L[ℝ] Vector n) := (NormedSpace.exp_analytic (𝕂 := ℝ) _).contDiffAt
  have hc : ContDiffAt ℝ ∞
      (fun K : SkewOperators n ↦ (K : Vector n →L[ℝ] Vector n)) K :=
    (skewAdjoint.submodule ℝ (Vector n →L[ℝ] Vector n)).subtypeL.contDiff.contDiffAt
  exact ha.comp K hc

theorem contMDiff_exp : ContMDiff 𝓘(ℝ, SkewOperators n) 𝓘(ℝ, SkewOperators n) ∞
    (exp (n := n)) :=
  contMDiff_iff_operator.mpr contDiff_exp_operator.contMDiff

theorem contMDiff_exp_smul (K : SkewOperators n) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, SkewOperators n) ∞ (fun t : ℝ ↦ exp (t • K)) :=
  contMDiff_exp.comp (contMDiff_id.smul contMDiff_const)

/-- This path uses the actual operator exponential and its actual endpoints. -/
noncomputable def path (K : SkewOperators n) : Path (1 : OrthogonalOperators n) (exp K) where
  toFun t := exp ((t : ℝ) • K)
  continuous_toFun := (contMDiff_exp_smul K).continuous.comp continuous_subtype_val
  source' := by change exp ((0 : ℝ) • K) = 1; rw [zero_smul, exp_zero]
  target' := by change exp ((1 : ℝ) • K) = exp K; rw [one_smul]

theorem hasDerivAt_exp_smul_operator (K : SkewOperators n) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ (exp (s • K)).1.1)
      ((exp (t • K)).1.1.comp (K : Vector n →L[ℝ] Vector n)) t := by
  exact hasDerivAt_exp_smul_const (K : Vector n →L[ℝ] Vector n) t

end

end NoExoticSixSphere.OrthogonalExponential
