import Wikipedia.NoExoticSixSphere.AffineParameterEvaluation
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Affine variations with zero value and prescribed composed spatial derivative

An injective source differential and a surjective target differential admit
linear splittings. The resulting actual affine variation vanishes at the
specified source point, while its derivative, after the given source and
target differentials and a nonzero scalar weight, is arbitrary.
-/

noncomputable section

open Function

namespace NoExoticSixSphere.AffinePerturbation

variable {X V E W : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

theorem exists_zero_value_prescribed_composition (x : V)
    (J : X →L[ℝ] V) (hJ : Injective J) (R : E →L[ℝ] W) (hR : Surjective R)
    {a : ℝ} (ha : a ≠ 0) (L : X →L[ℝ] W) :
    ∃ q : Parameters V E, value q x = 0 ∧ R.comp (a • q.1.comp J) = L := by
  obtain ⟨S, hS⟩ := J.toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hJ)
  obtain ⟨T, hT⟩ := R.toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hR)
  have hS' (z : X) : S.toContinuousLinearMap (J z) = z := DFunLike.congr_fun hS z
  have hT' (w : W) : R (T.toContinuousLinearMap w) = w := DFunLike.congr_fun hT w
  let A : V →L[ℝ] E :=
    a⁻¹ • T.toContinuousLinearMap.comp (L.comp S.toContinuousLinearMap)
  refine ⟨(A, -A x), ?_, ?_⟩
  · exact add_neg_cancel (A x)
  · ext z
    change R (a • (a⁻¹ • T.toContinuousLinearMap (L (S.toContinuousLinearMap (J z))))) = L z
    rw [smul_inv_smul₀ ha, hS', hT']

end NoExoticSixSphere.AffinePerturbation
