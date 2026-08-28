import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Actual factorization of every operator of rank at most one

The zero operator is included. A one-dimensional actual range is identified
with the scalar field, producing a continuous linear functional and a vector
whose outer product is exactly the original operator.
-/

noncomputable section

open Function Module

namespace NoExoticSixSphere.OperatorRank

variable {V W : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

omit [FiniteDimensional ℝ W] in
theorem finrank_operator : finrank ℝ (V →L[ℝ] W) = finrank ℝ V * finrank ℝ W := by
  rw [← (LinearMap.toContinuousLinearMap :
    (V →ₗ[ℝ] W) ≃ₗ[ℝ] (V →L[ℝ] W)).finrank_eq, finrank_linearMap]

omit [FiniteDimensional ℝ W] in
theorem exists_smulRight_of_rank_le_one (L : V →L[ℝ] W)
    (hr : finrank ℝ L.range ≤ 1) :
    ∃ ℓ : V →L[ℝ] ℝ, ∃ w : W, L = ℓ.smulRight w := by
  have hcases : finrank ℝ L.range = 0 ∨ finrank ℝ L.range = 1 := by omega
  rcases hcases with hzero | hone
  · have hbot : L.range = ⊥ := Submodule.finrank_eq_zero.mp hzero
    refine ⟨0, 0, ?_⟩
    ext x
    have hx : L x ∈ L.range := LinearMap.mem_range_self L.toLinearMap x
    rw [hbot] at hx
    simpa using hx
  · let e : L.range ≃L[ℝ] ℝ :=
      ContinuousLinearEquiv.ofFinrankEq (by simpa only [finrank_self] using hone)
    let ℓ : V →L[ℝ] ℝ := e.toContinuousLinearMap.comp L.rangeRestrict
    let w : W := (e.symm 1 : L.range)
    refine ⟨ℓ, w, ?_⟩
    ext x
    let z : L.range := ⟨L x, LinearMap.mem_range_self L.toLinearMap x⟩
    have he : (e z) • e.symm 1 = z := by
      apply e.injective
      rw [map_smul, e.apply_symm_apply, smul_eq_mul, mul_one]
    change (z : W) = e z • (e.symm 1 : W)
    exact congrArg (fun q : L.range ↦ (q : W)) he.symm

end NoExoticSixSphere.OperatorRank
