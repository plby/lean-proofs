import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicRightScalars
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicExponential
import Wikipedia.NoExoticSixSphere.SkewAntipodalSpectrum
import Mathlib.Analysis.Normed.Module.RCLike.Basic

/-!
# A quaternionic eigenvector from a real rotation plane

For a quaternionic-linear operator, a real rotation pair produces an
eigenvector for right multiplication by the fixed scalar `i`. The possible
vanishing of `x - y i` is handled by `x j`, using anticommutation of `i`
and `j`. This keeps the high-speed spectral direction inside the original
quaternionic vector space.
-/

namespace Wikipedia.HomotopyGroupsOfSpheres

section LinearAlgebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_eigenvector_of_quaternionic_rotation (T R S : E →ₗ[ℝ] E)
    (hR : ∀ v, R (R v) = -v) (hS : ∀ v, S (S v) = -v)
    (hRS : ∀ v, R (S v) = -(S (R v)))
    (hTR : ∀ v, T (R v) = R (T v)) (hTS : ∀ v, T (S v) = S (T v))
    {α : ℝ} {x y : E} (hx : x ≠ 0) (hTx : T x = α • y) (hTy : T y = (-α) • x) :
    ∃ v : E, v ≠ 0 ∧ T v = α • R v := by
  by_cases hz : x - R y = 0
  · have hxy : x = R y := sub_eq_zero.mp hz
    have hRx : R x = -y := by rw [hxy, hR]
    have hRSx : R (S x) = S y := by rw [hRS, hRx, map_neg, neg_neg]
    refine ⟨S x, ?_, ?_⟩
    · intro hs
      have he := hS x
      rw [hs, map_zero] at he
      exact hx (neg_eq_zero.mp he.symm)
    · rw [hTS, hTx, map_smul, hRSx]
  · refine ⟨x - R y, hz, ?_⟩
    rw [map_sub, hTR, hTx, hTy, map_smul, neg_smul, sub_neg_eq_add,
      map_sub, hR, sub_neg_eq_add, smul_add]
    exact add_comm _ _

theorem exists_unit_eigenvector_of_quaternionic_rotation (T R S : E →ₗ[ℝ] E)
    (hR : ∀ v, R (R v) = -v) (hS : ∀ v, S (S v) = -v)
    (hRS : ∀ v, R (S v) = -(S (R v)))
    (hTR : ∀ v, T (R v) = R (T v)) (hTS : ∀ v, T (S v) = S (T v))
    {α : ℝ} {x y : E} (hx : x ≠ 0) (hTx : T x = α • y) (hTy : T y = (-α) • x) :
    ∃ v : E, ‖v‖ = 1 ∧ T v = α • R v := by
  obtain ⟨v, hv, he⟩ := exists_eigenvector_of_quaternionic_rotation T R S
    hR hS hRS hTR hTS hx hTx hTy
  refine ⟨‖v‖⁻¹ • v, norm_smul_inv_norm hv, ?_⟩
  rw [map_smul, he, map_smul, smul_comm]

end LinearAlgebra

namespace QuaternionicColumns

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.SkewSpectralPlane

variable {n : ℕ}

theorem exists_unit_i_eigenvector_of_rotation (K : SkewSpace n)
    {α : ℝ} {x y : Vector (4 * n + 4)} (hx : x ≠ 0)
    (hKx : K.val x = α • y) (hKy : K.val y = (-α) • x) :
    ∃ v : Vector (4 * n + 4), ‖v‖ = 1 ∧
      K.val v = α • rightAction n QuaternionicScalars.i v := by
  apply exists_unit_eigenvector_of_quaternionic_rotation K.val.toLinearMap
    (rightAction n QuaternionicScalars.i).toLinearMap
    (rightAction n QuaternionicScalars.j).toLinearMap
    (fun v => DFunLike.congr_fun (rightAction_i_square n) v)
    (fun v => DFunLike.congr_fun (rightAction_j_square n) v)
    (fun v => DFunLike.congr_fun (rightAction_i_j_anticommute n) v)
    (fun v => DFunLike.congr_fun
      ((mem_commutant_iff n K.val).mp K.property.2 QuaternionicScalars.i) v)
    (fun v => DFunLike.congr_fun
      ((mem_commutant_iff n K.val).mp K.property.2 QuaternionicScalars.j) v)
    hx hKx hKy

/-- A nonminimal antipodal symplectic exponential has a fast quaternionic eigenvector. -/
theorem exists_fast_i_eigenvector (K : SkewSpace n)
    (hexp : (Exponential.exp K).val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (hnot : gram (toOrthogonalSkew n K) ≠
      Real.pi ^ 2 • (1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4))) :
    ∃ (α : ℝ) (v : Vector (4 * n + 4)), 3 * Real.pi ≤ α ∧ ‖v‖ = 1 ∧
      K.val v = α • rightAction n QuaternionicScalars.i v := by
  obtain ⟨α, x, y, hα, hx, _, _, hKx, hKy⟩ :=
    NoExoticSixSphere.SkewAntipodalSpectrum.exists_fast_rotationPlane
      (toOrthogonalSkew n K) hexp hnot
  have hx0 : x ≠ 0 := by
    intro he
    exact zero_ne_one (by simpa only [he, norm_zero] using hx)
  obtain ⟨v, hv, hKv⟩ := exists_unit_i_eigenvector_of_rotation K hx0 hKx hKy
  exact ⟨α, v, hα, hv, hKv⟩

end QuaternionicColumns

end Wikipedia.HomotopyGroupsOfSpheres
