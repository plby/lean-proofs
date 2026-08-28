import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Stereographic inversion through the antipodal chart

Mathlib's stereographic coordinate has scale two. Inversion in the unit
coordinate sphere is therefore the antipode of the same inverse chart
at minus four times the coordinate. The latter formula extends smoothly
through zero, which will parametrize the complementary disk.
-/

noncomputable section

open Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.SmoothSixDPoincare.SphereCoordinates

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem norm_unit_inversion (w : V) : ‖(‖w‖ ^ 2)⁻¹ • w‖ = ‖w‖⁻¹ := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (sq_nonneg _)]
  by_cases hw : ‖w‖ = 0
  · simp only [hw, zero_pow (by norm_num : 2 ≠ 0), inv_zero, mul_zero]
  · field_simp

theorem stereoInvFunAux_inversion (v : V) {w : V} (hw : w ≠ 0) :
    stereoInvFunAux v ((‖w‖ ^ 2)⁻¹ • w) =
      -stereoInvFunAux v ((-4 : ℝ) • w) := by
  have hs : 0 < ‖w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hw)
  have hnorm : ‖(‖w‖ ^ 2)⁻¹ • w‖ ^ 2 = (‖w‖ ^ 2)⁻¹ := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs, mul_pow]
    field_simp
  have hnorm' : ‖(-4 : ℝ) • w‖ ^ 2 = 16 * ‖w‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow]
    norm_num
  have hd₁ : (‖w‖ ^ 2)⁻¹ + 4 ≠ 0 := by positivity
  have hd₂ : 16 * ‖w‖ ^ 2 + 4 ≠ 0 := by positivity
  simp only [stereoInvFunAux_apply, hnorm, hnorm']
  match_scalars <;> field_simp [hs.ne', hd₁, hd₂] <;> ring

variable {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]

theorem stereographic_symm_inversion (v : sphere (0 : V) 1)
    {w : EuclideanSpace ℝ (Fin n)} (hw : w ≠ 0) :
    (stereographic' n v).symm ((‖w‖ ^ 2)⁻¹ • w) =
      -(stereographic' n v).symm ((-4 : ℝ) • w) := by
  let U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] (ℝ ∙ (v : V))ᗮ :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton n
    (ne_zero_of_mem_unit_sphere v)).repr.symm
  have hnorm : ‖(U w : V)‖ = ‖w‖ := U.norm_map w
  have hne : (U w : V) ≠ 0 := by
    intro h
    have hz : U w = 0 := Subtype.ext h
    exact hw (U.injective (hz.trans U.map_zero.symm))
  apply Subtype.ext
  change stereoInvFunAux (v : V) (U ((‖w‖ ^ 2)⁻¹ • w) : V) =
    -stereoInvFunAux (v : V) (U ((-4 : ℝ) • w) : V)
  simp only [map_smul, Submodule.coe_smul]
  rw [← hnorm]
  exact stereoInvFunAux_inversion (v : V) hne

end Wikipedia.SmoothSixDPoincare.SphereCoordinates
