import StackExchange.Puzzling139335.CornerSupport.Equality.Directions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Unit axes determined by perpendicular corner bisectors

Two perpendicular vectors of squared norm two determine an orthonormal basis
by taking half their difference and minus half their sum. These are the side
directions at the corner whose outward bisector is the first vector.
-/

namespace Puzzling139335.CornerSupport.Equality

noncomputable section

variable (U V : Plane) (hu : ‖U‖ ^ 2 = (2 : ℝ)) (hv : ‖V‖ ^ 2 = (2 : ℝ))
  (huv : inner ℝ U V = 0)

include hu hv huv in
private theorem bisector_axes_orthonormal :
    Orthonormal ℝ
      (![(1 / 2 : ℝ) • (V - U), -(1 / 2 : ℝ) • (V + U)] : Fin 2 → Plane) := by
  have hvu : inner ℝ V U = 0 := by
    rw [real_inner_comm U V]
    exact huv
  have hfirst : ‖(1 / 2 : ℝ) • (V - U)‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [norm_smul, mul_pow, norm_sub_sq_real]
    norm_num [hu, hv, hvu]
  have hsecond : ‖-(1 / 2 : ℝ) • (V + U)‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [norm_smul, mul_pow, norm_add_sq_real]
    norm_num [hu, hv, hvu]
  have hbase : inner ℝ (V - U) (V + U) = 0 := by
    simp only [inner_sub_left, inner_add_right, real_inner_self_eq_norm_sq,
      hu, hv, huv, hvu]
    norm_num
  have horthogonal :
      inner ℝ ((1 / 2 : ℝ) • (V - U)) (-(1 / 2 : ℝ) • (V + U)) = 0 := by
    rw [inner_smul_left, inner_smul_right, hbase]
    simp
  rw [orthonormal_vecCons_iff]
  refine ⟨hfirst, ?_, ?_⟩
  · intro i
    fin_cases i
    exact horthogonal
  · rw [orthonormal_vecCons_iff]
    exact ⟨hsecond, fun i => Fin.elim0 i, Orthonormal.of_isEmpty _⟩

/-- The side basis determined by two perpendicular bisectors of squared norm two. -/
def bisectorBasis : OrthonormalBasis (Fin 2) ℝ Plane :=
  OrthonormalBasis.mk (bisector_axes_orthonormal U V hu hv huv)
    ((bisector_axes_orthonormal U V hu hv huv).linearIndependent.span_eq_top_of_card_eq_finrank
      (by simp [Plane])).ge

@[simp] theorem bisectorBasis_zero :
    bisectorBasis U V hu hv huv 0 = (1 / 2 : ℝ) • (V - U) := by
  simp [bisectorBasis, OrthonormalBasis.coe_mk]

@[simp] theorem bisectorBasis_one :
    bisectorBasis U V hu hv huv 1 = -(1 / 2 : ℝ) • (V + U) := by
  simp [bisectorBasis, OrthonormalBasis.coe_mk]

/-- The inward side directions sum to minus the first outward bisector. -/
theorem bisectorBasis_sum :
    bisectorBasis U V hu hv huv 0 + bisectorBasis U V hu hv huv 1 = -U := by
  rw [bisectorBasis_zero, bisectorBasis_one]
  ext i
  simp
  ring

/-- The difference of the side directions recovers the second bisector. -/
theorem bisectorBasis_sub :
    bisectorBasis U V hu hv huv 0 - bisectorBasis U V hu hv huv 1 = V := by
  rw [bisectorBasis_zero, bisectorBasis_one]
  ext i
  simp
  ring

end

end Puzzling139335.CornerSupport.Equality
