import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumnSphere
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Quaternionic matrices as real linear maps

The real representation is the ordinary matrix action on the L² quaternionic
vector space. Hermitian adjoints and norm preservation are proved directly
from matrix multiplication, without assumptions about homotopy groups.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

open QuaternionicRankOne

local notation "ℍ" => Quaternion ℝ

variable {N : Type*} [Fintype N] [DecidableEq N]

omit [DecidableEq N] in
theorem pairing_mulVec_left (A : Matrix N N ℍ) (u v : N → ℍ) :
    pairing (A *ᵥ u) v = pairing u (star A *ᵥ v) := by
  simp only [pairing, Matrix.mulVec, dotProduct, star_sum, star_mul,
    Finset.sum_mul, Finset.mul_sum, Matrix.star_apply, mul_assoc]
  rw [Finset.sum_comm]

theorem pairing_unitary_mulVec (A : SpGroup N) (u v : N → ℍ) :
    pairing (A.val *ᵥ u) (A.val *ᵥ v) = pairing u v := by
  rw [pairing_mulVec_left, Matrix.mulVec_mulVec,
    Unitary.coe_star_mul_self, Matrix.one_mulVec]

theorem unitary_mulVec_norm (A : SpGroup N) (v : N → ℍ) :
    ‖(WithLp.toLp 2 (A.val *ᵥ v) : PiLp 2 (fun _ : N => ℍ))‖ =
      ‖(WithLp.toLp 2 v : PiLp 2 (fun _ : N => ℍ))‖ := by
  have h := pairing_unitary_mulVec A v v
  rw [pairing_self_eq_norm_sq, pairing_self_eq_norm_sq] at h
  have hr := congrArg (fun q : ℍ => q.re) h
  change ‖(WithLp.toLp 2 (A.val *ᵥ v) : PiLp 2 (fun _ : N => ℍ))‖ ^ 2 =
    ‖(WithLp.toLp 2 v : PiLp 2 (fun _ : N => ℍ))‖ ^ 2 at hr
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hr

/-- The real-linear action on the original quaternionic L² space. -/
def lpAction (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ) :
    QuaternionSpace n →ₗ[ℝ] QuaternionSpace n :=
  (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℍ)).symm.toLinearMap.comp
    ((Matrix.mulVecBilin ℝ ℝ A).comp
      (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℍ)).toLinearMap)

theorem lpAction_apply (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ)
    (v : QuaternionSpace n) :
    lpAction n A v = WithLp.toLp 2 (A *ᵥ WithLp.ofLp v) := rfl

theorem lpAction_one (n : ℕ) : lpAction n 1 = LinearMap.id := by
  apply LinearMap.ext
  intro v
  simp only [lpAction_apply, Matrix.one_mulVec, WithLp.toLp_ofLp, LinearMap.id_apply]

theorem lpAction_mul (n : ℕ) (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ) :
    lpAction n (A * B) = (lpAction n A).comp (lpAction n B) := by
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, lpAction_apply, Matrix.mulVec_mulVec]

theorem lpAction_norm (n : ℕ) (A : SpGroup (Fin (n + 1))) (v : QuaternionSpace n) :
    ‖lpAction n A.val v‖ = ‖v‖ :=
  unitary_mulVec_norm A (WithLp.ofLp v)

/-- Orthonormal real coordinates for the same matrix action. -/
def realActionLinear (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ) :
    EuclideanSpace ℝ (Fin (4 * n + 4)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (4 * n + 4)) :=
  (quaternionCoordinates n).toLinearEquiv.toLinearMap.comp
    ((lpAction n A).comp (quaternionCoordinates n).symm.toLinearEquiv.toLinearMap)

def realAction (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ) :
    EuclideanSpace ℝ (Fin (4 * n + 4)) →L[ℝ] EuclideanSpace ℝ (Fin (4 * n + 4)) :=
  (realActionLinear n A).toContinuousLinearMap

theorem realAction_apply (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ)
    (v : EuclideanSpace ℝ (Fin (4 * n + 4))) :
    realAction n A v = quaternionCoordinates n
      (WithLp.toLp 2 (A *ᵥ WithLp.ofLp ((quaternionCoordinates n).symm v))) := rfl

theorem realAction_norm (n : ℕ) (A : SpGroup (Fin (n + 1)))
    (v : EuclideanSpace ℝ (Fin (4 * n + 4))) : ‖realAction n A.val v‖ = ‖v‖ := by
  change ‖quaternionCoordinates n (lpAction n A.val ((quaternionCoordinates n).symm v))‖ = ‖v‖
  rw [(quaternionCoordinates n).norm_map, lpAction_norm, (quaternionCoordinates n).symm.norm_map]

theorem realAction_one (n : ℕ) : realAction n 1 = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  rw [realAction_apply, Matrix.one_mulVec, WithLp.toLp_ofLp,
    (quaternionCoordinates n).apply_symm_apply]
  rfl

theorem realAction_mul (n : ℕ) (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ) :
    realAction n (A * B) = (realAction n A).comp (realAction n B) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, realAction_apply,
    (quaternionCoordinates n).symm_apply_apply, WithLp.ofLp_toLp, Matrix.mulVec_mulVec]

theorem continuous_realAction (n : ℕ) : Continuous (realAction n) := by
  apply continuous_clm_apply.mpr
  intro v
  have h : Continuous (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ =>
      A *ᵥ WithLp.ofLp ((quaternionCoordinates n).symm v)) := by
    apply continuous_pi
    intro i
    change Continuous (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ =>
      ∑ k, A i k * WithLp.ofLp ((quaternionCoordinates n).symm v) k)
    apply continuous_finsetSum
    intro k _
    exact (continuous_id.matrix_elem i k).mul continuous_const
  have he := ((PiLp.homeomorph 2 (fun _ : Fin (n + 1) => ℍ)).symm.continuous).comp h
  exact (quaternionCoordinates n).continuous.comp he

theorem realAction_injective (n : ℕ) : Function.Injective (realAction n) := by
  intro A B h
  apply Matrix.ext
  intro i j
  have he := congrArg (fun L => (quaternionCoordinates n).symm
    (L (quaternionCoordinates n (WithLp.toLp 2 (axis j))))) h
  simp only [realAction_apply, (quaternionCoordinates n).symm_apply_apply,
    WithLp.ofLp_toLp] at he
  have hi := congrArg (fun v : QuaternionSpace n => WithLp.ofLp v i) he
  simpa [Matrix.mulVec, dotProduct, axis, Pi.single_apply] using hi

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
