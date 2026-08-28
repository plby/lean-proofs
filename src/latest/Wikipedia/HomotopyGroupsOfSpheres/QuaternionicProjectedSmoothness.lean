import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicProjectedCurveKernel
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Smoothness of the actual projected Bott formula

The inverse in the Schur expression has a nonzero denominator everywhere
on the symmetric-unitary parameter space. Smooth parameter families thus
give smooth first-column families, without any assumed local regularity.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres

namespace QuaternionicBottMatrix

open QuaternionicComplexPlane QuaternionicSymmetricMatrices QuaternionicScalars

local notation "ℍ" => Quaternion ℝ

local instance : StarModule ℝ ℍ where
  star_smul r q := by simp [Quaternion.star_smul]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ∞ω}

theorem contDiff_rotation_entry (s t : E → ℝ) (B : E → Space (Fin 3))
    (hs : ContDiff ℝ n s) (ht : ContDiff ℝ n t)
    (hB : ∀ r q, ContDiff ℝ n (fun y ↦ (B y).val.val r q)) (r q : Fin 3) :
    ContDiff ℝ n (fun y ↦ (rotation (s y) (t y) (B y)).val r q) := by
  have he : ContDiff ℝ n (fun y ↦ embed ((B y).val.val r q)) :=
    (coeComplexCLM.contDiff.comp (hB r q)).mul contDiff_const
  simp only [rotation_val, matrix_apply]
  exact ((hs.cos.smul contDiff_const).add
    ((hs.sin.mul ht.cos).smul contDiff_const)).add ((hs.sin.mul ht.sin).smul he)

theorem contDiff_scalarRotation (s t : E → ℝ)
    (hs : ContDiff ℝ n s) (ht : ContDiff ℝ n t) :
    ContDiff ℝ n (fun y ↦ scalarRotation (s y) (t y)) := by
  exact ((hs.cos.smul contDiff_const).add
    ((hs.sin.mul ht.cos).smul contDiff_const)).add
      ((hs.sin.mul ht.sin).smul contDiff_const)

theorem contDiff_firstColumnFormula_entry (s t : E → ℝ) (B : E → Space (Fin 3))
    (hs : ContDiff ℝ n s) (ht : ContDiff ℝ n t)
    (hB : ∀ r q, ContDiff ℝ n (fun y ↦ (B y).val.val r q)) (r : Fin 2) :
    ContDiff ℝ n (fun y ↦ firstColumnFormula (s y) (t y) (B y) r) := by
  have hA := contDiff_rotation_entry s t B hs ht hB
  have hi : ContDiff ℝ n (fun y ↦ (1 + (rotation (s y) (t y) (B y)).val 1 0)⁻¹) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    have hinv : ContDiffAt ℝ n (fun q : ℍ ↦ q⁻¹)
        (1 + (rotation (s y) (t y) (B y)).val 1 0) := by
      convert (contDiffAt_ringInverse ℝ
        (Units.mk0 _ (rotation_pivot_denominator_ne_zero (s y) (t y) (B y)))) using 1 <;>
        try rfl
      funext q
      exact congrFun Ring.inverse_eq_inv'.symm q
    exact hinv.comp y (contDiff_const.add (hA 1 0)).contDiffAt
  have href := (starL' ℝ : ℍ ≃L[ℝ] ℍ).contDiff.comp
    (((contDiff_scalarRotation s t hs ht).mul
      (contDiff_scalarRotation s t hs ht)).neg)
  exact ((hA (remainingRow r) 1).sub
    (((hA (remainingRow r) 0).mul hi).mul (hA 1 1))).mul href

end QuaternionicBottMatrix

namespace ComplexCrossProductUnitary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ∞ω}

theorem contDiff_matrix_entry (z : E → Vector)
    (hz : ∀ r, ContDiff ℝ n (fun y ↦ z y r)) (r q : Fin 3) :
    ContDiff ℝ n (fun y ↦ matrix (z y) r q) := by
  have hc : ContDiff ℝ n (fun y ↦ crossMatrix (fun k ↦ star (z y k)) r q) := by
    have hzstar (k : Fin 3) : ContDiff ℝ n (fun y ↦ star (z y k)) :=
      (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp (hz k)
    fin_cases r <;> fin_cases q
    all_goals first
      | exact contDiff_const
      | exact hzstar 0
      | exact hzstar 1
      | exact hzstar 2
      | exact (hzstar 0).neg
      | exact (hzstar 1).neg
      | exact (hzstar 2).neg
  exact ((hz r).mul (hz q)).add hc

theorem contDiff_symmetricMap_entry (z : E → UnitSphere)
    (hz : ∀ r, ContDiff ℝ n (fun y ↦ (z y).val r)) (r q : Fin 3) :
    ContDiff ℝ n (fun y ↦ (symmetricMap (z y)).val.val r q) := by
  have he : (fun y ↦ (symmetricMap (z y)).val.val r q) =
      fun y ↦ ∑ k, matrix (z y).val r k * matrix (z y).val q k := by
    funext y
    rw [symmetricMap_val]
    rfl
  rw [he]
  exact ContDiff.sum (fun k _ ↦
    (contDiff_matrix_entry _ hz r k).mul (contDiff_matrix_entry _ hz q k))

end ComplexCrossProductUnitary
end Wikipedia.HomotopyGroupsOfSpheres
