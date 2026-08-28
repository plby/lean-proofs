import Wikipedia.HopfProblem.ToricReduction
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Instances.Matrix

/-!
# The inverse real displacement for cusp straightening

The matrix `B_t` of the source is the already constructed displacement map.
Its total matrix inverse supplies an unconditionally linear function; on
the small-drift domain it is the genuine inverse, with norm bound `2`.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.ToricSpace

def displacementMatrix (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; -1, 0] + (Real.log ‖t‖)⁻¹ • driftMatrix C t

theorem displacementMatrix_mulVec (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (t : ℂ) (y : Fin 2 → ℝ) : displacementMatrix C t *ᵥ y = displacement C t y := by
  rw [displacementMatrix, Matrix.add_mulVec, Matrix.smul_mulVec]
  change !![(0 : ℝ), 1; -1, 0] *ᵥ y +
    (Real.log ‖t‖)⁻¹ • (driftMatrix C t *ᵥ y) =
    realCuspVector y + (Real.log ‖t‖)⁻¹ • (driftMatrix C t *ᵥ y)
  congr 1
  ext i
  fin_cases i <;> simp [realCuspVector, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

def inverseDisplacement (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) :
    (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
  (displacementMatrix C t)⁻¹.mulVecLin

@[simp] theorem inverseDisplacement_zero (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) :
    inverseDisplacement C t 0 = 0 := map_zero _

@[simp] theorem inverseDisplacement_add (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (t : ℂ) (y z : Fin 2 → ℝ) :
    inverseDisplacement C t (y + z) = inverseDisplacement C t y + inverseDisplacement C t z :=
  map_add _ _ _

@[simp] theorem inverseDisplacement_smul (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (t : ℂ) (a : ℝ) (y : Fin 2 → ℝ) :
    inverseDisplacement C t (a • y) = a • inverseDisplacement C t y := map_smul _ _ _

theorem displacementMatrix_isUnit (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {t : ℂ}
    (ht : Real.log ‖t‖ < 0)
    (hR : entryNorm (driftMatrix C t) ≤ -Real.log ‖t‖ / 4) :
    IsUnit (displacementMatrix C t) := by
  apply Matrix.mulVec_surjective_iff_isUnit.mp
  intro y
  obtain ⟨z, hz⟩ := (displacement_bijective C ht hR).surjective y
  exact ⟨z, (displacementMatrix_mulVec C t z).trans hz⟩

theorem displacementMatrix_det_ne_zero (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {t : ℂ}
    (ht : Real.log ‖t‖ < 0)
    (hR : entryNorm (driftMatrix C t) ≤ -Real.log ‖t‖ / 4) :
    (displacementMatrix C t).det ≠ 0 :=
  isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp (displacementMatrix_isUnit C ht hR))

theorem inverseDisplacement_displacement (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {t : ℂ}
    (ht : Real.log ‖t‖ < 0)
    (hR : entryNorm (driftMatrix C t) ≤ -Real.log ‖t‖ / 4) (y : Fin 2 → ℝ) :
    inverseDisplacement C t (displacement C t y) = y := by
  change (displacementMatrix C t)⁻¹ *ᵥ displacement C t y = y
  rw [← displacementMatrix_mulVec, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (displacementMatrix_det_ne_zero C ht hR)),
    Matrix.one_mulVec]

theorem displacement_inverseDisplacement (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {t : ℂ}
    (ht : Real.log ‖t‖ < 0)
    (hR : entryNorm (driftMatrix C t) ≤ -Real.log ‖t‖ / 4) (y : Fin 2 → ℝ) :
    displacement C t (inverseDisplacement C t y) = y := by
  rw [← displacementMatrix_mulVec]
  change displacementMatrix C t *ᵥ ((displacementMatrix C t)⁻¹ *ᵥ y) = y
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (displacementMatrix_det_ne_zero C ht hR)),
    Matrix.one_mulVec]

theorem inverseDisplacement_norm_le (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {t : ℂ}
    (ht : Real.log ‖t‖ < 0)
    (hR : entryNorm (driftMatrix C t) ≤ -Real.log ‖t‖ / 4) (y : Fin 2 → ℝ) :
    ‖inverseDisplacement C t y‖ ≤ 2 * ‖y‖ := by
  have h := displacement_lower_bound C ht hR (inverseDisplacement C t y)
  rwa [displacement_inverseDisplacement C ht hR y] at h

theorem displacementMatrix_continuousAt (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {t : ℂ}
    (hC : ∀ i j, ContinuousAt (fun s => C s i j) t)
    (ht0 : t ≠ 0) (htlog : Real.log ‖t‖ ≠ 0) : ContinuousAt (displacementMatrix C) t := by
  have hlog : ContinuousAt (fun s : ℂ => (Real.log ‖s‖)⁻¹) t :=
    ((Real.continuousAt_log (norm_ne_zero_iff.mpr ht0)).comp
      continuous_norm.continuousAt).inv₀ htlog
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  change ContinuousAt (fun s : ℂ =>
    !![(0 : ℝ), 1; -1, 0] i j + (Real.log ‖s‖)⁻¹ * (-2 * Real.pi * (C s i j).im)) t
  exact continuousAt_const.add
    (hlog.mul (continuousAt_const.mul (Complex.continuous_im.continuousAt.comp (hC i j))))

theorem inverseDisplacement_continuousAt_of_det_ne_zero
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {t : ℂ}
    (hC : ∀ i j, ContinuousAt (fun s => C s i j) t)
    (ht0 : t ≠ 0) (htlog : Real.log ‖t‖ ≠ 0)
    (hdet : (displacementMatrix C t).det ≠ 0) (y : Fin 2 → ℝ) :
    ContinuousAt (fun p : ℂ × (Fin 2 → ℝ) => inverseDisplacement C p.1 p.2) (t, y) := by
  have hi : ContinuousAt (fun s : ℂ => (displacementMatrix C s)⁻¹) t :=
    (continuousAt_matrix_inv (displacementMatrix C t) (by
      simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hdet)).comp
      (displacementMatrix_continuousAt C hC ht0 htlog)
  have hm : Continuous
      (fun p : Matrix (Fin 2) (Fin 2) ℝ × (Fin 2 → ℝ) => p.1 *ᵥ p.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  have hp : ContinuousAt
      (fun p : ℂ × (Fin 2 → ℝ) => (displacementMatrix C p.1)⁻¹) (t, y) :=
    ContinuousAt.comp (f := fun p : ℂ × (Fin 2 → ℝ) => p.1)
      (g := fun s : ℂ => (displacementMatrix C s)⁻¹)
      hi continuous_fst.continuousAt
  exact hm.continuousAt.comp (hp.prodMk continuous_snd.continuousAt)

theorem inverseDisplacement_continuousAt (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {t : ℂ}
    (hC : ∀ i j, ContinuousAt (fun s => C s i j) t)
    (ht : Real.log ‖t‖ < 0)
    (hR : entryNorm (driftMatrix C t) ≤ -Real.log ‖t‖ / 4) (y : Fin 2 → ℝ) :
    ContinuousAt (fun p : ℂ × (Fin 2 → ℝ) => inverseDisplacement C p.1 p.2) (t, y) := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht
  exact inverseDisplacement_continuousAt_of_det_ne_zero C hC ht0 ht.ne
    (displacementMatrix_det_ne_zero C ht hR) y

end Wikipedia.HopfProblem.ToricSpace
