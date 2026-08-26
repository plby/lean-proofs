import ErdosProblems.Erdos1002.WindowErrorReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The primitive resonance shot sum as a circle L² function

The manuscript compares the finite-denominator Fourier reconstruction with
the literal nearest-cell shot sum.  This file puts the latter into the same
Hilbert space.  The construction uses the half-open fundamental interval and
an explicit finite pointwise bound, so no periodic representative or endpoint
convention is implicit.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1002

noncomputable section

/-- The literal primitive shot sum, represented on the unit additive circle
using the fundamental interval `(0,1]`. -/
def primitiveShotSumCircle (N P : ℕ) : AddCircle (1 : ℝ) → ℂ :=
  AddCircle.liftIoc 1 0 fun α : ℝ ↦ (primitiveShotSum N P α : ℂ)

theorem primitiveShotSumCircle_coe
    {N P : ℕ} {α : ℝ} (hα : α ∈ Ioc (0 : ℝ) 1) :
    primitiveShotSumCircle N P (α : AddCircle (1 : ℝ)) =
      (primitiveShotSum N P α : ℂ) := by
  exact AddCircle.liftIoc_coe_apply (by simpa using! hα)

/-- Explicit finite bound for the whole primitive shot sum. -/
def primitiveShotSumBound (N P : ℕ) : ℝ :=
  ∑ p ∈ Finset.Icc 1 P, (N : ℝ) / (2 * (p : ℝ))

theorem primitiveShotSumBound_nonneg (N P : ℕ) :
    0 ≤ primitiveShotSumBound N P := by
  unfold primitiveShotSumBound
  positivity

theorem norm_primitiveShotSum_le_bound (N P : ℕ) (α : ℝ) :
    ‖(primitiveShotSum N P α : ℂ)‖ ≤ primitiveShotSumBound N P := by
  unfold primitiveShotSum primitiveShotSumBound
  rw [Complex.norm_real, Real.norm_eq_abs]
  calc
    |∑ p ∈ Finset.Icc 1 P, primitiveShot N p α| ≤
        ∑ p ∈ Finset.Icc 1 P, |primitiveShot N p α| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ p ∈ Finset.Icc 1 P, ‖(primitiveShot N p α : ℂ)‖ := by
      apply Finset.sum_congr rfl
      intro p _hp
      simp only [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ p ∈ Finset.Icc 1 P, (N : ℝ) / (2 * (p : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact norm_primitiveShot_le N p α (Finset.mem_Icc.mp hp).1

private theorem primitiveShotSum_memLp_Ioc (N P : ℕ) :
    MemLp (fun α : ℝ ↦ (primitiveShotSum N P α : ℂ)) 2
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
  apply MemLp.of_bound
    (measurable_primitiveShotSum N P).complex_ofReal.aestronglyMeasurable
    (primitiveShotSumBound N P)
  filter_upwards with α
  exact norm_primitiveShotSum_le_bound N P α

theorem primitiveShotSumCircle_memLp (N P : ℕ) :
    MemLp (primitiveShotSumCircle N P) 2
      (@AddCircle.haarAddCircle (1 : ℝ) inferInstance) := by
  have hIoc :
      MemLp (fun α : ℝ ↦ (primitiveShotSum N P α : ℂ)) 2
        (volume.restrict (Ioc (0 : ℝ) (0 + 1))) := by
    simpa using! primitiveShotSum_memLp_Ioc N P
  exact (hIoc.memLp_liftIoc.haarAddCircle :
    MemLp (AddCircle.liftIoc 1 0
      (fun α : ℝ ↦ (primitiveShotSum N P α : ℂ))) 2
      (@AddCircle.haarAddCircle (1 : ℝ) inferInstance))

/-- The actual `L²(AddCircle 1)` class of the primitive shot sum. -/
def primitiveShotSumL2 (N P : ℕ) : UnitCircleL2 :=
  (primitiveShotSumCircle_memLp N P).toLp (primitiveShotSumCircle N P)

theorem primitiveShotSumL2_coe_ae (N P : ℕ) :
    (primitiveShotSumL2 N P : AddCircle (1 : ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle] primitiveShotSumCircle N P := by
  exact (primitiveShotSumCircle_memLp N P).coeFn_toLp

/-- The central shot sum `Y_N` in circle `L²`. -/
def reconstructedShotL2 (N : ℕ) : UnitCircleL2 :=
  primitiveShotSumL2 N N

theorem reconstructedShotL2_coe_ae (N : ℕ) :
    (reconstructedShotL2 N : AddCircle (1 : ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle] primitiveShotSumCircle N N :=
  primitiveShotSumL2_coe_ae N N

end

end Erdos1002
