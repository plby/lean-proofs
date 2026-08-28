import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Entire functions with constant increments along a full lattice

A continuous function periodic under a full real lattice has compact
range. Liouville therefore makes every entire periodic function constant.
For a complex-analytic function with constant lattice increments, its
actual Fréchet derivative is periodic and hence constant. Integrating this
constant derivative gives the affine formula with linear part `fderiv f 0`.
No boundedness, constancy, or affine normal form is supplied as a premise.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.PeriodTorusQuasiperiodic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Constant increments make the actual derivative periodic, including
at points where the total derivative is defined by its default value. -/
theorem fderiv_periodic_of_constant_increments (L : Submodule ℤ E) (f : E → F)
    (hinc : ∀ w ∈ L, ∃ c : F, ∀ z, f (z + w) = f z + c) :
    ∀ z w, w ∈ L → fderiv ℂ f (z + w) = fderiv ℂ f z := by
  intro z w hw
  obtain ⟨c, hc⟩ := hinc w hw
  calc
    fderiv ℂ f (z + w) = fderiv ℂ (fun x => f (x + w)) z :=
      (fderiv_comp_add_right w).symm
    _ = fderiv ℂ (fun x => f x + c) z :=
      congrArg (fun g : E → F => fderiv ℂ g z) (funext hc)
    _ = fderiv ℂ f z := fderiv_add_const c

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/-- Actual full-lattice periodicity, not an assumed bound, supplies the
compact range needed by Liouville's theorem. -/
theorem eq_at_zero_of_lattice_periodic {f : E → F} (hf : Differentiable ℂ f)
    (hper : ∀ z w, w ∈ L → f (z + w) = f z) (z : E) : f z = f 0 :=
  hf.apply_eq_apply_of_bounded
    (IsZLattice.isCompact_range_of_periodic L f hf.continuous hper).isBounded z 0

/-- Two complex derivatives suffice for the actual first derivative
to be entire; compact lattice periodicity then makes it constant. -/
theorem fderiv_eq_at_zero_of_lattice_quasiperiodic {f : E → F}
    (hf : ContDiff ℂ 2 f)
    (hinc : ∀ w ∈ L, ∃ c : F, ∀ z, f (z + w) = f z + c) (z : E) :
    fderiv ℂ f z = fderiv ℂ f 0 := by
  have hd : ContDiff ℂ 1 (fderiv ℂ f) := hf.fderiv_right (by norm_num)
  exact eq_at_zero_of_lattice_periodic L (hd.differentiable (by simp))
    (fderiv_periodic_of_constant_increments L f hinc) z

/-- An entire function with constant full-lattice increments is the
actual affine function determined by its value and derivative at zero. -/
theorem affine_of_lattice_quasiperiodic {f : E → F} (hf : ContDiff ℂ 2 f)
    (hinc : ∀ w ∈ L, ∃ c : F, ∀ z, f (z + w) = f z + c) (z : E) :
    f z = f 0 + (fderiv ℂ f 0) z := by
  let A := fderiv ℂ f 0
  have he : f = fun x => f 0 + A x := by
    refine eq_of_fderiv_eq (hf.differentiable (by norm_num))
      (A.differentiable.const_add (f 0)) (fun x => ?_) (0 : E) ?_
    · exact (fderiv_eq_at_zero_of_lattice_quasiperiodic L hf hinc x).trans
        ((A.hasFDerivAt.const_add (f 0)).fderiv.symm)
    · simp
  exact congrFun he z

/-- The additive increment is exactly the actual affine linear part
evaluated on the corresponding lattice vector. -/
theorem increment_eq_fderiv {f : E → F} (hf : ContDiff ℂ 2 f)
    (hinc : ∀ w ∈ L, ∃ c : F, ∀ z, f (z + w) = f z + c)
    {w : E} {c : F} (hc : ∀ z, f (z + w) = f z + c) :
    c = (fderiv ℂ f 0) w := by
  have h := hc 0
  rw [zero_add, affine_of_lattice_quasiperiodic L hf hinc w] at h
  exact (add_left_cancel h).symm

/-- If the actual derivative at zero vanishes, all points have the
same value and every constant lattice increment vanishes. -/
theorem eq_at_zero_of_lattice_quasiperiodic_of_fderiv_zero {f : E → F}
    (hf : ContDiff ℂ 2 f)
    (hinc : ∀ w ∈ L, ∃ c : F, ∀ z, f (z + w) = f z + c)
    (hzero : fderiv ℂ f 0 = 0) (z : E) : f z = f 0 := by
  rw [affine_of_lattice_quasiperiodic L hf hinc z, hzero]
  simp

end Wikipedia.HopfProblem.PeriodTorusQuasiperiodic
