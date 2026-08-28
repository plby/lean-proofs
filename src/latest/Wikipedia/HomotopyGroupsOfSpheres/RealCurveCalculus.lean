import Wikipedia.HomotopyGroupsOfSpheres.FiniteSubmoduleProjection
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! # Real curve calculus with explicit normed-space parameters -/

namespace Wikipedia.HomotopyGroupsOfSpheres

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem real_hasDerivAt_smul (v : E) (x : ℝ) :
    HasDerivAt (fun s : ℝ => s • v) v x := by
  simpa only [one_smul, id_eq] using! (hasDerivAt_id x).smul_const v

theorem real_hasDerivAt_comp_smul_zero {f : E → E} {c : ℝ}
    (h : HasFDerivAt f (realScalarOperator E c) 0) (v : E) :
    HasDerivAt (fun s : ℝ => f (s • v)) (c • v) 0 := by
  have hf : HasFDerivAt f (realScalarOperator E c) ((0 : ℝ) • v) := by
    simpa only [zero_smul] using h
  exact hf.comp_hasDerivAt 0 (real_hasDerivAt_smul v 0)

theorem real_deriv_eq_of_hasDerivAt {f : ℝ → E} {D : E} {x : ℝ}
    (h : HasDerivAt f D x) : deriv f x = D := h.deriv

theorem real_hasDerivAt_pi {ι : Type*} {f : ℝ → ι → E} {D : ι → E} {x : ℝ}
    (h : ∀ i, HasDerivAt (fun s => f s i) (D i) x) : HasDerivAt f D x :=
  hasDerivAt_pi.mpr h

omit [NormedSpace ℝ E] in
theorem real_continuousAt_neg {X : Type*} [TopologicalSpace X] {f : X → E} {x : X}
    (h : ContinuousAt f x) : ContinuousAt (fun y => -f y) x := h.neg

end Wikipedia.HomotopyGroupsOfSpheres
