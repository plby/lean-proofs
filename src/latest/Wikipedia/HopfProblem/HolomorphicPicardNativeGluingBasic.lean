import Wikipedia.HopfProblem.HolomorphicExponentialSheafUnitsSections
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1Cech

/-!
# Pointwise identities of actual unit-valued Čech cocycles

The genuine additive-sheaf restriction identity becomes the multiplicative
identity of the underlying nowhere-zero holomorphic functions. These
identities are proved by evaluating the original sheaf sections.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicPicardNative

open HolomorphicExponentialSheaf
open HolomorphicFunctionSheaf.SphereH1

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  {ι : Type} (U : ι → Opens M)
  (c : CechOneCocycle (unitsSheaf I M) U)

/-- Evaluation of the actual restriction identity gives the native
transition multiplication order. -/
theorem cocycle_unit_eval_comp (i j k : ι) (x : M)
    (hi : x ∈ U i) (hj : x ∈ U j) (hk : x ∈ U k) :
    unitSectionEval (c.value j k) ⟨x, hj, hk⟩ *
      unitSectionEval (c.value i j) ⟨x, hi, hj⟩ =
        unitSectionEval (c.value i k) ⟨x, hi, hk⟩ := by
  have h : unitSectionEval (c.value i j) ⟨x, hi, hj⟩ *
      unitSectionEval (c.value j k) ⟨x, hj, hk⟩ =
        unitSectionEval (c.value i k) ⟨x, hi, hk⟩ :=
    congrArg (fun u : UnitSection I M ((U i ⊓ U j) ⊓ U k) =>
      unitSectionEval u ⟨x, ⟨hi, hj⟩, hk⟩) (c.condition i j k)
  simpa only [mul_comm] using h

/-- The diagonal cocycle section evaluates to one, as a consequence of
the Čech identity and the actual unit's nonvanishing. -/
theorem cocycle_unit_eval_self (i : ι) (x : M) (hx : x ∈ U i) :
    unitSectionEval (c.value i i) ⟨x, hx, hx⟩ = 1 := by
  apply mul_left_cancel₀ (unitSectionEval_ne_zero (c.value i i) ⟨x, hx, hx⟩)
  simpa only [mul_one] using cocycle_unit_eval_comp I M U c i i i x hx hx hx

/-- Opposite overlap values are actual multiplicative inverses. -/
theorem cocycle_unit_eval_inverse_mul (i j : ι) (x : M)
    (hi : x ∈ U i) (hj : x ∈ U j) :
    unitSectionEval (c.value j i) ⟨x, hj, hi⟩ *
      unitSectionEval (c.value i j) ⟨x, hi, hj⟩ = 1 :=
  (cocycle_unit_eval_comp I M U c i j i x hi hj hi).trans
    (cocycle_unit_eval_self I M U c i x hi)

end Wikipedia.HopfProblem.HolomorphicPicardNative
