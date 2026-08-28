import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1NegativeOneFrames

/-!
# Pointwise formulas for the genuine O(-infinity) ideal frames

The ideal-sheaf frames on every subopen of the finite and reciprocal
charts are the actual functions `1` and `w`.  This file records their
evaluation formulas and their relation to the already constructed
holomorphic transition unit on the actual overlap.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.CanonicalGlobal.BaseTwist

open HolomorphicFunctionSheaf.SphereH1

/-- The pointwise values of the genuine local ideal frames.  Analyticity
is only asserted on each frame's original chart, as in `chartFrame`. -/
def idealFrameValue : Bool → RiemannSphere → ℂ
  | false => fun _ => 1
  | true => fromFinite (fun z : ℂ => z⁻¹) 0

@[simp] theorem idealFrameValue_false (p : RiemannSphere) :
    idealFrameValue false p = 1 := rfl

@[simp] theorem idealFrameValue_true_coe (z : ℂ) :
    idealFrameValue true (z : RiemannSphere) = z⁻¹ := rfl

@[simp] theorem idealFrameValue_true_infty :
    idealFrameValue true (∞ : RiemannSphere) = 0 := rfl

/-- Every actual subopen frame has the same literal pointwise formula. -/
theorem chartFrame_value (b : Bool) (U : Opens RiemannSphere)
    (hU : U ≤ NegativeOneFrames.frameChart b) (p : U) :
    (NegativeOneFrames.chartFrame b U hU).val p = idealFrameValue b p := by
  cases b <;> rfl

/-- The ideal-section trivialization is actual multiplication of the
holomorphic coefficient by `1` or `w`, on every chart subopen. -/
theorem chartTrivialization_value (b : Bool) (U : Opens RiemannSphere)
    (hU : U ≤ NegativeOneFrames.frameChart b)
    (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U) (p : U) :
    (NegativeOneFrames.chartTrivialization b U hU f).val p =
      f p * idealFrameValue b p := by
  rw [NegativeOneFrames.chartTrivialization_as_frame]
  change f p * (NegativeOneFrames.chartFrame b U hU).val p = _
  rw [chartFrame_value]

/-- The finite frame is the finite-coordinate multiple of the reciprocal
frame on the actual overlap. -/
theorem idealFrameValue_false_eq_inverse_transition
    (p : NegativeOneFrames.chartOverlap) :
    idealFrameValue false p = NegativeOneFrames.inverseTransitionCoefficient p *
      idealFrameValue true p := by
  rcases p with ⟨p, hp⟩
  induction p using OnePoint.rec with
  | infty => exact (NegativeOneFrames.infty_not_mem_finiteChart hp.1).elim
  | coe z =>
    change 1 = z * z⁻¹
    exact (mul_inv_cancel₀ ((NegativeOneFrames.coe_mem_infinityChart_iff z).mp hp.2)).symm

/-- The reciprocal frame is the reciprocal-coordinate multiple of the
finite frame on the actual overlap. -/
theorem idealFrameValue_true_eq_transition
    (p : NegativeOneFrames.chartOverlap) :
    idealFrameValue true p = NegativeOneFrames.transitionCoefficient p *
      idealFrameValue false p := by
  change idealFrameValue true p = idealFrameValue true p * 1
  exact (mul_one _).symm

end Wikipedia.HopfProblem.CanonicalGlobal.BaseTwist
