import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionPeriod
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixedDescent

/-!
# A genuine vector translation cannot project to a constant orbit

A curve in a single fibre of a local homeomorphism is constant when its
parameter space is connected.  Apply this to the original complex
vector-cover translation and compare its second coordinates at times
zero and one.  This concerns being fixed by every time, not stabilizers
of individual times after a period quotient.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedVectors

variable {B Q : Type*}

theorem vectorFlow_continuous [TopologicalSpace B] (x : B × ComplexPlane₂) :
    Continuous (fun s : ℂ => Period.vectorFlow s x) :=
  continuous_const.prodMk (continuous_const.add Period.vector_holomorphic.continuous)

@[simp] theorem vectorFlow_zero (x : B × ComplexPlane₂) : Period.vectorFlow 0 x = x := by
  simp only [Period.vectorFlow, Period.vector_zero, add_zero, Prod.mk.eta]

theorem vectorFlow_one_ne_self (x : B × ComplexPlane₂) : Period.vectorFlow 1 x ≠ x := by
  intro h
  have he := congrArg (fun y : B × ComplexPlane₂ => y.2 1) h
  change x.2 1 + 1 = x.2 1 at he
  exact one_ne_zero (add_left_cancel (he.trans (add_zero _).symm))

/-- For the actual complex vector translation, no entire orbit can lie
in one fibre of a local homeomorphism. -/
theorem not_forall_vectorFlow_projection_eq_self [TopologicalSpace B] [TopologicalSpace Q]
    (q : B × ComplexPlane₂ → Q)
    (hq : IsLocalHomeomorph q) (x : B × ComplexPlane₂) :
    ¬ ∀ s : ℂ, q (Period.vectorFlow s x) = q x := by
  intro h
  have he := FixedDescent.eq_const_of_isLocalHomeomorph hq
    (vectorFlow_continuous x) (vectorFlow_zero x) h
  exact vectorFlow_one_ne_self x (he 1)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedVectors
