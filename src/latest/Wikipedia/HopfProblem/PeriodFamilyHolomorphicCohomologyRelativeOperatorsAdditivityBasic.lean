import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeOperatorsDifferential

/-!
# Linearity of actual derivatives of smooth torus families

The original quotient lifts agree locally with pointwise sums and scalar
multiples. Their actual Fréchet derivatives therefore satisfy the usual
linearity identities. The descended base and vertical derivatives inherit
these identities through the original lattice quotient.
-/

noncomputable section

open TopologicalSpace Filter
open scoped Topology

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeOperators

open FourierParameter PeriodTorusLineBundleClassification

variable {U : Opens ℂ} {d : Type*} [Fintype d]

/-- The derivative of the original sum lift is the sum of the actual derivatives. -/
theorem fderiv_ambientLift_add (f g : SmoothFamily U d) (x : ℂ × (d → ℝ))
    (hx : x ∈ Smooth.baseProductDomain U (d → ℝ)) :
    fderiv ℝ (ambientLift (add f g)) x =
      fderiv ℝ (ambientLift f) x + fderiv ℝ (ambientLift g) x := by
  have he : ambientLift (add f g) =ᶠ[𝓝 x]
      (fun y => ambientLift f y + ambientLift g y) := by
    filter_upwards [(Smooth.baseProductDomain_isOpen U (d → ℝ)).mem_nhds hx] with y hy
    exact ambientLift_add f g y hy
  exact (((f.jointLift_hasFDerivAt ⟨x.1, hx⟩ x.2).add
    (g.jointLift_hasFDerivAt ⟨x.1, hx⟩ x.2)).congr_of_eventuallyEq he).fderiv

/-- Multiplication by a constant complex scalar commutes with the actual real derivative. -/
theorem fderiv_ambientLift_constMul (a : ℂ) (f : SmoothFamily U d)
    (x : ℂ × (d → ℝ)) (hx : x ∈ Smooth.baseProductDomain U (d → ℝ)) :
    fderiv ℝ (ambientLift (constMul a f)) x = a • fderiv ℝ (ambientLift f) x := by
  have he : ambientLift (constMul a f) =ᶠ[𝓝 x] (fun y => a * ambientLift f y) := by
    filter_upwards [(Smooth.baseProductDomain_isOpen U (d → ℝ)).mem_nhds hx] with y hy
    exact ambientLift_constMul a f y hy
  exact (((f.jointLift_hasFDerivAt ⟨x.1, hx⟩ x.2).const_mul a).congr_of_eventuallyEq he).fderiv

/-- The actual descended base derivative preserves the literal pointwise sum. -/
theorem baseDerivative_add (f g : SmoothFamily U d) (v : ℂ) (b : U)
    (t : UnitAddTorus d) :
    (add f g).baseDerivative v (b, t) =
      f.baseDerivative v (b, t) + g.baseDerivative v (b, t) := by
  obtain ⟨x, rfl⟩ := torusQuotient_surjective t
  rw [← ambientLift_apply ((add f g).baseDerivative v) b x,
    ← ambientLift_apply (f.baseDerivative v) b x,
    ← ambientLift_apply (g.baseDerivative v) b x,
    (add f g).ambientLift_baseDerivative v _ b.property,
    f.ambientLift_baseDerivative v _ b.property,
    g.ambientLift_baseDerivative v _ b.property,
    fderiv_ambientLift_add f g _ b.property]
  rfl

/-- Every actual real vertical derivative preserves the literal pointwise sum. -/
theorem verticalDerivative_add (f g : SmoothFamily U d) (v : d → ℝ) (b : U)
    (t : UnitAddTorus d) :
    (add f g).verticalDerivative v (b, t) =
      f.verticalDerivative v (b, t) + g.verticalDerivative v (b, t) := by
  obtain ⟨x, rfl⟩ := torusQuotient_surjective t
  rw [← ambientLift_apply ((add f g).verticalDerivative v) b x,
    ← ambientLift_apply (f.verticalDerivative v) b x,
    ← ambientLift_apply (g.verticalDerivative v) b x,
    ambientLift_verticalDerivative (add f g) v _ b.property,
    ambientLift_verticalDerivative f v _ b.property,
    ambientLift_verticalDerivative g v _ b.property,
    fderiv_ambientLift_add f g _ b.property]
  rfl

/-- The actual base derivative is complex linear in the family. -/
theorem baseDerivative_constMul (a : ℂ) (f : SmoothFamily U d) (v : ℂ) (b : U)
    (t : UnitAddTorus d) :
    (constMul a f).baseDerivative v (b, t) = a * f.baseDerivative v (b, t) := by
  obtain ⟨x, rfl⟩ := torusQuotient_surjective t
  rw [← ambientLift_apply ((constMul a f).baseDerivative v) b x,
    ← ambientLift_apply (f.baseDerivative v) b x,
    (constMul a f).ambientLift_baseDerivative v _ b.property,
    f.ambientLift_baseDerivative v _ b.property,
    fderiv_ambientLift_constMul a f _ b.property]
  rfl

/-- The actual vertical derivative is complex linear in the family. -/
theorem verticalDerivative_constMul (a : ℂ) (f : SmoothFamily U d) (v : d → ℝ)
    (b : U) (t : UnitAddTorus d) :
    (constMul a f).verticalDerivative v (b, t) = a * f.verticalDerivative v (b, t) := by
  obtain ⟨x, rfl⟩ := torusQuotient_surjective t
  rw [← ambientLift_apply ((constMul a f).verticalDerivative v) b x,
    ← ambientLift_apply (f.verticalDerivative v) b x,
    ambientLift_verticalDerivative (constMul a f) v _ b.property,
    ambientLift_verticalDerivative f v _ b.property,
    fderiv_ambientLift_constMul a f _ b.property]
  rfl

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeOperators
