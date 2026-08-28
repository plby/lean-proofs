import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionCusp
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixedToricScaling

/-!
# The literal multiplicative action on the original cusp quotient

Vertical fibre multiplication preserves every actual cusp tube and commutes
with its genuine twisted lattice action. We descend that same multiplication
to the existing orbit quotient. The normalized-exponential formula identifies
it with the already constructed additive cusp flow.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.FiniteActionFixed.Cusp

open ToricCharts ToricSpace

/-- The existing second-fibre cocharacter, as a multiplicative homomorphism. -/
def verticalMultiplier : ℂˣ →* ActingTorus where
  toFun u := fibreMultiplier ![1, u]
  map_one' := by
    ext i
    fin_cases i <;> simp [fibreMultiplier]
  map_mul' u v := by
    ext i
    fin_cases i <;> simp [fibreMultiplier]

@[simp] theorem verticalMultiplier_apply (u : ℂˣ) :
    verticalMultiplier u = fibreMultiplier ![1, u] := rfl

/-- Restriction of literal vertical torus multiplication to the original tube. -/
def tubeMap (D : TopologicalSpace.Opens ℂ) (u : ℂˣ) (x : Tube D) : Tube D :=
  ⟨torusAction (verticalMultiplier u) x, by
    change time (torusAction (fibreMultiplier ![1, u]) x) ∈ D
    rw [time_fibreMultiplier]
    exact x.property⟩

@[simp] theorem tubeMap_coe (D : TopologicalSpace.Opens ℂ) (u : ℂˣ) (x : Tube D) :
    (tubeMap D u x : ToricSpace.Space) = torusAction (fibreMultiplier ![1, u]) x := rfl

@[simp] theorem tubeMap_one (D : TopologicalSpace.Opens ℂ) (x : Tube D) :
    tubeMap D 1 x = x := by
  apply Subtype.ext
  change torusAction (verticalMultiplier 1) (x : ToricSpace.Space) = (x : ToricSpace.Space)
  rw [map_one, torusAction_one]

theorem tubeMap_mul (D : TopologicalSpace.Opens ℂ) (u v : ℂˣ) (x : Tube D) :
    tubeMap D (u * v) x = tubeMap D u (tubeMap D v x) := by
  apply Subtype.ext
  change torusAction (verticalMultiplier (u * v)) (x : ToricSpace.Space) =
    torusAction (verticalMultiplier u) (torusAction (verticalMultiplier v) (x : ToricSpace.Space))
  rw [map_mul, torusAction_mul]

theorem tubeMap_iterate (D : TopologicalSpace.Opens ℂ) (u : ℂˣ) (n : ℕ) (x : Tube D) :
    (tubeMap D u)^[n] x = tubeMap D (u ^ n) x := by
  induction n with
  | zero => simp
  | succ n hn =>
      rw [Function.iterate_succ_apply', hn, ← tubeMap_mul, pow_succ']

/-- Commutation is with the genuine correction-dependent lattice translation. -/
theorem tubeMap_translate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (D : TopologicalSpace.Opens ℂ) (u : ℂˣ) (v : Fin 2 → ℤ) (x : Tube D) :
    tubeMap D u (tubeTranslate C D v x) = tubeTranslate C D v (tubeMap D u x) :=
  Subtype.ext (VerticalAction.Cusp.fibreMultiplier_twistedTranslate_commute ![1, u] C v x)

/-- The tube map is the old tube flow for exactly the normalized exponential. -/
theorem tubeMap_exponential (D : TopologicalSpace.Opens ℂ) (s : ℂ) (x : Tube D) :
    tubeMap D (VerticalAction.Exponential.normalizedExponential s) x =
      VerticalAction.Cusp.tubeFlow D s x := rfl

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)

/-- Literal descent of vertical multiplication to the original twisted orbit quotient. -/
def quotientAction (u : ℂˣ) :
    CuspQuotient.QuotientSpace C ε → CuspQuotient.QuotientSpace C ε :=
  Quotient.lift
    (fun x => CuspQuotient.quotientMap C ε (tubeMap (CuspQuotient.disc ε) u x)) (by
      let := ToricSpace.tubeAction C (CuspQuotient.disc ε)
      intro x y hxy
      change x ∈ MulAction.orbit CuspQuotient.LatticeGroup y at hxy
      obtain ⟨g, rfl⟩ := hxy
      change CuspQuotient.quotientMap C ε
        (tubeMap (CuspQuotient.disc ε) u
          (tubeTranslate C (CuspQuotient.disc ε) g.toAdd y)) = _
      rw [tubeMap_translate, CuspQuotient.quotientMap_translate])

@[simp] theorem quotientAction_quotientMap (u : ℂˣ)
    (x : Tube (CuspQuotient.disc ε)) :
    quotientAction C ε u (CuspQuotient.quotientMap C ε x) =
      CuspQuotient.quotientMap C ε (tubeMap (CuspQuotient.disc ε) u x) := rfl

@[simp] theorem quotientAction_one (x : CuspQuotient.QuotientSpace C ε) :
    quotientAction C ε 1 x = x := by
  induction x using Quotient.inductionOn with
  | h x => exact congrArg (CuspQuotient.quotientMap C ε) (tubeMap_one _ x)

theorem quotientAction_mul (u v : ℂˣ) (x : CuspQuotient.QuotientSpace C ε) :
    quotientAction C ε (u * v) x = quotientAction C ε u (quotientAction C ε v x) := by
  induction x using Quotient.inductionOn with
  | h x => exact congrArg (CuspQuotient.quotientMap C ε) (tubeMap_mul _ u v x)

/-- This is the existing quotient flow, not an alternative action on the cusp. -/
theorem quotientAction_exponential (s : ℂ) (x : CuspQuotient.QuotientSpace C ε) :
    quotientAction C ε (VerticalAction.Exponential.normalizedExponential s) x =
      VerticalAction.Cusp.flow C ε s x := by
  induction x using Quotient.inductionOn with
  | h x => exact congrArg (CuspQuotient.quotientMap C ε) (tubeMap_exponential _ s x)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.FiniteActionFixed.Cusp
