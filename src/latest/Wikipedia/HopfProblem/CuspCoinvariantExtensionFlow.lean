import Wikipedia.HopfProblem.CuspRetractionRadius
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionCusp

/-!
# The original vertical flow on closed cusp sublevels

The actual cusp flow preserves the original parameter, so it restricts
to every literal closed sublevel.  On the original toric covering it is
exactly the existing fibre action with multiplier `(1, exp (2πis))`.
For real time these are norm-one multipliers.  Thus invariance under the
compact fibre action implies invariance under the original delta circle;
no new action is substituted for it.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap Matrix

namespace Wikipedia.HopfProblem.CuspCoinvariantExtension

open ToricCharts ToricSpace CuspRetraction
open SpecialPeriods.Threefold.VerticalAction.Cusp

/-- The two fibre multipliers used literally in the native cusp flow. -/
def verticalFibreUnits (s : ℂ) : Fin 2 → ℂˣ :=
  ![1, Units.mk0 (Complex.exp (2 * Real.pi * Complex.I * s))
    (Complex.exp_ne_zero _)]

theorem verticalFibreUnits_real_norm (t : ℝ) (i : Fin 2) :
    ‖(verticalFibreUnits (t : ℂ) i : ℂ)‖ = 1 := by
  fin_cases i <;>
    simp [verticalFibreUnits, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

/-- Restriction of the original native flow, not an action on a model. -/
def closedFlow (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r η : ℝ) (s : ℂ) :
    C(ClosedQuotient C r η, ClosedQuotient C r η) where
  toFun x := ⟨flow C r s x.val, by
    rw [projection_flow]
    exact x.property⟩
  continuous_toFun :=
    ((flow_continuous C r s).comp continuous_subtype_val).subtype_mk _

@[simp] theorem closedFlow_coe (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r η : ℝ) (s : ℂ) (x : ClosedQuotient C r η) :
    (closedFlow C r η s x).val = flow C r s x.val := rfl

/-- The original quotient representatives retain exactly the native
fibre multipliers, with no sign or reparametrization. -/
theorem closedFlow_quotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {r η : ℝ} (hηr : η < r) (s : ℂ) (x : ClosedTube η) :
    closedFlow C r η s (closedQuotientMap C hηr x) =
      closedQuotientMap C hηr (closedFibreAction η (verticalFibreUnits s) x) := rfl

/-- An invariant core formula on the actual toric representatives is
invariant under every real parameter of the original cusp flow. -/
theorem invariant_closedFlow_real_of_fibreAction
    {Y : Type*} (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {r η : ℝ} (hηr : η < r) (f : ClosedQuotient C r η → Y)
    (hf : ∀ (u : Fin 2 → ℂˣ), (∀ i, ‖(u i : ℂ)‖ = 1) →
      ∀ x : ClosedTube η,
        f (closedQuotientMap C hηr (closedFibreAction η u x)) =
          f (closedQuotientMap C hηr x))
    (t : ℝ) (x : ClosedQuotient C r η) :
    f (closedFlow C r η (t : ℂ) x) = f x := by
  obtain ⟨y, rfl⟩ := closedQuotientMap_surjective C hηr x
  rw [closedFlow_quotientMap]
  exact hf (verticalFibreUnits (t : ℂ)) (verticalFibreUnits_real_norm t) y

end Wikipedia.HopfProblem.CuspCoinvariantExtension
