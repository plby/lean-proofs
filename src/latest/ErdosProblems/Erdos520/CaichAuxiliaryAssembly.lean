import ErdosProblems.Erdos520.QuadraticVariationReduction

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory Set
open scoped ENNReal Topology

namespace Erdos
namespace Problem520

/-!
# Assembly of Caich's auxiliary quadratic-variation terms

Caich's smoothing inequality contains one main block-energy term and five
auxiliary terms: `lambda^(2)`, `lambda^(3)`, `L^(12)`, `L^(2)`, and `W/x`.
`QuadraticVariationReduction` packages the latter five into one function `E`.
This file removes that packaging hypothesis.

The thresholds below are exactly those displayed in Caich v2 at lines
655--665 of `main.tex`.  The elementary estimate proved here is the
deterministic assembly used between inequality `inequality9901` (lines
647--650) and the failure union at lines 1047--1055.

The main block-energy term is intentionally absent.  In particular, none of
the results below uses, repairs, or conceals the reciprocal-sign inconsistency
between lines 1034--1038, 1042, and 1061--1065 of that source.
-/

/-! ## Scalar thresholds and assembly -/

/-- The common factor `ell * log ell` multiplying `lambda^(2)` and
`lambda^(3)` in Caich's smoothing inequality. -/
noncomputable def caichAuxiliaryLogFactor (ell : ℕ) : ℝ :=
  (ell : ℝ) * Real.log (ell : ℝ)

/-- The reciprocal scale `ell^(K/2)` appearing in all five auxiliary
thresholds. -/
noncomputable def caichAuxiliaryPower (K ell : ℕ) : ℝ :=
  (ell : ℝ) ^ ((K : ℝ) / 2)

/-- Threshold for each of `lambda^(2)` and `lambda^(3)`, corresponding to
lines 654--656 of Caich v2. -/
noncomputable def caichLambdaAuxThreshold (K ell : ℕ) : ℝ :=
  (ell : ℝ) ^ 10 /
    (caichAuxiliaryPower K ell * caichAuxiliaryLogFactor ell)

/-- Threshold for each of `L^(12)` and `L^(2)`, corresponding to lines
660--662 of Caich v2. -/
noncomputable def caichLargeAuxThreshold (K ell : ℕ) : ℝ :=
  (ell : ℝ) ^ 10 / caichAuxiliaryPower K ell

/-- Threshold for `W/x`, corresponding to lines 663--665 of Caich v2. -/
noncomputable def caichWAuxThreshold (K ell : ℕ) : ℝ :=
  1 / caichAuxiliaryPower K ell

/-- The five auxiliary terms in the exact combination in which they occur in
Caich's smoothing inequality. -/
noncomputable def caichAuxiliaryTotal (ell : ℕ)
    (lambda2 lambda3 L12 L2 WoverX : ℝ) : ℝ :=
  caichAuxiliaryLogFactor ell * (lambda2 + lambda3) +
    L12 + L2 + WoverX

/-- The five published auxiliary thresholds imply a reciprocal-scale bound
for their total.  The constant is exactly the count of the five contributions:
two lambda terms, two `L` terms, and one `W/x` term.

This is purely scalar; all analytic content remains in proving the five
displayed hypotheses. -/
theorem caichAuxiliaryTotal_le_five
    {ell K : ℕ} {lambda2 lambda3 L12 L2 WoverX : ℝ}
    (hell : 1 < ell)
    (hlambda2 : lambda2 ≤ caichLambdaAuxThreshold K ell)
    (hlambda3 : lambda3 ≤ caichLambdaAuxThreshold K ell)
    (hL12 : L12 ≤ caichLargeAuxThreshold K ell)
    (hL2 : L2 ≤ caichLargeAuxThreshold K ell)
    (hW : WoverX ≤ caichWAuxThreshold K ell) :
    caichAuxiliaryTotal ell lambda2 lambda3 L12 L2 WoverX ≤
      5 * (ell : ℝ) ^ 10 / caichAuxiliaryPower K ell := by
  let A : ℝ := caichAuxiliaryLogFactor ell
  let Q : ℝ := caichAuxiliaryPower K ell
  let T : ℝ := (ell : ℝ) ^ 10
  have hellR : 0 < (ell : ℝ) := by positivity
  have hlog : 0 < Real.log (ell : ℝ) :=
    Real.log_pos (by exact_mod_cast hell)
  have hA : 0 < A := by
    dsimp [A, caichAuxiliaryLogFactor]
    positivity
  have hQ : 0 < Q := by
    dsimp [Q, caichAuxiliaryPower]
    exact Real.rpow_pos_of_pos hellR _
  have hT : 1 ≤ T := by
    dsimp [T]
    exact one_le_pow₀ (by exact_mod_cast (show 1 ≤ ell by omega))
  have hlambda2' : A * lambda2 ≤ T / Q := by
    calc
      A * lambda2 ≤ A * (T / (Q * A)) :=
        mul_le_mul_of_nonneg_left (by
          simpa only [caichLambdaAuxThreshold, A, Q, T] using! hlambda2) hA.le
      _ = T / Q := by field_simp
  have hlambda3' : A * lambda3 ≤ T / Q := by
    calc
      A * lambda3 ≤ A * (T / (Q * A)) :=
        mul_le_mul_of_nonneg_left (by
          simpa only [caichLambdaAuxThreshold, A, Q, T] using! hlambda3) hA.le
      _ = T / Q := by field_simp
  have hL12' : L12 ≤ T / Q := by
    simpa only [caichLargeAuxThreshold, Q, T] using! hL12
  have hL2' : L2 ≤ T / Q := by
    simpa only [caichLargeAuxThreshold, Q, T] using! hL2
  have hW' : WoverX ≤ T / Q := by
    calc
      WoverX ≤ 1 / Q := by
        simpa only [caichWAuxThreshold, Q] using! hW
      _ ≤ T / Q := (div_le_div_iff_of_pos_right hQ).2 hT
  change A * (lambda2 + lambda3) + L12 + L2 + WoverX ≤ 5 * T / Q
  calc
    A * (lambda2 + lambda3) + L12 + L2 + WoverX =
        A * lambda2 + A * lambda3 + L12 + L2 + WoverX := by ring
    _ ≤ T / Q + T / Q + T / Q + T / Q + T / Q := by
      gcongr
    _ = 5 * T / Q := by ring

/-! ## Explicit functions at all test points -/

/-- The concrete auxiliary remainder function obtained from the five source
terms.  The arguments may later be instantiated by their arithmetic
definitions without changing any downstream reduction theorem. -/
noncomputable def caichExplicitAuxiliaryRemainder
    (lambda2 lambda3 L12 L2 WoverX : ℕ → ℕ → Omega → ℝ)
    (ell r : ℕ) (omega : Omega) : ℝ :=
  caichAuxiliaryTotal ell
    (lambda2 ell r omega) (lambda3 ell r omega)
    (L12 ell r omega) (L2 ell r omega) (WoverX ell r omega)

/-- A generic component is good at a scale if its threshold holds at every
selected test point. -/
def caichAuxiliaryComponentGoodAtScale
    (tests : ℕ → Finset ℕ) (value : ℕ → ℕ → Omega → ℝ)
    (threshold : ℕ → ℝ) (ell : ℕ) (omega : Omega) : Prop :=
  ∀ r ∈ tests ell, value ell r omega ≤ threshold ell

/-- Failure of one explicit auxiliary estimate at one scale. -/
def caichAuxiliaryComponentFailure
    (tests : ℕ → Finset ℕ) (value : ℕ → ℕ → Omega → ℝ)
    (threshold : ℕ → ℝ) (ell : ℕ) : Set Omega :=
  {omega | ¬ caichAuxiliaryComponentGoodAtScale
    tests value threshold ell omega}

/-- Simultaneous good event for the five published auxiliary estimates. -/
def caichAuxiliaryComponentsGoodAtScale
    (tests : ℕ → Finset ℕ)
    (lambda2 lambda3 L12 L2 WoverX : ℕ → ℕ → Omega → ℝ)
    (K ell : ℕ) (omega : Omega) : Prop :=
  caichAuxiliaryComponentGoodAtScale tests lambda2
      (caichLambdaAuxThreshold K) ell omega ∧
    caichAuxiliaryComponentGoodAtScale tests lambda3
      (caichLambdaAuxThreshold K) ell omega ∧
    caichAuxiliaryComponentGoodAtScale tests L12
      (caichLargeAuxThreshold K) ell omega ∧
    caichAuxiliaryComponentGoodAtScale tests L2
      (caichLargeAuxThreshold K) ell omega ∧
    caichAuxiliaryComponentGoodAtScale tests WoverX
      (caichWAuxThreshold K) ell omega

/-- The explicit five component bounds instantiate the formerly opaque
`auxiliaryRemainderGoodAtScale` hypothesis, with absolute constant `5`. -/
theorem auxiliaryRemainderGoodAtScale_of_caichComponents
    (tests : ℕ → Finset ℕ)
    (lambda2 lambda3 L12 L2 WoverX : ℕ → ℕ → Omega → ℝ)
    {K ell : ℕ} {omega : Omega} (hell : 1 < ell)
    (hgood : caichAuxiliaryComponentsGoodAtScale tests
      lambda2 lambda3 L12 L2 WoverX K ell omega) :
    auxiliaryRemainderGoodAtScale tests
      (caichExplicitAuxiliaryRemainder lambda2 lambda3 L12 L2 WoverX)
      5 K ell omega := by
  intro r hr
  exact caichAuxiliaryTotal_le_five hell
    (hgood.1 r hr) (hgood.2.1 r hr) (hgood.2.2.1 r hr)
    (hgood.2.2.2.1 r hr) (hgood.2.2.2.2 r hr)

/-! ## Borel--Cantelli wrapper for the five separate source estimates -/

/-- Summability of the five separate component failures gives the exact
almost-sure eventual auxiliary remainder bound needed by
`QuadraticVariationReduction`.

This theorem performs no analytic estimation: its five summability hypotheses
are precisely the remaining inputs corresponding respectively to Caich v2
Sections `Lambda_2_3`, `L3`, the following `L^(2)` subsection, and `prop2`.
-/
theorem ae_eventually_auxiliaryRemainderGood_of_caichComponents
    (tests : ℕ → Finset ℕ)
    (lambda2 lambda3 L12 L2 WoverX : ℕ → ℕ → Omega → ℝ)
    (K : ℕ)
    (hlambda2 : Summable fun ell ↦ μ.real
      (caichAuxiliaryComponentFailure tests lambda2
        (caichLambdaAuxThreshold K) ell))
    (hlambda3 : Summable fun ell ↦ μ.real
      (caichAuxiliaryComponentFailure tests lambda3
        (caichLambdaAuxThreshold K) ell))
    (hL12 : Summable fun ell ↦ μ.real
      (caichAuxiliaryComponentFailure tests L12
        (caichLargeAuxThreshold K) ell))
    (hL2 : Summable fun ell ↦ μ.real
      (caichAuxiliaryComponentFailure tests L2
        (caichLargeAuxThreshold K) ell))
    (hW : Summable fun ell ↦ μ.real
      (caichAuxiliaryComponentFailure tests WoverX
        (caichWAuxThreshold K) ell)) :
    ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      auxiliaryRemainderGoodAtScale tests
        (caichExplicitAuxiliaryRemainder lambda2 lambda3 L12 L2 WoverX)
        5 K ell omega := by
  have ha2 := ae_eventually_notMem_of_summable_measureReal hlambda2
  have ha3 := ae_eventually_notMem_of_summable_measureReal hlambda3
  have ha12 := ae_eventually_notMem_of_summable_measureReal hL12
  have haL2 := ae_eventually_notMem_of_summable_measureReal hL2
  have haW := ae_eventually_notMem_of_summable_measureReal hW
  filter_upwards [ha2, ha3, ha12, haL2, haW] with omega h2 h3 h12 hL hW'
  filter_upwards [h2, h3, h12, hL, hW',
    eventually_ge_atTop (2 : ℕ)] with ell h2' h3' h12' hL' hW'' hell
  apply auxiliaryRemainderGoodAtScale_of_caichComponents
    tests lambda2 lambda3 L12 L2 WoverX (by omega)
  exact ⟨not_not.mp h2', not_not.mp h3', not_not.mp h12',
    not_not.mp hL', not_not.mp hW''⟩

end Problem520
end Erdos
