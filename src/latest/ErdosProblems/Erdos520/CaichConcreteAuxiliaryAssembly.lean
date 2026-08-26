import ErdosProblems.Erdos520.CaichAuxiliaryAssembly
import ErdosProblems.Erdos520.CaichConcreteSmoothingReduction

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory
open scoped Topology

namespace Erdos
namespace Problem520

/-!
# Matching the five Caich auxiliaries to the concrete smoothing remainder

The initial smoothing reduction now has an explicit residual.  This file
identifies its `W/x` summand literally and isolates the one deterministic
domination still needed for the averaged main term.  Once that domination
and the five source estimates hold, the abstract auxiliary premise used by
the concentration theorem disappears.
-/

/-- The fifth Caich auxiliary is exactly the normalized short-interval error
from the unconditional first smoothing step. -/
noncomputable def caichConcreteWoverX
    (X : ℕ → ℕ → ℝ) (x a b : ℕ → ℕ → ℕ)
    (ell r : ℕ) (omega : Omega) : ℝ :=
  caichInitialSmoothingError (X ell r) omega
      (x ell r) (a ell r) (b ell r) /
    (x ell r : ℝ)

theorem caichConcreteWoverX_nonneg
    (X : ℕ → ℕ → ℝ) (x a b : ℕ → ℕ → ℕ)
    {ell r : ℕ} (hX : 0 < X ell r) (hx : 0 < x ell r)
    (omega : Omega) :
    0 ≤ caichConcreteWoverX X x a b ell r omega := by
  unfold caichConcreteWoverX
  exact div_nonneg
    (caichInitialSmoothingError_nonneg hX omega
      (x ell r) (a ell r) (b ell r))
    (by positivity)

/-- Exact deterministic obligation left by the main-term cleanup in Caich's
smoothing argument.  It contains no probabilistic assertion: pointwise, the
unaccounted averaged main term must be dominated by the two `lambda` terms
and the two boundary/long-ratio `L` terms.

The coefficient is the literal `ell * log ell` from equation (9). -/
def caichUnaccountedMainDominatedAtScale
    (tests : ℕ → Finset ℕ) (x a b : ℕ → ℕ → ℕ)
    (X : ℕ → ℕ → ℝ)
    (J : ℕ → ℕ) (U : ℕ → ℕ → Omega → ℝ)
    (lambda2 lambda3 L12 L2 : ℕ → ℕ → Omega → ℝ)
    (ell : ℕ) (omega : Omega) : Prop :=
  ∀ r ∈ tests ell,
    caichUnaccountedSmoothedMain (X ell r) J U ell omega
        (x ell r) (a ell r) (b ell r) ≤
      caichAuxiliaryLogFactor ell *
          (lambda2 ell r omega + lambda3 ell r omega) +
        L12 ell r omega + L2 ell r omega

/-- The deterministic domination turns the concrete smoothing residual into
the already assembled five-term auxiliary total. -/
theorem caichConcreteSmoothingRemainder_le_explicitAuxiliary
    (tests : ℕ → Finset ℕ) (x a b : ℕ → ℕ → ℕ)
    (X : ℕ → ℕ → ℝ)
    (J : ℕ → ℕ) (U : ℕ → ℕ → Omega → ℝ)
    (lambda2 lambda3 L12 L2 : ℕ → ℕ → Omega → ℝ)
    {ell r : ℕ} {omega : Omega}
    (hmain : caichUnaccountedMainDominatedAtScale
      tests x a b X J U lambda2 lambda3 L12 L2 ell omega)
    (hr : r ∈ tests ell) :
    caichConcreteSmoothingRemainder (X ell r) J U ell omega
        (x ell r) (a ell r) (b ell r) ≤
      caichExplicitAuxiliaryRemainder lambda2 lambda3 L12 L2
        (caichConcreteWoverX X x a b) ell r omega := by
  unfold caichConcreteSmoothingRemainder
    caichExplicitAuxiliaryRemainder caichAuxiliaryTotal
    caichConcreteWoverX
  exact add_le_add (hmain r hr) le_rfl

/-- Pointwise transfer from the five component estimates to the concrete
remainder consumed by the unconditional smoothing reduction. -/
theorem auxiliaryRemainderGoodAtScale_caichConcrete_of_components
    (tests : ℕ → Finset ℕ) (x a b : ℕ → ℕ → ℕ)
    (X : ℕ → ℕ → ℝ)
    (J : ℕ → ℕ) (U : ℕ → ℕ → Omega → ℝ)
    (lambda2 lambda3 L12 L2 : ℕ → ℕ → Omega → ℝ)
    {K ell : ℕ} {omega : Omega} (hell : 1 < ell)
    (hmain : caichUnaccountedMainDominatedAtScale
      tests x a b X J U lambda2 lambda3 L12 L2 ell omega)
    (hcomponents : caichAuxiliaryComponentsGoodAtScale tests
      lambda2 lambda3 L12 L2 (caichConcreteWoverX X x a b)
      K ell omega) :
    auxiliaryRemainderGoodAtScale tests
      (fun ell r omega =>
        caichConcreteSmoothingRemainder (X ell r) J U ell omega
          (x ell r) (a ell r) (b ell r))
      5 K ell omega := by
  have hexplicit := auxiliaryRemainderGoodAtScale_of_caichComponents
    tests lambda2 lambda3 L12 L2 (caichConcreteWoverX X x a b)
    hell hcomponents
  intro r hr
  exact (caichConcreteSmoothingRemainder_le_explicitAuxiliary
    tests x a b X J U lambda2 lambda3 L12 L2 hmain hr).trans
      (hexplicit r hr)

/-- Enlarging the numerical auxiliary constant preserves the good event. -/
theorem auxiliaryRemainderGoodAtScale_mono_constant
    (tests : ℕ → Finset ℕ) (E : ℕ → ℕ → Omega → ℝ)
    {B B' : ℝ} {K ell : ℕ} {omega : Omega}
    (hBB' : B ≤ B')
    (hgood : auxiliaryRemainderGoodAtScale tests E B K ell omega) :
    auxiliaryRemainderGoodAtScale tests E B' K ell omega := by
  intro r hr
  have hT : 0 ≤ (ell : ℝ) ^ 10 := pow_nonneg (Nat.cast_nonneg ell) 10
  have hQ : 0 ≤ (ell : ℝ) ^ ((K : ℝ) / 2) :=
    Real.rpow_nonneg (Nat.cast_nonneg ell) _
  have hnum : B * (ell : ℝ) ^ 10 ≤ B' * (ell : ℝ) ^ 10 :=
    mul_le_mul_of_nonneg_right hBB' hT
  exact (hgood r hr).trans (div_le_div_of_nonneg_right hnum hQ)

/-- Almost-sure assembly from the deterministic main cleanup and the five
separate summable failure estimates.  This is the exact bridge required by
the aligned Harper/concentration endpoint. -/
theorem ae_eventually_auxiliaryRemainderGood_caichConcrete
    (tests : ℕ → Finset ℕ) (x a b : ℕ → ℕ → ℕ)
    (X : ℕ → ℕ → ℝ)
    (J : ℕ → ℕ) (U : ℕ → ℕ → Omega → ℝ)
    (lambda2 lambda3 L12 L2 : ℕ → ℕ → Omega → ℝ)
    (K : ℕ)
    (hmain : ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      caichUnaccountedMainDominatedAtScale
        tests x a b X J U lambda2 lambda3 L12 L2 ell omega)
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
      (caichAuxiliaryComponentFailure tests
        (caichConcreteWoverX X x a b)
        (caichWAuxThreshold K) ell)) :
    ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in atTop,
      auxiliaryRemainderGoodAtScale tests
        (fun ell r omega =>
          caichConcreteSmoothingRemainder (X ell r) J U ell omega
            (x ell r) (a ell r) (b ell r))
        5 K ell omega := by
  have haux := ae_eventually_auxiliaryRemainderGood_of_caichComponents
    tests lambda2 lambda3 L12 L2 (caichConcreteWoverX X x a b) K
    hlambda2 hlambda3 hL12 hL2 hW
  filter_upwards [hmain, haux] with omega hmainOmega hauxOmega
  filter_upwards [hmainOmega, hauxOmega,
    eventually_ge_atTop (2 : ℕ)] with ell hmainEll hauxEll hell
  intro r hr
  exact (caichConcreteSmoothingRemainder_le_explicitAuxiliary
    tests x a b X J U lambda2 lambda3 L12 L2 hmainEll hr).trans
      (hauxEll r hr)

end Problem520
end Erdos
