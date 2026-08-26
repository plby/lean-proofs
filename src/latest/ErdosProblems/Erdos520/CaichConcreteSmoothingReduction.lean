import ErdosProblems.Erdos520.CaichInitialSmoothing
import ErdosProblems.Erdos520.QuadraticVariationReduction

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory

namespace Erdos
namespace Problem520

/-!
# A concrete, unconditional smoothing reduction

`QuadraticVariationReduction` deliberately accepts Caich's smoothing
inequality through the abstract predicate `qvSmoothingGoodAtScale`.  This
file removes that abstract premise.  The remainder below is a concrete
function of the actual averaged main term and the actual short-interval
error from `CaichInitialSmoothing`.

The definition subtracts the desired block-energy main term and retains its
positive part.  Consequently the reduction is an identity-level fact: no
prime-number estimate, probability estimate, or paper lemma is used here.
All remaining analytic work is now concentrated in proving that this one
explicit remainder is eventually small.
-/

/-- The part of the averaged main term not yet accounted for by the desired
`ell * log ell * max U_j` contribution. -/
noncomputable def caichUnaccountedSmoothedMain
    (X : ℝ) (J : ℕ → ℕ) (U : ℕ → ℕ → Omega → ℝ)
    (ell : ℕ) (omega : Omega) (x a b : ℕ) : ℝ :=
  max 0
    (caichInitialSmoothedMain X omega x a b / (x : ℝ) -
      (ell : ℝ) * Real.log (ell : ℝ) *
        caichBlockEnergyMax J U ell omega)

/-- The exact residual in the initial smoothing step: the unaccounted main
piece plus the normalized short-interval smoothing error `W/x`. -/
noncomputable def caichConcreteSmoothingRemainder
    (X : ℝ) (J : ℕ → ℕ) (U : ℕ → ℕ → Omega → ℝ)
    (ell : ℕ) (omega : Omega) (x a b : ℕ) : ℝ :=
  caichUnaccountedSmoothedMain X J U ell omega x a b +
    caichInitialSmoothingError X omega x a b / (x : ℝ)

theorem caichUnaccountedSmoothedMain_nonneg
    (X : ℝ) (J : ℕ → ℕ) (U : ℕ → ℕ → Omega → ℝ)
    (ell : ℕ) (omega : Omega) (x a b : ℕ) :
    0 ≤ caichUnaccountedSmoothedMain X J U ell omega x a b := by
  unfold caichUnaccountedSmoothedMain
  exact le_max_left _ _

theorem caichConcreteSmoothingRemainder_nonneg
    {X : ℝ} (hX : 0 < X)
    (J : ℕ → ℕ) (U : ℕ → ℕ → Omega → ℝ)
    (ell : ℕ) (omega : Omega) {x : ℕ} (hx : 0 < x) (a b : ℕ) :
    0 ≤ caichConcreteSmoothingRemainder X J U ell omega x a b := by
  unfold caichConcreteSmoothingRemainder
  exact add_nonneg
    (caichUnaccountedSmoothedMain_nonneg X J U ell omega x a b)
    (div_nonneg (caichInitialSmoothingError_nonneg hX omega x a b)
      (by positivity))

theorem caichInitialSmoothedMain_div_le_accounted_add_unaccounted
    (X : ℝ) (J : ℕ → ℕ) (U : ℕ → ℕ → Omega → ℝ)
    (ell : ℕ) (omega : Omega) (x a b : ℕ) :
    caichInitialSmoothedMain X omega x a b / (x : ℝ) ≤
      (ell : ℝ) * Real.log (ell : ℝ) *
          caichBlockEnergyMax J U ell omega +
        caichUnaccountedSmoothedMain X J U ell omega x a b := by
  unfold caichUnaccountedSmoothedMain
  have hmax :
      caichInitialSmoothedMain X omega x a b / (x : ℝ) -
          (ell : ℝ) * Real.log (ell : ℝ) *
            caichBlockEnergyMax J U ell omega ≤
        max 0
          (caichInitialSmoothedMain X omega x a b / (x : ℝ) -
            (ell : ℝ) * Real.log (ell : ℝ) *
              caichBlockEnergyMax J U ell omega) :=
    le_max_right _ _
  linarith

/-- Pointwise concrete form of Caich's equation-(9) reduction.  The factor
`2` is exactly the factor in `V <= 2 L + 2 W`.

Unlike the paper-facing equation, this theorem has no hidden `O(1)` and no
analytic hypothesis: the not-yet-estimated part is the explicitly defined
`caichConcreteSmoothingRemainder`. -/
theorem largestPrimeQuadraticVariation_div_le_concreteSmoothing
    {X : ℝ} (hX : 0 < X)
    (J : ℕ → ℕ) (U : ℕ → ℕ → Omega → ℝ)
    (ell : ℕ) (omega : Omega) {x a b : ℕ} (hx : 0 < x) :
    largestPrimeQuadraticVariation omega x a b / (x : ℝ) ≤
      2 * ((ell : ℝ) * Real.log (ell : ℝ) *
          caichBlockEnergyMax J U ell omega +
        caichConcreteSmoothingRemainder X J U ell omega x a b) := by
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  have hinitial :=
    largestPrimeQuadraticVariation_le_initialSmoothing
      hX omega x a b
  have hdiv :
      largestPrimeQuadraticVariation omega x a b / (x : ℝ) ≤
        (2 * caichInitialSmoothedMain X omega x a b +
          2 * caichInitialSmoothingError X omega x a b) / (x : ℝ) :=
    div_le_div_of_nonneg_right hinitial hxR.le
  have hmain :=
    caichInitialSmoothedMain_div_le_accounted_add_unaccounted
      X J U ell omega x a b
  unfold caichConcreteSmoothingRemainder
  calc
    largestPrimeQuadraticVariation omega x a b / (x : ℝ) ≤
        (2 * caichInitialSmoothedMain X omega x a b +
          2 * caichInitialSmoothingError X omega x a b) / (x : ℝ) := hdiv
    _ = 2 * (caichInitialSmoothedMain X omega x a b / (x : ℝ)) +
        2 * (caichInitialSmoothingError X omega x a b / (x : ℝ)) := by
      field_simp
    _ ≤ 2 *
        ((ell : ℝ) * Real.log (ell : ℝ) *
            caichBlockEnergyMax J U ell omega +
          caichUnaccountedSmoothedMain X J U ell omega x a b) +
        2 * (caichInitialSmoothingError X omega x a b / (x : ℝ)) := by
      gcongr
    _ = 2 * ((ell : ℝ) * Real.log (ell : ℝ) *
          caichBlockEnergyMax J U ell omega +
        (caichUnaccountedSmoothedMain X J U ell omega x a b +
          caichInitialSmoothingError X omega x a b / (x : ℝ))) := by
      ring

/-- Scale-wise version in exactly the shape consumed by
`QuadraticVariationReduction`. -/
theorem qvSmoothingGoodAtScale_caichConcrete
    (tests : ℕ → Finset ℕ) (x a b : ℕ → ℕ → ℕ)
    (X : ℕ → ℕ → ℝ)
    (J : ℕ → ℕ) (U : ℕ → ℕ → Omega → ℝ)
    {ell : ℕ} {omega : Omega}
    (hX : ∀ r ∈ tests ell, 0 < X ell r)
    (hx : ∀ r ∈ tests ell, 0 < x ell r) :
    qvSmoothingGoodAtScale tests x a b J U
      (fun ell r omega =>
        caichConcreteSmoothingRemainder (X ell r) J U ell omega
          (x ell r) (a ell r) (b ell r))
      2 ell omega := by
  intro r hr
  exact largestPrimeQuadraticVariation_div_le_concreteSmoothing
    (hX r hr) J U ell omega (hx r hr)

/-- The concrete smoothing predicate holds at every scale whenever the
smoothing parameters and test points are positive. -/
theorem ae_eventually_qvSmoothingGood_caichConcrete
    (tests : ℕ → Finset ℕ) (x a b : ℕ → ℕ → ℕ)
    (X : ℕ → ℕ → ℝ)
    (J : ℕ → ℕ) (U : ℕ → ℕ → Omega → ℝ)
    (hX : ∀ ell r, r ∈ tests ell → 0 < X ell r)
    (hx : ∀ ell r, r ∈ tests ell → 0 < x ell r) :
    ∀ᵐ omega ∂μ, ∀ᶠ ell : ℕ in Filter.atTop,
      qvSmoothingGoodAtScale tests x a b J U
        (fun ell r omega =>
          caichConcreteSmoothingRemainder (X ell r) J U ell omega
            (x ell r) (a ell r) (b ell r))
        2 ell omega := by
  filter_upwards with omega
  exact Filter.Eventually.of_forall fun ell =>
    qvSmoothingGoodAtScale_caichConcrete tests x a b X J U
      (fun r hr => hX ell r hr) (fun r hr => hx ell r hr)

end Problem520
end Erdos
