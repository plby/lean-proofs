/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerSourceAssemblyIndependent
import ErdosProblems.Erdos240.BakerSourceHeightAbsorptionCore

/-!
# Uniform height absorption for the rational-prime Baker theorem

The source lower bound has exponent

`C₀ * Ω' * log Ω' * log Aₙ * log N`.

Here `C₀` is uniform in the varying prime, while `Ω'` contains only the
fixed old heights and `Aₙ` is the normalized last height.  This file proves
the exact uniformity step which replaces the last-height factor by
`H(old) * log p`.  The resulting constant depends on the fixed old prime
family, but not on `p`, the coefficient vector, or `N`.

No analytic or algebraic source certificate is assumed silently.  The
predicate `HasNormalizedSourceCertificates` is the precise remaining source
construction theorem with the unabsorbed exponent, and the theorem at the
end of the file converts it into the project-facing certificate interface.
-/

open scoped BigOperators

noncomputable section

namespace Erdos240.BakerSourceHeightAbsorption

open Erdos240
open Erdos240.RationalPrimeBaker
open Erdos240.BakerSourceAssemblyIndependent

universe u

/-- The source construction statement before absorbing the fixed old heights
and the last source height.  Its `C₀` is allowed to depend on the fixed old
family, but all later quantifiers are uniform. -/
def HasNormalizedSourceCertificates : Prop :=
  ∀ (ι : Type u) [Fintype ι] [Nonempty ι] (old : ι → ℕ),
    (oldPrime : ∀ i, (old i).Prime) →
    (oldInjective : Function.Injective old) →
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ ⦃p : ℕ⦄ (c : ι → ℤ) (d : ℤ) (N : ℕ)
        (hp : p.Prime) (hpFresh : ∀ i, old i ≠ p)
        (hN : Real.exp 2 ≤ (N : ℝ))
        (_hc : ∀ i, (c i).natAbs ≤ N) (_hd : d.natAbs ≤ N)
        (_hdne : d ≠ 0) (_hform : indexedRationalLogForm old p c d ≠ 0),
        let P := sourceParameters old oldPrime oldInjective p hp hpFresh N hN
        |indexedRationalLogForm old p c d| <
            Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
              Real.log P.newHeight * Real.log (N : ℝ))) →
          VDPLContradictionCertificate P

/-- A faithful concrete source chain supplies the normalized certificate
interface.  The chain is already contradictory by the checked terminal
zero-count theorem; from that contradiction one may construct the legacy
existential certificate without transporting its parameter-dependent state
across the `Fin` enumeration. -/
theorem normalizedSourceCertificates_of_concreteSourceChains
    (hsource : HasNormalizedConcreteSourceChains.{u}) :
    HasNormalizedSourceCertificates.{u} := by
  intro ι _ _ old oldPrime oldInjective
  obtain ⟨C₀, hC₀, hconstruct⟩ :=
    hsource ι old oldPrime oldInjective
  refine ⟨C₀, hC₀, ?_⟩
  intro p c d N hp hpFresh hN hc hd hdne hform
  dsimp only
  intro hsmall
  letI : Nonempty (Fin (Fintype.card ι)) := finCardNonempty ι
  obtain ⟨chain⟩ :=
    hconstruct c d N hp hpFresh hN hc hd hdne hform hsmall
  exact chain.false.elim

/-- The unabsorbed source-certificate theorem implies the certificate
interface with exponent `C(old) * log p * log N`.

The proof is the complete dependency audit: `C(old)` is the product of the
source constant, the fixed old-height factors, and the old-family height
constant. -/
theorem sourceCertificates_of_normalized
    (hsource : HasNormalizedSourceCertificates.{u}) :
    HasIntegralCutoffSourceCertificates.{u} := by
  intro ι _ _ old oldPrime oldInjective
  obtain ⟨C₀, hC₀, hconstruct⟩ :=
    hsource ι old oldPrime oldInjective
  let C : ℝ := C₀ * oldFamilySourceMultiplier old
  have hC : 0 < C := mul_pos hC₀ (oldFamilySourceMultiplier_pos old)
  refine ⟨C, hC, ?_⟩
  intro p c d N hp hpFresh hN hc hd hdne hform hsmall
  let P := sourceParameters old oldPrime oldInjective p hp hpFresh N hN
  have hlogN : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg ((show (1 : ℝ) ≤ Real.exp 2 by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by norm_num)).trans hN)
  have hPold : P.old = old := by rfl
  have hPnewPrime : P.newPrime = p := by rfl
  have hsourceLe :
      C₀ * P.OmegaOld * Real.log P.OmegaOld * Real.log P.newHeight *
          Real.log (N : ℝ) ≤
        C * Real.log (p : ℝ) * Real.log (N : ℝ) := by
    dsimp only [C]
    rw [← hPold, ← hPnewPrime]
    exact sourceExponent_le_absorbedExponent P hC₀.le hlogN
  have hexp :
      Real.exp (-C * Real.log (p : ℝ) * Real.log (N : ℝ)) ≤
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (N : ℝ))) := by
    apply Real.exp_le_exp.mpr
    linarith
  apply hconstruct c d N hp hpFresh hN hc hd hdne hform
  exact hsmall.trans_le hexp

/-- Complete project-facing uniform bound, conditional only on the exact
normalized source-certificate construction. -/
theorem uniformBounds_of_normalizedSourceCertificates
    (hsource : HasNormalizedSourceCertificates.{u}) :
    HasUniformRationalPrimeLogBounds.{u} :=
  uniformBounds_of_sourceCertificates
    (sourceCertificates_of_normalized hsource)

/-- End-to-end logical assembly from the audited concrete source-chain
target through the explicit height-absorption certificate bridge. -/
theorem uniformBounds_of_normalizedConcreteSourceChains_viaCertificates
    (hsource : HasNormalizedConcreteSourceChains.{u}) :
    HasUniformRationalPrimeLogBounds.{u} :=
  uniformBounds_of_normalizedSourceCertificates
    (normalizedSourceCertificates_of_concreteSourceChains hsource)

#print axioms normalizedSourceCertificates_of_concreteSourceChains
#print axioms sourceCertificates_of_normalized
#print axioms uniformBounds_of_normalizedSourceCertificates
#print axioms uniformBounds_of_normalizedConcreteSourceChains_viaCertificates

end Erdos240.BakerSourceHeightAbsorption
