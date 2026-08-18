import ErdosProblems.Erdos140.BohrEstimates
import ErdosProblems.Erdos140.Chang

/-!
# Basic definitions for the relative Chang--Sanders lemma

This small module contains the definitions shared by the analytic dimension
bound, the relative-dissociation selection, and the indicator bridge.  It is
kept separate so that the final assembled theorem can import all three
components without an import cycle.
-/

noncomputable section

open Finset Function Real
open scoped BigOperators ComplexConjugate NNReal

namespace Erdos140.RelativeChangSanders

variable {G : Type*} [Fintype G] [AddCommGroup G]

/-- Sanders' measure-relative replacement for ordinary dissociativity. -/
def IsWeightedDissociated (mu : G → ℝ) (K : ℝ)
    (Delta : Finset (AddChar G ℂ)) : Prop :=
  ∀ u : AddChar G ℂ → ℂ,
    (∀ psi ∈ Delta, ‖u psi‖ ≤ 1) →
      ∑ x : G, mu x *
        ∏ psi ∈ Delta, (1 + (u psi * psi x).re) ≤ exp K

/-- The unnormalized Fourier sum of a real weight. -/
def weightedSpectrumSum (f : G → ℝ) (psi : AddChar G ℂ) : ℂ :=
  ∑ x : G, (f x : ℂ) * psi x

/-- The spectrum of `f` relative to a probability measure `mu`. -/
def relativeLargeSpectrum (mu f : G → ℝ) (eta : ℝ) :
    Finset (AddChar G ℂ) :=
    Finset.univ.filter fun psi ↦
    eta * (∑ x : G, f x * mu x) ≤
      ‖∑ x : G, (f x * mu x : ℝ) * psi x‖

@[simp] theorem mem_relativeLargeSpectrum {mu f : G → ℝ} {eta : ℝ}
    {psi : AddChar G ℂ} :
    psi ∈ relativeLargeSpectrum mu f eta ↔
      eta * (∑ x : G, f x * mu x) ≤
        ‖∑ x : G, (f x * mu x : ℝ) * psi x‖ := by
  simp [relativeLargeSpectrum]

end Erdos140.RelativeChangSanders
