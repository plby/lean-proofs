/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos186.LowerBound
import ErdosProblems.Erdos186.PZ.Main

/-!
# Erdős Problem 186

Let `F N` be the largest cardinality of a subset of `{1, ..., N}` in which
no element is the arithmetic mean of two or more distinct other elements.
Bosznay proved the lower bound `N^(1/4) ≪ F(N)`, while Pham and Zakharov
proved `F(N) ≪_ε N^(1/4+ε)` for every `ε > 0`.

The finite extremal definition is in `Foundations`, Bosznay's construction
is in `LowerBound`, and `UpperPackaging` states the precise
Pham--Zakharov integer-box estimate and proves its one-dimensional
specialization.  The theorem below is the narrow assembly boundary: once
the box estimate is supplied, it yields exactly the published resolution.

References:

* A. P. Bosznay, *On the lower estimation of nonaveraging sets* (1989).
* H. T. Pham and D. Zakharov, *Sharp bound for the Erdős--Straus
  non-averaging set problem*, arXiv:2410.14624.
-/

namespace Erdos186

open Filter

/-- The exact asymptotic conclusion of Erdős Problem 186, assembled from
Bosznay's proved construction and a proof of the Pham--Zakharov box theorem.

This is deliberately a theorem with an ordinary proof parameter, not a
postulate.  The unconditional main theorem is added only after `PZBoxBound`
has itself been proved. -/
theorem erdos_186_of_pzBoxBound (hPZ : PZBoxBound) :
    (fun N : ℕ ↦ (N : ℝ) ^ (1 / 4 : ℝ)) =O[atTop]
        (fun N : ℕ ↦ (F N : ℝ)) ∧
      ∀ ε : ℝ, 0 < ε →
        (fun N : ℕ ↦ (F N : ℝ)) =O[atTop]
          (fun N : ℕ ↦ (N : ℝ) ^ ((1 / 4 : ℝ) + ε)) := by
  exact ⟨bosznay_lower_bound, upper_isBigO_of_pzBoxBound hPZ⟩

/-- The same exact resolution assembled directly from the remaining
source-level Pham--Zakharov components and their one-step constructor.  The
source-specialized post-CFP intersection is internal to the assembly. -/
theorem erdos_186_of_pz_components
    (assemble : PZ.OneStepAssemblyStatement)
    (hCFP : CFP.NonemptyHigherDimensionalCorollary5)
    (hReplacement : PZ.Reduction.IrreducibleReplacementStatement)
    (hConvexDensity : PZ.ConvexDensity.PZLemmaOneStatement) :
    (fun N : ℕ ↦ (N : ℝ) ^ (1 / 4 : ℝ)) =O[atTop]
        (fun N : ℕ ↦ (F N : ℝ)) ∧
      ∀ ε : ℝ, 0 < ε →
        (fun N : ℕ ↦ (F N : ℝ)) =O[atTop]
          (fun N : ℕ ↦ (N : ℝ) ^ ((1 / 4 : ℝ) + ε)) := by
  exact erdos_186_of_pzBoxBound
    (PZ.pzBoxBound_of_components assemble hCFP hReplacement hConvexDensity)

/-- The guarded quantitative replacement construction is now unconditional,
so the remaining assembly boundary no longer exposes it as a parameter. -/
theorem erdos_186_of_cfp_convexDensity
    (assemble : PZ.OneStepAssemblyStatement)
    (hCFP : CFP.NonemptyHigherDimensionalCorollary5)
    (hConvexDensity : PZ.ConvexDensity.PZLemmaOneStatement) :
    (fun N : ℕ ↦ (N : ℝ) ^ (1 / 4 : ℝ)) =O[atTop]
        (fun N : ℕ ↦ (F N : ℝ)) ∧
      ∀ ε : ℝ, 0 < ε →
        (fun N : ℕ ↦ (F N : ℝ)) =O[atTop]
          (fun N : ℕ ↦ (N : ℝ) ^ ((1 / 4 : ℝ) + ε)) := by
  exact erdos_186_of_pzBoxBound
    (PZ.pzBoxBound_of_cfp_convexDensity assemble hCFP hConvexDensity)

/-- With replacement and convex density discharged by their proved
implementations, only the CFP source corollary remains outside the one-step
assembly. -/
theorem erdos_186_of_cfp
    (assemble : PZ.OneStepAssemblyStatement)
    (hCFP : CFP.NonemptyHigherDimensionalCorollary5) :
    (fun N : ℕ ↦ (N : ℝ) ^ (1 / 4 : ℝ)) =O[atTop]
        (fun N : ℕ ↦ (F N : ℝ)) ∧
      ∀ ε : ℝ, 0 < ε →
        (fun N : ℕ ↦ (F N : ℝ)) =O[atTop]
          (fun N : ℕ ↦ (N : ℝ) ^ ((1 / 4 : ℝ) + ε)) := by
  exact erdos_186_of_pzBoxBound (PZ.pzBoxBound_of_cfp assemble hCFP)

/-- The complete Erdős conclusion from the source-correct nonempty CFP
corollary.  All Pham--Zakharov reduction, intersection, convex-density,
discrete-John, one-step, and finite-iteration components are discharged by
proved implementations. -/
theorem erdos_186_of_nonemptyHigherDimensionalCorollary5
    (hCFP : CFP.NonemptyHigherDimensionalCorollary5) :
    (fun N : ℕ ↦ (N : ℝ) ^ (1 / 4 : ℝ)) =O[atTop]
        (fun N : ℕ ↦ (F N : ℝ)) ∧
      ∀ ε : ℝ, 0 < ε →
        (fun N : ℕ ↦ (F N : ℝ)) =O[atTop]
          (fun N : ℕ ↦ (N : ℝ) ^ ((1 / 4 : ℝ) + ε)) := by
  exact erdos_186_of_pzBoxBound
    (PZ.pzBoxBound_of_nonemptyHigherDimensionalCorollary5 hCFP)

/-- The exact resolution after the analytic Bilu--Freiman and geometric
Pham--Zakharov components have been discharged, conditional only on the
centered large-input CFP coverage constructor. -/
theorem erdos_186_of_centeredCoverage
    (hcoverage : CFP.UniformCenteredLargeInputLogLossCoverage) :
    (fun N : ℕ ↦ (N : ℝ) ^ (1 / 4 : ℝ)) =O[atTop]
        (fun N : ℕ ↦ (F N : ℝ)) ∧
      ∀ ε : ℝ, 0 < ε →
        (fun N : ℕ ↦ (F N : ℝ)) =O[atTop]
          (fun N : ℕ ↦ (N : ℝ) ^ ((1 / 4 : ℝ) + ε)) := by
  exact erdos_186_of_pzBoxBound
    (PZ.pzBoxBound_of_centeredCoverage hcoverage)

/-- Erdős Problem 186: the extremal size of a non-averaging subset of
`{1, …, N}` has exponent exactly `1/4`. -/
theorem erdos_186 :
    (fun N : ℕ ↦ (N : ℝ) ^ (1 / 4 : ℝ)) =O[atTop]
        (fun N : ℕ ↦ (F N : ℝ)) ∧
      ∀ ε : ℝ, 0 < ε →
        (fun N : ℕ ↦ (F N : ℝ)) =O[atTop]
          (fun N : ℕ ↦ (N : ℝ) ^ ((1 / 4 : ℝ) + ε)) := by
  exact erdos_186_of_pzBoxBound PZ.pzBoxBound

end Erdos186

#print axioms Erdos186.erdos_186_of_pzBoxBound
#print axioms Erdos186.erdos_186_of_pz_components
#print axioms Erdos186.erdos_186_of_cfp_convexDensity
#print axioms Erdos186.erdos_186_of_cfp
#print axioms Erdos186.erdos_186_of_nonemptyHigherDimensionalCorollary5
#print axioms Erdos186.erdos_186_of_centeredCoverage
#print axioms Erdos186.erdos_186
