/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerSourceAssemblyIndependent
import ErdosProblems.Erdos240.BakerSpecialization

/-!
# Final bridge from the normalized source construction to Erdős 240

This main-dependent module is intentionally separate from the analytic
source development.  It composes the source-independent uniform
rational-prime logarithm estimate with the checked finite-stage counting and
limiting argument in `ErdosProblems.Erdos240`.
-/

noncomputable section

namespace Erdos240.BakerProblem240Bridge

open Erdos240
open Erdos240.BakerSourceAssemblyIndependent

/-- The normalized concrete source components imply the complete
source-independent uniform rational-prime logarithm estimate.  This theorem
is kept in the project-facing module only to make the final dependency chain
explicit; the result itself remains the main-independent proposition from
`RationalPrimeBaker`. -/
theorem uniformRationalPrimeLogBounds_of_normalizedConcreteSourceComponents
    (hsource : HasNormalizedConcreteSourceComponents.{0}) :
    RationalPrimeBaker.HasUniformRationalPrimeLogBounds.{0} :=
  uniformBounds_of_normalizedConcreteSourceChains
    (normalizedConcreteSourceChains_of_components hsource)

/-- The independent uniform theorem specializes to the exact finite-stage
Baker--Wüstholz interface used by the Erdős-240 counting argument. -/
theorem hasRationalBakerWustholzBounds_of_normalizedConcreteSourceComponents
    (hsource : HasNormalizedConcreteSourceComponents.{0}) :
    HasRationalBakerWustholzBounds :=
  BakerSpecialization.hasRationalBakerWustholzBounds_of_uniform
    (uniformRationalPrimeLogBounds_of_normalizedConcreteSourceComponents
      hsource)

/-- The complete resolution of Problem 240 now waits only on the faithful
normalized concrete source-component construction.  All height absorption,
integer/real cutoff normalization, finite-stage specialization, tuple
counting, prime supply, and passage to the infinite prime set are internal. -/
theorem problem240_of_normalizedConcreteSourceComponents
    (hsource : HasNormalizedConcreteSourceComponents.{0}) :
    Problem240 :=
  problem240_of_tijdemanSquareLogBounds
    (HasRationalBakerWustholzBounds.toSquareLogBounds
      (hasRationalBakerWustholzBounds_of_normalizedConcreteSourceComponents
        hsource))

#print axioms uniformRationalPrimeLogBounds_of_normalizedConcreteSourceComponents
#print axioms hasRationalBakerWustholzBounds_of_normalizedConcreteSourceComponents
#print axioms problem240_of_normalizedConcreteSourceComponents

end Erdos240.BakerProblem240Bridge
