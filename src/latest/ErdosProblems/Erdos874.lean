/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos874.Foundations
import ErdosProblems.Erdos874.Tail
import ErdosProblems.Erdos874.Asymptotics
import ErdosProblems.Erdos874.ExactUpper
import ErdosProblems.Erdos874.Structure
import ErdosProblems.Erdos874.EndpointOrientation

/-!
# Erdős Problem 874

For a finite set `A` of positive integers, `restrictedSumset r A` is the set
of sums of `r` distinct members of `A`.  The predicate `IsAdmissible A` says
that the positive-cardinality restricted sumsets are pairwise disjoint.
The extremal function `k N` is the largest cardinality of an admissible
subset of `{1, ..., N}`.

Deshouillers and Freiman proved that, for all sufficiently large `N`,

`k N = Nat.sqrt (4 * N + 1) - 1`.

The final theorem below records the resulting answer
`k N / sqrt N -> 2`.
-/

open Filter
open scoped Topology

namespace Erdos874

/-- Straus's terminal interval gives the sharp lower construction for every
`N`, without any sufficiently-large hypothesis. -/
theorem erdos_874_lower_bound (N : ℕ) :
    Nat.sqrt (4 * N + 1) - 1 ≤ k N := by
  exact strausLength_le_k N

/-- The square inequality proved by the density endgame is exactly the
integer upper bound matching Straus's construction. -/
theorem le_strausLength_of_sq {N m : ℕ}
    (h : (m + 1) ^ 2 ≤ 4 * N + 1) :
    m ≤ strausLength N := by
  have hsqrt : m + 1 ≤ Nat.sqrt (4 * N + 1) := Nat.le_sqrt'.2 h
  simp only [strausLength]
  omega

/-- Once the finite density endgame has been constructed for every
maximizer, the upper and lower bounds identify `k N` exactly. -/
theorem exact_of_maximizers_density_endgame {N : ℕ}
    (hendgame : ∀ A : Finset ℤ, IsBoundedAdmissible N A →
      A.card = k N → HasDensityEndgame N A) :
    k N = strausLength N := by
  apply le_antisymm
  · exact le_strausLength_of_sq
      (k_sq_le_of_maximizers_density_endgame hendgame)
  · exact strausLength_le_k N

/-- Eventual finite density data gives the eventual exact closed form. -/
theorem eventual_exact_of_eventually_maximizers_density_endgame
    (hendgame : ∀ᶠ N : ℕ in atTop,
      ∀ A : Finset ℤ, IsBoundedAdmissible N A →
        A.card = k N → HasDensityEndgame N A) :
    ∀ᶠ N : ℕ in atTop, k N = strausLength N := by
  filter_upwards [hendgame] with N hN
  exact exact_of_maximizers_density_endgame hN

/-- The asymptotic resolution follows formally from any eventual construction
of the finite Deshouillers--Freiman density endgame. -/
theorem tendsto_of_eventually_maximizers_density_endgame
    (hendgame : ∀ᶠ N : ℕ in atTop,
      ∀ A : Finset ℤ, IsBoundedAdmissible N A →
        A.card = k N → HasDensityEndgame N A) :
    Tendsto (fun N : ℕ ↦ (k N : ℝ) / Real.sqrt N) atTop (𝓝 2) := by
  apply tendsto_normalized_of_eventuallyEq_sqrt_formula
  filter_upwards
    [eventual_exact_of_eventually_maximizers_density_endgame hendgame] with N hN
  simpa [strausLength] using hN

/-- The Deshouillers--Freiman resolution: for every sufficiently large `N`,
the extremal cardinality is exactly the length of Straus's terminal interval. -/
theorem erdos_874_eventual_exact :
    ∀ᶠ N : ℕ in atTop, k N = strausLength N := by
  exact eventual_exact_of_eventually_maximizers_density_endgame
    (eventually_maximizers_density_endgame hasEventuallyLargeSetStructure)

/-- Erdős Problem 874 has the conjectured asymptotic answer
`k N / sqrt N → 2`. -/
theorem erdos_874 :
    Tendsto (fun N : ℕ ↦ (k N : ℝ) / Real.sqrt N) atTop (nhds 2) := by
  exact tendsto_of_eventually_maximizers_density_endgame
    (eventually_maximizers_density_endgame hasEventuallyLargeSetStructure)

end Erdos874
