/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyContinuation
import ErdosProblems.Erdos207.CoverDownExtraction

/-!
# Terminal cover-down from an intermediate constrained-greedy state

The continuation law is automatically supported on exhausted invariant
extensions.  Therefore the entire final cover-down reduces to the uniform
pair-indexed failure estimate below; no structural or maximality hypotheses
remain to be supplied separately.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- A uniform failure estimate for the exhausted continuation of any
intermediate absorber-greedy state yields an outside packing. -/
theorem exists_ksssOutsidePacking_of_continuation_failure_probability
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (H : SimpleGraph V) (X : Finset V)
    (B : TripleSystemOn V) (S₀ : GreedyStateOn V) (ε : ℝ≥0)
    (hS₀ : AbsorberGreedyInvariant
      (absorberErdosForbiddenConfigurationsOn q B)
      (outsideAvailableTriangles H B) S₀)
    (hprob : ∀ e : DistinctPair V,
      (FiniteLaw.iterateKernel
        (greedyKernel (absorberErdosForbiddenConfigurationsOn q B))
        S₀.available.card (FiniteLaw.pure S₀)).probability
          (fun S ↦ KSSSCountFailureAt q H X B e S) ≤ ε)
    (hsmall : (Fintype.card (DistinctPair V) : ℝ≥0) * ε < 1) :
    ∃ P : TripleSystemOn V, HasKSSSOutsidePacking q H X B P := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let A := outsideAvailableTriangles H B
  let L := FiniteLaw.iterateKernel (greedyKernel F)
    S₀.available.card (FiniteLaw.pure S₀)
  have hsupport : L.SupportedOn (fun S ↦
      AbsorberGreedyInvariant F A S ∧ S.available = ∅) := by
    intro S hmass
    have h := absorberGreedyContinuationLaw_supported S₀ hS₀ S hmass
    exact ⟨h.1, h.2.2⟩
  apply exists_ksssOutsidePacking_of_uniform_failure_probability
    q H X B L id ε
  · simpa only [F, A, L, id_eq] using hsupport
  · intro e
    simpa only [F, L, id_eq] using hprob e
  · exact hsmall

/-- Sum-form variant, convenient when different ordered pairs receive
different estimates. -/
theorem exists_ksssOutsidePacking_of_continuation_sum_failure
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (H : SimpleGraph V) (X : Finset V)
    (B : TripleSystemOn V) (S₀ : GreedyStateOn V)
    (hS₀ : AbsorberGreedyInvariant
      (absorberErdosForbiddenConfigurationsOn q B)
      (outsideAvailableTriangles H B) S₀)
    (hsmall : ∑ e : DistinctPair V,
      (FiniteLaw.iterateKernel
        (greedyKernel (absorberErdosForbiddenConfigurationsOn q B))
        S₀.available.card (FiniteLaw.pure S₀)).probability
          (fun S ↦ KSSSCountFailureAt q H X B e S) < 1) :
    ∃ P : TripleSystemOn V, HasKSSSOutsidePacking q H X B P := by
  let F := absorberErdosForbiddenConfigurationsOn q B
  let A := outsideAvailableTriangles H B
  let L := FiniteLaw.iterateKernel (greedyKernel F)
    S₀.available.card (FiniteLaw.pure S₀)
  have hsupport : L.SupportedOn (fun S ↦
      AbsorberGreedyInvariant F A S ∧ S.available = ∅) := by
    intro S hmass
    have h := absorberGreedyContinuationLaw_supported S₀ hS₀ S hmass
    exact ⟨h.1, h.2.2⟩
  apply exists_ksssOutsidePacking_of_sum_failure_probability_lt_one
    q H X B L id
  · simpa only [F, A, L, id_eq] using hsupport
  · simpa only [F, L, id_eq] using hsmall

end

end Erdos207
