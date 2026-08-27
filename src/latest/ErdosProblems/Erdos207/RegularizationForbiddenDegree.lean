/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RegularizationForbiddenFamily
import ErdosProblems.Erdos207.ForbiddenFamilyDegreeUnion

/-! # Explicit density bound for the regularizer's actual forbidden family -/

namespace Erdos207

open Finset

noncomputable section

theorem regularizationForbiddenFamily_max_degree_le
    {V I K : Type*} [DecidableEq V] [Fintype I] [DecidableEq I] [DecidableEq K]
    (e : I ↪ TripleOn V) (U : Finset V) (hsupport : ∀ i, (e i).1 ⊆ U)
    (k : ℕ) (hk : 2 ≤ k) (G : Finset (Finset I))
    (orders : Finset K) (earlier : K → Finset (Finset I)) (size : K → ℕ)
    (hsize : ∀ i ∈ orders, 1 ≤ size i ∧ size i ≤ k)
    (huniform : ∀ i ∈ orders, ∀ E ∈ earlier i, E.card = size i) :
    finiteHypergraphMaxDegree (regularizationForbiddenFamily e k G (orders.biUnion earlier)) ≤
      6 * U.card ^ 2 * (Fintype.card I) ^ (k - 2) +
      (∑ i ∈ orders, 2 * finiteHypergraphMaxDegree (earlier i) * (Fintype.card I) ^ (k - size i)) +
      finiteHypergraphMaxDegree G := by
  unfold regularizationForbiddenFamily
  apply (finiteHypergraphMaxDegree_union_le _ G).trans
  apply Nat.add_le_add_right
  apply (finiteHypergraphMaxDegree_union_le _ _).trans
  exact Nat.add_le_add (auxiliaryNonDisjointFamily_max_degree_le e U hsupport k hk)
    (uniformSupersets_biUnion_max_degree_le orders earlier size k hsize huniform)

end

end Erdos207
