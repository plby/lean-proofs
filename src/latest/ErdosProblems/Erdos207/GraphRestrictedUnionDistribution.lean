/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GraphRestrictedDistribution
import ErdosProblems.Erdos207.LocalizedMasterUnionRootedThreatWeight

/-! # Joint selected-union and residual-edge estimates in the working graph -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem IsGraphStronglyWellDistributed.probability_union_and_edges_le
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k : Fin (ell + 1)} {G : SimpleGraph V}
    {initial later : Ω → TripleSystemOn V} {p C b : ℝ≥0}
    (h : IsGraphStronglyWellDistributed L W k G initial later p C b)
    (Q : TripleSystemOn V) (E : Finset (Sym2 V)) (hE : E ⊆ graphEdges G) :
    L.probability (fun ω ↦ Q ⊆ initial ω ∪ later ω ∧
      ∀ e ∈ E, e ∉ (coveredGraph (initial ω)).edgeSet) ≤
      C ^ (Q.card + E.card) * (p ^ E.card * setWeight (masterUnionTriangleWeight W k p) Q + 2 ^ Q.card * b) := by
  classical
  let Event := fun S : TripleSystemOn V ↦ StrongDistributionEvent initial later S (Q \ S) E
  have hcover : L.probability (fun ω ↦ Q ⊆ initial ω ∪ later ω ∧
      ∀ e ∈ E, e ∉ (coveredGraph (initial ω)).edgeSet) ≤
      L.probability (fun ω ↦ ∃ S ∈ Q.powerset, Event S ω) := by
    apply L.probability_mono
    intro ω hω
    obtain ⟨S, hS, hpart⟩ := subset_union_implies_strongDistributionEvent_partition initial later Q ω hω.1
    exact ⟨S, hS, hpart.1, hpart.2.1, hω.2⟩
  have hpart : ∀ S ∈ Q.powerset, L.probability (Event S) ≤
      C ^ (Q.card + E.card) *
        (p ^ E.card * (Fintype.card V : ℝ≥0)⁻¹ ^ S.card * laterTriangleScale W k p (Q \ S) + b) := by
    intro S hS
    have hSQ := mem_powerset.mp hS
    have hcard : S.card + (Q \ S).card = Q.card := by
      rw [card_sdiff_of_subset hSQ]
      have := card_le_card hSQ
      omega
    have hdis : Disjoint S (Q \ S) := disjoint_sdiff_self_right
    simpa only [Event, hcard] using h S (Q \ S) E hdis hE
  calc
    _ ≤ L.probability (fun ω ↦ ∃ S ∈ Q.powerset, Event S ω) := hcover
    _ ≤ ∑ S ∈ Q.powerset, L.probability (Event S) := L.probability_exists_le Q.powerset Event
    _ ≤ ∑ S ∈ Q.powerset, C ^ (Q.card + E.card) *
        (p ^ E.card * (Fintype.card V : ℝ≥0)⁻¹ ^ S.card * laterTriangleScale W k p (Q \ S) + b) :=
      sum_le_sum hpart
    _ = _ := by
      rw [← mul_sum, sum_add_distrib, setWeight_masterUnionTriangleWeight_eq_sum]
      simp_rw [mul_assoc]
      rw [← mul_sum]
      simp

theorem IsGraphStronglyWellDistributed.probability_union_and_edges_prefix_le
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k : Fin (ell + 1)} {G : SimpleGraph V}
    {initial later : Ω → TripleSystemOn V} {p C b : ℝ≥0}
    (h : IsGraphStronglyWellDistributed L W k G initial later p C b)
    (hp : p ≤ 1) (hnonempty : ∀ i, (W.U i).Nonempty)
    (Q : TripleSystemOn V) (E : Finset (Sym2 V)) (hE : E ⊆ graphEdges G) :
    L.probability (fun ω ↦ Q ⊆ initial ω ∪ later ω ∧
      ∀ e ∈ E, e ∉ (coveredGraph (initial ω)).edgeSet) ≤
      (2 * C) ^ (Q.card + E.card) *
        (p ^ E.card * setWeight (vortexTripleWeight (W.prefix k) 2) Q + b) := by
  have hw : setWeight (masterUnionTriangleWeight W k p) Q ≤ setWeight (vortexTripleWeight (W.prefix k) 2) Q :=
    setWeight_mono_pointwise (masterUnionTriangleWeight_le_prefix_vortex_two W k p hp hnonempty) Q
  apply (h.probability_union_and_edges_le Q E hE).trans
  have ht : (2 : ℝ≥0) ^ Q.card ≤ 2 ^ (Q.card + E.card) := pow_le_pow_right₀ (by norm_num) (Nat.le_add_right _ _)
  have hone : (1 : ℝ≥0) ≤ 2 ^ (Q.card + E.card) := one_le_pow₀ (by norm_num)
  calc
    _ ≤ C ^ (Q.card + E.card) * (p ^ E.card * setWeight (vortexTripleWeight (W.prefix k) 2) Q + 2 ^ Q.card * b) :=
      mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hw zero_le) le_rfl) zero_le
    _ ≤ C ^ (Q.card + E.card) *
        (2 ^ (Q.card + E.card) * (p ^ E.card * setWeight (vortexTripleWeight (W.prefix k) 2) Q) +
          2 ^ (Q.card + E.card) * b) := by
      apply mul_le_mul_of_nonneg_left _ zero_le
      apply add_le_add
      · simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right hone
            (show 0 ≤ p ^ E.card * setWeight (vortexTripleWeight (W.prefix k) 2) Q from zero_le))
      · exact mul_le_mul_of_nonneg_right ht zero_le
    _ = _ := by rw [mul_pow]; ring

end

end Erdos207
