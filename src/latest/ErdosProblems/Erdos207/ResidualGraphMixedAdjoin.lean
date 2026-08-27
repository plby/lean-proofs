/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ResidualGraphAdjoinNumeric
import ErdosProblems.Erdos207.GraphMixedProductBound

/-! # Mixed nibble laws supply the quantitative residual update -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem IsGraphMixedProductBound.selected_inclusion_le
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    {L : FiniteLaw Ω} {selected : Ω → TripleSystemOn V} {G : SimpleGraph V}
    {survival point C error : ℝ≥0}
    (h : IsGraphMixedProductBound L selected G survival point C error)
    (Q : TripleSystemOn V) :
    L.probability (fun x ↦ Q ⊆ selected x) ≤ (C * point) ^ Q.card + C ^ Q.card * error := by
  have hraw := h Q ∅ (empty_subset _)
  simpa only [card_empty, Nat.add_zero, pow_zero, one_mul, notMem_empty,
    IsEmpty.forall_iff, implies_true, and_true, mul_add, mul_pow] using hraw

theorem IsResidualGraphStronglyWellDistributed.jointBind_adjoin_graphMixed
    {Ω Ξ V : Type*} [Fintype Ω] [Fintype Ξ] [Fintype V]
    [DecidableEq Ω] [DecidableEq Ξ] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {K : Ω → FiniteLaw Ξ} {W : Vortex V ell} {k next : Fin (ell + 1)}
    {G : SimpleGraph V} {initial later : Ω → TripleSystemOn V} {p C b : ℝ≥0}
    (hstrong : IsResidualGraphStronglyWellDistributed L W k G initial later p C b)
    (added : Ω → Ξ → TripleSystemOn V) (testGraph : Ω → SimpleGraph V)
    (survival point constant : Ω → ℝ≥0) (alpha J factor delta : ℝ≥0)
    (hC : 1 ≤ C) (hJ : 1 ≤ J) (hfactor : 1 ≤ factor) (halpha : alpha ≤ 1)
    (hkn : k ≤ next) (hnonempty : ∀ i, (W.U i).Nonempty)
    (hnew : alpha * p ^ 3 ≤ factor * (p / ((W.U k).card : ℝ≥0)))
    (hmixed : ∀ ω, 0 < L.mass ω → IsGraphMixedProductBound (K ω) (added ω)
      (testGraph ω) (survival ω) (point ω) (constant ω) delta)
    (hpoint : ∀ ω, 0 < L.mass ω → constant ω * point ω ≤ alpha)
    (hconstant : ∀ ω, 0 < L.mass ω → constant ω ≤ J)
    (hstruct : ∀ ω, 0 < L.mass ω → (K ω).SupportedOn fun ξ ↦
      IsPackingOn ((initial ω ∪ later ω) ∪ added ω ξ) ∧
      Disjoint (initial ω ∪ later ω) (added ω ξ) ∧
      ∀ T ∈ added ω ξ, tripleEdgeFinset T ⊆ graphEdges G)
    (hscope : ∀ ω, 0 < L.mass ω → (K ω).SupportedOn fun ξ ↦
      ∀ T ∈ added ω ξ, T.1 ⊆ W.U k) :
    IsResidualGraphStronglyWellDistributed (L.jointBind K) W next G
      (jointInitial initial) (jointLater later added) p (2 * max (C ^ 3 * factor) J) (b + delta) := by
  apply hstrong.jointBind_adjoin_numeric added alpha J factor delta
    hC hJ hfactor halpha hkn hnonempty hnew _ hstruct hscope
  intro ω hω Q
  apply ((hmixed ω hω).selected_inclusion_le Q).trans
  exact add_le_add (pow_le_pow_left' (hpoint ω hω) _)
    (mul_le_mul_of_nonneg_right (pow_le_pow_left' (hconstant ω hω) _) zero_le)

theorem IsResidualGraphStronglyWellDistributed.conditionOn_adjoin_graphMixed
    {Ω Ξ V : Type*} [Fintype Ω] [Fintype Ξ] [Fintype V]
    [DecidableEq Ω] [DecidableEq Ξ] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {K : Ω → FiniteLaw Ξ} {W : Vortex V ell} {k next : Fin (ell + 1)}
    {G : SimpleGraph V} {initial later : Ω → TripleSystemOn V} {p C b : ℝ≥0}
    (hstrong : IsResidualGraphStronglyWellDistributed L W k G initial later p C b)
    (Good : Ω → Prop) (hGood : 0 < L.probability Good)
    (added : Ω → Ξ → TripleSystemOn V) (testGraph : Ω → SimpleGraph V)
    (survival point constant : Ω → ℝ≥0) (alpha J factor delta : ℝ≥0)
    (hC : 1 ≤ C) (hJ : 1 ≤ J) (hfactor : 1 ≤ factor) (halpha : alpha ≤ 1)
    (hkn : k ≤ next) (hnonempty : ∀ i, (W.U i).Nonempty)
    (hnew : alpha * p ^ 3 ≤ factor * (p / ((W.U k).card : ℝ≥0)))
    (hmixed : ∀ ω, Good ω → IsGraphMixedProductBound (K ω) (added ω)
      (testGraph ω) (survival ω) (point ω) (constant ω) delta)
    (hpoint : ∀ ω, Good ω → constant ω * point ω ≤ alpha)
    (hconstant : ∀ ω, Good ω → constant ω ≤ J)
    (hstruct : ∀ ω, Good ω → (K ω).SupportedOn fun ξ ↦
      IsPackingOn ((initial ω ∪ later ω) ∪ added ω ξ) ∧
      Disjoint (initial ω ∪ later ω) (added ω ξ) ∧
      ∀ T ∈ added ω ξ, tripleEdgeFinset T ⊆ graphEdges G)
    (hscope : ∀ ω, Good ω → (K ω).SupportedOn fun ξ ↦
      ∀ T ∈ added ω ξ, T.1 ⊆ W.U k) :
    IsResidualGraphStronglyWellDistributed ((L.conditionOn Good hGood).jointBind K) W next G
      (jointInitial initial) (jointLater later added) p
      (2 * max ((C / L.probability Good) ^ 3 * factor) J) (b + delta) := by
  have hsupport := L.conditionOn_supported Good hGood
  have hC' : 1 ≤ C / L.probability Good := by
    apply (le_div_iff₀ hGood).mpr
    simpa only [one_mul] using (L.probability_le_one Good).trans hC
  exact (hstrong.conditionOn Good hGood).jointBind_adjoin_graphMixed
    added testGraph survival point constant alpha J factor delta
    hC' hJ hfactor halpha hkn hnonempty hnew
    (fun ω hω ↦ hmixed ω (hsupport ω hω))
    (fun ω hω ↦ hpoint ω (hsupport ω hω))
    (fun ω hω ↦ hconstant ω (hsupport ω hω))
    (fun ω hω ↦ hstruct ω (hsupport ω hω))
    (fun ω hω ↦ hscope ω (hsupport ω hω))

end

end Erdos207
