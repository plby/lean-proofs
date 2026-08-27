/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.BoundedGraphInitialLaw
import ErdosProblems.Erdos207.KSSSInitialGraphLaw

/-! # Separate edge-survival and triangle-selection scales on genuine graph edges -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def IsGraphMixedProductBound
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (selected : Ω → TripleSystemOn V) (G : SimpleGraph V)
    (survival point C error : ℝ≥0) : Prop :=
  ∀ (Q : TripleSystemOn V) (edges : Finset (Sym2 V)), edges ⊆ graphEdges G →
    L.probability (fun x ↦ Q ⊆ selected x ∧ ∀ e ∈ edges, e ∉ (coveredGraph (selected x)).edgeSet) ≤
      C ^ (Q.card + edges.card) * (survival ^ edges.card * point ^ Q.card + error)

theorem graphMixedProductBound_of_bounded_compatible
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (selected : Ω → TripleSystemOn V) (G : SimpleGraph V)
    (ambient : TripleSystemOn V) (K : ℕ) (survival point C error : ℝ≥0)
    (hstruct : L.SupportedOn fun x ↦ IsPackingOn (selected x) ∧ selected x ⊆ ambient)
    (hcompatible : ∀ (Q : TripleSystemOn V) (edges : Finset (Sym2 V)),
      IsPackingOn Q → Q ⊆ ambient → Disjoint (Q.biUnion tripleEdgeFinset) edges → edges ⊆ graphEdges G →
      Q.card + edges.card ≤ K →
      L.probability (fun x ↦ Q ⊆ selected x ∧ ∀ e ∈ edges, e ∉ (coveredGraph (selected x)).edgeSet) ≤
        (C * survival) ^ edges.card * (C * point) ^ Q.card + error)
    (hC : 2 ≤ C) (herror : (1 / 2 : ℝ≥0) ^ K ≤ error) :
    IsGraphMixedProductBound L selected G survival point C error := by
  classical
  intro Q edges hedge
  by_cases hcard : Q.card + edges.card ≤ K
  · by_cases hgood : IsPackingOn Q ∧ Q ⊆ ambient ∧ Disjoint (Q.biUnion tripleEdgeFinset) edges
    · have h := hcompatible Q edges hgood.1 hgood.2.1 hgood.2.2 hedge hcard
      have hc1 : 1 ≤ C := (by norm_num : (1 : ℝ≥0) ≤ 2).trans hC
      have herr : error ≤ C ^ (Q.card + edges.card) * error := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (one_le_pow₀ hc1 : 1 ≤ C ^ (Q.card + edges.card)) zero_le
      apply h.trans
      calc
        _ ≤ (C * survival) ^ edges.card * (C * point) ^ Q.card + C ^ (Q.card + edges.card) * error := add_le_add le_rfl herr
        _ = _ := by simp only [mul_pow, pow_add]; ring
    · have hz : L.probability (fun x ↦ Q ⊆ selected x ∧ ∀ e ∈ edges, e ∉ (coveredGraph (selected x)).edgeSet) ≤
          L.probability (fun _ ↦ False) := by
        apply L.probability_mono_of_supported hstruct
        intro x hx hevent
        apply hgood
        refine ⟨hx.1.mono hevent.1, hevent.1.trans hx.2, disjoint_left.mpr ?_⟩
        intro e heQ heE
        obtain ⟨T, hT, heT⟩ := mem_biUnion.mp heQ
        apply hevent.2 e heE
        rw [coveredGraph_edgeSet_eq_biUnion]
        exact mem_biUnion.mpr ⟨T, hevent.1 hT, heT⟩
      rw [L.probability_false] at hz
      exact hz.trans zero_le
  · exact (L.probability_le_one _).trans
      (large_pattern_paid_by_dyadic_error K _ C error _ hC herror (Nat.lt_of_not_ge hcard))

theorem IsGraphMixedProductBound.map
    {Ω Ξ V : Type*} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ] [Fintype V] [DecidableEq V]
    {L : FiniteLaw Ω} {selected : Ξ → TripleSystemOn V} {G : SimpleGraph V}
    {survival point C error : ℝ≥0} (f : Ω → Ξ)
    (h : IsGraphMixedProductBound L (fun x ↦ selected (f x)) G survival point C error) :
    IsGraphMixedProductBound (L.map f) selected G survival point C error := by
  intro Q edges hedge
  rw [FiniteLaw.probability_map]
  exact h Q edges hedge

theorem IsGraphMixedProductBound.mono_parameters
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    {L : FiniteLaw Ω} {selected : Ω → TripleSystemOn V} {G : SimpleGraph V}
    {survival survival' point point' C C' error error' : ℝ≥0}
    (h : IsGraphMixedProductBound L selected G survival point C error)
    (hsurvival : survival ≤ survival') (hpoint : point ≤ point') (hC : C ≤ C') (herror : error ≤ error') :
    IsGraphMixedProductBound L selected G survival' point' C' error' := by
  intro Q edges hedge
  apply (h Q edges hedge).trans
  exact mul_le_mul (pow_le_pow_left' hC _) (add_le_add
    (mul_le_mul (pow_le_pow_left' hsurvival _) (pow_le_pow_left' hpoint _) zero_le zero_le) herror) zero_le zero_le

end

end Erdos207
