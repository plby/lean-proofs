/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceLinkMomentWeights
import ErdosProblems.Erdos207.LinkReserveAccounting

/-! # The canonical inner-edge and reserve-spoke weights in the source link lemma -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

def sourceLinkCanonicalEdgeWeight
    {V : Type*} [DecidableEq V] (U : Finset V) (p r : ℝ≥0) (e : Sym2 V) : ℝ≥0 := by
  classical
  exact p * if IsCrossingEdge U e then r else 1

theorem sourceLinkCanonicalEdgeWeight_le_one
    {V : Type*} [DecidableEq V] (U : Finset V) (p r : ℝ≥0)
    (hp : p ≤ 1) (hr : r ≤ 1) (e : Sym2 V) : sourceLinkCanonicalEdgeWeight U p r e ≤ 1 := by
  classical
  unfold sourceLinkCanonicalEdgeWeight
  split_ifs
  · exact (mul_le_of_le_one_right zero_le hr).trans hp
  · simpa only [mul_one] using hp

theorem sourceLinkCanonicalEdgeWeight_product
    {V : Type*} [DecidableEq V] (U : Finset V) (p r : ℝ≥0) (E : Finset (Sym2 V)) :
    setWeight (sourceLinkCanonicalEdgeWeight U p r) E =
      p ^ E.card * r ^ (E.filter (IsCrossingEdge U)).card := by
  classical
  unfold setWeight sourceLinkCanonicalEdgeWeight
  rw [prod_mul_distrib, prod_ite]
  simp only [prod_const, one_pow, mul_one]

theorem sourceLinkCanonicalEdgeWeight_triangle
    {V : Type*} [DecidableEq V] (U : Finset V) (p r : ℝ≥0) (T : TripleOn V)
    (hT : (tripleCrossingEdges U T).card = 2) :
    setWeight (sourceLinkCanonicalEdgeWeight U p r) (tripleEdgeFinset T) = p ^ 3 * r ^ 2 := by
  rw [sourceLinkCanonicalEdgeWeight_product, card_tripleEdgeFinset]
  exact congrArg (fun m ↦ p ^ 3 * r ^ m) hT

theorem sourceLinkCanonicalEdgeWeight_root_triangle
    {V : Type*} [DecidableEq V] (U : Finset V) (p r : ℝ≥0) (T : TripleOn V)
    (hT : (tripleCrossingEdges U T).card = 2) {e : Sym2 V}
    (he : e ∈ tripleEdgeFinset T) (hcross : IsCrossingEdge U e) :
    setWeight (sourceLinkCanonicalEdgeWeight U p r) ((tripleEdgeFinset T).erase e) = p ^ 2 * r := by
  rw [sourceLinkCanonicalEdgeWeight_product, card_erase_of_mem he, card_tripleEdgeFinset]
  have heq : ((tripleEdgeFinset T).erase e).filter (IsCrossingEdge U) =
      (tripleCrossingEdges U T).erase e := by
    ext f
    simp only [mem_filter, mem_erase, tripleCrossingEdges]
    tauto
  have heCross : e ∈ tripleCrossingEdges U T := mem_filter.mpr ⟨he, hcross⟩
  rw [heq, card_erase_of_mem heCross, hT]
  norm_num

theorem sourceLinkCanonicalWeight_block_le
    (p r a n u : ℝ≥0) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r)
    (_hn : 0 < n) (hu : 0 < u) (hscale : r * a ≤ p * u / n) :
    (a / (r * p ^ 2 * u)) * (p ^ 3 * r ^ 2) ≤ p / n := by
  have hdivide : r * a / u ≤ p / n := by
    apply (div_le_iff₀ hu).mpr
    exact hscale.trans_eq (by ring)
  calc
    _ = p * (r * a / u) := by field_simp
    _ ≤ p * (p / n) := mul_le_mul_of_nonneg_left hdivide zero_le
    _ ≤ p / n := mul_le_of_le_one_left zero_le hp1

theorem sourceLinkCanonicalWeight_root_block
    (p r a u : ℝ≥0) (hp : 0 < p) (hr : 0 < r) (hu : 0 < u) :
    (a / (r * p ^ 2 * u)) * (p ^ 2 * r) = a / u := by
  field_simp

end

end Erdos207
