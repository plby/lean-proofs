import Arxiv.Arxiv2411_18291.PuncturedClique
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Exact counting between consecutive clique sizes

Adding a vertex counts each larger punctured clique once for every removable
vertex outside its specified edge. This provides the factorial correction
when the one-vertex lower bounds are iterated.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {r k : ℕ}

omit [Fintype V] in
/-- The new vertex is recoverable from the extended vertex set. -/
theorem extendBlock_vertex_injective (U : Block V k) {v w : V}
    (hv : v ∉ U.val) (hw : w ∉ U.val)
    (he : extendBlock U v hv = extendBlock U w hw) : v = w := by
  have hm : v ∈ (extendBlock U w hw).val := by rw [← he]; exact mem_insert_self _ _
  rcases mem_insert.mp hm with h | h
  · exact h
  · exact (hv h).elim

theorem card_cliqueNextVertices_eq (G : Hypergraph V (r + 1)) (e : Block V (r + 1))
    (U : Block V k) (hU : IsPuncturedClique G e U.val) :
    (cliqueNextVertices G U).card =
      ((puncturedCliques G e (k + 1)).filter fun W => U.val ⊆ W.val).card := by
  apply card_bij (fun v hv => extendBlock U v ((mem_cliqueNextVertices G U v).mp hv).2)
  · intro v hv
    apply mem_filter.mpr
    refine ⟨(mem_puncturedCliques _ _ _).mpr ?_, subset_insert _ _⟩
    exact (hU.insert_iff ((mem_cliqueNextVertices G U v).mp hv).2).mpr hv
  · intro v hv w hw he
    exact extendBlock_vertex_injective U _ _ he
  · intro W hW
    obtain ⟨hWp, hUW⟩ := mem_filter.mp hW
    obtain ⟨v, hv, he⟩ := exists_eq_insert_iff.mpr
      ⟨hUW, by rw [U.property, W.property]⟩
    refine ⟨v, (hU.insert_iff hv).mp ?_, Subtype.ext he⟩
    rw [he]
    exact (mem_puncturedCliques _ _ _).mp hWp

/-- A larger punctured clique has exactly `k+1-(r+1)` predecessors. -/
theorem card_puncturedClique_predecessors (G : Hypergraph V (r + 1)) (e : Block V (r + 1))
    (hk : r + 1 ≤ k) (W : Block V (k + 1)) (hW : IsPuncturedClique G e W.val) :
    ((puncturedCliques G e k).filter fun U => U.val ⊆ W.val).card = k + 1 - (r + 1) := by
  have heq : (puncturedCliques G e k).filter (fun U => U.val ⊆ W.val) =
      univ.filter (fun U : Block V k => e.val ⊆ U.val ∧ U.val ⊆ W.val) := by
    ext U
    simp only [mem_filter, mem_puncturedCliques, mem_univ, true_and]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨hW.mono h.2 h.1, h.2⟩⟩
  rw [heq, card_blocks_between e.val W.val hW.1 (by simpa only [e.property] using hk),
    W.property, e.property, show k + 1 - (r + 1) = (k - (r + 1)) + 1 by omega,
    Nat.choose_succ_self_right]

/-- Double counting, with no approximation or assumed independence. -/
theorem puncturedClique_step_count (G : Hypergraph V (r + 1)) (e : Block V (r + 1))
    (hk : r + 1 ≤ k) :
    (∑ U ∈ puncturedCliques G e k, (cliqueNextVertices G U).card) =
      (k + 1 - (r + 1)) * (puncturedCliques G e (k + 1)).card := by
  calc
    _ = ∑ U ∈ puncturedCliques G e k,
        ((puncturedCliques G e (k + 1)).filter fun W => U.val ⊆ W.val).card := by
      apply sum_congr rfl
      intro U hU
      exact card_cliqueNextVertices_eq G e U ((mem_puncturedCliques _ _ _).mp hU)
    _ = ∑ W ∈ puncturedCliques G e (k + 1),
        ((puncturedCliques G e k).filter fun U => U.val ⊆ W.val).card := by
      simpa only [bipartiteAbove, bipartiteBelow] using
        sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
          (s := puncturedCliques G e k) (t := puncturedCliques G e (k + 1))
          (fun (U : Block V k) (W : Block V (k + 1)) => U.val ⊆ W.val)
    _ = _ := by
      have hc (W) (hW : W ∈ puncturedCliques G e (k + 1)) :=
        card_puncturedClique_predecessors G e hk W ((mem_puncturedCliques _ _ _).mp hW)
      rw [sum_congr rfl hc]
      simp [mul_comm]

theorem puncturedClique_step_lower (G : Hypergraph V (r + 1)) (e : Block V (r + 1))
    (hk : r + 1 ≤ k) {L : ℝ}
    (hL : ∀ U ∈ puncturedCliques G e k, L ≤ ((cliqueNextVertices G U).card : ℝ)) :
    (puncturedCliques G e k).card * L ≤
      (k + 1 - (r + 1) : ℕ) * ((puncturedCliques G e (k + 1)).card : ℝ) := by
  calc
    _ = ∑ _ ∈ puncturedCliques G e k, L := by simp
    _ ≤ ∑ U ∈ puncturedCliques G e k, ((cliqueNextVertices G U).card : ℝ) := sum_le_sum hL
    _ = ((∑ U ∈ puncturedCliques G e k, (cliqueNextVertices G U).card : ℕ) : ℝ) :=
      (Nat.cast_sum _ _).symm
    _ = _ := by rw [puncturedClique_step_count G e hk, Nat.cast_mul]

end Arxiv2411_18291
