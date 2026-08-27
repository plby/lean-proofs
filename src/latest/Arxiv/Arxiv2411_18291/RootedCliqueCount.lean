import Arxiv.Arxiv2411_18291.RootedCliqueExtensions

/-!
# Exact counts between consecutive rooted clique sizes

Each extension is counted once per removable vertex outside its root.
The resulting identity supplies both upper and lower counting recurrences,
with the factorial normalization needed for precise clique estimates.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {r a k : ℕ}

theorem card_rootedClique_extensions (G : Hypergraph V (r + 1)) (I : Block V a)
    (U : Block V k) (hU : IsRootedClique G I.val U.val) :
    (cliqueNextVertices G U).card =
      ((rootedCliques G I (k + 1)).filter fun W => U.val ⊆ W.val).card := by
  apply card_bij (fun v hv => extendBlock U v ((mem_cliqueNextVertices G U v).mp hv).2)
  · intro v hv
    refine mem_filter.mpr ⟨(mem_rootedCliques _ _ _).mpr ?_, subset_insert _ _⟩
    exact (hU.insert_iff ((mem_cliqueNextVertices G U v).mp hv).2).mpr hv
  · intro v hv w hw he
    exact extendBlock_vertex_injective U _ _ he
  · intro W hW
    obtain ⟨hWr, hUW⟩ := mem_filter.mp hW
    obtain ⟨v, hv, he⟩ := exists_eq_insert_iff.mpr
      ⟨hUW, by rw [U.property, W.property]⟩
    refine ⟨v, (hU.insert_iff hv).mp ?_, Subtype.ext he⟩
    rw [he]
    exact (mem_rootedCliques _ _ _).mp hWr

theorem card_rootedClique_predecessors (G : Hypergraph V (r + 1)) (I : Block V a)
    (hak : a ≤ k) (W : Block V (k + 1)) (hW : IsRootedClique G I.val W.val) :
    ((rootedCliques G I k).filter fun U => U.val ⊆ W.val).card = k + 1 - a := by
  have heq : (rootedCliques G I k).filter (fun U => U.val ⊆ W.val) =
      univ.filter (fun U : Block V k => I.val ⊆ U.val ∧ U.val ⊆ W.val) := by
    ext U
    simp only [mem_filter, mem_rootedCliques, mem_univ, true_and]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨hW.mono h.2 h.1, h.2⟩⟩
  rw [heq, card_blocks_between I.val W.val hW.1 (by simpa only [I.property] using hak),
    W.property, I.property, show k + 1 - a = (k - a) + 1 by omega,
    Nat.choose_succ_self_right]

theorem rootedClique_step_count (G : Hypergraph V (r + 1)) (I : Block V a) (hak : a ≤ k) :
    (∑ U ∈ rootedCliques G I k, (cliqueNextVertices G U).card) =
      (k + 1 - a) * (rootedCliques G I (k + 1)).card := by
  calc
    _ = ∑ U ∈ rootedCliques G I k,
        ((rootedCliques G I (k + 1)).filter fun W => U.val ⊆ W.val).card := by
      apply sum_congr rfl
      intro U hU
      exact card_rootedClique_extensions G I U ((mem_rootedCliques _ _ _).mp hU)
    _ = ∑ W ∈ rootedCliques G I (k + 1),
        ((rootedCliques G I k).filter fun U => U.val ⊆ W.val).card := by
      simpa only [bipartiteAbove, bipartiteBelow] using
        sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
          (s := rootedCliques G I k) (t := rootedCliques G I (k + 1))
          (fun (U : Block V k) (W : Block V (k + 1)) => U.val ⊆ W.val)
    _ = _ := by
      have hc (W) (hW : W ∈ rootedCliques G I (k + 1)) :=
        card_rootedClique_predecessors G I hak W ((mem_rootedCliques _ _ _).mp hW)
      rw [sum_congr rfl hc]
      simp only [sum_const, smul_eq_mul, Nat.mul_comm]

theorem rootedClique_step_lower (G : Hypergraph V (r + 1)) (I : Block V a)
    (hak : a ≤ k) {L : ℝ}
    (hL : ∀ U ∈ rootedCliques G I k, L ≤ ((cliqueNextVertices G U).card : ℝ)) :
    (rootedCliques G I k).card * L ≤
      (k + 1 - a : ℕ) * ((rootedCliques G I (k + 1)).card : ℝ) := by
  calc
    _ = ∑ _ ∈ rootedCliques G I k, L := by simp
    _ ≤ ∑ U ∈ rootedCliques G I k, ((cliqueNextVertices G U).card : ℝ) := sum_le_sum hL
    _ = ((∑ U ∈ rootedCliques G I k, (cliqueNextVertices G U).card : ℕ) : ℝ) :=
      (Nat.cast_sum _ _).symm
    _ = _ := by rw [rootedClique_step_count G I hak, Nat.cast_mul]

theorem rootedClique_step_upper (G : Hypergraph V (r + 1)) (I : Block V a)
    (hak : a ≤ k) {L : ℝ}
    (hL : ∀ U ∈ rootedCliques G I k, ((cliqueNextVertices G U).card : ℝ) ≤ L) :
    (k + 1 - a : ℕ) * ((rootedCliques G I (k + 1)).card : ℝ) ≤
      (rootedCliques G I k).card * L := by
  calc
    _ = ((∑ U ∈ rootedCliques G I k, (cliqueNextVertices G U).card : ℕ) : ℝ) := by
      rw [rootedClique_step_count G I hak, Nat.cast_mul]
    _ = ∑ U ∈ rootedCliques G I k, ((cliqueNextVertices G U).card : ℝ) := Nat.cast_sum _ _
    _ ≤ ∑ _ ∈ rootedCliques G I k, L := sum_le_sum hL
    _ = _ := by simp

end Arxiv2411_18291
