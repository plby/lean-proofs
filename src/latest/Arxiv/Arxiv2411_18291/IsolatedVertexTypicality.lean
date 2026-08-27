import Arxiv.Arxiv2411_18291.GraphBoundedness
import Arxiv.Arxiv2411_18291.Incidence
import Mathlib.Tactic

/-! # An isolated vertex obstructs typicality in a nonempty graph -/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V]

def pairStar (v : V) : Hypergraph V 2 := univ.filter fun e => v ∈ e.val

@[simp] theorem mem_pairStar (v : V) (e : Block V 2) : e ∈ pairStar v ↔ v ∈ e.val := by
  simp [pairStar]

theorem card_pairStar (v : V) : (pairStar v).card = Fintype.card V - 1 := by
  have h := card_blocks_between (r := 2) ({v} : Finset V) univ (subset_univ _)
    (by simp)
  simpa [pairStar] using h

theorem not_typical_of_isolated_vertex (G : Hypergraph V 2) (hG : G.Nonempty)
    (v : V) (hiso : ∀ e ∈ G, v ∉ e.val) {c : ℝ} (hc : c < 1) {h : ℕ} (hh : 1 ≤ h) :
    ¬IsTypical G c h := by
  intro hT
  let S : Block V 1 := ⟨{v}, card_singleton v⟩
  have hfilter : G.filter (fun e => S.val ⊆ e.val) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro e he
    exact hiso e (mem_filter.mp he).1 ((mem_filter.mp he).2 (mem_singleton_self v))
  obtain ⟨e, he⟩ := hG
  have hn : 2 ≤ Fintype.card V := by
    simpa only [e.property] using card_le_univ e.val
  have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast (by omega : 0 < Fintype.card V)
  have hd : 0 < density G := by
    unfold density
    exact div_pos (Nat.cast_pos.mpr (card_pos.mpr ⟨e, he⟩))
      (Nat.cast_pos.mpr (Nat.choose_pos hn))
  have hp : 0 < (Fintype.card V : ℝ) * density G := mul_pos hN hd
  have ht := hT {S} (by simpa only [card_singleton] using hh)
  simp only [card_singleton, pow_one, commonNeighbors_singleton, card_neighbors_eq_degree,
    hfilter, card_empty, Nat.cast_zero, zero_sub, abs_neg, abs_of_pos hp] at ht
  nlinarith only [ht, hp, mul_pos (sub_pos.mpr hc) hp]

end Arxiv2411_18291
