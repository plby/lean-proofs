import ErdosProblems.Erdos577.LocalFactors

/-! Positive local factors or triangle reductions with an explicit block-edge lower bound. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma LocalChain.exists_with_block {s b : Finset V} (hs : s.card = 8) (hb : b ⊆ s)
    (hq : QuadOn G b) (ht : TriangleIn G (s \ b)) :
    ∃ d : LocalChain G s, d.block = b := by
  obtain ⟨t, hts, ht⟩ := ht
  have hr4 : (s \ b).card = 4 := by rw [card_sdiff_of_subset hb, hs, hq.card]
  have hx1 : ((s \ b) \ t).card = 1 := by rw [card_sdiff_of_subset hts, hr4, ht.card_eq]
  obtain ⟨x, hx⟩ := card_eq_one.mp hx1
  have hxm : x ∈ (s \ b) \ t := by rw [hx]; exact mem_singleton_self _
  have he : insert x t = s \ b := by
    calc
      insert x t = t ∪ {x} := by ext v; simp
      _ = t ∪ ((s \ b) \ t) := by rw [hx]
      _ = s \ b := union_sdiff_of_subset hts
  refine ⟨{
    terminal := x
    triangle := t
    block := b
    triangle_clique := ht
    terminal_not_mem := (mem_sdiff.mp hxm).2
    quad := hq
    disjoint := ?_
    cover := ?_ }, rfl⟩
  · rw [he]
    exact sdiff_disjoint
  · rw [he]
    exact sdiff_union_of_subset hb

def TriangleReduction (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) (minEdges : ℕ) : Prop :=
  ∃ d : LocalChain G s, minEdges ≤ edgeCount G d.block

lemma TriangleReduction.image {W : Type*} [DecidableEq W] {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj] {s : Finset V} {minEdges : ℕ}
    (h : TriangleReduction G s minEdges) (f : G.Copy H) :
    TriangleReduction H (s.image f) minEdges := by
  obtain ⟨d, hd⟩ := h
  exact ⟨d.image f, hd.trans (d.image_edgeCount_le f)⟩

def ScoredExchange (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) (minEdges : ℕ) : Prop :=
  LocalFactor G s ∨ TriangleReduction G s minEdges

lemma ScoredExchange.image {W : Type*} [DecidableEq W] {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj] {s : Finset V} {minEdges : ℕ}
    (h : ScoredExchange G s minEdges) (f : G.Copy H) :
    ScoredExchange H (s.image f) minEdges := by
  rcases h with h | h
  · exact Or.inl (h.image f)
  · exact Or.inr (h.image f)

lemma LocalExchange.scored_four [DecidableRel G.Adj] {s : Finset V}
    (h : LocalExchange G s) (hs : s.card = 8) : ScoredExchange G s 4 := by
  obtain ⟨b, hb, hq, hrem⟩ := h
  rcases hrem with hrem | hrem
  · exact Or.inl ⟨b, hb, hq, hrem⟩
  · obtain ⟨d, hd⟩ := LocalChain.exists_with_block hs hb hq hrem
    refine Or.inr ⟨d, ?_⟩
    rw [hd]
    exact hq.four_le_edgeCount

end Erdos577
