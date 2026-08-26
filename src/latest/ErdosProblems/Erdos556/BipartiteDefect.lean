import ErdosProblems.Erdos556.BipartitePaths

/-! Missing-neighbour bounds for a dense bipartite pair. -/

namespace Erdos556

open SimpleGraph Finset

structure BipartiteDefect {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (X Y : Finset V) (d : ℕ) : Prop where
  left : ∀ x ∈ X, (Y.filter (fun y => ¬ G.Adj x y)).card ≤ d
  right : ∀ y ∈ Y, (X.filter (fun x => ¬ G.Adj y x)).card ≤ d

theorem BipartiteDefect.mono {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {X Y X' Y' : Finset V} {d : ℕ}
    (h : BipartiteDefect G X Y d) (hX : X' ⊆ X) (hY : Y' ⊆ Y) :
    BipartiteDefect G X' Y' d := by
  constructor
  · intro x hx
    exact (card_le_card (filter_subset_filter _ hY)).trans (h.left x (hX hx))
  · intro y hy
    exact (card_le_card (filter_subset_filter _ hX)).trans (h.right y (hY hy))

theorem BipartiteDefect.symm {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {X Y : Finset V} {d : ℕ}
    (h : BipartiteDefect G X Y d) : BipartiteDefect G Y X d := ⟨h.right, h.left⟩

theorem exists_neighbor_avoiding_of_defect {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) (Y F : Finset V) (d : ℕ)
    (hmiss : (Y.filter (fun y => ¬ G.Adj x y)).card ≤ d) (hsize : F.card + d < Y.card) :
    ∃ y ∈ Y, y ∉ F ∧ G.Adj x y := by
  classical
  let B := Y.filter (fun y => ¬ G.Adj x y)
  have hc : (F ∪ B).card < Y.card :=
    (card_union_le F B).trans_lt ((Nat.add_le_add_left hmiss F.card).trans_lt hsize)
  obtain ⟨y, hy, hybad⟩ := exists_mem_notMem_of_card_lt_card hc
  have hyF : y ∉ F := fun h => hybad (mem_union_left _ h)
  have hyB : y ∉ B := fun h => hybad (mem_union_right _ h)
  refine ⟨y, hy, hyF, ?_⟩
  by_contra h
  exact hyB (mem_filter.mpr ⟨hy, h⟩)

theorem exists_common_neighbor_of_defect {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) (Y : Finset V) (d : ℕ)
    (hu : (Y.filter (fun y => ¬ G.Adj u y)).card ≤ d)
    (hv : (Y.filter (fun y => ¬ G.Adj v y)).card ≤ d) (hsize : 2 * d < Y.card) :
    ∃ y ∈ Y, G.Adj u y ∧ G.Adj v y := by
  obtain ⟨y, hy, hybad, huy⟩ := exists_neighbor_avoiding_of_defect G u Y
    (Y.filter (fun y => ¬ G.Adj v y)) d hu (by omega)
  refine ⟨y, hy, huy, ?_⟩
  by_contra h
  exact hybad (mem_filter.mpr ⟨hy, h⟩)

#print axioms exists_common_neighbor_of_defect

end Erdos556
