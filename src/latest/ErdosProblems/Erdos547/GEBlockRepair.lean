import ErdosProblems.Erdos547.GESupport
import ErdosProblems.Erdos547.FractionalReplacement

/-!
# Fractional load deficit inside a nontrivial GE block

At most one matching edge leaves a block. Consequently its internal
fractional matching differs in vertex loads from a perfect fractional
matching at only that edge's endpoint.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace GallaiEdmondsPartition

theorem nontrivial_of_mem_block (D : GallaiEdmondsPartition G) {C : Finset V}
    (hC : C ∈ D.blocks) (hlarge : 1 < C.card) {u : V} (hu : u ∈ C) :
    u ∈ D.nontrivialVertices :=
  Finset.mem_biUnion.mpr ⟨C, Finset.mem_filter.mpr ⟨hC, hlarge⟩, hu⟩

theorem allowed_outside_nontrivial_block (D : GallaiEdmondsPartition G) {C : Finset V}
    (hC : C ∈ D.blocks) (hlarge : 1 < C.card) {u v : V} (hu : u ∈ C) (hv : v ∉ C)
    (h : D.Allowed u v) : D.matching.Adj u v := by
  have hubig := D.nontrivial_of_mem_block hC hlarge hu
  rcases h with (h | ⟨B, hB, _, huB, hvB⟩) | ⟨huS, _⟩ | ⟨_, huSingle⟩
  · exact h
  · have hBC : B = C := D.separates.eq_of_mem_parts hB hC huB hu
    exact (hv (hBC ▸ hvB)).elim
  · exact (D.nontrivial_not_separator hubig huS).elim
  · exact (D.singleton_not_nontrivial huSingle hubig).elim

theorem matching_neighbour_outside_block (D : GallaiEdmondsPartition G) {C : Finset V}
    (hC : C ∈ D.blocks) {z y : V} (hz : z ∈ C) (hzy : D.matching.Adj z y) : y ∉ C := by
  have hzS : z ∉ D.separator := (Finset.mem_sdiff.mp (D.separates.part_subset hC hz)).2
  have hyS : y ∈ D.separator := by
    rcases D.crosses z y hzy with ⟨hz', _⟩ | ⟨hy', _⟩
    · exact (hzS hz').elim
    · exact hy'
  exact fun hy ↦ Finset.disjoint_left.mp (D.separates.part_disjoint_separator hC) hy hyS

open scoped Classical in
theorem IsFractionalGE.cross_weight_eq {D : GallaiEdmondsPartition G}
    {μ : FractionalMatching G} (h : D.IsFractionalGE μ) {C : Finset V}
    (hC : C ∈ D.blocks) (hlarge : 1 < C.card) {z y : V}
    (hz : z ∈ C) (hzy : D.matching.Adj z y) {u v : V} (hu : u ∈ C) (hv : v ∉ C) :
    μ.weight u v = if u = z ∧ v = y then μ.weight z y else 0 := by
  classical
  by_cases heq : u = z ∧ v = y
  · rw [if_pos heq, heq.1, heq.2]
  · rw [if_neg heq]
    apply le_antisymm _ (μ.nonnegative u v)
    apply le_of_not_gt
    intro hpos
    have hm := D.allowed_outside_nontrivial_block hC hlarge hu hv (h.allowed_of_pos hpos)
    have huz : u = z := D.one_per_block C hC ⟨hu, hm.fst_mem⟩ ⟨hz, hzy.fst_mem⟩
    have hvy : v = y := D.isMatching.eq_of_adj_left (huz ▸ hm) hzy
    exact heq ⟨huz, hvy⟩

theorem exists_perfect_fractional_on_block (D : GallaiEdmondsPartition G)
    {C : Finset V} (hC : C ∈ D.blocks) (hlarge : 1 < C.card) :
    ∃ P : FractionalMatching G,
      (∀ u ∈ C, P.load u = 1) ∧ (∀ u ∉ C, P.load u = 0) ∧
      (∀ u v, u ∉ C ∨ v ∉ C → P.weight u v = 0) := by
  classical
  have hc : Fintype.card (C : Set V) = C.card := Fintype.card_of_subtype C (fun _ ↦ Iff.rfl)
  let : Nontrivial (C : Set V) := Fintype.one_lt_card_iff_nontrivial.mp (by rwa [hc])
  obtain ⟨P, hP⟩ := exists_perfect_fractional_of_factorCritical (G.induce (C : Set V))
    (D.factorCritical C hC)
  refine ⟨P.liftInduced (C : Set V), ?_, ?_, ?_⟩
  · intro u hu
    rw [FractionalMatching.liftInduced_load_of_mem _ _ hu, hP]
  · exact fun u hu ↦ FractionalMatching.liftInduced_load_of_notMem _ _ hu
  · exact fun u v huv ↦ FractionalMatching.liftInduced_weight_eq_zero_of_notMem _ _ huv

open scoped Classical in
theorem IsFractionalGE.block_load_gap {D : GallaiEdmondsPartition G}
    {μ : FractionalMatching G} (h : D.IsFractionalGE μ) {C : Finset V}
    (hC : C ∈ D.blocks) (hlarge : 1 < C.card) {z y : V}
    (hz : z ∈ C) (hzy : D.matching.Adj z y)
    (P : FractionalMatching G) (hP : ∀ u ∈ C, P.load u = 1)
    (hPout : ∀ u ∉ C, P.load u = 0) (u : V) :
    P.load u - (μ.inside (C : Set V)).load u = if u = z then μ.weight z y else 0 := by
  classical
  have hy := D.matching_neighbour_outside_block hC hz hzy
  by_cases hu : u ∈ C
  · have hzero : ∀ v ∉ (C : Set V), v ≠ y → μ.weight u v = 0 := by
      intro v hv hvy
      rw [h.cross_weight_eq hC hlarge hz hzy hu hv, if_neg (fun hp ↦ hvy hp.2)]
    have hrow := μ.inside_load_add_unique_outside hu hy hzero
    have hmu : μ.load u = 1 := h.load_nontrivial (D.nontrivial_of_mem_block hC hlarge hu)
    rw [hmu, h.cross_weight_eq hC hlarge hz hzy hu hy] at hrow
    rw [hP u hu]
    simp only [and_true] at hrow
    linarith
  · have huz : u ≠ z := fun heq ↦ hu (heq ▸ hz)
    rw [hPout u hu, μ.inside_load_of_notMem hu, if_neg huz, sub_self]

end GallaiEdmondsPartition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsFractionalGE.block_load_gap
