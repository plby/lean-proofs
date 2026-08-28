import ErdosProblems.Erdos577.JointDenseCore
import ErdosProblems.Erdos577.FullRowCompleteBlock

/-! CaseI exposes its specified center-neighbor as a second strong terminal. -/

namespace Erdos577.JointFirst

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem complete_first_replacement {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (q : Quadrilateral G) (hq : q.support = s) (hcase : JointClaims.CaseOne p q) :
    G.IsNClique 4 (insert p.leaf (s.erase (q 1))) := by
  have hcl := FullRow.full_leaf_clique hc p hp hs (hq ▸ hcase.1)
  have hu : q 1 ∈ s := hq ▸ (q.mem_support _).mpr ⟨1, rfl⟩
  have hthree : G.IsNClique 3 (s.erase (q 1)) :=
    ⟨hcl.isClique.subset (coe_subset.mpr (erase_subset _ _)), by
      rw [card_erase_of_mem hu, hcl.card_eq]⟩
  have hrow := (degreeIn_eq_card_iff p.leaf s).mp ((hq ▸ hcase.1).trans hcl.card_eq.symm)
  exact hthree.insert (fun v hv ↦ hrow v (mem_erase.mp hv).2)

theorem exists_center_terminal {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (q : Quadrilateral G) (hq : q.support = s) (hcase : JointClaims.CaseOne p q) :
    ∃ d : TriangleChain G, d.Strong ∧ d.terminal = q 1 ∧ d.triangle = p.triangle ∧
      d.edgeScore = c.edgeScore ∧ d.completeScore = c.completeScore ∧
      d.blocks = c.blocks.erase s ∪ {insert p.leaf (s.erase (q 1))} ∧
      (∀ a ∈ c.blocks, a ≠ s → a ∈ d.blocks) := by
  obtain ⟨d, hdf, ht, hT, he, hf, hblocks⟩ := FullRow.exists_full_leaf_swap hc p hp hs
    (hq ▸ hcase.1) (q 1) (hq ▸ (q.mem_support _).mpr ⟨1, rfl⟩)
  have hbound := d.terminal_degree_le_one hcard hn
  rw [ht, hT] at hbound
  have hpos : 0 < degreeIn G (q 1) p.triangle := card_pos.mpr
    ⟨p.center, mem_filter.mpr ⟨p.center_mem_triangle, hcase.2.1.symm⟩⟩
  have hstrong : d.Strong := by
    refine ⟨hdf, ?_⟩
    change degreeIn G d.terminal d.triangle = 1
    rw [ht, hT]
    omega
  refine ⟨d, hstrong, ht, hT, he, hf, hblocks, ?_⟩
  intro a ha has
  rw [hblocks]
  exact mem_union_left _ (mem_erase.mpr ⟨has, ha⟩)

theorem first_noncentral_replacement {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (q : Quadrilateral G) (hq : q.support = s) (hcase : JointClaims.CaseOne p q) :
    QuadOn G (insert (p.vertices 2) (s.erase (q 1))) := by
  have hm : q 1 ∈ s := hq ▸ (q.mem_support _).mpr ⟨1, rfl⟩
  have hcol := JointClaims.triangle_column_le_one hc hcard hn p hp hs
    (by rw [← hq, hcase.1]; decide) (q 1) hm
  have hmiss : ¬G.Adj (p.vertices 2) (q 1) := by
    intro hh
    have htwo : ({p.center, p.vertices 2} : Finset V) ⊆ p.triangle.filter (G.Adj (q 1)) :=
      insert_subset (mem_filter.mpr ⟨p.center_mem_triangle, hcase.2.1.symm⟩)
        (singleton_subset_iff.mpr (mem_filter.mpr ⟨by simp [Paw.triangle], hh.symm⟩))
    have hne : p.center ≠ p.vertices 2 := p.vertices.injective.ne (by decide : (1 : Fin 4) ≠ 2)
    have hc2 := card_le_card htwo
    rw [card_pair_eq_two_iff.mpr hne] at hc2
    change 2 ≤ degreeIn G (q 1) p.triangle at hc2
    omega
  have hr := JointCore.noncentral_replacement_of_missed hc p hp hs q hq (Or.inl hcase)
    (q 1) ((q.mem_support _).mpr ⟨1, rfl⟩) hmiss
  rwa [hq] at hr

end Erdos577.JointFirst
