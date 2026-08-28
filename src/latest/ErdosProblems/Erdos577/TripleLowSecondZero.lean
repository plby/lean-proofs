import ErdosProblems.Erdos577.TripleLowThirdZero

/-! Two actual terminal swaps turn a positive second row into a Claim2.6 contradiction. -/

namespace Erdos577.UniversalTriple

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {q : Quadrilateral G} {a : Finset V}

theorem LowCore.second_zero (h : LowCore c p q a) (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ z, 2 * k ≤ G.degree z)
    (hn : ¬HasPacking G k) : degreeIn G (p.vertices 2) a = 0 := by
  by_contra hb
  have hthird := h.third_zero hc hcard hdeg hn
  have hbound := (hc.claim_two_four hcard hdeg hn p h.paw h.core_block).1
  have hsum := p.contacts_triangle a
  rw [h.leaf_three] at hbound
  rw [h.triangle_four, hthird] at hsum
  have hr : 0 < degreeIn G p.center a := by
    change 4 = degreeIn G p.center a + (degreeIn G (p.vertices 2) a + 0) at hsum
    omega
  obtain ⟨u, hurow⟩ := card_pos.mp
    (show 0 < (a.filter (G.Adj (p.vertices 2))).card from by
      change 0 < degreeIn G (p.vertices 2) a
      omega)
  obtain ⟨hu, hbu⟩ := mem_filter.mp hurow
  obtain ⟨v, hvrow⟩ := card_pos.mp hr
  obtain ⟨hv, hrv⟩ := mem_filter.mp hvrow
  have hrows := JointClaims.triangle_rows_disjoint hc hcard hn p h.paw h.core_block
    h.leaf_three.ge p.center (p.vertices 2) p.center_mem_triangle (by simp [Paw.triangle])
    (p.vertices.injective.ne (by decide : (1 : Fin 4) ≠ 2))
  have hvu : v ≠ u := fun he ↦ disjoint_left.mp hrows (he ▸ hvrow) hurow
  have hFA := h.toConfiguration.paw_disjoint_block h.core_block
  have huT : u ∉ p.triangle := fun hh ↦
    disjoint_left.mp hFA ((p.support_eq ▸ subset_insert _ _) hh) hu
  have hXu : p.leaf ≠ u := fun he ↦ disjoint_left.mp hFA
    (p.support_eq ▸ mem_insert_self _ _) (he.symm ▸ hu)
  let p' := TwoExposed.alternatePaw p u huT hbu.symm
  have hpair : TwoExposed.PawPair p p' :=
    TwoExposed.alternatePaw_pair p u huT hbu.symm hXu
  have hnewcl : G.IsNClique 4 (insert (q 3) (a.erase u)) :=
    h.core_complete.insert_erase (fun _ hw ↦ h.exposed_adj (mem_sdiff.mp hw).1) hu
  obtain ⟨d, hd, hdY, hdT, _, _, hdblocks⟩ := h.toConfiguration.exists_exposed_chain hc
  have had : a ∈ d.blocks := by
    rw [hdblocks]
    exact mem_union_left _ (mem_erase.mpr ⟨h.core_ne, h.core_block⟩)
  have hrep : QuadOn G (insert d.terminal (a.erase u)) := by
    rw [hdY]
    exact QuadOn.of_clique hnewcl.card_eq hnewcl.isClique
  have hscore : edgeCount G (insert d.terminal (a.erase u)) = edgeCount G a := by
    rw [hdY, edgeCount_clique hnewcl.isClique, hnewcl.card_eq,
      edgeCount_clique h.core_complete.isClique, h.core_complete.card_eq]
  obtain ⟨e, he, heU, heT, _, _, heblocks⟩ := hd.exists_terminal_swap had hu hrep hscore
  have hp' : p'.support = e.remainder := by
    change p'.support = insert e.terminal e.triangle
    rw [p'.support_eq, hpair.triangle, heU, heT, hdT]
    rfl
  have hnew : insert (q 3) (a.erase u) ∈ e.blocks := by
    rw [heblocks, hdY]
    exact mem_union_right _ (mem_singleton_self _)
  have hYout : q 3 ∉ a.erase u := fun hh ↦
    h.toConfiguration.exposed_outside_other h.core_block h.core_ne
      (mem_union_right _ (mem_erase.mp hh).2)
  have hufour : degreeIn G u (insert (q 3) (a.erase u)) = 4 := by
    rw [degreeIn_insert G u (q 3) hYout, if_pos (h.exposed_adj hu).symm,
      degreeIn_erase_self G u hu, degreeIn_clique G h.core_complete.isClique hu,
      h.core_complete.card_eq]
  have hrpos : 0 < degreeIn G p.center (insert (q 3) (a.erase u)) := card_pos.mpr
    ⟨v, mem_filter.mpr ⟨mem_insert_of_mem (mem_erase.mpr ⟨hvu, hv⟩), hrv⟩⟩
  have hzero := (he.claim_two_six hcard hdeg hn p' hp' hnew hufour).1
  rw [hpair.second] at hzero
  omega

end Erdos577.UniversalTriple
