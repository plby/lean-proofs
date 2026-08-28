import ErdosProblems.Erdos577.TwoExposedFullCounts

/-! The zero-third-row case exposes an actual leaf and noncentral row of degree four. -/

namespace Erdos577.TwoExposed

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem full_center_three_second_one_false {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {a : Finset V} (ha : a ∈ c.blocks)
    (hx : degreeIn G p.leaf a = 4) (hr : degreeIn G p.center a = 3)
    (hb : degreeIn G (p.vertices 2) a = 1) : False := by
  obtain ⟨v, hvm⟩ := card_pos.mp
    (show 0 < (a.filter (G.Adj (p.vertices 2))).card from by change 0 < degreeIn G _ a; omega)
  obtain ⟨hv, hbv⟩ := mem_filter.mp hvm
  have hcl := FullRow.full_leaf_clique hc p hp ha hx
  have hFA : Disjoint p.support a := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha)
  have hxout : p.leaf ∉ a := fun hh ↦
    disjoint_left.mp hFA (p.support_eq ▸ mem_insert_self _ _) hh
  have hvt : v ∉ p.triangle := fun hh ↦
    disjoint_left.mp hFA ((p.support_eq ▸ subset_insert _ _) hh) hv
  have hxvne : p.leaf ≠ v := fun he ↦ hxout (he.symm ▸ hv)
  let p' := alternatePaw p v hvt hbv.symm
  have hpair : PawPair p p' := alternatePaw_pair p v hvt hbv.symm hxvne
  have hrows := JointClaims.triangle_rows_disjoint hc hcard hn p hp ha (by omega)
    p.center (p.vertices 2) p.center_mem_triangle (by simp [Paw.triangle])
    (p.vertices.injective.ne (by decide : (1 : Fin 4) ≠ 2))
  have hrv : ¬G.Adj p.center v := fun hh ↦
    disjoint_left.mp hrows (mem_filter.mpr ⟨hv, hh⟩) hvm
  have hrerase : degreeIn G p.center (a.erase v) = 3 := by
    have he := degreeIn_erase_add G p.center v hv
    rw [if_neg hrv, hr] at he
    omega
  have hvdegree : degreeIn G v a = 3 := by
    rw [degreeIn_clique G hcl.isClique hv, hcl.card_eq]
  have hxv : G.Adj p.leaf v :=
    (degreeIn_eq_card_iff p.leaf a).mp (hx.trans hcl.card_eq.symm) v hv
  have hxe : p.leaf ∉ a.erase v := fun hh ↦ hxout (mem_erase.mp hh).2
  have hvfour : degreeIn G v (insert p.leaf (a.erase v)) = 4 := by
    rw [degreeIn_insert G v p.leaf hxe, if_pos hxv.symm,
      degreeIn_erase_self G v hv, hvdegree]
  have hrfour : degreeIn G p.center (insert p.leaf (a.erase v)) = 4 := by
    rw [degreeIn_insert G p.center p.leaf hxe,
      if_pos (show G.Adj p.center p.leaf from p.pendant.symm), hrerase]
  obtain ⟨e, he, heV, heT, _, _, hblocks⟩ := FullRow.exists_full_leaf_swap hc p hp ha hx v hv
  have hp' : p'.support = e.remainder := by
    change p'.support = insert e.terminal e.triangle
    rw [p'.support_eq, hpair.triangle, heV, heT]
    rfl
  have hnew : insert p.leaf (a.erase v) ∈ e.blocks := by
    rw [hblocks]
    exact mem_union_right _ (mem_singleton_self _)
  have hbound := (he.claim_two_four hcard hdeg hn p' hp' hnew).1
  change degreeIn G v (insert p.leaf (a.erase v)) +
    degreeIn G p.center (insert p.leaf (a.erase v)) ≤ 6 at hbound
  omega

end Erdos577.TwoExposed
