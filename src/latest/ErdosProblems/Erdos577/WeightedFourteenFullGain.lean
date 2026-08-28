import ErdosProblems.Erdos577.WeightedFourteenTerminals
import ErdosProblems.Erdos577.MultiScores
import ErdosProblems.Erdos577.CycleLabels

/-! The final full-row branch strictly increases the first feasible-chain score. -/

namespace Erdos577.WeightedFourteen

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem full_rows_gain_false {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern14 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (v : Quadrilateral G) (hv : v.support = a) (hcl : G.IsNClique 4 v.support)
    (hxf : ∀ j : Fin 4, G.Adj p.leaf (v j)) (hyf : ∀ j : Fin 4, G.Adj (q 1) (v j))
    (hr : G.Adj p.center (v 0)) : False := by
  have hdis : Disjoint (p.support ∪ q.support) v.support := by
    rw [hp, hq, hv, disjoint_union_left]
    refine ⟨?_, c.property.blocks_disjoint hb ha hab.symm⟩
    apply disjoint_left.mpr
    intro w hw hwa
    exact (mem_sdiff.mp (c.complementPartition.block_subset ha hwa)).2 hw
  let e := joinTuples (PawEncoding.labeling p q hd) v.toEmbedding (by
    change Disjoint (univ.image (PawEncoding.labeling p q hd)) v.support
    rw [PawEncoding.labeling_image]
    exact hdis)
  have hinj : Function.Injective (e : Fin 12 → V) := e.injective
  have himage : univ.image e = (p.support ∪ q.support) ∪ v.support := by
    change tupleSupport (joinTuples _ _ _) = _
    rw [tupleSupport_joinTuples]
    change univ.image (PawEncoding.labeling p q hd) ∪ v.support = _
    rw [PawEncoding.labeling_image]
  let s : Finset (Fin 12) := {2, 4, 7, 6}
  let t : Finset (Fin 12) := {5, 9, 10, 11}
  have hs : s.image e = insert (p.vertices 2) (q.support.erase (q 1)) := by
    have hqinj : Function.Injective (q : Fin 4 → V) := q.injective
    rw [Quadrilateral.support, ← image_erase hqinj]
    have he : (univ : Finset (Fin 4)).erase 1 = {0, 2, 3} := by decide
    rw [he]
    simp only [s, image_insert, image_singleton]
    change {p.vertices 2, q 0, q 3, q 2} = {p.vertices 2, q 0, q 2, q 3}
    ext w
    simp only [mem_insert, mem_singleton]
    tauto
  have ht : t.image e = insert (q 1) (v.support.erase (v 0)) := by
    have hvinj : Function.Injective (v : Fin 4 → V) := v.injective
    rw [Quadrilateral.support, ← image_erase hvinj]
    have he : (univ : Finset (Fin 4)).erase 0 = {1, 2, 3} := by decide
    rw [he]
    simp only [t, image_insert, image_singleton]
    rfl
  have hsquad : QuadOn G (s.image e) := by
    simp only [s, image_insert, image_singleton]
    apply QuadOn.of_vertices
      (fun he ↦ (by decide : (2 : Fin 12) ≠ 7) (e.injective he))
      (fun he ↦ (by decide : (4 : Fin 12) ≠ 6) (e.injective he))
    · exact (h.2.2.1 0).mpr (by decide)
    · exact (q.adjacent 3).symm
    · exact (q.adjacent 2).symm
    · exact ((h.2.2.1 2).mpr (by decide)).symm
  have hyout : q 1 ∉ v.support := fun hh ↦ disjoint_left.mp hdis
    (mem_union_right _ ((q.mem_support _).mpr ⟨1, rfl⟩)) hh
  have htquad : QuadOn G (t.image e) := by
    rw [ht]
    exact v.quad_replaceAt 0 (q 1) hyout (fun j _ ↦ hyf j)
  have hsedge : edgeCount G (s.image e) = edgeCount G q.support + 1 := by
    have hbo : p.vertices 2 ∉ q.support := fun hh ↦
      disjoint_left.mp hd ((mem_tupleSupport p.vertices _).mpr ⟨2, rfl⟩) hh
    have hb3 : degreeIn G (p.vertices 2) q.support = 3 := by
      rw [(h.2.2.1).degree p q 2 13]
      decide +kernel
    have hbn : ¬G.Adj (p.vertices 2) (q 1) := by
      intro hh
      have he := (h.2.2.1 1).mp hh
      contradiction
    have hlow : degreeIn G (q 1) q.support = 2 := by
      rw [q.degreeIn_eq]
      change 2 + (if G.Adj (q 1) (q 3) then 1 else 0) = 2
      rw [if_neg h.1]
    have herase := degreeIn_erase_add G (p.vertices 2) (q 1) ((q.mem_support _).mpr ⟨1, rfl⟩)
    rw [if_neg hbn] at herase
    have he := edgeCount_replace G (q 1) (p.vertices 2) ((q.mem_support _).mpr ⟨1, rfl⟩) hbo
    rw [hs]
    omega
  have ha6 : edgeCount G v.support = 6 := by
    rw [edgeCount_clique hcl.isClique, hcl.card_eq]
    decide +kernel
  have htedge : edgeCount G (t.image e) = 6 := by
    have hy4 : degreeIn G (q 1) v.support = 4 := by
      apply (degreeIn_eq_card_iff (q 1) v.support).mpr
        (fun u hu ↦ by obtain ⟨j, rfl⟩ := (v.mem_support u).mp hu; exact hyf j) |>.trans
      exact hcl.card_eq
    have hu : v 0 ∈ v.support := (v.mem_support _).mpr ⟨0, rfl⟩
    have hu3 := degreeIn_clique G hcl.isClique hu
    rw [hcl.card_eq] at hu3
    have herase := degreeIn_erase_add G (q 1) (v 0) hu
    rw [if_pos (hyf 0)] at herase
    have he := edgeCount_replace G (v 0) (q 1) hu hyout
    rw [ht]
    omega
  have hst : Disjoint (s.image e) (t.image e) := by
    rw [disjoint_image hinj]
    decide +kernel
  let part := (BlockPartition.single hsquad).union (BlockPartition.single htquad) hst
  have hbs : ({b, a} : Finset (Finset V)) ⊆ c.blocks := by
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact hb
    · exact mem_singleton.mp hz ▸ ha
  have hcore : c.remainder ∪ ({b, a} : Finset (Finset V)).biUnion id = univ.image e := by
    rw [himage, hp, hq, hv]
    simp only [biUnion_insert, singleton_biUnion, id_eq, union_assoc]
  have hsub : s.image e ∪ t.image e ⊆ c.remainder ∪ ({b, a} : Finset (Finset V)).biUnion id := by
    rw [hcore, ← image_union]
    exact image_subset_image (subset_univ _)
  have hrem : (c.remainder ∪ ({b, a} : Finset (Finset V)).biUnion id) \ (s.image e ∪ t.image e) =
      ({0, 1, 3, 8} : Finset (Fin 12)).image e := by
    rw [hcore, ← image_union, ← image_sdiff _ _ hinj]
    congr 1
  have hrem4 : ((c.remainder ∪ ({b, a} : Finset (Finset V)).biUnion id) \
      (s.image e ∪ t.image e)).card = 4 := by
    rw [hrem, card_image_of_injective _ hinj]
    decide +kernel
  have htri : TriangleIn G ((c.remainder ∪ ({b, a} : Finset (Finset V)).biUnion id) \
      (s.image e ∪ t.image e)) := by
    rw [hrem]
    refine ⟨({0, 1, 8} : Finset (Fin 12)).image e, image_subset_image (by decide +kernel), ?_⟩
    simp only [image_insert, image_singleton]
    exact SimpleGraph.is3Clique_triple_iff.mpr ⟨p.pendant, hxf 0, hr⟩
  have hbound := hc.selected_edges_le {b, a} hbs part hsub hrem4 htri
  rw [BlockPartition.weightSum_union, BlockPartition.weightSum_single,
    BlockPartition.weightSum_single, hsedge, htedge, hq] at hbound
  have hOld : (c.complementPartition.select {b, a} hbs).weightSum (edgeCount G) =
      edgeCount G b + 6 := by
    change ∑ z ∈ ({b, a} : Finset (Finset V)), edgeCount G z = _
    rw [sum_pair hab.symm, ← hv, ha6]
  rw [hOld] at hbound
  omega

theorem no_full_principal_rows {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern14 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (hcl : G.IsNClique 4 a)
    (hx4 : degreeIn G p.leaf a = 4) (hy4 : degreeIn G (q 1) a = 4)
    (hrpos : 0 < degreeIn G p.center a) : False := by
  obtain ⟨u, hu⟩ := card_pos.mp hrpos
  obtain ⟨hua, hru⟩ := mem_filter.mp hu
  obtain ⟨v, hv⟩ := c.property.blocks_quad a ha
  obtain ⟨i, hui⟩ := (v.mem_support u).mp (hv.symm ▸ hua)
  let v' := v.rotate i
  have hv' : v'.support = a := (v.rotate_support i).trans hv
  have hcl' : G.IsNClique 4 v'.support := hv'.symm ▸ hcl
  have hfull (z : V) (hz4 : degreeIn G z a = 4) (j : Fin 4) : G.Adj z (v' j) :=
    (degreeIn_eq_card_iff z a).mp (hz4.trans hcl.card_eq.symm) (v' j)
      (hv' ▸ (v'.mem_support _).mpr ⟨j, rfl⟩)
  have hr' : G.Adj p.center (v' 0) := by simpa only [v', Quadrilateral.rotate_apply, zero_add, hui]
    using hru
  exact full_rows_gain_false hc p hp hb q hq hd h ha hab v' hv' hcl' (hfull p.leaf hx4)
    (hfull (q 1) hy4) hr'

end Erdos577.WeightedFourteen
