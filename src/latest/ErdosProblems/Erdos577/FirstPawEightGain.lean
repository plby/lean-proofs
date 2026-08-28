import ErdosProblems.Erdos577.FirstPawEightRigidity
import ErdosProblems.Erdos577.MultiScores

/-! The normalized exceptional rows give two blocks with a strictly larger first score. -/

namespace Erdos577.FirstPawEight

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma complete_middle (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern8 p q) :
    QuadOn G {p.center, q 0, q 2, p.vertices 2} ∧
      edgeCount G {p.center, q 0, q 2, p.vertices 2} = 6 := by
  let f := coreCopy p q hd h
  have hquad : QuadOn (graph (Unattached.diagonal q)) {1, 4, 6, 2} := by
    rcases diagonal_cases q h.1 with he | he
    · rw [he]
      exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    · rw [he]
      exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  have hscore : edgeCount (graph (Unattached.diagonal q)) {1, 4, 6, 2} = 6 := by
    rcases diagonal_cases q h.1 with he | he <;> rw [he] <;> decide +kernel
  have hq := hquad.image f
  have hs := edgeCount_image_le f {1, 4, 6, 2}
  rw [hscore] at hs
  simp only [image_insert, image_singleton] at hq hs
  change QuadOn G {p.center, q 0, q 2, p.vertices 2} at hq
  change 6 ≤ edgeCount G {p.center, q 0, q 2, p.vertices 2} at hs
  exact ⟨hq, le_antisymm (edgeCount_le_six G hq.card) hs⟩

variable [Fintype V]

theorem normalized_gain_false {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern8 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (d : Quadrilateral G) (hdA : d.support = a) (hdiag : ¬G.Adj (d 1) (d 3))
    (hy1 : G.Adj (q 1) (d 1)) (hy2 : G.Adj (q 1) (d 2))
    (hw1 : G.Adj (q 3) (d 1)) (hw2 : G.Adj (q 3) (d 2))
    (hx0 : G.Adj p.leaf (d 0)) (hx3 : G.Adj p.leaf (d 3)) : False := by
  have hdis : Disjoint (p.support ∪ q.support) d.support := by
    rw [hp, hq, hdA, disjoint_union_left]
    refine ⟨?_, c.property.blocks_disjoint hb ha hab.symm⟩
    apply disjoint_left.mpr
    intro w hw hwa
    exact (mem_sdiff.mp (c.complementPartition.block_subset ha hwa)).2 hw
  let e := joinTuples (PawEncoding.labeling p q hd) d.toEmbedding (by
    change Disjoint (univ.image (PawEncoding.labeling p q hd)) d.support
    rw [PawEncoding.labeling_image]
    exact hdis)
  have hinj : Function.Injective (e : Fin 12 → V) := e.injective
  have hne (i j : Fin 12) (hij : i ≠ j) : e i ≠ e j := fun he ↦ hij (hinj he)
  have himage : univ.image e = (p.support ∪ q.support) ∪ d.support := by
    change tupleSupport (joinTuples _ _ _) = _
    rw [tupleSupport_joinTuples]
    change univ.image (PawEncoding.labeling p q hd) ∪ d.support = _
    rw [PawEncoding.labeling_image]
  let s : Finset (Fin 12) := {5, 9, 7, 10}
  let t : Finset (Fin 12) := {1, 4, 6, 2}
  let v := Quadrilateral.ofVertices (e 5) (e 9) (e 7) (e 10)
    (hne 5 9 (by decide)) (hne 5 7 (by decide)) (hne 5 10 (by decide))
    (hne 9 7 (by decide)) (hne 9 10 (by decide)) (hne 7 10 (by decide))
    hy1 hw1.symm hw2 hy2.symm
  have hv : v.support = s.image e := by
    change univ.image (![e 5, e 9, e 7, e 10] : Fin 4 → V) = _
    have hu : (univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
    rw [hu]
    simp only [s, image_insert, image_singleton, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three]
    rfl
  have hsquad : QuadOn G (s.image e) := ⟨v, hv⟩
  obtain ⟨htquad, htedge⟩ := complete_middle p q hd h
  have ht : t.image e = {p.center, q 0, q 2, p.vertices 2} := by
    simp only [t, image_insert, image_singleton]
    rfl
  rw [← ht] at htquad htedge
  have hsedge : edgeCount G (s.image e) = edgeCount G q.support := by
    rw [← hv, v.edgeCount_eq, q.edgeCount_eq, if_pos h.1]
    change 4 + (if G.Adj (q 1) (q 3) then 1 else 0) +
      (if G.Adj (d 1) (d 2) then 1 else 0) =
      4 + 1 + (if G.Adj (q 1) (q 3) then 1 else 0)
    have h12 : G.Adj (d 1) (d 2) := d.adjacent 1
    rw [if_pos h12]
    omega
  have ha5 : edgeCount G a ≤ 5 := by
    rw [← hdA, d.edgeCount_eq, if_neg hdiag]
    split_ifs <;> omega
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
    rw [himage, hp, hq, hdA]
    simp only [biUnion_insert, singleton_biUnion, id_eq, union_assoc]
  have hsub : s.image e ∪ t.image e ⊆ c.remainder ∪ ({b, a} : Finset (Finset V)).biUnion id := by
    rw [hcore, ← image_union]
    exact image_subset_image (subset_univ _)
  have hrem : (c.remainder ∪ ({b, a} : Finset (Finset V)).biUnion id) \ (s.image e ∪ t.image e) =
      ({0, 3, 8, 11} : Finset (Fin 12)).image e := by
    rw [hcore, ← image_union, ← image_sdiff _ _ hinj]
    congr 1
  have hrem4 : ((c.remainder ∪ ({b, a} : Finset (Finset V)).biUnion id) \
      (s.image e ∪ t.image e)).card = 4 := by
    rw [hrem, card_image_of_injective _ hinj]
    decide +kernel
  have htri : TriangleIn G ((c.remainder ∪ ({b, a} : Finset (Finset V)).biUnion id) \
      (s.image e ∪ t.image e)) := by
    rw [hrem]
    refine ⟨({0, 8, 11} : Finset (Fin 12)).image e, image_subset_image (by decide +kernel), ?_⟩
    simp only [image_insert, image_singleton]
    exact SimpleGraph.is3Clique_triple_iff.mpr ⟨hx0, hx3, (d.adjacent 3).symm⟩
  have hbound := hc.selected_edges_le {b, a} hbs part hsub hrem4 htri
  rw [BlockPartition.weightSum_union, BlockPartition.weightSum_single,
    BlockPartition.weightSum_single, hsedge, htedge, hq] at hbound
  have hold : (c.complementPartition.select {b, a} hbs).weightSum (edgeCount G) =
      edgeCount G b + edgeCount G a := by
    change ∑ z ∈ ({b, a} : Finset (Finset V)), edgeCount G z = _
    exact sum_pair hab.symm
  rw [hold] at hbound
  omega

end Erdos577.FirstPawEight
