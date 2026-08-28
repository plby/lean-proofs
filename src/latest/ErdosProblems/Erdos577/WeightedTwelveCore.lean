import ErdosProblems.Erdos577.WeightedTwelveCoreZero

/-! Actual dense-core labels and complementary cycles for the final pattern12 argument. -/

namespace Erdos577.WeightedTwelve

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

structure DensePair (p : Paw G) (d : Quadrilateral G) : Prop where
  disjoint : Disjoint p.support d.support
  complete : G.IsNClique 4 d.support
  dense : 11 ≤ contacts G p.triangle d.support
  center_first : G.Adj p.center (d 2)
  center_second : G.Adj p.center (d 3)
  primary : G.IsNClique 4 ((p.triangle ∪ d.support) \ {p.center, d 2, d 3})

theorem exists_dense_pair (p : Paw G) {a : Finset V} (ha : G.IsNClique 4 a)
    (hd : Disjoint p.support a) (hT : 11 ≤ contacts G p.triangle a) :
    ∃ d : Quadrilateral G, d.support = a ∧ DensePair p d := by
  obtain ⟨d, hlabel, hr1, hr2, _, hprimary, _, _, _⟩ := JointCore.high_core_pair p ha hd hT
  refine ⟨d, hlabel, ⟨?_, ?_, ?_, hr1, hr2, ?_⟩⟩
  · rwa [hlabel]
  · rwa [hlabel]
  · rwa [hlabel]
  · rwa [hlabel]

def DensePair.pairPaw {p : Paw G} {d : Quadrilateral G} (h : DensePair p d) : Paw G :=
  Paw.ofVertices p.leaf p.center (d 2) (d 3) p.pendant.ne
    (fun he ↦ disjoint_left.mp h.disjoint (p.support_eq ▸ mem_insert_self _ _)
      (he.symm ▸ (d.mem_support _).mpr ⟨2, rfl⟩))
    (fun he ↦ disjoint_left.mp h.disjoint (p.support_eq ▸ mem_insert_self _ _)
      (he.symm ▸ (d.mem_support _).mpr ⟨3, rfl⟩))
    h.center_first.ne h.center_second.ne (d.injective.ne (by decide))
    p.pendant h.center_first h.center_second (d.adjacent 2)

lemma DensePair.pairPaw_apply {p : Paw G} {d : Quadrilateral G} (h : DensePair p d) (i : Fin 4) :
    h.pairPaw.vertices i = ![p.leaf, p.center, d 2, d 3] i := rfl

lemma DensePair.pairPaw_support {p : Paw G} {d : Quadrilateral G} (h : DensePair p d) :
    h.pairPaw.support = insert p.leaf {p.center, d 2, d 3} := h.pairPaw.support_eq

lemma DensePair.complement_clique {p : Paw G} {d : Quadrilateral G} (h : DensePair p d) :
    G.IsNClique 4 {p.vertices 2, p.vertices 3, d 0, d 1} := by
  rw [← JointFinal.primary_support_eq p d h.disjoint]
  exact h.primary

lemma DensePair.center_third_degrees {p : Paw G} {d : Quadrilateral G} (h : DensePair p d) :
    3 ≤ degreeIn G p.center d.support ∧ 3 ≤ degreeIn G (p.vertices 3) d.support := by
  have hr := degreeIn_le_card G p.center d.support
  have hb := degreeIn_le_card G (p.vertices 2) d.support
  have hc := degreeIn_le_card G (p.vertices 3) d.support
  rw [d.card_support] at hr hb hc
  have hsum := p.contacts_triangle d.support
  change contacts G p.triangle d.support = degreeIn G p.center d.support +
    (degreeIn G (p.vertices 2) d.support + degreeIn G (p.vertices 3) d.support) at hsum
  have hdense := h.dense
  constructor <;> omega

lemma DensePair.other_complement {p : Paw G} {d : Quadrilateral G} (h : DensePair p d)
    (i : Fin 4) (hi : i = 2 ∨ i = 3) : QuadOn G {p.vertices 3, d i, d 0, d 1} := by
  have hm (j : Fin 4) : d j ∈ d.support := (d.mem_support _).mpr ⟨j, rfl⟩
  have hcross (j : Fin 4) : p.vertices 3 ≠ d j := fun he ↦ disjoint_left.mp h.disjoint
    ((mem_tupleSupport p.vertices _).mpr ⟨3, rfl⟩) (he.symm ▸ hm j)
  have hi0 : i ≠ 0 := by rcases hi with rfl | rfl <;> decide
  have hi1 : i ≠ 1 := by rcases hi with rfl | rfl <;> decide
  have hc0 := h.complement_clique.isClique (by simp) (by simp) (hcross 0)
  have hc1 := h.complement_clique.isClique (by simp) (by simp) (hcross 1)
  have hh := QuadOn.of_vertices (hcross i) (d.injective.ne (by decide : (0 : Fin 4) ≠ 1))
    hc0 (h.complete.isClique (hm 0) (hm i) (d.injective.ne hi0.symm))
    (h.complete.isClique (hm i) (hm 1) (d.injective.ne hi1)) hc1.symm
  change QuadOn G {p.vertices 3, d 0, d i, d 1} at hh
  rwa [insert_comm (d 0) (d i)] at hh

end Erdos577.WeightedTwelve
