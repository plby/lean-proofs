import ErdosProblems.Erdos577.JointLossScores

/-! Exact rows in configurations L28 and L31, and their complete auxiliary block. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def LossRows (p : Paw G) (d : Quadrilateral G) : Prop :=
  WeightedPawBlock.Row p d 3 15 ∧
    ((WeightedPawBlock.Row p d 1 15 ∧
      1 ≤ degreeIn G (p.vertices 2) d.support ∧
      degreeIn G (p.vertices 2) d.support ≤ 2 ∧ G.Adj (p.vertices 2) (d 0)) ∨
    (WeightedPawBlock.Row p d 1 13 ∧ WeightedPawBlock.Row p d 2 13))

lemma LossRows.third_full {p : Paw G} {d : Quadrilateral G} (h : LossRows p d) :
    degreeIn G (p.vertices 3) d.support = 4 := by
  rw [h.1.degree p d 3 15]
  decide +kernel

lemma LossRows.pair_bound {p : Paw G} {d : Quadrilateral G} (h : LossRows p d) :
    contacts G {p.center, p.vertices 2} d.support ≤ 6 := by
  rw [show contacts G {p.center, p.vertices 2} d.support =
      degreeIn G p.center d.support + degreeIn G (p.vertices 2) d.support from
    sum_pair (p.vertices.injective.ne (by decide : (1 : Fin 4) ≠ 2))]
  change degreeIn G (p.vertices 1) d.support + degreeIn G (p.vertices 2) d.support ≤ 6
  rcases h.2 with h28 | h31
  · have hr : degreeIn G (p.vertices 1) d.support = 4 := by
      rw [h28.1.degree p d 1 15]
      decide +kernel
    have hb := h28.2.2.1
    omega
  · have hr : degreeIn G (p.vertices 1) d.support = 3 := by
      rw [h31.1.degree p d 1 13]
      decide +kernel
    have hb : degreeIn G (p.vertices 2) d.support = 3 := by
      rw [h31.2.degree p d 2 13]
      decide +kernel
    omega

lemma LossRows.auxiliary_clique {p : Paw G} {d : Quadrilateral G} (h : LossRows p d) :
    G.IsNClique 4 {p.center, p.vertices 2, p.vertices 3, d 0} := by
  have hr0 : G.Adj p.center (d 0) := by
    rcases h.2 with h28 | h31
    · exact h28.1.full p d 1 0
    · exact (h31.1 0).mpr (by decide)
  have hb0 : G.Adj (p.vertices 2) (d 0) := by
    rcases h.2 with h28 | h31
    · exact h28.2.2.2
    · exact (h31.2 0).mpr (by decide)
  have hc0 := h.1.full p d 3 0
  have hcl := p.triangle_clique.insert (by
    intro v hv
    simp only [Paw.triangle, mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact hr0.symm
    · exact hb0.symm
    · exact hc0.symm)
  have he : insert (d 0) p.triangle = {p.center, p.vertices 2, p.vertices 3, d 0} := by
    ext v
    simp only [Paw.triangle, Paw.center, mem_insert, mem_singleton]
    tauto
  exact he ▸ hcl

variable [Fintype V]

theorem Core.loss_rows {c : TriangleChain G} {p : Paw G} {q d : Quadrilateral G}
    {a : Finset V} (h : Core c p q d a)
    (hloss : edgeCount G ((p.triangle ∪ a) \ {p.center, d 2, d 3}) < edgeCount G a) :
    LossRows p d := by
  obtain ⟨tag, htag, hpat⟩ := h.loss_tags hloss
  have hc : WeightedPawBlock.Row p d 3 15 := by
    intro i
    rcases htag with rfl | rfl <;>
      exact ⟨(hpat.1.2.2 3 i (by decide)).2, (hpat.1.2.2 3 i (by decide)).1⟩
  refine ⟨hc, ?_⟩
  rcases htag with rfl | rfl
  · have hr : WeightedPawBlock.Row p d 1 15 := fun i ↦
      ⟨(hpat.1.2.2 1 i (by decide)).2, (hpat.1.2.2 1 i (by decide)).1⟩
    have hb0 := (hpat.1.2.2 2 0 (by decide)).1 (by decide)
    have hpos : 1 ≤ degreeIn G (p.vertices 2) d.support := by
      have hm : d 0 ∈ d.support.filter (G.Adj (p.vertices 2)) :=
        mem_filter.mpr ⟨(d.mem_support _).mpr ⟨0, rfl⟩, hb0⟩
      exact card_pos.mpr ⟨d 0, hm⟩
    have hr4 : degreeIn G (p.vertices 1) d.support = 4 := by
      rw [hr.degree p d 1 15]
      decide +kernel
    have hc4 : degreeIn G (p.vertices 3) d.support = 4 := by
      rw [hc.degree p d 3 15]
      decide +kernel
    have hlow := (h.loss_scores hloss).2.2.1
    rw [← h.labels, p.contacts_triangle, hr4, hc4] at hlow
    exact Or.inl ⟨hr, hpos, by omega, hb0⟩
  · have hr : WeightedPawBlock.Row p d 1 13 := fun i ↦
      ⟨(hpat.1.2.2 1 i (by decide)).2, (hpat.1.2.2 1 i (by decide)).1⟩
    have hb : WeightedPawBlock.Row p d 2 13 := by
      intro i
      exact ((hpat.2.2.2.1 rfl).2 (d i) ((d.mem_support _).mpr ⟨i, rfl⟩)).trans (hr i)
    exact Or.inr ⟨hr, hb⟩

end Erdos577.JointFinal
