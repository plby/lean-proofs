import ErdosProblems.Erdos577.JointFinalCore

/-! Exact four-row support and averaging; only three of these rows share the original center. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def arms (p : Paw G) (q d : Quadrilateral G) : Finset V := {p.leaf, q 3, d 2, d 3}

lemma Core.arms_card {c : TriangleChain G} {p : Paw G} {q d : Quadrilateral G} {a : Finset V}
    (h : Core c p q d a) : (arms p q d).card = 4 := by
  obtain ⟨_, hs, ha, has, _, _, _⟩ := h.config
  exact JointBridge.arms_card p (q 3) (d 2) (d 3) (h.paw_disjoint ha) (h.paw_disjoint hs)
    (c.property.blocks_disjoint ha hs has) ((q.mem_support _).mpr ⟨3, rfl⟩)
    (h.mem 2) (h.mem 3) (d.injective.ne (by decide))

lemma Core.arms_subset {c : TriangleChain G} {p : Paw G} {q d : Quadrilateral G} {a : Finset V}
    (h : Core c p q d a) : arms p q d ⊆ p.support ∪ q.support ∪ a := by
  exact insert_subset (mem_union_left _ (mem_union_left _ (p.support_eq ▸ mem_insert_self _ _)))
    (insert_subset (mem_union_left _ (mem_union_right _ ((q.mem_support _).mpr ⟨3, rfl⟩)))
      (insert_subset (mem_union_right _ (h.mem 2))
        (singleton_subset_iff.mpr (mem_union_right _ (h.mem 3)))))

lemma Core.arms_disjoint {c : TriangleChain G} {p : Paw G} {q d : Quadrilateral G} {a j : Finset V}
    (h : Core c p q d a) (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hja : j ≠ a) :
    Disjoint (arms p q d) j := by
  have hfull : Disjoint (p.support ∪ q.support ∪ a) j :=
    disjoint_union_left.mpr ⟨disjoint_union_left.mpr ⟨h.paw_disjoint hj,
      c.property.blocks_disjoint h.config.2.1 hj hjq.symm⟩,
      c.property.blocks_disjoint h.config.2.2.1 hj hja.symm⟩
  exact hfull.mono_left h.arms_subset

lemma Core.arms_contacts {c : TriangleChain G} {p : Paw G} {q d : Quadrilateral G} {a : Finset V}
    (h : Core c p q d a) (s : Finset V) : contacts G (arms p q d) s =
    degreeIn G p.leaf s + degreeIn G (q 3) s + degreeIn G (d 2) s + degreeIn G (d 3) s := by
  obtain ⟨hxy, hx1, hx2, hy1, hy2, h12⟩ := JointCore.four_distinct h.arms_card
  rw [arms, contacts, sum_insert (by simp [hxy, hx1, hx2]),
    sum_insert (by simp [hy1, hy2]), sum_insert (by simp [h12]), sum_singleton]
  omega

theorem Core.exists_heavy_block {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u)
    {p : Paw G} {q d : Quadrilateral G} {a : Finset V} (h : Core c p q d a) :
    ∃ j ∈ c.blocks, j ≠ q.support ∧ j ≠ a ∧ 9 ≤ contacts G (arms p q d) j := by
  obtain ⟨hp, hs, ha, has, _, _, _⟩ := h.config
  have hsel : ({q.support, a} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset hs (singleton_subset_iff.mpr ha)
  have he : c.remainder ∪ ({q.support, a} : Finset (Finset V)).biUnion id =
      p.support ∪ q.support ∪ a := by
    simp only [biUnion_insert, singleton_biUnion, id_eq, ← hp, union_assoc]
  have hr : ({p.leaf, d 2, d 3, q 3} : Finset V) = arms p q d := by
    ext v
    simp only [arms, mem_insert, mem_singleton]
    tauto
  have hinside := h.inside_four
  rw [hr, ← he] at hinside
  obtain ⟨j, hj, hjn, hnine⟩ := JointFirst.exists_nine_outside_two hcard hdeg {q.support, a}
    hsel (card_pair_eq_two_iff.mpr has.symm) (arms p q d) h.arms_card hinside
  simp only [mem_insert, mem_singleton, not_or] at hjn
  exact ⟨j, hj, hjn.1, hjn.2, hnine⟩

end Erdos577.JointFinal
