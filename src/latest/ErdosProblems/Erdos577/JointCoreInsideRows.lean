import ErdosProblems.Erdos577.JointCoreFirstRows
import ErdosProblems.Erdos577.PawInduced

/-! Individual inside bounds: five for either exposed leaf and six for a core vertex. -/

namespace Erdos577.JointCore

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma leaf_inside_bound (p : Paw G) (q : Quadrilateral G) {a : Finset V}
    (hFQ : Disjoint p.support q.support) (hFA : Disjoint p.support a)
    (hQA : Disjoint q.support a) (hno : ¬QuadOn G p.support) (hzero : degreeIn G p.leaf a = 0) :
    degreeIn G p.leaf (p.support ∪ q.support ∪ a) ≤ 5 := by
  have hF : degreeIn G p.leaf p.support = 1 := by
    rw [p.support_eq, degreeIn_insert G p.leaf p.leaf p.leaf_not_mem_triangle,
      if_neg (G.irrefl), zero_add]
    exact p.leaf_triangle_degree_eq_one hno
  have hQ := degreeIn_le_card G p.leaf q.support
  rw [q.card_support] at hQ
  rw [degreeIn_union G p.leaf (disjoint_union_left.mpr ⟨hFA, hQA⟩),
    degreeIn_union G p.leaf hFQ, hF, hzero]
  omega

lemma core_inside_bound (p : Paw G) (q : Quadrilateral G) {a : Finset V} (ha : a.card = 4)
    (hFQ : Disjoint p.support q.support) (hFA : Disjoint p.support a)
    (hQA : Disjoint q.support a) (hx : degreeIn G p.leaf a = 0)
    (z : V) (hz : z ∈ a) (hzero : degreeIn G z q.support = 0) :
    degreeIn G z (p.support ∪ q.support ∪ a) ≤ 6 := by
  have hT : p.triangle ⊆ p.support := p.support_eq ▸ subset_insert _ _
  have hKQ : Disjoint (p.triangle ∪ a) q.support :=
    disjoint_union_left.mpr ⟨hFQ.mono_left hT, hQA.symm⟩
  have hKcard : (p.triangle ∪ a).card = 7 := by
    rw [card_union_of_disjoint (hFA.mono_left hT), p.triangle_clique.card_eq, ha]
  have hzK : z ∈ p.triangle ∪ a := mem_union_right _ hz
  have hK := degreeIn_le_card G z ((p.triangle ∪ a).erase z)
  rw [degreeIn_erase_self G z hzK, card_erase_of_mem hzK, hKcard] at hK
  have hxF : p.leaf ∈ p.support := p.support_eq ▸ mem_insert_self _ _
  have hxout : p.leaf ∉ (p.triangle ∪ a) ∪ q.support := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · rcases mem_union.mp hh with hh | hh
      · exact p.leaf_not_mem_triangle hh
      · exact disjoint_left.mp hFA hxF hh
    · exact disjoint_left.mp hFQ hxF hh
  have hzx : ¬G.Adj z p.leaf := fun hh ↦
    (degreeIn_eq_zero_iff (G := G) _ _).mp hx z hz hh.symm
  have he : p.support ∪ q.support ∪ a = insert p.leaf ((p.triangle ∪ a) ∪ q.support) := by
    rw [p.support_eq, insert_union, insert_union, union_right_comm]
  rw [he, degreeIn_insert G z p.leaf hxout, if_neg hzx, zero_add,
    degreeIn_union G z hKQ, hzero, add_zero]
  exact hK

variable [Fintype V]

theorem last_inside_bound {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (has : a ≠ s)
    (q : Quadrilateral G) (hq : q.support = s)
    (hcase : JointClaims.CaseOne p q ∨ JointClaims.CaseTwo p q) (hzero : degreeIn G (q 3) a = 0) :
    degreeIn G (q 3) (p.support ∪ q.support ∪ a) ≤ 5 := by
  have hFQ : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hFA : Disjoint p.support a := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha)
  have hQA : Disjoint q.support a := by rw [hq]; exact c.property.blocks_disjoint hs ha has.symm
  have hm : q 3 ∈ q.support := (q.mem_support _).mpr ⟨3, rfl⟩
  have hT := JointClaims.triangle_column_le_one hc hcard hn p hp hs
    (hq ▸ JointClaims.leaf_lower p q hcase) (q 3) (hq ▸ hm)
  have hF : degreeIn G (q 3) p.support ≤ 2 := by
    rw [p.support_eq, degreeIn_insert G (q 3) p.leaf p.leaf_not_mem_triangle]
    split_ifs <;> omega
  have hQ := degreeIn_le_card G (q 3) (q.support.erase (q 3))
  rw [degreeIn_erase_self G (q 3) hm, card_erase_of_mem hm, q.card_support] at hQ
  rw [degreeIn_union G (q 3) (disjoint_union_left.mpr ⟨hFA, hQA⟩),
    degreeIn_union G (q 3) hFQ, hzero]
  omega

end Erdos577.JointCore
