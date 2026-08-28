import ErdosProblems.Erdos577.JointFirstSwap

/-! The four arms in CaseI and their exact cardinality and inside budget. -/

namespace Erdos577.JointFirst

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def arms (p : Paw G) (q : Quadrilateral G) (z1 z2 : V) : Finset V := {p.leaf, q 1, z1, z2}

lemma arms_card (p : Paw G) (q : Quadrilateral G) (hFQ : Disjoint p.support q.support)
    (z1 z2 : V) (h1F : z1 ∉ p.support) (h2F : z2 ∉ p.support)
    (h1Q : z1 ∉ q.support) (h2Q : z2 ∉ q.support) (hne : z1 ≠ z2) :
    (arms p q z1 z2).card = 4 := by
  have hxF : p.leaf ∈ p.support := p.support_eq ▸ mem_insert_self _ _
  have hvQ : q 1 ∈ q.support := (q.mem_support _).mpr ⟨1, rfl⟩
  apply card_eq_four.mpr
  exact ⟨p.leaf, q 1, z1, z2,
    (fun he ↦ disjoint_left.mp hFQ hxF (he.symm ▸ hvQ)),
    (fun he ↦ h1F (he ▸ hxF)), (fun he ↦ h2F (he ▸ hxF)),
    (fun he ↦ h1Q (he ▸ hvQ)), (fun he ↦ h2Q (he ▸ hvQ)), hne, rfl⟩

lemma arms_subset (p : Paw G) (q : Quadrilateral G) {a : Finset V} {z1 z2 : V}
    (h1 : z1 ∈ a) (h2 : z2 ∈ a) : arms p q z1 z2 ⊆ p.support ∪ q.support ∪ a := by
  have hxF : p.leaf ∈ p.support := p.support_eq ▸ mem_insert_self _ _
  have hvQ : q 1 ∈ q.support := (q.mem_support _).mpr ⟨1, rfl⟩
  exact insert_subset (mem_union_left _ (mem_union_left _ hxF))
    (insert_subset (mem_union_left _ (mem_union_right _ hvQ))
      (insert_subset (mem_union_right _ h1) (singleton_subset_iff.mpr (mem_union_right _ h2))))

lemma arms_center (p : Paw G) (q : Quadrilateral G) {z1 z2 : V}
    (hv : G.Adj p.center (q 1)) (h1 : G.Adj p.center z1) (h2 : G.Adj p.center z2) :
    ∀ u ∈ arms p q z1 z2, G.Adj p.center u := by
  intro u hu
  simp only [arms, mem_insert, mem_singleton] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · exact p.pendant.symm
  · exact hv
  · exact h1
  · exact h2

variable [DecidableRel G.Adj]

lemma inside_of_first_column (p : Paw G) (q : Quadrilateral G) {a : Finset V}
    (hFQ : Disjoint p.support q.support) (hFA : Disjoint p.support a)
    (hAQ : Disjoint a q.support) (u : V) (hu : u ∈ q.support)
    (hcol : degreeIn G u (p.triangle ∪ a) ≤ 1) :
    degreeIn G u (p.support ∪ q.support ∪ a) ≤ 5 := by
  have hT : p.triangle ⊆ p.support := p.support_eq ▸ subset_insert _ _
  have hKQ : Disjoint (p.triangle ∪ a) q.support :=
    disjoint_union_left.mpr ⟨hFQ.mono_left hT, hAQ⟩
  have hxF : p.leaf ∈ p.support := p.support_eq ▸ mem_insert_self _ _
  have hxout : p.leaf ∉ (p.triangle ∪ a) ∪ q.support := by
    intro h
    rcases mem_union.mp h with h | h
    · rcases mem_union.mp h with h | h
      · exact p.leaf_not_mem_triangle h
      · exact disjoint_left.mp hFA hxF h
    · exact disjoint_left.mp hFQ hxF h
  have hQ := degreeIn_le_card G u (q.support.erase u)
  rw [degreeIn_erase_self G u hu, card_erase_of_mem hu, q.card_support] at hQ
  have he : p.support ∪ q.support ∪ a = insert p.leaf ((p.triangle ∪ a) ∪ q.support) := by
    rw [p.support_eq, insert_union, insert_union, union_right_comm]
  rw [he, degreeIn_insert G u p.leaf hxout, degreeIn_union G u hKQ]
  split_ifs <;> omega

variable [Fintype V]

theorem first_inside_bound {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (has : a ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (hcase : JointClaims.CaseOne p q)
    (houter : 7 ≤ degreeIn G p.center a + degreeIn G (p.vertices 3) a)
    (hweighted : 13 ≤ degreeIn G (p.vertices 3) a + contacts G p.triangle a) :
    degreeIn G (q 1) (p.support ∪ q.support ∪ a) ≤ 5 := by
  have hFQ : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hFA : Disjoint p.support a := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha)
  have hAQ : Disjoint a q.support := by rw [hq]; exact c.property.blocks_disjoint ha hs has
  have hvQ : q 1 ∈ q.support := (q.mem_support _).mpr ⟨1, rfl⟩
  exact inside_of_first_column p q hFQ hFA hAQ (q 1) hvQ
    (JointCore.first_core_column hc hcard hn p hp hs ha has q hq (Or.inl hcase)
      houter hweighted (q 1) (hq ▸ hvQ))

theorem arms_inside_bound {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (has : a ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (hcase : JointClaims.CaseOne p q)
    (houter : 7 ≤ degreeIn G p.center a + degreeIn G (p.vertices 3) a)
    (hweighted : 13 ≤ degreeIn G (p.vertices 3) a + contacts G p.triangle a)
    (z1 z2 : V) (h17 : contacts G {p.leaf, z1, z2} (p.support ∪ q.support ∪ a) ≤ 17) :
    contacts G (arms p q z1 z2) (p.support ∪ q.support ∪ a) ≤ 22 := by
  have hv := first_inside_bound hc hcard hn p hp hs ha has q hq hcase houter hweighted
  have hb := JointCore.contacts_insert_upper (G := G) (q 1) {p.leaf, z1, z2}
    (p.support ∪ q.support ∪ a)
  have he : insert (q 1) ({p.leaf, z1, z2} : Finset V) = arms p q z1 z2 := by
    rw [insert_comm]
    rfl
  rw [he] at hb
  omega

end Erdos577.JointFirst
