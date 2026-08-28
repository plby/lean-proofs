import ErdosProblems.Erdos577.TripleTriangleExchange

/-! The actual seven-vertex core and the inside budgets for both forbidden-triangle cases. -/

namespace Erdos577.UniversalTriple

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {q : Quadrilateral G} {a : Finset V} {w : V}

lemma HighCore.core_card (h : HighCore c p q a w) : (p.triangle ∪ a).card = 7 := by
  rw [card_union_of_disjoint ((h.toConfiguration.paw_disjoint_block h.core_block).mono_left
      (p.support_eq ▸ subset_insert _ _)), p.triangle_clique.card_eq,
    (c.property.blocks_quad a h.core_block).card]

lemma HighCore.core_disjoint_first (h : HighCore c p q a w) :
    Disjoint (p.triangle ∪ a) q.support :=
  disjoint_union_left.mpr ⟨h.toConfiguration.disjoint.mono_left
    (p.support_eq ▸ subset_insert _ _), c.property.blocks_disjoint h.core_block h.block h.core_ne⟩

lemma HighCore.leaf_outside_core (h : HighCore c p q a w) : p.leaf ∉ p.triangle ∪ a := by
  rw [mem_union, not_or]
  exact ⟨p.leaf_not_mem_triangle, fun hh ↦ disjoint_left.mp
    (h.toConfiguration.paw_disjoint_block h.core_block) (p.support_eq ▸ mem_insert_self _ _) hh⟩

lemma HighCore.exposed_outside_core (h : HighCore c p q a w) : q 3 ∉ p.triangle ∪ a :=
  fun hh ↦ disjoint_left.mp h.core_disjoint_first hh ((q.mem_support _).mpr ⟨3, rfl⟩)

lemma HighCore.exposed_degree (h : HighCore c p q a w) : degreeIn G (q 3) a = 1 := by
  have he : a.filter (G.Adj (q 3)) = {w} := by
    ext u
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hu, hadj⟩
      exact (h.exposed_row u hu).mp hadj
    · intro hu
      subst u
      exact ⟨h.marked, (h.exposed_row w h.marked).mpr rfl⟩
  rw [degreeIn, he, card_singleton]

lemma HighCore.core_first_degree (h : HighCore c p q a w) {v : V}
    (hv : v ∈ p.triangle ∪ a) (hvb : v ≠ p.vertices 2) : degreeIn G v q.support ≤ 1 := by
  rcases mem_union.mp hv with hv | hv
  · simp only [Paw.triangle, mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · change degreeIn G p.center q.support ≤ 1
      rw [h.toConfiguration.row_degrees.2.2.2]
      split_ifs <;> omega
    · exact False.elim (hvb rfl)
    · rw [h.toConfiguration.row_degrees.2.2.1]
      decide
  · have hno (i : Fin 4) (hi : i ≠ 3) : ¬G.Adj v (q i) := by
      intro he
      exact (degreeIn_eq_zero_iff _ _).mp (h.first_zero i hi) v hv he.symm
    rw [Quadrilateral.support, degreeIn_image G v univ q q.injective, Fin.sum_univ_four,
      if_neg (hno 0 (by decide)), if_neg (hno 1 (by decide)), if_neg (hno 2 (by decide))]
    split_ifs <;> omega

lemma HighCore.leaf_core_row (h : HighCore c p q a w) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k) {v : V}
    (hv : v ∈ p.triangle ∪ a) : G.Adj p.leaf v ↔ v = p.center := by
  have hdegree : degreeIn G p.leaf (p.triangle ∪ a) = 1 := by
    rw [degreeIn_union G _ ((h.toConfiguration.paw_disjoint_block h.core_block).mono_left
        (p.support_eq ▸ subset_insert _ _)), h.leaf_zero, add_zero]
    exact p.leaf_triangle_degree_eq_one (by rw [h.paw]; exact c.no_quad_remainder hcard hn)
  constructor
  · intro he
    exact card_le_one.mp hdegree.le v (mem_filter.mpr ⟨hv, he⟩) p.center
      (mem_filter.mpr ⟨mem_union_left _ p.center_mem_triangle, p.pendant⟩)
  · intro he
    rw [he]
    exact p.pendant

lemma HighCore.leaf_inside_degree (h : HighCore c p q a w) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k) :
    degreeIn G p.leaf (p.support ∪ q.support ∪ a) = 4 := by
  have hF : degreeIn G p.leaf p.support = 1 := by
    rw [p.support_eq, degreeIn_insert G _ _ p.leaf_not_mem_triangle,
      if_neg G.irrefl, zero_add]
    exact p.leaf_triangle_degree_eq_one (by rw [h.paw]; exact c.no_quad_remainder hcard hn)
  have hd : Disjoint (p.support ∪ q.support) a := disjoint_union_left.mpr
    ⟨h.toConfiguration.paw_disjoint_block h.core_block,
      c.property.blocks_disjoint h.block h.core_block h.core_ne.symm⟩
  rw [degreeIn_union G _ hd, degreeIn_union G _ h.toConfiguration.disjoint,
    hF, h.toConfiguration.row_degrees.1, h.leaf_zero]

lemma HighCore.exposed_inside_degree (h : HighCore c p q a w) :
    degreeIn G (q 3) (p.support ∪ q.support ∪ a) ≤ 5 := by
  have hQ : degreeIn G (q 3) q.support = 3 := by
    rw [degreeIn_clique G h.complete.isClique ((q.mem_support _).mpr ⟨3, rfl⟩), q.card_support]
  have hd : Disjoint (p.support ∪ q.support) a := disjoint_union_left.mpr
    ⟨h.toConfiguration.paw_disjoint_block h.core_block,
      c.property.blocks_disjoint h.block h.core_block h.core_ne.symm⟩
  rw [degreeIn_union G _ hd, degreeIn_union G _ h.toConfiguration.disjoint,
    h.toConfiguration.exposed_paw_degree, hQ, h.exposed_degree]
  split_ifs <;> omega

lemma HighCore.core_inside_degree (h : HighCore c p q a w) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k) {v : V}
    (hv : v ∈ p.triangle ∪ a) (hvr : v ≠ p.center) (hvb : v ≠ p.vertices 2) :
    degreeIn G v (p.support ∪ q.support ∪ a) ≤ 7 := by
  have hno : ¬G.Adj v p.leaf := fun he ↦ hvr ((h.leaf_core_row hcard hn hv).mp he.symm)
  have hXout : p.leaf ∉ (p.triangle ∪ a) ∪ q.support := by
    rw [mem_union, not_or]
    exact ⟨h.leaf_outside_core, h.toConfiguration.paw_outside 0⟩
  have he : p.support ∪ q.support ∪ a = insert p.leaf ((p.triangle ∪ a) ∪ q.support) := by
    rw [p.support_eq]
    ext u
    simp only [mem_insert, mem_union]
    tauto
  have hK := degreeIn_le_card G v ((p.triangle ∪ a).erase v)
  rw [degreeIn_erase_self G v hv, card_erase_of_mem hv, h.core_card] at hK
  have hQ := h.core_first_degree hv hvb
  rw [he, degreeIn_insert G _ _ hXout, if_neg hno, zero_add,
    degreeIn_union G _ h.core_disjoint_first]
  omega

end Erdos577.UniversalTriple
