import ErdosProblems.Erdos577.FullLeafSparseCoreChoice

/-! Replacing the actual core triangle preserves feasibility, both scores, and the original leaf. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

theorem Configuration.center_rows_zero_of_four (h : Configuration c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    (hX : degreeIn G p.leaf j = 4)
    (hfour : contacts G (insert (p.vertices 3) a) j = 4) :
    degreeIn G p.center j = 0 ∧ degreeIn G (p.vertices 2) j = 0 := by
  have hcols (v : V) (hv : v ∈ j) : degreeIn G v (p.triangle ∪ a) ≤ 1 :=
    h.core_degree_of_first_replacement hcard hn (mem_insert_self _ _) hj hjs hja hv
      (h.first_universal_replacements (mem_insert_self _ _) hj hjs (by omega) v hv)
  have hbound : contacts G j (p.triangle ∪ a) ≤ 4 := by
    calc
      contacts G j (p.triangle ∪ a) ≤ ∑ _ ∈ j, (1 : ℕ) := sum_le_sum hcols
      _ = 4 := by simp only [sum_const, smul_eq_mul,
        (c.property.blocks_quad j hj).card, mul_one]
  have hrb : p.center ≠ p.vertices 2 := p.vertices.injective.ne (by decide : (1 : Fin 4) ≠ 2)
  have hrout : p.center ∉ insert (p.vertices 2) (insert (p.vertices 3) a) := by
    rw [mem_insert, not_or]
    exact ⟨hrb, fun hv ↦ (h.second_avoids hv).2.1 rfl⟩
  have hbout : p.vertices 2 ∉ insert (p.vertices 3) a :=
    fun hv ↦ (h.second_avoids hv).2.2 rfl
  have hK : p.triangle ∪ a = insert p.center (insert (p.vertices 2) (insert (p.vertices 3) a)) := by
    ext v
    simp only [Paw.triangle, Paw.center, mem_union, mem_insert, mem_singleton]
    tauto
  rw [contacts_comm G j (p.triangle ∪ a), hK, contacts,
    sum_insert hrout, sum_insert hbout] at hbound
  change degreeIn G p.center j + (degreeIn G (p.vertices 2) j +
    contacts G (insert (p.vertices 3) a) j) ≤ 4 at hbound
  constructor <;> omega

theorem Configuration.core_triangle_exchange (h : Configuration c p s a y)
    {j : Finset V} (hj : j ∈ c.blocks) (hja : j ≠ a)
    (hX : degreeIn G p.leaf j = 4)
    {z : V} (hz : z ∈ insert (p.vertices 3) a) (hrz : G.Adj p.center z)
    (hzb : G.Adj z (p.vertices 2))
    (hrem : G.IsNClique 4 ((p.triangle ∪ a) \ {p.center, z, p.vertices 2}))
    (hzpos : 0 < degreeIn G z j) :
    ∃ (e : TriangleChain G) (q : Paw G) (w : V),
      Configuration e q j ((p.triangle ∪ a) \ {p.center, z, p.vertices 2}) w ∧
      q.leaf = p.leaf ∧ q.vertices 3 = p.vertices 2 ∧
      e.edgeScore = c.edgeScore ∧ e.completeScore = c.completeScore := by
  have hzK := h.second_five_subset hz
  have hrK : p.center ∈ p.triangle ∪ a := mem_union_left _ p.center_mem_triangle
  have hbK : p.vertices 2 ∈ p.triangle ∪ a := mem_union_left _ (by simp [Paw.triangle])
  have hXout : p.leaf ∉ p.triangle ∪ a := fun hv ↦
    disjoint_left.mp h.five_disjoint_core (mem_insert_self _ _) hv
  let q := Paw.ofVertices p.leaf p.center z (p.vertices 2)
    (fun he ↦ hXout (he ▸ hrK)) (fun he ↦ hXout (he ▸ hzK))
    (fun he ↦ hXout (he ▸ hbK)) hrz.ne p.edge12.ne hzb.ne p.pendant hrz p.edge12 hzb
  have htri : q.triangle = {p.center, z, p.vertices 2} := rfl
  have htSub : q.triangle ⊆ p.triangle ∪ a := by
    rw [htri]
    exact insert_subset hrK (insert_subset hzK (singleton_subset_iff.mpr hbK))
  let a' := (p.triangle ∪ a) \ q.triangle
  have ha' : G.IsNClique 4 a' := by simpa only [a', htri] using hrem
  have hd : Disjoint q.triangle a' := disjoint_sdiff_self_right
  have hcover : q.triangle ∪ a' = p.triangle ∪ a := union_sdiff_of_subset htSub
  let loc : LocalChain G (c.remainder ∪ a) := {
    terminal := p.leaf
    triangle := q.triangle
    block := a'
    triangle_clique := q.triangle_clique
    terminal_not_mem := q.leaf_not_mem_triangle
    quad := QuadOn.of_clique ha'.card_eq ha'.isClique
    disjoint := disjoint_insert_left.mpr
      ⟨fun hv ↦ hXout (mem_sdiff.mp hv).1, hd⟩
    cover := by rw [insert_union, hcover, ← h.paw, p.support_eq, insert_union] }
  have hscore : edgeCount G loc.block = edgeCount G a := by
    change edgeCount G a' = edgeCount G a
    rw [edgeCount_clique ha'.isClique, edgeCount_clique h.core_clique.isClique,
      ha'.card_eq, h.core_clique.card_eq]
  let e := c.replaceBlock a h.core loc
  have he : e.Feasible := h.feasible.replaceBlock_feasible h.core loc hscore
  have hscores := c.replaceBlock_scores_eq h.core loc hscore
  have hj' : j ∈ e.blocks := mem_union_left _ (mem_erase.mpr ⟨hja, hj⟩)
  have ha'mem : a' ∈ e.blocks := mem_union_right _ (mem_singleton_self _)
  have ha'ne : a' ≠ j := by
    obtain ⟨v, hv⟩ := card_pos.mp (show 0 < a'.card by rw [ha'.card_eq]; decide)
    intro hsame
    exact disjoint_left.mp (h.core_disjoint_block hj hja) (mem_sdiff.mp hv).1 (hsame ▸ hv)
  have hdense : 11 ≤ contacts G q.triangle a' := by
    have hta : Disjoint p.triangle a :=
      (h.paw_disjoint h.core).mono_left (p.support_eq ▸ subset_insert _ _)
    have htwenty := (dense_triangle_clique_edges p.triangle_clique h.core_clique hta h.dense).1
    rw [← hcover, edgeCount_union G hd, edgeCount_clique q.triangle_clique.isClique,
      edgeCount_clique ha'.isClique, q.triangle_clique.card_eq, ha'.card_eq] at htwenty
    norm_num only [Nat.choose] at htwenty
    omega
  obtain ⟨w, hw⟩ := card_pos.mp hzpos
  obtain ⟨hw, hzw⟩ := mem_filter.mp hw
  refine ⟨e, q, w, ?_, rfl, rfl, hscores.1, hscores.2⟩
  change Configuration e q j a' w
  exact ⟨he, q.support_eq, hj', ha'mem, ha'ne, hX, hw, hzw, hdense⟩

end Erdos577.FullLeafCore
