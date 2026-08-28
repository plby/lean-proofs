import ErdosProblems.Erdos577.TripleHeavyRows
import ErdosProblems.Erdos577.TwoExposedPaws

/-! The three first-block neighbors have no edges to the ten-contact triangle core. -/

namespace Erdos577.UniversalTriple

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {q : Quadrilateral G}

theorem Configuration.high_first_columns_zero (h : Configuration c p q) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {a : Finset V} (ha : a ∈ c.blocks) (haq : a ≠ q.support)
    (hten : 10 ≤ contacts G p.triangle a) (i : Fin 4) (hi : i ≠ 3) :
    degreeIn G (q i) a = 0 := by
  by_contra hpos
  have hz : q i ∉ p.triangle := fun hh ↦ h.quad_outside i
    (p.support_eq ▸ mem_insert_of_mem hh)
  have hzb : G.Adj (q i) (p.vertices 2) := ((h.second_row i).mpr hi).symm
  let d := TwoExposed.alternatePaw p (q i) hz hzb
  have hleaf : d.leaf = q i := rfl
  have hpair : TwoExposed.PawPair p d := TwoExposed.alternatePaw_pair p (q i) hz hzb (by
    intro he
    have hout : p.leaf ∉ q.support := h.paw_outside 0
    apply hout
    rw [he]
    exact (q.mem_support _).mpr ⟨i, rfl⟩)
  have hT : d.triangle = p.triangle := hpair.triangle
  have hsupp : d.support = insert (q i) p.triangle := by rw [d.support_eq, hleaf, hT]
  obtain ⟨v, hv⟩ := c.property.blocks_quad a ha
  have hd : Disjoint d.support v.support := by
    rw [hsupp, hv]
    exact disjoint_insert_left.mpr ⟨fun hh ↦ disjoint_left.mp
      (c.property.blocks_disjoint h.block ha haq.symm)
      ((q.mem_support _).mpr ⟨i, rfl⟩) hh,
      (h.paw_disjoint_block ha).mono_left (p.support_eq ▸ subset_insert _ _)⟩
  have hcross : 11 ≤ contacts G d.support v.support := by
    rw [d.contacts_support, hleaf, hT, hv]
    omega
  rcases d.eleven_contacts v hd (by rw [hleaf, hv]; omega) hcross with hf | ⟨v', hv', hpat⟩
  · rw [hsupp, hv, insert_union] at hf
    exact h.no_triangle_core_factor hcard hn ha haq ((q.mem_support _).mpr ⟨i, rfl⟩)
      (clique_replace_of_degree_three h.complete (h.paw_outside 0) h.row_degrees.1.ge
        ((q.mem_support _).mpr ⟨i, rfl⟩)) hf
  · have he := hpat.triangle_contacts
    rw [hv', hv, hT] at he
    omega

structure HighCore (c : TriangleChain G) (p : Paw G) (q : Quadrilateral G)
    (a : Finset V) (w : V) : Prop extends Configuration c p q where
  core_block : a ∈ c.blocks
  core_ne : a ≠ q.support
  leaf_zero : degreeIn G p.leaf a = 0
  triangle_ten : contacts G p.triangle a = 10
  core_edges : 5 ≤ edgeCount G a
  first_zero : ∀ i : Fin 4, i ≠ 3 → degreeIn G (q i) a = 0
  marked : w ∈ a
  exposed_row : ∀ u ∈ a, G.Adj (q 3) u ↔ u = w

theorem Configuration.exists_high_core (h : Configuration c p q) (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) {a : Finset V} (ha : a ∈ c.blocks) (haq : a ≠ q.support)
    (hheavy : 11 ≤ contacts G (insert (q 3) p.support) a)
    (hpaw : 9 ≤ contacts G p.support a) : ∃ w, HighCore c p q a w := by
  obtain ⟨hzero, hten, hY, hedges⟩ := h.high_exact_counts hc hcard hdeg hn ha haq hheavy hpaw
  obtain ⟨w, hw⟩ := card_eq_one.mp hY
  have hwa : w ∈ a := (mem_filter.mp (hw.symm ▸ mem_singleton_self w)).1
  refine ⟨w, h, ha, haq, hzero, hten, hedges, ?_, hwa, ?_⟩
  · exact fun i hi ↦ h.high_first_columns_zero hcard hn ha haq hten.ge i hi
  · intro u hu
    have he : (u ∈ a ∧ G.Adj (q 3) u) ↔ u = w := by
      have hm := Finset.ext_iff.mp hw u
      simpa only [mem_filter, mem_singleton] using hm
    exact ⟨fun hh ↦ he.mp ⟨hu, hh⟩, fun hh ↦ (he.mpr hh).2⟩

end Erdos577.UniversalTriple
