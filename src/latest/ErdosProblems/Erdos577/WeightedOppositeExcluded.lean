import ErdosProblems.Erdos577.WeightedOppositeHigh
import ErdosProblems.Erdos577.PathColumnCount

/-! Global exclusion of weighted patterns (16) and (17), including the low-contact branch. -/

namespace Erdos577

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace WeightedOpposite

theorem excluded {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (seventeen : Bool) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (h : Rows seventeen p q) : False := by
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    apply disjoint_left.mpr
    intro v hv hvb
    exact (mem_sdiff.mp (c.complementPartition.block_subset hb hvb)).2 hv
  obtain ⟨a, ha, hab, hheavy⟩ := heavy_block hcard hdeg hn seventeen p hp hb q hq hd h
  let P := path seventeen p q hd h
  have hsmall := path_contacts_le_eight hc hcard hdeg hn seventeen p hp hb q hq hd h ha hab hheavy
  have hw : 3 ≤ degreeIn G (q 3) a := by omega
  have hrep := hc.opposite_exposed_universal seventeen p hp hb q hq h ha hab hw
  have hno := no_common_replacement hcard hn seventeen p hp hb q hq hd h ha hab
  have h02 (u : V) (hu : u ∈ a) : ¬(G.Adj (P.vertices 0) u ∧ G.Adj (P.vertices 2) u) := by
    rintro ⟨hu0, hu2⟩
    exact hno 5 ⟨u, hu, hu0, hu2, hrep u hu⟩
  have h03 (u : V) (hu : u ∈ a) : ¬(G.Adj (P.vertices 0) u ∧ G.Adj (P.vertices 3) u) := by
    rintro ⟨hu0, hu3⟩
    exact hno 6 ⟨u, hu, hu0, hu3, hrep u hu⟩
  have h12 (u : V) (hu : u ∈ a) : ¬(G.Adj (P.vertices 1) u ∧ G.Adj (P.vertices 2) u) := by
    rintro ⟨hu1, hu2⟩
    exact hno 4 ⟨u, hu, hu1, hu2, hrep u hu⟩
  have h13 (u : V) (hu : u ∈ a) : ¬(G.Adj (P.vertices 1) u ∧ G.Adj (P.vertices 3) u) := by
    rintro ⟨hu1, hu3⟩
    exact hno 8 ⟨u, hu, hu1, hu3, hrep u hu⟩
  have h23 (u : V) (hu : u ∈ a) : ¬(G.Adj (P.vertices 2) u ∧ G.Adj (P.vertices 3) u) := by
    rintro ⟨hu2, hu3⟩
    exact hno 7 ⟨u, hu, hu2, hu3, hrep u hu⟩
  let I := a.filter (fun u ↦ G.Adj (P.vertices 0) u ∧ G.Adj (P.vertices 1) u)
  let M := a.filter (G.Adj (q 3))
  have hbound := P.contacts_le_card_add_common a h02 h03 h12 h13 h23
  have hacard := (c.property.blocks_quad a ha).card
  have hsum : 7 ≤ I.card + M.card := by
    change contacts G P.support a ≤ a.card + I.card at hbound
    change 11 ≤ contacts G P.support a + M.card at hheavy
    omega
  have hinter : 3 ≤ (I ∩ M).card :=
    common_intersection_three a I M (filter_subset _ _) (filter_subset _ _) hacard hsum
  obtain ⟨q₂, hq₂⟩ := c.property.blocks_quad a ha
  have hrout : p.vertices 1 ∉ q₂.support := by
    rw [hq₂]
    intro hv
    have hr : p.vertices 1 ∈ c.remainder := hp ▸ (mem_tupleSupport p.vertices _).mpr ⟨1, rfl⟩
    exact (mem_sdiff.mp (c.complementPartition.block_subset ha hv)).2 hr
  have hsub : I ∩ M ⊆ q₂.support := by
    rw [hq₂]
    exact inter_subset_left.trans (filter_subset _ _)
  have hrow (u : V) (hu : u ∈ I ∩ M) : G.Adj (p.vertices 1) u :=
    (mem_filter.mp (mem_inter.mp hu).1).2.2
  obtain ⟨u, hu, hur⟩ := q₂.replace_in_three_contacts (p.vertices 1) hrout (I ∩ M)
    hsub hinter hrow
  obtain ⟨hui, hum⟩ := mem_inter.mp hu
  obtain ⟨hua, hu0, _⟩ := mem_filter.mp hui
  have huw := (mem_filter.mp hum).2
  rw [hq₂] at hur
  exact hno 9 ⟨u, hua, hu0, huw, hur⟩

end WeightedOpposite

lemma TriangleChain.Feasible.not_weighted_pattern16 {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b) :
    ¬WeightedPawBlock.Pattern16 p q :=
  fun h ↦ WeightedOpposite.excluded hc hcard hdeg hn false p hp hb q hq h

lemma TriangleChain.Feasible.not_weighted_pattern17 {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b) :
    ¬WeightedPawBlock.Pattern17 p q :=
  fun h ↦ WeightedOpposite.excluded hc hcard hdeg hn true p hp hb q hq h

end Erdos577
