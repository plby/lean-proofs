import ErdosProblems.Erdos577.WeightedOppositeTerminal
import ErdosProblems.Erdos577.LocalChainSupport
import ErdosProblems.Erdos577.OutsideCoreCount

/-! The heavy outside block and the universally replaceable exposed vertex in (16)/(17). -/

namespace Erdos577

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace WeightedOpposite

omit [Fintype V] in
lemma five_contacts_eq (seventeen : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Rows seventeen p q) (a : Finset V) :
    contacts G (fiveSet.image (PawEncoding.labeling p q hd)) a =
      contacts G (path seventeen p q hd h).support a + degreeIn G (q 3) a := by
  let e := PawEncoding.labeling p q hd
  have hinj : Function.Injective (e : Fin 8 → V) := e.injective
  have hs : ({7} : Finset (Fin 8)).image e = {q 3} := by
    rw [image_singleton]
    rfl
  have he : fiveSet.image e = (path seventeen p q hd h).support ∪ {q 3} := by
    rw [path_support_image, ← hs]
    change fiveSet.image e = pathSet.image e ∪ ({7} : Finset (Fin 8)).image e
    rw [← image_union]
    congr 1
  have hdis : Disjoint (path seventeen p q hd h).support ({q 3} : Finset V) := by
    rw [path_support_image, ← hs]
    change Disjoint (pathSet.image e) (({7} : Finset (Fin 8)).image e)
    rw [disjoint_image hinj]
    decide +kernel
  rw [he, contacts_union_left G hdis, contacts_singleton_left]

theorem heavy_block {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (seventeen : Bool) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : Rows seventeen p q) :
    ∃ a ∈ c.blocks, a ≠ b ∧
      11 ≤ contacts G (path seventeen p q hd h).support a + degreeIn G (q 3) a := by
  let e := PawEncoding.labeling p q hd
  have hinj : Function.Injective (e : Fin 8 → V) := e.injective
  have hlocal : ¬LocalFactor G (p.support ∪ q.support) := by
    rw [hp, hq]
    exact c.no_local_factor hcard hn hb
  have hleaf := c.paw_nonadjacent hcard hn p hp
  have hcenter := h.center_absent seventeen p q hd hlocal
  have himage : fiveSet.image e = {p.vertices 0, p.vertices 1, p.vertices 3, q 1, q 3} := by
    simp only [fiveSet, image_insert, image_singleton]
    rfl
  have hfive : (fiveSet.image e).card = 5 := by
    rw [card_image_of_injective _ hinj]
    decide +kernel
  have hinside : contacts G (fiveSet.image e) (c.remainder ∪ b) ≤ 19 := by
    rw [himage, ← hp, ← hq]
    exact h.inside_bound seventeen p q hd hleaf hcenter
  obtain ⟨a, ha, hab, hh⟩ := c.exists_eleven_contact_outside_core
    hcard hdeg hb (fiveSet.image e) hfive hinside
  rw [five_contacts_eq seventeen p q hd h] at hh
  exact ⟨a, ha, hab, hh⟩

end WeightedOpposite

theorem TriangleChain.Feasible.opposite_exposed_universal {c : TriangleChain G} (hc : c.Feasible)
    (seventeen : Bool) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (h : WeightedOpposite.Rows seventeen p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (hrow : 3 ≤ degreeIn G (q 3) a) (u : V) (hu : u ∈ a) :
    QuadOn G (insert (q 3) (a.erase u)) := by
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    apply disjoint_left.mpr
    intro v hv hvb
    exact (mem_sdiff.mp (c.complementPartition.block_subset hb hvb)).2 hv
  let d := (WeightedOpposite.terminalLocalChain seventeen p q hd h).withSupport
    (show p.support ∪ q.support = c.remainder ∪ b by rw [hp, hq])
  let c' := c.replaceBlock b hb d
  have hc' : c'.Feasible := hc.replaceBlock_feasible hb d (by
    change edgeCount G (WeightedOpposite.terminalLocalChain seventeen p q hd h).block = _
    rw [WeightedOpposite.terminalLocalChain_score, hq])
  have ha' : a ∈ c'.blocks := mem_union_left _ (mem_erase.mpr ⟨hab, ha⟩)
  exact hc'.terminal_universal_replace ha' hrow hu

end Erdos577
