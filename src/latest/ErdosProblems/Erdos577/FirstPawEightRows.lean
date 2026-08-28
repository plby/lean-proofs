import ErdosProblems.Erdos577.FirstPawEightFactors
import ErdosProblems.Erdos577.FirstPawEightAlternate
import ErdosProblems.Erdos577.FirstPawEightHeavy
import ErdosProblems.Erdos577.IndexedInsertionBound

/-! All four rows are nonuniversal; both actual terminal rows have degree at most two. -/

namespace Erdos577.FirstPawEight

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
lemma no_common_pair {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern8 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (u v w : Fin 8) (hu : u ∈ weightSet)
    (hv : v ∈ weightSet.erase u) (hw : w ∈ weightSet.erase u) (hvw : v ≠ w) :
    ¬CommonReplacement G (PawEncoding.labeling p q hd v) (PawEncoding.labeling p q hd w)
      (PawEncoding.labeling p q hd u) a := by
  obtain ⟨tag, ht, hend⟩ := FactorTable.endpoint_coverage u v w hu hv hw hvw
  have hno := no_common_replacement hcard hn p hp hb q hq hd h ha hab tag
  rw [ht] at hno
  rcases hend with ⟨h0, h2⟩ | ⟨h0, h2⟩
  · rwa [h0, h2] at hno
  · rw [h0, h2] at hno
    rintro ⟨z, hz, hvz, hwz, hrep⟩
    exact hno ⟨z, hz, hwz, hvz, hrep⟩

lemma no_universal {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern8 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (hheavy : 9 ≤ contacts G (rows p q hd) a)
    (u : Fin 8) (hu : u ∈ weightSet) :
    ¬∀ z ∈ a, QuadOn G (insert (PawEncoding.labeling p q hd u) (a.erase z)) := by
  let e := PawEncoding.labeling p q hd
  have hid := contacts_image_erase_add (G := G) e weightSet u hu a
  have hfour := degreeIn_le_card G (e u) a
  rw [(c.property.blocks_quad a ha).card] at hfour
  apply no_universal_of_index_pairs (c.property.blocks_quad a ha) e weightSet u
  · change 9 ≤ contacts G (weightSet.image e) a at hheavy
    omega
  · intro v hv w hw hvw
    exact no_common_pair hcard hn p hp hb q hq hd h ha hab u v w hu hv hw hvw

theorem row_bound {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern8 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (hheavy : 9 ≤ contacts G (rows p q hd) a)
    (u : Fin 8) (hu : u ∈ weightSet) : degreeIn G (PawEncoding.labeling p q hd u) a ≤ 3 := by
  by_contra! hh
  let x := PawEncoding.labeling p q hd u
  change 3 < degreeIn G x a at hh
  have hbnd := degreeIn_le_card G x a
  rw [(c.property.blocks_quad a ha).card] at hbnd
  have hfour : degreeIn G x a = 4 := by omega
  have hfull := (degreeIn_eq_card_iff x a).mp (hfour.trans (c.property.blocks_quad a ha).card.symm)
  have hout : x ∉ a := fun hx ↦ G.irrefl (hfull x hx)
  apply no_universal hcard hn p hp hb q hq hd h ha hab hheavy u hu
  exact fun z hz ↦ (c.property.blocks_quad a ha).replace_of_degree_four hout hfour hz

theorem terminal_bound {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern8 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (hheavy : 9 ≤ contacts G (rows p q hd) a)
    (second : Bool) :
    degreeIn G (PawEncoding.labeling p q hd (if second then 3 else 0)) a ≤ 2 := by
  by_contra! hh
  obtain ⟨d, hdf, hdt, hkeep⟩ := exists_terminal hc p hp hb q hq hd h second
  apply no_universal hcard hn p hp hb q hq hd h ha hab hheavy (if second then 3 else 0)
    (by cases second <;> decide +kernel)
  intro z hz
  have hr : 3 ≤ degreeIn G d.terminal a := by rw [hdt]; exact hh
  have hrep := hdf.terminal_universal_replace (hkeep a ha hab) hr hz
  rwa [hdt] at hrep

end Erdos577.FirstPawEight
