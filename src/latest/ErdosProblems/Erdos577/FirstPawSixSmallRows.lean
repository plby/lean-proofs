import ErdosProblems.Erdos577.FirstPawSixSmallFactors
import ErdosProblems.Erdos577.FirstPawSixSmallHeavy
import ErdosProblems.Erdos577.FirstPawSixTerminals
import ErdosProblems.Erdos577.IndexedInsertionBound
import ErdosProblems.Erdos577.TerminalReplacements

/-! The two alternate terminal rows on the heavy outside block are both at most two. -/

namespace Erdos577.FirstPawSix.SmallCases

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma no_universal {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (hdiag : PawBlock.OnlyFirst q) (variant : Bool)
    (hrows : PawBlock.ExactRows p q (caseRows (caseTag variant)))
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (hheavy : 9 ≤ contacts G (rows p q hd) a)
    (u : Fin 8) (hu : u ∈ terminalSet) :
    ¬∀ z ∈ a, QuadOn G (insert (PawEncoding.labeling p q hd u) (a.erase z)) := by
  let e := PawEncoding.labeling p q hd
  have huR : u ∈ weightSet := (by decide +kernel : terminalSet ⊆ weightSet) hu
  have hsplit := contacts_image_erase_add (G := G) e weightSet u huR a
  change contacts G ((weightSet.erase u).image e) a + degreeIn G (e u) a =
    contacts G (rows p q hd) a at hsplit
  have hfour := degreeIn_le_card G (e u) a
  rw [(c.property.blocks_quad a ha).card] at hfour
  apply no_universal_of_index_pairs (c.property.blocks_quad a ha) e weightSet u (by omega)
  intro v hv w hw hvw
  exact no_common_pair hcard hn p hp hb q hq hd hdiag variant hrows ha hab u v w hu hv hw hvw

theorem terminal_bound {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (hdiag : PawBlock.OnlyFirst q) (variant : Bool)
    (hrows : PawBlock.ExactRows p q (caseRows (caseTag variant)))
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (hheavy : 9 ≤ contacts G (rows p q hd) a)
    (second : Bool) :
    degreeIn G (PawEncoding.labeling p q hd (if second then 3 else 7)) a ≤ 2 := by
  by_contra! hlarge
  obtain ⟨d, hdf, hdt, _, hkeep⟩ :=
    FirstPawSix.exists_alternate hc p hp hb q hq hd hdiag (index variant) hrows second
  apply no_universal hcard hn p hp hb q hq hd hdiag variant hrows ha hab hheavy
    (if second then 3 else 7) (by cases second <;> decide +kernel)
  intro z hz
  have hr : 3 ≤ degreeIn G d.terminal a := by rw [hdt]; exact hlarge
  have hrep := hdf.terminal_universal_replace (hkeep a ha hab) hr hz
  rw [hdt] at hrep
  exact hrep

end Erdos577.FirstPawSix.SmallCases
