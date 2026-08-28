import ErdosProblems.Erdos577.FirstPawFourHeavy
import ErdosProblems.Erdos577.FirstPawFourPaths
import ErdosProblems.Erdos577.NeighborPairPigeonhole
import ErdosProblems.Erdos577.PawTerminalExchange
import ErdosProblems.Erdos577.TerminalReplacements

/-! The outside block's leaf row has at most two contacts;
the five rows then total at least eleven. -/

namespace Erdos577.FirstPawFour

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma weight_vertexSet (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (a : Finset V) : weight p q a = contacts G (vertexSet p q) a + degreeIn G p.leaf a := by
  rw [← vertexSet_image p q hd,
    contacts_image_left G _ (PawEncoding.labeling p q hd) (PawEncoding.labeling p q hd).injective]
  norm_num [PairTable.vertexSet]
  change weight p q a = degreeIn G p.leaf a +
    (degreeIn G (p.vertices 2) a + (degreeIn G (p.vertices 3) a +
    (degreeIn G (q 1) a + degreeIn G (q 3) a))) + degreeIn G p.leaf a
  unfold weight
  omega

variable [Fintype V]

lemma no_universal_of_five {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern4 p q)
    (hheavy : 9 ≤ contacts G p.support q.support)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (u : V) (hu : u ∈ terminalSet p q)
    (hfive : 5 ≤ contacts G ((vertexSet p q).erase u) a) :
    ¬∀ z ∈ a, QuadOn G (insert u (a.erase z)) := by
  intro hrep
  obtain ⟨z, hz, v, hv, w, hw, hvw, hvz, hwz⟩ :=
    exists_common_pair_of_contacts (G := G) ((vertexSet p q).erase u) a
      (by rw [(c.property.blocks_quad a ha).card]; omega)
  exact no_common_replacement hcard hn p hp hb q hq hd h hheavy ha hab u v w hu hv hw hvw
    ⟨z, hz, hvz, hwz, hrep z hz⟩

theorem leaf_bound {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern4 p q)
    (hheavy : 9 ≤ contacts G p.support q.support)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (hweight : 13 ≤ weight p q a) :
    degreeIn G p.leaf a ≤ 2 ∧ 11 ≤ contacts G (vertexSet p q) a := by
  have hleaf4 := degreeIn_le_card G p.leaf a
  rw [(c.property.blocks_quad a ha).card] at hleaf4
  have he := weight_vertexSet p q hd a
  have hsmall : degreeIn G p.leaf a ≤ 2 := by
    by_contra! hlarge
    have hm : p.leaf ∈ vertexSet p q := mem_insert_self _ _
    have herase : contacts G ((vertexSet p q).erase p.leaf) a + degreeIn G p.leaf a =
        contacts G (vertexSet p q) a := sum_erase_add _ _ hm
    have hfive : 5 ≤ contacts G ((vertexSet p q).erase p.leaf) a := by omega
    have hno := no_universal_of_five hcard hn p hp hb q hq hd h hheavy ha hab p.leaf
      (mem_insert_self _ _) hfive
    exact hno (fun z hz ↦ (hc.presentPaw_feasible p hp).terminal_universal_replace ha hlarge hz)
  exact ⟨hsmall, by omega⟩

end Erdos577.FirstPawFour
