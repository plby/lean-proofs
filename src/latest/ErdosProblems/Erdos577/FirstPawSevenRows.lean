import ErdosProblems.Erdos577.FirstPawSevenFactors
import ErdosProblems.Erdos577.FirstPawSevenAlternate
import ErdosProblems.Erdos577.FirstPawSevenHeavy
import ErdosProblems.Erdos577.NeighborPairPigeonhole
import ErdosProblems.Erdos577.TerminalReplacements

/-! Both feasible terminal rows on the outside heavy block have degree at most two. -/

namespace Erdos577.FirstPawSeven

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma no_universal {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern7 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (hheavy : 9 ≤ contacts G (rows p q hd) a)
    (u : Fin 8) (hu : u ∈ terminalSet) :
    ¬∀ z ∈ a, QuadOn G (insert (PawEncoding.labeling p q hd u) (a.erase z)) := by
  intro hrep
  let e := PawEncoding.labeling p q hd
  have huR : u ∈ weightSet := (by decide +kernel : terminalSet ⊆ weightSet) hu
  have hum : e u ∈ rows p q hd := mem_image.mpr ⟨u, huR, rfl⟩
  have he : contacts G ((rows p q hd).erase (e u)) a + degreeIn G (e u) a =
      contacts G (rows p q hd) a := sum_erase_add _ _ hum
  have hfour := degreeIn_le_card G (e u) a
  rw [(c.property.blocks_quad a ha).card] at hfour
  obtain ⟨z, hz, v, hv, w, hw, hvw, hvz, hwz⟩ :=
    exists_common_pair_of_contacts (G := G) ((rows p q hd).erase (e u)) a
      (by rw [(c.property.blocks_quad a ha).card]; omega)
  have hinj : Function.Injective (e : Fin 8 → V) := e.injective
  change v ∈ (weightSet.image e).erase (e u) at hv
  change w ∈ (weightSet.image e).erase (e u) at hw
  rw [← image_erase hinj] at hv hw
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hv
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hw
  obtain ⟨tag, ht, hend⟩ := FactorTable.endpoint_coverage u i j hu hi hj
    (fun he ↦ hvw (congrArg e he))
  have hno := no_common_replacement hcard hn p hp hb q hq hd h ha hab tag
  change ¬CommonReplacement G (e (FactorTable.triple tag 0))
    (e (FactorTable.triple tag 2)) (e (FactorTable.terminal tag)) a at hno
  rw [ht] at hno
  rcases hend with ⟨h0, h2⟩ | ⟨h0, h2⟩
  · rw [h0, h2] at hno
    exact hno ⟨z, hz, hvz, hwz, hrep z hz⟩
  · rw [h0, h2] at hno
    exact hno ⟨z, hz, hwz, hvz, hrep z hz⟩

theorem terminal_bound {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern7 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (hheavy : 9 ≤ contacts G (rows p q hd) a)
    (second : Bool) :
    degreeIn G (PawEncoding.labeling p q hd (if second then 7 else 0)) a ≤ 2 := by
  by_contra! hlarge
  obtain ⟨d, hdf, hdt, hkeep⟩ := exists_terminal hc p hp hb q hq hd h second
  apply no_universal hcard hn p hp hb q hq hd h ha hab hheavy (if second then 7 else 0)
    (by cases second <;> decide +kernel)
  intro z hz
  have hr : 3 ≤ degreeIn G d.terminal a := by rw [hdt]; exact hlarge
  have hrep := hdf.terminal_universal_replace (hkeep a ha hab) hr hz
  rw [hdt] at hrep
  exact hrep

end Erdos577.FirstPawSeven
