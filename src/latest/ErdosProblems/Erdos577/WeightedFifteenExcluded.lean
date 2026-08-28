import ErdosProblems.Erdos577.WeightedFifteenDenseHeavy
import ErdosProblems.Erdos577.WeightedFifteenDenseTerminals
import ErdosProblems.Erdos577.WeightedFifteenFinalFactors

/-! The complete global exclusion of weighted pattern (15). -/

namespace Erdos577

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace WeightedFifteen

theorem excluded {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (h : WeightedPawBlock.Pattern15 p q) : False := by
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    apply disjoint_left.mpr
    intro w hw hwb
    exact (mem_sdiff.mp (c.complementPartition.block_subset hb hwb)).2 hw
  obtain ⟨a, ha, hab, v, hv, hcl, hrows⟩ := exists_dense_block hc hcard hdeg hn p hp hb q hq hd h
  obtain ⟨t, ht, htb, hta, h13⟩ := dense_heavy_block hc hcard hdeg hn p hp hb q hq
    hd h ha hab v hv hrows
  have hdis : Disjoint (p.support ∪ q.support) v.support := by
    rw [hp, hq, hv, disjoint_union_left]
    refine ⟨?_, c.property.blocks_disjoint hb ha hab.symm⟩
    apply disjoint_left.mpr
    intro w hw hwa
    exact (mem_sdiff.mp (c.complementPartition.block_subset ha hwa)).2 hw
  let f := DenseModel.copy p q hd h v hdis hcl hrows
  have himage : univ.image f = (c.remainder ∪ b) ∪ a := by
    change univ.image (twoBlockLabeling p q hd v hdis) = _
    rw [twoBlockLabeling_image, hp, hq, hv]
  have hdt : Disjoint (univ.image f) t := by
    rw [himage, disjoint_union_left, disjoint_union_left]
    refine ⟨⟨?_, c.property.blocks_disjoint hb ht htb.symm⟩,
      c.property.blocks_disjoint ha ht hta.symm⟩
    apply disjoint_left.mpr
    intro w hw hwt
    exact (mem_sdiff.mp (c.complementPartition.block_subset ht hwt)).2 hw
  have h13' : 13 ≤ contacts G (DenseModel.sixSet.image f) t := by
    change 13 ≤ contacts G (DenseModel.sixSet.image (twoBlockLabeling p q hd v hdis)) t
    rw [six_contacts p q hd h v hdis]
    exact h13
  have hex : ∃ second : Bool, 3 ≤ degreeIn G (if second then q 3 else v 0) t := by
    rcases dense_high_terminal hc hcard hdeg hn p hp hb q hq hd h (v 0) ht htb h13 with hw | hz
    · exact ⟨true, hw⟩
    · exact ⟨false, hz⟩
  obtain ⟨second, h3⟩ := hex
  have hrep (u : V) (hu : u ∈ t) :
      QuadOn G (insert (f (DenseModel.terminal second)) (t.erase u)) := by
    have he : f (DenseModel.terminal second) = (if second then q 3 else v 0) := by
      cases second <;> rfl
    rw [he]
    exact dense_terminal_universal hc hcard hn second p hp hb q hq hd h ha hab v hv hcl hrows
      ht htb hta h3 u hu
  obtain ⟨part⟩ := DenseModel.FinalTable.factor_of_thirteen f second t hdt
    (c.property.blocks_quad t ht).card h13' hrep
  have hbs : ({b, a, t} : Finset (Finset V)) ⊆ c.blocks := by
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact hb
    · rcases mem_insert.mp hz with rfl | hz
      · exact ha
      · exact mem_singleton.mp hz ▸ ht
  have he : c.remainder ∪ ({b, a, t} : Finset (Finset V)).biUnion id = univ.image f ∪ t := by
    rw [himage]
    simp only [biUnion_insert, singleton_biUnion, id_eq, union_assoc]
  exact hn (c.complementPartition.hasPacking_of_selected_factor hcard {b, a, t} hbs
    (he.symm ▸ part))

end WeightedFifteen

lemma TriangleChain.Feasible.not_weighted_pattern15 {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b) :
    ¬WeightedPawBlock.Pattern15 p q :=
  fun h ↦ WeightedFifteen.excluded hc hcard hdeg hn p hp hb q hq h

end Erdos577
