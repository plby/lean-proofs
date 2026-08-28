import ErdosProblems.Erdos577.JointFullExposureGeometry

/-! The actual feasible low-vertex exposure and its unique core neighbor. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Core.exists_full_last_chain {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support)
    (v : Quadrilateral G) (hv : v.support = j) (z w : V)
    (hpattern : FullPattern v p.leaf (q 3) z w) :
    ∃ f : TriangleChain G, f.Feasible ∧ f.terminal = v 3 ∧ f.triangle = p.triangle ∧
      f.edgeScore = c.edgeScore ∧ f.completeScore = c.completeScore ∧
      f.blocks = (c.blocks.erase q.support ∪ {insert p.leaf (q.support.erase (q 3))}).erase j ∪
        {insert (q 3) (j.erase (v 3))} ∧
      ∀ b ∈ c.blocks, b ≠ q.support → b ≠ j → b ∈ f.blocks := by
  obtain ⟨hp, hq, _, _, hcase, _, _⟩ := h.config
  obtain ⟨e, he, hterm, htri, _, hee, hec, heb, hkeep⟩ :=
    JointClaims.exists_exposed_chain hc hcard hn p hp hq q rfl (h.paw_disjoint hq) (Or.inr hcase)
  have hj' := hkeep j hj hjq
  have hyout : q 3 ∉ v.support := by
    rw [hv]
    exact fun hh ↦ disjoint_left.mp (c.property.blocks_disjoint hq hj hjq.symm)
      ((q.mem_support _).mpr ⟨3, rfl⟩) hh
  obtain ⟨hr, hs⟩ := hpattern.last_replacement hyout
  rw [hv] at hr hs
  obtain ⟨f, hf, hft, hfT, hfe, hfc, hfb⟩ := he.toFeasible.exists_terminal_swap hj'
    (hv ▸ (v.mem_support _).mpr ⟨3, rfl⟩) (by rwa [hterm]) (by rwa [hterm])
  refine ⟨f, hf, hft, hfT.trans htri, hfe.trans hee, hfc.trans hec, ?_, ?_⟩
  · rw [hfb, heb, hterm]
  · intro b hb hbq hbj
    rw [hfb]
    exact mem_union_left _ (mem_erase.mpr ⟨hbj, hkeep b hb hbq⟩)

theorem Core.full_last_core_unique {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hja : j ≠ a)
    (v : Quadrilateral G) (hv : v.support = j) (z w : V)
    (hpair : z = d 2 ∧ w = d 3 ∨ z = d 3 ∧ w = d 2)
    (hpattern : FullPattern v p.leaf (q 3) z w) :
    degreeIn G (v 3) (p.triangle ∪ a) = 1 ∧
      ∀ u ∈ p.triangle ∪ a, G.Adj (v 3) u ↔ u = z := by
  obtain ⟨f, _, ht, hT, _, _, _, hkeep⟩ :=
    h.exists_full_last_chain hc hcard hn hj hjq v hv z w hpattern
  have hm : v 3 ∈ j := hv ▸ (v.mem_support _).mpr ⟨3, rfl⟩
  have hout : v 3 ∉ p.triangle ∪ a :=
    fun hh ↦ disjoint_left.mp (h.core_disjoint hj hja.symm) hh hm
  have hbound : degreeIn G (v 3) (p.triangle ∪ a) ≤ 1 := by
    by_contra! hh
    apply f.no_local_factor hcard hn (hkeep a h.config.2.2.1 h.config.2.2.2.1 hja.symm)
    change LocalFactor G (insert f.terminal f.triangle ∪ a)
    rw [ht, hT, insert_union]
    exact h.outside_factor (v 3) hout (by omega)
  have hza : z ∈ a := by
    rcases hpair with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact h.mem 2
    · exact h.mem 3
  exact FullRow.unique_row_of_bound (p.triangle ∪ a) (v 3) z
    (mem_union_right _ hza) (hpattern.2.2.1 3).symm hbound

end Erdos577.JointFinal
