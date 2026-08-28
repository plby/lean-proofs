import ErdosProblems.Erdos577.FirstPawFourCompleteModel
import ErdosProblems.Erdos577.FirstPawFourHeavy
import ErdosProblems.Erdos577.LocalChainSupport
import ErdosProblems.Erdos577.QuadScores

/-! The complete-block exchange preserves feasibility, the five weighted rows, and pattern (4). -/

namespace Erdos577.FirstPawFour

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem complete_swap_data (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : PawBlock.Pattern4 p q) (hheavy : 9 ≤ contacts G p.support q.support)
    (hleaf : ¬G.Adj p.leaf (p.vertices 2) ∧ ¬G.Adj p.leaf (p.vertices 3))
    (hlow : G.Adj (q 1) (q 3)) :
    ∃ (l : LocalChain G (p.support ∪ q.support)) (p' : Paw G) (q' : Quadrilateral G),
      p'.support = l.remainder ∧ q'.support = l.block ∧
      edgeCount G l.block = edgeCount G q.support ∧ PawBlock.Pattern4 p' q' ∧
      9 ≤ contacts G p'.support q'.support ∧
      p'.leaf = p.leaf ∧ p'.vertices 2 = q 1 ∧ p'.vertices 3 = q 3 ∧
      q' 1 = p.vertices 2 ∧ q' 3 = p.vertices 3 := by
  obtain ⟨miss, hrows⟩ := exists_lower_rows p q h hheavy
  let f := CompleteModel.copy p q hd h.1 hlow miss hrows
  let p' := (CompleteModel.paw miss).image f
  let q' : Quadrilateral G := f.comp (CompleteModel.quad miss)
  let l := ((CompleteModel.chain miss).image f).withSupport
    (CompleteModel.copy_image p q hd h.1 hlow miss hrows)
  have hp' : p'.support = (CompleteModel.paw miss).support.image f := Paw.image_support _ _
  have hq' : q'.support = (CompleteModel.quad miss).support.image f :=
    Quadrilateral.support_copy_comp _ _
  have hrem : p'.support = l.remainder := by
    rw [hp', Paw.support_eq, image_insert]
    rfl
  have hblock : q'.support = l.block := hq'
  have hscore : edgeCount G l.block = edgeCount G q.support := by
    have hlo := (CompleteModel.chain miss).image_edgeCount_le f
    rw [CompleteModel.block_score] at hlo
    have hup := l.quad.edgeCount_le_six
    have hold : edgeCount G q.support = 6 := by
      rw [q.edgeCount_eq, if_pos h.1, if_pos hlow]
    change 6 ≤ edgeCount G l.block at hlo
    omega
  have hpat : PawBlock.Pattern4 p' q' := by
    refine ⟨f.toHom.map_rel' (CompleteModel.diagonal miss), ?_, ?_, ?_⟩
    · have hc := degreeIn_image_le f (CompleteModel.paw miss).center
        (CompleteModel.quad miss).support
      rw [← hq'] at hc
      exact (CompleteModel.center_three miss).trans hc
    · have hc := degreeIn_le_card G p'.center q'.support
      rw [q'.card_support] at hc
      exact hc
    · intro j hj
      apply CompleteModel.low_restriction miss j
      have he (i : Fin 4) (hi : G.Adj (p'.vertices i) (q' j)) :
          upperGraph.Adj ((CompleteModel.paw miss).vertices i) (CompleteModel.quad miss j) :=
        adj_upper p q hd h hleaf _ _ hi
      rcases hj with h0 | h2 | h3
      · exact Or.inl (he 0 h0)
      · exact Or.inr (Or.inl (he 2 h2))
      · exact Or.inr (Or.inr (he 3 h3))
  have hnine : 9 ≤ contacts G p'.support q'.support := by
    apply (CompleteModel.contacts_nine miss).trans
    rw [hp', hq', contacts_image_left G _ f f.injective]
    exact sum_le_sum fun v _ ↦ degreeIn_image_le f v (CompleteModel.quad miss).support
  exact ⟨l, p', q', hrem, hblock, hscore, hpat, hnine, rfl, rfl, rfl, rfl, rfl⟩

variable [Fintype V]

theorem exists_complete_swap {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern4 p q)
    (hheavy : 9 ≤ contacts G p.support q.support) (hlow : G.Adj (q 1) (q 3)) :
    ∃ (d : TriangleChain G) (p' : Paw G) (q' : Quadrilateral G), d.Feasible ∧
      p'.support = d.remainder ∧ q'.support ∈ d.blocks ∧
      Disjoint p'.support q'.support ∧ PawBlock.Pattern4 p' q' ∧
      9 ≤ contacts G p'.support q'.support ∧
      p'.leaf = p.leaf ∧ p'.vertices 2 = q 1 ∧ p'.vertices 3 = q 3 ∧
      q' 1 = p.vertices 2 ∧ q' 3 = p.vertices 3 ∧
      ∀ a ∈ c.blocks, a ≠ b → a ∈ d.blocks ∧ a ≠ q'.support := by
  obtain ⟨l₀, p', q', hp', hq', hscore, hpat, hnine, hleaf, h2, h3, hq1, hq3⟩ :=
    complete_swap_data p q hd h hheavy (c.paw_nonadjacent hcard hn p hp) hlow
  let l := l₀.withSupport (show p.support ∪ q.support = c.remainder ∪ b by rw [hp, hq])
  let d := c.replaceBlock b hb l
  have hdf : d.Feasible := hc.replaceBlock_feasible hb l
    (hscore.trans (congrArg (edgeCount G) hq))
  refine ⟨d, p', q', hdf, hp', mem_union_right _ (mem_singleton.mpr hq'),
    ?_, hpat, hnine, hleaf, h2, h3, hq1, hq3, ?_⟩
  · rw [hp', hq']
    exact l₀.disjoint
  · intro a ha hab
    refine ⟨mem_union_left _ (mem_erase.mpr ⟨hab, ha⟩), ?_⟩
    intro he
    have hm : p.vertices 2 ∈ a := by rw [he, ← hq1]; exact (q'.mem_support _).mpr ⟨1, rfl⟩
    exact (mem_sdiff.mp (c.complementPartition.block_subset ha hm)).2
      (hp ▸ (mem_tupleSupport p.vertices _).mpr ⟨2, rfl⟩)

end Erdos577.FirstPawFour
