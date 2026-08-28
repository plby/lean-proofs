import ErdosProblems.Erdos577.JointFirstPreparation
import ErdosProblems.Erdos577.JointFirstRowCoverage
import ErdosProblems.Erdos577.JointFirstPatternTransport

/-! TeX9.50: CaseI is incompatible with the two dense-core row inequalities. -/

namespace Erdos577.JointClaims

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem case_one_dense_false {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (has : a ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (hcase : CaseOne p q)
    (houter : 7 ≤ degreeIn G p.center a + degreeIn G (p.vertices 3) a)
    (hweighted : 13 ≤ degreeIn G (p.vertices 3) a + contacts G p.triangle a) : False := by
  obtain ⟨z1, h1, z2, h2, hne, hc1, hc2, hz, hrep, hprimary, hpe, hcore,
      j, hj, hjs, hja, hnine, hcommon, hrows, hx, hv⟩ :=
    JointFirst.exists_restricted_heavy_block hc hcard hdeg hn p hp hs ha has q hq hcase
      houter hweighted
  have hFQ : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hFA : Disjoint p.support a := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha)
  have hFJ : Disjoint p.support j.support := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hj)
  have hAQ : Disjoint a q.support := by rw [hq]; exact c.property.blocks_disjoint ha hs has
  have hQJ : Disjoint q.support j.support := by
    rw [hq]
    exact c.property.blocks_disjoint hs hj hjs.symm
  have hAJ : Disjoint a j.support := c.property.blocks_disjoint ha hj hja.symm
  have hfour := JointFirst.arms_card p q hFQ z1 z2
    (fun hh ↦ disjoint_left.mp hFA hh h1) (fun hh ↦ disjoint_left.mp hFA hh h2)
    (fun hh ↦ disjoint_left.mp hAQ h1 hh) (fun hh ↦ disjoint_left.mp hAQ h2 hh) hne
  obtain ⟨hxv, hx1, hx2, hv1, hv2, hz12⟩ := JointCore.four_distinct hfour
  let rows := fourTuple p.leaf (q 1) z1 z2 hxv hx1 hx2 hv1 hv2 hz12
  have hsupport : tupleSupport rows = JointFirst.arms p q z1 z2 := by
    rw [fourTuple_support]
    rfl
  have hmem (i : Fin 4) : rows i ∈ JointFirst.arms p q z1 z2 := by
    rw [← hsupport]
    exact (mem_tupleSupport rows _).mpr ⟨i, rfl⟩
  have hdis : Disjoint (JointFirst.arms p q z1 z2) j.support :=
    (disjoint_union_left.mpr ⟨disjoint_union_left.mpr ⟨hFJ, hQJ⟩, hAJ⟩).mono_left
      (JointFirst.arms_subset p q h1 h2)
  have hout (i : Fin 4) : rows i ∉ j.support := fun hh ↦ disjoint_left.mp hdis (hmem i) hh
  have hh : JointFirstRows.Hypotheses (JointFirstRows.encoded rows j).val := by
    unfold JointFirstRows.Hypotheses
    rw [JointFirstRows.rowCount_encoded, JointFirstRows.rowCount_encoded,
      JointFirstRows.rowCount_encoded, JointFirstRows.rowCount_encoded,
      JointFirstRows.crossCount_encoded, hsupport]
    exact ⟨hx, hv, hrows z1 (by simp [JointFirst.arms]),
      hrows z2 (by simp [JointFirst.arms]), hnine⟩
  rcases JointFirstRows.finite_classification (Unattached.diagonal j)
      (JointFirstRows.encoded rows j) hh with h | ⟨leaf, which, cols, h⟩ | ⟨leaf, cols, h⟩
  · obtain ⟨x, y, z, hxy, hxz, hyz, hinsert⟩ := h.transport rows j hout
    exact hcommon (rows x) (hmem x) (rows y) (hmem y) (rows z) (hmem z)
      (rows.injective.ne hxy) (rows.injective.ne hxz) (rows.injective.ne hyz) hinsert
  · obtain ⟨j', hsupport', hdiag, h0, h2', hlow, hhigh1, hhigh2⟩ :=
      h.transport rows j leaf which cols
    have hj' : j'.support ∈ c.blocks := hsupport'.symm ▸ hj
    have hjs' : j'.support ≠ s := by rwa [hsupport']
    have haj' : a ≠ j'.support := by rw [hsupport']; exact hja.symm
    have hbad : ¬(G.Adj p.leaf (j' 0) ∧ G.Adj p.leaf (j' 2)) ∧
        ¬(G.Adj (q 1) (j' 0) ∧ G.Adj (q 1) (j' 2)) := by
      fin_cases which
      · exact JointFirst.both_leaves_high_pair_forbidden hc hcard hdeg hn p hp hs ha has q hq
          hcase j' hj' hjs' haj' hdiag hcore h1 h2 hne hc1 (hrep z1 h1) hlow hhigh1 hhigh2
      · exact JointFirst.both_leaves_high_pair_forbidden hc hcard hdeg hn p hp hs ha has q hq
          hcase j' hj' hjs' haj' hdiag hcore h2 h1 hne.symm hc2 (hrep z2 h2) hlow hhigh2 hhigh1
    fin_cases leaf
    · exact hbad.1 ⟨h0, h2'⟩
    · exact hbad.2 ⟨h0, h2'⟩
  · obtain ⟨j', hsupport', he, h0, h3, h21, h22, h31, h32⟩ := h.transport rows j leaf cols
    have hj' : j'.support ∈ c.blocks := hsupport'.symm ▸ hj
    have hjs' : j'.support ≠ s := by rwa [hsupport']
    have haj' : a ≠ j'.support := by rw [hsupport']; exact hja.symm
    have hbad := JointFirst.both_leaves_crossing_gain_forbidden hc hcard hn p hp hs ha has q hq
      hcase j' hj' hjs' haj' he h1 h2 hprimary hpe hz h21 h22 h31 h32
    fin_cases leaf
    · exact hbad.1 ⟨h0, h3⟩
    · exact hbad.2 ⟨h0, h3⟩

end Erdos577.JointClaims
