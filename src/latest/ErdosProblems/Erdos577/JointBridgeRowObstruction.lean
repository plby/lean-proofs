import ErdosProblems.Erdos577.JointBridgeObstructions
import ErdosProblems.Erdos577.JointFirstRowCoverage
import ErdosProblems.Erdos577.JointFirstPatternTransport

/-! The existing certified row classification closes the bridge's four-arm obstruction. -/

namespace Erdos577.JointBridge

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem four_arm_obstruction {c d : TriangleChain G} (hc : c.Feasible) (hd : d.Strong)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder)
    (u : V) (ht : d.terminal = u) (hT : d.triangle = p.triangle)
    {a : Finset V} (ha : a ∈ c.blocks) (had : a ∈ d.blocks)
    (j : Quadrilateral G) (hj : j.support ∈ c.blocks) (hjd : j.support ∈ d.blocks)
    (haj : a ≠ j.support)
    {z1 z2 : V} (h1 : z1 ∈ a) (h2 : z2 ∈ a)
    (hc1 : G.Adj p.center z1) (hc2 : G.Adj p.center z2) (hz : G.Adj z1 z2)
    (hrep : ∀ v ∈ a, QuadOn G (insert (p.vertices 3) (a.erase v)))
    (hprimary : QuadOn G ((p.triangle ∪ a) \ {p.center, z1, z2}))
    (hpe : 5 ≤ edgeCount G ((p.triangle ∪ a) \ {p.center, z1, z2}))
    (hcore : ∀ v, v ∉ p.triangle ∪ a → 2 ≤ degreeIn G v (p.triangle ∪ a) →
      LocalFactor G (insert v (p.triangle ∪ a)))
    (hfour : (arms p u z1 z2).card = 4) (hdis : Disjoint (arms p u z1 z2) j.support)
    (hnine : 9 ≤ contacts G (arms p u z1 z2) j.support)
    (hcommon : ∀ x ∈ arms p u z1 z2, ∀ y ∈ arms p u z1 z2, ∀ z ∈ arms p u z1 z2,
      x ≠ y → x ≠ z → y ≠ z → ¬CommonReplacement G x y z j.support)
    (hrows : ∀ z ∈ arms p u z1 z2, degreeIn G z j.support ≤ 3)
    (hx : degreeIn G p.leaf j.support ≤ 2) (hu : degreeIn G u j.support ≤ 2) : False := by
  obtain ⟨hxu, hx1, hx2, hu1, hu2, hne⟩ := JointCore.four_distinct hfour
  let rows := fourTuple p.leaf u z1 z2 hxu hx1 hx2 hu1 hu2 hne
  have hsupport : tupleSupport rows = arms p u z1 z2 := by
    rw [fourTuple_support]
    rfl
  have hmem (i : Fin 4) : rows i ∈ arms p u z1 z2 := by
    rw [← hsupport]
    exact (mem_tupleSupport rows _).mpr ⟨i, rfl⟩
  have hout (i : Fin 4) : rows i ∉ j.support := fun hh ↦ disjoint_left.mp hdis (hmem i) hh
  have hh : JointFirstRows.Hypotheses (JointFirstRows.encoded rows j).val := by
    unfold JointFirstRows.Hypotheses
    rw [JointFirstRows.rowCount_encoded, JointFirstRows.rowCount_encoded,
      JointFirstRows.rowCount_encoded, JointFirstRows.rowCount_encoded,
      JointFirstRows.crossCount_encoded, hsupport]
    exact ⟨hx, hu, hrows z1 (by simp [arms]), hrows z2 (by simp [arms]), hnine⟩
  rcases JointFirstRows.finite_classification (Unattached.diagonal j)
      (JointFirstRows.encoded rows j) hh with h | ⟨leaf, which, cols, h⟩ | ⟨leaf, cols, h⟩
  · obtain ⟨x, y, z, hxy, hxz, hyz, hinsert⟩ := h.transport rows j hout
    exact hcommon (rows x) (hmem x) (rows y) (hmem y) (rows z) (hmem z)
      (rows.injective.ne hxy) (rows.injective.ne hxz) (rows.injective.ne hyz) hinsert
  · obtain ⟨j', hsupport', hdiag, h0, h2', hlow, hhigh1, hhigh2⟩ :=
      h.transport rows j leaf which cols
    have hj' : j'.support ∈ c.blocks := hsupport'.symm ▸ hj
    have hjd' : j'.support ∈ d.blocks := hsupport'.symm ▸ hjd
    have haj' : a ≠ j'.support := by rwa [hsupport']
    have hbad : ¬(G.Adj p.leaf (j' 0) ∧ G.Adj p.leaf (j' 2)) ∧
        ¬(G.Adj u (j' 0) ∧ G.Adj u (j' 2)) := by
      fin_cases which
      · exact both_high_pairs_forbidden hc hd hcard hdeg hn p hp u ht hT ha had j' hj' hjd'
          haj' hdiag hcore h1 h2 hne hc1 (hrep z1 h1) hlow hhigh1 hhigh2
      · exact both_high_pairs_forbidden hc hd hcard hdeg hn p hp u ht hT ha had j' hj' hjd'
          haj' hdiag hcore h2 h1 hne.symm hc2 (hrep z2 h2) hlow hhigh2 hhigh1
    fin_cases leaf
    · exact hbad.1 ⟨h0, h2'⟩
    · exact hbad.2 ⟨h0, h2'⟩
  · obtain ⟨j', hsupport', he, h0, h3, h21, h22, h31, h32⟩ := h.transport rows j leaf cols
    have hj' : j'.support ∈ c.blocks := hsupport'.symm ▸ hj
    have hjd' : j'.support ∈ d.blocks := hsupport'.symm ▸ hjd
    have haj' : a ≠ j'.support := by rwa [hsupport']
    have hbad := both_crossing_gains_forbidden hc hd.toFeasible p hp u ht hT ha had j' hj'
      hjd' haj' he h1 h2 hprimary hpe hz h21 h22 h31 h32
    fin_cases leaf
    · exact hbad.1 ⟨h0, h3⟩
    · exact hbad.2 ⟨h0, h3⟩

end Erdos577.JointBridge
