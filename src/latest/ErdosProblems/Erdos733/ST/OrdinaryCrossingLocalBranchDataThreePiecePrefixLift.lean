import Mathlib.Tactic
import ErdosProblems.Erdos733.ST.OrdinaryCrossingLocalBranchData
import ErdosProblems.Erdos733.ST.PolygonalArcEndpointGluedVertices

open Classical
noncomputable section

-- [TABLET NODE: OrdinaryCrossingLocalBranchDataThreePiecePrefixLift]
lemma OrdinaryCrossingLocalBranchDataThreePiecePrefixLift
    (P bridge S R : PolygonalArc)
    (p : EuclideanSpace ℝ (Fin 2)) (radius : ℝ)
    (branch : OrdinaryCrossingLocalBranchData P p radius)
    (hvertices : R.vertices =
      PolygonalArcEndpointGluedVertices [P, bridge, S])
    (hclosed : Metric.closedBall p radius ∩ R.carrier =
      Metric.closedBall p radius ∩ P.carrier)
    (hsphere : Metric.sphere p radius ∩ R.carrier =
      Metric.sphere p radius ∩ P.carrier) :
    ∃ branch' : OrdinaryCrossingLocalBranchData R p radius,
      branch'.beforeGate = branch.beforeGate ∧
        branch'.afterGate = branch.afterGate := by
-- BODY
  have hlen : P.vertices.length ≤ R.vertices.length := by
    rw [hvertices]
    simp [PolygonalArcEndpointGluedVertices]
  have hget : ∀ n (hn : n < P.vertices.length),
      R.vertices[n] = P.vertices[n] := by
    intro n hn
    have hnR : n < R.vertices.length := hn.trans_le hlen
    have hopt := congrArg
      (fun xs : List (EuclideanSpace ℝ (Fin 2)) => xs[n]?) hvertices
    rw [List.getElem?_eq_getElem hnR] at hopt
    have hnG : n <
        (PolygonalArcEndpointGluedVertices [P, bridge, S]).length := by
      simpa [PolygonalArcEndpointGluedVertices] using
        (lt_of_lt_of_le hn (Nat.le_add_right P.vertices.length
          ((bridge.vertices.tail ++ S.vertices.tail).length)))
    rw [List.getElem?_eq_getElem hnG] at hopt
    calc
      R.vertices[n] =
          (P.vertices ++ (bridge.vertices.tail ++ S.vertices.tail))[n]'(by
            simp only [List.length_append]
            omega) := by
        simpa [PolygonalArcEndpointGluedVertices] using Option.some.inj hopt
      _ = P.vertices[n] :=
        List.getElem_append_left (as := P.vertices)
          (bs := bridge.vertices.tail ++ S.vertices.tail) hn
  have hbefore : branch.beforeIndex + 1 < R.vertices.length :=
    lt_of_lt_of_le branch.beforeIndex_valid hlen
  have hafter : branch.afterIndex + 1 < R.vertices.length :=
    lt_of_lt_of_le branch.afterIndex_valid hlen
  have hb0 := hget branch.beforeIndex
    (Nat.lt_of_succ_lt branch.beforeIndex_valid)
  have hb1 := hget (branch.beforeIndex + 1) branch.beforeIndex_valid
  have ha0 := hget branch.afterIndex
    (Nat.lt_of_succ_lt branch.afterIndex_valid)
  have ha1 := hget (branch.afterIndex + 1) branch.afterIndex_valid
  refine ⟨{
    radius_pos := branch.radius_pos
    beforeIndex := branch.beforeIndex
    afterIndex := branch.afterIndex
    beforeIndex_valid := hbefore
    afterIndex_valid := hafter
    center_case := ?_
    beforeGate := branch.beforeGate
    afterGate := branch.afterGate
    beforeGate_open := ?_
    afterGate_open := ?_
    beforeGate_on_sphere := branch.beforeGate_on_sphere
    afterGate_on_sphere := branch.afterGate_on_sphere
    gates_ne := branch.gates_ne
    closedBall_carrier_eq := ?_
    sphere_carrier_eq := ?_
  }, rfl, rfl⟩
  · rcases branch.center_case with h | h
    · left
      refine ⟨h.1, ?_⟩
      simpa only [hb0, hb1] using h.2
    · right
      refine ⟨h.1, ?_⟩
      simpa only [ha0] using h.2
  · simpa only [hb0] using branch.beforeGate_open
  · simpa only [ha1] using branch.afterGate_open
  · rw [hclosed, branch.closedBall_carrier_eq]
    simp only [hb0, hb1, ha0, ha1]
  · rw [hsphere, branch.sphere_carrier_eq]
