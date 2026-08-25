import Mathlib.Tactic
import Util.IncidenceGeometry.OrdinaryCrossingLocalBranchData
import Util.IncidenceGeometry.PolygonalArcEndpointGluedVertices

open Classical
noncomputable section

lemma OrdinaryCrossingLocalBranchDataThreePieceSuffixLift
    (P bridge S R : PolygonalArc)
    (p : EuclideanSpace ℝ (Fin 2)) (radius : ℝ)
    (branch : OrdinaryCrossingLocalBranchData S p radius)
    (hvertices : R.vertices =
      PolygonalArcEndpointGluedVertices [P, bridge, S])
    (hattach : bridge.target = S.source)
    (hclosed : Metric.closedBall p radius ∩ R.carrier =
      Metric.closedBall p radius ∩ S.carrier)
    (hsphere : Metric.sphere p radius ∩ R.carrier =
      Metric.sphere p radius ∩ S.carrier) :
    ∃ branch' : OrdinaryCrossingLocalBranchData R p radius,
      branch'.beforeGate = branch.beforeGate ∧
        branch'.afterGate = branch.afterGate := by
  let offset := P.vertices.length + bridge.vertices.length - 2
  have hPlen := P.length_ge_two
  have hBlen := bridge.length_ge_two
  have hSlen := S.length_ge_two
  have hRlen : R.vertices.length =
      P.vertices.length + (bridge.vertices.length - 1) +
        (S.vertices.length - 1) := by
    rw [hvertices]
    simp [PolygonalArcEndpointGluedVertices, List.length_tail]
    omega
  have hSzero : S.vertices[0] = S.source := by
    have h := S.source_eq_head
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h
    exact Option.some.inj h
  have hBlast : bridge.vertices[bridge.vertices.length - 1] = bridge.target := by
    have h := bridge.target_eq_last
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h
    exact Option.some.inj h
  have hsegment : ∀ m (hm : m + 1 < S.vertices.length),
      offset + m + 1 < R.vertices.length ∧
        R.vertices[offset + m] = S.vertices[m] ∧
        R.vertices[offset + m + 1] = S.vertices[m + 1] := by
    intro m hm
    have hvalid : offset + m + 1 < R.vertices.length := by
      dsimp [offset]
      rw [hRlen]
      omega
    refine ⟨hvalid, ?_, ?_⟩
    · have hidxR : offset + m < R.vertices.length := by omega
      have hopt := congrArg
        (fun xs : List (EuclideanSpace ℝ (Fin 2)) => xs[offset + m]?) hvertices
      rw [List.getElem?_eq_getElem hidxR] at hopt
      simp only [PolygonalArcEndpointGluedVertices, List.getElem?_append] at hopt
      rw [if_neg (by dsimp [offset]; omega)] at hopt
      simp only [List.map, List.flatten] at hopt
      have hopt' : some R.vertices[offset + m] =
          (bridge.vertices.tail ++ S.vertices.tail)[offset + m - P.vertices.length]? := by
        simpa using hopt
      rw [List.getElem?_append] at hopt'
      by_cases hm0 : m = 0
      · subst m
        have hsub : offset + 0 - P.vertices.length =
            bridge.vertices.tail.length - 1 := by
          dsimp [offset]
          rw [List.length_tail]
          omega
        rw [hsub, if_pos (by rw [List.length_tail]; omega)] at hopt'
        rw [List.getElem?_tail] at hopt'
        have hidx : bridge.vertices.tail.length - 1 + 1 =
            bridge.vertices.length - 1 := by
          rw [List.length_tail]
          omega
        rw [hidx, List.getElem?_eq_getElem (by omega)] at hopt'
        simpa only [hBlast, hattach, ← hSzero] using Option.some.inj hopt'
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
        have hsub : offset + m - P.vertices.length =
            bridge.vertices.tail.length + (m - 1) := by
          dsimp [offset]
          rw [List.length_tail]
          omega
        rw [hsub, if_neg (by omega)] at hopt'
        have hsub2 : bridge.vertices.tail.length + (m - 1) -
            bridge.vertices.tail.length = m - 1 := by omega
        rw [hsub2, List.getElem?_tail] at hopt'
        have hidx : m - 1 + 1 = m := by omega
        rw [hidx, List.getElem?_eq_getElem (by omega)] at hopt'
        exact Option.some.inj hopt'
    · have hidxR : offset + m + 1 < R.vertices.length := hvalid
      have hopt := congrArg
        (fun xs : List (EuclideanSpace ℝ (Fin 2)) => xs[offset + m + 1]?) hvertices
      rw [List.getElem?_eq_getElem hidxR] at hopt
      simp only [PolygonalArcEndpointGluedVertices, List.getElem?_append] at hopt
      rw [if_neg (by dsimp [offset]; omega)] at hopt
      simp only [List.map, List.flatten] at hopt
      have hopt' : some R.vertices[offset + m + 1] =
          (bridge.vertices.tail ++ S.vertices.tail)[offset + m + 1 - P.vertices.length]? := by
        simpa using hopt
      rw [List.getElem?_append] at hopt'
      have hsub : offset + m + 1 - P.vertices.length =
          bridge.vertices.tail.length + m := by
        dsimp [offset]
        rw [List.length_tail]
        omega
      rw [hsub, if_neg (by omega)] at hopt'
      have hsub2 : bridge.vertices.tail.length + m -
          bridge.vertices.tail.length = m := by omega
      rw [hsub2, List.getElem?_tail,
        List.getElem?_eq_getElem (by omega)] at hopt'
      exact Option.some.inj hopt'
  have hbeforeSeg := hsegment branch.beforeIndex branch.beforeIndex_valid
  have hafterSeg := hsegment branch.afterIndex branch.afterIndex_valid
  let beforeIndex := offset + branch.beforeIndex
  let afterIndex := offset + branch.afterIndex
  refine ⟨{
    radius_pos := branch.radius_pos
    beforeIndex := beforeIndex
    afterIndex := afterIndex
    beforeIndex_valid := by simpa [beforeIndex, Nat.add_assoc] using hbeforeSeg.1
    afterIndex_valid := by simpa [afterIndex, Nat.add_assoc] using hafterSeg.1
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
      refine ⟨by dsimp [beforeIndex, afterIndex]; omega, ?_⟩
      simpa only [beforeIndex, hbeforeSeg.2.1, hbeforeSeg.2.2] using h.2
    · right
      refine ⟨by dsimp [beforeIndex, afterIndex]; omega, ?_⟩
      simpa only [afterIndex, hafterSeg.2.1] using h.2
  · simpa only [beforeIndex, hbeforeSeg.2.1] using branch.beforeGate_open
  · simpa only [afterIndex, hafterSeg.2.2] using branch.afterGate_open
  · rw [hclosed, branch.closedBall_carrier_eq]
    simp only [beforeIndex, afterIndex, hbeforeSeg.2.1, hbeforeSeg.2.2,
      hafterSeg.2.1, hafterSeg.2.2]
  · rw [hsphere, branch.sphere_carrier_eq]
