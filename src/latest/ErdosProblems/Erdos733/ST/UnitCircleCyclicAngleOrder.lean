import ErdosProblems.Erdos733.ST.UnitCircle
import ErdosProblems.Erdos733.ST.UnitCircleCyclicAngleBasicOrder
import ErdosProblems.Erdos733.ST.UnitCircleCyclicAngleData
import ErdosProblems.Erdos733.ST.UnitCircleFundamentalAngles

open Classical
noncomputable section

-- [TABLET NODE: UnitCircleCyclicAngleOrder]
lemma UnitCircleCyclicAngleOrder
    (p : EuclideanSpace ℝ (Fin 2))
    (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (hS : (↑S : Set (EuclideanSpace ℝ (Fin 2))) ⊆ UnitCircle p)
    (hcard : 3 ≤ S.card) :
    Nonempty (UnitCircleCyclicAngleData p S) := by
-- BODY
  rcases UnitCircleFundamentalAngles p S hS with ⟨θ, hθ_mem, hθ_point, hθ_inj⟩
  rcases UnitCircleCyclicAngleBasicOrder p S θ hθ_mem hθ_point hθ_inj hcard with
    ⟨succ, startAngle, endAngle, hsucc_bijective, hsucc_ne, hendpoint_unique,
      hstart_mem, hstart_point, hend_point, hend_lift, hgap_pos, hgap_short,
      hno_S_in_open_gap, hopen_gaps_disjoint⟩
  refine ⟨
    { succ := succ
      startAngle := startAngle
      endAngle := endAngle
      succ_bijective := hsucc_bijective
      succ_ne := hsucc_ne
      endpoint_unique := hendpoint_unique
      start_mem_fundamental := hstart_mem
      start_point := hstart_point
      end_point := hend_point
      end_lift := hend_lift
      gap_pos := hgap_pos
      gap_short := hgap_short
      no_S_in_open_gap := hno_S_in_open_gap
      open_gaps_disjoint := hopen_gaps_disjoint }⟩
