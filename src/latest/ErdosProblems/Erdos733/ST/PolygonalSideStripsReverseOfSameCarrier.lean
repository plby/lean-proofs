import ErdosProblems.Erdos733.ST.PolygonalArc
import ErdosProblems.Erdos733.ST.PolygonalSideStrips

open Classical
noncomputable section

-- [TABLET NODE: PolygonalSideStripsReverseOfSameCarrier]
lemma PolygonalSideStripsReverseOfSameCarrier (γ δ : PolygonalArc)
    (S : PolygonalSideStrips γ) :
    δ.carrier = γ.carrier →
      δ.source = γ.target →
        δ.target = γ.source →
          ∃ T : PolygonalSideStrips δ,
            T.leftStrip = S.rightStrip ∧ T.rightStrip = S.leftStrip := by
-- BODY
  intro hcarrier hsource htarget
  have hrel : δ.relativeInterior = γ.relativeInterior := by
    rw [δ.relativeInterior_eq, γ.relativeInterior_eq, hcarrier, hsource, htarget]
    ext p
    simp [Set.mem_diff, and_assoc, and_comm]
  refine
    ⟨{ collar := S.collar
       leftStrip := S.rightStrip
       rightStrip := S.leftStrip
       collar_open := S.collar_open
       left_open := S.right_open
       right_open := S.left_open
       relativeInterior_subset_collar := by
        intro x hx
        exact S.relativeInterior_subset_collar (by simpa [hrel] using hx)
       left_subset_collar := S.right_subset_collar
       right_subset_collar := S.left_subset_collar
       left_connected := S.right_connected
       right_connected := S.left_connected
       left_disjoint_arc := by
        simpa [hcarrier] using S.right_disjoint_arc
       right_disjoint_arc := by
        simpa [hcarrier] using S.left_disjoint_arc
       side_strips_disjoint := S.side_strips_disjoint.symm
       relativeInterior_subset_closure_left := by
        intro x hx
        exact S.relativeInterior_subset_closure_right (by simpa [hrel] using hx)
       relativeInterior_subset_closure_right := by
        intro x hx
        exact S.relativeInterior_subset_closure_left (by simpa [hrel] using hx)
       collar_without_arc := by
        calc
          S.collar \ δ.relativeInterior = S.collar \ γ.relativeInterior := by
            rw [hrel]
          _ = S.leftStrip ∪ S.rightStrip := S.collar_without_arc
          _ = S.rightStrip ∪ S.leftStrip := by
            rw [Set.union_comm] },
      rfl, rfl⟩
