import ErdosProblems.Erdos633b.DoubledPlacement

/-! The actual trapezoid support equals the fifth region of the explicit outer triangle. -/

namespace Erdos633b.DoubledCoordinates

open Sixty

theorem trapezoid_support (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3) (a b c m : ℝ)
    (ha : 0 < a) (hab : a < b) (hc : 0 < c) (hm : 0 < m)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    let L := DoubledParameters.layout a b c ha hab hc hrel
    let T := outer d hd a b c m ha (ha.trans hab) hc hm
    trapezoidTurn d he a b c m hc hrel ''
      TrapezoidPartition.trapezoidSet (frame d hd) (shortBase a c m) (lateralSide a b c m) =
        DoubledPartition.region T L.u L.v L.r L.μ L.height .trapezoid := by
  let L := DoubledParameters.layout a b c ha hab hc hrel
  let T := outer d hd a b c m ha (ha.trans hab) hc hm
  have hD := D_coords d hd a b c m ha (ha.trans hab) hc hm hrel
  have hG := G_coords d hd a b c m ha (ha.trans hab) hc hm hrel
  have hE := E_coords d hd a b c m ha (ha.trans hab) hc hm hrel
  have hF := F_coords d hd a b c m ha (ha.trans hab) hc hm
  change T.coord 1 (pointD d a b m) = L.u ∧ T.coord 2 (pointD d a b m) = L.v at hD
  change T.coord 1 (pointG d a b m) = 1 - L.r ∧ T.coord 2 (pointG d a b m) = L.r at hG
  change T.coord 1 (pointE d a b m) = L.ε * L.u ∧ T.coord 2 (pointE d a b m) = L.ε * L.v at hE
  change T.coord 1 (pointF d a b c m) = 0 ∧ T.coord 2 (pointF d a b c m) = L.μ at hF
  apply L.trapezoid_support_of_vertices T d hd _ _ (shortBase_pos a c m ha hc hm)
    (lateralSide_pos a b c m ha hab hc hm) _ (trapezoid_scale a b c m ha hab hc hrel)
  · intro i
    rw [trapezoidTurn_vertices d he a b c m ha (ha.trans hab) hc hrel]
    fin_cases i
    · exact hF.1
    · exact hE.1
    · exact hD.1
    · exact hG.1
  · intro i
    rw [trapezoidTurn_vertices d he a b c m ha (ha.trans hab) hc hrel]
    fin_cases i
    · exact hF.2
    · exact hE.2
    · exact hD.2
    · exact hG.2

end Erdos633b.DoubledCoordinates
