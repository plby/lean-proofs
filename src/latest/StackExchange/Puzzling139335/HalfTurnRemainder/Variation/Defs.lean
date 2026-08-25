import StackExchange.Puzzling139335.InterfacePairing
import StackExchange.Puzzling139335.LoopVariation.Geometric.Arc

/-! # Concrete sums over the actual interface arcs -/

namespace Puzzling139335.HalfTurnRemainder

noncomputable section

/-- Sum of intrinsic arc variations on one boundary's actual finite partition. -/
def boundaryArcSum {d : SquareDissection} (F : ExactBoundaryArcFamily d)
    (ε : ℝ) (i : ExtendedPieceIndex) : ℝ :=
  ∑ k : Fin (F.n i), LoopVariation.arcVariation ε (F.arc i k)

theorem boundaryArcSum_nonneg {d : SquareDissection} (F : ExactBoundaryArcFamily d)
    {ε : ℝ} (hε : 0 < ε) (i : ExtendedPieceIndex) : 0 ≤ boundaryArcSum F ε i := by
  apply Finset.sum_nonneg
  intro k _
  exact LoopVariation.arcVariation_nonneg (F.arc_between i k).isArc hε

end

end Puzzling139335.HalfTurnRemainder
