import StackExchange.Puzzling139335.N4MiddleInvolutions.BoundaryBalance.SegmentBounds
import StackExchange.Puzzling139335.N4MiddleInvolutions.BoundaryBalance.Algebra

/-! Applying the actual straight-segment bound to partner-selected arcs. -/

open Set

namespace Puzzling139335.N4MiddleInvolutions.BoundaryBalance

noncomputable section

/-- A partner-selected interface sum is bounded by any segment containing
all of its actual arc carriers. -/
theorem pairArcSum_le_dist_of_subset_segment {d : SquareDissection}
    (F : ExactBoundaryArcFamily d) {ε : ℝ} (hε : 0 < ε)
    (i j : ExtendedPieceIndex) {a b : Plane}
    (hsub : ∀ k, F.partner i k = j → F.arc i k ⊆ segment ℝ a b) :
    pairArcSum F ε i j ≤ dist a b := by
  classical
  have h := selected_arcVariation_sum_le_dist F hε i
    (Finset.univ.filter fun k => F.partner i k = j)
    (fun k hk => hsub k (Finset.mem_filter.mp hk).2)
  simpa only [Finset.sum_filter, pairArcSum] using h

/-- If two actual regions have their entire intersection in one segment,
the corresponding concrete interface sum is at most that segment's length. -/
theorem pairArcSum_le_dist_of_inter_subset_segment {d : SquareDissection}
    (F : ExactBoundaryArcFamily d) {ε : ℝ} (hε : 0 < ε)
    (i j : ExtendedPieceIndex) {a b : Plane}
    (hsub : d.extendedPiece i ∩ d.extendedPiece j ⊆ segment ℝ a b) :
    pairArcSum F ε i j ≤ dist a b := by
  apply pairArcSum_le_dist_of_subset_segment F hε i j
  intro k hk z hz
  have hfront := F.subset_frontiers i k hz
  rw [hk] at hfront
  apply hsub
  exact ⟨(d.extendedPiece_closed i).closure_eq ▸ hfront.1.1,
    (d.extendedPiece_closed j).closure_eq ▸ hfront.2.1⟩

end

end Puzzling139335.N4MiddleInvolutions.BoundaryBalance
