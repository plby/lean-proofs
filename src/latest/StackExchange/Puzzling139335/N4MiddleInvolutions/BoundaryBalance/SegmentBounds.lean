import StackExchange.Puzzling139335.InterfacePairing
import StackExchange.Puzzling139335.N4MiddleInvolutions.BoundaryBalance.SegmentBounds.ArcIdentity
import StackExchange.Puzzling139335.N4MiddleInvolutions.BoundaryBalance.SegmentBounds.Packing
import StackExchange.Puzzling139335.N4MiddleInvolutions.BoundaryBalance.SegmentBounds.StraightVariation

/-!
# Straight-segment bounds for actual boundary-arc sums

No perimeter hypothesis is used. Each arc contained in a segment is its
endpoint segment, finite-chain variation is at most its endpoint distance,
and the disjoint open endpoint segments pack into the containing segment.
-/

open Set
open scoped BigOperators

namespace Puzzling139335.N4MiddleInvolutions.BoundaryBalance

noncomputable section

/-- An actual arc contained in a straight segment has variation at most the
distance between its own named endpoints. -/
theorem arcVariation_le_dist_of_subset_segment {ε : ℝ} (hε : 0 ≤ ε)
    {A : Set Plane} {x y a b : Plane}
    (hA : Schoenflies.IsArcBetween A x y) (hsub : A ⊆ segment ℝ a b) :
    LoopVariation.arcVariation ε A ≤ dist x y := by
  rw [arc_eq_segment_of_subset_segment hA hsub]
  exact arcVariation_segment_le_dist hε (arc_endpoints_ne hA)

/-- A finite family of arcs meeting only at their named endpoints and
contained in one straight segment has total variation at most its length. -/
theorem sum_arcVariation_le_dist_of_subset_segment {ι : Type*}
    (K : Finset ι) (A : ι → Set Plane) (x y : ι → Plane)
    {ε : ℝ} (hε : 0 ≤ ε) {a b : Plane}
    (hA : ∀ k ∈ K, Schoenflies.IsArcBetween (A k) (x k) (y k))
    (hsub : ∀ k ∈ K, A k ⊆ segment ℝ a b)
    (hmeet : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → A i ∩ A j ⊆ {x i, y i}) :
    (∑ k ∈ K, LoopVariation.arcVariation ε (A k)) ≤ dist a b := by
  classical
  have heq (k : ι) (hk : k ∈ K) : A k = segment ℝ (x k) (y k) :=
    arc_eq_segment_of_subset_segment (hA k hk) (hsub k hk)
  have hdis : (↑K : Set ι).Pairwise fun i j =>
      Disjoint (openSegment ℝ (x i) (y i)) (openSegment ℝ (x j) (y j)) := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro z hzi hzj
    have hziA : z ∈ A i := by
      rw [heq i hi]
      exact openSegment_subset_segment ℝ (x i) (y i) hzi
    have hzjA : z ∈ A j := by
      rw [heq j hj]
      exact openSegment_subset_segment ℝ (x j) (y j) hzj
    rcases hmeet i hi j hj hij ⟨hziA, hzjA⟩ with rfl | rfl
    · exact arc_endpoints_ne (hA i hi) (left_mem_openSegment_iff.mp hzi)
    · exact arc_endpoints_ne (hA i hi) (right_mem_openSegment_iff.mp hzi)
  calc
    (∑ k ∈ K, LoopVariation.arcVariation ε (A k)) ≤
        ∑ k ∈ K, dist (x k) (y k) := by
      apply Finset.sum_le_sum
      intro k hk
      exact arcVariation_le_dist_of_subset_segment hε (hA k hk) (hsub k hk)
    _ ≤ dist a b := sum_dist_le_of_disjoint_openSegments K x y
      (fun k hk => hsub k hk (hA k hk).left_mem)
      (fun k hk => hsub k hk (hA k hk).right_mem) hdis

/-- Selected actual arcs from one exact boundary partition pack into any
common straight segment containing them. -/
theorem selected_arcVariation_sum_le_dist {d : SquareDissection}
    (F : ExactBoundaryArcFamily d) {ε : ℝ} (hε : 0 < ε)
    (i : ExtendedPieceIndex) (K : Finset (Fin (F.n i))) {a b : Plane}
    (hsub : ∀ k ∈ K, F.arc i k ⊆ segment ℝ a b) :
    (∑ k ∈ K, LoopVariation.arcVariation ε (F.arc i k)) ≤ dist a b := by
  apply sum_arcVariation_le_dist_of_subset_segment K (F.arc i) (F.left i) (F.right i)
    hε.le (fun k _ => F.arc_between i k) hsub
  intro k _ l _ hkl z hz
  exact (F.meet_endpoints i k l hkl hz).1

end

end Puzzling139335.N4MiddleInvolutions.BoundaryBalance
