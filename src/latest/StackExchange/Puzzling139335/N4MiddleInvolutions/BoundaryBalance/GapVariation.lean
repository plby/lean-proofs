import StackExchange.Puzzling139335.N4MiddleInvolutions.BoundaryBalance.MiddleGaps
import StackExchange.Puzzling139335.N4MiddleInvolutions.BoundaryBalance.SegmentBounds
import StackExchange.Puzzling139335.N4MiddleInvolutions.BoundaryBalance.Algebra

/-! Finite-resolution bounds on all actual middle exterior arcs. -/

open Set

namespace Puzzling139335.N4MiddleInvolutions.BoundaryBalance

noncomputable section

/-- Selected disjoint interface arcs in two separated vertical gaps have
total variation at most the sum of the two straight gap lengths. -/
theorem selected_arcVariation_sum_le_two_gaps {d : SquareDissection}
    (F : ExactBoundaryArcFamily d) {ε a b : ℝ} (hε : 0 < ε)
    (ha : a ≤ 1 / 2) (hb : b ≤ 1 / 2)
    (i : ExtendedPieceIndex) (K : Finset (Fin (F.n i)))
    (hsub : ∀ k ∈ K, F.arc i k ⊆ verticalGap 0 a ∪ verticalGap 1 b) :
    ∑ k ∈ K, LoopVariation.arcVariation ε (F.arc i k) ≤ 2 - 2 * (a + b) := by
  classical
  let p : Fin (F.n i) → Prop := fun k => F.arc i k ⊆ verticalGap 0 a
  have hL := selected_arcVariation_sum_le_dist F hε i (K.filter p)
    (fun k hk => (Finset.mem_filter.mp hk).2)
  have hR := selected_arcVariation_sum_le_dist F hε i (K.filter (fun k => ¬ p k)) (by
    intro k hk
    have hclass := preconnected_subset_one_verticalGap
      (F.arc_between i k).isArc.isConnected.isPreconnected
      (hsub k (Finset.mem_filter.mp hk).1)
    exact hclass.resolve_left (Finset.mem_filter.mp hk).2)
  have hsplit := Finset.sum_filter_add_sum_filter_not K p
    (fun k => LoopVariation.arcVariation ε (F.arc i k))
  rw [verticalGap_endpoint_distance 0 ha] at hL
  rw [verticalGap_endpoint_distance 1 hb] at hR
  linarith

/-- The exterior contributions of the two middle pieces are bounded by the
actual uncovered side lengths. -/
theorem middle_exterior_pairArcSum_le {d : SquareDissection}
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    {a b : ℝ} (ha : a ≤ 1 / 2) (hb : b ≤ 1 / 2)
    (hleft : ∀ y : ℝ,
      Schoenflies.Plane.mk 0 y ∈ d.piece 0 ↔ y ∈ Icc (0 : ℝ) a)
    (hright : ∀ y : ℝ,
      Schoenflies.Plane.mk 1 y ∈ d.piece 0 ↔ y ∈ Icc (0 : ℝ) b)
    (F : ExactBoundaryArcFamily d) {ε : ℝ} (hε : 0 < ε) :
    pairArcSum F ε (Sum.inl 2) (Sum.inr ()) +
      pairArcSum F ε (Sum.inl 3) (Sum.inr ()) ≤ 2 - 2 * (a + b) := by
  classical
  let K : Finset (Fin (F.n (Sum.inr ()))) := Finset.univ.filter fun k =>
    F.partner (Sum.inr ()) k = Sum.inl 2 ∨ F.partner (Sum.inr ()) k = Sum.inl 3
  have hbound := selected_arcVariation_sum_le_two_gaps F hε ha hb (Sum.inr ()) K (by
    intro k hk
    exact middle_exterior_arc_subset_gaps h hc ha hb hleft hright F k
      (Finset.mem_filter.mp hk).2)
  have hsum : pairArcSum F ε (Sum.inr ()) (Sum.inl 2) +
      pairArcSum F ε (Sum.inr ()) (Sum.inl 3) =
      ∑ k ∈ K, LoopVariation.arcVariation ε (F.arc (Sum.inr ()) k) := by
    simp only [pairArcSum, K, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk2 : F.partner (Sum.inr ()) k = Sum.inl 2
    · simp [hk2]
    · by_cases hk3 : F.partner (Sum.inr ()) k = Sum.inl 3 <;> simp [hk2, hk3]
  rw [pairArcSum_symm F ε (Sum.inl 2) (Sum.inr ()),
    pairArcSum_symm F ε (Sum.inl 3) (Sum.inr ()), hsum]
  exact hbound

end

end Puzzling139335.N4MiddleInvolutions.BoundaryBalance
