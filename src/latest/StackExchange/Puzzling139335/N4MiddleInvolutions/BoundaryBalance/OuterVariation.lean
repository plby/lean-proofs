import StackExchange.Puzzling139335.N4MiddleInvolutions.BoundaryBalance.Algebra
import StackExchange.Puzzling139335.N4MiddleInvolutions.BoundaryBalance.PolylineBounds
import StackExchange.Puzzling139335.N4MiddleInvolutions.BoundaryBalance.ExteriorArcs.Geometry

/-! Lower bounds from the two actual outer contact arcs. -/

open Set

namespace Puzzling139335.N4MiddleInvolutions.BoundaryBalance

noncomputable section

theorem lowerOuterArc_variation_lower {a b ε : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε) :
    1 + a + b - 3 * ε ≤ LoopVariation.arcVariation ε (lowerOuterArc a b) :=
  lower_three_sides_variation_lower ha hb hε

theorem upperOuterArc_variation_lower {a b ε : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε) :
    1 + a + b - 3 * ε ≤ LoopVariation.arcVariation ε (upperOuterArc a b) := by
  rw [upperOuterArc, LoopVariation.arcVariation_image_isometry ε
    (lowerOuterArc_isArcBetween ha hb).isArc ReflectionSeparation.horizontal.isometry]
  exact lowerOuterArc_variation_lower ha hb hε

/-- Every named occurrence contributes its nonnegative variation to the
corresponding partner-selected sum. -/
theorem arcVariation_le_pairArcSum {d : SquareDissection}
    (F : ExactBoundaryArcFamily d) {ε : ℝ} (hε : 0 < ε)
    (i j : ExtendedPieceIndex) (k : Fin (F.n i)) (hk : F.partner i k = j) :
    LoopVariation.arcVariation ε (F.arc i k) ≤ pairArcSum F ε i j := by
  classical
  unfold pairArcSum
  calc
    LoopVariation.arcVariation ε (F.arc i k) =
        (if F.partner i k = j then LoopVariation.arcVariation ε (F.arc i k) else 0) := by
      rw [if_pos hk]
    _ ≤ ∑ l : Fin (F.n i),
        if F.partner i l = j then LoopVariation.arcVariation ε (F.arc i l) else 0 := by
      apply Finset.single_le_sum ?_ (Finset.mem_univ k)
      intro l _
      split_ifs
      · exact LoopVariation.arcVariation_nonneg (F.arc_between i l).isArc hε
      · exact le_rfl

/-- Once identified as actual exterior occurrences, the two three-side arcs
give the complete lower bound needed for interface cancellation. -/
theorem outer_pairArcSum_lower_of_occurrences {d : SquareDissection}
    (F : ExactBoundaryArcFamily d) {a b ε : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε)
    (k0 k1 : Fin (F.n (Sum.inr ())))
    (hp0 : F.partner (Sum.inr ()) k0 = Sum.inl 0)
    (hp1 : F.partner (Sum.inr ()) k1 = Sum.inl 1)
    (hA0 : F.arc (Sum.inr ()) k0 = lowerOuterArc a b)
    (hA1 : F.arc (Sum.inr ()) k1 = upperOuterArc a b) :
    2 + 2 * (a + b) - 6 * ε ≤
      pairArcSum F ε (Sum.inl 0) (Sum.inr ()) +
        pairArcSum F ε (Sum.inl 1) (Sum.inr ()) := by
  have h0 := arcVariation_le_pairArcSum F hε (Sum.inr ()) (Sum.inl 0) k0 hp0
  have h1 := arcVariation_le_pairArcSum F hε (Sum.inr ()) (Sum.inl 1) k1 hp1
  rw [hA0] at h0
  rw [hA1] at h1
  rw [pairArcSum_symm F ε (Sum.inl 0) (Sum.inr ()),
    pairArcSum_symm F ε (Sum.inl 1) (Sum.inr ())]
  linarith [lowerOuterArc_variation_lower ha hb hε,
    upperOuterArc_variation_lower ha hb hε]

end

end Puzzling139335.N4MiddleInvolutions.BoundaryBalance
