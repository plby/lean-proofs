import StackExchange.Puzzling139335.N4MiddleInvolutions.BoundaryBalance.Matching
import StackExchange.Puzzling139335.HalfTurnRemainder.Variation.BoundaryBounds

/-!
# Actual interface sums and finite boundary balance

Each sum is taken over the arcs of the actual exact boundary partition.
The mate involution proves that an interface has the same intrinsic variation
when counted from either of its two regions.
-/

open Set

namespace Puzzling139335.N4MiddleInvolutions.BoundaryBalance

open HalfTurnRemainder LoopVariation

noncomputable section

/-- The intrinsic variations of the actual arcs on boundary `i` whose named
partner is `j`. -/
def pairArcSum {d : SquareDissection} (F : ExactBoundaryArcFamily d)
    (ε : ℝ) (i j : ExtendedPieceIndex) : ℝ :=
  ∑ k : Fin (F.n i), if F.partner i k = j then arcVariation ε (F.arc i k) else 0

theorem pairArcSum_nonneg {d : SquareDissection} (F : ExactBoundaryArcFamily d)
    {ε : ℝ} (hε : 0 < ε) (i j : ExtendedPieceIndex) :
    0 ≤ pairArcSum F ε i j := by
  apply Finset.sum_nonneg
  intro k _
  split_ifs
  · exact arcVariation_nonneg (F.arc_between i k).isArc hε
  · exact le_rfl

/-- A boundary never names itself as the partner of an interface arc. -/
@[simp] theorem pairArcSum_self {d : SquareDissection} (F : ExactBoundaryArcFamily d)
    (ε : ℝ) (i : ExtendedPieceIndex) : pairArcSum F ε i i = 0 := by
  simp [pairArcSum, F.partner_ne]

/-- The actual mate involution matches the two copies of each interface,
preserving their geometric carriers and hence their intrinsic variations. -/
theorem pairArcSum_symm {d : SquareDissection} (F : ExactBoundaryArcFamily d)
    (ε : ℝ) (i j : ExtendedPieceIndex) :
    pairArcSum F ε i j = pairArcSum F ε j i := by
  exact interfaceWeight_symm F (fun a => arcVariation ε (F.carrier a))
    (fun a => congrArg (arcVariation ε) (F.carrier_mate a)) i j

/-- Every actual boundary arc is counted in exactly one partner sum. -/
theorem boundaryArcSum_eq_sum_pairArcSum {d : SquareDissection}
    (F : ExactBoundaryArcFamily d) (ε : ℝ) (i : ExtendedPieceIndex) :
    boundaryArcSum F ε i = ∑ j : ExtendedPieceIndex, pairArcSum F ε i j := by
  exact rowSum_eq_sum_interfaceWeight F (fun a => arcVariation ε (F.carrier a)) i

/-- The exact signed identity for the four actual boundary sums.  Interfaces
between the two chosen pairs cancel, while each interface within a pair is
counted twice. -/
theorem boundaryArcSum_signed_identity {d : SquareDissection}
    (F : ExactBoundaryArcFamily d) (ε : ℝ) :
    boundaryArcSum F ε (Sum.inl 0) + boundaryArcSum F ε (Sum.inl 1) -
        boundaryArcSum F ε (Sum.inl 2) - boundaryArcSum F ε (Sum.inl 3) =
      2 * pairArcSum F ε (Sum.inl 0) (Sum.inl 1) -
        2 * pairArcSum F ε (Sum.inl 2) (Sum.inl 3) +
        pairArcSum F ε (Sum.inl 0) (Sum.inr ()) +
        pairArcSum F ε (Sum.inl 1) (Sum.inr ()) -
        pairArcSum F ε (Sum.inl 2) (Sum.inr ()) -
        pairArcSum F ε (Sum.inl 3) (Sum.inr ()) := by
  have hbalance := signed_rowSum_balance F (fun a => arcVariation ε (F.carrier a))
    (fun a => congrArg (arcVariation ε) (F.carrier_mate a))
  change boundaryArcSum F ε (Sum.inl 0) + boundaryArcSum F ε (Sum.inl 1) -
      boundaryArcSum F ε (Sum.inl 2) - boundaryArcSum F ε (Sum.inl 3) =
    pairArcSum F ε (Sum.inl 0) (Sum.inr ()) +
      pairArcSum F ε (Sum.inl 1) (Sum.inr ()) -
      pairArcSum F ε (Sum.inl 2) (Sum.inr ()) -
      pairArcSum F ε (Sum.inl 3) (Sum.inr ()) +
      2 * (pairArcSum F ε (Sum.inl 0) (Sum.inl 1) -
        pairArcSum F ε (Sum.inl 2) (Sum.inl 3)) at hbalance
  linarith

/-- Congruence makes the four loop variations equal.  Their actual arc sums
can differ only by their finite partition penalties. -/
theorem boundaryArcSum_signed_bounds {d : SquareDissection}
    (F : ExactBoundaryArcFamily d) (hparams : F.HasLoopParameters)
    {ε : ℝ} (hε : 0 < ε) :
    -((F.n (Sum.inl 0) : ℝ) + (F.n (Sum.inl 1) : ℝ)) * ε ≤
        boundaryArcSum F ε (Sum.inl 0) + boundaryArcSum F ε (Sum.inl 1) -
          boundaryArcSum F ε (Sum.inl 2) - boundaryArcSum F ε (Sum.inl 3) ∧
      boundaryArcSum F ε (Sum.inl 0) + boundaryArcSum F ε (Sum.inl 1) -
          boundaryArcSum F ε (Sum.inl 2) - boundaryArcSum F ε (Sum.inl 3) ≤
        ((F.n (Sum.inl 2) : ℝ) + (F.n (Sum.inl 3) : ℝ)) * ε := by
  have hb (i : Fin 4) :
      boundaryArcSum F ε (Sum.inl i) ≤ loopVariation ε (frontier (d.piece 0)) ∧
        loopVariation ε (frontier (d.piece 0)) ≤
          boundaryArcSum F ε (Sum.inl i) + (F.n (Sum.inl i) : ℝ) * ε := by
    have hi := boundaryArcSum_bounds F hparams hε (Sum.inl i)
    change boundaryArcSum F ε (Sum.inl i) ≤ loopVariation ε (frontier (d.piece i)) ∧
      loopVariation ε (frontier (d.piece i)) ≤
        boundaryArcSum F ε (Sum.inl i) + (F.n (Sum.inl i) : ℝ) * ε at hi
    rwa [piece_boundary_variation_eq d ε i 0] at hi
  have h₀ := hb 0
  have h₁ := hb 1
  have h₂ := hb 2
  have h₃ := hb 3
  constructor <;> nlinarith [h₀.1, h₀.2, h₁.1, h₁.2, h₂.1, h₂.2, h₃.1, h₃.2]

/-- The absolute signed discrepancy is bounded by one resolution penalty per
arc of the four actual piece boundaries. -/
theorem boundaryArcSum_signed_abs_le {d : SquareDissection}
    (F : ExactBoundaryArcFamily d) (hparams : F.HasLoopParameters)
    {ε : ℝ} (hε : 0 < ε) :
    |boundaryArcSum F ε (Sum.inl 0) + boundaryArcSum F ε (Sum.inl 1) -
        boundaryArcSum F ε (Sum.inl 2) - boundaryArcSum F ε (Sum.inl 3)| ≤
      ((F.n (Sum.inl 0) : ℝ) + (F.n (Sum.inl 1) : ℝ) +
        (F.n (Sum.inl 2) : ℝ) + (F.n (Sum.inl 3) : ℝ)) * ε := by
  have hbounds := boundaryArcSum_signed_bounds F hparams hε
  have hleft : 0 ≤ ((F.n (Sum.inl 0) : ℝ) + (F.n (Sum.inl 1) : ℝ)) * ε := by
    positivity
  have hright : 0 ≤ ((F.n (Sum.inl 2) : ℝ) + (F.n (Sum.inl 3) : ℝ)) * ε := by
    positivity
  rw [abs_le]
  constructor <;> nlinarith [hbounds.1, hbounds.2]

/-- The difference between the middle-pair interface contribution and the
outer-pair interface plus signed exterior contribution tends to zero with
the resolution, with an explicit finite bound from the actual partitions. -/
theorem pairArcSum_balance_abs_le {d : SquareDissection}
    (F : ExactBoundaryArcFamily d) (hparams : F.HasLoopParameters)
    {ε : ℝ} (hε : 0 < ε) :
    |2 * pairArcSum F ε (Sum.inl 2) (Sum.inl 3) -
      (2 * pairArcSum F ε (Sum.inl 0) (Sum.inl 1) +
        pairArcSum F ε (Sum.inl 0) (Sum.inr ()) +
        pairArcSum F ε (Sum.inl 1) (Sum.inr ()) -
        pairArcSum F ε (Sum.inl 2) (Sum.inr ()) -
        pairArcSum F ε (Sum.inl 3) (Sum.inr ()))| ≤
      ((F.n (Sum.inl 0) : ℝ) + (F.n (Sum.inl 1) : ℝ) +
        (F.n (Sum.inl 2) : ℝ) + (F.n (Sum.inl 3) : ℝ)) * ε := by
  have herror :
      2 * pairArcSum F ε (Sum.inl 2) (Sum.inl 3) -
        (2 * pairArcSum F ε (Sum.inl 0) (Sum.inl 1) +
          pairArcSum F ε (Sum.inl 0) (Sum.inr ()) +
          pairArcSum F ε (Sum.inl 1) (Sum.inr ()) -
          pairArcSum F ε (Sum.inl 2) (Sum.inr ()) -
          pairArcSum F ε (Sum.inl 3) (Sum.inr ())) =
        -(boundaryArcSum F ε (Sum.inl 0) + boundaryArcSum F ε (Sum.inl 1) -
          boundaryArcSum F ε (Sum.inl 2) - boundaryArcSum F ε (Sum.inl 3)) := by
    linarith [boundaryArcSum_signed_identity F ε]
  rw [herror, abs_neg]
  exact boundaryArcSum_signed_abs_le F hparams hε

end

end Puzzling139335.N4MiddleInvolutions.BoundaryBalance
