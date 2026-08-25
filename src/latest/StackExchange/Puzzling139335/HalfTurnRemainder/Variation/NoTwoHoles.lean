import StackExchange.Puzzling139335.HalfTurnRemainder.Variation.BoundaryBounds
import StackExchange.Puzzling139335.HalfTurnRemainder.Variation.Balance
import StackExchange.Puzzling139335.HalfTurnRemainder.NoHoleInterfaces

/-!
# Truncated variation excludes the actual two-hole configuration

Matching interface occurrences bounds the square's arc sum by the total
remaining arc sum minus the two hole sums. Congruence makes the four tile-loop
variations equal. Hence the square's loop variation is at most a fixed finite
multiple of `ε`, contradicting its positive lower bound as `ε` tends to zero.
All partitions and partner restrictions are derived from the actual dissection.
-/

open Set

namespace Puzzling139335.HalfTurnRemainder

open LoopVariation

noncomputable section

/-- If every exterior or omitted-tile interface matches a remaining-tile
interface, the outer boundary variation is bounded by a fixed penalty count. -/
theorem square_boundary_variation_le_penalty {d : SquareDissection}
    (F : ExactBoundaryArcFamily d) (hparams : F.HasLoopParameters)
    (hpartner : ∀ (i : ExtendedPieceIndex), i ≠ Sum.inl 0 → i ≠ Sum.inl 1 →
      ∀ k : Fin (F.n i), F.partner i k = Sum.inl 0 ∨ F.partner i k = Sum.inl 1)
    {ε : ℝ} (hε : 0 < ε) :
    loopVariation ε (frontier unitSquare) ≤
      ((F.n (Sum.inl 2) : ℝ) + (F.n (Sum.inl 3) : ℝ) +
        (F.n (Sum.inr ()) : ℝ)) * ε := by
  have hmatch := boundaryArcSum_balance_of_partner_restriction F hε hpartner
  have h₀ := (boundaryArcSum_bounds F hparams hε (Sum.inl 0)).1
  have h₁ := (boundaryArcSum_bounds F hparams hε (Sum.inl 1)).1
  have h₂ := (boundaryArcSum_bounds F hparams hε (Sum.inl 2)).2
  have h₃ := (boundaryArcSum_bounds F hparams hε (Sum.inl 3)).2
  have hext := (boundaryArcSum_bounds F hparams hε (Sum.inr ())).2
  change loopVariation ε (frontier closedSquareExterior) ≤
    boundaryArcSum F ε (Sum.inr ()) + (F.n (Sum.inr ()) : ℝ) * ε at hext
  rw [frontier_closedSquareExterior] at hext
  change boundaryArcSum F ε (Sum.inl 0) ≤ loopVariation ε (frontier (d.piece 0)) at h₀
  change boundaryArcSum F ε (Sum.inl 1) ≤ loopVariation ε (frontier (d.piece 1)) at h₁
  change loopVariation ε (frontier (d.piece 2)) ≤
    boundaryArcSum F ε (Sum.inl 2) + (F.n (Sum.inl 2) : ℝ) * ε at h₂
  change loopVariation ε (frontier (d.piece 3)) ≤
    boundaryArcSum F ε (Sum.inl 3) + (F.n (Sum.inl 3) : ℝ) * ε at h₃
  have h₀₂ := piece_boundary_variation_eq d ε 0 2
  have h₁₃ := piece_boundary_variation_eq d ε 1 3
  nlinarith

/-- Such an interface arrangement is impossible: the outer Jordan curve has
a positive small-resolution lower bound, while the finite error tends to zero. -/
theorem not_all_interface_partners_remaining {d : SquareDissection}
    (F : ExactBoundaryArcFamily d) (hparams : F.HasLoopParameters)
    (hpartner : ∀ (i : ExtendedPieceIndex), i ≠ Sum.inl 0 → i ≠ Sum.inl 1 →
      ∀ k : Fin (F.n i), F.partner i k = Sum.inl 0 ∨ F.partner i k = Sum.inl 1) : False := by
  obtain ⟨η, hη, hlower⟩ :=
    loopVariation_exists_positive_lower_bound isJordanCurve_frontier_unitSquare
  let K : ℝ := (F.n (Sum.inl 2) : ℝ) + (F.n (Sum.inl 3) : ℝ) +
    (F.n (Sum.inr ()) : ℝ)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hden : 0 < K + 1 := by linarith
  let ε : ℝ := η / (K + 1)
  have hε : 0 < ε := div_pos hη hden
  have hmul : (K + 1) * ε = η := by
    dsimp only [ε]
    field_simp [ne_of_gt hden]
  have hsmall : ε ≤ η := by nlinarith [mul_nonneg hK hε.le]
  have hlow := hlower ε hε hsmall
  have hupp : loopVariation ε (frontier unitSquare) ≤ K * ε :=
    square_boundary_variation_le_penalty F hparams hpartner hε
  nlinarith

/-- Two omitted congruent pieces cannot be precisely two complementary holes
of the other two pieces in an actual four-piece square dissection. -/
theorem two_hole_components_impossible (d : SquareDissection) {x₂ x₃ : Plane}
    (h₂ : connectedComponentIn (d.piece 0 ∪ d.piece 1)ᶜ x₂ = interior (d.piece 2))
    (h₃ : connectedComponentIn (d.piece 0 ∪ d.piece 1)ᶜ x₃ = interior (d.piece 3)) : False := by
  obtain ⟨F, _, hparams⟩ := d.exists_exact_boundary_arc_family
  exact not_all_interface_partners_remaining F hparams
    (partner_eq_zero_or_one_of_two_holes F h₂ h₃)

end

end Puzzling139335.HalfTurnRemainder
