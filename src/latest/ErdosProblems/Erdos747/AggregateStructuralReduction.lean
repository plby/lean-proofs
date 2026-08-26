import ErdosProblems.Erdos747.ResidualAggregateInheritance

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Reduction of a structural layer to aggregate spreading events -/

/-- The residual aggregate package and high residual lower spreading imply
the coordinate-transfer certificate once the purely numerical cutoff,
exception, and adaptive-tail estimates have been checked. -/
lemma coordinateTransferRegularAwayAboveMax_of_residualAggregate
    {n M d D codegCap Q b B e₁ : ℕ}
    {c C₀ C₁ q₁ etaDeg₁ Bdeg₁ L eta : ℝ}
    {H : Finset (Edge n)}
    (hn : 2 ≤ n) (hM0 : 0 < M) (hH : H ∈ sample n M)
    (hresidual : ResidualAggregateInheritanceGood
      n M d D codegCap c C₀ C₁ q₁ etaDeg₁ Bdeg₁ H)
    (hdb : b < d) (hJpos : 0 < M - 3 * D)
    (hspread : HighResidualLowerSpread n H c L eta)
    (hcutoff : ∀ (Z : Edge n) (hZ : Z ∈ allEdges n),
      c * ((reindexGraphAway H Z hZ).card : ℝ) ≤
        L * ((d - b : ℕ) : ℝ) * ((n - 1 : ℕ) : ℝ))
    (hbadBudget : eta * (allEdges (n - 1)).card ≤ B)
    (htail : ∀ Z ∈ allEdges n, ∀ x ∈ Z,
      (coordinateLinkTailVertices Z x
        (residualTransferCutoff Z c d b (inducedAway H Z))
        d D Q (b + 1) H).card ≤ e₁) :
    CoordinateTransferRegularAwayAboveMax
      n H c d D codegCap Q b B e₁ := by
  rcases hresidual with
    ⟨hPhi, hcount, hdegreeLower, hdegreeUpper, hcodeg, hinherit⟩
  apply coordinateTransferRegularAwayAboveMax_of_residualSpread
    hn hH hdegreeLower hdegreeUpper hcodeg hdb
  · intro Z hZ
    exact lt_of_lt_of_le hJpos
      (card_reindexGraphAway_lower hZ (mem_sample.mp hH).2
        (fun z hz ↦ hdegreeUpper z))
  · exact hspread
  · exact hcutoff
  · exact hbadBudget
  · exact htail

/-- An abstract standard certificate used to isolate the few pathwise
degree/codegree estimates from the two entropy-spreading estimates. -/
def AggregateLayerBase (n M : ℕ) (H : Finset (Edge n)) : Prop :=
  H ∈ sample n M

/-- If a base certificate turns a count-good graph into both aggregate
insertion packages, and high residual spreading turns the residual package
into coordinate transfer, then failure of the whole Kahn layer is contained
in exactly three events: base failure, upper-spread failure, or residual
lower-spread failure. -/
lemma kahnLayerInput_failure_probability_le_aggregate
    {n M d D codegCap Q b B e₁ : ℕ}
    {C₀ C₁ L eta cTransfer q etaDeg Bdeg q₁ etaDeg₁ Bdeg₁
      Lres etaRes : ℝ}
    (Base : Finset (Edge n) → Prop)
    (hupper : ∀ H ∈ sample n M, Base H → KahnCountLower H C₀ →
      KahnAggregateInsertionGood n M codegCap C₀ q etaDeg Bdeg H)
    (hresidual : ∀ H ∈ sample n M, Base H → KahnCountLower H C₀ →
      ResidualAggregateInheritanceGood n M d D codegCap
        cTransfer C₀ C₁ q₁ etaDeg₁ Bdeg₁ H)
    (hcoordinate : ∀ H ∈ sample n M,
      ResidualAggregateInheritanceGood n M d D codegCap
          cTransfer C₀ C₁ q₁ etaDeg₁ Bdeg₁ H →
        HighResidualLowerSpread n H cTransfer Lres etaRes →
          CoordinateTransferRegularAwayAboveMax
            n H cTransfer d D codegCap Q b B e₁) :
    finsetProbability (sample n M)
        (fun H ↦ ¬ KahnLayerInput n d D codegCap Q b B e₁
          C₀ L eta cTransfer H) ≤
      finsetProbability (sample n M)
        (fun H ↦ KahnCountLower H C₀ ∧ ¬ Base H) +
      finsetProbability (sample n M)
        (fun H ↦ KahnAggregateInsertionGood n M codegCap C₀
          q etaDeg Bdeg H ∧ ¬ GlobalUpperWeightSpread n H L eta) +
      finsetProbability (sample n M)
        (fun H ↦ ResidualAggregateInheritanceGood
            n M d D codegCap cTransfer C₀ C₁ q₁ etaDeg₁ Bdeg₁ H ∧
          ¬ HighResidualLowerSpread n H cTransfer Lres etaRes) := by
  let E₀ : Finset (Edge n) → Prop := fun H ↦
    KahnCountLower H C₀ ∧ ¬ Base H
  let E₁ : Finset (Edge n) → Prop := fun H ↦
    KahnAggregateInsertionGood n M codegCap C₀ q etaDeg Bdeg H ∧
      ¬ GlobalUpperWeightSpread n H L eta
  let E₂ : Finset (Edge n) → Prop := fun H ↦
    ResidualAggregateInheritanceGood n M d D codegCap
        cTransfer C₀ C₁ q₁ etaDeg₁ Bdeg₁ H ∧
      ¬ HighResidualLowerSpread n H cTransfer Lres etaRes
  change finsetProbability (sample n M)
      (fun H ↦ ¬ KahnLayerInput n d D codegCap Q b B e₁
        C₀ L eta cTransfer H) ≤
    finsetProbability (sample n M) E₀ +
      finsetProbability (sample n M) E₁ +
      finsetProbability (sample n M) E₂
  calc
    finsetProbability (sample n M)
        (fun H ↦ ¬ KahnLayerInput n d D codegCap Q b B e₁
          C₀ L eta cTransfer H) ≤
      finsetProbability (sample n M) (fun H ↦ E₀ H ∨ E₁ H ∨ E₂ H) := by
        apply finsetProbability_mono_event
        intro H hHs hfail
        unfold KahnLayerInput at hfail
        push Not at hfail
        rcases hfail with ⟨hcount, hnot⟩
        by_cases hbase : Base H
        · have hu := hupper H hHs hbase hcount
          have hr := hresidual H hHs hbase hcount
          by_cases hglobal : GlobalUpperWeightSpread n H L eta
          · by_cases hhigh : HighResidualLowerSpread n H cTransfer Lres etaRes
            · exact False.elim
                (hnot hglobal (hcoordinate H hHs hr hhigh))
            · exact Or.inr (Or.inr ⟨hr, hhigh⟩)
          · exact Or.inr (Or.inl ⟨hu, hglobal⟩)
        · exact Or.inl ⟨hcount, hbase⟩
    _ ≤ finsetProbability (sample n M) E₀ +
          finsetProbability (sample n M) E₁ +
          finsetProbability (sample n M) E₂ := by
      calc
        finsetProbability (sample n M) (fun H ↦ E₀ H ∨ E₁ H ∨ E₂ H) ≤
            finsetProbability (sample n M) E₀ +
              finsetProbability (sample n M) (fun H ↦ E₁ H ∨ E₂ H) :=
          finsetProbability_or_le_add _ _ _
        _ ≤ finsetProbability (sample n M) E₀ +
            (finsetProbability (sample n M) E₁ +
              finsetProbability (sample n M) E₂) :=
          add_le_add le_rfl
            (finsetProbability_or_le_add (sample n M) E₁ E₂)
        _ = _ := by ring

end

end Erdos747
