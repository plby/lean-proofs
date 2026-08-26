import ErdosProblems.Erdos747.AggregateBaseRegularity

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Deterministic bridges out of aggregate layer regularity -/

/-- A positive Kahn logarithmic lower bound certifies that the perfect
matching finset is nonempty.  The positivity hypothesis is kept explicit
because `Real.log 0 = 0` in Mathlib. -/
lemma perfectMatchings_card_ne_zero_of_kahnCountLower
    {n : ℕ} {H : Finset (Edge n)} {C : ℝ}
    (hpositive :
      0 < (n : ℝ) * Real.log ((H.card : ℝ) / n) -
        2 * (n : ℝ) - C * (n : ℝ))
    (hcount : KahnCountLower H C) :
    (perfectMatchings n H).card ≠ 0 := by
  intro hzero
  unfold KahnCountLower at hcount
  rw [hzero] at hcount
  norm_num at hcount
  linarith

/-- Aggregate layer regularity, a positive count lower bound, and sample
membership form the aggregate insertion certificate used by the entropy
argument. -/
lemma kahnAggregateInsertionGood_of_aggregateLayerRegular
    {n M codegCap : ℕ} {a B q etaDeg Bdeg C₀ : ℝ}
    {H : Finset (Edge n)}
    (hH : H ∈ sample n M)
    (hregular : AggregateLayerRegular n M codegCap
      a B q etaDeg Bdeg H)
    (hpositive :
      0 < (n : ℝ) * Real.log ((M : ℝ) / n) -
        2 * (n : ℝ) - C₀ * (n : ℝ))
    (hcount : KahnCountLower H C₀) :
    KahnAggregateInsertionGood n M codegCap C₀
      q etaDeg Bdeg H := by
  have hcard : H.card = M := (mem_sample.mp hH).2
  have hpositive' :
      0 < (n : ℝ) * Real.log ((H.card : ℝ) / n) -
        2 * (n : ℝ) - C₀ * (n : ℝ) := by
    simpa only [hcard] using hpositive
  have hPhi := perfectMatchings_card_ne_zero_of_kahnCountLower
    hpositive' hcount
  have hpm : HasPerfectMatching n H :=
    hasPerfectMatching_iff_perfectMatchings_nonempty.mpr
      (Finset.card_ne_zero.mp hPhi)
  exact ⟨hH, hpm, hcount, hregular.2.2.1, hregular.2.2.2⟩

/-- The same base certificate supplies the parent half of residual
aggregate inheritance.  All losses caused by deleting one triple are
isolated as explicit numerical hypotheses, so later asymptotic parameter
selection has no hidden combinatorial obligations. -/
lemma residualAggregateInheritanceGood_of_aggregateLayerRegular
    {n M d D codegCap : ℕ}
    {a B q etaDeg Bdeg c C₀ C₁ q₁ etaDeg₁ Bdeg₁ : ℝ}
    {H : Finset (Edge n)}
    (hH : H ∈ sample n M)
    (hregular : AggregateLayerRegular n M codegCap
      a B q etaDeg Bdeg H)
    (hpositive :
      0 < (n : ℝ) * Real.log ((M : ℝ) / n) -
        2 * (n : ℝ) - C₀ * (n : ℝ))
    (hcount : KahnCountLower H C₀)
    (hdegreeLower :
      (((d + 3 * codegCap : ℕ) : ℝ)) ≤ a * ((M : ℝ) / n))
    (hdegreeUpper : B * ((M : ℝ) / n) ≤ (D : ℝ))
    (hcountBudget : ∀ (Z : Edge n) (hZ : Z ∈ allEdges n),
      c^2 * matchingWeightTarget n H ≤ completionWeight H Z →
      ((n - 1 : ℕ) : ℝ) *
            Real.log (((reindexGraphAway H Z hZ).card : ℝ) /
              (n - 1 : ℕ)) -
          2 * ((n - 1 : ℕ) : ℝ) - C₁ * ((n - 1 : ℕ) : ℝ) ≤
        ((n : ℝ) * Real.log ((M : ℝ) / n) -
          2 * (n : ℝ) - C₀ * (n : ℝ)) +
          Real.log (c^2 * (n : ℝ) / M))
    (haggregateLower : ∀ (Z : Edge n) (hZ : Z ∈ allEdges n),
      (1 - q₁) *
          (((reindexGraphAway H Z hZ).card : ℝ) / (n - 1 : ℕ)) ≤
        (1 - q) * ((M : ℝ) / n) - 3 * codegCap)
    (haggregateUpper : ∀ (Z : Edge n) (hZ : Z ∈ allEdges n),
      (1 + q) * ((M : ℝ) / n) ≤
        (1 + q₁) *
          (((reindexGraphAway H Z hZ).card : ℝ) / (n - 1 : ℕ)))
    (haggregateEta :
      etaDeg * (3 * n : ℝ) ≤
        etaDeg₁ * (3 * ((n - 1 : ℕ) : ℝ)))
    (haggregateB : ∀ (Z : Edge n) (hZ : Z ∈ allEdges n),
      Bdeg * ((M : ℝ) / n) ≤
        Bdeg₁ *
          (((reindexGraphAway H Z hZ).card : ℝ) / (n - 1 : ℕ))) :
    ResidualAggregateInheritanceGood n M d D codegCap
      c C₀ C₁ q₁ etaDeg₁ Bdeg₁ H := by
  have hcard : H.card = M := (mem_sample.mp hH).2
  have hpositive' :
      0 < (n : ℝ) * Real.log ((H.card : ℝ) / n) -
        2 * (n : ℝ) - C₀ * (n : ℝ) := by
    simpa only [hcard] using hpositive
  have hPhi := perfectMatchings_card_ne_zero_of_kahnCountLower
    hpositive' hcount
  refine ⟨hPhi, hcount, ?_, ?_, hregular.2.2.1, ?_⟩
  · intro v
    have hlower := hregular.1 v
    have hcast : ((d + 3 * codegCap : ℕ) : ℝ) <
        (vertexDegree H v : ℝ) := hdegreeLower.trans_lt hlower
    have hnat : d + 3 * codegCap < vertexDegree H v := by
      exact_mod_cast hcast
    omega
  · intro v
    have hupper := hregular.2.1 v
    have hcast : (vertexDegree H v : ℝ) < (D : ℝ) :=
      hupper.trans_le hdegreeUpper
    have hnat : vertexDegree H v < D := by exact_mod_cast hcast
    omega
  · intro Z hZ hweight
    refine ⟨hcountBudget Z hZ hweight, ?_⟩
    exact degreeAggregateRegular_reindexGraphAway hZ hcard
      q etaDeg Bdeg q₁ etaDeg₁ Bdeg₁ hregular.2.2.1
      hregular.2.2.2 (haggregateLower Z hZ)
      (haggregateUpper Z hZ) haggregateEta (haggregateB Z hZ)

end

end Erdos747
