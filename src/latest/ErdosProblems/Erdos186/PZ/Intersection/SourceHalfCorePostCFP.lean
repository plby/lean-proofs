/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.SourceSpecializedMassNumerics

/-!
# Post-CFP assembly from the terminal half-core invariant

The actual irreducible-replacement output retains at least half of its
terminal population in the selected core.  This gives the high-coefficient
mass budget directly, without first controlling the selected loss or exposing
the terminal ambient dimension.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

namespace Theorem4PostCFPData

/-- Bounded-support post-CFP construction specialized to the terminal
half-core invariant.  The mass premise is derived internally from
`core ≥ N/2`, `mu*N ≥ 32`, and `delta < mu/8`. -/
def ofHighCoefficientSource_halfCore
    {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context)
    {ambient : ℕ} {A : Finset (LatticePoint ambient)}
    {hA : selector.Eligible A}
    {delta gamma mu : ℝ}
    {a₀ : realImage (selector.chosen A hA).identifiedCore}
    {c : realImage (selector.chosen A hA).identifiedCore → ℝ}
    (D : ConvexPoolsData (selector.chosen A hA).identifiedCore a₀ c mu)
    (hirr : Reduction.IsBoundedCoordinateIrreducible selector A hA
      delta gamma)
    (hclosed : selector.CandidateClosedAt A hA delta)
    (hcoreRetention : delta * (A.card : ℝ) ≤
      ((((selector.chosen A hA).identifiedCore.card - 2) / 2 : ℕ) : ℝ))
    (hhalf : (1 / 2 : ℝ) * (A.card : ℝ) ≤
      ((selector.chosen A hA).identifiedCore.card : ℝ))
    (hpopulation : 32 / mu ≤ (A.card : ℝ))
    (hdeltaMu : delta < mu / 8)
    (hdelta : 0 < delta) (hmu : 0 < mu) (hgamma : 0 < gamma) :
    let theta := sourceCoefficientThreshold A.card
    let hcap : 0 < (mu *
        (selector.chosen A hA).identifiedCore.card)⁻¹ :=
      inv_mu_mul_coreCard_pos_of_coreRetention
        (selector.eligible_nonempty hA).card_pos hdelta hmu hcoreRetention
    let E := chooseHighCoefficientSideSelectionData selector D hirr hclosed
      hdelta (sourceCoefficientThreshold_pos
        (selector.eligible_nonempty hA).card_pos).le hcap
      (highCoefficient_massBudget_of_halfCore
        (selector.eligible_nonempty hA).card_pos hmu hdeltaMu hhalf hpopulation)
    HighCoefficientBoundedSupportScalarHierarchies E →
    (∀ y : Fin (selector.chosen A hA).dimension → ℝ,
      (∀ i, |y i| ≤
        (3 * E.commonCoveringRadius + 2 : ℕ) + E.forwardCenterError) →
      y ∈ centeredZonotope E.forwardRoundingCore
        (D.scaledForwardCoefficient (highCoefficientZonotopeScale D))) →
    (∀ y : Fin (selector.chosen A hA).dimension → ℝ,
      (∀ i, |y i| ≤
        (3 * E.commonCoveringRadius + 2 : ℕ) + E.reverseCenterError) →
      y ∈ centeredZonotope E.reverseRoundingCore
        (D.scaledReverseCoefficient (highCoefficientZonotopeScale D))) →
    { Dout : Theorem4PostCFPData
        (selector.chosen A hA).identifiedCore // Dout.a = D.a } := by
  dsimp only
  intro Hscalar hthick₁ hthick₂
  exact ofHighCoefficientSource_boundedSupport selector D hirr hclosed
    hcoreRetention hdelta hmu
    (sourceCoefficientThreshold_pos
      (selector.eligible_nonempty hA).card_pos).le
    hgamma
    (inv_mu_mul_coreCard_pos_of_coreRetention
      (selector.eligible_nonempty hA).card_pos hdelta hmu hcoreRetention)
    (highCoefficient_massBudget_of_halfCore
      (selector.eligible_nonempty hA).card_pos hmu hdeltaMu hhalf hpopulation)
    Hscalar hthick₁ hthick₂

end Theorem4PostCFPData

end

end Erdos186.PZ.Intersection
