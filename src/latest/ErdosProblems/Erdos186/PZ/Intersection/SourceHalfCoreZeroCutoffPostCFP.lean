/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.SourceHalfCorePostCFP

/-!
# Terminal half-core assembly at zero coefficient cutoff

At cutoff zero the two selected high pools are the complete alternating
coefficient pools.  This is the source-scale choice for weighted thickness:
it preserves the common balanced center and makes the low-coefficient
omission error vanish.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

/-- The half-core mass estimate at the source cutoff implies the weaker
selection budget at cutoff zero. -/
theorem highCoefficient_zeroCutoff_massBudget_of_halfCore
    {population core : ℕ} {delta mu : ℝ}
    (hpopulation : 0 < population) (hmu : 0 < mu)
    (hdeltaMu : delta < mu / 8)
    (hhalf : (1 / 2 : ℝ) * (population : ℝ) ≤ (core : ℝ))
    (hlarge : 32 / mu ≤ (population : ℝ)) :
    (population : ℝ) * 0 +
          delta * (population : ℝ) * (mu * core)⁻¹ <
      (1 - 2 * (mu * core)⁻¹) / 2 := by
  have H := highCoefficient_massBudget_of_halfCore hpopulation hmu
    hdeltaMu hhalf hlarge
  have htheta : 0 ≤ (population : ℝ) *
      sourceCoefficientThreshold population :=
    mul_nonneg (by positivity) (sourceCoefficientThreshold_pos hpopulation).le
  linarith

namespace ConvexPoolsData

variable {d : ℕ} {A : Finset (LatticePoint d)}
    {a₀ : realImage A} {c : realImage A → ℝ} {mu : ℝ}

/-- At cutoff zero, nonnegativity of the convex coefficients makes the
forward high pool equal to the complete alternating pool. -/
@[simp] theorem largeA₁_zero (D : ConvexPoolsData A a₀ c mu) :
    D.largeA₁ 0 = D.A₁ := by
  ext x
  rw [largeA₁, largeCoefficientPool, Finset.mem_filter]
  constructor
  · exact fun hx ↦ hx.1
  · intro hx
    exact ⟨hx, (D.coefficient_bounds_A₁ hx).1⟩

/-- Reverse counterpart of `largeA₁_zero`. -/
@[simp] theorem largeA₂_zero (D : ConvexPoolsData A a₀ c mu) :
    D.largeA₂ 0 = D.A₂ := by
  ext x
  rw [largeA₂, largeCoefficientPool, Finset.mem_filter]
  constructor
  · exact fun hx ↦ hx.1
  · intro hx
    exact ⟨hx, (D.coefficient_bounds_A₂ hx).1⟩

end ConvexPoolsData

namespace HighCoefficientSideSelectionData

variable {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    {ambient : ℕ} {A : Finset (LatticePoint ambient)}
    {hA : selector.Eligible A}
    {a₀ : realImage (selector.chosen A hA).identifiedCore}
    {c : realImage (selector.chosen A hA).identifiedCore → ℝ}
    {mu gamma : ℝ}
    {D : ConvexPoolsData (selector.chosen A hA).identifiedCore a₀ c mu}

/-- At cutoff zero the forward center error contains only the CFP
discard/reserve/translation error. -/
@[simp] theorem forwardCenterError_zero
    (E : HighCoefficientSideSelectionData selector hA D 0 gamma) :
    E.forwardCenterError =
      ((((E.side₁.loss + E.side₁.reserveBound : ℕ) : ℝ) *
          ((1 : ℝ) / 2 *
            (sourceCoordinateWidth
              (selector.chosen A hA).progression : ℝ))) +
        (E.side₁.reserveBound : ℝ) *
          (sourceCoordinateWidth
            (selector.chosen A hA).progression : ℝ)) := by
  simp [forwardCenterError]

/-- Reverse zero-cutoff center-error formula. -/
@[simp] theorem reverseCenterError_zero
    (E : HighCoefficientSideSelectionData selector hA D 0 gamma) :
    E.reverseCenterError =
      ((((E.side₂.loss + E.side₂.reserveBound : ℕ) : ℝ) *
          ((1 : ℝ) / 2 *
            (sourceCoordinateWidth
              (selector.chosen A hA).progression : ℝ))) +
        (E.side₂.reserveBound : ℝ) *
          (sourceCoordinateWidth
            (selector.chosen A hA).progression : ℝ)) := by
  simp [reverseCenterError]

end HighCoefficientSideSelectionData

namespace Theorem4PostCFPData

/-- Bounded-support post-CFP construction on the complete alternating pools,
encoded as high-coefficient pools at cutoff zero. -/
def ofFullCoefficientSource_halfCore
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
    let theta : ℝ := 0
    let hcap : 0 < (mu *
        (selector.chosen A hA).identifiedCore.card)⁻¹ :=
      inv_mu_mul_coreCard_pos_of_coreRetention
        (selector.eligible_nonempty hA).card_pos hdelta hmu hcoreRetention
    let hmass := highCoefficient_zeroCutoff_massBudget_of_halfCore
      (selector.eligible_nonempty hA).card_pos hmu hdeltaMu hhalf hpopulation
    let E := chooseHighCoefficientSideSelectionData selector D hirr hclosed
      hdelta (show (0 : ℝ) ≤ 0 by rfl) hcap hmass
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
    hcoreRetention hdelta hmu (show (0 : ℝ) ≤ 0 by rfl) hgamma
    (inv_mu_mul_coreCard_pos_of_coreRetention
      (selector.eligible_nonempty hA).card_pos hdelta hmu hcoreRetention)
    (highCoefficient_zeroCutoff_massBudget_of_halfCore
      (selector.eligible_nonempty hA).card_pos hmu hdeltaMu hhalf hpopulation)
    Hscalar hthick₁ hthick₂

end Theorem4PostCFPData

end

end Erdos186.PZ.Intersection
