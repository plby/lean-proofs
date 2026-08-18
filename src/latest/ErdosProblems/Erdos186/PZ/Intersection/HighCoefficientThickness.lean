/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.LargeCoefficientPool
import ErdosProblems.Erdos186.PZ.Intersection.SourceCenterError
import ErdosProblems.Erdos186.PZ.Intersection.ZonotopeSeparation

/-!
# High-coefficient input for zonotope thickness

This file connects the high-coefficient pools used by the source selection
to the variable radii of the centered zonotope.  It also records the exact
finite loss calculation: after the CFP discarded and reserved generators
and a narrow functional slab are removed, all remaining generators still
have a uniform positive radius.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators

noncomputable section

set_option autoImplicit false

namespace ConvexPoolsData

variable {d : ℕ} {A : Finset (LatticePoint d)}
    {a₀ : realImage A} {c : realImage A → ℝ} {mu : ℝ}

/-- The centered-zonotope radius on the forward deviation set. -/
def scaledForwardCoefficient (D : ConvexPoolsData A a₀ c mu)
    (scale : ℝ) (y : LatticePoint d) : ℝ :=
  scale * D.forwardCoefficient y

/-- Membership in the translated high-coefficient pool retains the
coefficient lower bound. -/
theorem forwardCoefficient_lower_of_mem_identifiedTranslate_largeA₁
    (D : ConvexPoolsData A a₀ c mu) {theta : ℝ} {y : LatticePoint d}
    (hy : y ∈ Reduction.identifiedTranslate (D.largeA₁ theta) D.a) :
    theta ≤ D.forwardCoefficient y := by
  rw [Reduction.identifiedTranslate, PZ.translate, Finset.mem_image] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  simpa [forwardCoefficient, sub_eq_add_neg] using
    D.coefficient_lower_largeA₁ hx

/-- The canonical rounding core of a witness selected on the translated
high-coefficient pool has uniformly positive forward radii. -/
theorem scaledForwardCoefficient_lower_on_canonicalRoundingCore
    (D : ConvexPoolsData A a₀ c mu) {theta scale : ℝ}
    (hscale : 0 ≤ scale) {s Dmax k loss : ℕ}
    (W : CFP.EnhancedCFPWitness
      (Reduction.identifiedTranslate (D.largeA₁ theta) D.a)
      s Dmax k loss) :
    ∀ y ∈ canonicalRoundingCore W,
      scale * theta ≤ D.scaledForwardCoefficient scale y := by
  intro y hy
  dsimp only [scaledForwardCoefficient]
  exact mul_le_mul_of_nonneg_left
    (D.forwardCoefficient_lower_of_mem_identifiedTranslate_largeA₁
      (W.core_subset (canonicalRoundingCore_subset_core W hy))) hscale

/-- The same radii are nonnegative and inherit the original coefficient
cap. -/
theorem scaledForwardCoefficient_bounds_on_canonicalRoundingCore
    (D : ConvexPoolsData A a₀ c mu) {theta scale : ℝ}
    (hscale : 0 ≤ scale) {s Dmax k loss : ℕ}
    (W : CFP.EnhancedCFPWitness
      (Reduction.identifiedTranslate (D.largeA₁ theta) D.a)
      s Dmax k loss) :
    ∀ y ∈ canonicalRoundingCore W,
      0 ≤ D.scaledForwardCoefficient scale y ∧
        D.scaledForwardCoefficient scale y ≤
          scale * (mu * A.card)⁻¹ := by
  intro y hy
  have hyInput : y ∈
      Reduction.identifiedTranslate (D.largeA₁ theta) D.a :=
    W.core_subset (canonicalRoundingCore_subset_core W hy)
  rw [Reduction.identifiedTranslate, PZ.translate, Finset.mem_image] at hyInput
  obtain ⟨x, hx, rfl⟩ := hyInput
  have hxA₁ : x ∈ D.A₁ := D.largeA₁_subset theta hx
  have hb := D.coefficient_bounds_A₁ hxA₁
  have hb' : 0 ≤ D.forwardCoefficient (x - D.a) ∧
      D.forwardCoefficient (x - D.a) ≤ (mu * A.card)⁻¹ := by
    simpa [forwardCoefficient, sub_eq_add_neg] using hb
  dsimp only [scaledForwardCoefficient]
  exact ⟨mul_nonneg hscale hb'.1,
    mul_le_mul_of_nonneg_left hb'.2 hscale⟩

end ConvexPoolsData

/-- Removing at most `missing` input points and then at most `slab` core
points leaves the displayed number of points outside the slab. -/
theorem card_sub_missing_slab_le_filter_ge
    {α : Type*} [DecidableEq α]
    (input core : Finset α) (hcore : core ⊆ input)
    (p : α → Prop) [DecidablePred p]
    (missing slab : ℕ)
    (hmissing : (input \ core).card ≤ missing)
    (hslab : (core.filter fun x ↦ ¬ p x).card ≤ slab) :
    input.card - (missing + slab) ≤ (core.filter p).card := by
  have hinput : input.card ≤ core.card + missing := by
    rw [Finset.card_sdiff_of_subset hcore] at hmissing
    omega
  have hsplit := core.card_filter_add_card_filter_not p
  omega

/-- A uniform lower radius turns the surviving outside-slab cardinality
into weighted mass. -/
theorem minRadius_mul_card_filter_le_sum
    {α : Type*} [DecidableEq α]
    (core : Finset α) (q : α → ℝ) (p : α → Prop) [DecidablePred p]
    (minRadius : ℝ) (hq : ∀ x ∈ core, minRadius ≤ q x) :
    minRadius * ((core.filter p).card : ℝ) ≤
      ∑ x ∈ core.filter p, q x := by
  calc
    minRadius * ((core.filter p).card : ℝ) =
        ∑ _x ∈ core.filter p, minRadius := by simp [mul_comm]
    _ ≤ ∑ x ∈ core.filter p, q x := by
      apply Finset.sum_le_sum
      intro x hx
      exact hq x (Finset.mem_filter.mp hx).1

namespace ConvexPoolsData

variable {d : ℕ} {A : Finset (LatticePoint d)}
    {a₀ : realImage A} {c : realImage A → ℝ} {mu : ℝ}

/-- Once irreducibility bounds every narrow functional slab, the canonical
high-coefficient CFP core contains the requested coordinate cube.  The
remaining displayed inequality is purely scalar and is where the source
parameter hierarchy is used. -/
theorem cube_subset_centeredZonotope_of_highCoefficient_slabCard
    (D : ConvexPoolsData A a₀ c mu) {theta scale radius : ℝ}
    (htheta : 0 ≤ theta) (hscale : 0 ≤ scale)
    {s Dmax k loss slab : ℕ}
    (W : CFP.EnhancedCFPWitness
      (Reduction.identifiedTranslate (D.largeA₁ theta) D.a)
      s Dmax k loss)
    (threshold : ((Fin d → ℝ) →L[ℝ] ℝ) → ℝ)
    (hthreshold : ∀ f, 0 ≤ threshold f)
    (hslab : ∀ f : (Fin d → ℝ) →L[ℝ] ℝ, f ≠ 0 →
      ((canonicalRoundingCore W).filter fun x ↦
        ¬threshold f ≤ |f (realVector x)|).card ≤ slab)
    (hnumeric : ∀ f : (Fin d → ℝ) →L[ℝ] ℝ, f ≠ 0 →
      radius * ∑ i, |f (Pi.single i 1)| ≤
        threshold f * (scale * theta *
          (((Reduction.identifiedTranslate (D.largeA₁ theta) D.a).card -
            (loss + s + slab) : ℕ) : ℝ))) :
    {y : Fin d → ℝ | ∀ i, |y i| ≤ radius} ⊆
      centeredZonotope (canonicalRoundingCore W)
        (D.scaledForwardCoefficient scale) := by
  let input := Reduction.identifiedTranslate (D.largeA₁ theta) D.a
  let core := canonicalRoundingCore W
  let q := D.scaledForwardCoefficient scale
  have hqnonneg : ∀ x ∈ core, 0 ≤ q x := by
    intro x hx
    exact (D.scaledForwardCoefficient_bounds_on_canonicalRoundingCore
      hscale W x hx).1
  apply cube_subset_centeredZonotope_of_outsideSlabMass
    core q hqnonneg radius threshold
  intro f
  by_cases hf : f = 0
  · subst f
    simp only [ContinuousLinearMap.zero_apply, abs_zero,
      Finset.sum_const_zero, mul_zero]
    exact mul_nonneg (hthreshold 0) (Finset.sum_nonneg fun x hx ↦
      hqnonneg x (Finset.mem_filter.mp hx).1)
  let outside := core.filter fun x ↦ threshold f ≤ |f (realVector x)|
  have hcardNat : input.card - ((loss + s) + slab) ≤ outside.card := by
    apply card_sub_missing_slab_le_filter_ge input core
      (canonicalRoundingCore_subset_input W)
      (fun x ↦ threshold f ≤ |f (realVector x)|) (loss + s) slab
    · exact card_sdiff_canonicalRoundingCore_le W
    · simpa only [core] using hslab f hf
  have hcardReal :
      (((input.card - (loss + s + slab) : ℕ) : ℝ)) ≤
        (outside.card : ℝ) := by
    exact_mod_cast hcardNat
  have hmass : scale * theta * (outside.card : ℝ) ≤
      ∑ x ∈ outside, q x := by
    apply minRadius_mul_card_filter_le_sum core q
      (fun x ↦ threshold f ≤ |f (realVector x)|) (scale * theta)
    intro x hx
    exact D.scaledForwardCoefficient_lower_on_canonicalRoundingCore
      hscale W x hx
  calc
    radius * ∑ i, |f (Pi.single i 1)| ≤
        threshold f * (scale * theta *
          (((input.card - (loss + s + slab) : ℕ) : ℝ))) := by
      simpa only [input] using hnumeric f hf
    _ ≤ threshold f * (scale * theta * (outside.card : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (hthreshold f)
      exact mul_le_mul_of_nonneg_left hcardReal
        (mul_nonneg hscale htheta)
    _ ≤ threshold f * (∑ x ∈ outside, q x) :=
      mul_le_mul_of_nonneg_left hmass (hthreshold f)

end ConvexPoolsData

end

end Erdos186.PZ.Intersection
