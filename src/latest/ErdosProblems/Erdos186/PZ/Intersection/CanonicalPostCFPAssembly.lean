/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.CanonicalFullRank
import ErdosProblems.Erdos186.PZ.Intersection.SideTarget

/-!
# Canonical post-CFP assembly with the full-rank conclusion discharged

This file combines the source-faithful canonical targets from
`SideTarget.lean` with the projection-cardinality proof that their step
lattices have a common covering radius.  Consequently the theorem below has
no abstract Lemma 13, Lemma 14, lattice, or covering-radius input.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

namespace Theorem4PostCFPData

/-- The canonical two-side post-CFP datum, with full rank and the common
covering radius derived from controlled-box containment, retained volume,
and the explicit `k * gamma` hierarchy. -/
def ofCanonicalTargets_controlledBoxGammaHierarchy
    {d : ℕ} {A A₁ A₂ : Finset (LatticePoint (d + 1))}
    {a : LatticePoint (d + 1)}
    {s₁ D₁ k₁ loss₁ structuredDilation₁ margin₁ : ℕ}
    {s₂ D₂ k₂ loss₂ structuredDilation₂ margin₂ : ℕ}
    {ambient rank Q : ℕ}
    (ha : a ∈ A)
    (hA₁ : A₁ ⊆ A.erase a) (hA₂ : A₂ ⊆ A.erase a)
    (hdisjoint : Disjoint A₁ A₂)
    (W₁ : CFP.EnhancedCFPWitness (orientedTranslate .forward a A₁)
      s₁ D₁ k₁ loss₁)
    (W₂ : CFP.EnhancedCFPWitness (orientedTranslate .reverse a A₂)
      s₂ D₂ k₂ loss₂)
    (hrank₁ : W₁.rank = d + 1) (hrank₂ : W₂.rank = d + 1)
    (roundingCore₁ roundingCore₂ : Finset (LatticePoint (d + 1)))
    (hreserved₁ : Disjoint W₁.reserved roundingCore₁)
    (hreserved₂ : Disjoint W₂.reserved roundingCore₂)
    (hcoreWitness₁ : roundingCore₁ ⊆ W₁.core)
    (hcoreWitness₂ : roundingCore₂ ⊆ W₂.core)
    (width₁ width₂ : ℝ)
    (hwidth₁ : 0 ≤ width₁) (hwidth₂ : 0 ≤ width₂)
    (hcoreBound₁ : ∀ x ∈ roundingCore₁, ∀ i, |(x i : ℝ)| ≤ width₁)
    (hcoreBound₂ : ∀ x ∈ roundingCore₂, ∀ i, |(x i : ℝ)| ≤ width₂)
    (hscale₁ : structuredDilation₁ + margin₁ ≤ k₁)
    (hscale₂ : structuredDilation₂ + margin₂ ≤ k₂)
    (herrorBox₁ : ∀ e : LatticePoint (d + 1),
      e ∈ gapStepLattice W₁.progression →
      (∀ i, |(e i : ℝ)| ≤
        Real.sqrt (((((d + 1) * roundingCore₁.card : ℕ)) : ℝ)) * width₁) →
      e ∈ (W₁.progression.dilate margin₁).carrier)
    (herrorBox₂ : ∀ e : LatticePoint (d + 1),
      e ∈ gapStepLattice W₂.progression →
      (∀ i, |(e i : ℝ)| ≤
        Real.sqrt (((((d + 1) * roundingCore₂.card : ℕ)) : ℝ)) * width₂) →
      e ∈ (W₂.progression.dilate margin₂).carrier)
    (q₁ q₂ : LatticePoint (d + 1) → ℝ)
    (center : Fin (d + 1) → ℝ)
    (p₀₁ p₀₂ : LatticePoint (d + 1))
    (hp₀₁ : p₀₁ ∈ CFP.translate W₁.translatePoint
      (W₁.progression.dilate structuredDilation₁).carrier)
    (hp₀₂ : p₀₂ ∈ CFP.translate W₂.translatePoint
      (W₂.progression.dilate structuredDilation₂).carrier)
    (centerError₁ centerError₂ : ℝ)
    (hcenter₁ : ∀ i,
      |center i - (realVector p₀₁ + zonotopeCenter roundingCore₁ q₁) i| ≤
        centerError₁)
    (hcenter₂ : ∀ i,
      |center i - (realVector p₀₂ + zonotopeCenter roundingCore₂ q₂) i| ≤
        centerError₂)
    (hq₁ : ∀ x ∈ roundingCore₁, 0 ≤ q₁ x ∧ q₁ x ≤ (1 : ℝ) / 2)
    (hq₂ : ∀ x ∈ roundingCore₂, 0 ≤ q₂ x ∧ q₂ x ≤ (1 : ℝ) / 2)
    (S : GAP ambient rank) (B : CFP.IntegerBox (d + 1))
    (t₁ t₂ : LatticePoint (d + 1)) (gamma : ℝ)
    (hcontain₁ : W₁.progression.carrier ⊆ CFP.translate t₁ B.carrier)
    (hcontain₂ : W₂.progression.carrier ⊆ CFP.translate t₂ B.carrier)
    (hbox : B.carrier.card ≤ Q * S.volume)
    (hvolume₁ : gamma * (S.volume : ℝ) ≤ (W₁.progression.volume : ℝ))
    (hvolume₂ : gamma * (S.volume : ℝ) ≤ (W₂.progression.volume : ℝ))
    (hgamma : 0 < gamma)
    (hhierarchy₁ :
      ((2 ^ (d + 1) * (2 * (d + 1) + 1) ^ d * Q : ℕ) : ℝ) <
        (k₁ : ℝ) * gamma)
    (hhierarchy₂ :
      ((2 ^ (d + 1) * (2 * (d + 1) + 1) ^ d * Q : ℕ) : ℝ) <
        (k₂ : ℝ) * gamma)
    (hthick₁ : ∀ y : Fin (d + 1) → ℝ,
      (∀ i, |y i| ≤
      (3 * ((stepMatrix (rankCastGAP W₁.progression hrank₁)).det.natAbs ^
            (d + 1) *
          (stepMatrix (rankCastGAP W₂.progression hrank₂)).det.natAbs ^
            (d + 1)) + 2 : ℕ) + centerError₁) →
      y ∈ centeredZonotope roundingCore₁ q₁)
    (hthick₂ : ∀ y : Fin (d + 1) → ℝ,
      (∀ i, |y i| ≤
      (3 * ((stepMatrix (rankCastGAP W₁.progression hrank₁)).det.natAbs ^
            (d + 1) *
          (stepMatrix (rankCastGAP W₂.progression hrank₂)).det.natAbs ^
            (d + 1)) + 2 : ℕ) + centerError₂) →
      y ∈ centeredZonotope roundingCore₂ q₂) :
    Theorem4PostCFPData A := by
  let R : ℕ :=
    (stepMatrix (rankCastGAP W₁.progression hrank₁)).det.natAbs ^ (d + 1) *
      (stepMatrix (rankCastGAP W₂.progression hrank₂)).det.natAbs ^ (d + 1)
  have hcover : HasCommonCoveringRadius
      (gapStepLattice W₁.progression : Set (LatticePoint (d + 1)))
      (gapStepLattice W₂.progression : Set (LatticePoint (d + 1))) R := by
    simpa [R] using
      enhancedWitnesses_commonCoveringRadius_of_controlledBoxGammaHierarchy
        W₁ W₂ hrank₁ hrank₂ S B t₁ t₂ gamma hcontain₁ hcontain₂ hbox
        hvolume₁ hvolume₂ hgamma hhierarchy₁ hhierarchy₂
  exact ofCanonicalStepLatticeTargets
    (R := R) (Nat.zero_lt_succ d) ha hA₁ hA₂ hdisjoint W₁ W₂
    roundingCore₁ roundingCore₂ hreserved₁ hreserved₂ hcoreWitness₁
    hcoreWitness₂ width₁ width₂ hwidth₁ hwidth₂ hcoreBound₁ hcoreBound₂
    hscale₁ hscale₂ herrorBox₁ herrorBox₂ q₁ q₂ center p₀₁ p₀₂
    hp₀₁ hp₀₂ centerError₁ centerError₂ hcenter₁ hcenter₂
    hq₁ hq₂ (by simpa [R] using hthick₁) (by simpa [R] using hthick₂)
    hcover

end Theorem4PostCFPData

end

end Erdos186.PZ.Intersection
