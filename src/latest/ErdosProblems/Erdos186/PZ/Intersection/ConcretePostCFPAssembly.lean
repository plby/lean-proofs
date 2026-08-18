/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.FullRankSideLattice
import ErdosProblems.Erdos186.PZ.Intersection.GAPErrorBox
import ErdosProblems.Erdos186.PZ.Intersection.SideGeometryAssembly

/-!
# Concrete post-CFP assembly

This theorem is the source-data version of the post-CFP intersection
constructor.  Residual absorption is proved by zonotope rounding plus an
actual symmetric-GAP margin, target thickness is proved from a literal
centered-zonotope cube, and the common covering radius is proved from the
projection-cardinality nonsingularity argument for the two step lattices.

Thus none of the three abstract predicates consumed by
`Theorem4PostCFPData.ofSourceLemmas` occurs as an input below.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-- Assemble the complete post-CFP data from literal geometric and
quantitative side estimates. -/
def Theorem4PostCFPData.ofZonotopeMarginCenteredCubeProjectionBounds
    {d k₁ k₂ : ℕ}
    {A A₁ A₂ : Finset (LatticePoint (d + 1))}
    {a : LatticePoint (d + 1)} {center : Fin (d + 1) → ℝ}
    (ha : a ∈ A)
    (hA₁ : A₁ ⊆ A.erase a) (hA₂ : A₂ ⊆ A.erase a)
    (hdisjoint : Disjoint A₁ A₂)
    (I₁ : IntersectionSideInput A₁ a .forward)
    (I₂ : IntersectionSideInput A₂ a .reverse)
    (structuredDilation₁ margin₁ : ℕ) (width₁ : ℝ)
    (hwidth₁ : 0 ≤ width₁)
    (hcore₁ : ∀ x ∈ I₁.roundingCore, ∀ i, |(x i : ℝ)| ≤ width₁)
    (htargetDecomposition₁ : ∀ z ∈ I₁.target,
      ∃ p ∈ CFP.translate I₁.witness.translatePoint
          (I₁.witness.progression.dilate structuredDilation₁).carrier,
        ∃ x : LatticePoint (d + 1),
          Zonotope.IsZonotopePoint I₁.roundingCore
            (fun i ↦ (x i : ℝ)) ∧ z = p + x)
    (hscale₁ : structuredDilation₁ + margin₁ ≤ I₁.dilation)
    (herrorBox₁ : ∀ e : LatticePoint (d + 1),
      (∀ i, |(e i : ℝ)| ≤
        Real.sqrt ((((d + 1) * I₁.roundingCore.card : ℕ) : ℝ)) * width₁) →
      e ∈ (I₁.witness.progression.dilate margin₁).carrier)
    (structuredDilation₂ margin₂ : ℕ) (width₂ : ℝ)
    (hwidth₂ : 0 ≤ width₂)
    (hcore₂ : ∀ x ∈ I₂.roundingCore, ∀ i, |(x i : ℝ)| ≤ width₂)
    (htargetDecomposition₂ : ∀ z ∈ I₂.target,
      ∃ p ∈ CFP.translate I₂.witness.translatePoint
          (I₂.witness.progression.dilate structuredDilation₂).carrier,
        ∃ x : LatticePoint (d + 1),
          Zonotope.IsZonotopePoint I₂.roundingCore
            (fun i ↦ (x i : ℝ)) ∧ z = p + x)
    (hscale₂ : structuredDilation₂ + margin₂ ≤ I₂.dilation)
    (herrorBox₂ : ∀ e : LatticePoint (d + 1),
      (∀ i, |(e i : ℝ)| ≤
        Real.sqrt ((((d + 1) * I₂.roundingCore.card : ℕ) : ℝ)) * width₂) →
      e ∈ (I₂.witness.progression.dilate margin₂).carrier)
    (P₁ P₂ : GAP (d + 1) (d + 1))
    (hlattice₁ : I₁.lattice =
      (stepLattice P₁ : Set (LatticePoint (d + 1))))
    (hlattice₂ : I₂.lattice =
      (stepLattice P₂ : Set (LatticePoint (d + 1))))
    (B₁ B₂ : CFP.IntegerBox (d + 1))
    (t₁ t₂ : LatticePoint (d + 1))
    (hcontain₁ : P₁.carrier ⊆ CFP.translate t₁ B₁.carrier)
    (hcontain₂ : P₂.carrier ⊆ CFP.translate t₂ B₂.carrier)
    (hnondegenerate₁ : P₁.Nondegenerate)
    (hnondegenerate₂ : P₂.Nondegenerate)
    (hproper₁ : (P₁.dilate k₁).Proper)
    (hproper₂ : (P₂.dilate k₂).Proper)
    (hlarge₁ : ∀ j₀ : Fin (d + 1),
      2 ^ (d + 1) *
          (∏ j : Fin d,
            (2 * projectionRadius k₁ B₁ (j₀.succAbove j) + 1)) <
        k₁ ^ (d + 1) * P₁.volume)
    (hlarge₂ : ∀ j₀ : Fin (d + 1),
      2 ^ (d + 1) *
          (∏ j : Fin d,
            (2 * projectionRadius k₂ B₂ (j₀.succAbove j) + 1)) <
        k₂ ^ (d + 1) * P₂.volume)
    (q₁ q₂ : LatticePoint (d + 1) → ℝ)
    (hcenter₁ : center = zonotopeCenter I₁.roundingCore q₁)
    (hcenter₂ : center = zonotopeCenter I₂.roundingCore q₂)
    (hq₁ : ∀ x ∈ I₁.roundingCore, 0 ≤ q₁ x ∧ q₁ x ≤ (1 : ℝ) / 2)
    (hq₂ : ∀ x ∈ I₂.roundingCore, 0 ≤ q₂ x ∧ q₂ x ≤ (1 : ℝ) / 2)
    (hthick₁ : ∀ z : Fin (d + 1) → ℝ,
      (∀ i, |z i| ≤
        3 * ((stepMatrix P₁).det.natAbs ^ (d + 1) *
          (stepMatrix P₂).det.natAbs ^ (d + 1)) + 2) →
      z ∈ centeredZonotope I₁.roundingCore q₁)
    (hthick₂ : ∀ z : Fin (d + 1) → ℝ,
      (∀ i, |z i| ≤
        3 * ((stepMatrix P₁).det.natAbs ^ (d + 1) *
          (stepMatrix P₂).det.natAbs ^ (d + 1)) + 2) →
      z ∈ centeredZonotope I₂.roundingCore q₂)
    (htarget₁ : ∀ z, z ∈ I₁.lattice →
      (fun i ↦ (z i : ℝ)) ∈ zonotope I₁.roundingCore → z ∈ I₁.target)
    (htarget₂ : ∀ z, z ∈ I₂.lattice →
      (fun i ↦ (z i : ℝ)) ∈ zonotope I₂.roundingCore → z ∈ I₂.target) :
    Theorem4PostCFPData A := by
  let R := (stepMatrix P₁).det.natAbs ^ (d + 1) *
    (stepMatrix P₂).det.natAbs ^ (d + 1)
  have hcovolume : FullRankLatticeCovolumeConclusion I₁ I₂ R :=
    fullRankLatticeCovolumeConclusion_of_projectionBounds I₁ I₂ P₁ P₂
      hlattice₁ hlattice₂ B₁ B₂ t₁ t₂ hcontain₁ hcontain₂
      hnondegenerate₁ hnondegenerate₂ hproper₁ hproper₂ hlarge₁ hlarge₂
  have htargetThickness₁ :
      I₁.Lemma14TargetThickness center (3 * R + 2) :=
    I₁.lemma14TargetThickness_of_centeredZonotope_cube q₁ center
      (3 * R + 2) hcenter₁ hq₁ (by simpa [R] using hthick₁) htarget₁
  have htargetThickness₂ :
    I₂.Lemma14TargetThickness center (3 * R + 2) :=
    I₂.lemma14TargetThickness_of_centeredZonotope_cube q₂ center
      (3 * R + 2) hcenter₂ hq₂ (by simpa [R] using hthick₂) htarget₂
  exact Theorem4PostCFPData.ofZonotopeMarginSourceLemmas
    (Nat.zero_lt_succ d) ha hA₁ hA₂ hdisjoint I₁ I₂
    structuredDilation₁ margin₁ width₁ hwidth₁ hcore₁
    htargetDecomposition₁ hscale₁ herrorBox₁
    structuredDilation₂ margin₂ width₂ hwidth₂ hcore₂
    htargetDecomposition₂ hscale₂ herrorBox₂
    htargetThickness₁ htargetThickness₂ hcovolume

end

end Erdos186.PZ.Intersection
