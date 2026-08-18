/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.BoundedFractionalCanonicalPostCFPAssembly
import ErdosProblems.Erdos186.PZ.Intersection.CoordinateCenterError

/-!
# Canonical post-CFP assembly with coordinatewise center error
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

namespace Theorem4PostCFPData

/-- Bounded-support canonical assembly retaining a separate center error in
each source coordinate. -/
def ofCanonicalTargets_controlledBoxGammaHierarchy_anisotropic_finrank_pos_coordinateCenterError
    {r : ℕ} {A A₁ A₂ : Finset (LatticePoint r)}
    {a : LatticePoint r}
    {s₁ D₁ k₁ loss₁ structuredDilation₁ margin₁ : ℕ}
    {s₂ D₂ k₂ loss₂ structuredDilation₂ margin₂ : ℕ}
    {ambient rank Q : ℕ}
    (hr : 0 < r)
    (ha : a ∈ A)
    (hA₁ : A₁ ⊆ A.erase a) (hA₂ : A₂ ⊆ A.erase a)
    (hdisjoint : Disjoint A₁ A₂)
    (W₁ : CFP.EnhancedCFPWitness (orientedTranslate .forward a A₁)
      s₁ D₁ k₁ loss₁)
    (W₂ : CFP.EnhancedCFPWitness (orientedTranslate .reverse a A₂)
      s₂ D₂ k₂ loss₂)
    (hrank₁ : W₁.rank = r) (hrank₂ : W₂.rank = r)
    (roundingCore₁ roundingCore₂ : Finset (LatticePoint r))
    (hreserved₁ : Disjoint W₁.reserved roundingCore₁)
    (hreserved₂ : Disjoint W₂.reserved roundingCore₂)
    (hcoreWitness₁ : roundingCore₁ ⊆ W₁.core)
    (hcoreWitness₂ : roundingCore₂ ⊆ W₂.core)
    (width₁ width₂ : Fin r → ℝ)
    (hwidth₁ : ∀ i, 0 < width₁ i) (hwidth₂ : ∀ i, 0 < width₂ i)
    (hcoreBound₁ : ∀ x ∈ roundingCore₁, ∀ i, |(x i : ℝ)| ≤ width₁ i)
    (hcoreBound₂ : ∀ x ∈ roundingCore₂, ∀ i, |(x i : ℝ)| ≤ width₂ i)
    (hscale₁ : structuredDilation₁ + margin₁ ≤ k₁)
    (hscale₂ : structuredDilation₂ + margin₂ ≤ k₂)
    (herrorBox₁ : ∀ e : LatticePoint r,
      e ∈ gapStepLattice W₁.progression →
      (∀ i, |(e i : ℝ)| ≤ (r : ℝ) * width₁ i) →
      e ∈ (W₁.progression.dilate margin₁).carrier)
    (herrorBox₂ : ∀ e : LatticePoint r,
      e ∈ gapStepLattice W₂.progression →
      (∀ i, |(e i : ℝ)| ≤ (r : ℝ) * width₂ i) →
      e ∈ (W₂.progression.dilate margin₂).carrier)
    (q₁ q₂ : LatticePoint r → ℝ)
    (center : Fin r → ℝ)
    (p₀₁ p₀₂ : LatticePoint r)
    (hp₀₁ : p₀₁ ∈ CFP.translate W₁.translatePoint
      (W₁.progression.dilate structuredDilation₁).carrier)
    (hp₀₂ : p₀₂ ∈ CFP.translate W₂.translatePoint
      (W₂.progression.dilate structuredDilation₂).carrier)
    (centerError₁ centerError₂ : Fin r → ℝ)
    (hcenter₁ : ∀ i,
      |center i - (realVector p₀₁ + zonotopeCenter roundingCore₁ q₁) i| ≤
        centerError₁ i)
    (hcenter₂ : ∀ i,
      |center i - (realVector p₀₂ + zonotopeCenter roundingCore₂ q₂) i| ≤
        centerError₂ i)
    (hq₁ : ∀ x ∈ roundingCore₁, 0 ≤ q₁ x ∧ q₁ x ≤ (1 : ℝ) / 2)
    (hq₂ : ∀ x ∈ roundingCore₂, 0 ≤ q₂ x ∧ q₂ x ≤ (1 : ℝ) / 2)
    (S : GAP ambient rank) (B : CFP.IntegerBox r)
    (t₁ t₂ : LatticePoint r) (gamma : ℝ)
    (hcontain₁ : W₁.progression.carrier ⊆ CFP.translate t₁ B.carrier)
    (hcontain₂ : W₂.progression.carrier ⊆ CFP.translate t₂ B.carrier)
    (hbox : B.carrier.card ≤ Q * S.volume)
    (hvolume₁ : gamma * (S.volume : ℝ) ≤ (W₁.progression.volume : ℝ))
    (hvolume₂ : gamma * (S.volume : ℝ) ≤ (W₂.progression.volume : ℝ))
    (hgamma : 0 < gamma)
    (hhierarchy₁ :
      ((2 ^ r * (2 * r + 1) ^ (r - 1) * Q : ℕ) : ℝ) <
        (k₁ : ℝ) * gamma)
    (hhierarchy₂ :
      ((2 ^ r * (2 * r + 1) ^ (r - 1) * Q : ℕ) : ℝ) <
        (k₂ : ℝ) * gamma)
    (hthick₁ : ∀ y : Fin r → ℝ,
      (∀ i, |y i| ≤
      (3 * ((stepMatrix (rankCastGAP W₁.progression hrank₁)).det.natAbs ^ r *
          (stepMatrix (rankCastGAP W₂.progression hrank₂)).det.natAbs ^ r) + 2 : ℕ) +
        centerError₁ i) →
      y ∈ centeredZonotope roundingCore₁ q₁)
    (hthick₂ : ∀ y : Fin r → ℝ,
      (∀ i, |y i| ≤
      (3 * ((stepMatrix (rankCastGAP W₁.progression hrank₁)).det.natAbs ^ r *
          (stepMatrix (rankCastGAP W₂.progression hrank₂)).det.natAbs ^ r) + 2 : ℕ) +
        centerError₂ i) →
      y ∈ centeredZonotope roundingCore₂ q₂) :
    { Dout : Theorem4PostCFPData A // Dout.a = a } := by
  let P₁ := rankCastGAP W₁.progression hrank₁
  let P₂ := rankCastGAP W₂.progression hrank₂
  have hdet₁ : (stepMatrix P₁).det ≠ 0 := by
    apply det_ne_zero_of_controlled_box_gamma_hierarchy_pos hr P₁ S B t₁ gamma
    · simpa only [P₁, rankCastGAP_carrier] using hcontain₁
    · exact rankCastGAP_nondegenerate hrank₁ W₁.progression_nondegenerate
    · exact rankCastGAP_dilate_proper hrank₁ W₁.dilate_proper
    · exact W₁.k_pos
    · exact hbox
    · simpa [P₁, rankCastGAP_volume] using hvolume₁
    · exact hgamma
    · exact hhierarchy₁
  have hdet₂ : (stepMatrix P₂).det ≠ 0 := by
    apply det_ne_zero_of_controlled_box_gamma_hierarchy_pos hr P₂ S B t₂ gamma
    · simpa only [P₂, rankCastGAP_carrier] using hcontain₂
    · exact rankCastGAP_nondegenerate hrank₂ W₂.progression_nondegenerate
    · exact rankCastGAP_dilate_proper hrank₂ W₂.dilate_proper
    · exact W₂.k_pos
    · exact hbox
    · simpa [P₂, rankCastGAP_volume] using hvolume₂
    · exact hgamma
    · exact hhierarchy₂
  let R : ℕ :=
    (stepMatrix P₁).det.natAbs ^ r * (stepMatrix P₂).det.natAbs ^ r
  have hcover : HasCommonCoveringRadius
      (gapStepLattice W₁.progression : Set (LatticePoint r))
      (gapStepLattice W₂.progression : Set (LatticePoint r)) R := by
    have h := stepLattices_commonCoveringRadius P₁ P₂ hdet₁ hdet₂
    simpa [P₁, P₂, R, rankCastGAP_stepLattice] using h
  let I₁ : IntersectionSideInput A₁ a .forward :=
    IntersectionSideInput.canonicalStepLattice
      (structuredDilation := structuredDilation₁) W₁ roundingCore₁
      (hcoreWitness₁.trans W₁.core_subset) hreserved₁
  let I₂ : IntersectionSideInput A₂ a .reverse :=
    IntersectionSideInput.canonicalStepLattice
      (structuredDilation := structuredDilation₂) W₂ roundingCore₂
      (hcoreWitness₂.trans W₂.core_subset) hreserved₂
  have hround₁ : I₁.Lemma13ResidualAbsorption := by
    have hcoreL : ∀ x ∈ roundingCore₁,
        x ∈ gapStepLattice W₁.progression := by
      intro x hx
      apply carrier_subset_gapStepLattice_of_symmetric
        W₁.progression W₁.progression_symmetric
      exact W₁.core_zero_subset
        (Finset.mem_insert_of_mem (hcoreWitness₁ hx))
    have hdecomp : ∀ z ∈ I₁.target,
        ∃ p ∈ CFP.translate W₁.translatePoint
            (W₁.progression.dilate structuredDilation₁).carrier,
          ∃ x : LatticePoint r,
            Zonotope.IsZonotopePoint roundingCore₁ (fun i ↦ (x i : ℝ)) ∧
            x ∈ gapStepLattice W₁.progression ∧ z = p + x := by
      intro z hz
      change z ∈ structuredZonotopeTargetIn
        (gapStepLattice W₁.progression : Set (LatticePoint r))
        (CFP.translate W₁.translatePoint
          (W₁.progression.dilate structuredDilation₁).carrier)
        roundingCore₁ at hz
      rw [mem_structuredZonotopeTargetIn_iff] at hz
      obtain ⟨hzL, p, hp, x, hxZ, hzx⟩ := hz
      have hpL := enhanced_mem_gapStepLattice_of_mem_translate_dilate W₁ hp
      have hxL : x ∈ gapStepLattice W₁.progression := by
        have hsub := AddSubgroup.sub_mem
          (gapStepLattice W₁.progression) hzL hpL
        have hxeq : x = z - p := by rw [hzx]; abel
        rwa [hxeq]
      exact ⟨p, hp, x, hxZ, hxL, hzx⟩
    change RoundingErrorsAbsorbedBy I₁.target roundingCore₁
      (CFP.translate W₁.translatePoint
        (W₁.progression.dilate k₁).carrier)
    exact
      roundingErrorsAbsorbedBy_cfpTranslate_add_of_margin_stepLattice_anisotropic_finrank
        I₁.target roundingCore₁ width₁ W₁.progression
        W₁.progression_symmetric W₁.translatePoint
        (fun i ↦ (hwidth₁ i).le) hcoreBound₁ hcoreL hdecomp hscale₁ herrorBox₁
  have hround₂ : I₂.Lemma13ResidualAbsorption := by
    have hcoreL : ∀ x ∈ roundingCore₂,
        x ∈ gapStepLattice W₂.progression := by
      intro x hx
      apply carrier_subset_gapStepLattice_of_symmetric
        W₂.progression W₂.progression_symmetric
      exact W₂.core_zero_subset
        (Finset.mem_insert_of_mem (hcoreWitness₂ hx))
    have hdecomp : ∀ z ∈ I₂.target,
        ∃ p ∈ CFP.translate W₂.translatePoint
            (W₂.progression.dilate structuredDilation₂).carrier,
          ∃ x : LatticePoint r,
            Zonotope.IsZonotopePoint roundingCore₂ (fun i ↦ (x i : ℝ)) ∧
            x ∈ gapStepLattice W₂.progression ∧ z = p + x := by
      intro z hz
      change z ∈ structuredZonotopeTargetIn
        (gapStepLattice W₂.progression : Set (LatticePoint r))
        (CFP.translate W₂.translatePoint
          (W₂.progression.dilate structuredDilation₂).carrier)
        roundingCore₂ at hz
      rw [mem_structuredZonotopeTargetIn_iff] at hz
      obtain ⟨hzL, p, hp, x, hxZ, hzx⟩ := hz
      have hpL := enhanced_mem_gapStepLattice_of_mem_translate_dilate W₂ hp
      have hxL : x ∈ gapStepLattice W₂.progression := by
        have hsub := AddSubgroup.sub_mem
          (gapStepLattice W₂.progression) hzL hpL
        have hxeq : x = z - p := by rw [hzx]; abel
        rwa [hxeq]
      exact ⟨p, hp, x, hxZ, hxL, hzx⟩
    change RoundingErrorsAbsorbedBy I₂.target roundingCore₂
      (CFP.translate W₂.translatePoint
        (W₂.progression.dilate k₂).carrier)
    exact
      roundingErrorsAbsorbedBy_cfpTranslate_add_of_margin_stepLattice_anisotropic_finrank
        I₂.target roundingCore₂ width₂ W₂.progression
        W₂.progression_symmetric W₂.translatePoint
        (fun i ↦ (hwidth₂ i).le) hcoreBound₂ hcoreL hdecomp hscale₂ herrorBox₂
  have htarget₁ : I₁.Lemma14TargetThickness center (3 * R + 2) := by
    apply I₁.lemma14TargetThickness_of_eq_structuredZonotopeTargetIn_coordinateCenterError
      (CFP.translate W₁.translatePoint
        (W₁.progression.dilate structuredDilation₁).carrier)
      p₀₁ q₁ center (3 * R + 2) centerError₁
    · rfl
    · exact hp₀₁
    · exact hcenter₁
    · exact hq₁
    · simpa [I₁, P₁, P₂, R,
        IntersectionSideInput.canonicalStepLattice] using hthick₁
  have htarget₂ : I₂.Lemma14TargetThickness center (3 * R + 2) := by
    apply I₂.lemma14TargetThickness_of_eq_structuredZonotopeTargetIn_coordinateCenterError
      (CFP.translate W₂.translatePoint
        (W₂.progression.dilate structuredDilation₂).carrier)
      p₀₂ q₂ center (3 * R + 2) centerError₂
    · rfl
    · exact hp₀₂
    · exact hcenter₂
    · exact hq₂
    · simpa [I₂, P₁, P₂, R,
        IntersectionSideInput.canonicalStepLattice] using hthick₂
  have hcovolume : FullRankLatticeCovolumeConclusion I₁ I₂ R := hcover
  refine ⟨ofSourceLemmas hr ha hA₁ hA₂ hdisjoint I₁ I₂
    hround₁ hround₂ htarget₁ htarget₂ hcovolume, ?_⟩
  rfl

end Theorem4PostCFPData

end

end Erdos186.PZ.Intersection
