/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Corollary217MapBack
import ErdosProblems.Erdos186.CFP.WitnessAssembly

/-!
# Assemble the Corollary 2.17 witness before source projection

The usual map-back proves that source evaluation is injective on a large
dilate.  That condition is stronger than necessary: the coordinate GAP is
already proper.  We first assemble the fixed-scale witness in common-basis
coordinates, so generic projected properization can be applied afterwards.
-/

namespace Erdos186.CFP

open scoped BigOperators

noncomputable section

/-- Coordinate-lattice counterpart of
`preprocessedReserveCertificate_of_commonBasisDenseBox`.  There is no
ambient evaluation and therefore no no-carry/injectivity premise. -/
theorem exists_coordinateFixedScaleWitness_of_commonBasisDenseBox
    {d ell s D k loss scaleNum scaleDen : ℕ}
    {H core : Finset (LatticePoint d)}
    (radius : Fin d → ℕ)
    (family reserve : Fin ell → Finset (LatticePoint d))
    (hradius : ∀ i, 0 < radius i)
    (hcovered : ContainsTranslate (heterogeneousSumset family)
      ((symmetricAxisBox radius).dilate k))
    (hfamilyReserve : ∀ i, family i ⊆ GAP.subsetSums (reserve i))
    (hdisjoint : (Set.univ : Set (Fin ell)).PairwiseDisjoint reserve)
    (hcoreH : core ⊆ H)
    (hreserveCore : ∀ i, reserve i ⊆ core)
    (hcoreLarge : H.card ≤ core.card + loss)
    (hreserveSmall : (∑ i, (reserve i).card) ≤ s)
    (hcoreProgression : insert 0 core ⊆
      (symmetricCoordinateGAP radius).carrier)
    (hrank : d ≤ D) (hk : 0 < k)
    (hscaleNum : 0 < scaleNum) (hscaleDen : 0 < scaleDen)
    (hscaleLower : scaleNum * s ≤ scaleDen * k)
    (hscaleUpper : k ≤ s) :
    Nonempty (FixedScaleWitness H s D k loss scaleNum scaleDen) := by
  classical
  obtain ⟨u, hu⟩ := hcovered
  let P := symmetricCoordinateGAP radius
  let center : LatticePoint d := fun i ↦ (k * radius i : ℕ)
  let t : LatticePoint d := u + center
  have hcoveredTarget :
      Elementary.translate t (P.dilate k).carrier ⊆
        heterogeneousSumset (fun i ↦ GAP.subsetSums (reserve i)) := by
    intro x hx
    obtain ⟨p, hp, hpx⟩ := Elementary.mem_translate_iff.mp hx
    have hcenterP : center + p ∈
        ((symmetricAxisBox radius).dilate k).carrier := by
      rw [← symmetricCoordinateGAP_dilate_carrier radius]
      exact Elementary.mem_translate_iff.mpr ⟨p, hp, rfl⟩
    have hsource : u + (center + p) ∈ heterogeneousSumset family :=
      hu (Elementary.mem_translate_iff.mpr ⟨center + p, hcenterP, rfl⟩)
    have htarget := heterogeneousSumset_mono hfamilyReserve hsource
    rw [← hpx]
    simpa only [t, add_assoc] using htarget
  have htranslateHomogeneous : ∃ z : Fin d → ℤ,
      t + (P.dilate k).offset =
        (fun j ↦ ∑ i, z i * P.steps i j) := by
    refine ⟨u, ?_⟩
    have hcenterOffset : center + (P.dilate k).offset = 0 := by
      funext i
      simp [center, P, symmetricCoordinateGAP]
    rw [show t = u + center by rfl, add_assoc, hcenterOffset, add_zero]
    funext j
    simp [P, symmetricCoordinateGAP]
  let E : EnhancedCFPWitness H s D k loss :=
    enhancedCFPWitness_of_disjoint_reserveFamily reserve P t hdisjoint
      hrank hcoreH hreserveCore hcoreLarge hreserveSmall hcoreProgression
      (symmetricCoordinateGAP_centered radius).homogeneous hcoveredTarget
      (symmetricCoordinateGAP_dilate_proper radius) hk hscaleNum hscaleDen
      hscaleLower hscaleUpper (symmetricCoordinateGAP_proper radius)
      ⟨radius, symmetricCoordinateGAP_centered radius⟩
      (symmetricCoordinateGAP_nondegenerate hradius) htranslateHomogeneous
  exact ⟨⟨E, rfl, rfl⟩⟩

end

end Erdos186.CFP

#print axioms
  Erdos186.CFP.exists_coordinateFixedScaleWitness_of_commonBasisDenseBox
