/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.AppendixEncoding

/-!
# The projected-properization boundary for the CFP Appendix

An additive projection of a proper GAP need not be proper.  This file does
not make that false preservation claim.  Instead it packages the genuine
Lemma 2.27-style output: a lower-rank proper target GAP which contains the
projected base carrier, while a translate of its smaller dilate is contained
in the projected covered dilate.  The scale comparison records the uniform
loss needed to preserve the fixed rational scale.

The final theorem performs all finite-set and witness bookkeeping.  Thus the
only remaining geometric obligation at a projection site is to construct a
`ProjectedProperization` certificate.
-/

namespace Erdos186.CFP.ProjectedProperization

open scoped BigOperators
open NoCarryEmbedding

noncomputable section

/-- Mapping a subset sum through an additive homomorphism gives a subset sum
of the image, provided the homomorphism is injective on the set of available
summands.  Injectivity is necessary because `Finset.image` removes duplicate
summands. -/
theorem map_mem_subsetSums_image {d e : ℕ}
    (f : LatticePoint d →+ LatticePoint e)
    (R : Finset (LatticePoint d)) (hinjective : Set.InjOn f R)
    {x : LatticePoint d} (hx : x ∈ GAP.subsetSums R) :
    f x ∈ GAP.subsetSums (R.image f) := by
  obtain ⟨S, hSR, rfl⟩ := GAP.mem_subsetSums_iff.mp hx
  apply GAP.mem_subsetSums_iff.mpr
  refine ⟨S.image f, Finset.image_mono f hSR, ?_⟩
  rw [Finset.sum_image]
  · simp
  · intro a ha b hb hab
    exact hinjective (hSR ha) (hSR hb) hab

/-- The exact finite output required from projected properization.

`base_image_subset` preserves the structured core.  `covered_subset` points
in the opposite direction at the shrunken dilation scale, so coverage is
inherited from the old witness.  No equality of projected carriers is
asserted. -/
structure Data {d e s D k loss factor : ℕ}
    {H : Finset (LatticePoint d)}
    (f : LatticePoint d →+ LatticePoint e)
    (W : EnhancedCFPWitness H s D k loss) where
  scale : ℕ
  scale_pos : 0 < scale
  scale_le_source : scale ≤ k
  source_le_factor_mul_scale : k ≤ factor * scale
  rank : ℕ
  rank_le : rank ≤ W.rank
  progression : GAP e rank
  progression_proper : progression.Proper
  dilate_proper : (progression.dilate scale).Proper
  progression_symmetric : progression.Symmetric
  progression_nondegenerate : progression.Nondegenerate
  homogeneous : progression.Homogeneous
  base_image_subset : W.progression.carrier.image f ⊆ progression.carrier
  translatePoint : LatticePoint e
  covered_subset :
    translate translatePoint (progression.dilate scale).carrier ⊆
      translate (f W.translatePoint)
        (mapGAP f (W.progression.dilate k)).carrier
  covered_translate_homogeneous :
    ∃ z : Fin rank → ℤ,
      translatePoint + (progression.dilate scale).offset =
        (fun j ↦ ∑ i, z i * progression.steps i j)

namespace Data

variable {d e s D k loss factor : ℕ}
    {f : LatticePoint d →+ LatticePoint e}

/-- Enlarging the advertised dimension-only loss factor preserves a
projected-properization certificate.  All geometric data are unchanged;
only the scale comparison becomes weaker. -/
def monoFactor
    {factor' : ℕ} {H : Finset (LatticePoint d)}
    {W : EnhancedCFPWitness H s D k loss}
    (Z : Data (factor := factor) f W) (hfactor : factor ≤ factor') :
    Data (factor := factor') f W where
  scale := Z.scale
  scale_pos := Z.scale_pos
  scale_le_source := Z.scale_le_source
  source_le_factor_mul_scale := Z.source_le_factor_mul_scale.trans <|
    Nat.mul_le_mul_right Z.scale hfactor
  rank := Z.rank
  rank_le := Z.rank_le
  progression := Z.progression
  progression_proper := Z.progression_proper
  dilate_proper := Z.dilate_proper
  progression_symmetric := Z.progression_symmetric
  progression_nondegenerate := Z.progression_nondegenerate
  homogeneous := Z.homogeneous
  base_image_subset := Z.base_image_subset
  translatePoint := Z.translatePoint
  covered_subset := Z.covered_subset
  covered_translate_homogeneous := Z.covered_translate_homogeneous

/-- A projected-properization certificate transfers an enhanced CFP witness
to the finite image set, with only the advertised denominator factor. -/
noncomputable def transportEnhanced
    {H : Finset (LatticePoint d)}
    (W : EnhancedCFPWitness H s D k loss)
    (hinjective : Set.InjOn f H)
    (hfactor : 0 < factor)
    (Z : Data (factor := factor) f W) :
    EnhancedCFPWitness (H.image f) s D Z.scale loss := by
  let core := W.core.image f
  let reserved := W.reserved.image f
  have hinjectiveCore : Set.InjOn f W.core :=
    hinjective.mono W.core_subset
  have hinjectiveReserved : Set.InjOn f W.reserved :=
    hinjective.mono W.reserved_subset
  have hHCard : (H.image f).card = H.card :=
    Finset.card_image_of_injOn hinjective
  have hcoreCard : core.card = W.core.card := by
    exact Finset.card_image_of_injOn hinjectiveCore
  have hreservedCard : reserved.card = W.reserved.card := by
    exact Finset.card_image_of_injOn hinjectiveReserved
  have hcoreZero : insert 0 core ⊆ Z.progression.carrier := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · have hzeroSource : (0 : LatticePoint d) ∈ W.progression.carrier :=
        W.core_zero_subset (Finset.mem_insert_self 0 W.core)
      apply Z.base_image_subset
      exact Finset.mem_image.mpr ⟨0, hzeroSource, map_zero f⟩
    · obtain ⟨y, hycore, rfl⟩ := Finset.mem_image.mp hx
      apply Z.base_image_subset
      apply Finset.mem_image.mpr
      refine ⟨y, ?_, rfl⟩
      exact W.core_zero_subset (Finset.mem_insert_of_mem hycore)
  have hcoveredMapped :
      translate (f W.translatePoint)
          (mapGAP f (W.progression.dilate k)).carrier ⊆
        GAP.subsetSums reserved := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := mem_translate_iff.mp hx
    rw [mapGAP_carrier] at hq
    obtain ⟨p, hp, hpq⟩ := Finset.mem_image.mp hq
    have hsource : W.translatePoint + p ∈
        translate W.translatePoint (W.progression.dilate k).carrier :=
      mem_translate_iff.mpr ⟨p, hp, rfl⟩
    have hsourceCovered : W.translatePoint + p ∈
        GAP.subsetSums W.reserved := by
      exact W.covered hsource
    have hmapped := map_mem_subsetSums_image f W.reserved
      hinjectiveReserved hsourceCovered
    simpa only [map_add, hpq] using hmapped
  refine
    { core := core
      reserved := reserved
      rank := Z.rank
      rank_le := Z.rank_le.trans W.rank_le
      progression := Z.progression
      core_subset := Finset.image_mono f W.core_subset
      reserved_subset_core := Finset.image_mono f W.reserved_subset_core
      core_large := ?_
      reserved_small := ?_
      core_zero_subset := hcoreZero
      homogeneous := Z.homogeneous
      translatePoint := Z.translatePoint
      covered := Z.covered_subset.trans hcoveredMapped
      dilate_proper := Z.dilate_proper
      k_pos := Z.scale_pos
      scaleNum := W.scaleNum
      scaleDen := W.scaleDen * factor
      scaleNum_pos := W.scaleNum_pos
      scaleDen_pos := Nat.mul_pos W.scaleDen_pos hfactor
      scale_lower := ?_
      scale_upper := Z.scale_le_source.trans W.scale_upper
      progression_proper := Z.progression_proper
      progression_symmetric := Z.progression_symmetric
      progression_nondegenerate := Z.progression_nondegenerate
      covered_translate_homogeneous := Z.covered_translate_homogeneous }
  · calc
      (H.image f).card = H.card := hHCard
      _ ≤ W.core.card + loss := W.core_large
      _ = core.card + loss := by rw [hcoreCard]
  · rw [hreservedCard]
    exact W.reserved_small
  · calc
      W.scaleNum * s ≤ W.scaleDen * k := W.scale_lower
      _ ≤ W.scaleDen * (factor * Z.scale) :=
        Nat.mul_le_mul_left W.scaleDen Z.source_le_factor_mul_scale
      _ = (W.scaleDen * factor) * Z.scale := by
        rw [Nat.mul_assoc]

/-- Fixed-scale packaging of `transportEnhanced`. -/
noncomputable def transportFixed
    {scaleNum scaleDen : ℕ}
    {H : Finset (LatticePoint d)}
    (W : FixedScaleWitness H s D k loss scaleNum scaleDen)
    (hinjective : Set.InjOn f H)
    (hfactor : 0 < factor)
    (Z : Data (factor := factor) f W.enhanced) :
    FixedScaleWitness (H.image f) s D Z.scale loss
      scaleNum (scaleDen * factor) := by
  refine ⟨Z.transportEnhanced W.enhanced hinjective hfactor, ?_⟩
  constructor
  · exact W.scaleNum_eq
  · change W.enhanced.scaleDen * factor = scaleDen * factor
    rw [W.scaleDen_eq]

end Data

/-! ### Specialization to box dehomogenization -/

/-- Dehomogenization is injective on the normalized homogeneous copy of the
original box set, although it is not injective on the ambient lattice or on
an arbitrary GAP containing that copy. -/
theorem boxDehomogenizeHom_injOn_homogenizedBoxSet
    {d : ℕ} (B : IntegerBox d) (A : Finset (LatticePoint d)) :
    Set.InjOn (AppendixEncoding.boxDehomogenizeHom B)
      (AppendixEncoding.homogenizedBoxSet B A) := by
  intro x hx y hy hxy
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
  have hab : a = b := by
    simpa only [AppendixEncoding.boxDehomogenizeHom_boxHomogenize]
      using hxy
  subst b
  rfl

/-- Direct consumer-facing specialization after
`liftFixedScaleWitness_to_homogenizedBoxSet`.  The only remaining input is
the genuine projected-properization certificate; exact carrier preservation
is not assumed. -/
noncomputable def Data.transportFixed_boxDehomogenize
    {d D s k loss scaleNum scaleDen factor : ℕ}
    (B : IntegerBox d) (A : Finset (LatticePoint d))
    (W : FixedScaleWitness
      (AppendixEncoding.homogenizedBoxSet B A)
        s D k loss scaleNum scaleDen)
    (hfactor : 0 < factor)
    (Z : Data (factor := factor)
      (AppendixEncoding.boxDehomogenizeHom B) W.enhanced) :
    FixedScaleWitness A s D Z.scale loss scaleNum
      (scaleDen * factor) := by
  have Wprojected := Z.transportFixed W
    (boxDehomogenizeHom_injOn_homogenizedBoxSet B A) hfactor
  rw [AppendixEncoding.boxDehomogenizeHom_image_homogenizedBoxSet]
    at Wprojected
  exact Wprojected

end

end Erdos186.CFP.ProjectedProperization

#print axioms Erdos186.CFP.ProjectedProperization.Data.transportFixed
#print axioms
  Erdos186.CFP.ProjectedProperization.Data.transportFixed_boxDehomogenize
