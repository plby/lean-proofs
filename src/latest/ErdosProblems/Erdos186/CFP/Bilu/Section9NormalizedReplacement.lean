/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section91CoveringEnlargement

/-!
# Normalized coordinate form of the Lemma 4.5 replacement

This module transports the finite Lemma 4.5 seed and Proposition 7.5's
volume estimate through the canonical Euclidean coordinate isometry of the
section.  The resulting body lives with the literal lattice
`integralPoints (coordinateC0 D)` and its volume bound uses that lattice's
ordinary covolume, which is the input form required by a lattice-basis
normalization or a primitive kernel quotient.
-/

namespace Erdos186.CFP.Bilu.Section9NormalizedReplacement

open scoped Pointwise
open MeasureTheory Set Module Submodule
open Proposition75Data Proposition75Case2 Proposition75Case2Construction
open Section9Replacement SubspaceLattice
open Section9ContainerIntegration
open Section91CoveringEnlargement

noncomputable section

variable {m r : ℕ} {B : Set (EuclideanSpace ℝ (Fin m))}
  {a : Fin r → EuclideanSpace ℝ (Fin m)}
  {D : GeometricData B a}
  {K : Finset (Mahler.IntegralPoint m)} {coverConstant : ℕ}

/-- The translated large slice in the canonical Euclidean coordinates of
`C₀`. -/
noncomputable def coordinateSection
    (S : Lemma45SectionSeed D K coverConstant) :
    Finset (coordinateC0 D) :=
  S.sectionSlice.image (coordinateC0Equiv D)

@[simp] theorem card_coordinateSection
    (S : Lemma45SectionSeed D K coverConstant) :
    (coordinateSection S).card = S.sectionSlice.card := by
  rw [coordinateSection, Finset.card_image_of_injective]
  exact (coordinateC0Equiv D).injective

theorem coordinateSection_nonempty
    (S : Lemma45SectionSeed D K coverConstant) :
    (coordinateSection S).Nonempty := by
  rw [← Finset.card_pos, card_coordinateSection]
  exact S.sectionSlice_nonempty.card_pos

/-- The normalized finite slice remains inside the normalized section
body. -/
theorem coordinateSection_subset_coordinateB0
    (S : Lemma45SectionSeed D K coverConstant) :
    (coordinateSection S : Set (coordinateC0 D)) ⊆ coordinateB0 D := by
  intro z hz
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
  exact ⟨w, S.sectionSlice_subset_B0 hw, rfl⟩

/-- Every normalized slice point belongs to the literal integral lattice in
the coordinate subspace. -/
theorem coordinateSection_subset_integralPoints
    (S : Lemma45SectionSeed D K coverConstant) :
    (coordinateSection S : Set (coordinateC0 D)) ⊆
      integralPoints (coordinateC0 D) := by
  intro z hz
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
  exact (coordinateLatticeEquiv D
    ⟨w, S.sectionSlice_subset_lattice hw⟩).property

/-- The large-slice cardinal inequality is unchanged by coordinate
normalization. -/
theorem large_coordinateSection
    (S : Lemma45SectionSeed D K coverConstant) :
    K.card ≤ coverConstant * (coordinateSection S).card := by
  rw [card_coordinateSection]
  exact S.large_sectionSlice

/-- Projection to the original first coordinate stays injective after
normalization. -/
theorem sourceHead_injOn_coordinateSection
    (S : Lemma45SectionSeed D K coverConstant) :
    Set.InjOn
      (fun z : coordinateC0 D ↦
        head (((coordinateC0Equiv D).symm z : D.C0) : Ambient m r))
      (coordinateSection S : Set (coordinateC0 D)) := by
  intro x hx y hy hxy
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
  apply congrArg (coordinateC0Equiv D)
  apply S.head_injOn_sectionSlice hu hv
  simpa using hxy

/-- Proposition 7.5 written in the normalized coordinate space with the
literal coordinate-lattice covolume.  No determinant or measure factor is
lost in the transport. -/
theorem coordinate_volume_bound
    {constant scale : ENNReal}
    (h75 : Proposition75Conclusion D constant scale) :
    volume (coordinateB0 D) ≤
      constant * volume B * scale *
        ENNReal.ofReal
          (ZLattice.covolume (integralPoints (coordinateC0 D))) := by
  rw [volume_coordinateB0 D,
    coordinateIntegralPoints_volume_covolume_eq_latticePoints D]
  exact h75

/-- Joint normalized handoff: the finite seed and Proposition 7.5 produce
one coordinate body carrying the integral slice, the large-cardinality
bound, head injectivity, and the exact volume/covolume estimate. -/
structure NormalizedReplacement
    (constant scale : ENNReal) where
  seed : Lemma45SectionSeed D K coverConstant
  proposition75 : Proposition75Conclusion D constant scale

namespace NormalizedReplacement

variable {constant scale : ENNReal}

theorem section_nonempty
    (N : NormalizedReplacement (D := D) (K := K)
      (coverConstant := coverConstant) constant scale) :
    (coordinateSection N.seed).Nonempty :=
  coordinateSection_nonempty N.seed

theorem section_subset_body
    (N : NormalizedReplacement (D := D) (K := K)
      (coverConstant := coverConstant) constant scale) :
    (coordinateSection N.seed : Set (coordinateC0 D)) ⊆ coordinateB0 D :=
  coordinateSection_subset_coordinateB0 N.seed

theorem section_subset_lattice
    (N : NormalizedReplacement (D := D) (K := K)
      (coverConstant := coverConstant) constant scale) :
    (coordinateSection N.seed : Set (coordinateC0 D)) ⊆
      integralPoints (coordinateC0 D) :=
  coordinateSection_subset_integralPoints N.seed

theorem volume_bound
    (N : NormalizedReplacement (D := D) (K := K)
      (coverConstant := coverConstant) constant scale) :
    volume (coordinateB0 D) ≤
      constant * volume B * scale *
        ENNReal.ofReal
          (ZLattice.covolume (integralPoints (coordinateC0 D))) :=
  coordinate_volume_bound N.proposition75

end NormalizedReplacement

/-! ## Joint Section 9.1 package -/

/-- The normalized Lemma 4.5 replacement after adjoining the Ruzsa-cover
centres.  Besides the exact volume/covolume estimate, this records the
literal lattice lift of every difference used to cover `K`. -/
structure CoveredNormalizedReplacement
    (constant scale : ENNReal) (sigma : ℕ) where
  normalized : NormalizedReplacement (D := D) (K := K)
    (coverConstant := coverConstant) constant scale
  cover : CoveringCertificate K normalized.seed.sourceSlice
  centers_card : cover.centers.card ≤ sigma * coverConstant
  cover_lift : ∀ z ∈ K, ∃ c ∈ cover.centers,
    ∃ x : {x // x ∈ normalized.seed.sourceSlice},
    ∃ y : {y // y ∈ normalized.seed.sourceSlice},
      z = c + latticeHead D
        (Section91CoveringEnlargement.Lemma45SectionSeed.differenceLift
          normalized.seed x y)

/-- Proposition 7.5, the Lemma 4.5 seed, and the Section 9.1 Ruzsa lemma
assemble without any further geometric hypothesis. -/
theorem exists_coveredNormalizedReplacement
    {constant scale : ENNReal} {sigma : ℕ}
    (S : Lemma45SectionSeed D K coverConstant)
    (h75 : Proposition75Conclusion D constant scale)
    (hdouble : (K + K).card ≤ sigma * K.card) :
    Nonempty (CoveredNormalizedReplacement (D := D) (K := K)
      (coverConstant := coverConstant) constant scale sigma) := by
  obtain ⟨C, hCcard, hClift⟩ :=
    Section91CoveringEnlargement.Lemma45SectionSeed.exists_coveringEnlargement
      S sigma hdouble
  exact ⟨⟨⟨S, h75⟩, C, hCcard, hClift⟩⟩

end

end Erdos186.CFP.Bilu.Section9NormalizedReplacement

#print axioms Erdos186.CFP.Bilu.Section9NormalizedReplacement.coordinate_volume_bound
#print axioms Erdos186.CFP.Bilu.Section9NormalizedReplacement.NormalizedReplacement.volume_bound
#print axioms Erdos186.CFP.Bilu.Section9NormalizedReplacement.exists_coveredNormalizedReplacement
