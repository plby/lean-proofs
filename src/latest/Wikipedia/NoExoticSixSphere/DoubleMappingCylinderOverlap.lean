import Wikipedia.NoExoticSixSphere.DoubleMappingCylinderCoverEquivalence

/-!
# The overlap is the actual open middle cylinder

An open subspace avoiding an attaching locus embeds openly after the
pushout. Applying this twice identifies the overlap of the actual cover
with the product of the open middle third and the attaching space.
-/

noncomputable section

universe u

open CategoryTheory Set Topology unitInterval
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.DoubleMappingCylinder

def middleTimes : Set I := {t | (1 : ℝ) / 3 < t ∧ (t : ℝ) < 2 / 3}

theorem middleTimes_isOpen : IsOpen middleTimes :=
  (isOpen_lt continuous_const continuous_subtype_val).inter
    (isOpen_lt continuous_subtype_val continuous_const)

theorem middleTimes_ne_zero (t : middleTimes) : t.val ≠ 0 := by
  intro h
  have ht := t.property.1
  rw [h] at ht
  norm_num at ht

theorem middleTimes_ne_one (t : middleTimes) : t.val ≠ 1 := by
  intro h
  have ht := t.property.2
  rw [h] at ht
  norm_num at ht

def windowInclusion (A : TopCat.{u}) : TopCat.of (middleTimes × A) ⟶ TopCat.of (I × A) :=
  TopCat.ofHom ⟨fun p ↦ (p.1.val, p.2),
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd⟩

theorem windowInclusion_isOpenEmbedding (A : TopCat.{u}) :
    IsOpenEmbedding (windowInclusion A) :=
  middleTimes_isOpen.isOpenEmbedding_subtypeVal.prodMap IsOpenEmbedding.id

theorem windowInclusion_avoids_zero (A : TopCat.{u}) (p : middleTimes × A) :
    windowInclusion A p ∉ Set.range (HomotopyExtension.cylinderEndpoint A 0) := by
  rintro ⟨a, h⟩
  exact middleTimes_ne_zero p.1 (congrArg Prod.fst h).symm

variable {A X Y : TopCat.{u}} (e : A ⟶ X) (f : A ⟶ Y)

def windowToMiddle : TopCat.of (middleTimes × A) ⟶ MappingCylinder.space f :=
  windowInclusion A ≫ MappingCylinder.cylinder f

theorem windowToMiddle_isOpenEmbedding : IsOpenEmbedding (windowToMiddle f) :=
  PushoutOutsideAttachment.comp_isOpenEmbedding (MappingCylinder.square f)
    (windowInclusion A) (windowInclusion_avoids_zero A) (windowInclusion_isOpenEmbedding A)

theorem windowToMiddle_avoids_source (p : middleTimes × A) :
    windowToMiddle f p ∉ Set.range (MappingCylinder.source f) := by
  rintro ⟨a, h⟩
  have hp : (p.1.val, p.2) = (1, a) :=
    PushoutOutsideAttachment.eq_of_notMem_range (MappingCylinder.square f)
      (windowInclusion_avoids_zero A p) h.symm
  exact middleTimes_ne_one p.1 (congrArg Prod.fst hp)

def window : TopCat.of (middleTimes × A) ⟶ space e f :=
  windowToMiddle f ≫ middle e f

theorem window_apply (p : middleTimes × A) : window e f p = tube e f (p.1.val, p.2) := rfl

theorem window_isOpenEmbedding : IsOpenEmbedding (window e f) :=
  PushoutOutsideAttachment.comp_isOpenEmbedding (square e f)
    (windowToMiddle f) (windowToMiddle_avoids_source f) (windowToMiddle_isOpenEmbedding f)

def overlap : Set (space e f) := lower e f ∩ upper e f

theorem window_mem_overlap (p : middleTimes × A) : window e f p ∈ overlap e f :=
  (tube_mem_overlap_iff e f p.1.val p.2).mpr p.1.property

def overlapParametrization : C(middleTimes × A, overlap e f) :=
  ⟨fun p ↦ ⟨window e f p, window_mem_overlap e f p⟩,
    (window e f).hom.continuous.subtype_mk _⟩

theorem overlapParametrization_isEmbedding : IsEmbedding (overlapParametrization e f) :=
  IsEmbedding.of_comp (overlapParametrization e f).continuous continuous_subtype_val
    (window_isOpenEmbedding e f).isEmbedding

theorem overlapParametrization_surjective : Function.Surjective (overlapParametrization e f) := by
  intro p
  obtain ⟨t, a, h, ht0, ht1⟩ := overlap_representative e f p
  exact ⟨(⟨t, ht0, ht1⟩, a), Subtype.ext h⟩

def overlapHomeomorph : (middleTimes × A) ≃ₜ overlap e f :=
  (overlapParametrization_isEmbedding e f).toHomeomorphOfSurjective
    (overlapParametrization_surjective e f)

theorem overlapHomeomorph_apply (p : middleTimes × A) :
    (overlapHomeomorph e f p).val = tube e f (p.1.val, p.2) := rfl

end NoExoticSixSphere.DoubleMappingCylinder
