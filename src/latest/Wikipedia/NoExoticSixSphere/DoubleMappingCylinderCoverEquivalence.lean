import Wikipedia.NoExoticSixSphere.DoubleMappingCylinderCoverMotion
import Wikipedia.NoExoticSixSphere.DoubleMappingCylinderEndEmbedding

/-!
# Actual homotopy equivalences for the two open pieces of the double cylinder

Each endpoint motion defines a continuous retraction using the inverse of
the actual end-space embedding on its image. Both homotopy equivalences
have the literal end inclusion as their forward map. On a cylinder point,
the inverse maps recover the original right or left attaching map.
-/

noncomputable section

universe u

open CategoryTheory Set Topology unitInterval

namespace NoExoticSixSphere.DoubleMappingCylinder

variable {A X Y : TopCat.{u}} (e : A ⟶ X) (f : A ⟶ Y)

def lowerInclusion : C(Y, lower e f) :=
  ⟨fun y ↦ ⟨right e f y, right_mem_lower e f y⟩, (right e f).hom.continuous.subtype_mk _⟩

def upperInclusion : C(X, upper e f) :=
  ⟨fun x ↦ ⟨left e f x, left_mem_upper e f x⟩, (left e f).hom.continuous.subtype_mk _⟩

def lowerRetraction : C(lower e f, Y) :=
  ⟨fun p ↦ (right_isClosedEmbedding e f).isEmbedding.toHomeomorph.symm
      ⟨lowerMotion e f (1, p.val), lowerMotion_terminal e f p⟩,
    (right_isClosedEmbedding e f).isEmbedding.toHomeomorph.symm.continuous.comp
      (((lowerMotion e f).continuous.comp
        (continuous_const.prodMk continuous_subtype_val)).subtype_mk _)⟩

def upperRetraction : C(upper e f, X) :=
  ⟨fun p ↦ (left_isClosedEmbedding e f).isEmbedding.toHomeomorph.symm
      ⟨upperMotion e f (1, p.val), upperMotion_terminal e f p⟩,
    (left_isClosedEmbedding e f).isEmbedding.toHomeomorph.symm.continuous.comp
      (((upperMotion e f).continuous.comp
        (continuous_const.prodMk continuous_subtype_val)).subtype_mk _)⟩

theorem right_lowerRetraction (p : lower e f) :
    right e f (lowerRetraction e f p) = lowerMotion e f (1, p.val) :=
  congrArg Subtype.val ((right_isClosedEmbedding e f).isEmbedding.toHomeomorph.apply_symm_apply
    ⟨lowerMotion e f (1, p.val), lowerMotion_terminal e f p⟩)

theorem left_upperRetraction (p : upper e f) :
    left e f (upperRetraction e f p) = upperMotion e f (1, p.val) :=
  congrArg Subtype.val ((left_isClosedEmbedding e f).isEmbedding.toHomeomorph.apply_symm_apply
    ⟨upperMotion e f (1, p.val), upperMotion_terminal e f p⟩)

theorem lowerRetraction_inclusion (y : Y) :
    lowerRetraction e f (lowerInclusion e f y) = y := by
  apply (right_isClosedEmbedding e f).injective
  rw [right_lowerRetraction]
  exact lowerMotion_right e f 1 y

theorem upperRetraction_inclusion (x : X) :
    upperRetraction e f (upperInclusion e f x) = x := by
  apply (left_isClosedEmbedding e f).injective
  rw [left_upperRetraction]
  exact upperMotion_left e f 1 x

def lowerRetractionHomotopy : (ContinuousMap.id (lower e f)).Homotopy
    ((lowerInclusion e f).comp (lowerRetraction e f)) where
  toContinuousMap := lowerDeformation e f
  map_zero_left p := Subtype.ext (lowerMotion_initial e f p.val)
  map_one_left p := Subtype.ext (right_lowerRetraction e f p).symm

def upperRetractionHomotopy : (ContinuousMap.id (upper e f)).Homotopy
    ((upperInclusion e f).comp (upperRetraction e f)) where
  toContinuousMap := upperDeformation e f
  map_zero_left p := Subtype.ext (upperMotion_initial e f p.val)
  map_one_left p := Subtype.ext (left_upperRetraction e f p).symm

def lowerEquiv : ContinuousMap.HomotopyEquiv Y (lower e f) where
  toFun := lowerInclusion e f
  invFun := lowerRetraction e f
  left_inv := by
    have h : (lowerRetraction e f).comp (lowerInclusion e f) = ContinuousMap.id Y :=
      ContinuousMap.ext (lowerRetraction_inclusion e f)
    rw [h]
  right_inv := ⟨(lowerRetractionHomotopy e f).symm⟩

def upperEquiv : ContinuousMap.HomotopyEquiv X (upper e f) where
  toFun := upperInclusion e f
  invFun := upperRetraction e f
  left_inv := by
    have h : (upperRetraction e f).comp (upperInclusion e f) = ContinuousMap.id X :=
      ContinuousMap.ext (upperRetraction_inclusion e f)
    rw [h]
  right_inv := ⟨(upperRetractionHomotopy e f).symm⟩

theorem lowerEquiv_forward : (lowerEquiv e f).toFun = lowerInclusion e f := rfl

theorem upperEquiv_forward : (upperEquiv e f).toFun = upperInclusion e f := rfl

theorem lowerRetraction_tube (p : lower e f) (t : I) (a : A)
    (hp : p.val = tube e f (t, a)) : lowerRetraction e f p = f a := by
  have ht : (t : ℝ) < 2 / 3 := by
    have h := p.property
    change (height e f p.val : ℝ) < 2 / 3 at h
    rw [hp, height_tube] at h
    exact h
  apply (right_isClosedEmbedding e f).injective
  rw [right_lowerRetraction, hp, lowerMotion_tube,
    Clock.lowerClock_terminal_zero t ht.le, tube_zero]

theorem upperRetraction_tube (p : upper e f) (t : I) (a : A)
    (hp : p.val = tube e f (t, a)) : upperRetraction e f p = e a := by
  have ht : (1 : ℝ) / 3 < t := by
    have h := p.property
    change (1 : ℝ) / 3 < height e f p.val at h
    rw [hp, height_tube] at h
    exact h
  apply (left_isClosedEmbedding e f).injective
  rw [left_upperRetraction, hp, upperMotion_tube,
    Clock.upperClock_terminal_one t ht.le, tube_one]

end NoExoticSixSphere.DoubleMappingCylinder
