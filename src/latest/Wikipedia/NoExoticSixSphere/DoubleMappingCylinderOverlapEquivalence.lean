import Wikipedia.NoExoticSixSphere.DoubleMappingCylinderOverlap
import Mathlib.Analysis.Convex.Basic

/-!
# Midpoint equivalence and exact attaching-map coordinates on the overlap

The open middle interval contracts linearly to its midpoint. Transport
through the proved overlap homeomorphism gives a homotopy equivalence
whose forward map is literally the midpoint of the cylinder. Composing
it with either cover inclusion and the corresponding retraction gives
the original attaching map exactly.
-/

noncomputable section

universe u

open CategoryTheory Set Topology unitInterval

namespace NoExoticSixSphere.DoubleMappingCylinder

def middlePoint : middleTimes := ⟨⟨1 / 2, by norm_num⟩, by norm_num [middleTimes]⟩

theorem middleCombination_mem (s : I) (t : middleTimes) :
    Set.Icc.convexComb t.val middlePoint.val s ∈ middleTimes := by
  have h := (convex_Ioo (𝕜 := ℝ) ((1 : ℝ) / 3) (2 / 3))
    t.property middlePoint.property (sub_nonneg.mpr s.property.2) s.property.1
    (sub_add_cancel 1 (s : ℝ))
  exact h

def middleContraction : C(I × middleTimes, middleTimes) :=
  ⟨fun p ↦ ⟨Set.Icc.convexComb p.2.val middlePoint.val p.1,
      middleCombination_mem p.1 p.2⟩,
    (Set.Icc.continuous_convexComb_prod.comp
      ((continuous_subtype_val.comp continuous_snd).prodMk
        (continuous_const.prodMk continuous_fst))).subtype_mk _⟩

theorem middleContraction_initial (t : middleTimes) : middleContraction (0, t) = t :=
  Subtype.ext (Set.Icc.convexComb_zero t.val middlePoint.val)

theorem middleContraction_terminal (t : middleTimes) :
    middleContraction (1, t) = middlePoint :=
  Subtype.ext (Set.Icc.convexComb_one t.val middlePoint.val)

theorem middleContraction_fixed (s : I) : middleContraction (s, middlePoint) = middlePoint :=
  Subtype.ext (Set.Icc.convexComb_eq middlePoint.val s)

def middleSection (A : TopCat.{u}) : C(A, middleTimes × A) :=
  ⟨fun a ↦ (middlePoint, a), continuous_const.prodMk continuous_id⟩

def middleProductHomotopy (A : TopCat.{u}) : (ContinuousMap.id (middleTimes × A)).Homotopy
    ((middleSection A).comp ContinuousMap.snd) where
  toFun p := (middleContraction (p.1, p.2.1), p.2.2)
  continuous_toFun := (middleContraction.continuous.comp
    (continuous_fst.prodMk continuous_snd.fst)).prodMk continuous_snd.snd
  map_zero_left p := Prod.ext (middleContraction_initial p.1) rfl
  map_one_left p := Prod.ext (middleContraction_terminal p.1) rfl

def middleProductEquiv (A : TopCat.{u}) : ContinuousMap.HomotopyEquiv A (middleTimes × A) where
  toFun := middleSection A
  invFun := ContinuousMap.snd
  left_inv := ContinuousMap.Homotopic.refl _
  right_inv := ⟨(middleProductHomotopy A).symm⟩

variable {A X Y : TopCat.{u}} (e : A ⟶ X) (f : A ⟶ Y)

def overlapEquiv : ContinuousMap.HomotopyEquiv A (overlap e f) :=
  (middleProductEquiv A).trans (overlapHomeomorph e f).toHomotopyEquiv

theorem overlapEquiv_forward (a : A) :
    ((overlapEquiv e f).toFun a).val = tube e f (middlePoint.val, a) := rfl

def overlapToLower : C(overlap e f, lower e f) :=
  ⟨fun p ↦ ⟨p.val, p.property.1⟩, continuous_subtype_val.subtype_mk _⟩

def overlapToUpper : C(overlap e f, upper e f) :=
  ⟨fun p ↦ ⟨p.val, p.property.2⟩, continuous_subtype_val.subtype_mk _⟩

theorem lowerRetraction_midpoint :
    (lowerRetraction e f).comp ((overlapToLower e f).comp (overlapEquiv e f).toFun) = f.hom := by
  apply ContinuousMap.ext
  intro a
  exact lowerRetraction_tube e f _ middlePoint.val a rfl

theorem upperRetraction_midpoint :
    (upperRetraction e f).comp ((overlapToUpper e f).comp (overlapEquiv e f).toFun) = e.hom := by
  apply ContinuousMap.ext
  intro a
  exact upperRetraction_tube e f _ middlePoint.val a rfl

end NoExoticSixSphere.DoubleMappingCylinder
