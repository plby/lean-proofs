import Wikipedia.NoExoticSixSphere.DoubleMappingCylinderCover
import Wikipedia.NoExoticSixSphere.DoubleMappingCylinderFamilies

/-!
# Retiming the actual double mapping cylinder while fixing both ends

A jointly continuous family of interval maps fixing zero and one glues
to a family on the double mapping cylinder. Its actual height is the
retimed original height, and both end spaces remain fixed exactly.
-/

noncomputable section

universe u

open CategoryTheory Topology unitInterval

namespace NoExoticSixSphere.DoubleMappingCylinder

variable {A X Y : TopCat.{u}} (e : A ⟶ X) (f : A ⟶ Y)
    (φ : C(I × I, I)) (h0 : ∀ s, φ (s, 0) = 0) (h1 : ∀ s, φ (s, 1) = 1)

def stationaryLeft : C(I × X, space e f) := (left e f).hom.comp ContinuousMap.snd

def stationaryRight : C(I × Y, space e f) := (right e f).hom.comp ContinuousMap.snd

def retimeTube : C(I × (I × A), space e f) :=
  (tube e f).hom.comp ⟨fun p ↦ (φ (p.1, p.2.1), p.2.2),
    (φ.continuous.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk continuous_snd.snd⟩

include h0 in
theorem retimeTube_zero (s : I) (a : A) :
    retimeTube e f φ (s, (0, a)) = stationaryRight e f (s, f a) := by
  change tube e f (φ (s, 0), a) = right e f (f a)
  rw [h0, tube_zero]

include h1 in
theorem retimeTube_one (s : I) (a : A) :
    retimeTube e f φ (s, (1, a)) = stationaryLeft e f (s, e a) := by
  change tube e f (φ (s, 1), a) = left e f (e a)
  rw [h1, tube_one]

def retimeFamily : C(I × space e f, space e f) :=
  family e f (stationaryLeft e f) (stationaryRight e f) (retimeTube e f φ)
    (retimeTube_zero e f φ h0) (retimeTube_one e f φ h1)

theorem retimeFamily_left (s : I) (x : X) : retimeFamily e f φ h0 h1 (s, left e f x) = left e f x :=
  family_left e f (stationaryLeft e f) (stationaryRight e f) (retimeTube e f φ)
    (retimeTube_zero e f φ h0) (retimeTube_one e f φ h1) s x

theorem retimeFamily_right (s : I) (y : Y) :
    retimeFamily e f φ h0 h1 (s, right e f y) = right e f y :=
  family_right e f (stationaryLeft e f) (stationaryRight e f) (retimeTube e f φ)
    (retimeTube_zero e f φ h0) (retimeTube_one e f φ h1) s y

theorem retimeFamily_tube (s t : I) (a : A) :
    retimeFamily e f φ h0 h1 (s, tube e f (t, a)) = tube e f (φ (s, t), a) :=
  family_tube e f (stationaryLeft e f) (stationaryRight e f) (retimeTube e f φ)
    (retimeTube_zero e f φ h0) (retimeTube_one e f φ h1) s t a

theorem height_retimeFamily (s : I) (p : space e f) :
    height e f (retimeFamily e f φ h0 h1 (s, p)) = φ (s, height e f p) := by
  rcases jointly_surjective e f p with ⟨x, rfl⟩ | ⟨y, rfl⟩ | ⟨t, a, rfl⟩
  · rw [retimeFamily_left, height_left, h1]
  · rw [retimeFamily_right, height_right, h0]
  · rw [retimeFamily_tube, height_tube, height_tube]

theorem retimeFamily_initial (hinit : ∀ t, φ (0, t) = t) (p : space e f) :
    retimeFamily e f φ h0 h1 (0, p) = p := by
  rcases jointly_surjective e f p with ⟨x, rfl⟩ | ⟨y, rfl⟩ | ⟨t, a, rfl⟩
  · exact retimeFamily_left e f φ h0 h1 0 x
  · exact retimeFamily_right e f φ h0 h1 0 y
  · rw [retimeFamily_tube, hinit]

end NoExoticSixSphere.DoubleMappingCylinder
