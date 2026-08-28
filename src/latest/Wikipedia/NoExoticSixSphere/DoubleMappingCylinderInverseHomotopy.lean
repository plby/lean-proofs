import Wikipedia.NoExoticSixSphere.DoubleMappingCylinderCollapse

/-!
# The inverse homotopy on the actual double mapping cylinder

The extended left motion is glued to the fixed right space and the
shrinking connecting cylinder. Endpoint compatibility is exact, so this
is a homotopy on the original double mapping cylinder from its identity
to the candidate inverse after collapse.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology unitInterval
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.DoubleMappingCylinder

variable {A X Y P : TopCat.{u}} (e : A ⟶ X) (f : A ⟶ Y)
    {i : X ⟶ P} {j : Y ⟶ P} (hP : IsPushout e f i j)
    (K : C(I × X, space e f)) (hK0 : ∀ x, K (0, x) = left e f x)
    (hKe : ∀ s a, K (s, e a) = tube e f (σ s, a))

def fixedRight : C(I × Y, space e f) := (right e f).hom.comp ContinuousMap.snd

def inverseTube : C(I × (I × A), space e f) :=
  (tube e f).hom.comp ⟨fun p ↦ (σ p.1 * p.2.1, p.2.2),
    ((continuous_symm.comp continuous_fst).mul continuous_snd.fst).prodMk continuous_snd.snd⟩

theorem inverseTube_zero (s : I) (a : A) :
    inverseTube e f (s, (0, a)) = fixedRight e f (s, f a) := by
  change tube e f (σ s * 0, a) = right e f (f a)
  rw [mul_zero, tube_zero]

include hKe in
theorem inverseTube_one (s : I) (a : A) : inverseTube e f (s, (1, a)) = K (s, e a) := by
  change tube e f (σ s * 1, a) = _
  rw [mul_one, hKe]

def inverseFamily : C(I × space e f, space e f) :=
  family e f K (fixedRight e f) (inverseTube e f) (inverseTube_zero e f)
    (inverseTube_one e f K hKe)

theorem inverseFamily_left (s : I) (x : X) :
    inverseFamily e f K hKe (s, left e f x) = K (s, x) :=
  family_left e f K (fixedRight e f) (inverseTube e f) (inverseTube_zero e f)
    (inverseTube_one e f K hKe) s x

theorem inverseFamily_right (s : I) (y : Y) :
    inverseFamily e f K hKe (s, right e f y) = right e f y :=
  family_right e f K (fixedRight e f) (inverseTube e f) (inverseTube_zero e f)
    (inverseTube_one e f K hKe) s y

theorem inverseFamily_tube (s t : I) (a : A) :
    inverseFamily e f K hKe (s, tube e f (t, a)) = tube e f (σ s * t, a) :=
  family_tube e f K (fixedRight e f) (inverseTube e f) (inverseTube_zero e f)
    (inverseTube_one e f K hKe) s t a

include hK0 in
theorem inverseFamily_zero (p : space e f) : inverseFamily e f K hKe (0, p) = p := by
  rcases jointly_surjective e f p with ⟨x, rfl⟩ | ⟨y, rfl⟩ | ⟨t, a, rfl⟩
  · rw [inverseFamily_left, hK0]
  · exact inverseFamily_right e f K hKe 0 y
  · rw [inverseFamily_tube, symm_zero, one_mul]

theorem inverseFamily_one (p : space e f) :
    inverseFamily e f K hKe (1, p) = inverseMap e f hP K hKe (collapse e f hP p) := by
  rcases jointly_surjective e f p with ⟨x, rfl⟩ | ⟨y, rfl⟩ | ⟨t, a, rfl⟩
  · rw [inverseFamily_left]
    have hc : collapse e f hP (left e f x) = i x :=
      congrArg (fun m ↦ m x) (left_collapse e f hP)
    have hi : inverseMap e f hP K hKe (i x) = K (1, x) :=
      congrArg (fun m ↦ m x) (left_inverseMap e f hP K hKe)
    exact hi.symm.trans (congrArg (inverseMap e f hP K hKe) hc.symm)
  · rw [inverseFamily_right]
    have hc : collapse e f hP (right e f y) = j y :=
      congrArg (fun m ↦ m y) (right_collapse e f hP)
    have hj : inverseMap e f hP K hKe (j y) = right e f y :=
      congrArg (fun m ↦ m y) (right_inverseMap e f hP K hKe)
    exact hj.symm.trans (congrArg (inverseMap e f hP K hKe) hc.symm)
  · rw [inverseFamily_tube, symm_one, zero_mul, tube_zero]
    have hc : collapse e f hP (tube e f (t, a)) = j (f a) :=
      congrArg (fun m ↦ m (t, a)) (tube_collapse e f hP)
    have hj : inverseMap e f hP K hKe (j (f a)) = right e f (f a) :=
      congrArg (fun m ↦ m (f a)) (right_inverseMap e f hP K hKe)
    exact hj.symm.trans (congrArg (inverseMap e f hP K hKe) hc.symm)

def inverseHomotopy : (ContinuousMap.id (space e f)).Homotopy
    (collapse e f hP ≫ inverseMap e f hP K hKe).hom where
  toContinuousMap := inverseFamily e f K hKe
  map_zero_left := inverseFamily_zero e f K hK0 hKe
  map_one_left := inverseFamily_one e f hP K hKe

end NoExoticSixSphere.DoubleMappingCylinder
