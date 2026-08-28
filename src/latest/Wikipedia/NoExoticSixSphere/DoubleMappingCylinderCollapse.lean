import Wikipedia.NoExoticSixSphere.DoubleMappingCylinderFamilies

/-!
# Collapsing the actual double mapping cylinder

The span's ordinary pushout receives a collapse map that is constant
along each connecting cylinder. Homotopy extension across the left
attaching map supplies a candidate inverse, with its values on the two
original pushout pieces proved exactly. The two inverse homotopies are
constructed separately.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology unitInterval
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.DoubleMappingCylinder

variable {A X Y P : TopCat.{u}} (e : A ⟶ X) (f : A ⟶ Y)
    {i : X ⟶ P} {j : Y ⟶ P} (hP : IsPushout e f i j)

def collapseTube : C(I × A, P) := j.hom.comp (f.hom.comp ContinuousMap.snd)

def collapse : space e f ⟶ P :=
  glue e f j.hom (collapseTube f (j := j)) (fun _ ↦ rfl) i.hom
    (fun a ↦ (congrArg (fun m ↦ m a) hP.w).symm)

theorem left_collapse : left e f ≫ collapse e f hP = i :=
  left_glue e f j.hom (collapseTube f (j := j)) (fun _ ↦ rfl) i.hom
    (fun a ↦ (congrArg (fun m ↦ m a) hP.w).symm)

theorem right_collapse : right e f ≫ collapse e f hP = j :=
  right_glue e f j.hom (collapseTube f (j := j)) (fun _ ↦ rfl) i.hom
    (fun a ↦ (congrArg (fun m ↦ m a) hP.w).symm)

theorem tube_collapse : tube e f ≫ collapse e f hP = TopCat.ofHom (collapseTube f (j := j)) :=
  tube_glue e f j.hom (collapseTube f (j := j)) (fun _ ↦ rfl) i.hom
    (fun a ↦ (congrArg (fun m ↦ m a) hP.w).symm)

def boundaryMotion : C(I × A, space e f) :=
  (tube e f).hom.comp ⟨fun p ↦ (σ p.1, p.2),
    (continuous_symm.comp continuous_fst).prodMk continuous_snd⟩

theorem boundaryMotion_zero (a : A) : boundaryMotion e f (0, a) = left e f (e a) := by
  change tube e f (σ 0, a) = _
  rw [symm_zero, tube_one]

theorem boundaryMotion_one (a : A) : boundaryMotion e f (1, a) = right e f (f a) := by
  change tube e f (σ 1, a) = _
  rw [symm_one, tube_zero]

theorem exists_extension (he : HomotopyExtension.HasHomotopyExtension e) :
    ∃ K : C(I × X, space e f), (∀ x, K (0, x) = left e f x) ∧
      ∀ s a, K (s, e a) = tube e f (σ s, a) :=
  he (space e f) (left e f).hom (boundaryMotion e f) (boundaryMotion_zero e f)

variable (K : C(I × X, space e f))
    (hKe : ∀ s a, K (s, e a) = tube e f (σ s, a))

def inverseLeft : C(X, space e f) :=
  K.comp ⟨fun x ↦ (1, x), continuous_const.prodMk continuous_id⟩

include hKe in
theorem inverse_compatible : e ≫ TopCat.ofHom (inverseLeft e f K) = f ≫ right e f := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro a
  change K (1, e a) = right e f (f a)
  rw [hKe, symm_one, tube_zero]

def inverseMap : P ⟶ space e f :=
  hP.desc (TopCat.ofHom (inverseLeft e f K)) (right e f) (inverse_compatible e f K hKe)

theorem left_inverseMap : i ≫ inverseMap e f hP K hKe = TopCat.ofHom (inverseLeft e f K) :=
  hP.inl_desc _ _ (inverse_compatible e f K hKe)

theorem right_inverseMap : j ≫ inverseMap e f hP K hKe = right e f :=
  hP.inr_desc _ _ (inverse_compatible e f K hKe)

end NoExoticSixSphere.DoubleMappingCylinder
