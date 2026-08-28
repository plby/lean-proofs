import Wikipedia.HopfProblem.OrbitPairCylinderEndpoint
import Wikipedia.HopfProblem.OrbitPairPushoutDeformation
import Wikipedia.HopfProblem.OrbitPairSubdivisionStandardEquivalence

/-!
# The actual topological mapping cylinder

The space is the native `TopCat` pushout of a map and the zero endpoint
of the product cylinder. Its projection, source map, target inclusion,
and stationary deformation are given on that actual pushout.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits unitInterval

namespace Wikipedia.HopfProblem.OrbitPair.MappingCylinder

open HomotopyExtension

variable {A B : TopCat.{u}} (f : A ⟶ B)

def space : TopCat.{u} := pushout f (cylinderEndpoint A 0)

def target : B ⟶ space f := pushout.inl f (cylinderEndpoint A 0)

def cylinder : TopCat.of (I × A) ⟶ space f := pushout.inr f (cylinderEndpoint A 0)

def source : A ⟶ space f := cylinderEndpoint A 1 ≫ cylinder f

theorem square : IsPushout f (cylinderEndpoint A 0) (target f) (cylinder f) :=
  IsPushout.of_hasPushout _ _

def projection : space f ⟶ B :=
  pushout.desc (𝟙 B) (TopCat.ofHom (ContinuousMap.snd : C(I × A, A)) ≫ f) (by rfl)

theorem target_projection : target f ≫ projection f = 𝟙 B := pushout.inl_desc _ _ _

theorem cylinder_projection : cylinder f ≫ projection f =
    TopCat.ofHom (ContinuousMap.snd : C(I × A, A)) ≫ f := pushout.inr_desc _ _ _

theorem source_projection : source f ≫ projection f = f := by
  rw [source, Category.assoc, cylinder_projection]
  rfl

def cylinderDeformation (A : TopCat.{u}) :
    (ContinuousMap.id (I × A)).HomotopyRel
      ((cylinderEndpoint A 0).hom.comp ContinuousMap.snd) (Set.range (cylinderEndpoint A 0)) where
  toFun p := (σ p.1 * p.2.1, p.2.2)
  continuous_toFun := by fun_prop
  map_zero_left p := by simp
  map_one_left p := by simp [cylinderEndpoint]
  prop' := by
    rintro t _ ⟨a, rfl⟩
    change (σ t * 0, a) = (0, a)
    rw [mul_zero]

def deformation : (ContinuousMap.id (space f)).HomotopyRel
    (projection f ≫ target f).hom (Set.range (target f)) :=
  PushoutHomotopy.deformation (square f) (projection f)
    (TopCat.ofHom (ContinuousMap.snd : C(I × A, A)))
    (target_projection f) (cylinder_projection f) (cylinderDeformation A)

def targetEquiv : ContinuousMap.HomotopyEquiv B (space f) where
  toFun := (target f).hom
  invFun := (projection f).hom
  left_inv := by
    have h := congrArg TopCat.Hom.hom (target_projection f)
    change ((target f ≫ projection f).hom).Homotopic (ContinuousMap.id B)
    rw [h]
    exact ContinuousMap.Homotopic.refl _
  right_inv := ⟨(deformation f).toHomotopy.symm⟩

def projectionEquiv : ContinuousMap.HomotopyEquiv (space f) B := (targetEquiv f).symm

theorem target_hasHomotopyExtension : HasHomotopyExtension (target f) :=
  of_pushout (square f) (cylinderEndpoint_zero A)

def sourceTargetHomotopy : (source f).hom.Homotopy ((target f).hom.comp f.hom) where
  toFun p := cylinder f (σ p.1, p.2)
  continuous_toFun := (cylinder f).hom.continuous.comp
    ((continuous_symm.comp continuous_fst).prodMk continuous_snd)
  map_zero_left a := by simp [source, cylinderEndpoint]
  map_one_left a := by
    change cylinder f (σ 1, a) = target f (f a)
    rw [symm_one]
    exact (congrArg (fun m ↦ m a) (square f).w).symm

def sourceEquiv (e : ContinuousMap.HomotopyEquiv A B) (he : e.toFun = f.hom) :
    ContinuousMap.HomotopyEquiv A (space f) :=
  HomotopyEquivalence.replaceForward (e.trans (targetEquiv f)) (source f).hom
    ⟨(sourceTargetHomotopy f).cast rfl (by change _ = (target f).hom.comp e.toFun; rw [he])⟩

theorem sourceEquiv_forward (e : ContinuousMap.HomotopyEquiv A B) (he : e.toFun = f.hom) :
    (sourceEquiv f e he).toFun = (source f).hom := rfl

end Wikipedia.HopfProblem.OrbitPair.MappingCylinder
