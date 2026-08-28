import Wikipedia.NoExoticSixSphere.CollapsedSubspace
import Wikipedia.NoExoticSixSphere.DoubleMappingCylinderSimplyConnected

/-!
# The literal subspace-collapse pushout and simple connectivity

The quotient is the actual pushout of the subspace inclusion and its
map to a point. If that inclusion has homotopy extension, the proved
double-cylinder comparison and van Kampen transfer simple connectivity.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.CollapsedSubspacePushout

variable {X : Type} [TopologicalSpace X] (A : Set X) (a : A)

def inclusion : TopCat.of A ⟶ TopCat.of X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

def toPoint : TopCat.of A ⟶ TopCat.of Unit := TopCat.ofHom (ContinuousMap.const _ ())

def point : TopCat.of Unit ⟶ TopCat.of (CollapsedSubspace.Space A) :=
  TopCat.ofHom (ContinuousMap.const _ (CollapsedSubspace.quotientMap A a.val))

def quotient : TopCat.of X ⟶ TopCat.of (CollapsedSubspace.Space A) :=
  TopCat.ofHom (CollapsedSubspace.quotientMap A)

theorem square : inclusion A ≫ quotient A = toPoint A ≫ point A a := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  exact (CollapsedSubspace.quotientMap_eq_iff A x.val a.val).mpr
    (Or.inr ⟨x.property, a.property⟩)

theorem isPushout : IsPushout (inclusion A) (toPoint A) (quotient A) (point A a) := by
  apply IsPushout.mk' (square A a)
  · intro Z φ ψ he _
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro y
    obtain ⟨x, rfl⟩ := (CollapsedSubspace.isQuotientMap A).surjective y
    exact congrArg (fun m ↦ m x) he
  · intro Z F G hFG
    have hF (x : A) : F x.val = G () := congrArg (fun m ↦ m x) hFG
    let L := CollapsedSubspace.lift A F.hom
      (fun x hx y hy ↦ (hF ⟨x, hx⟩).trans (hF ⟨y, hy⟩).symm)
    refine ⟨TopCat.ofHom L, ?_, ?_⟩
    · apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro x
      rfl
    · apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro u
      cases u
      exact hF a

include a in
theorem simplyConnectedSpace [SimplyConnectedSpace X] [PathConnectedSpace A]
    (he : HomotopyExtension.HasHomotopyExtension (inclusion A)) :
    SimplyConnectedSpace (CollapsedSubspace.Space A) :=
  DoubleMappingCylinder.pushout_simplyConnectedSpace (inclusion A) (toPoint A)
    (isPushout A a) he

end NoExoticSixSphere.CollapsedSubspacePushout
