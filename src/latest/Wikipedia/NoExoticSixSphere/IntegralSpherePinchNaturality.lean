import Wikipedia.NoExoticSixSphere.IntegralSphereHomotopyClass
import Wikipedia.NoExoticSixSphere.SphereThreeAntipodalHomotopy

/-!
# Postcomposition and common based representatives for integral sphere pinches

Postcomposition commutes with the actual hemisphere pinch, as an equality
of continuous maps. Two integral classes in a two-connected source admit
representatives with the common base value required by that pinch.
-/

noncomputable section

open Function ContinuousMap
open scoped Topology

namespace NoExoticSixSphere.SphereFold

theorem comp_pinch {E Y Z : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [TopologicalSpace Y] [TopologicalSpace Z] (v : UnitSphere E)
    (f g : C(UnitSphere E, Y)) (hbase : f (antipode v) = g (antipode v))
    (i : C(Y, Z)) :
    i.comp (pinch v f g hbase) =
      pinch v (i.comp f) (i.comp g) (congrArg i hbase) := by
  ext z
  change i (pinch v f g hbase z) =
    pinch v (i.comp f) (i.comp g) (congrArg i hbase) z
  rcases le_total 0 (height v z) with hz | hz
  · rw [pinch_north v f g hbase z hz,
      pinch_north v (i.comp f) (i.comp g) (congrArg i hbase) z hz]
    rfl
  · rw [pinch_south v f g hbase z hz,
      pinch_south v (i.comp f) (i.comp g) (congrArg i hbase) z hz]
    rfl

end NoExoticSixSphere.SphereFold

namespace NoExoticSixSphere.SmoothCube

open SphereSumNeck Wikipedia.HopfProblem.SingularMayerVietoris

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
  (x : X) [h₂ : Subsingleton (π_ 2 X x)]

include x h₂ in
theorem exists_common_pinch_representatives (a b : SingularHomology X 3) :
    ∃ f g : C(Sphere 3, X), f (antipode pinchPole) = g (antipode pinchPole) ∧
      integralSphereClass f = a ∧ integralSphereClass g = b := by
  let f := integralClassRepresentative x a
  let g := integralClassRepresentative x b
  let F := f.val.comp SphereThreeAntipodal.map
  let G := g.val.comp SphereThreeAntipodal.map
  have HF : f.val.Homotopic F :=
    (Homotopic.refl f.val).comp ⟨SphereThreeAntipodal.homotopy⟩
  have HG : g.val.Homotopic G :=
    (Homotopic.refl g.val).comp ⟨SphereThreeAntipodal.homotopy⟩
  refine ⟨F, G, ?_, ?_, ?_⟩
  · have ha : SphereThreeAntipodal.map (antipode pinchPole) = spherePole 3 :=
      Subtype.ext (neg_neg _)
    change f.val (SphereThreeAntipodal.map (antipode pinchPole)) =
      g.val (SphereThreeAntipodal.map (antipode pinchPole))
    rw [ha, f.property, g.property]
  · exact (integralSphereClass_homotopic HF).symm.trans
      (integralSphereClass_representative x a)
  · exact (integralSphereClass_homotopic HG).symm.trans
      (integralSphereClass_representative x b)

end NoExoticSixSphere.SmoothCube
