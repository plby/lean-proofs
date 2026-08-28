import Wikipedia.HopfProblem.DegreeCollapseSevenAttachingTubeCoordinates
import Wikipedia.HopfProblem.DegreeCollapseIntegralTubeCoreUnit
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-!
# An actual whole-product parametrization of the original attaching tube

The standard ball homeomorphism preserves zero. Composing it with the
original smooth tube coordinates gives a homeomorphism from S3 times R4
onto the original open tube. Its zero section is exactly the supplied
attaching sphere, and its compact core support is that original image.
-/

noncomputable section

open Set Metric TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct

open NoExoticSixSphere GLOrthonormalization

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def normalBallHomeomorph : Vector 4 ≃ₜ ball (0 : Vector 4) A.radius :=
  (Homeomorph.Set.univ (Vector 4)).symm.trans
    ((Homeomorph.setCongr (OpenPartialHomeomorph.univBall_source
      (0 : Vector 4) A.radius).symm).trans
      ((OpenPartialHomeomorph.univBall (0 : Vector 4) A.radius).toHomeomorphSourceTarget.trans
        (Homeomorph.setCongr (OpenPartialHomeomorph.univBall_target
          (0 : Vector 4) A.radius_pos))))

theorem normalBallHomeomorph_zero : (A.normalBallHomeomorph 0).val = 0 :=
  OpenPartialHomeomorph.univBall_apply_zero (0 : Vector 4) A.radius

def openTubeParameterHomeomorph :
    (Sphere 3 × ball (0 : Vector 4) A.radius) ≃ₜ A.openTubeDomain where
  toFun p := ⟨(p.1, p.2.val), mem_univ _, p.2.property⟩
  invFun p := (p.val.1, ⟨p.val.2, p.property.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_fst.prodMk
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  continuous_invFun := (continuous_fst.comp continuous_subtype_val).prodMk
    ((continuous_snd.comp continuous_subtype_val).subtype_mk _)

def tubeOpen : Opens M := ⟨A.tubeCoordinates.target, A.tubeCoordinates.open_target⟩

def tubeProductHomeomorph : (Sphere 3 × Vector 4) ≃ₜ A.tubeOpen :=
  let g := A.tubeCoordinates.toOpenPartialHomeomorph.toHomeomorphSourceTarget
  ((Homeomorph.refl (Sphere 3)).prodCongr A.normalBallHomeomorph).trans
    (A.openTubeParameterHomeomorph.trans g)

theorem tubeProductHomeomorph_core (s : Sphere 3) :
    (A.tubeProductHomeomorph (s, 0)).val = f s := by
  change A.tube (s, (A.normalBallHomeomorph 0).val) = f s
  rw [normalBallHomeomorph_zero]
  exact A.tube_core s

theorem originalTubeCoreSupport :
    (IntegralTubeCore.coreSupport A.tubeOpen A.tubeProductHomeomorph : Set M) = range f := by
  ext x
  constructor
  · rintro ⟨p, hp, hx⟩
    have hp0 : p.2 = 0 := norm_eq_zero.mp (le_antisymm hp (norm_nonneg _))
    have he : p = (p.1, 0) := Prod.ext rfl hp0
    rw [he] at hx
    exact ⟨p.1, (A.tubeProductHomeomorph_core p.1).symm.trans hx⟩
  · rintro ⟨s, rfl⟩
    exact ⟨(s, 0), norm_zero.le, A.tubeProductHomeomorph_core s⟩

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct
