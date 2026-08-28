import Wikipedia.NoExoticSixSphere.SphereInverseRadialFrameObstruction
import Wikipedia.NoExoticSixSphere.SpanningDiskSourceTwist

/-!
# The actual source twist of any constant Hopf-product frame is nonextendible

Two fixed injective operators of the same dimensions differ by an ambient
linear equivalence, obtained by extending the isomorphism of their ranges.
This identifies the actual twisted constant frame with fifteen identity
columns followed by the inverse radial frame. All coordinate changes are
fixed; the sphere-dependent inverse radial block is retained and detected.
-/

noncomputable section

namespace NoExoticSixSphere

open GLOrthonormalization Stiefel DiskBoundary

namespace Stiefel.Monomorphism

theorem exists_target_coordinates {N n : ℕ} (A B : Space N n) :
    ∃ U : Vector N ≃L[ℝ] Vector N, ∀ v, U (B.val v) = A.val v := by
  let eA : Vector n ≃ₗ[ℝ] A.val.range := LinearEquiv.ofInjective A.val.toLinearMap A.property
  let eB : Vector n ≃ₗ[ℝ] B.val.range := LinearEquiv.ofInjective B.val.toLinearMap B.property
  obtain ⟨U, hU⟩ := Submodule.exists_linearEquiv_restrict_eq (eB.symm.trans eA)
  refine ⟨U.toContinuousLinearEquiv, ?_⟩
  intro v
  have h := hU (eB v)
  rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at h
  exact h.symm

end Stiefel.Monomorphism

namespace SpanningDiskFrameCoordinates

open SphereThreeTangentFrame FrameBlockCoordinates

attribute [local irreducible] targetCoordinates sourceShuffle sourceSphere

def fixedFourInclusion : Monomorphism.Space 7 4 :=
  ⟨EuclideanSpace.finAddEquivProd.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ (Vector 4) (Vector 3)), by
      intro v w h
      have he := congrArg (EuclideanSpace.finAddEquivProd (n := 4) (m := 3)) h
      change EuclideanSpace.finAddEquivProd
        (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3))) =
          EuclideanSpace.finAddEquivProd
            (EuclideanSpace.finAddEquivProd.symm (w, (0 : Vector 3))) at he
      rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply] at he
      exact congrArg Prod.fst he⟩

def standardFixedFrame : Monomorphism.Space 22 19 :=
  Monomorphism.frontBlockMap 15 fixedFourInclusion

def actualFixedFrame (F : Monomorphism.Space 16 13) : Monomorphism.Space 22 19 :=
  Monomorphism.recoordinate (targetCoordinates 16) (sourceShuffle 10)
    (Monomorphism.blockMap 6 F)

theorem actualFixedFrame_apply (F : Monomorphism.Space 16 13) (v : Vector 19) :
    (actualFixedFrame F).val v =
      targetCoordinates 16 (BlockSum.operator 6 F.val (sourceShuffle 10 v)) := rfl

theorem twisted_constant_apply (F : Monomorphism.Space 16 13) (s : Sphere 3) (v : Vector 19) :
    (twistedBlockMap (k := 10) (ContinuousMap.const _ F) s).val v =
      (actualFixedFrame F).val ((sourceSphere 10 s).symm v) := by
  rw [twistedBlockMap_value, actualFixedFrame_apply]
  rfl

theorem standardFixedFrame_apply (v : Vector 19) :
    standardFixedFrame.val v = EuclideanSpace.finAddEquivProd.symm
      ((EuclideanSpace.finAddEquivProd (n := 15) (m := 4) v).1,
        EuclideanSpace.finAddEquivProd.symm
          ((EuclideanSpace.finAddEquivProd (n := 15) (m := 4) v).2, (0 : Vector 3))) := rfl

theorem standardFixedFrame_sourceSphere (s : Sphere 3) (v : Vector 19) :
    standardFixedFrame.val ((sourceSphere 10 s).symm v) =
      (Monomorphism.frontBlockMap 15 (liftedInverseRadialMap s)).val v := by
  rw [sourceSphere_symm_apply, standardFixedFrame_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  change _ = EuclideanSpace.finAddEquivProd.symm
    ((EuclideanSpace.finAddEquivProd (n := 15) (m := 4) v).1,
      liftedInverseRadialOperator s
        (EuclideanSpace.finAddEquivProd (n := 15) (m := 4) v).2)
  rw [liftedInverseRadialOperator_apply]

theorem twisted_constant_not_extends (F : Monomorphism.Space 16 13) :
    ¬ Extends (twistedBlockMap (k := 10) (ContinuousMap.const _ F)) := by
  obtain ⟨U, hU⟩ := Monomorphism.exists_target_coordinates (actualFixedFrame F) standardFixedFrame
  let G := (Monomorphism.frontBlockMap 15).comp liftedInverseRadialMap
  have he (s : Sphere 3) : twistedBlockMap (k := 10) (ContinuousMap.const _ F) s =
      Monomorphism.recoordinate U (ContinuousLinearEquiv.refl ℝ (Vector 19)) (G s) := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    rw [twisted_constant_apply, Monomorphism.recoordinate_apply]
    change (actualFixedFrame F).val ((sourceSphere 10 s).symm v) =
      U ((Monomorphism.frontBlockMap 15 (liftedInverseRadialMap s)).val v)
    rw [← standardFixedFrame_sourceSphere]
    exact (hU ((sourceSphere 10 s).symm v)).symm
  have hext : Extends (twistedBlockMap (k := 10) (ContinuousMap.const _ F)) ↔ Extends G :=
    Monomorphism.extends_recoordinate_iff (fun _ ↦ U)
      (fun _ ↦ ContinuousLinearEquiv.refl ℝ (Vector 19))
      continuous_const continuous_const continuous_const continuous_const
      G (twistedBlockMap (k := 10) (ContinuousMap.const _ F)) he
  intro h
  apply liftedInverseRadialMap_not_extends
  exact (Monomorphism.extends_frontBlockMap_iff (by decide) rfl 15
    liftedInverseRadialMap).mp (hext.mp h)

end SpanningDiskFrameCoordinates

end NoExoticSixSphere
