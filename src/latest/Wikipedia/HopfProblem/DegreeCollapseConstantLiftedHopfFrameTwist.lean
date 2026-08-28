import Wikipedia.NoExoticSixSphere.SphereInverseRadialFrameObstruction
import Wikipedia.NoExoticSixSphere.SpanningDiskSourceTwist
import Wikipedia.NoExoticSixSphere.InjectiveOperatorDimensionParity

/-!
# Nonzero parity of the actual source twist in the lifted Hopf dimensions

Retain the original twist on operators from R14 to R17. After its six-column
stabilization, a fixed ambient coordinate change identifies any twisted
constant frame with sixteen identity columns and the inverse radial frame.
The checked inverse-radial obstruction therefore gives parity one.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.ConstantLiftedHopfFrameTwist

open NoExoticSixSphere GLOrthonormalization Stiefel DiskBoundary
open SphereThreeTangentFrame SpanningDiskFrameCoordinates FrameBlockCoordinates

attribute [local irreducible] targetCoordinates sourceShuffle sourceSphere

theorem exists_target_coordinates {N n : ℕ} (A B : Monomorphism.Space N n) :
    ∃ U : Vector N ≃L[ℝ] Vector N, ∀ v, U (B.val v) = A.val v := by
  let eA : Vector n ≃ₗ[ℝ] A.val.range := LinearEquiv.ofInjective A.val.toLinearMap A.property
  let eB : Vector n ≃ₗ[ℝ] B.val.range := LinearEquiv.ofInjective B.val.toLinearMap B.property
  obtain ⟨U, hU⟩ := Submodule.exists_linearEquiv_restrict_eq (eB.symm.trans eA)
  refine ⟨U.toContinuousLinearEquiv, ?_⟩
  intro v
  have h := hU (eB v)
  rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at h
  exact h.symm

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

def standardFixedFrame : Monomorphism.Space 23 20 :=
  Monomorphism.frontBlockMap 16 fixedFourInclusion

def actualFixedFrame (F : Monomorphism.Space 17 14) : Monomorphism.Space 23 20 :=
  Monomorphism.recoordinate (targetCoordinates 17) (sourceShuffle 11)
    (Monomorphism.blockMap 6 F)

theorem actualFixedFrame_apply (F : Monomorphism.Space 17 14) (v : Vector 20) :
    (actualFixedFrame F).val v =
      targetCoordinates 17 (BlockSum.operator 6 F.val (sourceShuffle 11 v)) := rfl

theorem twisted_constant_apply (F : Monomorphism.Space 17 14) (s : Sphere 3) (v : Vector 20) :
    (twistedBlockMap (k := 11) (ContinuousMap.const _ F) s).val v =
      (actualFixedFrame F).val ((sourceSphere 11 s).symm v) := by
  rw [twistedBlockMap_value, actualFixedFrame_apply]
  rfl

theorem standardFixedFrame_apply (v : Vector 20) :
    standardFixedFrame.val v = EuclideanSpace.finAddEquivProd.symm
      ((EuclideanSpace.finAddEquivProd (n := 16) (m := 4) v).1,
        EuclideanSpace.finAddEquivProd.symm
          ((EuclideanSpace.finAddEquivProd (n := 16) (m := 4) v).2, (0 : Vector 3))) := rfl

theorem standardFixedFrame_sourceSphere (s : Sphere 3) (v : Vector 20) :
    standardFixedFrame.val ((sourceSphere 11 s).symm v) =
      (Monomorphism.frontBlockMap 16 (liftedInverseRadialMap s)).val v := by
  rw [sourceSphere_symm_apply, standardFixedFrame_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  change _ = EuclideanSpace.finAddEquivProd.symm
    ((EuclideanSpace.finAddEquivProd (n := 16) (m := 4) v).1,
      liftedInverseRadialOperator s
        (EuclideanSpace.finAddEquivProd (n := 16) (m := 4) v).2)
  rw [liftedInverseRadialOperator_apply]

theorem twisted_constant_not_extends (F : Monomorphism.Space 17 14) :
    ¬ Extends (twistedBlockMap (k := 11) (ContinuousMap.const _ F)) := by
  obtain ⟨U, hU⟩ := exists_target_coordinates (actualFixedFrame F) standardFixedFrame
  let G := (Monomorphism.frontBlockMap 16).comp liftedInverseRadialMap
  have he (s : Sphere 3) : twistedBlockMap (k := 11) (ContinuousMap.const _ F) s =
      Monomorphism.recoordinate U (ContinuousLinearEquiv.refl ℝ (Vector 20)) (G s) := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    rw [twisted_constant_apply, Monomorphism.recoordinate_apply]
    change (actualFixedFrame F).val ((sourceSphere 11 s).symm v) =
      U ((Monomorphism.frontBlockMap 16 (liftedInverseRadialMap s)).val v)
    rw [← standardFixedFrame_sourceSphere]
    exact (hU ((sourceSphere 11 s).symm v)).symm
  have hext : Extends (twistedBlockMap (k := 11) (ContinuousMap.const _ F)) ↔ Extends G :=
    Monomorphism.extends_recoordinate_iff (fun _ ↦ U)
      (fun _ ↦ ContinuousLinearEquiv.refl ℝ (Vector 20))
      continuous_const continuous_const continuous_const continuous_const
      G (twistedBlockMap (k := 11) (ContinuousMap.const _ F)) he
  intro h
  apply liftedInverseRadialMap_not_extends
  exact (Monomorphism.extends_frontBlockMap_iff (by decide) rfl 16
    liftedInverseRadialMap).mp (hext.mp h)

theorem twisted_constant_parity (F : Monomorphism.Space 17 14) :
    Monomorphism.sphereParityOfDimension 18 (by decide) (by decide)
      (twistedBlockMap (k := 11) (ContinuousMap.const _ F)) = 1 := by
  apply zmodTwo_eq_of_zero_iff
  apply iff_of_false _ (by decide)
  intro hz
  exact twisted_constant_not_extends F
    ((Monomorphism.sphereParityOfDimension_zero_iff 18 (by decide) (by decide) _).mp hz)

theorem twisted_parity_of_contraction (F : C(Sphere 3, Monomorphism.Space 17 14))
    (a : Monomorphism.Space 17 14) (h : F.Homotopic (ContinuousMap.const _ a)) :
    Monomorphism.sphereParityOfDimension 18 (by decide) (by decide)
      (twistedBlockMap F) = 1 :=
  (Monomorphism.sphereParityOfDimension_homotopic _ _ _
    (twistedBlockMap_homotopic h)).trans (twisted_constant_parity a)

end Wikipedia.HopfProblem.DegreeCollapse.ConstantLiftedHopfFrameTwist
