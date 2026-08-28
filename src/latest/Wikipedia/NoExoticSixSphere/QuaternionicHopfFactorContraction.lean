import Wikipedia.NoExoticSixSphere.QuaternionicHopfFactorRawFrames
import Wikipedia.NoExoticSixSphere.QuaternionicHopfBalancedFrameComparison

/-!
# Contracting the actual untwisted Hopf factor frames

The balanced quaternionic contraction is placed in either original ambient
factor and transported by the retained ambient isometry. It acts on the
actual reference frame, so every intermediate combined operator remains
injective. The original normal coordinates and tangent scaling are retained.
-/

noncomputable section

open Function unitInterval
open scoped Quaternion

namespace NoExoticSixSphere.QuaternionicHopf

open SphereThreeTangentFrame Stiefel SpanningDiskFrameCoordinates DiskBoundary

def southPairAmbientOperator (B C : V 8 →L[ℝ] V 8) : V 16 →L[ℝ] V 16 :=
  southPairAmbientEuclideanCoordinates.toContinuousLinearMap.comp
    ((HilbertProduct.map B C).comp southPairAmbientEuclideanCoordinates.symm.toContinuousLinearMap)

theorem southPairAmbientOperator_on_coordinates (B C : V 8 →L[ℝ] V 8)
    (v : SouthPairAmbientModel) :
    southPairAmbientOperator B C (southPairAmbientEuclideanCoordinates v) =
      southPairAmbientEuclideanCoordinates (HilbertProduct.map B C v) := by
  change southPairAmbientEuclideanCoordinates (HilbertProduct.map B C
    (southPairAmbientEuclideanCoordinates.symm (southPairAmbientEuclideanCoordinates v))) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

theorem southPairAmbientOperator_id (v : V 16) :
    southPairAmbientOperator (ContinuousLinearMap.id ℝ (V 8))
      (ContinuousLinearMap.id ℝ (V 8)) v = v := by
  have h := southPairAmbientOperator_on_coordinates (ContinuousLinearMap.id ℝ (V 8))
    (ContinuousLinearMap.id ℝ (V 8)) (southPairAmbientEuclideanCoordinates.symm v)
  have he : HilbertProduct.map (ContinuousLinearMap.id ℝ (V 8))
      (ContinuousLinearMap.id ℝ (V 8)) (southPairAmbientEuclideanCoordinates.symm v) =
        southPairAmbientEuclideanCoordinates.symm v := rfl
  rw [he, LinearIsometryEquiv.apply_symm_apply] at h
  exact h

theorem southPairAmbientOperator_injective (B C : V 8 →L[ℝ] V 8)
    (hB : Injective B) (hC : Injective C) : Injective (southPairAmbientOperator B C) := by
  intro v w h
  apply southPairAmbientEuclideanCoordinates.symm.injective
  have he := southPairAmbientEuclideanCoordinates.injective h
  change HilbertProduct.map B C (southPairAmbientEuclideanCoordinates.symm v) =
    HilbertProduct.map B C (southPairAmbientEuclideanCoordinates.symm w) at he
  rw [HilbertProduct.map_apply, HilbertProduct.map_apply] at he
  apply WithLp.ofLp_injective 2
  exact Prod.ext (hB (congrArg (fun z : SouthPairAmbientModel ↦ z.fst) he))
    (hC (congrArg (fun z : SouthPairAmbientModel ↦ z.snd) he))

theorem continuous_southPairAmbientOperator {X : Type*} [TopologicalSpace X]
    (B C : X → V 8 →L[ℝ] V 8) (hB : Continuous B) (hC : Continuous C) :
    Continuous (fun x ↦ southPairAmbientOperator (B x) (C x)) := by
  apply continuous_clm_apply.mpr
  intro v
  change Continuous (fun x ↦ southPairAmbientEuclideanCoordinates
    (HilbertProduct.map (B x) (C x) (southPairAmbientEuclideanCoordinates.symm v)))
  simp only [HilbertProduct.map_apply]
  exact southPairAmbientEuclideanCoordinates.continuous.comp
    ((WithLp.prod_continuous_toLp 2 (V 8) (V 8)).comp
      ((hB.clm_apply continuous_const).prodMk (hC.clm_apply continuous_const)))

theorem southPairBalanced_normal_left (s : Sphere 3) (v : SouthPairNormalModel) :
    HilbertProduct.map (balancedFrameContraction (0, s)) (ContinuousLinearMap.id ℝ (V 8))
      (southPairNormalFrame.ambient (southFrameReference, spherePole 3) v) =
        southPairNormalFrame.ambient (s, spherePole 3) v := by
  simp only [southPairNormalFrame_ambient, HilbertProduct.map_apply]
  change WithLp.toLp 2
    (balancedFrameContraction (0, s) (southNormalFrame.ambient southFrameReference v.fst),
      southNormalFrame.ambient (spherePole 3) v.snd) = _
  rw [balancedFrameContraction_normal]

theorem southPairBalanced_normal_right (s : Sphere 3) (v : SouthPairNormalModel) :
    HilbertProduct.map (ContinuousLinearMap.id ℝ (V 8)) (balancedFrameContraction (0, s))
      (southPairNormalFrame.ambient (spherePole 3, southFrameReference) v) =
        southPairNormalFrame.ambient (spherePole 3, s) v := by
  simp only [southPairNormalFrame_ambient, HilbertProduct.map_apply]
  change WithLp.toLp 2 (southNormalFrame.ambient (spherePole 3) v.fst,
    balancedFrameContraction (0, s) (southNormalFrame.ambient southFrameReference v.snd)) = _
  rw [balancedFrameContraction_normal]

theorem southPairBalanced_tangent_left (s : Sphere 3) (v : V 3) :
    HilbertProduct.map (balancedFrameContraction (0, s)) (ContinuousLinearMap.id ℝ (V 8))
      ((2 : ℝ) • WithLp.toLp 2
        (southAxis (operator southFrameReference.val v), (0 : V 8))) =
      (2 : ℝ) • WithLp.toLp 2 (southAxis (operator s.val v), (0 : V 8)) := by
  rw [map_smul, HilbertProduct.map_apply]
  change (2 : ℝ) • WithLp.toLp 2
    (balancedFrameContraction (0, s) (southAxis (operator southFrameReference.val v)), 0) = _
  rw [balancedFrameContraction_tangent]

theorem southPairBalanced_tangent_right (s : Sphere 3) (v : V 3) :
    HilbertProduct.map (ContinuousLinearMap.id ℝ (V 8)) (balancedFrameContraction (0, s))
      ((2 : ℝ) • WithLp.toLp 2
        ((0 : V 8), southAxis (operator southFrameReference.val v))) =
      (2 : ℝ) • WithLp.toLp 2 ((0 : V 8), southAxis (operator s.val v)) := by
  rw [map_smul, HilbertProduct.map_apply]
  change (2 : ℝ) • WithLp.toLp 2
    (0, balancedFrameContraction (0, s) (southAxis (operator southFrameReference.val v))) = _
  rw [balancedFrameContraction_tangent]

theorem southPairBalanced_leftFrame (s : Sphere 3) (v : V 13) :
    southPairAmbientOperator (balancedFrameContraction (0, s)) (ContinuousLinearMap.id ℝ (V 8))
      ((southPairLeftRawFrameMap southFrameReference).val v) =
        (southPairLeftRawFrameMap s).val v := by
  rw [southPairLeftRawFrameMap_apply southFrameReference v,
    southPairAmbientOperator_on_coordinates, map_add,
    southPairBalanced_normal_left, southPairBalanced_tangent_left]
  exact (southPairLeftRawFrameMap_apply s v).symm

theorem southPairBalanced_rightFrame (s : Sphere 3) (v : V 13) :
    southPairAmbientOperator (ContinuousLinearMap.id ℝ (V 8)) (balancedFrameContraction (0, s))
      ((southPairRightRawFrameMap southFrameReference).val v) =
        (southPairRightRawFrameMap s).val v := by
  rw [southPairRightRawFrameMap_apply southFrameReference v,
    southPairAmbientOperator_on_coordinates, map_add,
    southPairBalanced_normal_right, southPairBalanced_tangent_right]
  exact (southPairRightRawFrameMap_apply s v).symm

theorem southPairBalanced_one_left (s : Sphere 3) (v : V 16) :
    southPairAmbientOperator (balancedFrameContraction (1, s))
      (ContinuousLinearMap.id ℝ (V 8)) v = v := by
  have h : balancedFrameContraction (1, s) = ContinuousLinearMap.id ℝ (V 8) :=
    ContinuousLinearMap.ext (balancedFrameContraction_one s)
  rw [h]
  exact southPairAmbientOperator_id v

theorem southPairBalanced_one_right (s : Sphere 3) (v : V 16) :
    southPairAmbientOperator (ContinuousLinearMap.id ℝ (V 8))
      (balancedFrameContraction (1, s)) v = v := by
  have h : balancedFrameContraction (1, s) = ContinuousLinearMap.id ℝ (V 8) :=
    ContinuousLinearMap.ext (balancedFrameContraction_one s)
  rw [h]
  exact southPairAmbientOperator_id v

def southPairLeftRawFrameContraction : southPairLeftRawFrameMap.Homotopy
    (ContinuousMap.const _ (southPairLeftRawFrameMap southFrameReference)) where
  toFun p := ⟨(southPairAmbientOperator (balancedFrameContraction p)
    (ContinuousLinearMap.id ℝ (V 8))).comp (southPairLeftRawFrameMap southFrameReference).val,
      (southPairAmbientOperator_injective _ _ (balancedFrameContraction_injective p)
        Function.injective_id).comp (southPairLeftRawFrameMap southFrameReference).property⟩
  continuous_toFun := by
    have h := continuous_southPairAmbientOperator balancedFrameContraction
      (fun _ ↦ ContinuousLinearMap.id ℝ (V 8)) continuous_balancedFrameContraction continuous_const
    exact (h.clm_comp continuous_const).subtype_mk _
  map_zero_left s := Subtype.ext (ContinuousLinearMap.ext (southPairBalanced_leftFrame s))
  map_one_left s := Subtype.ext (ContinuousLinearMap.ext (fun v ↦
    southPairBalanced_one_left s ((southPairLeftRawFrameMap southFrameReference).val v)))

def southPairRightRawFrameContraction : southPairRightRawFrameMap.Homotopy
    (ContinuousMap.const _ (southPairRightRawFrameMap southFrameReference)) where
  toFun p := ⟨(southPairAmbientOperator (ContinuousLinearMap.id ℝ (V 8))
    (balancedFrameContraction p)).comp (southPairRightRawFrameMap southFrameReference).val,
      (southPairAmbientOperator_injective _ _ Function.injective_id
        (balancedFrameContraction_injective p)).comp
          (southPairRightRawFrameMap southFrameReference).property⟩
  continuous_toFun := ((continuous_southPairAmbientOperator
    (fun _ ↦ ContinuousLinearMap.id ℝ (V 8)) balancedFrameContraction
      continuous_const continuous_balancedFrameContraction).clm_comp continuous_const).subtype_mk _
  map_zero_left s := Subtype.ext (ContinuousLinearMap.ext (southPairBalanced_rightFrame s))
  map_one_left s := Subtype.ext (ContinuousLinearMap.ext (fun v ↦
    southPairBalanced_one_right s ((southPairRightRawFrameMap southFrameReference).val v)))

theorem southPairLeftRawFrame_twisted_constant :
    (twistedBlockMap (k := 10) southPairLeftRawFrameMap).Homotopic
      (twistedBlockMap (k := 10)
        (ContinuousMap.const _ (southPairLeftRawFrameMap southFrameReference))) :=
  twistedBlockMap_homotopic ⟨southPairLeftRawFrameContraction⟩

theorem southPairRightRawFrame_twisted_constant :
    (twistedBlockMap (k := 10) southPairRightRawFrameMap).Homotopic
      (twistedBlockMap (k := 10)
        (ContinuousMap.const _ (southPairRightRawFrameMap southFrameReference))) :=
  twistedBlockMap_homotopic ⟨southPairRightRawFrameContraction⟩

end NoExoticSixSphere.QuaternionicHopf
