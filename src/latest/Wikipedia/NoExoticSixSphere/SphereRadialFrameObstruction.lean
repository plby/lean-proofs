import Wikipedia.NoExoticSixSphere.SphereThreeRadialFrame
import Wikipedia.NoExoticSixSphere.PartialFrameFiberParity
import Wikipedia.NoExoticSixSphere.InjectiveOperatorBlockExtension

/-!
# The stabilized radial quaternion frame has a nonzero disk obstruction

Move its three tangent columns into three extra ambient axes, keeping the
radial column fixed. The resulting injective homotopy ends at the genuine
one-column sphere fiber with three identity columns. Its nonzero obstruction
is supplied by the checked fiber-parity theorem, not assigned by definition.
-/

noncomputable section

open Function unitInterval

namespace NoExoticSixSphere.SphereThreeTangentFrame

open GLOrthonormalization Stiefel DiskBoundary

def scalarUnit : UnitSphere (Vector 1) :=
  ⟨EuclideanTailCoordinates.scalar 1, by
    rw [mem_sphere_zero_iff_norm, EuclideanTailCoordinates.scalar.norm_map, norm_one]⟩

theorem inner_scalarUnit (v : Vector 1) :
    inner ℝ scalarUnit.val v = EuclideanTailCoordinates.scalar.symm v := by
  have h := EuclideanTailCoordinates.scalar.inner_map_map 1
    (EuclideanTailCoordinates.scalar.symm v)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  change inner ℝ scalarUnit.val v = EuclideanTailCoordinates.scalar.symm v * 1 at h
  simpa only [mul_one] using h

def radialSphereEquiv : Sphere 3 ≃ₜ Stiefel.Space 4 1 :=
  (OneColumn.homeomorph scalarUnit).symm

theorem radialSphereEquiv_value (s : Sphere 3) : (radialSphereEquiv s).val = radialOperator s := by
  apply ContinuousLinearMap.ext
  intro v
  change inner ℝ scalarUnit.val v • s.val = radialOperator s v
  rw [inner_scalarUnit, radialOperator_apply]

theorem radialSphere_blockOne_parity :
    sphereThirdObstruction 0
      ((BlockSum.map 1).comp (radialSphereEquiv : C(Sphere 3, Stiefel.Space 4 1))) = 1 := by
  have he : (BlockSum.map 1).comp (radialSphereEquiv : C(Sphere 3, Stiefel.Space 4 1)) =
      (SplitReconstruction.map (EuclideanTailCoordinates.split 1)
        (EuclideanTailCoordinates.split 4)).comp (radialSphereEquiv : C(_, _)) := by
    apply ContinuousMap.ext
    intro s
    exact BlockSum.frame_one_eq_split (radialSphereEquiv s)
  rw [he]
  exact SplitReconstruction.oneColumn_sphere_parity _ _ radialSphereEquiv

theorem radialSphere_blockThree_parity :
    sphereThirdObstruction 2
      ((BlockSum.map 3).comp (radialSphereEquiv : C(Sphere 3, Stiefel.Space 4 1))) = 1 := by
  rw [BlockSum.map_succ_comp 2, BlockSum.sphere_parity_one 1,
    BlockSum.map_succ_comp 1, BlockSum.sphere_parity_one 0]
  exact radialSphere_blockOne_parity

def liftedRadialOperator (s : Sphere 3) : Vector 4 →L[ℝ] Vector 7 :=
  EuclideanSpace.finAddEquivProd.symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.inl ℝ (Vector 4) (Vector 3)).comp
      (radialCoordinates s).toContinuousLinearMap)

theorem liftedRadialOperator_apply (s : Sphere 3) (v : Vector 4) :
    liftedRadialOperator s v = EuclideanSpace.finAddEquivProd.symm
      (radialCoordinates s v, (0 : Vector 3)) := rfl

def liftedRadialMap : C(Sphere 3, Monomorphism.Space 7 4) where
  toFun s := ⟨liftedRadialOperator s, by
    intro v w h
    apply (radialCoordinates s).injective
    have he := congrArg (fun z : Vector 7 ↦
      (EuclideanSpace.finAddEquivProd (n := 4) (m := 3) z).1) h
    simpa only [liftedRadialOperator_apply, ContinuousLinearEquiv.apply_symm_apply] using he⟩
  continuous_toFun := by
    have h : Continuous liftedRadialOperator := by
      apply continuous_clm_apply.mpr
      intro v
      simp only [liftedRadialOperator_apply]
      exact EuclideanSpace.finAddEquivProd.symm.continuous.comp
        ((continuous_radialCoordinates.clm_apply continuous_const).prodMk continuous_const)
    exact h.subtype_mk _

def separatedRadialMap : C(Sphere 3, Monomorphism.Space 7 4) :=
  (Monomorphism.recoordinateHomeomorph (ContinuousLinearEquiv.refl ℝ (Vector 7))
    (Monomorphism.blockSwap 3 1) : C(_, _)).comp
      ((Monomorphism.inclusion 7 4).comp
        ((BlockSum.map 3).comp (radialSphereEquiv : C(_, _))))

theorem separatedRadialMap_apply (s : Sphere 3) (v : Vector 4) :
    (separatedRadialMap s).val v = EuclideanSpace.finAddEquivProd.symm
      (radialOperator s (EuclideanSpace.finAddEquivProd (n := 3) (m := 1) v).2,
        (EuclideanSpace.finAddEquivProd (n := 3) (m := 1) v).1) := by
  change BlockSum.operator 3 (radialSphereEquiv s).val (Monomorphism.blockSwap 3 1 v) = _
  rw [radialSphereEquiv_value, Monomorphism.blockSwap_apply, BlockSum.operator_apply,
    ContinuousLinearEquiv.apply_symm_apply]

theorem separatedRadialMap_not_extends : ¬ Extends separatedRadialMap := by
  let F := (Monomorphism.inclusion 7 4).comp
    ((BlockSum.map 3).comp (radialSphereEquiv : C(Sphere 3, Stiefel.Space 4 1)))
  have he : Extends separatedRadialMap ↔ Extends F :=
    Monomorphism.extends_recoordinate_iff
      (fun _ ↦ ContinuousLinearEquiv.refl ℝ (Vector 7))
      (fun _ ↦ Monomorphism.blockSwap 3 1)
      continuous_const continuous_const continuous_const continuous_const F separatedRadialMap
      (fun _ ↦ rfl)
  intro h
  have hf := (extends_inclusion_iff _).mp (he.mp h)
  have hz := (sphereThirdObstruction_zero_iff_extension 2 _).mpr hf
  rw [radialSphere_blockThree_parity] at hz
  exact one_ne_zero hz

def movingRadialOperator (p : I × Sphere 3) : Vector 4 →L[ℝ] Vector 7 :=
  EuclideanSpace.finAddEquivProd.symm.toContinuousLinearMap.comp
    (((((1 - (p.1 : ℝ)) • operator p.2.val).comp
      (ContinuousLinearMap.fst ℝ (Vector 3) (Vector 1)) +
      (radialOperator p.2).comp (ContinuousLinearMap.snd ℝ (Vector 3) (Vector 1))).prod
        ((p.1 : ℝ) • ContinuousLinearMap.fst ℝ (Vector 3) (Vector 1))).comp
          EuclideanSpace.finAddEquivProd.toContinuousLinearMap)

theorem movingRadialOperator_apply (p : I × Sphere 3) (v : Vector 4) :
    movingRadialOperator p v = EuclideanSpace.finAddEquivProd.symm
      ((1 - (p.1 : ℝ)) • operator p.2.val
        (EuclideanSpace.finAddEquivProd (n := 3) (m := 1) v).1 +
        radialOperator p.2 (EuclideanSpace.finAddEquivProd (n := 3) (m := 1) v).2,
        (p.1 : ℝ) • (EuclideanSpace.finAddEquivProd (n := 3) (m := 1) v).1) := rfl

theorem movingRadialOperator_injective (p : I × Sphere 3) :
    Injective (movingRadialOperator p) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  have he := congrArg (EuclideanSpace.finAddEquivProd (n := 4) (m := 3)) hv
  rw [movingRadialOperator_apply, ContinuousLinearEquiv.apply_symm_apply, map_zero] at he
  have ht := congrArg Prod.snd he
  have hn := congrArg Prod.fst he
  change (p.1 : ℝ) • (EuclideanSpace.finAddEquivProd (n := 3) (m := 1) v).1 = 0 at ht
  change (1 - (p.1 : ℝ)) • operator p.2.val
    (EuclideanSpace.finAddEquivProd (n := 3) (m := 1) v).1 +
      radialOperator p.2 (EuclideanSpace.finAddEquivProd (n := 3) (m := 1) v).2 = 0 at hn
  by_cases hzero : (p.1 : ℝ) = 0
  · have hr : radialCoordinates p.2 v = 0 := by
      rw [hzero, sub_zero, one_smul] at hn
      exact hn
    exact (radialCoordinates p.2).injective (hr.trans (map_zero _).symm)
  · have htan : (EuclideanSpace.finAddEquivProd (n := 3) (m := 1) v).1 = 0 :=
      (smul_eq_zero.mp ht).resolve_left hzero
    have hrad : radialOperator p.2
        (EuclideanSpace.finAddEquivProd (n := 3) (m := 1) v).2 = 0 := by
      simpa only [htan, map_zero, smul_zero, zero_add] using hn
    have hr := radialOperator_injective p.2 (hrad.trans (map_zero _).symm)
    apply (EuclideanSpace.finAddEquivProd (n := 3) (m := 1)).injective
    exact Prod.ext htan hr

theorem continuous_movingRadialOperator : Continuous movingRadialOperator := by
  apply continuous_clm_apply.mpr
  intro v
  simp only [movingRadialOperator_apply]
  have ht : Continuous (fun p : I × Sphere 3 ↦ (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have htan : Continuous (fun p : I × Sphere 3 ↦
      operator p.2.val (EuclideanSpace.finAddEquivProd (n := 3) (m := 1) v).1) :=
    ((continuous_subtype_val.comp continuous_frame).comp continuous_snd).clm_apply continuous_const
  have hrad : Continuous (fun p : I × Sphere 3 ↦
      radialOperator p.2 (EuclideanSpace.finAddEquivProd (n := 3) (m := 1) v).2) :=
    (continuous_radialOperator.comp continuous_snd).clm_apply continuous_const
  exact EuclideanSpace.finAddEquivProd.symm.continuous.comp
    ((((continuous_const.sub ht).smul htan).add hrad).prodMk (ht.smul continuous_const))

def radialSeparationHomotopy : liftedRadialMap.Homotopy separatedRadialMap where
  toFun p := ⟨movingRadialOperator p, movingRadialOperator_injective p⟩
  continuous_toFun := continuous_movingRadialOperator.subtype_mk _
  map_zero_left s := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    change movingRadialOperator (0, s) v = liftedRadialOperator s v
    rw [movingRadialOperator_apply, liftedRadialOperator_apply, radialCoordinates_apply]
    simp only [show ((0 : I) : ℝ) = 0 from rfl,
      sub_zero, one_smul, zero_smul, radialOperator_apply]
  map_one_left s := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    change movingRadialOperator (1, s) v = (separatedRadialMap s).val v
    rw [movingRadialOperator_apply, separatedRadialMap_apply]
    simp only [show ((1 : I) : ℝ) = 1 from rfl, sub_self, zero_smul, zero_add, one_smul]

theorem liftedRadialMap_not_extends : ¬ Extends liftedRadialMap := by
  intro h
  exact separatedRadialMap_not_extends ((extends_homotopic_iff ⟨radialSeparationHomotopy⟩).mp h)

end NoExoticSixSphere.SphereThreeTangentFrame
