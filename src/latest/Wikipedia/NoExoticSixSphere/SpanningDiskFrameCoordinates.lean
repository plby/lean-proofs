import Wikipedia.NoExoticSixSphere.SpanningDiskFramedCollar

/-!
# Fixed coordinate permutations and the sphere-dependent source framing

The source shuffle moves the three tangent columns next to the original
normal columns. The target coordinates separate the five graph axes and
the height, including its actual factor two. Only the radial source frame
depends on the sphere point; none of these maps depends on the sphere map.
-/

noncomputable section

namespace NoExoticSixSphere.SpanningDiskFrameCoordinates

open GLOrthonormalization SphereThreeTangentFrame StabilizedSpanningDisk

def sourceSphere (k : ℕ) (s : Sphere 3) : Vector ((k + 5) + 4) ≃L[ℝ] Vector ((k + 5) + 4) :=
  EuclideanSpace.finAddEquivProd.trans
    (((ContinuousLinearEquiv.refl ℝ (Vector (k + 5))).prodCongr (radialCoordinates s)).trans
      EuclideanSpace.finAddEquivProd.symm)

theorem sourceSphere_apply (k : ℕ) (s : Sphere 3) (v : Vector ((k + 5) + 4)) :
    sourceSphere k s v = EuclideanSpace.finAddEquivProd.symm
      ((EuclideanSpace.finAddEquivProd v).1, radialCoordinates s
        (EuclideanSpace.finAddEquivProd (n := k + 5) (m := 4) v).2) := rfl

theorem sourceSphere_symm_apply (k : ℕ) (s : Sphere 3) (v : Vector ((k + 5) + 4)) :
    (sourceSphere k s).symm v = EuclideanSpace.finAddEquivProd.symm
      ((EuclideanSpace.finAddEquivProd v).1, (radialCoordinates s).symm
        (EuclideanSpace.finAddEquivProd (n := k + 5) (m := 4) v).2) := by
  apply (sourceSphere k s).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, sourceSphere_apply,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
  exact (EuclideanSpace.finAddEquivProd.symm_apply_apply v).symm

theorem continuous_sourceSphere (k : ℕ) :
    Continuous (fun s ↦ (sourceSphere k s).toContinuousLinearMap) := by
  apply continuous_clm_apply.mpr
  intro v
  change Continuous (fun s ↦ sourceSphere k s v)
  simp_rw [sourceSphere_apply]
  exact EuclideanSpace.finAddEquivProd.symm.continuous.comp
    (continuous_const.prodMk (continuous_radialCoordinates.clm_apply continuous_const))

theorem continuous_inverse_sourceSphere (k : ℕ) :
    Continuous (fun s ↦ (sourceSphere k s).symm.toContinuousLinearMap) := by
  apply continuous_clm_apply.mpr
  intro v
  change Continuous (fun s ↦ (sourceSphere k s).symm v)
  simp_rw [sourceSphere_symm_apply]
  exact EuclideanSpace.finAddEquivProd.symm.continuous.comp
    (continuous_const.prodMk (continuous_inverse_radialCoordinates.clm_apply continuous_const))

def sourceShuffle (k : ℕ) : Vector ((k + 5) + 4) ≃L[ℝ] Vector ((k + 3) + 6) :=
  EuclideanSpace.finAddEquivProd.trans
    ((EuclideanSpace.finAddEquivProd.prodCongr
      (EuclideanSpace.finAddEquivProd (n := 3) (m := 1))).trans
        ((ContinuousLinearEquiv.prodProdProdComm ℝ (Vector k) (Vector 5)
          (Vector 3) (Vector 1)).trans
            ((EuclideanSpace.finAddEquivProd.symm.prodCongr
              (EuclideanSpace.finAddEquivProd (n := 5) (m := 1)).symm).trans
                EuclideanSpace.finAddEquivProd.symm)))

theorem sourceShuffle_apply (k : ℕ) (v : Vector ((k + 5) + 4)) :
    sourceShuffle k v = EuclideanSpace.finAddEquivProd.symm
      (EuclideanSpace.finAddEquivProd.symm
        ((EuclideanSpace.finAddEquivProd (n := k) (m := 5)
          (EuclideanSpace.finAddEquivProd v).1).1,
          (EuclideanSpace.finAddEquivProd (n := 3) (m := 1)
            (EuclideanSpace.finAddEquivProd (n := k + 5) (m := 4) v).2).1),
        EuclideanSpace.finAddEquivProd.symm
          ((EuclideanSpace.finAddEquivProd (n := k) (m := 5)
            (EuclideanSpace.finAddEquivProd v).1).2,
            (EuclideanSpace.finAddEquivProd (n := 3) (m := 1)
              (EuclideanSpace.finAddEquivProd (n := k + 5) (m := 4) v).2).2)) := rfl

def doubleScalar : ℝ ≃L[ℝ] ℝ :=
  (LinearEquiv.smulOfNeZero ℝ ℝ 2 (by norm_num)).toContinuousLinearEquiv

theorem doubleScalar_apply (x : ℝ) : doubleScalar x = 2 * x := rfl

def targetExtra : Vector 6 ≃L[ℝ] ℝ × (ℝ × Vector 4) :=
  (EuclideanSpace.finAddEquivProd (n := 5) (m := 1)).trans
    ((ContinuousLinearEquiv.prodComm ℝ (Vector 5) (Vector 1)).trans
      ((EuclideanTailCoordinates.scalar.symm.toContinuousLinearEquiv.trans doubleScalar).prodCongr
        (DiskGraph.extraCoordinates 4).symm))

theorem targetExtra_apply (v : Vector 6) : targetExtra v =
    (2 * EuclideanTailCoordinates.scalar.symm
      (EuclideanSpace.finAddEquivProd (n := 5) (m := 1) v).2,
      (DiskGraph.extraCoordinates 4).symm
        (EuclideanSpace.finAddEquivProd (n := 5) (m := 1) v).1) := rfl

def targetCoordinates (N : ℕ) : Vector (N + 6) ≃L[ℝ] Vector (N + 6) :=
  EuclideanSpace.finAddEquivProd.trans
    (((ContinuousLinearEquiv.refl ℝ (Vector N)).prodCongr targetExtra).trans
      ((ContinuousLinearEquiv.prodAssoc ℝ (Vector N) ℝ (ℝ × Vector 4)).symm.trans
        (coordinates N 4)))

theorem targetCoordinates_apply (N : ℕ) (v : Vector (N + 6)) :
    targetCoordinates N v = coordinates N 4
      (((EuclideanSpace.finAddEquivProd (n := N) (m := 6) v).1,
        (targetExtra (EuclideanSpace.finAddEquivProd (n := N) (m := 6) v).2).1),
        (targetExtra (EuclideanSpace.finAddEquivProd (n := N) (m := 6) v).2).2) := rfl

def sourceTwist (k : ℕ) (s : Sphere 3) :
    Vector ((k + 5) + 4) ≃L[ℝ] Vector ((k + 3) + 6) :=
  (sourceSphere k s).symm.trans (sourceShuffle k)

theorem sourceTwist_apply (k : ℕ) (s : Sphere 3) (v : Vector ((k + 5) + 4)) :
    sourceTwist k s v = sourceShuffle k ((sourceSphere k s).symm v) := rfl

theorem continuous_sourceTwist (k : ℕ) :
    Continuous (fun s ↦ (sourceTwist k s).toContinuousLinearMap) := by
  change Continuous (fun s ↦ (sourceShuffle k).toContinuousLinearMap.comp
    (sourceSphere k s).symm.toContinuousLinearMap)
  exact (continuous_const : Continuous (fun _ : Sphere 3 ↦
    (sourceShuffle k).toContinuousLinearMap)).clm_comp (continuous_inverse_sourceSphere k)

end NoExoticSixSphere.SpanningDiskFrameCoordinates
