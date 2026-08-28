import Wikipedia.NoExoticSixSphere.CircleCylinderSpatialCoordinates
import Wikipedia.NoExoticSixSphere.OrthogonalFramePrepend
import Wikipedia.NoExoticSixSphere.OrthogonalFrameAppendStabilization

/-!
# The signed two-axis stabilization of the ordered circle boundary columns

The leading radial column moves after the original endpoint columns.
Its pole sign is retained, and the final time column has the outward
negative sign. All ambient and source changes below are genuine isometries.
-/

noncomputable section

namespace NoExoticSixSphere.CircleCylinder

open GLOrthonormalization Stiefel Wikipedia.HopfProblem.DegreeCollapse

def circleAxisCoordinates (left : Bool) : WithLp 2 (ℝ × ℝ) ≃ₗᵢ[ℝ] V :=
  (LinearIsometryEquiv.withLpProdCongr 2
    (if left then LinearIsometryEquiv.refl ℝ ℝ else LinearIsometryEquiv.neg ℝ)
    ((LinearIsometryEquiv.neg ℝ).trans EuclideanTailCoordinates.scalar)).trans
      (EuclideanProduct.headIsometry 1)

theorem circleAxisCoordinates_apply (left : Bool) (r t : ℝ) :
    circleAxisCoordinates left (WithLp.toLp 2 (r, t)) =
      r • (SphereCylinder.endPole 0 left).val + t • (-circleTimeUnit) := by
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · cases left
    · change -r = r * (-1) + t * (-0)
      ring
    · change r = r * 1 + t * (-0)
      ring
  · change -t = r * 0 + t * (-1)
    ring

def stabilizationAmbient (m : ℕ) : Vector ((m + 1) + 2) ≃ₗᵢ[ℝ] Vector (2 + (m + 1)) :=
  ((EuclideanTailCoordinates.finAdd (m + 1) 2).trans
    (LinearIsometryEquiv.withLpProdComm 2 ℝ (Vector (m + 1)) V)).trans (ambientCoordinates m)

theorem stabilizationAmbient_apply (m : ℕ) (v : Vector (m + 1)) (c : V) :
    stabilizationAmbient m (EuclideanSpace.finAddEquivProd.symm (v, c)) =
      ambientCoordinates m (WithLp.toLp 2 (c, v)) := by
  change ambientCoordinates m (WithLp.toLp 2
    ((EuclideanSpace.finAddEquivProd (EuclideanSpace.finAddEquivProd.symm (v, c))).2,
      (EuclideanSpace.finAddEquivProd (EuclideanSpace.finAddEquivProd.symm (v, c))).1)) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]

def boundaryColumnCoordinates (q : ℕ) (left : Bool) :
    Vector ((q + 1) + 1) ≃L[ℝ] Vector (q + 2) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := q + 1) (m := 1)).trans
    (((EuclideanProduct.coordinates q).symm.prodCongr
      EuclideanTailCoordinates.scalar.symm.toContinuousLinearEquiv).trans
        ((ContinuousLinearEquiv.prodAssoc ℝ ℝ (Vector q) ℝ).trans
          (((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
            (ContinuousLinearEquiv.prodComm ℝ (Vector q) ℝ)).trans
              ((ContinuousLinearEquiv.prodAssoc ℝ ℝ ℝ (Vector q)).symm.trans
                ((ContinuousLinearEquiv.prodComm ℝ (ℝ × ℝ) (Vector q)).trans
                  (((ContinuousLinearEquiv.refl ℝ (Vector q)).prodCongr
                    ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm.trans
                      (circleAxisCoordinates left).toContinuousLinearEquiv)).trans
                        EuclideanSpace.finAddEquivProd.symm))))))

theorem boundaryColumnCoordinates_split (q : ℕ) (left : Bool) (v : Vector ((q + 1) + 1)) :
    EuclideanSpace.finAddEquivProd (boundaryColumnCoordinates q left v) =
      (WithLp.toLp 2 (fun i : Fin q ↦ (EuclideanSpace.finAddEquivProd v).1 i.succ),
        circleAxisCoordinates left (WithLp.toLp 2
          ((EuclideanSpace.finAddEquivProd v).1 0,
            EuclideanTailCoordinates.scalar.symm (EuclideanSpace.finAddEquivProd v).2))) := by
  change EuclideanSpace.finAddEquivProd (EuclideanSpace.finAddEquivProd.symm _) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl

theorem inner_boundaryColumnCoordinates (q : ℕ) (left : Bool)
    (u v : Vector ((q + 1) + 1)) :
    inner ℝ (boundaryColumnCoordinates q left u) (boundaryColumnCoordinates q left v) =
      inner ℝ u v := by
  rw [inner_finAdd_split, boundaryColumnCoordinates_split, boundaryColumnCoordinates_split,
    (circleAxisCoordinates left).inner_map_map, WithLp.prod_inner_apply]
  have hh := (EuclideanProduct.headIsometry q).symm.inner_map_map
    (EuclideanSpace.finAddEquivProd u).1 (EuclideanSpace.finAddEquivProd v).1
  have ht := EuclideanTailCoordinates.scalar.symm.inner_map_map
    (EuclideanSpace.finAddEquivProd u).2 (EuclideanSpace.finAddEquivProd v).2
  change inner ℝ ((EuclideanSpace.finAddEquivProd u).1 0)
      ((EuclideanSpace.finAddEquivProd v).1 0) +
    inner ℝ (WithLp.toLp 2 (fun i : Fin q ↦ (EuclideanSpace.finAddEquivProd u).1 i.succ))
      (WithLp.toLp 2 (fun i : Fin q ↦ (EuclideanSpace.finAddEquivProd v).1 i.succ)) = _ at hh
  rw [inner_finAdd_split u v, ← hh, ← ht]
  ring

def boundaryColumnIsometry (q : ℕ) (left : Bool) :
    Vector ((q + 1) + 1) ≃ₗᵢ[ℝ] Vector (q + 2) where
  toLinearEquiv := (boundaryColumnCoordinates q left).toLinearEquiv
  norm_map' v := by
    change ‖boundaryColumnCoordinates q left v‖ = ‖v‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simpa only [real_inner_self_eq_norm_sq] using inner_boundaryColumnCoordinates q left v v

theorem append_prepend_eq_twoAxisBlock {m q : ℕ} (left : Bool)
    (A : Vector q →L[ℝ] Vector (m + 1)) :
    OrthogonalFrameAppend.operator
      (OrthogonalFramePrepend.operator (radialUnit m left)
        ((spatialIsometry m).toContinuousLinearMap.comp A)) (-timeUnit m) =
      ((stabilizationAmbient m).toContinuousLinearMap.comp (BlockSum.operator 2 A)).comp
        (boundaryColumnIsometry q left).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro v
  change OrthogonalFrameAppend.operator _ (-timeUnit m) v =
    stabilizationAmbient m (BlockSum.operator 2 A (boundaryColumnCoordinates q left v))
  rw [OrthogonalFrameAppend.operator_apply, OrthogonalFramePrepend.operator_apply,
    BlockSum.operator_apply, boundaryColumnCoordinates_split, stabilizationAmbient_apply,
    circleAxisCoordinates_apply]
  change _ • ambientCoordinates m (WithLp.toLp 2
      ((SphereCylinder.endPole 0 left).val, (0 : Vector (m + 1)))) +
    ambientCoordinates m (WithLp.toLp 2 ((0 : V), _)) +
    _ • (-ambientCoordinates m (WithLp.toLp 2 (circleTimeUnit, (0 : Vector (m + 1))))) = _
  rw [← map_neg, ← map_smul, ← map_smul, ← map_add, ← map_add]
  congr 1
  apply WithLp.ofLp_injective
  simp

end NoExoticSixSphere.CircleCylinder
