import Wikipedia.NoExoticSixSphere.RegularFiberNormalIsometry
import Wikipedia.NoExoticSixSphere.SphereSuspensionNormalOperator
import Wikipedia.NoExoticSixSphere.PartialFrameBlockSum

/-!
# Fixed isometries for the actual suspension frame comparison

Move the appended ambient coordinate to the first position. In the normal
space, move the new height equation past the old norm equation and retain
the original ordered target coordinates. All maps are fixed isometries.
-/

noncomputable section

namespace NoExoticSixSphere.SphereMapSuspension

open GLOrthonormalization Stiefel Wikipedia.HopfProblem.DegreeCollapse

def ambientSuspensionIsometry (N : ℕ) : Vector (N + 1) ≃ₗᵢ[ℝ] Vector (N + 1) :=
  (EuclideanTailCoordinates.split N).trans (EuclideanProduct.headIsometry N)

theorem ambientSuspensionIsometry_appendZero (m : ℕ) (v : Vector (m + 1)) :
    ambientSuspensionIsometry (m + 1) (appendZeroMap (m + 1) 1 v) =
      SphereCylinder.join m (0, v) := by
  change EuclideanProduct.headIsometry (m + 1)
    (EuclideanTailCoordinates.split (m + 1) (appendZeroMap (m + 1) 1 v)) = _
  rw [EuclideanTailCoordinates.split_apply]
  change EuclideanProduct.headIsometry (m + 1) (WithLp.toLp 2
    (EuclideanTailCoordinates.scalar.symm (EuclideanSpace.finAddEquivProd
      (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 1)))).2,
      (EuclideanSpace.finAddEquivProd
        (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 1)))).1)) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  change EuclideanProduct.headIsometry (m + 1)
    (WithLp.toLp 2 (EuclideanTailCoordinates.scalar.symm 0, v)) = _
  rw [map_zero]
  rfl

theorem ambientSuspensionIsometry_block {m q : ℕ}
    (A : Vector q →L[ℝ] Vector (m + 1)) (v : Vector (q + 1)) :
    ambientSuspensionIsometry (m + 1) (BlockSum.operator 1 A v) =
      SphereCylinder.join m ((EuclideanTailCoordinates.split q v).fst,
        A (EuclideanTailCoordinates.split q v).snd) := by
  change EuclideanProduct.headIsometry (m + 1)
    (EuclideanTailCoordinates.split (m + 1) (BlockSum.operator 1 A v)) = _
  rw [EuclideanTailCoordinates.split_apply, BlockSum.operator_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  rfl

def equationSuspensionShuffle (n : ℕ) :
    WithLp 2 (ℝ × Vector (n + 1)) ≃ₗᵢ[ℝ] WithLp 2 (ℝ × WithLp 2 (ℝ × Vector n)) :=
  (LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ ℝ)
    (EuclideanProduct.headIsometry n).symm).trans
      ((LinearIsometryEquiv.withLpProdAssoc 2 ℝ ℝ ℝ (Vector n)).symm.trans
        ((LinearIsometryEquiv.withLpProdCongr 2
          (LinearIsometryEquiv.withLpProdComm 2 ℝ ℝ ℝ)
            (LinearIsometryEquiv.refl ℝ (Vector n))).trans
          (LinearIsometryEquiv.withLpProdAssoc 2 ℝ ℝ ℝ (Vector n))))

theorem equationSuspensionShuffle_apply (n : ℕ) (r s : ℝ) (z : Vector n) :
    equationSuspensionShuffle n (WithLp.toLp 2 (r, EuclideanProduct.coordinates n (s, z))) =
      WithLp.toLp 2 (s, WithLp.toLp 2 (r, z)) := rfl

def normalSuspensionIsometry {m n : ℕ} (k : ℕ) (hd : m = n + k) :
    Vector ((m + 2) - k) ≃ₗᵢ[ℝ] Vector ((m + 1 - k) + 1) :=
  (RegularSphereFiber.normalCoordinatesIsometry k (show m + 1 = n + 1 + k by omega)).trans
    ((equationSuspensionShuffle n).trans
      ((LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ ℝ)
        (RegularSphereFiber.normalCoordinatesIsometry k hd).symm).trans
          (EuclideanTailCoordinates.split (m + 1 - k)).symm))

theorem normalSuspensionIsometry_apply {m n : ℕ} (k : ℕ) (hd : m = n + k)
    (r s : ℝ) (z : Vector n) :
    normalSuspensionIsometry k hd
      ((RegularSphereFiber.normalCoordinatesIsometry k
        (show m + 1 = n + 1 + k by omega)).symm
          (WithLp.toLp 2 (r, EuclideanProduct.coordinates n (s, z)))) =
      (EuclideanTailCoordinates.split (m + 1 - k)).symm
        (WithLp.toLp 2 (s, (RegularSphereFiber.normalCoordinatesIsometry k hd).symm
          (WithLp.toLp 2 (r, z)))) := by
  simp only [normalSuspensionIsometry, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply, equationSuspensionShuffle_apply]
  rfl

theorem normalSuspension_block {m n : ℕ} (k : ℕ) (hd : m = n + k)
    (R : WithLp 2 (ℝ × Vector n) →L[ℝ] Vector (m + 1))
    (R' : WithLp 2 (ℝ × Vector (n + 1)) →L[ℝ] Vector (m + 2))
    (hR : ∀ s r z, R' (WithLp.toLp 2 (r, EuclideanProduct.coordinates n (s, z))) =
      SphereCylinder.join m (s, R (WithLp.toLp 2 (r, z))))
    (v : Vector (m + 2 - k)) :
    (R'.comp (RegularSphereFiber.normalCoordinates k
      (show m + 1 = n + 1 + k by omega)).toContinuousLinearMap) v =
    ambientSuspensionIsometry (m + 1)
      (BlockSum.operator 1 (R.comp (RegularSphereFiber.normalCoordinates k hd
        ).toContinuousLinearMap) (normalSuspensionIsometry k hd v)) := by
  let N' := RegularSphereFiber.normalCoordinatesIsometry k
    (show m + 1 = n + 1 + k by omega)
  obtain ⟨w, rfl⟩ := N'.symm.surjective v
  obtain ⟨⟨s, z⟩, hp⟩ := (EuclideanProduct.coordinates n).surjective w.snd
  have hw : w = WithLp.toLp 2 (w.fst, EuclideanProduct.coordinates n (s, z)) := by
    rw [hp]
    rfl
  rw [hw]
  dsimp only [N']
  rw [ambientSuspensionIsometry_block, normalSuspensionIsometry_apply,
    LinearIsometryEquiv.apply_symm_apply]
  rw [← RegularSphereFiber.normalCoordinatesIsometry_toContinuousLinearEquiv k hd,
    ← RegularSphereFiber.normalCoordinatesIsometry_toContinuousLinearEquiv k
      (show m + 1 = n + 1 + k by omega)]
  change R' (RegularSphereFiber.normalCoordinatesIsometry k
      (show m + 1 = n + 1 + k by omega)
        ((RegularSphereFiber.normalCoordinatesIsometry k
          (show m + 1 = n + 1 + k by omega)).symm
            (WithLp.toLp 2 (w.fst, EuclideanProduct.coordinates n (s, z))))) =
    SphereCylinder.join m (s, R (RegularSphereFiber.normalCoordinatesIsometry k hd
      ((RegularSphereFiber.normalCoordinatesIsometry k hd).symm (WithLp.toLp 2 (w.fst, z)))))
  rw [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  exact hR s w.fst z

end NoExoticSixSphere.SphereMapSuspension
