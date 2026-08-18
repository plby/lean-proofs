/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.GraphWindowAffine
import ErdosProblems.Erdos186.PZ.ConvexDensity.RetainedFibers

/-!
# Volume normalization of the graph-window chart

Rather than expanding a determinant in coordinates, we evaluate the affine
Jacobian on one reference box.  The physical box has volume
`(2*q)^n * outer` and its graph-window image has volume one.  This exact
identity is the cancellation needed when a normalized graph slab is compared
with the original normalized convex body.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace Erdos186.PZ.ConvexDensity

set_option autoImplicit false
noncomputable section

def graphWindowReferenceProduct (n : ℕ) (q outer : ℝ) :
    Set (EuclideanPoint n × ℝ) :=
  affineGraphSlab
    (closedAxisBox (fun _ : Fin n ↦ -q) (fun _ : Fin n ↦ q))
    (AffineMap.const ℝ (EuclideanPoint n) 0) (outer / 2)

def graphWindowUnitProduct (n : ℕ) : Set (EuclideanPoint n × ℝ) :=
  affineGraphSlab
    (closedAxisBox (fun _ : Fin n ↦ 0) (fun _ : Fin n ↦ 1))
    (AffineMap.const ℝ (EuclideanPoint n) 0) (1 / 2)

def graphWindowReferenceBox (n : ℕ) (q outer : ℝ) :
    Set (EuclideanPoint (n + 1)) :=
  (lastCoordinateCLE n).symm '' graphWindowReferenceProduct n q outer

def graphWindowUnitBox (n : ℕ) : Set (EuclideanPoint (n + 1)) :=
  (lastCoordinateCLE n).symm '' graphWindowUnitProduct n

theorem mem_graphWindowReferenceBox_iff {n : ℕ} {q outer : ℝ}
    {z : EuclideanPoint (n + 1)} :
    z ∈ graphWindowReferenceBox n q outer ↔
      (∀ i, -q ≤ coordinate (baseCoordinates z) i ∧
        coordinate (baseCoordinates z) i ≤ q) ∧
      -(outer / 2) ≤ lastCoordinate z ∧ lastCoordinate z ≤ outer / 2 := by
  rw [graphWindowReferenceBox]
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hp' := hp
    simp only [graphWindowReferenceProduct, affineGraphSlab,
      AffineMap.const_apply, sub_zero, zero_add, mem_setOf_eq] at hp'
    simpa [baseCoordinates_lastCoordinateCLE_symm,
      lastCoordinate_lastCoordinateCLE_symm] using hp'
  · intro hz
    refine ⟨lastCoordinateCLE n z, ?_, (lastCoordinateCLE n).symm_apply_apply z⟩
    simpa [graphWindowReferenceProduct, affineGraphSlab,
      baseCoordinates_lastCoordinateCLE_symm,
      lastCoordinate_lastCoordinateCLE_symm] using hz

theorem mem_graphWindowUnitBox_iff {n : ℕ}
    {z : EuclideanPoint (n + 1)} :
    z ∈ graphWindowUnitBox n ↔
      (∀ i, 0 ≤ coordinate (baseCoordinates z) i ∧
        coordinate (baseCoordinates z) i ≤ 1) ∧
      -(1 / 2 : ℝ) ≤ lastCoordinate z ∧
        lastCoordinate z ≤ (1 / 2 : ℝ) := by
  rw [graphWindowUnitBox]
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hp' := hp
    simp only [graphWindowUnitProduct, affineGraphSlab,
      AffineMap.const_apply, sub_zero, zero_add, mem_setOf_eq] at hp'
    simpa [baseCoordinates_lastCoordinateCLE_symm,
      lastCoordinate_lastCoordinateCLE_symm] using hp'
  · intro hz
    refine ⟨lastCoordinateCLE n z, ?_, (lastCoordinateCLE n).symm_apply_apply z⟩
    simpa [graphWindowUnitProduct, affineGraphSlab,
      baseCoordinates_lastCoordinateCLE_symm,
      lastCoordinate_lastCoordinateCLE_symm] using hz

/-- The reference box maps exactly to the unit-volume box. -/
theorem graphWindowAffineEquiv_image_referenceBox {n : ℕ} {q outer : ℝ}
    (hq : 0 < q) (houter : 0 < outer) :
    graphWindowAffineEquiv q outer hq.ne' houter.ne' ''
        graphWindowReferenceBox n q outer =
      graphWindowUnitBox n := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [mem_graphWindowUnitBox_iff]
    have hz' := mem_graphWindowReferenceBox_iff.mp hz
    rw [graphWindowAffineEquiv_apply hq.ne' houter.ne',
      baseCoordinates_normalizeGraphPoint,
      lastCoordinate_normalizeGraphPoint]
    constructor
    · intro i
      have hi := hz'.1 i
      have hden : 0 < 2 * q := by positivity
      constructor
      · exact div_nonneg (by linarith) hden.le
      · exact (div_le_one hden).2 (by linarith)
    · constructor
      · rw [le_div_iff₀ houter]
        linarith [hz'.2.1]
      · rw [div_le_iff₀ houter]
        linarith [hz'.2.2]
  · intro hy
    have hy' := mem_graphWindowUnitBox_iff.mp hy
    let half : EuclideanPoint n :=
      WithLp.toLp 2 (fun _ : Fin n ↦ (1 / 2 : ℝ))
    let z : EuclideanPoint (n + 1) :=
      appendCoordinate ((2 * q) • (baseCoordinates y - half))
        (outer * lastCoordinate y)
    have hz : z ∈ graphWindowReferenceBox n q outer := by
      rw [mem_graphWindowReferenceBox_iff]
      constructor
      · intro i
        have hi := hy'.1 i
        dsimp only [z, half]
        simp only [baseCoordinates_appendCoordinate, coordinate,
          WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, WithLp.ofLp_sub,
          Pi.sub_apply, WithLp.ofLp_toLp]
        constructor <;> nlinarith
      · dsimp only [z]
        rw [lastCoordinate_appendCoordinate]
        constructor <;> nlinarith [hy'.2.1, hy'.2.2]
    refine ⟨z, hz, ?_⟩
    rw [graphWindowAffineEquiv_apply hq.ne' houter.ne']
    apply (lastCoordinateCLE n).injective
    apply Prod.ext
    · ext i
      simp [z, half, normalizeGraphPoint]
      field_simp
      ring
    · simp [z, normalizeGraphPoint, houter.ne']

theorem volume_graphWindowReferenceBox {n : ℕ} {q outer : ℝ}
    (hq : 0 ≤ q) (houter : 0 ≤ outer) :
    volume (graphWindowReferenceBox n q outer) =
      ENNReal.ofReal ((2 * q) ^ n * outer) := by
  rw [graphWindowReferenceBox, volume_lastCoordinateCLE_symm_image,
    graphWindowReferenceProduct,
    volume_affineGraphSlab_closedAxisBox _ _ _ (by positivity)]
  simp only [sub_neg_eq_add, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [show q + q = 2 * q by ring,
    show 2 * (outer / 2) = outer by ring]
  rw [← ENNReal.ofReal_pow (by positivity : 0 ≤ 2 * q) n,
    ← ENNReal.ofReal_mul (by positivity)]

theorem volume_graphWindowUnitBox (n : ℕ) :
    volume (graphWindowUnitBox n) = 1 := by
  rw [graphWindowUnitBox, volume_lastCoordinateCLE_symm_image,
    graphWindowUnitProduct,
    volume_affineGraphSlab_closedAxisBox _ _ _ (by norm_num)]
  simp

/-- Exact Jacobian cancellation for the graph-window chart. -/
theorem graphWindowVolumeFactor_mul_referenceVolume {n : ℕ}
    {q outer : ℝ} (hq : 0 < q) (houter : 0 < outer) :
    affineEquivVolumeFactor
        (graphWindowAffineEquiv (n := n) q outer hq.ne' houter.ne') *
      ENNReal.ofReal ((2 * q) ^ n * outer) = 1 := by
  have hvol := volume_affineEquivImage
    (graphWindowAffineEquiv (n := n) q outer hq.ne' houter.ne')
    (graphWindowReferenceBox n q outer)
  rw [graphWindowAffineEquiv_image_referenceBox hq houter,
    volume_graphWindowUnitBox,
    volume_graphWindowReferenceBox hq.le houter.le] at hvol
  exact hvol.symm

/-- A normalized-volume estimate becomes a relative-volume estimate in the
original body after multiplying by the physical reference volume. -/
theorem graphWindow_volume_le_chart_body
    {n : ℕ} {q outer eta c : ℝ}
    (hq : 0 < q) (houter : 0 < outer) (heta : 0 ≤ eta) (hc : 0 ≤ c)
    {Omega : Set (EuclideanPoint (n + 1))}
    (hOmegaLower : ENNReal.ofReal c ≤ volume Omega)
    {W : Set (EuclideanPoint n × ℝ)} {r : ℝ}
    (hnormalized :
      volume (minkowskiClosedBall W r) *
          ENNReal.ofReal ((2 * q) ^ n * outer) ≤
        ENNReal.ofReal eta * ENNReal.ofReal c) :
    volume (minkowskiClosedBall W r) ≤
      ENNReal.ofReal eta *
        volume (graphWindowAffineEquiv q outer hq.ne' houter.ne' '' Omega) := by
  let e := graphWindowAffineEquiv (n := n) q outer hq.ne' houter.ne'
  have hfactor := graphWindowVolumeFactor_mul_referenceVolume
    (n := n) hq houter
  rw [volume_affineEquivImage]
  calc
    volume (minkowskiClosedBall W r) =
        volume (minkowskiClosedBall W r) *
          (affineEquivVolumeFactor e *
            ENNReal.ofReal ((2 * q) ^ n * outer)) := by rw [hfactor, mul_one]
    _ = affineEquivVolumeFactor e *
        (volume (minkowskiClosedBall W r) *
          ENNReal.ofReal ((2 * q) ^ n * outer)) := by ac_rfl
    _ ≤ affineEquivVolumeFactor e *
        (ENNReal.ofReal eta * ENNReal.ofReal c) := by gcongr
    _ ≤ ENNReal.ofReal eta *
        (affineEquivVolumeFactor e * volume Omega) := by
      calc
        affineEquivVolumeFactor e *
              (ENNReal.ofReal eta * ENNReal.ofReal c) =
            ENNReal.ofReal eta *
              (affineEquivVolumeFactor e * ENNReal.ofReal c) := by ac_rfl
        _ ≤ ENNReal.ofReal eta *
              (affineEquivVolumeFactor e * volume Omega) := by gcongr

end
end Erdos186.PZ.ConvexDensity
