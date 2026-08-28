import Wikipedia.NoExoticSixSphere.RadialShapeChange
import Wikipedia.NoExoticSixSphere.FiberCoordinateCollapse
import Wikipedia.NoExoticSixSphere.OpenProductSlice

/-!
# An open-tube homotopy from an ellipsoidal fiber to a round fiber

The quadratic defect is nonnegative after a uniform shrinking factor is
chosen. Radial compression by its time multiple is an actual open embedding
of the full parameter/base/fiber product. Composing with the original open
tube therefore gives a based collapse homotopy, uniformly at infinity.
-/

noncomputable section

open Function Set Topology
open scoped unitInterval

namespace NoExoticSixSphere.RadialTubeShapeHomotopy

def scale (s : ℝ) (t : I) : ℝ := (1 - (t : ℝ)) + (t : ℝ) * s

theorem scale_pos {s : ℝ} (hs : 0 < s) (t : I) : 0 < scale s t := by
  unfold scale
  by_cases ht : (t : ℝ) = 0
  · rw [ht, sub_zero, zero_mul, add_zero]
    exact zero_lt_one
  · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr t.property.2)
      (mul_pos (lt_of_le_of_ne t.property.1 (Ne.symm ht)) hs)

theorem continuous_scale (s : ℝ) : Continuous (scale s) :=
  (continuous_const.sub continuous_subtype_val).add (continuous_subtype_val.mul continuous_const)

variable {M K Y : Type*} [TopologicalSpace M]
  [NormedAddCommGroup K] [NormedSpace ℝ K] [TopologicalSpace Y]
  (L : M → K ≃L[ℝ] K) (s : ℝ) (hs : 0 < s)

def quadratic (p : (I × M) × K) : ℝ :=
  (p.1.1 : ℝ) * RadialShapeChange.defect (L p.1.2).toContinuousLinearMap s p.2

theorem quadratic_smul (b : I × M) (c : ℝ) (v : K) :
    quadratic L s (b, c • v) = c ^ 2 * quadratic L s (b, v) := by
  rw [quadratic, RadialShapeChange.defect_smul, quadratic]
  ring

include hs in
theorem quadratic_nonneg (hb : ∀ m v, s * ‖L m v‖ ≤ ‖v‖) (p : (I × M) × K) :
    0 ≤ quadratic L s p :=
  mul_nonneg p.1.1.property.1
    (RadialShapeChange.defect_nonneg (L p.1.2).toContinuousLinearMap s hs.le (hb p.1.2) p.2)

def scaledCoordinates (b : I × M) : K ≃ₜ K :=
  (L b.2).toHomeomorph.trans (Homeomorph.smulOfNeZero (scale s b.1) (scale_pos hs b.1).ne')

def tubeFamily (τ : M × K → Y) (p : (I × M) × K) : I × Y :=
  OpenFiberCollapse.parameterTube τ (scaledCoordinates L s hs)
    (QuadraticRadialCompression.compress (quadratic L s) p)

def tube (τ : M × K → Y) (t : I) (p : M × K) : Y := (tubeFamily L s hs τ ((t, p.1), p.2)).2

theorem tubeFamily_time (τ : M × K → Y) (p : (I × M) × K) :
    (tubeFamily L s hs τ p).1 = p.1.1 := rfl

theorem tube_zero (τ : M × K → Y) (p : M × K) :
    tube L s hs τ 0 p = τ (p.1, L p.1 p.2) := by
  change τ (p.1, scale s 0 • L p.1 ((Real.sqrt (1 + quadratic L s ((0, p.1), p.2)))⁻¹ •
    p.2)) = τ (p.1, L p.1 p.2)
  simp only [scale, quadratic, Set.Icc.coe_zero, sub_zero, zero_mul, add_zero,
    zero_add, Real.sqrt_one, inv_one, one_smul]

theorem tube_one (τ : M × K → Y) (p : M × K) :
    tube L s hs τ 1 p =
      τ (p.1, RadialShapeChange.finalCoordinates (L p.1).toContinuousLinearMap s p.2) := by
  change τ (p.1, scale s 1 • L p.1 ((Real.sqrt (1 + quadratic L s ((1, p.1), p.2)))⁻¹ •
    p.2)) = _
  simp only [scale, quadratic, Set.Icc.coe_one, sub_self, one_mul, zero_add]
  rfl

theorem tube_core (τ : M × K → Y) (t : I) (m : M) : tube L s hs τ t (m, 0) = τ (m, 0) := by
  change τ (m, scale s t • L m ((Real.sqrt (1 + quadratic L s ((t, m), 0)))⁻¹ • 0)) = _
  rw [smul_zero, map_zero, smul_zero]

variable (hc : Continuous (fun p : M × K ↦ L p.1 p.2))
  (hi : Continuous (fun p : M × K ↦ (L p.1).symm p.2))

include hc in
theorem continuous_quadratic : Continuous (quadratic L s) := by
  have hL : Continuous (fun p : (I × M) × K ↦ L p.1.2 p.2) :=
    hc.comp (continuous_fst.snd.prodMk continuous_snd)
  exact (continuous_subtype_val.comp continuous_fst.fst).mul
    ((continuous_snd.norm.pow 2).sub (continuous_const.mul (hL.norm.pow 2)))

include hc in
theorem continuous_scaledCoordinates :
    Continuous (fun p : (I × M) × K ↦ scaledCoordinates L s hs p.1 p.2) :=
  ((continuous_scale s).comp continuous_fst.fst).smul
    (hc.comp (continuous_fst.snd.prodMk continuous_snd))

include hi in
theorem continuous_scaledCoordinates_symm :
    Continuous (fun p : (I × M) × K ↦ (scaledCoordinates L s hs p.1).symm p.2) :=
  hi.comp (continuous_fst.snd.prodMk
    ((((continuous_scale s).inv₀ (fun t ↦ (scale_pos hs t).ne')).comp
      continuous_fst.fst).smul continuous_snd))

include hc hi in
theorem isOpenEmbedding_tubeFamily (hb : ∀ m v, s * ‖L m v‖ ≤ ‖v‖)
    (τ : M × K → Y) (hτ : IsOpenEmbedding τ) : IsOpenEmbedding (tubeFamily L s hs τ) :=
  (OpenFiberCollapse.isOpenEmbedding_parameterTube τ (scaledCoordinates L s hs) hτ
    (continuous_scaledCoordinates L s hs hc) (continuous_scaledCoordinates_symm L s hs hi)).comp
      (QuadraticRadialCompression.isOpenEmbedding_compress (quadratic L s)
        (quadratic_nonneg L s hs hb) (quadratic_smul L s) (continuous_quadratic L s hc))

include hc hi in
theorem isOpenEmbedding_tube (hb : ∀ m v, s * ‖L m v‖ ≤ ‖v‖)
    (τ : M × K → Y) (hτ : IsOpenEmbedding τ) (t : I) :
    IsOpenEmbedding (tube L s hs τ t) := by
  have hj : Continuous (fun p : M × K ↦ ((t, p.1), p.2)) :=
    (continuous_const.prodMk continuous_fst).prodMk continuous_snd
  exact (OpenFiberCollapse.isOpenEmbedding_coordinateTube τ (scaledCoordinates L s hs) hτ
    (continuous_scaledCoordinates L s hs hc) (continuous_scaledCoordinates_symm L s hs hi) t).comp
      (QuadraticRadialCompression.isOpenEmbedding_compress
        (fun p : M × K ↦ quadratic L s ((t, p.1), p.2))
        (fun p ↦ quadratic_nonneg L s hs hb ((t, p.1), p.2))
        (fun m c v ↦ quadratic_smul L s (t, m) c v)
        ((continuous_quadratic L s hc).comp hj))

variable [CompactSpace M] [T2Space Y] [LocallyCompactSpace Y]
  (hb : ∀ m v, s * ‖L m v‖ ≤ ‖v‖) (τ : M × K → Y) (hτ : IsOpenEmbedding τ)

def compactTubeFamily (p : (I × M) × K) : I × OnePoint Y :=
  ((tubeFamily L s hs τ p).1, ((tubeFamily L s hs τ p).2 : OnePoint Y))

include hc hi hb hτ in
theorem isOpenEmbedding_compactTubeFamily : IsOpenEmbedding (compactTubeFamily L s hs τ) :=
  ((Homeomorph.refl I).isOpenEmbedding.prodMap OnePoint.isOpenEmbedding_coe).comp
    (isOpenEmbedding_tubeFamily L s hs hc hi hb τ hτ)

def collapseFamily : C(I × OnePoint Y, OnePoint K) :=
  ⟨OpenFiberCollapse.collapse (compactTubeFamily L s hs τ),
    OpenFiberCollapse.continuous_collapse _
      (isOpenEmbedding_compactTubeFamily L s hs hc hi hb τ hτ)⟩

theorem collapseFamily_apply (t : I) (z : OnePoint Y) :
    collapseFamily L s hs hc hi hb τ hτ (t, z) =
      OpenFiberCollapse.collapseOnePoint (tube L s hs τ t) z :=
  OpenProductSlice.ProductBase.collapse_slice (compactTubeFamily L s hs τ) (fun _ ↦ rfl)
    (isOpenEmbedding_compactTubeFamily L s hs hc hi hb τ hτ).injective t z

theorem collapseFamily_infty (t : I) :
    collapseFamily L s hs hc hi hb τ hτ (t, OnePoint.infty) = OnePoint.infty := by
  rw [collapseFamily_apply, OpenFiberCollapse.collapseOnePoint_infty]

def collapseAt (t : I) : C(OnePoint Y, OnePoint K) :=
  (collapseFamily L s hs hc hi hb τ hτ).comp
    ((ContinuousMap.const _ t).prodMk (ContinuousMap.id _))

def collapseHomotopy :
    (collapseAt L s hs hc hi hb τ hτ 0).Homotopy (collapseAt L s hs hc hi hb τ hτ 1) where
  toContinuousMap := collapseFamily L s hs hc hi hb τ hτ
  map_zero_left _ := rfl
  map_one_left _ := rfl

theorem collapseHomotopy_infty (t : I) :
    collapseHomotopy L s hs hc hi hb τ hτ (t, OnePoint.infty) = OnePoint.infty :=
  collapseFamily_infty L s hs hc hi hb τ hτ t

end NoExoticSixSphere.RadialTubeShapeHomotopy
