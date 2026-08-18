/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Proposition74Construction
import ErdosProblems.Erdos186.CFP.Bilu.Case2Coordinates
import ErdosProblems.Erdos186.CFP.Bilu.Section8Case2Canonical

/-!
# The Case 2 branch of Bilu Proposition 7.5

This file is the consumer layer between the source data of Proposition 7.4
and the completed geometry of Section 8.3.  It transports the source
Hilbert product to one coordinate Euclidean space, constructs the literal
normal-coordinate body, and applies equations (8.7)--(8.10).

No estimate is stored in `Case2Witness`: its fields are the geometric
objects and set containments constructed in Sections 7--8.  The resulting
volume inequality is `raw_case2_bound`.
-/

namespace Erdos186.CFP.Bilu.Proposition75Case2

open MeasureTheory Set Module Submodule
open scoped ENNReal Pointwise RealInnerProductSpace
open ProjectionVolumeCoarse VolumeSections
open Proposition75Data Case2Coordinates Section8Case2Canonical

noncomputable section

/-- The source Hilbert product, written as one coordinate Euclidean space. -/
noncomputable def ambientEquiv (m r : ℕ) :
    Ambient m r ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m + r)) :=
  (euclideanFinAddEquivProdL2 m r).symm

/-- Equation (7.7) in the ordinary product underlying the Hilbert sum. -/
def rawDistortionBody {m r : ℕ}
    (B : Set (EuclideanSpace ℝ (Fin m)))
    (a : Fin r → EuclideanSpace ℝ (Fin m)) :
    Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin r)) :=
  (MeasurableEquiv.toLp 2 _) ⁻¹' distortionBody B a

theorem measurableSet_rawDistortionBody {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    (hB : MeasurableSet B) (a : Fin r → EuclideanSpace ℝ (Fin m)) :
    MeasurableSet (rawDistortionBody B a) :=
  (measurableSet_distortionBody hB a).preimage
    (MeasurableEquiv.toLp 2 _).measurable

/-- Every vertical fibre of (7.7) is either empty or a translate of the
cube `[-1,1]^r`. -/
theorem rawDistortionBody_fiber {m r : ℕ}
    (B : Set (EuclideanSpace ℝ (Fin m)))
    (a : Fin r → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin m)) :
    (fun y : EuclideanSpace ℝ (Fin r) ↦ (x, y)) ⁻¹'
        rawDistortionBody B a =
      {y | x ∈ (2 : ℝ) • B ∧
        WithLp.ofLp y ∈
          Icc (fun i ↦ ⟪x, a i⟫ - 1) (fun i ↦ ⟪x, a i⟫ + 1)} := by
  ext y
  change (x ∈ (2 : ℝ) • B ∧
      ∀ i, |⟪x, a i⟫ - WithLp.ofLp y i| ≤ 1) ↔
    x ∈ (2 : ℝ) • B ∧
      ((∀ i, ⟪x, a i⟫ - 1 ≤ WithLp.ofLp y i) ∧
        ∀ i, WithLp.ofLp y i ≤ ⟪x, a i⟫ + 1)
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    constructor
    · intro i
      linarith [(abs_le.mp (h i)).2]
    · intro i
      linarith [(abs_le.mp (h i)).1]
  · rintro ⟨hx, hlo, hhi⟩
    refine ⟨hx, fun i ↦ abs_le.mpr ?_⟩
    exact ⟨by linarith [hhi i], by linarith [hlo i]⟩

/-- The exact fibre volume in (7.7). -/
theorem volume_rawDistortionBody_fiber {m r : ℕ}
    (B : Set (EuclideanSpace ℝ (Fin m)))
    (a : Fin r → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin m)) :
    volume ((fun y : EuclideanSpace ℝ (Fin r) ↦ (x, y)) ⁻¹'
        rawDistortionBody B a) =
      ((2 : ℝ) • B).indicator (fun _ ↦ (2 : ENNReal) ^ r) x := by
  classical
  rw [rawDistortionBody_fiber]
  by_cases hx : x ∈ (2 : ℝ) • B
  · rw [Set.indicator_of_mem hx]
    let lo : Fin r → ℝ := fun i ↦ ⟪x, a i⟫ - 1
    let hi : Fin r → ℝ := fun i ↦ ⟪x, a i⟫ + 1
    let e := (MeasurableEquiv.toLp 2 (Fin r → ℝ)).symm
    have he : MeasurePreserving e :=
      EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin r)
    simp only [hx, true_and]
    change volume (e ⁻¹' Icc lo hi) = _
    calc
      volume (e ⁻¹' Icc lo hi) = volume (Icc lo hi) :=
        he.measure_preimage measurableSet_Icc.nullMeasurableSet
      _ = (2 : ENNReal) ^ r := by
        rw [Real.volume_Icc_pi]
        norm_num [lo, hi]
  · simp [hx]

/-- Exact volume of Bilu's distortion body (7.7). -/
theorem volume_distortionBody {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    (hB : MeasurableSet B)
    (a : Fin r → EuclideanSpace ℝ (Fin m)) :
    volume (distortionBody B a) =
      (2 : ENNReal) ^ (m + r) * volume B := by
  classical
  let e := MeasurableEquiv.toLp 2
    (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin r))
  have he : MeasurePreserving e := WithLp.volume_preserving_toLp _ _
  have hraw : MeasurableSet (rawDistortionBody B a) :=
    measurableSet_rawDistortionBody hB a
  calc
    volume (distortionBody B a) = volume (rawDistortionBody B a) :=
      (he.measure_preimage
        (measurableSet_distortionBody hB a).nullMeasurableSet).symm
    _ = (volume.prod volume) (rawDistortionBody B a) := by
      rw [← Measure.volume_eq_prod]
    _ = ∫⁻ x : EuclideanSpace ℝ (Fin m),
          volume ((fun y : EuclideanSpace ℝ (Fin r) ↦ (x, y)) ⁻¹'
            rawDistortionBody B a) := Measure.prod_apply hraw
    _ = ∫⁻ x : EuclideanSpace ℝ (Fin m),
          ((2 : ℝ) • B).indicator (fun _ ↦ (2 : ENNReal) ^ r) x := by
      apply lintegral_congr
      exact fun x ↦ volume_rawDistortionBody_fiber B a x
    _ = (2 : ENNReal) ^ r * volume ((2 : ℝ) • B) := by
      have hscaled : MeasurableSet ((2 : ℝ) • B) := hB.const_smul₀ 2
      rw [lintegral_indicator hscaled, setLIntegral_const]
    _ = (2 : ENNReal) ^ r * ((2 : ENNReal) ^ m * volume B) := by
      rw [volume.addHaar_smul]
      simp [Module.finrank_fin_fun]
    _ = (2 : ENNReal) ^ (m + r) * volume B := by
      rw [pow_add]
      ac_rfl

/-- The source distortion body after the canonical coordinate
identification `E_m ⊕ E_r ≃ E_(m+r)`. -/
def coordinateDistortionBody {m r : ℕ}
    (B : Set (EuclideanSpace ℝ (Fin m)))
    (a : Fin r → EuclideanSpace ℝ (Fin m)) :
    Set (EuclideanSpace ℝ (Fin (m + r))) :=
  (ambientEquiv m r).symm ⁻¹' distortionBody B a

theorem measurableSet_coordinateDistortionBody {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    (hB : MeasurableSet B) (a : Fin r → EuclideanSpace ℝ (Fin m)) :
    MeasurableSet (coordinateDistortionBody B a) :=
  (measurableSet_distortionBody hB a).preimage
    (ambientEquiv m r).symm.continuous.measurable

theorem convex_coordinateDistortionBody {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    (hB : Convex ℝ B) (a : Fin r → EuclideanSpace ℝ (Fin m)) :
    Convex ℝ (coordinateDistortionBody B a) :=
  (convex_distortionBody hB a).linear_preimage
    (ambientEquiv m r).symm.toLinearMap

theorem volume_coordinateDistortionBody {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (hB : MeasurableSet B) :
    volume (coordinateDistortionBody B a) = volume (distortionBody B a) := by
  exact (ambientEquiv m r).symm.measurePreserving.measure_preimage
    (measurableSet_distortionBody hB a).nullMeasurableSet

theorem volume_coordinateDistortionBody_eq {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    (hB : MeasurableSet B)
    (a : Fin r → EuclideanSpace ℝ (Fin m)) :
    volume (coordinateDistortionBody B a) =
      (2 : ENNReal) ^ (m + r) * volume B := by
  rw [volume_coordinateDistortionBody hB, volume_distortionBody hB]

/-- The subspace `C₀` in the single-coordinate ambient model. -/
noncomputable def coordinateC0 {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a) :
    Submodule ℝ (EuclideanSpace ℝ (Fin (m + r))) :=
  D.C0.map (ambientEquiv m r).toLinearMap

/-- Isometric transport from the source `C₀` subtype to `coordinateC0`. -/
noncomputable def coordinateC0Equiv {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a) :
    D.C0 ≃ₗᵢ[ℝ] coordinateC0 D :=
  LinearIsometryEquiv.submoduleMap D.C0 (ambientEquiv m r)

/-- The section `B₀` transported together with its ambient subspace. -/
def coordinateB0 {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a) : Set (coordinateC0 D) :=
  coordinateC0Equiv D '' D.B0

theorem finrank_coordinateC0 {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a) :
    finrank ℝ (coordinateC0 D) = finrank ℝ D.C0 :=
  (coordinateC0Equiv D).toLinearEquiv.finrank_eq.symm

/-- Intrinsic volume of `B₀` is unchanged by the ambient coordinate
identification. -/
theorem volume_coordinateB0 {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a) :
    volume (coordinateB0 D) = μHE[finrank ℝ D.C0] D.B0 := by
  rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume
    (V := coordinateC0 D), finrank_coordinateC0 D]
  exact (coordinateC0Equiv D).isometry.euclideanHausdorffMeasure_image D.B0

/-- A linear projection of a convex body is convex. -/
theorem convex_baseProjection {d : ℕ} {A : Set (Base d × ℝ)}
    (hA : Convex ℝ A) : Convex ℝ (baseProjection A) := by
  rintro x ⟨p, hp, rfl⟩ y ⟨q, hq, rfl⟩ c e hc he hce
  refine ⟨c • p + e • q, hA hp hq hc he hce, ?_⟩
  simp

/-- Geometric output of the Case 2 construction.

The body occurring below is definitionally `coordinateDistortionBody B a`;
the product body used by Fubini is its pullback along the normal-coordinate
map from `Case2Coordinates`.  Consequently measure preservation,
convexity, the base inball, and the vertical segment are all derived in
`raw_case2_bound`, rather than postulated for an unrelated set.
-/
structure Case2Witness {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a) (d k : ℕ) where
  measurable_B : MeasurableSet B
  convex_B : Convex ℝ B
  rank_C0 : finrank ℝ D.C0 = d
  W : Submodule ℝ (EuclideanSpace ℝ (Fin (m + r)))
  u : EuclideanSpace ℝ (Fin (m + r))
  u_ne_zero : u ≠ 0
  u_mem_orthogonal : u ∈ Wᗮ
  W_codim_one : finrank ℝ W + 1 =
    finrank ℝ (EuclideanSpace ℝ (Fin (m + r)))
  q : Base (d + k) ≃ₗᵢ[ℝ] W
  l : EuclideanSpace ℝ (Fin (m + r))
  l_ne_zero : l ≠ 0
  l_mem_orthogonal : l ∈ (coordinateC0 D)ᗮ
  rho : ℝ
  gaugeValue : ℝ
  C : ℝ
  rho_pos : 0 < rho
  gauge_pos : 0 < gaugeValue
  gauge_half : 2 * gaugeValue ≤ 1
  C_pos : 0 < C
  polar_separation : C < |⟪u, l⟫|
  ambient_inball :
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + r))) rho ⊆
      coordinateDistortionBody B a
  normal_segment : ∀ t ∈ Icc (-(‖u‖ / gaugeValue)) (‖u‖ / gaugeValue),
    t • unitNormal u ∈ coordinateDistortionBody B a
  base_measurable : MeasurableSet
    (baseProjection
      ((normalCoordinateMeasurableEquiv W u q W_codim_one
        u_mem_orthogonal u_ne_zero) ⁻¹' coordinateDistortionBody B a))
  half_base_measurable : MeasurableSet
    (halfBaseProjection
      ((normalCoordinateMeasurableEquiv W u q W_codim_one
        u_mem_orthogonal u_ne_zero) ⁻¹' coordinateDistortionBody B a))
  section_image :
    q.symm ''
        (projectionRestrict W (coordinateC0 D) ''
          coordinateB0 D) ⊆
      canonicalCoordinateFlagF d k 0 (Nat.zero_le k) ''
        ((canonicalCoordinateFlagF d k 0 (Nat.zero_le k)) ⁻¹'
          baseProjection
            ((normalCoordinateMeasurableEquiv W u q W_codim_one
              u_mem_orthogonal u_ne_zero) ⁻¹'
                coordinateDistortionBody B a))

/-- The actual Case 2 estimate obtained by applying the completed chain
(8.7)--(8.10) to the source distortion body. -/
theorem raw_case2_bound {m r d k : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    {D : GeometricData B a} (X : Case2Witness D d k) :
    2 * ENNReal.ofReal X.C * μHE[finrank ℝ D.C0] D.B0 ≤
      ((‖(2 : ℝ)⁻¹‖₊ : ENNReal) ^ (d + k))⁻¹ *
        ((2 : ENNReal) ^ (m + r)) *
        (((d.factorial : ENNReal) * ENNReal.ofReal (X.rho ^ k))⁻¹ *
          ((d + k).factorial : ENNReal)) *
        ENNReal.ofReal ‖X.l‖ * volume B := by
  let A : Set (EuclideanSpace ℝ (Fin (m + r))) :=
    coordinateDistortionBody B a
  let Omega : Set (Base (d + k) × ℝ) :=
    (normalCoordinateMeasurableEquiv X.W X.u X.q X.W_codim_one
      X.u_mem_orthogonal X.u_ne_zero) ⁻¹' A
  have hAmeas : MeasurableSet A :=
    measurableSet_coordinateDistortionBody X.measurable_B a
  have hOmegaMeas : MeasurableSet Omega := hAmeas.preimage
    (normalCoordinateMeasurableEquiv X.W X.u X.q X.W_codim_one
      X.u_mem_orthogonal X.u_ne_zero).measurable
  have hOmegaConv : Convex ℝ Omega :=
    convex_preimage_normalCoordinate X.W X.u X.q X.W_codim_one
      X.u_mem_orthogonal X.u_ne_zero
      (convex_coordinateDistortionBody X.convex_B a)
  have hbaseConv : Convex ℝ (baseProjection Omega) :=
    convex_baseProjection hOmegaConv
  have hbaseBall : Metric.closedBall (0 : Base (d + k)) X.rho ⊆
      baseProjection Omega :=
    closedBall_subset_baseProjection_preimage_normalCoordinate
      X.W X.u X.q X.W_codim_one X.u_mem_orthogonal X.u_ne_zero
      X.ambient_inball
  have hsegment : ∀ t ∈ Icc (-(‖X.u‖ / X.gaugeValue))
      (‖X.u‖ / X.gaugeValue),
      ((0 : Base (d + k)), t) ∈ Omega :=
    vertical_segment_mem_preimage_normalCoordinate
      X.W X.u X.q X.W_codim_one X.u_mem_orthogonal X.u_ne_zero
      X.normal_segment
  have hOmegaVolume : (volume.prod volume) Omega ≤
      (2 : ENNReal) ^ (m + r) * volume B := by
    rw [volume_preimage_normalCoordinate X.W X.u X.q X.W_codim_one
      X.u_mem_orthogonal X.u_ne_zero hAmeas]
    exact (volume_coordinateDistortionBody_eq X.measurable_B a).le
  have hcodim : finrank ℝ X.W + 1 =
      finrank ℝ (EuclideanSpace ℝ (Fin (m + r))) := by
    simpa using X.W_codim_one
  have hrank : finrank ℝ (coordinateC0 D) = d := by
    rw [finrank_coordinateC0 D, X.rank_C0]
  have hmain := combine_case2_of_isometric_section_identification
    X.u X.l (coordinateB0 D) X.q.symm.toLinearIsometry
    X.rho_pos X.C_pos X.gauge_pos X.gauge_half X.polar_separation
    hcodim hrank X.u_mem_orthogonal X.u_ne_zero X.l_mem_orthogonal
    X.l_ne_zero hOmegaMeas X.half_base_measurable X.base_measurable
    hOmegaConv hbaseConv hbaseBall hsegment hOmegaVolume (by
      intro x hx
      change x ∈ X.q.symm ''
        (projectionRestrict X.W (coordinateC0 D) '' coordinateB0 D) at hx
      have hmem := X.section_image hx
      simpa only [Omega, A] using hmem)
  rw [volume_coordinateB0 D] at hmain
  exact hmain

/-- The remaining arithmetic after the geometric Case 2 estimate.

`normalFactor` is the dimension factor in the Bombieri--Vaaler norm bound
for the integral normal.  The hypothesis `hconstants` is precisely the
subsequent explicit parameter calculation in Bilu, with no geometric or
lattice assertion hidden inside it. -/
theorem proposition75Conclusion_of_raw_case2 {m r d k : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    {D : GeometricData B a} (X : Case2Witness D d k)
    (normalFactor constant scale : ENNReal)
    (hnormal : ENNReal.ofReal ‖X.l‖ ≤ normalFactor *
      ENNReal.ofReal
        (ZLattice.covolume D.latticePoints μHE[finrank ℝ D.C0]))
    (hconstants :
      (2 * ENNReal.ofReal X.C)⁻¹ *
          (((‖(2 : ℝ)⁻¹‖₊ : ENNReal) ^ (d + k))⁻¹ *
            ((2 : ENNReal) ^ (m + r)) *
            (((d.factorial : ENNReal) * ENNReal.ofReal (X.rho ^ k))⁻¹ *
              ((d + k).factorial : ENNReal))) * normalFactor ≤
        constant * scale) :
    Proposition75Conclusion D constant scale := by
  let V0 : ENNReal := μHE[finrank ℝ D.C0] D.B0
  let covol : ENNReal := ENNReal.ofReal
    (ZLattice.covolume D.latticePoints μHE[finrank ℝ D.C0])
  let G : ENNReal :=
    ((‖(2 : ℝ)⁻¹‖₊ : ENNReal) ^ (d + k))⁻¹ *
      ((2 : ENNReal) ^ (m + r)) *
      (((d.factorial : ENNReal) * ENNReal.ofReal (X.rho ^ k))⁻¹ *
        ((d + k).factorial : ENNReal))
  let factor : ENNReal := 2 * ENNReal.ofReal X.C
  have hraw : factor * V0 ≤ G * ENNReal.ofReal ‖X.l‖ * volume B := by
    simpa only [factor, V0, G, mul_assoc] using raw_case2_bound X
  have hnormal' : ENNReal.ofReal ‖X.l‖ ≤ normalFactor * covol := by
    simpa only [covol] using hnormal
  have hcross : factor * V0 ≤
      (G * normalFactor * volume B) * covol := by
    calc
      factor * V0 ≤ G * ENNReal.ofReal ‖X.l‖ * volume B := hraw
      _ ≤ G * (normalFactor * covol) * volume B := by gcongr
      _ = (G * normalFactor * volume B) * covol := by ac_rfl
  have hfactor0 : factor ≠ 0 := by
    dsimp only [factor]
    exact mul_ne_zero (by norm_num) (ENNReal.ofReal_ne_zero_iff.mpr X.C_pos)
  have hfactortop : factor ≠ ∞ := by
    dsimp only [factor]
    finiteness
  have hsolve : V0 ≤ factor⁻¹ * (G * normalFactor * volume B) * covol :=
    section_le_of_factor_mul_le hfactor0 hfactortop hcross
  have hcoeff : factor⁻¹ * G * normalFactor ≤ constant * scale := by
    simpa only [factor, G, mul_assoc] using hconstants
  change V0 ≤ constant * volume B * scale * covol
  calc
    V0 ≤ factor⁻¹ * (G * normalFactor * volume B) * covol := hsolve
    _ = (factor⁻¹ * G * normalFactor) * volume B * covol := by ac_rfl
    _ ≤ (constant * scale) * volume B * covol := by gcongr
    _ = constant * volume B * scale * covol := by ac_rfl

end

end Erdos186.CFP.Bilu.Proposition75Case2

#print axioms Erdos186.CFP.Bilu.Proposition75Case2.volume_coordinateB0
#print axioms Erdos186.CFP.Bilu.Proposition75Case2.raw_case2_bound
#print axioms Erdos186.CFP.Bilu.Proposition75Case2.proposition75Conclusion_of_raw_case2
