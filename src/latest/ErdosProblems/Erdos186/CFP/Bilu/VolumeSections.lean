/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import ErdosProblems.Erdos186.CFP.Bilu.GaugeRadialIntegral

/-!
# Bilu's section and projection inequalities

This file records the two convex-geometric estimates used in Sections 8
and 9 of Bilu's proof of Freiman's theorem (Bilu, Lemmas 6.5 and 6.6).
We use the normalized Euclidean Hausdorff measure `μHE[d]`; on a
`d`-dimensional Euclidean space this is ordinary Lebesgue volume, while on
an affine `d`-plane it is its intrinsic Euclidean volume.

The inequalities are written in cross-multiplied form.  This is both
faithful to the source and avoids making artificial nonzero assumptions on
volumes.  In particular Lemma 6.5 is

`d! ρ^(n-d) Vol_d(B₁) ≤ n! Vol_n(B)`.

Bilu proves the more general Rogers--Shephard type inequality (6.7)

`Vol_m(π B) Vol_l(B ∩ L) ≤ choose n l Vol_n(B)`

and obtains Lemma 6.6 by taking `L = ℝ w`.  The last part of the file
proves the exact algebraic deductions used for Proposition 8.5 and for
equation (8.8) in Case 2.
-/

namespace Erdos186.CFP.Bilu.VolumeSections

open Filter MeasureTheory MeasureTheory.Measure Set Module
open scoped ENNReal MeasureTheory Pointwise Topology

/-- The elementary beta-integral which supplies the factor `1 / (d+1)`
in the volume of a cone. -/
theorem integral_one_sub_div_pow {d : ℕ} {h : ℝ} (hh : 0 < h) :
    (∫ x in (0 : ℝ)..h, (1 - x / h) ^ d) = h / (d + 1) := by
  have hc : -(h⁻¹) ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hh.ne')
  have hchange := intervalIntegral.integral_comp_mul_add
    (f := fun x : ℝ ↦ x ^ d) (a := (0 : ℝ)) (b := h)
    (c := -(h⁻¹)) hc (1 : ℝ)
  calc
    (∫ x in (0 : ℝ)..h, (1 - x / h) ^ d) =
        ∫ x in (0 : ℝ)..h, (-(h⁻¹) * x + 1) ^ d := by
      congr 1
      funext x
      congr 1
      field_simp
      ring
    _ = (-(h⁻¹))⁻¹ •
        ∫ x in (-(h⁻¹) * 0 + 1)..(-(h⁻¹) * h + 1), x ^ d := hchange
    _ = h / (d + 1) := by
      rw [integral_pow d]
      simp [hh.ne']
      field_simp

/-- `ℝ≥0∞` form of `integral_one_sub_div_pow`, on the open interval used
as the height coordinate of a cone. -/
theorem lintegral_one_sub_div_pow {d : ℕ} {h : ℝ} (hh : 0 < h) :
    (∫⁻ x in Set.Ioo (0 : ℝ) h, ENNReal.ofReal ((1 - x / h) ^ d)) =
      ENNReal.ofReal (h / (d + 1)) := by
  let f : ℝ → ℝ := fun x ↦ (1 - x / h) ^ d
  have hfcont : Continuous f := by
    fun_prop
  have hfintIoc : Integrable f (volume.restrict (Set.Ioc (0 : ℝ) h)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hh.le).mp
      (hfcont.intervalIntegrable 0 h)
  have hfintIoo : Integrable f (volume.restrict (Set.Ioo (0 : ℝ) h)) := by
    rwa [restrict_Ioo_eq_restrict_Ioc]
  have hfnn : (fun _ : ℝ ↦ (0 : ℝ))
      ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) h)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact pow_nonneg (sub_nonneg.mpr ((div_le_one hh).2 hx.2.le)) d
  calc
    (∫⁻ x in Set.Ioo (0 : ℝ) h, ENNReal.ofReal ((1 - x / h) ^ d)) =
        ENNReal.ofReal (∫ x in Set.Ioo (0 : ℝ) h, f x) := by
      exact (ofReal_integral_eq_lintegral_ofReal hfintIoo hfnn).symm
    _ = ENNReal.ofReal (∫ x in (0 : ℝ)..h, f x) := by
      rw [intervalIntegral.integral_of_le hh.le]
      congr 2
      exact restrict_Ioo_eq_restrict_Ioc
    _ = ENNReal.ofReal (h / (d + 1)) := by
      rw [integral_one_sub_div_pow hh]

/-- Intrinsic `d`-dimensional Euclidean volume of a set in a Euclidean
ambient space. -/
noncomputable def intrinsicVolume {X : Type*} [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (d : ℕ) (s : Set X) : ℝ≥0∞ :=
  μHE[d] s

@[simp]
theorem intrinsicVolume_def {X : Type*} [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] {d : ℕ} (s : Set X) :
    intrinsicVolume d s = μHE[d] s := rfl

/-- Taking the closure of a convex set does not change its
full-dimensional Euclidean volume.  This is the measure-theoretic step
needed to use Bilu's source hypothesis that the inball lies in `closure B`. -/
theorem intrinsicVolume_closure_of_convex {n : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin n))} (hconv : Convex ℝ B) :
    intrinsicVolume n (closure B) = intrinsicVolume n B := by
  simp only [intrinsicVolume]
  apply measure_closure_of_null_frontier
  rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  exact hconv.addHaar_frontier volume

/-! ## Exact volume of a coordinate cone -/

/-- The orthogonal product used to model a cone over a `d`-dimensional
base. -/
abbrev ConeProduct (d : ℕ) :=
  WithLp 2 (ℝ × EuclideanSpace ℝ (Fin d))

/-- The cone before transporting the ordinary product into its Hilbert
direct-sum norm.  The apex is `(h, 0)` and the base is `{0} × S`; the two
boundary slices are omitted, which does not change its volume. -/
def rawCoordinateCone {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (h : ℝ) : Set (ℝ × EuclideanSpace ℝ (Fin d)) :=
  {p | p.1 ∈ Set.Ioo (0 : ℝ) h ∧ p.2 ∈ (1 - p.1 / h) • S}

/-- The raw cone over a measurable base is measurable.  On the open
height interval its fiber condition is equivalently tested by scaling by
the reciprocal factor. -/
theorem measurableSet_rawCoordinateCone {d : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin d))} {h : ℝ}
    (hS : MeasurableSet S) (hh : 0 < h) :
    MeasurableSet (rawCoordinateCone S h) := by
  let q : (ℝ × EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) :=
    fun p ↦ (1 - p.1 / h)⁻¹ • p.2
  have hq : Measurable q := by
    fun_prop
  have hset : rawCoordinateCone S h =
      (Prod.fst ⁻¹' Set.Ioo (0 : ℝ) h) ∩ q ⁻¹' S := by
    ext p
    simp only [rawCoordinateCone, mem_setOf_eq, mem_inter_iff, mem_preimage, q]
    constructor
    · rintro ⟨hp, y, hy, hpy⟩
      refine ⟨hp, ?_⟩
      have ha : 1 - p.1 / h ≠ 0 :=
        (sub_pos.mpr ((div_lt_one hh).2 hp.2)).ne'
      rw [← hpy]
      simpa [ha] using hy
    · rintro ⟨hp, hpS⟩
      refine ⟨hp, (1 - p.1 / h)⁻¹ • p.2, hpS, ?_⟩
      have ha : 1 - p.1 / h ≠ 0 :=
        (sub_pos.mpr ((div_lt_one hh).2 hp.2)).ne'
      simp [ha]
  rw [hset]
  exact (measurable_fst measurableSet_Ioo).inter (hS.preimage hq)

/-- Transport the coordinate cone to the orthogonal product. -/
def coordinateCone {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (h : ℝ) : Set (ConeProduct d) :=
  (MeasurableEquiv.toLp 2 (ℝ × EuclideanSpace ℝ (Fin d))) ''
    rawCoordinateCone S h

/-- A point in the orthogonal product used for the base and apex of a
coordinate cone. -/
def conePair {d : ℕ} (r : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    ConeProduct d :=
  WithLp.toLp 2 (r, x)

/-- Canonical orthogonal decomposition of a coordinate Euclidean space
at a sum of dimensions. -/
noncomputable def euclideanFinAddEquivProdL2 (a b : ℕ) :
    EuclideanSpace ℝ (Fin (a + b)) ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin a) × EuclideanSpace ℝ (Fin b)) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv.symm).trans
    (PiLp.sumPiLpEquivProdLpPiLp 2
      (fun _ : Fin a ⊕ Fin b ↦ ℝ))

/-- Canonical identification of `ℝ ⊕ ℝ^d` with `ℝ^(d+1)`. -/
noncomputable def coneProductEquivSuccessor (d : ℕ) :
    ConeProduct d ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (d + 1)) :=
  (LinearIsometryEquiv.withLpProdComm 2 ℝ ℝ
      (EuclideanSpace ℝ (Fin d))).trans <|
    (LinearIsometryEquiv.withLpProdCongr 2
      (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin d)))
      (OrthonormalBasis.singleton (Fin 1) ℝ).repr).trans <|
      (euclideanFinAddEquivProdL2 d 1).symm

/-- Convexity puts the entire coordinate cone inside any set containing
its base and apex. -/
theorem coordinateCone_subset_of_convex {d : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin d))} {h : ℝ}
    {B : Set (ConeProduct d)} (hh : 0 < h) (hconv : Convex ℝ B)
    (hbase : ∀ x ∈ S, conePair 0 x ∈ B)
    (hapex : conePair h 0 ∈ B) :
    coordinateCone S h ⊆ B := by
  rintro z ⟨p, hp, rfl⟩
  rcases hp with ⟨hr, hy⟩
  rcases hy with ⟨x, hx, hxy⟩
  have ht0 : 0 ≤ p.1 / h := div_nonneg hr.1.le hh.le
  have ht1 : 0 ≤ 1 - p.1 / h :=
    sub_nonneg.mpr ((div_le_one hh).2 hr.2.le)
  have hz := hconv (hbase x hx) hapex ht1 ht0 (by ring)
  convert hz using 1
  apply (MeasurableEquiv.toLp 2
    (ℝ × EuclideanSpace ℝ (Fin d))).symm.injective
  apply Prod.ext
  · simp [conePair]
    field_simp
  · change p.2 = (1 - p.1 / h) • x + (p.1 / h) • 0
    simpa using hxy.symm

/-- Exact Fubini computation of the volume of a cone.  The only explicit
measurability premise is the natural one needed by `Measure.prod_apply`;
in applications it follows, for example, from measurability of the convex
body containing the base. -/
theorem intrinsicVolume_coordinateCone {d : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin d))} {h : ℝ} (hh : 0 < h)
    (hcone : MeasurableSet (rawCoordinateCone S h)) :
    intrinsicVolume (d + 1) (coordinateCone S h) =
      ENNReal.ofReal (h / (d + 1)) * intrinsicVolume d S := by
  have hrank : finrank ℝ (ConeProduct d) = d + 1 := by
    calc
      finrank ℝ (ConeProduct d) =
          finrank ℝ (ℝ × EuclideanSpace ℝ (Fin d)) :=
        (WithLp.linearEquiv 2 ℝ
          (ℝ × EuclideanSpace ℝ (Fin d))).finrank_eq
      _ = d + 1 := by simp [add_comm]
  simp only [intrinsicVolume]
  rw [
    show (μHE[d + 1] : Measure (ConeProduct d)) = volume by
      rw [← hrank]
      exact
        (InnerProductSpace.euclideanHausdorffMeasure_eq_volume
          (V := ConeProduct d)),
    show (μHE[d] : Measure (EuclideanSpace ℝ (Fin d))) = volume by
      simpa using
        (InnerProductSpace.euclideanHausdorffMeasure_eq_volume
          (V := EuclideanSpace ℝ (Fin d)))]
  let e : (ℝ × EuclideanSpace ℝ (Fin d)) ≃ᵐ ConeProduct d :=
    MeasurableEquiv.toLp 2 _
  have he : MeasurePreserving e := WithLp.volume_preserving_toLp _ _
  have himage : e '' rawCoordinateCone S h =
      e.symm ⁻¹' rawCoordinateCone S h := by
    ext z
    constructor
    · rintro ⟨q, hq, rfl⟩
      simpa using hq
    · intro hz
      exact ⟨e.symm z, hz, e.apply_symm_apply z⟩
  have hfiber (r : ℝ) :
      volume (Prod.mk r ⁻¹' rawCoordinateCone S h) =
        if r ∈ Set.Ioo (0 : ℝ) h then
          ENNReal.ofReal ((1 - r / h) ^ d) * volume S else 0 := by
    by_cases hr : r ∈ Set.Ioo (0 : ℝ) h
    · rw [if_pos hr]
      have hset : Prod.mk r ⁻¹' rawCoordinateCone S h =
          (1 - r / h) • S := by
        ext x
        simp only [mem_preimage, rawCoordinateCone, mem_setOf_eq]
        simp [hr]
      rw [hset, addHaar_smul_of_nonneg volume
        (sub_nonneg.mpr ((div_le_one hh).2 hr.2.le))]
      simp
    · rw [if_neg hr]
      have hset : Prod.mk r ⁻¹' rawCoordinateCone S h = ∅ := by
        ext x
        simp only [mem_preimage, rawCoordinateCone, mem_setOf_eq, mem_empty_iff_false]
        simp [hr]
      simp [hset]
  have hscale_meas : Measurable
      (fun r : ℝ ↦ ENNReal.ofReal ((1 - r / h) ^ d)) := by
    fun_prop
  change volume (coordinateCone S h) = _
  rw [coordinateCone, show
      (MeasurableEquiv.toLp 2 (ℝ × EuclideanSpace ℝ (Fin d))) = e from rfl,
    himage, he.symm.measure_preimage_equiv, Measure.volume_eq_prod,
    Measure.prod_apply hcone]
  simp_rw [hfiber]
  calc
    (∫⁻ r : ℝ, if r ∈ Set.Ioo (0 : ℝ) h then
        ENNReal.ofReal ((1 - r / h) ^ d) * volume S else 0) =
        ∫⁻ r in Set.Ioo (0 : ℝ) h,
          ENNReal.ofReal ((1 - r / h) ^ d) * volume S := by
      rw [← lintegral_indicator measurableSet_Ioo]
      apply lintegral_congr
      intro r
      simp only [Set.indicator_apply]
    _ = (∫⁻ r in Set.Ioo (0 : ℝ) h,
          ENNReal.ofReal ((1 - r / h) ^ d)) * volume S := by
      exact lintegral_mul_const'' (volume S)
        hscale_meas.aemeasurable.restrict
    _ = ENNReal.ofReal (h / (d + 1)) * volume S := by
      rw [lintegral_one_sub_div_pow hh]

/-- Exact codimension-one section estimate in coordinate normal form.
This is the sharp cone step in Bilu's induction for Lemma 6.5: the factor
is exactly `h/(d+1)`, not the coarse midpoint-product constant. -/
theorem coordinate_cone_section_bound {d : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin d))} {h : ℝ}
    {B : Set (ConeProduct d)} (hh : 0 < h)
    (hcone : MeasurableSet (rawCoordinateCone S h))
    (hconv : Convex ℝ B)
    (hbase : ∀ x ∈ S, conePair 0 x ∈ B)
    (hapex : conePair h 0 ∈ B) :
    ENNReal.ofReal (h / (d + 1)) * intrinsicVolume d S ≤
      intrinsicVolume (d + 1) B := by
  calc
    ENNReal.ofReal (h / (d + 1)) * intrinsicVolume d S =
        intrinsicVolume (d + 1) (coordinateCone S h) :=
      (intrinsicVolume_coordinateCone hh hcone).symm
    _ ≤ intrinsicVolume (d + 1) B :=
      measure_mono (coordinateCone_subset_of_convex hh hconv hbase hapex)

/-- Cross-multiplied form of the sharp coordinate codimension-one bound.
It is the `n=d+1` induction step in the normalization of Bilu's Lemma 6.5. -/
theorem coordinate_cone_section_bound_crossmultiplied {d : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin d))} {h : ℝ}
    {B : Set (ConeProduct d)} (hh : 0 < h)
    (hcone : MeasurableSet (rawCoordinateCone S h))
    (hconv : Convex ℝ B)
    (hbase : ∀ x ∈ S, conePair 0 x ∈ B)
    (hapex : conePair h 0 ∈ B) :
    ENNReal.ofReal h * intrinsicVolume d S ≤
      (d + 1 : ℝ≥0∞) * intrinsicVolume (d + 1) B := by
  have hb := coordinate_cone_section_bound hh hcone hconv hbase hapex
  have hdpos : (0 : ℝ) < d + 1 := by positivity
  rw [ENNReal.ofReal_div_of_pos hdpos] at hb
  have hdreal : ENNReal.ofReal ((d : ℝ) + 1) = (d + 1 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_add (Nat.cast_nonneg d) zero_le_one]
    simp
  rw [hdreal] at hb
  have hd0 : (d + 1 : ℝ≥0∞) ≠ 0 := by norm_num
  have hdtop : (d + 1 : ℝ≥0∞) ≠ ∞ := by finiteness
  have hb' :
      (ENNReal.ofReal h * intrinsicVolume d S) / (d + 1 : ℝ≥0∞) ≤
        intrinsicVolume (d + 1) B := by
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hb
  have hcross := (ENNReal.div_le_iff hd0 hdtop).mp hb'
  simpa only [mul_comm] using hcross

/-- The sharp cone bound transported through a linear isometric embedding
and a translation.  This is the coordinate-free interface needed to place
the cone over a section in an arbitrary ambient Euclidean space. -/
theorem isometric_coordinate_cone_section_bound_crossmultiplied
    {d : ℕ} {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X]
    {S : Set (EuclideanSpace ℝ (Fin d))} {h : ℝ} {B : Set X}
    (g : ConeProduct d →ₗᵢ[ℝ] X) (c : X)
    (hh : 0 < h) (hcone : MeasurableSet (rawCoordinateCone S h))
    (hconv : Convex ℝ B)
    (hbase : ∀ x ∈ S, c + g (conePair 0 x) ∈ B)
    (hapex : c + g (conePair h 0) ∈ B) :
    ENNReal.ofReal h * intrinsicVolume d S ≤
      (d + 1 : ℝ≥0∞) * intrinsicVolume (d + 1) B := by
  let preB : Set (ConeProduct d) := {z | c + g z ∈ B}
  have hpreconv : Convex ℝ preB := by
    intro x hx y hy a b ha hb hab
    have hz := hconv hx hy ha hb hab
    change c + g (a • x + b • y) ∈ B
    convert hz using 1
    simp only [map_add, map_smul]
    have hc : c = a • c + b • c := by
      rw [← add_smul, hab, one_smul]
    calc
      c + (a • g x + b • g y) =
          (a • c + b • c) + (a • g x + b • g y) :=
        congrArg (fun u ↦ u + (a • g x + b • g y)) hc
      _ = a • (c + g x) + b • (c + g y) := by module
  have hprebase : ∀ x ∈ S, conePair 0 x ∈ preB := by
    intro x hx
    exact hbase x hx
  have hpreapex : conePair h 0 ∈ preB := hapex
  have hconesub : coordinateCone S h ⊆ preB :=
    coordinateCone_subset_of_convex hh hpreconv hprebase hpreapex
  let f : ConeProduct d → X := fun z ↦ c + g z
  have hf : Isometry f := (isometry_vadd X c).comp g.isometry
  have himagesub : f '' coordinateCone S h ⊆ B := by
    rintro _ ⟨z, hz, rfl⟩
    exact hconesub hz
  have hbcoef :
      ENNReal.ofReal (h / (d + 1)) * intrinsicVolume d S ≤
        intrinsicVolume (d + 1) B := by
    calc
      ENNReal.ofReal (h / (d + 1)) * intrinsicVolume d S =
          intrinsicVolume (d + 1) (coordinateCone S h) :=
        (intrinsicVolume_coordinateCone hh hcone).symm
      _ = intrinsicVolume (d + 1) (f '' coordinateCone S h) := by
        symm
        exact hf.euclideanHausdorffMeasure_image (coordinateCone S h)
      _ ≤ intrinsicVolume (d + 1) B := measure_mono himagesub
  have hdpos : (0 : ℝ) < d + 1 := by positivity
  rw [ENNReal.ofReal_div_of_pos hdpos] at hbcoef
  have hdreal : ENNReal.ofReal ((d : ℝ) + 1) = (d + 1 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_add (Nat.cast_nonneg d) zero_le_one]
    simp
  rw [hdreal] at hbcoef
  have hd0 : (d + 1 : ℝ≥0∞) ≠ 0 := by norm_num
  have hdtop : (d + 1 : ℝ≥0∞) ≠ ∞ := by finiteness
  have hb' :
      (ENNReal.ofReal h * intrinsicVolume d S) / (d + 1 : ℝ≥0∞) ≤
        intrinsicVolume (d + 1) B := by
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hbcoef
  have hcross := (ENNReal.div_le_iff hd0 hdtop).mp hb'
  simpa only [mul_comm] using hcross

/-- Origin-centered specialization: the apex premise is supplied directly
by an ambient inball.  This is the sharp one-step interface tailored to
the convex bodies occurring in Bilu's Section 8. -/
theorem origin_centered_isometric_section_step {d : ℕ} {X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X]
    {S : Set (EuclideanSpace ℝ (Fin d))} {ρ : ℝ} {B : Set X}
    (g : ConeProduct d →ₗᵢ[ℝ] X)
    (hρ : 0 < ρ) (hcone : MeasurableSet (rawCoordinateCone S ρ))
    (hconv : Convex ℝ B)
    (hbase : ∀ x ∈ S, g (conePair 0 x) ∈ B)
    (hball : Metric.closedBall (0 : X) ρ ⊆ B) :
    ENNReal.ofReal ρ * intrinsicVolume d S ≤
      (d + 1 : ℝ≥0∞) * intrinsicVolume (d + 1) B := by
  apply isometric_coordinate_cone_section_bound_crossmultiplied
    g 0 hρ hcone hconv
  · simpa using hbase
  · simp only [zero_add]
    apply hball
    rw [Metric.mem_closedBall, dist_zero_right, g.norm_map]
    simp [conePair, abs_of_pos hρ]

/-- Measurable-base form of `origin_centered_isometric_section_step`;
the raw-cone measurability condition is discharged internally. -/
theorem origin_centered_isometric_section_step_of_measurable
    {d : ℕ} {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X]
    {S : Set (EuclideanSpace ℝ (Fin d))} {ρ : ℝ} {B : Set X}
    (g : ConeProduct d →ₗᵢ[ℝ] X)
    (hρ : 0 < ρ) (hS : MeasurableSet S)
    (hconv : Convex ℝ B)
    (hbase : ∀ x ∈ S, g (conePair 0 x) ∈ B)
    (hball : Metric.closedBall (0 : X) ρ ⊆ B) :
    ENNReal.ofReal ρ * intrinsicVolume d S ≤
      (d + 1 : ℝ≥0∞) * intrinsicVolume (d + 1) B :=
  origin_centered_isometric_section_step g hρ
    (measurableSet_rawCoordinateCone hS hρ) hconv hbase hball

/-! ## Iterating the sharp cone step -/

/-- Geometric data for an iterated chain of sharp cone extensions.  At
stage `i`, an isometric copy of the cone over `S i`, of height `ρ`, lies in
the next convex set `S (i+1)`.  This packages geometry, not a volume
inequality. -/
def CoordinateConeChain (d k : ℕ) (ρ : ℝ)
    (S : (i : ℕ) → Set (EuclideanSpace ℝ (Fin (d + i)))) : Prop :=
  0 < ρ ∧
    ∀ i, i < k →
      ∃ (g : ConeProduct (d + i) →ₗᵢ[ℝ]
          EuclideanSpace ℝ (Fin (d + (i + 1))))
        (c : EuclideanSpace ℝ (Fin (d + (i + 1)))),
        MeasurableSet (rawCoordinateCone (S i) ρ) ∧
        Convex ℝ (S (i + 1)) ∧
        (∀ x ∈ S i, c + g (conePair 0 x) ∈ S (i + 1)) ∧
        c + g (conePair ρ 0) ∈ S (i + 1)

/-- Origin-centered form of the cone-chain data.  Each next-dimensional
section contains the radius-`ρ` ball in its own orthonormal coordinates,
so the needed apex is automatic. -/
def OriginCenteredConeChain (d k : ℕ) (ρ : ℝ)
    (S : (i : ℕ) → Set (EuclideanSpace ℝ (Fin (d + i)))) : Prop :=
  0 < ρ ∧
    ∀ i, i < k →
      ∃ (g : ConeProduct (d + i) →ₗᵢ[ℝ]
          EuclideanSpace ℝ (Fin (d + (i + 1)))),
        MeasurableSet (rawCoordinateCone (S i) ρ) ∧
        Convex ℝ (S (i + 1)) ∧
        (∀ x ∈ S i, g (conePair 0 x) ∈ S (i + 1)) ∧
        Metric.closedBall
            (0 : EuclideanSpace ℝ (Fin (d + (i + 1)))) ρ ⊆ S (i + 1)

/-- An origin-centered flag supplies the more general translated cone
chain. -/
theorem originCenteredConeChain_to_coordinateConeChain {d k : ℕ} {ρ : ℝ}
    {S : (i : ℕ) → Set (EuclideanSpace ℝ (Fin (d + i)))}
    (hchain : OriginCenteredConeChain d k ρ S) :
    CoordinateConeChain d k ρ S := by
  refine ⟨hchain.1, ?_⟩
  intro i hi
  rcases hchain.2 i hi with ⟨g, hmeas, hconv, hbase, hball⟩
  refine ⟨g, 0, hmeas, hconv, ?_, ?_⟩
  · intro x hx
    simpa using hbase x hx
  · simp only [zero_add]
    apply hball
    rw [Metric.mem_closedBall, dist_zero_right, g.norm_map]
    simp [conePair, abs_of_pos hchain.1]

/-- Pure ordered-semiring bookkeeping for the factorial accumulated by
successive codimension-one cone bounds. -/
private theorem factorial_bound_of_steps (d k : ℕ) (r : ℝ≥0∞)
    (V : ℕ → ℝ≥0∞)
    (hstep : ∀ i, i < k → r * V i ≤ (d + i + 1 : ℝ≥0∞) * V (i + 1)) :
    (d.factorial : ℝ≥0∞) * r ^ k * V 0 ≤
      ((d + k).factorial : ℝ≥0∞) * V k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hprev := ih (fun i hi ↦ hstep i (hi.trans (Nat.lt_succ_self k)))
      have hlast := hstep k (Nat.lt_succ_self k)
      calc
        (d.factorial : ℝ≥0∞) * r ^ (k + 1) * V 0 =
            r * ((d.factorial : ℝ≥0∞) * r ^ k * V 0) := by
          rw [pow_succ]
          ac_rfl
        _ ≤ r * (((d + k).factorial : ℝ≥0∞) * V k) :=
          mul_le_mul_right hprev r
        _ = ((d + k).factorial : ℝ≥0∞) * (r * V k) := by ac_rfl
        _ ≤ ((d + k).factorial : ℝ≥0∞) *
            ((d + k + 1 : ℝ≥0∞) * V (k + 1)) :=
          mul_le_mul_right hlast ((d + k).factorial : ℝ≥0∞)
        _ = ((d + (k + 1)).factorial : ℝ≥0∞) * V (k + 1) := by
          rw [show d + (k + 1) = (d + k) + 1 by omega,
            Nat.factorial_succ, Nat.cast_mul]
          simp only [Nat.cast_add, Nat.cast_one]
          ac_rfl

/-- Exact factorial estimate obtained by iterating actual isometric cone
extensions.  This realizes the induction and the sharp constant in Bilu's
Lemma 6.5 for any section chain that has been put in orthonormal
coordinates. -/
theorem coordinate_cone_chain_factorial_bound {d k : ℕ} {ρ : ℝ}
    {S : (i : ℕ) → Set (EuclideanSpace ℝ (Fin (d + i)))}
    (hchain : CoordinateConeChain d k ρ S) :
    ((d.factorial : ℝ≥0∞) * ENNReal.ofReal (ρ ^ k)) *
        intrinsicVolume d (S 0) ≤
      ((d + k).factorial : ℝ≥0∞) * intrinsicVolume (d + k) (S k) := by
  let V : ℕ → ℝ≥0∞ := fun i ↦ intrinsicVolume (d + i) (S i)
  have hstep : ∀ i, i < k →
      ENNReal.ofReal ρ * V i ≤ (d + i + 1 : ℝ≥0∞) * V (i + 1) := by
    intro i hi
    rcases hchain.2 i hi with ⟨g, c, hmeas, hconv, hbase, hapex⟩
    simpa only [V, Nat.add_zero, Nat.add_assoc, Nat.cast_add, Nat.cast_one] using
      (isometric_coordinate_cone_section_bound_crossmultiplied
        g c hchain.1 hmeas hconv hbase hapex)
  have h := factorial_bound_of_steps d k (ENNReal.ofReal ρ) V hstep
  rw [← ENNReal.ofReal_pow hchain.1.le] at h
  simpa only [V, Nat.add_zero, mul_assoc] using h

/-- Sharp factorial bound for an origin-centered orthonormal section
flag.  This is the direct all-codimensions corollary used when the inball
is centered at the origin. -/
theorem origin_centered_cone_chain_factorial_bound {d k : ℕ} {ρ : ℝ}
    {S : (i : ℕ) → Set (EuclideanSpace ℝ (Fin (d + i)))}
    (hchain : OriginCenteredConeChain d k ρ S) :
    ((d.factorial : ℝ≥0∞) * ENNReal.ofReal (ρ ^ k)) *
        intrinsicVolume d (S 0) ≤
      ((d + k).factorial : ℝ≥0∞) * intrinsicVolume (d + k) (S k) :=
  coordinate_cone_chain_factorial_bound
    (originCenteredConeChain_to_coordinateConeChain hchain)

/-- Ambient-space endpoint form of the origin-centered flag estimate.
The final coordinate body need only embed isometrically into the ambient
body; no volume comparison is assumed. -/
theorem origin_centered_cone_chain_bound_in_ambient
    {d k : ℕ} {ρ : ℝ}
    {S : (i : ℕ) → Set (EuclideanSpace ℝ (Fin (d + i)))}
    (hchain : OriginCenteredConeChain d k ρ S)
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X]
    (f : EuclideanSpace ℝ (Fin (d + k)) →ₗᵢ[ℝ] X) {B : Set X}
    (hfinal : f '' S k ⊆ B) :
    ((d.factorial : ℝ≥0∞) * ENNReal.ofReal (ρ ^ k)) *
        intrinsicVolume d (S 0) ≤
      ((d + k).factorial : ℝ≥0∞) * intrinsicVolume (d + k) B := by
  calc
    ((d.factorial : ℝ≥0∞) * ENNReal.ofReal (ρ ^ k)) *
          intrinsicVolume d (S 0) ≤
        ((d + k).factorial : ℝ≥0∞) * intrinsicVolume (d + k) (S k) :=
      origin_centered_cone_chain_factorial_bound hchain
    _ = ((d + k).factorial : ℝ≥0∞) *
          intrinsicVolume (d + k) (f '' S k) := by
      simp only [intrinsicVolume]
      rw [f.isometry.euclideanHausdorffMeasure_image]
    _ ≤ ((d + k).factorial : ℝ≥0∞) * intrinsicVolume (d + k) B :=
      mul_le_mul_right (measure_mono hfinal) ((d + k).factorial : ℝ≥0∞)

/-- Origin-centered linear-section estimate from a nested orthonormal
coordinate flag.  The sets in the cone chain are constructed internally
as pullbacks of `B`; compatibility says that each coordinate embedding
extends the preceding one. -/
theorem origin_centered_linear_section_bound_of_isometric_flag
    {d k : ℕ} {ρ : ℝ} {X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X]
    {B : Set X} (hρ : 0 < ρ) (hB : MeasurableSet B)
    (hconv : Convex ℝ B) (hball : Metric.closedBall (0 : X) ρ ⊆ B)
    (f : (i : ℕ) → i ≤ k →
      EuclideanSpace ℝ (Fin (d + i)) →ₗᵢ[ℝ] X)
    (g : (i : ℕ) → i < k → ConeProduct (d + i) →ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (d + (i + 1))))
    (hcompat : ∀ i (hi : i < k) x,
      f (i + 1) (Nat.succ_le_of_lt hi) (g i hi (conePair 0 x)) =
        f i hi.le x) :
    ((d.factorial : ℝ≥0∞) * ENNReal.ofReal (ρ ^ k)) *
        intrinsicVolume d (f 0 (Nat.zero_le k) ⁻¹' B) ≤
      ((d + k).factorial : ℝ≥0∞) * intrinsicVolume (d + k) B := by
  let S : (i : ℕ) → Set (EuclideanSpace ℝ (Fin (d + i))) :=
    fun i ↦ if hi : i ≤ k then f i hi ⁻¹' B else ∅
  have hchain : OriginCenteredConeChain d k ρ S := by
    refine ⟨hρ, ?_⟩
    intro i hi
    have hSi : S i = f i hi.le ⁻¹' B := by
      simp only [S, dif_pos hi.le]
    have hSsucc : S (i + 1) =
        f (i + 1) (Nat.succ_le_of_lt hi) ⁻¹' B := by
      simp only [S, dif_pos (Nat.succ_le_of_lt hi)]
    refine ⟨g i hi, measurableSet_rawCoordinateCone
      (hSi ▸ hB.preimage (f i hi.le).continuous.measurable) hρ, ?_, ?_, ?_⟩
    · intro x hx y hy a b ha hb hab
      rw [hSsucc]
      change f (i + 1) (Nat.succ_le_of_lt hi) (a • x + b • y) ∈ B
      have hx' : f (i + 1) (Nat.succ_le_of_lt hi) x ∈ B := by
        rw [hSsucc] at hx
        exact hx
      have hy' : f (i + 1) (Nat.succ_le_of_lt hi) y ∈ B := by
        rw [hSsucc] at hy
        exact hy
      simpa only [map_add, map_smul] using
        hconv hx' hy' ha hb hab
    · intro x hx
      rw [hSsucc]
      change f (i + 1) (Nat.succ_le_of_lt hi) (g i hi (conePair 0 x)) ∈ B
      rw [hcompat i hi x]
      rw [hSi] at hx
      exact hx
    · intro z hz
      rw [hSsucc]
      change f (i + 1) (Nat.succ_le_of_lt hi) z ∈ B
      apply hball
      simpa [Metric.mem_closedBall,
        (f (i + 1) (Nat.succ_le_of_lt hi)).norm_map] using hz
  have hfinal : f k le_rfl '' S k ⊆ B := by
    rintro _ ⟨x, hx, rfl⟩
    have hSk : S k = f k le_rfl ⁻¹' B := by
      simp only [S, dif_pos le_rfl]
    rw [hSk] at hx
    exact hx
  simpa only [S, dif_pos (Nat.zero_le k)] using
    (origin_centered_cone_chain_bound_in_ambient hchain (f k le_rfl) hfinal)

/-! ## An unconditional product-thickening estimate -/

/-- The Hilbert direct sum of two coordinate Euclidean spaces.  The
`WithLp 2` wrapper is important: the ordinary product carries the max norm,
whereas this type carries the orthogonal-product inner product. -/
abbrev OrthogonalProduct (d k : ℕ) :=
  WithLp 2 (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin k))

/-- Put a pair of coordinate vectors into their Hilbert direct sum. -/
def orthogonalPair {d k : ℕ}
    (x : EuclideanSpace ℝ (Fin d)) (y : EuclideanSpace ℝ (Fin k)) :
    OrthogonalProduct d k :=
  WithLp.toLp 2 (x, y)

/-- Uncurried version of `orthogonalPair`. -/
def orthogonalPairMap {d k : ℕ} :
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin k)) →
      OrthogonalProduct d k :=
  fun p ↦ orthogonalPair p.1 p.2

/-- Central fibre in the first factor of an orthogonal product. -/
def centralFiber {l m : ℕ} (B : Set (OrthogonalProduct l m)) :
    Set (EuclideanSpace ℝ (Fin l)) :=
  {x | orthogonalPair x 0 ∈ B}

/-- Projection of a set in an orthogonal product to its second factor. -/
def secondProjection {l m : ℕ} (B : Set (OrthogonalProduct l m)) :
    Set (EuclideanSpace ℝ (Fin m)) :=
  {y | ∃ x, orthogonalPair x y ∈ B}

/-- Fibre over a point of the second projection. -/
def firstFiber {l m : ℕ} (B : Set (OrthogonalProduct l m))
    (y : EuclideanSpace ℝ (Fin m)) : Set (EuclideanSpace ℝ (Fin l)) :=
  {x | orthogonalPair x y ∈ B}

/-- A linear projection of a convex set is convex.  This elementary
coordinate form is used by the gauge argument below. -/
theorem convex_secondProjection {l m : ℕ} {B : Set (OrthogonalProduct l m)}
    (hconv : Convex ℝ B) : Convex ℝ (secondProjection B) := by
  rintro y₁ ⟨x₁, hx₁⟩ y₂ ⟨x₂, hx₂⟩ a b ha hb hab
  refine ⟨a • x₁ + b • x₂, ?_⟩
  have h := hconv hx₁ hx₂ ha hb hab
  change orthogonalPair (a • x₁ + b • x₂) (a • y₁ + b • y₂) ∈ B
  convert h using 1
  apply (MeasurableEquiv.toLp 2
    (EuclideanSpace ℝ (Fin l) × EuclideanSpace ℝ (Fin m))).symm.injective
  rfl

/-- Convexity gives the sharp radial lower bound for fibres: above `t y`
the fibre contains a translate of `(1-t)` times the central fibre.
This is the geometric input for Bilu's radial proof of (6.7). -/
theorem radial_firstFiber_volume_lower_bound {l m : ℕ}
    {B : Set (OrthogonalProduct l m)} (hconv : Convex ℝ B)
    {y : EuclideanSpace ℝ (Fin m)} (hy : y ∈ secondProjection B)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (‖1 - t‖₊ ^ l) • intrinsicVolume l (centralFiber B) ≤
      intrinsicVolume l (firstFiber B (t • y)) := by
  rcases hy with ⟨b, hb⟩
  let T : Set (EuclideanSpace ℝ (Fin l)) :=
    (fun x ↦ x + t • b) '' ((1 - t) • centralFiber B)
  have hTsub : T ⊆ firstFiber B (t • y) := by
    rintro z ⟨u, ⟨x, hx, hux⟩, rfl⟩
    have hz := hconv hx hb (sub_nonneg.mpr ht1.le) ht0 (by ring)
    change orthogonalPair (u + t • b) (t • y) ∈ B
    convert hz using 1
    apply (MeasurableEquiv.toLp 2
      (EuclideanSpace ℝ (Fin l) × EuclideanSpace ℝ (Fin m))).symm.injective
    apply Prod.ext
    · change u + t • b = (1 - t) • x + t • b
      rw [← hux]
    · change t • y = (1 - t) • 0 + t • y
      simp
  have htranslate :
      intrinsicVolume l T = intrinsicVolume l ((1 - t) • centralFiber B) := by
    unfold T intrinsicVolume
    exact (IsometryEquiv.addRight (t • b)).isometry.euclideanHausdorffMeasure_image _
  calc
    (‖1 - t‖₊ ^ l) • intrinsicVolume l (centralFiber B) =
        intrinsicVolume l ((1 - t) • centralFiber B) := by
      symm
      unfold intrinsicVolume
      exact Measure.euclideanHausdorffMeasure_smul₀ l
        (sub_ne_zero.mpr (ne_of_gt ht1)) (centralFiber B)
    _ = intrinsicVolume l T := htranslate.symm
    _ ≤ intrinsicVolume l (firstFiber B (t • y)) := measure_mono hTsub

/-- Fubini identity for the first-coordinate fibres of a measurable set
in an orthogonal product. -/
theorem intrinsicVolume_eq_lintegral_firstFiber {l m : ℕ}
    {B : Set (OrthogonalProduct l m)} (hB : MeasurableSet B) :
    intrinsicVolume (l + m) B =
      ∫⁻ y : EuclideanSpace ℝ (Fin m), intrinsicVolume l (firstFiber B y) := by
  simp only [intrinsicVolume]
  have hrank : finrank ℝ (OrthogonalProduct l m) = l + m := by
    calc
      finrank ℝ (OrthogonalProduct l m) =
          finrank ℝ (EuclideanSpace ℝ (Fin l) × EuclideanSpace ℝ (Fin m)) :=
        (WithLp.linearEquiv 2 ℝ
          (EuclideanSpace ℝ (Fin l) × EuclideanSpace ℝ (Fin m))).finrank_eq
      _ = l + m := by simp
  rw [show (μHE[l + m] : Measure (OrthogonalProduct l m)) = volume by
        rw [← hrank]
        exact InnerProductSpace.euclideanHausdorffMeasure_eq_volume,
    show (μHE[l] : Measure (EuclideanSpace ℝ (Fin l))) = volume by
      simpa using
        (InnerProductSpace.euclideanHausdorffMeasure_eq_volume
          (V := EuclideanSpace ℝ (Fin l)))]
  let e :
      (EuclideanSpace ℝ (Fin l) × EuclideanSpace ℝ (Fin m)) ≃ᵐ
        OrthogonalProduct l m := MeasurableEquiv.toLp 2 _
  have he : MeasurePreserving e := WithLp.volume_preserving_toLp _ _
  have hraw : MeasurableSet (e ⁻¹' B) := hB.preimage e.measurable
  calc
    volume B = volume (e ⁻¹' B) :=
      (he.measure_preimage hB.nullMeasurableSet).symm
    _ = (volume.prod volume) (e ⁻¹' B) := by
      rw [← Measure.volume_eq_prod]
    _ = ∫⁻ y : EuclideanSpace ℝ (Fin m),
          volume ((fun x ↦ (x, y)) ⁻¹' (e ⁻¹' B)) :=
      Measure.prod_apply_symm hraw
    _ = ∫⁻ y : EuclideanSpace ℝ (Fin m), volume (firstFiber B y) := by
      apply lintegral_congr
      intro y
      congr 1

/-- Pointwise gauge form of the radial fibre estimate.  Closedness is
needed only to put the normalized boundary point back in the projection;
boundedness makes the gauge nondegenerate. -/
theorem gauge_firstFiber_volume_lower_bound {l m : ℕ} (hl : 0 < l)
    {B : Set (OrthogonalProduct l m)} (hconv : Convex ℝ B)
    (hPnhds : secondProjection B ∈ 𝓝 0)
    (hPclosed : IsClosed (secondProjection B))
    (hPbounded : Bornology.IsVonNBounded ℝ (secondProjection B))
    {z : EuclideanSpace ℝ (Fin m)} (hz : z ∈ secondProjection B) :
    (‖1 - gauge (secondProjection B) z‖₊ ^ l) •
        intrinsicVolume l (centralFiber B) ≤
      intrinsicVolume l (firstFiber B z) := by
  let P := secondProjection B
  let q := gauge P z
  have hPconv : Convex ℝ P := convex_secondProjection hconv
  have hq0 : 0 ≤ q := gauge_nonneg _
  have hq1 : q ≤ 1 := gauge_le_one_of_mem hz
  rcases hq0.eq_or_lt with hq | hqpos
  · have hz0 : z = 0 :=
      (gauge_eq_zero (absorbent_nhds_zero hPnhds) hPbounded).mp hq.symm
    subst z
    simp [q, P, centralFiber, firstFiber]
  rcases hq1.eq_or_lt with hq | hqlt
  · change (‖1 - q‖₊ ^ l) • intrinsicVolume l (centralFiber B) ≤ _
    simp [hq, Nat.ne_of_gt hl]
  · let y : EuclideanSpace ℝ (Fin m) := q⁻¹ • z
    have hgy : gauge P y = 1 := by
      dsimp only [y]
      rw [gauge_smul_of_nonneg (inv_nonneg.mpr hq0)]
      simp [q, hqpos.ne']
    have hy_closure : y ∈ closure P :=
      (gauge_le_one_iff_mem_closure hPconv hPnhds).mp hgy.le
    have hy : y ∈ P := by
      rwa [hPclosed.closure_eq] at hy_closure
    have hqsmul : q • y = z := by
      simp [y, hqpos.ne']
    have hradial := radial_firstFiber_volume_lower_bound hconv hy hq0 hqlt
    rw [hqsmul] at hradial
    simpa [q, P] using hradial

/-- Integrating the pointwise gauge estimate.  The final premise is the
beta-integral identity for the gauge of the projected convex body. -/
theorem coordinate_projection_central_section_beta_bound {l m : ℕ}
    (hl : 0 < l) {B : Set (OrthogonalProduct l m)}
    (hconv : Convex ℝ B) (hB : MeasurableSet B)
    (hPnhds : secondProjection B ∈ 𝓝 0)
    (hPclosed : IsClosed (secondProjection B))
    (hPbounded : Bornology.IsVonNBounded ℝ (secondProjection B))
    (hbeta :
      (∫⁻ y in secondProjection B,
          ENNReal.ofReal ((1 - gauge (secondProjection B) y) ^ l)) =
        ENNReal.ofReal
            (((m.factorial : ℝ) * l.factorial) / (m + l).factorial) *
          intrinsicVolume m (secondProjection B)) :
    (ENNReal.ofReal
          (((m.factorial : ℝ) * l.factorial) / (m + l).factorial) *
        intrinsicVolume m (secondProjection B)) *
          intrinsicVolume l (centralFiber B) ≤
      intrinsicVolume (l + m) B := by
  let D := secondProjection B
  let C := intrinsicVolume l (centralFiber B)
  let w : EuclideanSpace ℝ (Fin m) → ℝ≥0∞ := fun y ↦
    ENNReal.ofReal ((1 - gauge D y) ^ l)
  have hpoint : ∀ y ∈ D,
      w y * C ≤ intrinsicVolume l (firstFiber B y) := by
    intro y hy
    have hg := gauge_firstFiber_volume_lower_bound hl hconv hPnhds hPclosed hPbounded hy
    have hnonneg : 0 ≤ 1 - gauge D y :=
      sub_nonneg.mpr (gauge_le_one_of_mem hy)
    simpa only [w, D, C, Real.nnnorm_of_nonneg hnonneg,
      ENNReal.coe_pow, ENNReal.ofReal_pow hnonneg, ENNReal.ofReal_eq_coe_nnreal hnonneg,
      ENNReal.smul_def, smul_eq_mul] using hg
  calc
    (ENNReal.ofReal
          (((m.factorial : ℝ) * l.factorial) / (m + l).factorial) *
        intrinsicVolume m (secondProjection B)) *
          intrinsicVolume l (centralFiber B) =
        (∫⁻ y in D, w y) * C := by rw [hbeta]
    _ ≤ ∫⁻ y in D, w y * C := lintegral_mul_const_le C w
    _ ≤ ∫⁻ y in D, intrinsicVolume l (firstFiber B y) :=
      setLIntegral_mono' hPclosed.measurableSet hpoint
    _ ≤ ∫⁻ y, intrinsicVolume l (firstFiber B y) :=
      setLIntegral_le_lintegral D _
    _ = intrinsicVolume (l + m) B :=
      (intrinsicVolume_eq_lintegral_firstFiber hB).symm

/-- The beta coefficient is the reciprocal binomial coefficient, so the
integrated gauge bound is precisely Bilu's inequality (6.7) in orthogonal
coordinates. -/
theorem coordinate_projection_central_section_bound_of_beta {l m : ℕ}
    (hl : 0 < l) {B : Set (OrthogonalProduct l m)}
    (hconv : Convex ℝ B) (hB : MeasurableSet B)
    (hPnhds : secondProjection B ∈ 𝓝 0)
    (hPclosed : IsClosed (secondProjection B))
    (hPbounded : Bornology.IsVonNBounded ℝ (secondProjection B))
    (hbeta :
      (∫⁻ y in secondProjection B,
          ENNReal.ofReal ((1 - gauge (secondProjection B) y) ^ l)) =
        ENNReal.ofReal
            (((m.factorial : ℝ) * l.factorial) / (m + l).factorial) *
          intrinsicVolume m (secondProjection B)) :
    intrinsicVolume m (secondProjection B) *
        intrinsicVolume l (centralFiber B) ≤
      ((m + l).choose l : ℝ≥0∞) * intrinsicVolume (l + m) B := by
  have hratio_nonneg :
      0 ≤ ((m.factorial : ℝ) * l.factorial) / (m + l).factorial := by
    positivity
  have hchoose :
      (((m + l).choose l : ℕ) : ℝ) =
        (m + l).factorial / (l.factorial * m.factorial) := by
    simpa using Nat.cast_choose ℝ (Nat.le_add_left l m)
  have hscalar_real :
      (((m + l).choose l : ℕ) : ℝ) *
          (((m.factorial : ℝ) * l.factorial) / (m + l).factorial) = 1 := by
    rw [hchoose]
    field_simp
  have hscalar :
      ((m + l).choose l : ℝ≥0∞) *
          ENNReal.ofReal
            (((m.factorial : ℝ) * l.factorial) / (m + l).factorial) = 1 := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      hscalar_real, ENNReal.ofReal_one]
  have hb := coordinate_projection_central_section_beta_bound hl hconv hB
    hPnhds hPclosed hPbounded hbeta
  calc
    intrinsicVolume m (secondProjection B) *
          intrinsicVolume l (centralFiber B) =
        1 * (intrinsicVolume m (secondProjection B) *
          intrinsicVolume l (centralFiber B)) := by rw [one_mul]
    _ = (((m + l).choose l : ℝ≥0∞) *
          ENNReal.ofReal
            (((m.factorial : ℝ) * l.factorial) / (m + l).factorial)) *
          (intrinsicVolume m (secondProjection B) *
            intrinsicVolume l (centralFiber B)) := by rw [hscalar]
    _ = ((m + l).choose l : ℝ≥0∞) *
          ((ENNReal.ofReal
              (((m.factorial : ℝ) * l.factorial) / (m + l).factorial) *
            intrinsicVolume m (secondProjection B)) *
              intrinsicVolume l (centralFiber B)) := by ac_rfl
    _ ≤ ((m + l).choose l : ℝ≥0∞) * intrinsicVolume (l + m) B :=
      mul_le_mul_right hb _

/-- Bilu's sharp projection/central-section inequality (6.7) for the
orthogonal coordinate decomposition `ℝ^l ⊕ ℝ^m`.  Unlike the later
abstract interface, this result is unconditional. -/
theorem coordinate_projection_central_section_bound {l m : ℕ}
    (hl : 0 < l) {B : Set (OrthogonalProduct l m)}
    (hconv : Convex ℝ B) (hB : MeasurableSet B)
    (hPnhds : secondProjection B ∈ 𝓝 0)
    (hPclosed : IsClosed (secondProjection B))
    (hPbounded : Bornology.IsVonNBounded ℝ (secondProjection B)) :
    intrinsicVolume m (secondProjection B) *
        intrinsicVolume l (centralFiber B) ≤
      ((m + l).choose l : ℝ≥0∞) * intrinsicVolume (l + m) B := by
  have hPconv : Convex ℝ (secondProjection B) := convex_secondProjection hconv
  have hvol :
      intrinsicVolume m (secondProjection B) = volume (secondProjection B) := by
    unfold intrinsicVolume
    have hm :
        (μHE[m] : Measure (EuclideanSpace ℝ (Fin m))) = volume := by
      simpa using
        (InnerProductSpace.euclideanHausdorffMeasure_eq_volume
          (V := EuclideanSpace ℝ (Fin m)))
    rw [hm]
  have hbeta :=
    GaugeRadialIntegral.lintegral_one_sub_gauge_pow
      (secondProjection B) hPconv hPclosed hPnhds (l := l)
  rw [← hvol] at hbeta
  exact coordinate_projection_central_section_bound_of_beta hl hconv hB
    hPnhds hPclosed hPbounded hbeta

/-- Euclidean Hausdorff volume is multiplicative on products of measurable
sets when the dimensions match the two Euclidean factors. -/
theorem intrinsicVolume_prod {d k : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin d))}
    {T : Set (EuclideanSpace ℝ (Fin k))}
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    intrinsicVolume (d + k)
        (orthogonalPairMap '' (S ×ˢ T)) =
      intrinsicVolume d S * intrinsicVolume k T := by
  simp only [intrinsicVolume]
  have hrank : finrank ℝ (OrthogonalProduct d k) = d + k := by
    calc
      finrank ℝ (OrthogonalProduct d k) =
          finrank ℝ (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin k)) :=
        (WithLp.linearEquiv 2 ℝ
          (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin k))).finrank_eq
      _ = d + k := by simp
  rw [show (μHE[d + k] : Measure (OrthogonalProduct d k)) = volume by
        rw [← hrank]
        exact
          (InnerProductSpace.euclideanHausdorffMeasure_eq_volume
            (V := OrthogonalProduct d k)),
    show (μHE[d] : Measure (EuclideanSpace ℝ (Fin d))) = volume by
      simpa using
        (InnerProductSpace.euclideanHausdorffMeasure_eq_volume
          (V := EuclideanSpace ℝ (Fin d))),
    show (μHE[k] : Measure (EuclideanSpace ℝ (Fin k))) = volume by
      simpa using
        (InnerProductSpace.euclideanHausdorffMeasure_eq_volume
          (V := EuclideanSpace ℝ (Fin k)))]
  let e :
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin k)) ≃ᵐ
        OrthogonalProduct d k := MeasurableEquiv.toLp 2 _
  have he : MeasurePreserving e := WithLp.volume_preserving_toLp _ _
  have himage : e '' (S ×ˢ T) = e.symm ⁻¹' (S ×ˢ T) := by
    ext z
    constructor
    · rintro ⟨q, hq, rfl⟩
      simpa using hq
    · intro hz
      exact ⟨e.symm z, hz, e.apply_symm_apply z⟩
  rw [show orthogonalPairMap = e from rfl, himage,
    he.symm.measure_preimage_equiv, Measure.volume_eq_prod,
    Measure.prod_prod]

/-- A completely formalized coarse form of the geometric core of Bilu
Lemma 6.5.  If a convex set contains a `d`-dimensional base and a
`k`-dimensional transverse set, then it contains the half-scaled Cartesian
product.  Hence its ambient volume is at least `2^{-(d+k)}` times the
product of the two intrinsic volumes.

Unlike `Lemma65Statement`, this theorem is unconditional.  It is often
enough in applications where only a dimension-dependent constant matters.
-/
theorem midpoint_product_volume_le {d k : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin d))}
    {T : Set (EuclideanSpace ℝ (Fin k))}
    {B : Set (OrthogonalProduct d k)}
    (hSmeas : MeasurableSet S) (hTmeas : MeasurableSet T)
    (hconv : Convex ℝ B)
    (hbase : ∀ x ∈ S, orthogonalPair x 0 ∈ B)
    (htransverse : ∀ y ∈ T, orthogonalPair 0 y ∈ B) :
    (‖(2 : ℝ)⁻¹‖₊ ^ (d + k)) •
        (intrinsicVolume d S * intrinsicVolume k T) ≤
      intrinsicVolume (d + k) B := by
  have hsubset :
      (2 : ℝ)⁻¹ • (orthogonalPairMap '' (S ×ˢ T)) ⊆ B := by
    rintro z ⟨p, hp, rfl⟩
    rcases hp with ⟨q, ⟨hx, hy⟩, rfl⟩
    have hz := hconv (hbase q.1 hx) (htransverse q.2 hy)
      (show 0 ≤ (2 : ℝ)⁻¹ by positivity)
      (show 0 ≤ (2 : ℝ)⁻¹ by positivity)
      (show (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1 by norm_num)
    have heq :
        (2 : ℝ)⁻¹ • orthogonalPairMap q =
          (2 : ℝ)⁻¹ • orthogonalPair q.1 0 +
            (2 : ℝ)⁻¹ • orthogonalPair 0 q.2 := by
      apply (MeasurableEquiv.toLp 2 _).symm.injective
      simp [orthogonalPairMap, orthogonalPair]
      rfl
    change (2 : ℝ)⁻¹ • orthogonalPairMap q ∈ B
    rw [heq]
    exact hz
  calc
    (‖(2 : ℝ)⁻¹‖₊ ^ (d + k)) •
          (intrinsicVolume d S * intrinsicVolume k T) =
        intrinsicVolume (d + k)
          ((2 : ℝ)⁻¹ • (orthogonalPairMap '' (S ×ˢ T))) := by
      symm
      rw [intrinsicVolume,
        Measure.euclideanHausdorffMeasure_smul₀ (d + k)
          (show (2 : ℝ)⁻¹ ≠ 0 by norm_num),
        ← intrinsicVolume_def,
        intrinsicVolume_prod hSmeas hTmeas]
    _ ≤ intrinsicVolume (d + k) B := measure_mono hsubset

/-- Coordinate normal form of the coarse section estimate.  A full
ambient ball supplies the transverse `k`-ball used by
`midpoint_product_volume_le`.  The constant is explicit (the usual
Euclidean unit-ball volume) and depends only on the dimensions.

This is weaker than Bilu's sharp factorial constant, but it has precisely
the qualitative strength used in his bounded-dimensional applications:
an inradius bounds every fixed-dimensional section by a
dimension-dependent multiple of the ambient volume. -/
theorem coarse_section_bound_coordinate {d k : ℕ} (hk : 0 < k)
    {S : Set (EuclideanSpace ℝ (Fin d))}
    {B : Set (OrthogonalProduct d k)}
    (ρ : ℝ) (hSmeas : MeasurableSet S)
    (hconv : Convex ℝ B)
    (hbase : ∀ x ∈ S, orthogonalPair x 0 ∈ B)
    (hball : Metric.closedBall (0 : OrthogonalProduct d k) ρ ⊆ B) :
    (‖(2 : ℝ)⁻¹‖₊ ^ (d + k)) •
        (intrinsicVolume d S *
          ((ENNReal.ofReal ρ) ^ k *
            ENNReal.ofReal
              (Real.sqrt Real.pi ^ k /
                Real.Gamma ((k : ℝ) / 2 + 1)))) ≤
      intrinsicVolume (d + k) B := by
  let : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  let T : Set (EuclideanSpace ℝ (Fin k)) := Metric.closedBall 0 ρ
  have hTmeas : MeasurableSet T := measurableSet_closedBall
  have htransverse : ∀ y ∈ T, orthogonalPair (d := d) 0 y ∈ B := by
    intro y hy
    apply hball
    change dist (orthogonalPair (d := d) 0 y) 0 ≤ ρ
    simpa [orthogonalPair, T, Metric.mem_closedBall] using hy
  have hmid := midpoint_product_volume_le
    (d := d) (k := k) (S := S) (T := T) (B := B)
    hSmeas hTmeas hconv hbase htransverse
  have hTvolume :
      intrinsicVolume k T =
        (ENNReal.ofReal ρ) ^ k *
          ENNReal.ofReal
            (Real.sqrt Real.pi ^ k /
              Real.Gamma ((k : ℝ) / 2 + 1)) := by
    rw [intrinsicVolume,
      show (μHE[k] : Measure (EuclideanSpace ℝ (Fin k))) = volume by
        simpa using
          (InnerProductSpace.euclideanHausdorffMeasure_eq_volume
            (V := EuclideanSpace ℝ (Fin k)))]
    change volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) ρ) = _
    rw [EuclideanSpace.volume_closedBall]
    simp [hk]
  rwa [hTvolume] at hmid

/-- An affine set has the dimension used to measure it.  Keeping this as a
separate predicate makes it impossible to silently measure a lower
dimensional set with ambient Lebesgue measure. -/
def HasAffineDimension {n : ℕ} (d : ℕ)
    (s : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  finrank ℝ (affineSpan ℝ s).direction = d

/-- Bilu's Lemma 6.5, in division-free form.

The ball is allowed to lie in `closure B`, exactly as in the source. -/
def Lemma65Statement : Prop :=
  ∀ (n d : ℕ) (B B₁ : Set (EuclideanSpace ℝ (Fin n)))
      (c : EuclideanSpace ℝ (Fin n)) (ρ : ℝ),
    d ≤ n →
    Convex ℝ B →
    MeasurableSet B₁ →
    B₁ ⊆ B →
    HasAffineDimension d B₁ →
    0 < ρ →
    Metric.closedBall c ρ ⊆ closure B →
      ((d.factorial : ℝ≥0∞) * ENNReal.ofReal (ρ ^ (n - d))) *
          intrinsicVolume d B₁ ≤
        (n.factorial : ℝ≥0∞) * intrinsicVolume n B

/-- The codimension-zero case of Lemma 6.5 is just monotonicity of
Hausdorff measure. -/
theorem lemma65_codimension_zero {n : ℕ}
    {B B₁ : Set (EuclideanSpace ℝ (Fin n))} (hsub : B₁ ⊆ B) :
    ((n.factorial : ℝ≥0∞) * ENNReal.ofReal ((1 : ℝ) ^ (n - n))) *
          intrinsicVolume n B₁ ≤
        (n.factorial : ℝ≥0∞) * intrinsicVolume n B := by
  simpa [intrinsicVolume] using
    mul_le_mul_right (measure_mono hsub) (n.factorial : ℝ≥0∞)

/-- Bilu's general projection/central-section inequality (6.7).  Here `L`
has dimension `l`, its orthogonal complement has dimension `m`, and the
ambient dimension is `n`. -/
def Lemma67Statement : Prop :=
  ∀ (n l m : ℕ) (B : Set (EuclideanSpace ℝ (Fin n)))
      (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))),
    l + m = n →
    finrank ℝ L = l →
    finrank ℝ Lᗮ = m →
    Convex ℝ B →
    (-B : Set (EuclideanSpace ℝ (Fin n))) = B →
    MeasurableSet B →
      intrinsicVolume m (Lᗮ.orthogonalProjectionOnto '' B) *
          intrinsicVolume l (B ∩ (L : Set (EuclideanSpace ℝ (Fin n)))) ≤
        (n.choose l : ℝ≥0∞) * intrinsicVolume n B

/-- Division-free form of Bilu's Lemma 6.6.  The seminorm `p` is the
Minkowski functional `‖·‖_B` in the application.

The displayed inequality is equivalent, when the denominators are
positive, to

`Vol_(n-1)(π B) ≤ (n/2) (p w / ‖w‖) Vol_n(B)`.
-/
def Lemma66Conclusion {n : ℕ} (B : Set (EuclideanSpace ℝ (Fin n)))
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin n)))
    (w : EuclideanSpace ℝ (Fin n)) : Prop :=
  (2 : ℝ≥0∞) * ENNReal.ofReal ‖w‖ *
      intrinsicVolume (n - 1) ((ℝ ∙ w)ᗮ.orthogonalProjectionOnto '' B) ≤
    (n : ℝ≥0∞) * ENNReal.ofReal (p w) * intrinsicVolume n B

/-- The elementary final step from (6.7) to Lemma 6.6.  `hsection` is the
one-dimensional identity

`Vol₁(B ∩ ℝw) = 2 ‖w‖ / ‖w‖_B`

in cross-multiplied form. -/
theorem lemma66_of_central_section_bound {n : ℕ}
    (B : Set (EuclideanSpace ℝ (Fin n)))
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin n)))
    (w : EuclideanSpace ℝ (Fin n))
    (hsection :
      (2 : ℝ≥0∞) * ENNReal.ofReal ‖w‖ ≤
        ENNReal.ofReal (p w) * intrinsicVolume 1
          (B ∩ ((ℝ ∙ w) : Set (EuclideanSpace ℝ (Fin n)))))
    (hprojection :
      intrinsicVolume (n - 1) ((ℝ ∙ w)ᗮ.orthogonalProjectionOnto '' B) *
          intrinsicVolume 1
            (B ∩ ((ℝ ∙ w) : Set (EuclideanSpace ℝ (Fin n)))) ≤
        (n : ℝ≥0∞) * intrinsicVolume n B) :
    Lemma66Conclusion B p w := by
  let P : ℝ≥0∞ :=
    intrinsicVolume (n - 1) ((ℝ ∙ w)ᗮ.orthogonalProjectionOnto '' B)
  let S : ℝ≥0∞ :=
    intrinsicVolume 1 (B ∩ ((ℝ ∙ w) : Set (EuclideanSpace ℝ (Fin n))))
  let q : ℝ≥0∞ := ENNReal.ofReal (p w)
  let a : ℝ≥0∞ := (2 : ℝ≥0∞) * ENNReal.ofReal ‖w‖
  let V : ℝ≥0∞ := intrinsicVolume n B
  change a * P ≤ (n : ℝ≥0∞) * q * V
  calc
    a * P ≤ (q * S) * P := mul_le_mul_left hsection P
    _ = q * (P * S) := by ac_rfl
    _ ≤ q * ((n : ℝ≥0∞) * V) := mul_le_mul_right hprojection q
    _ = (n : ℝ≥0∞) * q * V := by ac_rfl

/-- Specialization of (6.7) to the line generated by a nonzero vector.
This supplies the `hprojection` premise of
`lemma66_of_central_section_bound`. -/
theorem line_projection_bound_of_lemma67
    (h67 : Lemma67Statement) {n : ℕ} (hn : 0 < n)
    (B : Set (EuclideanSpace ℝ (Fin n)))
    (w : EuclideanSpace ℝ (Fin n)) (hw : w ≠ 0)
    (hconv : Convex ℝ B)
    (hsymm : (-B : Set (EuclideanSpace ℝ (Fin n))) = B)
    (hmeas : MeasurableSet B) :
    intrinsicVolume (n - 1) ((ℝ ∙ w)ᗮ.orthogonalProjectionOnto '' B) *
        intrinsicVolume 1
          (B ∩ ((ℝ ∙ w) : Set (EuclideanSpace ℝ (Fin n)))) ≤
      (n : ℝ≥0∞) * intrinsicVolume n B := by
  have hspan : finrank ℝ (ℝ ∙ w) = 1 := finrank_span_singleton hw
  have horth : finrank ℝ (ℝ ∙ w)ᗮ = n - 1 := by
    have hsumrank : 1 + finrank ℝ (ℝ ∙ w)ᗮ = n := by
      simpa [hspan] using (ℝ ∙ w).finrank_add_finrank_orthogonal
    omega
  have hsum : 1 + (n - 1) = n := Nat.add_sub_of_le hn
  simpa [Nat.choose_one_right] using
    h67 n 1 (n - 1) B (ℝ ∙ w) hsum hspan horth hconv hsymm hmeas

/-- Full Lemma 6.6 obtained from Bilu's (6.7) and the central-line
section formula. -/
theorem lemma66_of_lemma67
    (h67 : Lemma67Statement) {n : ℕ} (hn : 0 < n)
    (B : Set (EuclideanSpace ℝ (Fin n)))
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin n)))
    (w : EuclideanSpace ℝ (Fin n)) (hw : w ≠ 0)
    (hconv : Convex ℝ B)
    (hsymm : (-B : Set (EuclideanSpace ℝ (Fin n))) = B)
    (hmeas : MeasurableSet B)
    (hsection :
      (2 : ℝ≥0∞) * ENNReal.ofReal ‖w‖ ≤
        ENNReal.ofReal (p w) * intrinsicVolume 1
          (B ∩ ((ℝ ∙ w) : Set (EuclideanSpace ℝ (Fin n))))) :
    Lemma66Conclusion B p w :=
  lemma66_of_central_section_bound B p w hsection
    (line_projection_bound_of_lemma67 h67 hn B w hw hconv hsymm hmeas)

/-! ## Exact deductions used in Bilu's Section 8 -/

/-- Cross-multiplied conclusion of Proposition 8.5 before Bilu replaces
the actual affine dimension by the coarser ambient bound. -/
theorem proposition85_of_lemma65
    (h65 : Lemma65Statement) (n d : ℕ)
    (B B₀ : Set (EuclideanSpace ℝ (Fin n)))
    (c : EuclideanSpace ℝ (Fin n)) (ρ : ℝ)
    (hdn : d ≤ n) (hconv : Convex ℝ B) (hmeas : MeasurableSet B₀)
    (hsub : B₀ ⊆ B) (hdim : HasAffineDimension d B₀)
    (hρ : 0 < ρ) (hball : Metric.closedBall c ρ ⊆ closure B) :
    ((d.factorial : ℝ≥0∞) * ENNReal.ofReal (ρ ^ (n - d))) *
          intrinsicVolume d B₀ ≤
        (n.factorial : ℝ≥0∞) * intrinsicVolume n B :=
  h65 n d B B₀ c ρ hdn hconv hmeas hsub hdim hρ hball

/-- Equation (8.8), with Bilu's already-computed full-dimensional volume
substituted.  This is deliberately kept in cross-multiplied form; cancelling
`‖w‖` is a later arithmetic step and requires its positivity. -/
theorem equation88_of_lemma66 {n : ℕ}
    (B : Set (EuclideanSpace ℝ (Fin n)))
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin n)))
    (w : EuclideanSpace ℝ (Fin n)) (V : ℝ≥0∞)
    (h66 : Lemma66Conclusion B p w)
    (hvolume : intrinsicVolume n B = (2 : ℝ≥0∞) ^ n * V) :
    (2 : ℝ≥0∞) * ENNReal.ofReal ‖w‖ *
        intrinsicVolume (n - 1) ((ℝ ∙ w)ᗮ.orthogonalProjectionOnto '' B) ≤
      ((n : ℝ≥0∞) * (2 : ℝ≥0∞) ^ n) * ENNReal.ofReal (p w) * V := by
  unfold Lemma66Conclusion at h66
  rw [hvolume] at h66
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h66

#print axioms midpoint_product_volume_le
#print axioms coarse_section_bound_coordinate
#print axioms intrinsicVolume_coordinateCone
#print axioms intrinsicVolume_closure_of_convex
#print axioms coordinate_cone_section_bound_crossmultiplied
#print axioms isometric_coordinate_cone_section_bound_crossmultiplied
#print axioms origin_centered_isometric_section_step
#print axioms coordinate_cone_chain_factorial_bound
#print axioms origin_centered_linear_section_bound_of_isometric_flag
#print axioms radial_firstFiber_volume_lower_bound
#print axioms intrinsicVolume_eq_lintegral_firstFiber
#print axioms gauge_firstFiber_volume_lower_bound
#print axioms coordinate_projection_central_section_beta_bound
#print axioms coordinate_projection_central_section_bound_of_beta
#print axioms coordinate_projection_central_section_bound

end Erdos186.CFP.Bilu.VolumeSections
