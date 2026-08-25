/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.TorusModel
import ErdosProblems.Erdos232.CircleBessel
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set
open scoped ComplexConjugate ENNReal

namespace Erdos232

noncomputable section

local instance torusFourierMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance torusFourierIsAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance torusFourierIsProbability :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The complex-valued indicator of a measurable torus set. -/
def torusIndicator (S : Set SquareTorus) : SquareTorus → ℂ :=
  S.indicator (fun _ ↦ 1)

theorem measurable_torusIndicator {S : Set SquareTorus} (hS : MeasurableSet S) :
    Measurable (torusIndicator S) := by
  exact measurable_const.indicator hS

theorem memLp_torusIndicator {S : Set SquareTorus} (hS : MeasurableSet S) :
    MemLp (torusIndicator S) 2 volume := by
  exact (memLp_const (1 : ℂ)).indicator hS

/-- The `L²` indicator used in Parseval's identity. -/
def torusIndicatorLp (S : Set SquareTorus) (hS : MeasurableSet S) :
    Lp ℂ 2 (volume : Measure SquareTorus) :=
  (memLp_torusIndicator hS).toLp (torusIndicator S)

theorem coe_torusIndicatorLp {S : Set SquareTorus} (hS : MeasurableSet S) :
    ⇑(torusIndicatorLp S hS) =ᵐ[volume] torusIndicator S :=
  (memLp_torusIndicator hS).coeFn_toLp

theorem mFourierCoeff_torusIndicatorLp {S : Set SquareTorus}
    (hS : MeasurableSet S) (n : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff (⇑(torusIndicatorLp S hS)) n =
      UnitAddTorus.mFourierCoeff (torusIndicator S) n := by
  unfold UnitAddTorus.mFourierCoeff
  apply integral_congr_ae
  filter_upwards [coe_torusIndicatorLp hS] with x hx
  rw [hx]

/-- Nonnegative Fourier mass of a measurable torus indicator. -/
def torusFourierMass (S : Set SquareTorus) (n : Fin 2 → ℤ) : ℝ :=
  ‖UnitAddTorus.mFourierCoeff (torusIndicator S) n‖ ^ 2

theorem torusFourierMass_nonnegative (S : Set SquareTorus) (n : Fin 2 → ℤ) :
    0 ≤ torusFourierMass S n := sq_nonneg _

/-- Parseval: the total Fourier mass is the Haar density of the set. -/
theorem hasSum_torusFourierMass {S : Set SquareTorus} (hS : MeasurableSet S) :
    HasSum (torusFourierMass S) (volume.real S) := by
  have hparseval := UnitAddTorus.hasSum_sq_mFourierCoeff (torusIndicatorLp S hS)
  have hterm : (fun n : Fin 2 → ℤ ↦
      ‖UnitAddTorus.mFourierCoeff (⇑(torusIndicatorLp S hS)) n‖ ^ 2) =
      torusFourierMass S := by
    funext n
    rw [mFourierCoeff_torusIndicatorLp hS]
    rfl
  rw [hterm] at hparseval
  convert hparseval using 1
  have hnorm : (fun x : SquareTorus ↦ ‖(⇑(torusIndicatorLp S hS)) x‖ ^ 2) =ᵐ[volume]
      S.indicator (fun _ ↦ (1 : ℝ)) := by
    filter_upwards [coe_torusIndicatorLp hS] with x hx
    rw [hx]
    by_cases hxS : x ∈ S <;> simp [torusIndicator, hxS]
  rw [integral_congr_ae hnorm]
  exact (integral_indicator_one hS).symm

theorem summable_torusFourierMass {S : Set SquareTorus} (hS : MeasurableSet S) :
    Summable (torusFourierMass S) :=
  (hasSum_torusFourierMass hS).summable

private theorem mFourier_add_point {d : Type*} [Fintype d]
    (n : d → ℤ) (x y : UnitAddTorus d) :
    UnitAddTorus.mFourier n (x + y) =
      UnitAddTorus.mFourier n x * UnitAddTorus.mFourier n y := by
  simp only [UnitAddTorus.mFourier, Pi.add_apply, fourier_apply,
    zsmul_add, AddCircle.toCircle_add, Circle.coe_mul,
    Finset.prod_mul_distrib, ContinuousMap.coe_mk]

private theorem mFourier_neg_arg {d : Type*} [Fintype d]
    (n : d → ℤ) (x : UnitAddTorus d) :
    UnitAddTorus.mFourier (-n) (-x) = UnitAddTorus.mFourier n x := by
  simp only [UnitAddTorus.mFourier, Pi.neg_apply, fourier_apply,
    neg_zsmul, ContinuousMap.coe_mk]
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  simp
  rfl

theorem mFourierCoeff_translate {S : Set SquareTorus} (hS : MeasurableSet S)
    (v : SquareTorus) (n : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff (fun x ↦ torusIndicator S (x + v)) n =
      UnitAddTorus.mFourier n v *
        UnitAddTorus.mFourierCoeff (torusIndicator S) n := by
  unfold UnitAddTorus.mFourierCoeff
  let F : SquareTorus → ℂ := fun y ↦
    UnitAddTorus.mFourier (-n) (y - v) * torusIndicator S y
  calc
    (∫ x : SquareTorus,
        UnitAddTorus.mFourier (-n) x • torusIndicator S (x + v)) =
        ∫ x : SquareTorus, F (x + v) := by
          apply integral_congr_ae
          filter_upwards [] with x
          simp only [F, add_sub_cancel_right, smul_eq_mul]
    _ = ∫ y : SquareTorus, F y :=
      integral_add_right_eq_self F v
    _ = ∫ y : SquareTorus,
        UnitAddTorus.mFourier n v *
          (UnitAddTorus.mFourier (-n) y * torusIndicator S y) := by
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [F]
      rw [show y - v = y + (-v) by abel, mFourier_add_point,
        mFourier_neg_arg]
      ring
    _ = UnitAddTorus.mFourier n v *
        ∫ y : SquareTorus,
          UnitAddTorus.mFourier (-n) y * torusIndicator S y := by
      rw [integral_const_mul]
    _ = _ := by simp only [smul_eq_mul]

/-- The (unradialized) autocorrelation event on the torus. -/
def torusPairEvent (S : Set SquareTorus) (v : SquareTorus) : Set SquareTorus :=
  {x | x ∈ S ∧ x + v ∈ S}

theorem measurable_torusPairEvent {S : Set SquareTorus} (hS : MeasurableSet S)
    (v : SquareTorus) : MeasurableSet (torusPairEvent S v) := by
  exact hS.inter (hS.preimage (measurable_id.add measurable_const))

private theorem memLp_translate_torusIndicator {S : Set SquareTorus}
    (hS : MeasurableSet S) (v : SquareTorus) :
    MemLp (fun x ↦ torusIndicator S (x + v)) 2 volume := by
  apply MemLp.of_bound (C := 1)
  · exact (measurable_torusIndicator hS).comp
      (measurable_id.add measurable_const) |>.aestronglyMeasurable
  · filter_upwards [] with x
    by_cases hx : x + v ∈ S <;> simp [torusIndicator, hx]

/-- Parseval's inner-product identity gives the absolutely convergent character expansion of
every translated two-point correlation. -/
theorem hasSum_torusFourierMass_mul_mFourier_re
    {S : Set SquareTorus} (hS : MeasurableSet S) (v : SquareTorus) :
    HasSum (fun n : Fin 2 → ℤ ↦
      torusFourierMass S n * (UnitAddTorus.mFourier n v).re)
      (volume.real (torusPairEvent S v)) := by
  let g : SquareTorus → ℂ := fun x ↦ torusIndicator S (x + v)
  let gLp : Lp ℂ 2 (volume : Measure SquareTorus) :=
    (memLp_translate_torusIndicator hS v).toLp g
  have hg : ⇑gLp =ᵐ[volume] g :=
    (memLp_translate_torusIndicator hS v).coeFn_toLp
  have hcomplex := UnitAddTorus.hasSum_prod_mFourierCoeff
    (torusIndicatorLp S hS) gLp
  have hfcoeff (n : Fin 2 → ℤ) :
      UnitAddTorus.mFourierCoeff (⇑(torusIndicatorLp S hS)) n =
        UnitAddTorus.mFourierCoeff (torusIndicator S) n :=
    mFourierCoeff_torusIndicatorLp hS n
  have hgcoeff (n : Fin 2 → ℤ) :
      UnitAddTorus.mFourierCoeff (⇑gLp) n =
        UnitAddTorus.mFourierCoeff g n := by
    unfold UnitAddTorus.mFourierCoeff
    apply integral_congr_ae
    filter_upwards [hg] with x hx
    rw [hx]
  have hcomplex' : HasSum (fun n : Fin 2 → ℤ ↦
      (torusFourierMass S n : ℂ) * UnitAddTorus.mFourier n v)
      ((volume.real (torusPairEvent S v) : ℝ) : ℂ) := by
    convert hcomplex using 1
    · ext n
      rw [hfcoeff, hgcoeff, mFourierCoeff_translate hS]
      simp only [torusFourierMass, map_mul]
      rw [mul_comm (UnitAddTorus.mFourier n v), ← mul_assoc, RCLike.conj_mul]
      norm_cast
    · have hfg : (fun x : SquareTorus ↦ conj ((⇑(torusIndicatorLp S hS)) x) *
          (⇑gLp) x) =ᵐ[volume]
          (torusPairEvent S v).indicator (fun _ ↦ (1 : ℂ)) := by
        filter_upwards [coe_torusIndicatorLp hS, hg] with x hfx hgx
        rw [hfx, hgx]
        by_cases hx : x ∈ S <;> by_cases hxv : x + v ∈ S <;>
          simp [torusIndicator, torusPairEvent, hx, hxv, g]
      rw [integral_congr_ae hfg,
        integral_indicator_const (1 : ℂ) (measurable_torusPairEvent hS v)]
      simp
  have hre := RCLike.hasSum_re ℂ hcomplex'
  convert hre using 1 <;>
    simp [Complex.mul_re]

/-- Encode the integer frequency vector as the complex number whose product with a physical
displacement has real part equal to their Euclidean dot product. -/
def latticeComplex (n : Fin 2 → ℤ) : ℂ := ⟨n 0, -(n 1)⟩

/-- Physical frequency of a square-torus character with side length `L`. -/
def torusFrequency (L : ℝ) (n : Fin 2 → ℤ) : ℝ :=
  (2 * Real.pi / L) * ‖latticeComplex n‖

theorem torusFrequency_nonnegative {L : ℝ} (hL : 0 < L) (n : Fin 2 → ℤ) :
    0 ≤ torusFrequency L n := by
  exact mul_nonneg (div_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hL.le)
    (norm_nonneg _)

theorem mFourier_torusVector_re (L : ℝ) (z : ℂ) (n : Fin 2 → ℤ) :
    (UnitAddTorus.mFourier n (torusVector L z)).re =
      Real.cos ((2 * Real.pi / L) * (latticeComplex n * z).re) := by
  simp only [UnitAddTorus.mFourier, Fin.prod_univ_two, ContinuousMap.coe_mk]
  change (fourier (n 0) (torusVector L z 0) *
      fourier (n 1) (torusVector L z 1)).re = _
  rw [show torusVector L z 0 = (z.re / L : UnitAddCircle) by rfl,
    show torusVector L z 1 = (z.im / L : UnitAddCircle) by rfl]
  rw [fourier_coe_apply, fourier_coe_apply]
  rw [← Complex.exp_add]
  simp only [Complex.exp_re, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    latticeComplex, Complex.mul_re, Complex.mul_im]
  simp
  congr 2
  push_cast
  ring

/-- Angular averaging of a square-torus character is exactly the Bessel kernel at its physical
frequency times the displacement norm. -/
theorem integral_mFourier_torusVector_rotate_re
    {L : ℝ} (hL : 0 < L) (z : ℂ) (n : Fin 2 → ℤ) :
    ∫ theta : UnitAddCircle,
        (UnitAddTorus.mFourier n (torusVector L (rotateComplex theta z))).re
          ∂AddCircle.haarAddCircle =
      besselJ0 (torusFrequency L n * ‖z‖) := by
  simp_rw [mFourier_torusVector_re]
  have harg (theta : UnitAddCircle) :
      (latticeComplex n * rotateComplex theta z).re =
        (fourier 1 theta * (latticeComplex n * z)).re := by
    simp only [rotateComplex]
    ring
  simp_rw [harg]
  rw [integral_cos_fourier_one_mul_re]
  simp only [torusFrequency, norm_mul]
  ring_nf

/-- The radial two-point correlation of a measurable torus set. -/
noncomputable def torusRadialCorrelation (S : Set SquareTorus) (L : ℝ) (z : ℂ) : ℝ :=
  ∫ theta : UnitAddCircle,
    volume.real (torusPairEvent S (torusVector L (rotateComplex theta z)))
      ∂AddCircle.haarAddCircle

/-- Radial Parseval: angular averaging turns every torus character into the order-zero
Bessel kernel at its physical frequency. -/
theorem hasSum_torusFourierMass_mul_besselJ0
    {S : Set SquareTorus} (hS : MeasurableSet S) {L : ℝ} (hL : 0 < L) (z : ℂ) :
    HasSum (fun n : Fin 2 → ℤ ↦
      torusFourierMass S n * besselJ0 (torusFrequency L n * ‖z‖))
      (torusRadialCorrelation S L z) := by
  let F : (Fin 2 → ℤ) → UnitAddCircle → ℝ := fun n theta ↦
    torusFourierMass S n *
      (UnitAddTorus.mFourier n (torusVector L (rotateComplex theta z))).re
  let bound : (Fin 2 → ℤ) → UnitAddCircle → ℝ := fun n _ ↦ torusFourierMass S n
  have hFmeas : ∀ n, AEStronglyMeasurable (F n) AddCircle.haarAddCircle := by
    intro n
    apply Measurable.aestronglyMeasurable
    exact measurable_const.mul <| Complex.measurable_re.comp <|
      (UnitAddTorus.mFourier n).continuous.measurable.comp <|
        (measurable_torusVector L).comp (measurable_rotateComplex_const z)
  have hbound : ∀ n, ∀ᵐ theta ∂AddCircle.haarAddCircle,
      ‖F n theta‖ ≤ bound n theta := by
    intro n
    filter_upwards [] with theta
    have hmass := torusFourierMass_nonnegative S n
    have hchar : ‖UnitAddTorus.mFourier n
        (torusVector L (rotateComplex theta z))‖ = 1 := by
      simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod,
        fourier_apply, Circle.norm_coe, Finset.prod_const_one]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hmass]
    calc
      torusFourierMass S n *
          |(UnitAddTorus.mFourier n
            (torusVector L (rotateComplex theta z))).re| ≤
          torusFourierMass S n *
            ‖UnitAddTorus.mFourier n
              (torusVector L (rotateComplex theta z))‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hmass
      _ = bound n theta := by simp [hchar, bound]
  have hboundSummable : ∀ᵐ theta ∂AddCircle.haarAddCircle,
      Summable fun n ↦ bound n theta := by
    filter_upwards [] with theta
    exact summable_torusFourierMass hS
  have hboundIntegrable : Integrable
      (fun theta : UnitAddCircle ↦ ∑' n, bound n theta)
      AddCircle.haarAddCircle := by
    simpa only [bound] using
      (integrable_const (μ := AddCircle.haarAddCircle)
        (c := ∑' n : Fin 2 → ℤ, torusFourierMass S n))
  have hlim : ∀ᵐ theta ∂AddCircle.haarAddCircle,
      HasSum (fun n ↦ F n theta)
        (volume.real
          (torusPairEvent S (torusVector L (rotateComplex theta z)))) := by
    filter_upwards [] with theta
    exact hasSum_torusFourierMass_mul_mFourier_re hS _
  have hseries := MeasureTheory.hasSum_integral_of_dominated_convergence
    (μ := AddCircle.haarAddCircle) bound hFmeas hbound hboundSummable hboundIntegrable hlim
  unfold torusRadialCorrelation
  refine Filter.Tendsto.congr' ?_ hseries
  filter_upwards [] with s
  apply Finset.sum_congr rfl
  intro n _
  unfold F
  rw [MeasureTheory.integral_const_mul, integral_mFourier_torusVector_rotate_re hL]

end

end Erdos232
