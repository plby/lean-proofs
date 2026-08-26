import ErdosProblems.Erdos520.CaichInitialSmoothing
import ErdosProblems.Erdos520.QuadraticVariationReduction
import ErdosProblems.Erdos520.ShortIntervalPrimes
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory Set
open scoped BigOperators Interval

namespace Erdos
namespace Problem520

/-!
# The core and residual pieces in Caich's averaged main term

After the finite prime sum is interchanged with the short smoothing
integral and `z = x / t`, the core of one thin block is supported on
`x / b < z <= x / a`.  The prime weight at `z` is the reciprocal mass in
the multiplicative interval

`x / (z * (1 + 1 / X)) < p <= x / z`.

This file records that expression literally.  The main theorem below shows
that the standard short-interval reciprocal-prime estimate bounds the core
by a constant times `x` times the concrete equation-(16) block energy.  The
thin-block boundary strip and the long-ratio blocks are separate named
objects; neither is folded into an unspecified positive-part remainder.
-/

/-- Membership in the short multiplicative prime window seen after the
change of variables `z = x / t`. -/
def caichShortWindowCondition
    (X : ℝ) (x p : ℕ) (z : ℝ) : Prop :=
  (x : ℝ) / (z * (1 + 1 / X)) < (p : ℝ) ∧
    (p : ℝ) ≤ (x : ℝ) / z

/-- Reciprocal-prime mass of the short window, restricted to `(a,b]`. -/
noncomputable def caichShortWindowReciprocalMass
    (X : ℝ) (x a b : ℕ) (z : ℝ) : ℝ := by
  classical
  exact ∑ p ∈ freshPrimes a b,
    if caichShortWindowCondition X x p z then (p : ℝ)⁻¹ else 0

/-- The exact strict-smooth kernel in the core of one block. -/
noncomputable def caichCoreBlockKernel
    (X : ℝ) (omega : Omega) (x a b : ℕ) (z : ℝ) : ℝ := by
  classical
  exact ∑ p ∈ freshPrimes a b,
    if caichShortWindowCondition X x p z then
      (p : ℝ)⁻¹ * |caichStrictSmoothReal omega z p| ^ 2
    else 0

/-- The same core kernel before changing variables, with `t` as smoothing
variable. -/
noncomputable def caichCoreTimeKernel
    (X : ℝ) (omega : Omega) (x a b : ℕ) (t : ℝ) : ℝ := by
  classical
  exact ∑ p ∈ freshPrimes a b,
    if t / (1 + 1 / X) < (p : ℝ) ∧ (p : ℝ) ≤ t then
      (p : ℝ)⁻¹ *
        |caichStrictSmoothReal omega ((x : ℝ) / t) p| ^ 2
    else 0

/-- One block's core averaged main term after interchanging the finite sum
and integral and changing variables. -/
noncomputable def caichCoreAveragedBlockMain
    (X : ℝ) (omega : Omega) (x a b : ℕ) : ℝ :=
  (x : ℝ) * X *
    ∫ z in Ioc ((x : ℝ) / (b : ℝ)) ((x : ℝ) / (a : ℝ)),
      caichCoreBlockKernel X omega x a b z / z ^ 2

/-- Time-coordinate form of the same core. -/
noncomputable def caichCoreAveragedBlockMainTime
    (X : ℝ) (omega : Omega) (x a b : ℕ) : ℝ :=
  X * ∫ t in Ioc (a : ℝ) (b : ℝ),
    caichCoreTimeKernel X omega x a b t

/-- The explicit upper-end boundary strip `b < t <= b(1+1/X)` of one
block.  In `z` coordinates it is the interval displayed below. -/
noncomputable def caichBoundaryAveragedBlockMain
    (X : ℝ) (omega : Omega) (x a b : ℕ) : ℝ :=
  (x : ℝ) * X *
    ∫ z in Ioc
        ((x : ℝ) / ((b : ℝ) * (1 + 1 / X)))
        ((x : ℝ) / (b : ℝ)),
      caichCoreBlockKernel X omega x a b z / z ^ 2

/-- Blocks declared `far` by a schedule-specific ratio test.  This is the
literal long-ratio residual corresponding to Caich's `L^(12)` piece. -/
noncomputable def caichLongRatioAveragedMain
    (X : ℝ) (omega : Omega) (x : ℕ)
    (blocks : Finset ℕ) (left right : ℕ → ℕ)
    (near : ℕ → Prop) [DecidablePred near] : ℝ :=
  ∑ j ∈ blocks with ¬ near j,
    caichCoreAveragedBlockMain X omega x (left j) (right j)

/-- Core contribution of the complementary near-ratio blocks. -/
noncomputable def caichNearRatioAveragedMain
    (X : ℝ) (omega : Omega) (x : ℕ)
    (blocks : Finset ℕ) (left right : ℕ → ℕ)
    (near : ℕ → Prop) [DecidablePred near] : ℝ :=
  ∑ j ∈ blocks with near j,
    caichCoreAveragedBlockMain X omega x (left j) (right j)

/-- Sum of the explicit upper-end boundary strips over the selected blocks;
this is the deterministic object corresponding to Caich's `L^(2)` piece. -/
noncomputable def caichBoundaryAveragedMain
    (X : ℝ) (omega : Omega) (x : ℕ)
    (blocks : Finset ℕ) (left right : ℕ → ℕ) : ℝ :=
  ∑ j ∈ blocks,
    caichBoundaryAveragedBlockMain X omega x (left j) (right j)

/-! ## The inversion change of variables -/

/-- Measurable-integrand change of variables `t = d / z` on a positive
finite interval.  The monotone substitution theorem used here does not
require continuity of `g`, which is important because the prime-window
kernel has finitely many jumps. -/
theorem integral_comp_const_div_Ioc
    (g : ℝ → ℝ) {d a b : ℝ}
    (hd : 0 < d) (ha : 0 < a) (hab : a ≤ b) :
    d * (∫ z in Ioc (d / b) (d / a), g (d / z) / z ^ 2) =
      ∫ t in Ioc a b, g t := by
  have hb : 0 < b := ha.trans_le hab
  have hdu : d / b ≤ d / a := by
    apply (div_le_div_iff₀ hb ha).2
    nlinarith
  let f : ℝ → ℝ := fun z => d / z
  let f' : ℝ → ℝ := fun z => -d / z ^ 2
  have hf : ContinuousOn f [[d / b, d / a]] := by
    rw [uIcc_of_le hdu]
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro z hz
    exact ne_of_gt ((div_pos hd hb).trans_le hz.1)
  have hff' : ∀ z ∈ Ioo (min (d / b) (d / a)) (max (d / b) (d / a)),
      HasDerivAt f (f' z) z := by
    intro z hz
    have hzpos : 0 < z := by
      rw [min_eq_left hdu] at hz
      exact (div_pos hd hb).trans hz.1
    dsimp only [f, f']
    convert! ((hasDerivAt_inv hzpos.ne').const_mul d) using 1 <;>
      field_simp <;> ring
  have hf' : ∀ z ∈ Ioo (min (d / b) (d / a)) (max (d / b) (d / a)),
      f' z ≤ 0 := by
    intro z hz
    dsimp only [f']
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hd.le) (sq_nonneg z)
  have hchange := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (g := g) hf hff' hf'
  have hfl : f (d / b) = b := by
    dsimp only [f]
    field_simp
  have hfu : f (d / a) = a := by
    dsimp only [f]
    field_simp
  rw [hfl, hfu] at hchange
  have hleft :
      (∫ z in d / b..d / a, (g ∘ f) z * f' z) =
        -d * (∫ z in d / b..d / a, g (d / z) / z ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro z hz
    dsimp only [f, f', Function.comp_apply]
    ring
  have hright : (∫ t in b..a, g t) = -(∫ t in a..b, g t) := by
    rw [intervalIntegral.integral_symm]
  rw [hleft, hright] at hchange
  rw [intervalIntegral.integral_of_le hdu,
    intervalIntegral.integral_of_le hab] at hchange
  linarith

/-- On positive `z`, the time kernel pulled back by `t=x/z` is exactly the
post-substitution kernel. -/
theorem caichCoreTimeKernel_comp_div
    {X : ℝ} {x a b : ℕ} {z : ℝ}
    (hX : X ≠ 0) (hx : 0 < x) (hz : z ≠ 0) (omega : Omega) :
    caichCoreTimeKernel X omega x a b ((x : ℝ) / z) =
      caichCoreBlockKernel X omega x a b z := by
  classical
  have hxR : (x : ℝ) ≠ 0 := by exact_mod_cast hx.ne'
  have hwindow (p : ℕ) :
      (((x : ℝ) / z) / (1 + 1 / X) < (p : ℝ) ∧
        (p : ℝ) ≤ (x : ℝ) / z) ↔
      caichShortWindowCondition X x p z := by
    unfold caichShortWindowCondition
    rw [div_div]
  have harg : (x : ℝ) / ((x : ℝ) / z) = z := by
    field_simp
  unfold caichCoreTimeKernel caichCoreBlockKernel
  apply Finset.sum_congr rfl
  intro p hp
  by_cases ht :
      ((x : ℝ) / z) / (1 + 1 / X) < (p : ℝ) ∧
        (p : ℝ) ≤ (x : ℝ) / z
  · have hzcond : caichShortWindowCondition X x p z := (hwindow p).mp ht
    simp only [if_pos ht, if_pos hzcond, harg]
  · have hzcond : ¬ caichShortWindowCondition X x p z := by
      exact fun h => ht ((hwindow p).mpr h)
    simp only [if_neg ht, if_neg hzcond]

/-- The `z`- and `t`-coordinate definitions of the core agree exactly. -/
theorem caichCoreAveragedBlockMain_eq_time
    {X : ℝ} {x a b : ℕ}
    (hX : 0 < X) (hx : 0 < x) (ha : 1 ≤ a) (hab : a ≤ b)
    (omega : Omega) :
    caichCoreAveragedBlockMain X omega x a b =
      caichCoreAveragedBlockMainTime X omega x a b := by
  have haR : (0 : ℝ) < (a : ℝ) := by positivity
  have hsub := integral_comp_const_div_Ioc
    (g := caichCoreTimeKernel X omega x a b)
    (d := (x : ℝ)) (a := (a : ℝ)) (b := (b : ℝ))
    (by exact_mod_cast hx) haR (by exact_mod_cast hab)
  have hpullback :
      (∫ z in Ioc ((x : ℝ) / (b : ℝ)) ((x : ℝ) / (a : ℝ)),
          caichCoreTimeKernel X omega x a b ((x : ℝ) / z) / z ^ 2) =
        ∫ z in Ioc ((x : ℝ) / (b : ℝ)) ((x : ℝ) / (a : ℝ)),
          caichCoreBlockKernel X omega x a b z / z ^ 2 := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro z hz
    have hzpos : 0 < z := by
      have hxb : (0 : ℝ) ≤ (x : ℝ) / (b : ℝ) := by positivity
      exact hxb.trans_lt hz.1
    change caichCoreTimeKernel X omega x a b ((x : ℝ) / z) / z ^ 2 =
      caichCoreBlockKernel X omega x a b z / z ^ 2
    rw [caichCoreTimeKernel_comp_div hX.ne' hx hzpos.ne' omega]
  unfold caichCoreAveragedBlockMain caichCoreAveragedBlockMainTime
  rw [← hpullback]
  calc
    (x : ℝ) * X *
        (∫ z in Ioc ((x : ℝ) / (b : ℝ)) ((x : ℝ) / (a : ℝ)),
          caichCoreTimeKernel X omega x a b ((x : ℝ) / z) / z ^ 2) =
      X * ((x : ℝ) *
        ∫ z in Ioc ((x : ℝ) / (b : ℝ)) ((x : ℝ) / (a : ℝ)),
          caichCoreTimeKernel X omega x a b ((x : ℝ) / z) / z ^ 2) := by ring
    _ = X * ∫ t in Ioc (a : ℝ) (b : ℝ),
        caichCoreTimeKernel X omega x a b t := by rw [hsub]

private theorem measurableSet_caichShortWindowCondition
    (X : ℝ) (x p : ℕ) :
    MeasurableSet {z : ℝ | caichShortWindowCondition X x p z} := by
  unfold caichShortWindowCondition
  exact (measurableSet_lt
      (measurable_const.div (measurable_id.mul measurable_const))
      measurable_const).inter
    (measurableSet_le measurable_const (measurable_const.div measurable_id))

theorem measurable_caichShortWindowReciprocalMass
    (X : ℝ) (x a b : ℕ) :
    Measurable (caichShortWindowReciprocalMass X x a b) := by
  classical
  unfold caichShortWindowReciprocalMass
  apply Finset.measurable_sum
  intro p hp
  exact Measurable.ite (measurableSet_caichShortWindowCondition X x p)
    measurable_const measurable_const

theorem measurable_caichCoreBlockKernel
    (X : ℝ) (omega : Omega) (x a b : ℕ) :
    Measurable (caichCoreBlockKernel X omega x a b) := by
  classical
  unfold caichCoreBlockKernel
  apply Finset.measurable_sum
  intro p hp
  apply Measurable.ite
  · exact measurableSet_caichShortWindowCondition X x p
  · exact measurable_const.mul
      ((measurable_caichStrictSmoothReal_cutoff omega p).abs.pow_const 2)
  · exact measurable_const

theorem caichCoreBlockKernel_nonneg
    (X : ℝ) (omega : Omega) (x a b : ℕ) (z : ℝ) :
    0 ≤ caichCoreBlockKernel X omega x a b z := by
  classical
  unfold caichCoreBlockKernel
  apply Finset.sum_nonneg
  intro p hp
  split_ifs <;> positivity

theorem caichCoreAveragedBlockMain_nonneg
    {X : ℝ} (hX : 0 ≤ X) (omega : Omega) (x a b : ℕ) :
    0 ≤ caichCoreAveragedBlockMain X omega x a b := by
  unfold caichCoreAveragedBlockMain
  exact mul_nonneg (mul_nonneg (by positivity) hX)
    (integral_nonneg fun z ↦ div_nonneg
      (caichCoreBlockKernel_nonneg X omega x a b z) (sq_nonneg z))

theorem caichBoundaryAveragedBlockMain_nonneg
    {X : ℝ} (hX : 0 ≤ X) (omega : Omega) (x a b : ℕ) :
    0 ≤ caichBoundaryAveragedBlockMain X omega x a b := by
  unfold caichBoundaryAveragedBlockMain
  exact mul_nonneg (mul_nonneg (by positivity) hX)
    (integral_nonneg fun z ↦ div_nonneg
      (caichCoreBlockKernel_nonneg X omega x a b z) (sq_nonneg z))

theorem caichLongRatioAveragedMain_nonneg
    {X : ℝ} (hX : 0 ≤ X) (omega : Omega) (x : ℕ)
    (blocks : Finset ℕ) (left right : ℕ → ℕ)
    (near : ℕ → Prop) [DecidablePred near] :
    0 ≤ caichLongRatioAveragedMain X omega x blocks left right near := by
  classical
  unfold caichLongRatioAveragedMain
  exact Finset.sum_nonneg fun j hj ↦
    caichCoreAveragedBlockMain_nonneg hX omega x (left j) (right j)

theorem caichBoundaryAveragedMain_nonneg
    {X : ℝ} (hX : 0 ≤ X) (omega : Omega) (x : ℕ)
    (blocks : Finset ℕ) (left right : ℕ → ℕ) :
    0 ≤ caichBoundaryAveragedMain X omega x blocks left right := by
  unfold caichBoundaryAveragedMain
  exact Finset.sum_nonneg fun j hj ↦
    caichBoundaryAveragedBlockMain_nonneg hX omega x (left j) (right j)

/-- The strict cutoff `p-1` of every prime in `(a,b]` is one of the cutoffs
in the concrete running block maximum. -/
theorem abs_caichStrictSmoothReal_sq_le_blockMax
    {a b p : ℕ} (hp : p ∈ freshPrimes a b)
    (omega : Omega) (z : ℝ) :
    |caichStrictSmoothReal omega z p| ^ 2 ≤
      realSmoothBlockMaxSq a b omega z := by
  have hmem := mem_freshPrimes.mp hp
  unfold caichStrictSmoothReal
  exact abs_ΨReal_sq_le_realSmoothBlockMaxSq
    (by omega) (by omega) omega z

/-- Pointwise domination of the strict-smooth prime kernel by reciprocal
mass times the block running maximum. -/
theorem caichCoreBlockKernel_le_mass_mul_blockMax
    (X : ℝ) (omega : Omega) (x a b : ℕ) (z : ℝ) :
    caichCoreBlockKernel X omega x a b z ≤
      caichShortWindowReciprocalMass X x a b z *
        realSmoothBlockMaxSq a b omega z := by
  classical
  unfold caichCoreBlockKernel caichShortWindowReciprocalMass
  calc
    (∑ p ∈ freshPrimes a b,
        if caichShortWindowCondition X x p z then
          (p : ℝ)⁻¹ * |caichStrictSmoothReal omega z p| ^ 2
        else 0) ≤
      ∑ p ∈ freshPrimes a b,
        if caichShortWindowCondition X x p z then
          (p : ℝ)⁻¹ * realSmoothBlockMaxSq a b omega z
        else 0 := by
      apply Finset.sum_le_sum
      intro p hp
      split_ifs
      · exact mul_le_mul_of_nonneg_left
          (abs_caichStrictSmoothReal_sq_le_blockMax hp omega z) (by positivity)
      · exact le_rfl
    _ = (∑ p ∈ freshPrimes a b,
          if caichShortWindowCondition X x p z then (p : ℝ)⁻¹ else 0) *
        realSmoothBlockMaxSq a b omega z := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      split_ifs <;> ring

/-- Exact short-interval reciprocal mass implies the desired core estimate
for one thin block.  No probabilistic input occurs here.

The assumption is deliberately the window estimate itself, so it can be
instantiated either from `ShortIntervalPrimes` or from any sharper prime
theorem without changing the smoothing cleanup. -/
theorem caichCoreAveragedBlockMain_le_realSmoothBlockEnergy
    {X C : ℝ} {x a b : ℕ}
    (hX : 0 < X) (hx : 0 < x)
    (ha : 1 ≤ a) (hab : a ≤ b) (hb : 2 ≤ b)
    (hC : 0 ≤ C) (omega : Omega)
    (hshort : ∀ z ∈
      Ioc ((x : ℝ) / (b : ℝ)) ((x : ℝ) / (a : ℝ)),
      caichShortWindowReciprocalMass X x a b z ≤
        C / (X * Real.log (b : ℝ))) :
    caichCoreAveragedBlockMain X omega x a b ≤
      C * (x : ℝ) * realSmoothBlockEnergy a b omega := by
  let s : Set ℝ :=
    Ioc ((x : ℝ) / (b : ℝ)) ((x : ℝ) / (a : ℝ))
  let f : ℝ → ℝ := fun z ↦
    caichCoreBlockKernel X omega x a b z / z ^ 2
  let A : ℝ := C / (X * Real.log (b : ℝ))
  let g : ℝ → ℝ := fun z ↦
    A * (realSmoothBlockMaxSq a b omega z / z ^ 2)
  have hlog : 0 < Real.log (b : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < b by omega))
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hs : s ⊆ Ioi (0 : ℝ) := by
    intro z hz
    have hxb : (0 : ℝ) ≤ (x : ℝ) / (b : ℝ) := by positivity
    exact hxb.trans_lt hz.1
  have hgBase : IntegrableOn
      (fun z : ℝ ↦ realSmoothBlockMaxSq a b omega z / z ^ 2) s :=
    (integrableOn_realSmoothBlockMaxSq_div_sq hab omega).mono_set hs
  have hg : IntegrableOn g s := by
    simpa only [g] using! hgBase.const_mul A
  have hfMeas : AEStronglyMeasurable f (volume.restrict s) := by
    apply Measurable.aestronglyMeasurable
    exact (measurable_caichCoreBlockKernel X omega x a b).div
      (measurable_id.pow_const 2)
  have hpoint : ∀ z ∈ s, f z ≤ g z := by
    intro z hz
    have hmass : caichShortWindowReciprocalMass X x a b z ≤ A := by
      simpa only [s, A] using! hshort z hz
    have hkernel := caichCoreBlockKernel_le_mass_mul_blockMax
      X omega x a b z
    have hmax := ConcreteThinBlockSchedule.realSmoothBlockMaxSq_nonneg
      a b omega z
    have hmassMax :
        caichShortWindowReciprocalMass X x a b z *
            realSmoothBlockMaxSq a b omega z ≤
          A * realSmoothBlockMaxSq a b omega z :=
      mul_le_mul_of_nonneg_right hmass hmax
    dsimp only [f, g]
    calc
      caichCoreBlockKernel X omega x a b z / z ^ 2 ≤
          (caichShortWindowReciprocalMass X x a b z *
            realSmoothBlockMaxSq a b omega z) / z ^ 2 :=
        div_le_div_of_nonneg_right hkernel (sq_nonneg z)
      _ ≤ (A * realSmoothBlockMaxSq a b omega z) / z ^ 2 :=
        div_le_div_of_nonneg_right hmassMax (sq_nonneg z)
      _ = A * (realSmoothBlockMaxSq a b omega z / z ^ 2) := by ring
  have hf : IntegrableOn f s := by
    refine hg.mono' hfMeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    have hf0 : 0 ≤ f z := by
      dsimp only [f]
      exact div_nonneg (caichCoreBlockKernel_nonneg X omega x a b z)
        (sq_nonneg z)
    rw [Real.norm_eq_abs, abs_of_nonneg hf0]
    exact hpoint z hz
  have hcoreIntegral : (∫ z in s, f z) ≤ ∫ z in s, g z :=
    setIntegral_mono_on hf hg measurableSet_Ioc hpoint
  have hbase0 : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun z : ℝ ↦ realSmoothBlockMaxSq a b omega z / z ^ 2 := by
    filter_upwards with z
    exact div_nonneg
      (ConcreteThinBlockSchedule.realSmoothBlockMaxSq_nonneg a b omega z)
      (sq_nonneg z)
  have henlarge :
      (∫ z in s, realSmoothBlockMaxSq a b omega z / z ^ 2) ≤
        ∫ z in Ioi (0 : ℝ),
          realSmoothBlockMaxSq a b omega z / z ^ 2 :=
    setIntegral_mono_set
      (integrableOn_realSmoothBlockMaxSq_div_sq hab omega)
      hbase0 (ae_of_all volume hs)
  have hxX : 0 ≤ (x : ℝ) * X := by positivity
  unfold caichCoreAveragedBlockMain realSmoothBlockEnergy
  dsimp only [s, f] at hcoreIntegral
  calc
    (x : ℝ) * X *
        (∫ z in s, caichCoreBlockKernel X omega x a b z / z ^ 2) ≤
      (x : ℝ) * X * (∫ z in s, g z) :=
        mul_le_mul_of_nonneg_left hcoreIntegral hxX
    _ = (x : ℝ) * X * A *
        (∫ z in s, realSmoothBlockMaxSq a b omega z / z ^ 2) := by
      rw [show (∫ z in s, g z) =
          A * ∫ z in s, realSmoothBlockMaxSq a b omega z / z ^ 2 by
        unfold g
        simpa only using!
          (integral_const_mul A
            (fun z : ℝ ↦ realSmoothBlockMaxSq a b omega z / z ^ 2)
            (μ := volume.restrict s))]
      ring
    _ ≤ (x : ℝ) * X * A *
        (∫ z in Ioi (0 : ℝ),
          realSmoothBlockMaxSq a b omega z / z ^ 2) := by
      exact mul_le_mul_of_nonneg_left henlarge (by positivity)
    _ = C * (x : ℝ) *
        ((Real.log (b : ℝ))⁻¹ *
          ∫ z in Ioi (0 : ℝ),
            realSmoothBlockMaxSq a b omega z / z ^ 2) := by
      dsimp only [A]
      field_simp
      <;> ring

/-! ## Finite-block deterministic assembly -/

/-- The near- and long-ratio pieces are an exact partition of the core
block sum. -/
theorem caichNear_add_longRatio_eq_coreSum
    (X : ℝ) (omega : Omega) (x : ℕ)
    (blocks : Finset ℕ) (left right : ℕ → ℕ)
    (near : ℕ → Prop) [DecidablePred near] :
    caichNearRatioAveragedMain X omega x blocks left right near +
        caichLongRatioAveragedMain X omega x blocks left right near =
      ∑ j ∈ blocks,
        caichCoreAveragedBlockMain X omega x (left j) (right j) := by
  classical
  unfold caichNearRatioAveragedMain caichLongRatioAveragedMain
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hnear : near j <;> simp [hnear]

/-- A finite family of near blocks is bounded by its cardinality times the
single block-energy maximum.  This is the precise deterministic step which
turns the geometric `O(ell log ell)` near-block count into the main term in
Caich's equation (24). -/
theorem caichNearRatioAveragedMain_le_card_mul_blockEnergyMax
    {X C : ℝ} {x ell : ℕ}
    (J : ℕ → ℕ) (U : ℕ → ℕ → Omega → ℝ)
    (blocks : Finset ℕ) (left right : ℕ → ℕ)
    (near : ℕ → Prop) [DecidablePred near]
    (blockIndex : ℕ → ℕ)
    (hX : 0 < X) (hx : 0 < x) (hC : 0 ≤ C) (omega : Omega)
    (hJ : ∀ j ∈ blocks, near j → blockIndex j ≤ J ell)
    (hleft : ∀ j ∈ blocks, near j → 1 ≤ left j)
    (hmono : ∀ j ∈ blocks, near j → left j ≤ right j)
    (hright : ∀ j ∈ blocks, near j → 2 ≤ right j)
    (hU : ∀ j ∈ blocks, near j →
      realSmoothBlockEnergy (left j) (right j) omega ≤
        U ell (blockIndex j) omega)
    (hshort : ∀ j ∈ blocks, near j → ∀ z ∈
      Ioc ((x : ℝ) / (right j : ℝ)) ((x : ℝ) / (left j : ℝ)),
      caichShortWindowReciprocalMass X x (left j) (right j) z ≤
        C / (X * Real.log (right j : ℝ))) :
    caichNearRatioAveragedMain X omega x blocks left right near ≤
      ((blocks.filter near).card : ℝ) * C * (x : ℝ) *
        caichBlockEnergyMax J U ell omega := by
  classical
  unfold caichNearRatioAveragedMain
  calc
    (∑ j ∈ blocks with near j,
        caichCoreAveragedBlockMain X omega x (left j) (right j)) ≤
      ∑ j ∈ blocks with near j,
        C * (x : ℝ) * U ell (blockIndex j) omega := by
      apply Finset.sum_le_sum
      intro j hj
      have hjBlocks : j ∈ blocks := (Finset.mem_filter.mp hj).1
      have hjNear : near j := (Finset.mem_filter.mp hj).2
      have hcore :=
        caichCoreAveragedBlockMain_le_realSmoothBlockEnergy
          hX hx (hleft j hjBlocks hjNear) (hmono j hjBlocks hjNear)
          (hright j hjBlocks hjNear) hC omega
          (hshort j hjBlocks hjNear)
      exact hcore.trans <| mul_le_mul_of_nonneg_left
        (hU j hjBlocks hjNear) (by positivity)
    _ ≤ ∑ _j ∈ blocks with near _j,
        C * (x : ℝ) * caichBlockEnergyMax J U ell omega := by
      apply Finset.sum_le_sum
      intro j hj
      have hjBlocks : j ∈ blocks := (Finset.mem_filter.mp hj).1
      have hjNear : near j := (Finset.mem_filter.mp hj).2
      have hjRange : blockIndex j ∈ Finset.range (J ell + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le (hJ j hjBlocks hjNear))
      have hUmax : U ell (blockIndex j) omega ≤
          caichBlockEnergyMax J U ell omega := by
        unfold caichBlockEnergyMax
        exact Finset.le_sup' (fun k ↦ U ell k omega) hjRange
      exact mul_le_mul_of_nonneg_left hUmax (by positivity)
    _ = ((blocks.filter near).card : ℝ) * C * (x : ℝ) *
        caichBlockEnergyMax J U ell omega := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      push_cast
      ring

end Problem520
end Erdos
