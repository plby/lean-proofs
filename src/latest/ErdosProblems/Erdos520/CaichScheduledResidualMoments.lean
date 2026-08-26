import ErdosProblems.Erdos520.CaichScheduledMainCleanup
import ErdosProblems.Erdos520.CaichAuxiliaryMomentTail
import ErdosProblems.Erdos520.SmoothRankinEstimate
import ErdosProblems.Erdos520.SmoothDoob

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory Set
open scoped BigOperators ENNReal Interval

namespace Erdos
namespace Problem520

/-!
# First moments of the scheduled Caich residuals

The two residuals left by the exact main-term cleanup are nonnegative.  This
file starts their unconditional probabilistic treatment at the literal
integrands: the expectation of every strict smooth square is bounded by the
corresponding finite smooth-number count, and this estimate is propagated
through the finite prime sum and the smoothing integral.
-/

/-! ## The strict-smooth second moment -/

theorem measurable_caichStrictSmoothReal_joint (p : ℕ) :
    Measurable fun u : ℝ × Omega ↦
      caichStrictSmoothReal u.2 u.1 p := by
  simpa only [caichStrictSmoothReal] using! measurable_ΨReal_joint (p - 1)

theorem integrable_abs_caichStrictSmoothReal_sq (z : ℝ) (p : ℕ) :
    Integrable (fun omega ↦ |caichStrictSmoothReal omega z p| ^ 2) μ := by
  simpa only [caichStrictSmoothReal, ΨReal] using!
    integrable_abs_Ψ_pow ⌊z⌋₊ (p - 1) 2

/-- The exact second-moment input for a strict cutoff.  The natural smooth
bound has cutoff `p`, since the random sum itself has cutoff `p - 1`. -/
theorem integral_abs_caichStrictSmoothReal_sq_le
    (z : ℝ) {p : ℕ} (hp : 0 < p) :
    (∫ omega, |caichStrictSmoothReal omega z p| ^ 2 ∂μ) ≤
      ((Nat.smoothNumbersUpTo ⌊z⌋₊ p).card : ℝ) := by
  unfold caichStrictSmoothReal ΨReal
  simpa only [Nat.sub_add_cancel hp] using!
    integral_sq_Ψ_le_smoothNumbersUpTo_card ⌊z⌋₊ (p - 1)

/-! ## Literal deterministic first-moment kernels -/

/-- Replace each strict-smooth square in the time-coordinate core by its
finite smooth-number second-moment bound. -/
noncomputable def caichCoreTimeFirstMomentKernel
    (X : ℝ) (x a b : ℕ) (t : ℝ) : ℝ := by
  classical
  exact ∑ p ∈ freshPrimes a b,
    if t / (1 + 1 / X) < (p : ℝ) ∧ (p : ℝ) ≤ t then
      (p : ℝ)⁻¹ *
        ((Nat.smoothNumbersUpTo
          (Nat.floor ((x : ℝ) / t)) p).card : ℝ)
    else 0

theorem caichCoreTimeFirstMomentKernel_nonneg
    (X : ℝ) (x a b : ℕ) (t : ℝ) :
    0 ≤ caichCoreTimeFirstMomentKernel X x a b t := by
  classical
  unfold caichCoreTimeFirstMomentKernel
  exact Finset.sum_nonneg fun p hp ↦ by split_ifs <;> positivity

theorem card_smoothNumbersUpTo_le_self (z y : ℕ) :
    (Nat.smoothNumbersUpTo z y).card ≤ z := by
  have hsub : Nat.smoothNumbersUpTo z y ⊆ Finset.Ioc 0 z := by
    intro n hn
    rw [Nat.mem_smoothNumbersUpTo] at hn
    exact Finset.mem_Ioc.mpr
      ⟨Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers hn.2), hn.1⟩
  simpa using! Finset.card_le_card hsub

theorem measurable_caichCoreTimeFirstMomentKernel
    (X : ℝ) (x a b : ℕ) :
    Measurable (caichCoreTimeFirstMomentKernel X x a b) := by
  classical
  unfold caichCoreTimeFirstMomentKernel
  apply Finset.measurable_sum
  intro p hp
  apply Measurable.ite
  · exact (measurableSet_lt
      (measurable_id.div measurable_const) measurable_const).inter
      (measurableSet_le measurable_const measurable_id)
  · have hfloor : Measurable fun t : ℝ ↦
        Nat.floor ((x : ℝ) / t) :=
      Nat.measurable_floor.comp (measurable_const.div measurable_id)
    have hcard : Measurable fun n : ℕ ↦
        ((Nat.smoothNumbersUpTo n p).card : ℝ) :=
      measurable_of_countable _
    exact measurable_const.mul (hcard.comp hfloor)
  · exact measurable_const

/-- On `t ≥ 1`, the pointwise first-moment kernel has the elementary finite
majorant `x` times the reciprocal mass of the whole prime block. -/
theorem caichCoreTimeFirstMomentKernel_le
    (X : ℝ) (x a b : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    caichCoreTimeFirstMomentKernel X x a b t ≤
      (x : ℝ) * freshReciprocalSum a b := by
  classical
  have hxdiv : (x : ℝ) / t ≤ (x : ℝ) := by
    have htpos : (0 : ℝ) < t := zero_lt_one.trans_le ht
    exact (div_le_iff₀ htpos).2 (by
      nlinarith [show (0 : ℝ) ≤ x by positivity])
  have hfloor : Nat.floor ((x : ℝ) / t) ≤ x := by
    have := Nat.floor_mono hxdiv
    simpa only [Nat.floor_natCast] using! this
  unfold caichCoreTimeFirstMomentKernel freshReciprocalSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  split_ifs
  · rw [mul_comm (x : ℝ) (p : ℝ)⁻¹]
    apply mul_le_mul_of_nonneg_left
    · exact_mod_cast
        (card_smoothNumbersUpTo_le_self
          (Nat.floor ((x : ℝ) / t)) p).trans hfloor
    · positivity
  · positivity

set_option maxHeartbeats 800000 in
theorem measurable_caichCoreTimeKernel_joint
    (X : ℝ) (x a b : ℕ) :
    Measurable fun u : ℝ × Omega ↦
      caichCoreTimeKernel X u.2 x a b u.1 := by
  classical
  unfold caichCoreTimeKernel
  apply Finset.measurable_sum
  intro p hp
  apply Measurable.ite
  · exact (measurableSet_lt
      (measurable_fst.div measurable_const) measurable_const).inter
      (measurableSet_le measurable_const measurable_fst)
  · have hstrict : Measurable fun u : ℝ × Omega ↦
        caichStrictSmoothReal u.2 ((x : ℝ) / u.1) p :=
      (measurable_caichStrictSmoothReal_joint p).comp
        ((measurable_const.div measurable_fst).prodMk measurable_snd)
    exact measurable_const.mul (hstrict.abs.pow_const 2)
  · exact measurable_const

theorem integrable_caichCoreTimeKernel_section
    (X : ℝ) (x a b : ℕ) (t : ℝ) :
    Integrable (fun omega ↦ caichCoreTimeKernel X omega x a b t) μ := by
  classical
  unfold caichCoreTimeKernel
  apply integrable_finset_sum
  intro p hp
  split_ifs with ht
  · exact (integrable_abs_caichStrictSmoothReal_sq ((x : ℝ) / t) p).const_mul _
  · exact integrable_zero _ _ _

/-- A finite deterministic bound used solely to justify Fubini. -/
noncomputable def caichCoreTimeKernelUniformBound
    (x a b : ℕ) : ℝ :=
  ∑ p ∈ freshPrimes a b, caichCorePrimeTimeBound x p

theorem caichCoreTimeKernelUniformBound_nonneg (x a b : ℕ) :
    0 ≤ caichCoreTimeKernelUniformBound x a b := by
  unfold caichCoreTimeKernelUniformBound caichCorePrimeTimeBound
  exact Finset.sum_nonneg fun p hp ↦ by positivity

theorem norm_caichCoreTimeKernel_le_uniformBound
    (X : ℝ) (x a b : ℕ) (t : ℝ) (omega : Omega) :
    ‖caichCoreTimeKernel X omega x a b t‖ ≤
      caichCoreTimeKernelUniformBound x a b := by
  rw [Real.norm_eq_abs,
    abs_of_nonneg (caichCoreTimeKernel_nonneg X omega x a b t)]
  rw [caichCoreTimeKernel_eq_sum_primeTerms]
  unfold caichCoreTimeKernelUniformBound
  exact Finset.sum_le_sum fun p hp ↦
    caichCorePrimeTimeTerm_le_bound X omega x p t

theorem integrable_caichCoreTimeKernel_prod_Ioc
    (X : ℝ) (x a b : ℕ) (u v : ℝ) :
    Integrable
      (fun w : ℝ × Omega ↦
        caichCoreTimeKernel X w.2 x a b w.1)
      ((volume.restrict (Ioc u v)).prod μ) := by
  apply Integrable.of_bound
    (measurable_caichCoreTimeKernel_joint X x a b).aestronglyMeasurable
    (caichCoreTimeKernelUniformBound x a b)
  exact ae_of_all _ fun w ↦
    norm_caichCoreTimeKernel_le_uniformBound X x a b w.1 w.2

theorem integrable_caichCoreTimeFirstMomentKernel_Ioc
    (X : ℝ) (x a b : ℕ) {u v : ℝ} (hu : 1 ≤ u) :
    Integrable (caichCoreTimeFirstMomentKernel X x a b)
      (volume.restrict (Ioc u v)) := by
  apply Integrable.of_bound
    (measurable_caichCoreTimeFirstMomentKernel X x a b).aestronglyMeasurable
    ((x : ℝ) * freshReciprocalSum a b)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs,
    abs_of_nonneg (caichCoreTimeFirstMomentKernel_nonneg X x a b t)]
  exact caichCoreTimeFirstMomentKernel_le X x a b (hu.trans_lt ht.1).le

/-- The expectation of the literal time-coordinate prime kernel is bounded
pointwise by its deterministic smooth-number kernel. -/
theorem integral_caichCoreTimeKernel_le_firstMomentKernel
    (X : ℝ) (x a b : ℕ) (t : ℝ) :
    (∫ omega, caichCoreTimeKernel X omega x a b t ∂μ) ≤
      caichCoreTimeFirstMomentKernel X x a b t := by
  classical
  unfold caichCoreTimeKernel caichCoreTimeFirstMomentKernel
  rw [integral_finset_sum (freshPrimes a b) (fun p hp ↦ by
    split_ifs
    · exact (integrable_abs_caichStrictSmoothReal_sq
        ((x : ℝ) / t) p).const_mul _
    · exact integrable_zero _ _ _)]
  apply Finset.sum_le_sum
  intro p hp
  have hpPrime := (mem_freshPrimes.mp hp).1
  split_ifs with ht
  · rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (integral_abs_caichStrictSmoothReal_sq_le
        ((x : ℝ) / t) hpPrime.pos)
      (by positivity)
  · simp

/-! ## Fubini through one scheduled block -/

/-- Exact expectation bound for one time-coordinate core block. -/
theorem integral_caichCoreAveragedBlockMainTime_le_firstMoment
    {X : ℝ} (hX : 0 ≤ X) (x a b : ℕ) (ha : 1 ≤ a) :
    (∫ omega, caichCoreAveragedBlockMainTime X omega x a b ∂μ) ≤
      X * ∫ t in Ioc (a : ℝ) (b : ℝ),
        caichCoreTimeFirstMomentKernel X x a b t := by
  let ν : Measure ℝ := volume.restrict (Ioc (a : ℝ) (b : ℝ))
  let F : ℝ × Omega → ℝ := fun w ↦
    caichCoreTimeKernel X w.2 x a b w.1
  have hF : Integrable F (ν.prod μ) := by
    simpa only [ν, F] using!
      integrable_caichCoreTimeKernel_prod_Ioc X x a b (a : ℝ) (b : ℝ)
  have hleft : Integrable (fun omega ↦ ∫ t, F (t, omega) ∂ν) μ :=
    hF.integral_prod_right
  have hright : Integrable
      (caichCoreTimeFirstMomentKernel X x a b) ν := by
    simpa only [ν] using!
      integrable_caichCoreTimeFirstMomentKernel_Ioc X x a b
        (u := (a : ℝ)) (v := (b : ℝ)) (by exact_mod_cast ha)
  have hswap :
      (∫ omega, ∫ t, F (t, omega) ∂ν ∂μ) =
        ∫ t, ∫ omega, F (t, omega) ∂μ ∂ν := by
    calc
      (∫ omega, ∫ t, F (t, omega) ∂ν ∂μ) =
          ∫ w, F w ∂ν.prod μ :=
        (integral_prod_symm F hF).symm
      _ = ∫ t, ∫ omega, F (t, omega) ∂μ ∂ν :=
        integral_prod F hF
  have hinner :
      (∫ t, ∫ omega, F (t, omega) ∂μ ∂ν) ≤
        ∫ t, caichCoreTimeFirstMomentKernel X x a b t ∂ν := by
    apply integral_mono_ae hF.integral_prod_left hright
    exact ae_of_all ν fun t ↦ by
      simpa only [F] using!
        integral_caichCoreTimeKernel_le_firstMomentKernel X x a b t
  unfold caichCoreAveragedBlockMainTime
  rw [show (fun omega ↦ X * ∫ t in Ioc (a : ℝ) (b : ℝ),
        caichCoreTimeKernel X omega x a b t) =
      fun omega ↦ X * ∫ t, F (t, omega) ∂ν by rfl,
    integral_const_mul]
  exact mul_le_mul_of_nonneg_left (hswap ▸ hinner) hX

/-- The corresponding expectation bound in the literal `z`-coordinate
definition used by `caichScheduledL12`. -/
theorem integral_caichCoreAveragedBlockMain_le_firstMoment
    {X : ℝ} (hX : 0 < X) {x a b : ℕ}
    (hx : 0 < x) (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ omega, caichCoreAveragedBlockMain X omega x a b ∂μ) ≤
      X * ∫ t in Ioc (a : ℝ) (b : ℝ),
        caichCoreTimeFirstMomentKernel X x a b t := by
  have heq : (fun omega ↦ caichCoreAveragedBlockMain X omega x a b) =
      fun omega ↦ caichCoreAveragedBlockMainTime X omega x a b := by
    funext omega
    exact caichCoreAveragedBlockMain_eq_time hX hx ha hab omega
  rw [heq]
  exact integral_caichCoreAveragedBlockMainTime_le_firstMoment
    hX.le x a b ha

/-- Exact expectation bound for one upper boundary strip in time
coordinates. -/
theorem integral_caichBoundaryAveragedBlockMainTime_le_firstMoment
    {X : ℝ} (hX : 0 ≤ X) (x a b : ℕ) (hb : 1 ≤ b) :
    (∫ omega, caichBoundaryAveragedBlockMainTime X omega x a b ∂μ) ≤
      X * ∫ t in Ioc (b : ℝ) ((b : ℝ) * (1 + 1 / X)),
        caichCoreTimeFirstMomentKernel X x a b t := by
  let u : ℝ := b
  let v : ℝ := (b : ℝ) * (1 + 1 / X)
  let ν : Measure ℝ := volume.restrict (Ioc u v)
  let F : ℝ × Omega → ℝ := fun w ↦
    caichCoreTimeKernel X w.2 x a b w.1
  have hF : Integrable F (ν.prod μ) := by
    simpa only [ν, F, u, v] using!
      integrable_caichCoreTimeKernel_prod_Ioc X x a b u v
  have hright : Integrable
      (caichCoreTimeFirstMomentKernel X x a b) ν := by
    simpa only [ν, u, v] using!
      integrable_caichCoreTimeFirstMomentKernel_Ioc X x a b
        (u := (b : ℝ)) (v := (b : ℝ) * (1 + 1 / X))
        (by exact_mod_cast hb)
  have hswap :
      (∫ omega, ∫ t, F (t, omega) ∂ν ∂μ) =
        ∫ t, ∫ omega, F (t, omega) ∂μ ∂ν := by
    calc
      (∫ omega, ∫ t, F (t, omega) ∂ν ∂μ) =
          ∫ w, F w ∂ν.prod μ :=
        (integral_prod_symm F hF).symm
      _ = ∫ t, ∫ omega, F (t, omega) ∂μ ∂ν :=
        integral_prod F hF
  have hinner :
      (∫ t, ∫ omega, F (t, omega) ∂μ ∂ν) ≤
        ∫ t, caichCoreTimeFirstMomentKernel X x a b t ∂ν := by
    apply integral_mono_ae hF.integral_prod_left hright
    exact ae_of_all ν fun t ↦ by
      simpa only [F] using!
        integral_caichCoreTimeKernel_le_firstMomentKernel X x a b t
  unfold caichBoundaryAveragedBlockMainTime
  rw [show (fun omega ↦ X *
        ∫ t in Ioc (b : ℝ) ((b : ℝ) * (1 + 1 / X)),
          caichCoreTimeKernel X omega x a b t) =
      fun omega ↦ X * ∫ t, F (t, omega) ∂ν by rfl,
    integral_const_mul]
  exact mul_le_mul_of_nonneg_left (hswap ▸ hinner) hX

/-- Expectation bound for the literal boundary object in `z` coordinates. -/
theorem integral_caichBoundaryAveragedBlockMain_le_firstMoment
    {X : ℝ} (hX : 0 < X) {x a b : ℕ}
    (hx : 0 < x) (hb : 1 ≤ b) :
    (∫ omega, caichBoundaryAveragedBlockMain X omega x a b ∂μ) ≤
      X * ∫ t in Ioc (b : ℝ) ((b : ℝ) * (1 + 1 / X)),
        caichCoreTimeFirstMomentKernel X x a b t := by
  have heq : (fun omega ↦ caichBoundaryAveragedBlockMain X omega x a b) =
      fun omega ↦ caichBoundaryAveragedBlockMainTime X omega x a b := by
    funext omega
    exact caichBoundaryAveragedBlockMain_eq_time hX omega x hx hb
  rw [heq]
  exact integral_caichBoundaryAveragedBlockMainTime_le_firstMoment
    hX.le x a b hb

/-! ## Integrability of the literal block residuals -/

theorem integrable_caichCoreAveragedBlockMainTime
    (X : ℝ) (x a b : ℕ) :
    Integrable (fun omega ↦
      caichCoreAveragedBlockMainTime X omega x a b) μ := by
  let ν : Measure ℝ := volume.restrict (Ioc (a : ℝ) (b : ℝ))
  let F : ℝ × Omega → ℝ := fun w ↦
    caichCoreTimeKernel X w.2 x a b w.1
  have hF : Integrable F (ν.prod μ) := by
    simpa only [ν, F] using!
      integrable_caichCoreTimeKernel_prod_Ioc X x a b (a : ℝ) (b : ℝ)
  have hsection : Integrable (fun omega ↦
      ∫ t, F (t, omega) ∂ν) μ := hF.integral_prod_right
  unfold caichCoreAveragedBlockMainTime
  simpa only [ν, F] using! hsection.const_mul X

theorem integrable_caichCoreAveragedBlockMain
    {X : ℝ} (hX : 0 < X) {x a b : ℕ}
    (hx : 0 < x) (ha : 1 ≤ a) (hab : a ≤ b) :
    Integrable (fun omega ↦
      caichCoreAveragedBlockMain X omega x a b) μ := by
  have heq : (fun omega ↦ caichCoreAveragedBlockMain X omega x a b) =
      fun omega ↦ caichCoreAveragedBlockMainTime X omega x a b := by
    funext omega
    exact caichCoreAveragedBlockMain_eq_time hX hx ha hab omega
  rw [heq]
  exact integrable_caichCoreAveragedBlockMainTime X x a b

theorem integrable_caichBoundaryAveragedBlockMainTime
    (X : ℝ) (x a b : ℕ) :
    Integrable (fun omega ↦
      caichBoundaryAveragedBlockMainTime X omega x a b) μ := by
  let ν : Measure ℝ := volume.restrict
    (Ioc (b : ℝ) ((b : ℝ) * (1 + 1 / X)))
  let F : ℝ × Omega → ℝ := fun w ↦
    caichCoreTimeKernel X w.2 x a b w.1
  have hF : Integrable F (ν.prod μ) := by
    simpa only [ν, F] using!
      integrable_caichCoreTimeKernel_prod_Ioc X x a b
        (b : ℝ) ((b : ℝ) * (1 + 1 / X))
  have hsection : Integrable (fun omega ↦
      ∫ t, F (t, omega) ∂ν) μ := hF.integral_prod_right
  unfold caichBoundaryAveragedBlockMainTime
  simpa only [ν, F] using! hsection.const_mul X

theorem integrable_caichBoundaryAveragedBlockMain
    {X : ℝ} (hX : 0 < X) {x a b : ℕ}
    (hx : 0 < x) (hb : 1 ≤ b) :
    Integrable (fun omega ↦
      caichBoundaryAveragedBlockMain X omega x a b) μ := by
  have heq : (fun omega ↦ caichBoundaryAveragedBlockMain X omega x a b) =
      fun omega ↦ caichBoundaryAveragedBlockMainTime X omega x a b := by
    funext omega
    exact caichBoundaryAveragedBlockMain_eq_time hX omega x hx hb
  rw [heq]
  exact integrable_caichBoundaryAveragedBlockMainTime X x a b

/-! ## First-moment budgets for the finite scheduled sums -/

noncomputable def caichCoreAveragedBlockFirstMoment
    (X : ℝ) (x a b : ℕ) : ℝ :=
  X * ∫ t in Ioc (a : ℝ) (b : ℝ),
    caichCoreTimeFirstMomentKernel X x a b t

noncomputable def caichBoundaryAveragedBlockFirstMoment
    (X : ℝ) (x a b : ℕ) : ℝ :=
  X * ∫ t in Ioc (b : ℝ) ((b : ℝ) * (1 + 1 / X)),
    caichCoreTimeFirstMomentKernel X x a b t

noncomputable def caichLongRatioFirstMoment
    (X : ℝ) (x : ℕ) (blocks : Finset ℕ)
    (left right : ℕ → ℕ) (near : ℕ → Prop) [DecidablePred near] : ℝ :=
  ∑ j ∈ blocks with ¬ near j,
    caichCoreAveragedBlockFirstMoment X x (left j) (right j)

noncomputable def caichBoundaryFirstMoment
    (X : ℝ) (x : ℕ) (blocks : Finset ℕ)
    (left right : ℕ → ℕ) : ℝ :=
  ∑ j ∈ blocks,
    caichBoundaryAveragedBlockFirstMoment X x (left j) (right j)

noncomputable def caichScheduledL12FirstMoment
    (X : ℝ) (x : ℕ) (blocks : Finset ℕ)
    (left right : ℕ → ℕ) (near : ℕ → Prop) [DecidablePred near] : ℝ :=
  caichLongRatioFirstMoment X x blocks left right near / (x : ℝ)

noncomputable def caichScheduledL2FirstMoment
    (X : ℝ) (x : ℕ) (blocks : Finset ℕ)
    (left right : ℕ → ℕ) : ℝ :=
  caichBoundaryFirstMoment X x blocks left right / (x : ℝ)

theorem caichCoreAveragedBlockFirstMoment_nonneg
    {X : ℝ} (hX : 0 ≤ X) (x a b : ℕ) :
    0 ≤ caichCoreAveragedBlockFirstMoment X x a b := by
  unfold caichCoreAveragedBlockFirstMoment
  exact mul_nonneg hX (integral_nonneg fun t ↦
    caichCoreTimeFirstMomentKernel_nonneg X x a b t)

theorem caichBoundaryAveragedBlockFirstMoment_nonneg
    {X : ℝ} (hX : 0 ≤ X) (x a b : ℕ) :
    0 ≤ caichBoundaryAveragedBlockFirstMoment X x a b := by
  unfold caichBoundaryAveragedBlockFirstMoment
  exact mul_nonneg hX (integral_nonneg fun t ↦
    caichCoreTimeFirstMomentKernel_nonneg X x a b t)

theorem caichScheduledL12FirstMoment_nonneg
    {X : ℝ} (hX : 0 ≤ X) {x : ℕ} (hx : 0 < x)
    (blocks : Finset ℕ) (left right : ℕ → ℕ)
    (near : ℕ → Prop) [DecidablePred near] :
    0 ≤ caichScheduledL12FirstMoment X x blocks left right near := by
  unfold caichScheduledL12FirstMoment caichLongRatioFirstMoment
  exact div_nonneg (Finset.sum_nonneg fun j hj ↦
    caichCoreAveragedBlockFirstMoment_nonneg hX x (left j) (right j))
    (by positivity)

theorem caichScheduledL2FirstMoment_nonneg
    {X : ℝ} (hX : 0 ≤ X) {x : ℕ} (hx : 0 < x)
    (blocks : Finset ℕ) (left right : ℕ → ℕ) :
    0 ≤ caichScheduledL2FirstMoment X x blocks left right := by
  unfold caichScheduledL2FirstMoment caichBoundaryFirstMoment
  exact div_nonneg (Finset.sum_nonneg fun j hj ↦
    caichBoundaryAveragedBlockFirstMoment_nonneg hX x (left j) (right j))
    (by positivity)

theorem integrable_caichLongRatioAveragedMain
    {X : ℝ} (hX : 0 < X) {x : ℕ} (hx : 0 < x)
    (blocks : Finset ℕ) (left right : ℕ → ℕ)
    (near : ℕ → Prop) [DecidablePred near]
    (hleft : ∀ j ∈ blocks, 1 ≤ left j)
    (hle : ∀ j ∈ blocks, left j ≤ right j) :
    Integrable (fun omega ↦
      caichLongRatioAveragedMain X omega x blocks left right near) μ := by
  unfold caichLongRatioAveragedMain
  apply integrable_finset_sum
  intro j hj
  have hjb : j ∈ blocks := (Finset.mem_filter.mp hj).1
  exact integrable_caichCoreAveragedBlockMain hX hx
    (hleft j hjb) (hle j hjb)

theorem integral_caichLongRatioAveragedMain_le_firstMoment
    {X : ℝ} (hX : 0 < X) {x : ℕ} (hx : 0 < x)
    (blocks : Finset ℕ) (left right : ℕ → ℕ)
    (near : ℕ → Prop) [DecidablePred near]
    (hleft : ∀ j ∈ blocks, 1 ≤ left j)
    (hle : ∀ j ∈ blocks, left j ≤ right j) :
    (∫ omega,
      caichLongRatioAveragedMain X omega x blocks left right near ∂μ) ≤
      caichLongRatioFirstMoment X x blocks left right near := by
  unfold caichLongRatioAveragedMain caichLongRatioFirstMoment
  rw [integral_finset_sum _ (fun j hj ↦ by
    have hjb : j ∈ blocks := (Finset.mem_filter.mp hj).1
    exact integrable_caichCoreAveragedBlockMain hX hx
      (hleft j hjb) (hle j hjb))]
  apply Finset.sum_le_sum
  intro j hj
  have hjb : j ∈ blocks := (Finset.mem_filter.mp hj).1
  exact integral_caichCoreAveragedBlockMain_le_firstMoment
    hX hx (hleft j hjb) (hle j hjb)

theorem integrable_caichBoundaryAveragedMain
    {X : ℝ} (hX : 0 < X) {x : ℕ} (hx : 0 < x)
    (blocks : Finset ℕ) (left right : ℕ → ℕ)
    (hright : ∀ j ∈ blocks, 1 ≤ right j) :
    Integrable (fun omega ↦
      caichBoundaryAveragedMain X omega x blocks left right) μ := by
  unfold caichBoundaryAveragedMain
  exact integrable_finset_sum _ fun j hj ↦
    integrable_caichBoundaryAveragedBlockMain hX hx (hright j hj)

theorem integral_caichBoundaryAveragedMain_le_firstMoment
    {X : ℝ} (hX : 0 < X) {x : ℕ} (hx : 0 < x)
    (blocks : Finset ℕ) (left right : ℕ → ℕ)
    (hright : ∀ j ∈ blocks, 1 ≤ right j) :
    (∫ omega,
      caichBoundaryAveragedMain X omega x blocks left right ∂μ) ≤
      caichBoundaryFirstMoment X x blocks left right := by
  unfold caichBoundaryAveragedMain caichBoundaryFirstMoment
  rw [integral_finset_sum _ (fun j hj ↦
    integrable_caichBoundaryAveragedBlockMain hX hx (hright j hj))]
  exact Finset.sum_le_sum fun j hj ↦
    integral_caichBoundaryAveragedBlockMain_le_firstMoment
      hX hx (hright j hj)

theorem integrable_caichScheduledL12
    {X : ℝ} (hX : 0 < X) {x : ℕ} (hx : 0 < x)
    (blocks : Finset ℕ) (left right : ℕ → ℕ)
    (near : ℕ → Prop) [DecidablePred near]
    (hleft : ∀ j ∈ blocks, 1 ≤ left j)
    (hle : ∀ j ∈ blocks, left j ≤ right j) :
    Integrable (fun omega ↦
      caichScheduledL12 X omega x blocks left right near) μ := by
  unfold caichScheduledL12
  exact (integrable_caichLongRatioAveragedMain
    hX hx blocks left right near hleft hle).div_const (x : ℝ)

theorem integral_caichScheduledL12_le_firstMoment
    {X : ℝ} (hX : 0 < X) {x : ℕ} (hx : 0 < x)
    (blocks : Finset ℕ) (left right : ℕ → ℕ)
    (near : ℕ → Prop) [DecidablePred near]
    (hleft : ∀ j ∈ blocks, 1 ≤ left j)
    (hle : ∀ j ∈ blocks, left j ≤ right j) :
    (∫ omega, caichScheduledL12 X omega x blocks left right near ∂μ) ≤
      caichScheduledL12FirstMoment X x blocks left right near := by
  unfold caichScheduledL12 caichScheduledL12FirstMoment
  rw [integral_div]
  exact div_le_div_of_nonneg_right
    (integral_caichLongRatioAveragedMain_le_firstMoment
      hX hx blocks left right near hleft hle) (by positivity)

theorem integrable_caichScheduledL2
    {X : ℝ} (hX : 0 < X) {x : ℕ} (hx : 0 < x)
    (blocks : Finset ℕ) (left right : ℕ → ℕ)
    (hright : ∀ j ∈ blocks, 1 ≤ right j) :
    Integrable (fun omega ↦
      caichScheduledL2 X omega x blocks left right) μ := by
  unfold caichScheduledL2
  exact (integrable_caichBoundaryAveragedMain
    hX hx blocks left right hright).div_const (x : ℝ)

theorem integral_caichScheduledL2_le_firstMoment
    {X : ℝ} (hX : 0 < X) {x : ℕ} (hx : 0 < x)
    (blocks : Finset ℕ) (left right : ℕ → ℕ)
    (hright : ∀ j ∈ blocks, 1 ≤ right j) :
    (∫ omega, caichScheduledL2 X omega x blocks left right ∂μ) ≤
      caichScheduledL2FirstMoment X x blocks left right := by
  unfold caichScheduledL2 caichScheduledL2FirstMoment
  rw [integral_div]
  exact div_le_div_of_nonneg_right
    (integral_caichBoundaryAveragedMain_le_firstMoment
      hX hx blocks left right hright) (by positivity)

end Problem520
end Erdos
