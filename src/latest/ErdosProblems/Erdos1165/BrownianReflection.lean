/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.BrownianSmallBall

/-!
# The measurable Brownian strip event

The Brownian comparison in HLOZ Lemma A.8 concerns the event that an entire
Brownian path stays in a two-sided interval.  This is an uncountable
intersection of evaluation events.  Mathlib's current Brownian API gives
finite-dimensional laws and almost-sure continuity, but it does not yet give
the reflection principle, the distribution of the running maximum, or the
Dirichlet heat kernel of an interval.

This file closes the measure-theoretic part of that gap.  We define a
measurable envelope of the literal, all-times strip event and prove from
almost-sure continuity at zero that a Brownian motion has positive
probability of remaining in any prescribed strip for some deterministic
positive time.  No reflection or exit-time theorem is assumed.

The quantitative theorem needed by HLOZ is a uniform lower bound of order
`exp (-C * T / r^2)`.  It is proved downstream in `BrownianDyadic`,
`BrownianRecenter`, and `BrownianIteration`: dyadic Gaussian tails replace a
missing reflection-principle API, and deterministic-time independence
iterates a uniformly recentering short block.
-/

open scoped ENNReal NNReal Topology

namespace Erdos1165.BrownianReflection

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set

variable {Omega : Type*} {mOmega : MeasurableSpace Omega}
    {P : Measure Omega} {B : ℝ≥0 → Omega → ℝ}

/-- The literal event that a path remains in the open strip `(-r,r)` at
every nonnegative time up to `T`.  We keep this definition separate from its
measurable envelope because it is the pathwise event used in applications. -/
def rawStripEvent (B : ℝ≥0 → Omega → ℝ) (T : ℝ≥0) (r : ℝ) : Set Omega :=
  {omega | ∀ t : ℝ≥0, t ≤ T → |B t omega| < r}

/-- A measurable envelope of the literal all-times strip event.  Its measure
is the outer measure of `rawStripEvent`; this avoids adding a joint
measurability hypothesis not present in `IsBrownianReal`. -/
def stripEvent (P : Measure Omega) (B : ℝ≥0 → Omega → ℝ)
    (T : ℝ≥0) (r : ℝ) : Set Omega :=
  toMeasurable P (rawStripEvent B T r)

lemma measurableSet_stripEvent (T : ℝ≥0) (r : ℝ) :
    MeasurableSet (stripEvent P B T r) :=
  measurableSet_toMeasurable _ _

lemma rawStripEvent_subset_stripEvent (T : ℝ≥0) (r : ℝ) :
    rawStripEvent B T r ⊆ stripEvent P B T r :=
  subset_toMeasurable _ _

lemma rawStripEvent_mono_time {S T : ℝ≥0} (hST : S ≤ T) (r : ℝ) :
    rawStripEvent B T r ⊆ rawStripEvent B S r := by
  intro omega homega t ht
  exact homega t (ht.trans hST)

lemma rawStripEvent_mono_radius (T : ℝ≥0) {r R : ℝ} (hrR : r ≤ R) :
    rawStripEvent B T r ⊆ rawStripEvent B T R := by
  intro omega homega t ht
  exact (homega t ht).trans_le hrR

/-! ## A countable measurable skeleton -/

/-- The event that all nonnegative rational observation times through `T`
belong to the closed strip `[-r,r]`.  The closed boundary is useful when
passing to limits along rational times. -/
def rationalClosedStripEvent (B : ℝ≥0 → Omega → ℝ) (T : ℝ≥0) (r : ℝ) : Set Omega :=
  {omega | ∀ q : ℚ≥0, (q : ℝ≥0) ≤ T → |B (q : ℝ≥0) omega| ≤ r}

/-- The literal closed-strip event. -/
def rawClosedStripEvent (B : ℝ≥0 → Omega → ℝ) (T : ℝ≥0) (r : ℝ) : Set Omega :=
  {omega | ∀ t : ℝ≥0, t ≤ T → |B t omega| ≤ r}

/-- The rational closed-strip skeleton is measurable modulo null sets under
the hypotheses available in Mathlib's Brownian API.  This is a genuine
countable intersection; no joint measurability of `(t,omega) ↦ B t omega`
is needed. -/
theorem nullMeasurableSet_rationalClosedStripEvent
    (hB : IsPreBrownianReal B P) (T : ℝ≥0) (r : ℝ) :
    NullMeasurableSet (rationalClosedStripEvent B T r) P := by
  rw [show rationalClosedStripEvent B T r =
      ⋂ q : ℚ≥0, ⋂ (_h : (q : ℝ≥0) ≤ T),
        {omega | |B (q : ℝ≥0) omega| ≤ r} by
    ext omega
    simp [rationalClosedStripEvent]]
  apply NullMeasurableSet.iInter
  intro q
  apply NullMeasurableSet.iInter
  intro _hq
  have hpre : NullMeasurableSet
      ((B (q : ℝ≥0)) ⁻¹' Icc (-r) r) P :=
    (hB.aemeasurable (q : ℝ≥0)).nullMeasurableSet_preimage measurableSet_Icc
  convert hpre using 1
  ext omega
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Icc, abs_le]

/-- Literal open-strip survival implies membership in the rational closed
skeleton at the same radius. -/
lemma rawStripEvent_subset_rationalClosedStripEvent (T : ℝ≥0) (r : ℝ) :
    rawStripEvent B T r ⊆ rationalClosedStripEvent B T r := by
  intro omega homega q hq
  exact (homega (q : ℝ≥0) hq).le

/-- On a continuous path, checking a closed strip at nonnegative rational
times checks it at every time. -/
theorem mem_rawClosedStripEvent_of_continuous_of_mem_rational
    {omega : Omega} (hcont : Continuous (B · omega)) {T : ℝ≥0} {r : ℝ}
    (homega : omega ∈ rationalClosedStripEvent B T r) :
    omega ∈ rawClosedStripEvent B T r := by
  intro t ht
  obtain ⟨u, _hu_mono, hu_lt, hu_lim⟩ :=
    Real.exists_seq_rat_strictMono_tendsto (t : ℝ)
  let qn : ℕ → ℚ≥0 := fun n ↦ ⟨max (u n) 0, le_max_right _ _⟩
  have hcoe (n : ℕ) : ((qn n : ℝ≥0) : ℝ) = max (u n : ℝ) 0 := by
    change ((max (u n) 0 : ℚ) : ℝ) = max (u n : ℝ) 0
    norm_cast
  have hrealLim : Tendsto (fun n ↦ max (u n : ℝ) 0) atTop (𝓝 (t : ℝ)) := by
    have hzeroLim : Tendsto (fun _n : ℕ ↦ (0 : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds
    have hmax := hu_lim.max hzeroLim
    simpa [max_eq_left (NNReal.coe_nonneg t)] using hmax
  have hqnLim : Tendsto (fun n ↦ (qn n : ℝ≥0)) atTop (𝓝 t) := by
    rw [← NNReal.tendsto_coe]
    simpa only [hcoe] using hrealLim
  have hBLim : Tendsto (fun n ↦ B (qn n : ℝ≥0) omega) atTop (𝓝 (B t omega)) :=
    (hcont.tendsto t).comp hqnLim
  have habsLim : Tendsto (fun n ↦ |B (qn n : ℝ≥0) omega|) atTop (𝓝 |B t omega|) :=
    (continuous_abs.tendsto (B t omega)).comp hBLim
  apply le_of_tendsto' habsLim
  intro n
  apply homega (qn n)
  apply NNReal.coe_le_coe.mp
  rw [hcoe]
  exact max_le ((hu_lt n).le.trans (by exact_mod_cast ht)) (NNReal.coe_nonneg T)

/-- The literal closed-strip event is null-measurable for Brownian motion.
Almost-sure continuity identifies it with the countable rational skeleton. -/
theorem nullMeasurableSet_rawClosedStripEvent
    (hB : IsBrownianReal B P) (T : ℝ≥0) (r : ℝ) :
    NullMeasurableSet (rawClosedStripEvent B T r) P := by
  have hrat := nullMeasurableSet_rationalClosedStripEvent
    hB.toIsPreBrownianReal T r
  apply hrat.congr
  filter_upwards [hB.cont] with omega hcont
  apply propext
  constructor
  · exact mem_rawClosedStripEvent_of_continuous_of_mem_rational hcont
  · intro homega q hq
    exact homega (q : ℝ≥0) hq

/-- A countable union of closed strips with reciprocal-natural margins. -/
def marginStripEvent (B : ℝ≥0 → Omega → ℝ) (T : ℝ≥0) (r : ℝ) : Set Omega :=
  ⋃ n : ℕ, rawClosedStripEvent B T (r - 1 / (n + 1 : ℝ))

theorem nullMeasurableSet_marginStripEvent
    (hB : IsBrownianReal B P) (T : ℝ≥0) (r : ℝ) :
    NullMeasurableSet (marginStripEvent B T r) P := by
  unfold marginStripEvent
  exact NullMeasurableSet.iUnion fun n ↦
    nullMeasurableSet_rawClosedStripEvent hB T (r - 1 / (n + 1 : ℝ))

/-- A continuous path which stays strictly inside a strip on a compact time
interval has a uniform positive margin from the boundary. -/
theorem mem_marginStripEvent_of_continuous_of_mem_rawStripEvent
    {omega : Omega} (hcont : Continuous (B · omega)) {T : ℝ≥0} {r : ℝ}
    (homega : omega ∈ rawStripEvent B T r) :
    omega ∈ marginStripEvent B T r := by
  have hfcont : Continuous (fun t : ℝ≥0 ↦ |B t omega|) :=
    continuous_abs.comp hcont
  obtain ⟨tmax, htmax, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 (bot_le : (0 : ℝ≥0) ≤ T))
      hfcont.continuousOn
  have hmax_lt : |B tmax omega| < r := homega tmax htmax.2
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hmax_lt)
  rw [marginStripEvent]
  refine mem_iUnion.2 ⟨n, ?_⟩
  intro t ht
  have htmem : t ∈ Icc (0 : ℝ≥0) T := ⟨bot_le, ht⟩
  have hle : |B t omega| ≤ |B tmax omega| := hmax htmem
  linarith

/-- Any closed strip with a strictly positive reciprocal-natural margin is
contained in the corresponding open strip. -/
lemma marginStripEvent_subset_rawStripEvent (T : ℝ≥0) (r : ℝ) :
    marginStripEvent B T r ⊆ rawStripEvent B T r := by
  intro omega homega
  rw [marginStripEvent] at homega
  obtain ⟨n, hn⟩ := mem_iUnion.1 homega
  intro t ht
  exact (hn t ht).trans_lt (sub_lt_self r (by positivity))

/-- The literal all-times open-strip event is null-measurable for Brownian
motion.  This removes the uncountable-intersection measurability obstacle:
almost-sure path continuity identifies it with `marginStripEvent`, a
countable union of countable rational skeletons. -/
theorem nullMeasurableSet_rawStripEvent
    (hB : IsBrownianReal B P) (T : ℝ≥0) (r : ℝ) :
    NullMeasurableSet (rawStripEvent B T r) P := by
  have hmargin := nullMeasurableSet_marginStripEvent hB T r
  apply hmargin.congr
  filter_upwards [hB.cont] with omega hcont
  apply propext
  constructor
  · intro homega
    exact marginStripEvent_subset_rawStripEvent T r homega
  · exact mem_marginStripEvent_of_continuous_of_mem_rawStripEvent hcont

/-- The chosen measurable envelope agrees almost everywhere with the literal
all-times event. -/
theorem stripEvent_ae_eq_rawStripEvent
    (hB : IsBrownianReal B P) (T : ℝ≥0) (r : ℝ) :
    stripEvent P B T r =ᵐ[P] rawStripEvent B T r := by
  exact (nullMeasurableSet_rawStripEvent hB T r).toMeasurable_ae_eq

/-! ## Exact Brownian scaling of the path event -/

/-- Diffusive rescaling by the positive spatial factor `r`. -/
def rescaledPath (B : ℝ≥0 → Omega → ℝ) (r : ℝ≥0) : ℝ≥0 → Omega → ℝ :=
  fun t omega ↦ (r : ℝ)⁻¹ * B (r ^ 2 * t) omega

lemma abs_rescaledPath_lt_one_iff {r : ℝ≥0} (hr : 0 < r)
    (B : ℝ≥0 → Omega → ℝ) (t : ℝ≥0) (omega : Omega) :
    |rescaledPath B r t omega| < 1 ↔ |B (r ^ 2 * t) omega| < (r : ℝ) := by
  rw [rescaledPath, abs_mul, abs_inv, abs_of_nonneg (NNReal.coe_nonneg r),
    inv_mul_lt_one₀ (by exact_mod_cast hr)]

/-- The literal strip event obeys the exact diffusive scaling identity.
This is the pathwise content of Brownian scaling; no probability statement is
used here. -/
theorem rawStripEvent_rescaledPath {r : ℝ≥0} (hr : 0 < r) (T : ℝ≥0) :
    rawStripEvent (rescaledPath B r) T 1 =
      rawStripEvent B (r ^ 2 * T) (r : ℝ) := by
  ext omega
  constructor
  · intro homega u hu
    have hr2 : 0 < r ^ 2 := pow_pos hr _
    let t : ℝ≥0 := u / r ^ 2
    have ht : t ≤ T := by
      dsimp [t]
      rw [div_le_iff₀ hr2]
      simpa [mul_comm] using hu
    have hscaled := homega t ht
    have htime : r ^ 2 * t = u := by
      dsimp [t]
      field_simp
    rw [abs_rescaledPath_lt_one_iff hr B t omega, htime] at hscaled
    exact hscaled
  · intro homega t ht
    rw [abs_rescaledPath_lt_one_iff hr B t omega]
    apply homega (r ^ 2 * t)
    simpa [mul_comm] using mul_le_mul_left ht (r ^ 2)

/-- The measurable envelope obeys the same exact scaling identity. -/
theorem stripEvent_rescaledPath {r : ℝ≥0} (hr : 0 < r) (T : ℝ≥0) :
    stripEvent P (rescaledPath B r) T 1 =
      stripEvent P B (r ^ 2 * T) (r : ℝ) := by
  unfold stripEvent
  rw [rawStripEvent_rescaledPath hr]

/-- Diffusive rescaling preserves the Brownian property. -/
theorem isBrownianReal_rescaledPath (hB : IsBrownianReal B P)
    {r : ℝ≥0} (hr : 0 < r) :
    IsBrownianReal (rescaledPath B r) P := by
  have hr2 : r ^ 2 ≠ 0 := (pow_pos hr 2).ne'
  have hscaled := hB.smul hr2
  change IsBrownianReal (fun t omega ↦ (r : ℝ)⁻¹ * B (r ^ 2 * t) omega) P
  simpa only [NNReal.coe_pow, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (NNReal.coe_nonneg r)] using hscaled

/-- Every continuous path starting at zero remains in an arbitrary positive
strip on some reciprocal-natural time interval. -/
lemma exists_reciprocal_horizon_mem_rawStripEvent
    {omega : Omega} (hcont : Continuous (B · omega)) (hzero : B 0 omega = 0)
    {r : ℝ} (hr : 0 < r) :
    ∃ n : ℕ, omega ∈ rawStripEvent B (1 / (n + 1 : ℝ≥0)) r := by
  have htend : Tendsto (B · omega) (𝓝 (0 : ℝ≥0)) (𝓝 (0 : ℝ)) := by
    simpa [hzero] using hcont.tendsto (0 : ℝ≥0)
  have hIoo : Ioo (-r) r ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (neg_lt_zero.mpr hr) hr
  have hpre : {t : ℝ≥0 | B t omega ∈ Ioo (-r) r} ∈ 𝓝 (0 : ℝ≥0) :=
    htend hIoo
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_nhds_iff.mp hpre
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hepsilon
  refine ⟨n, ?_⟩
  intro t ht
  have htball : t ∈ Metric.ball (0 : ℝ≥0) epsilon := by
    rw [Metric.mem_ball]
    rw [NNReal.dist_eq]
    simp only [NNReal.coe_zero, sub_zero]
    have htReal : (t : ℝ) ≤ 1 / (n + 1 : ℝ) := by
      exact_mod_cast ht
    rw [abs_of_nonneg (NNReal.coe_nonneg t)]
    exact htReal.trans_lt hn
  have htIoo := hball htball
  change B t omega ∈ Ioo (-r) r at htIoo
  rw [mem_Ioo] at htIoo
  exact (abs_lt).2 htIoo

/-- Almost every Brownian path belongs to one of the shrinking-horizon
literal strip events. -/
theorem ae_exists_reciprocal_horizon_mem_rawStripEvent
    (hB : IsBrownianReal B P) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ omega ∂P, ∃ n : ℕ,
      omega ∈ rawStripEvent B (1 / (n + 1 : ℝ≥0)) r := by
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero] with omega hcont hzero
  exact exists_reciprocal_horizon_mem_rawStripEvent hcont hzero hr

/-- The measurable strip envelopes at reciprocal-natural horizons cover
almost every Brownian path. -/
theorem ae_mem_iUnion_reciprocal_stripEvent
    (hB : IsBrownianReal B P) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ omega ∂P, omega ∈ ⋃ n : ℕ,
      stripEvent P B (1 / (n + 1 : ℝ≥0)) r := by
  filter_upwards [ae_exists_reciprocal_horizon_mem_rawStripEvent hB hr]
    with omega homega
  obtain ⟨n, hn⟩ := homega
  exact mem_iUnion.2 ⟨n, rawStripEvent_subset_stripEvent _ _ hn⟩

/-- **Unconditional short-time strip survival.**  For every positive strip
radius, some deterministic positive reciprocal-natural horizon has strictly
positive Brownian survival probability.

This is the strongest lower bound obtainable from path continuity alone; the
downstream dyadic-chaining development supplies quantitative constants. -/
theorem exists_reciprocal_horizon_stripEvent_measure_pos
    (hB : IsBrownianReal B P) {r : ℝ} (hr : 0 < r) :
    ∃ n : ℕ, 0 < P (stripEvent P B (1 / (n + 1 : ℝ≥0)) r) := by
  let U : Set Omega := ⋃ n : ℕ, stripEvent P B (1 / (n + 1 : ℝ≥0)) r
  have hUae : ∀ᵐ omega ∂P, omega ∈ U := by
    simpa [U] using ae_mem_iUnion_reciprocal_stripEvent hB hr
  have hUne : P U ≠ 0 := by
    let _ : IsProbabilityMeasure P :=
      hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
    have hUeq : U =ᵐ[P] Set.univ := by
      filter_upwards [hUae] with omega homega
      apply propext
      exact iff_true_intro homega
    have hUone : P U = 1 := by
      calc
        P U = P Set.univ := measure_congr hUeq
        _ = 1 := measure_univ
    rw [hUone]
    exact one_ne_zero
  simpa [U] using exists_measure_pos_of_not_measure_iUnion_null hUne

/-- The same result stated for the literal all-times event.  Measures in Lean
are outer measures on arbitrary sets, and `measure_toMeasurable` says that
passing to the envelope does not change this value. -/
theorem exists_reciprocal_horizon_rawStripEvent_measure_pos
    (hB : IsBrownianReal B P) {r : ℝ} (hr : 0 < r) :
    ∃ n : ℕ, 0 < P (rawStripEvent B (1 / (n + 1 : ℝ≥0)) r) := by
  obtain ⟨n, hn⟩ := exists_reciprocal_horizon_stripEvent_measure_pos hB hr
  refine ⟨n, ?_⟩
  simpa [stripEvent, measure_toMeasurable] using hn

/-- Combining short-time positivity with exact Brownian scaling puts the
positive horizon in the diffusive form `r^2 /(n+1)`. -/
theorem exists_diffusive_reciprocal_stripEvent_measure_pos
    (hB : IsBrownianReal B P) {r : ℝ≥0} (hr : 0 < r) :
    ∃ n : ℕ, 0 <
      P (stripEvent P B (r ^ 2 * (1 / (n + 1 : ℝ≥0))) (r : ℝ)) := by
  have hscaled : IsBrownianReal (rescaledPath B r) P :=
    isBrownianReal_rescaledPath hB hr
  obtain ⟨n, hn⟩ :=
    exists_reciprocal_horizon_stripEvent_measure_pos hscaled (by norm_num : (0 : ℝ) < 1)
  refine ⟨n, ?_⟩
  rwa [stripEvent_rescaledPath hr] at hn

/-- Literal-event form of the diffusive positive-horizon theorem. -/
theorem exists_diffusive_reciprocal_rawStripEvent_measure_pos
    (hB : IsBrownianReal B P) {r : ℝ≥0} (hr : 0 < r) :
    ∃ n : ℕ, 0 <
      P (rawStripEvent B (r ^ 2 * (1 / (n + 1 : ℝ≥0))) (r : ℝ)) := by
  obtain ⟨n, hn⟩ := exists_diffusive_reciprocal_stripEvent_measure_pos hB hr
  refine ⟨n, ?_⟩
  simpa [stripEvent, measure_toMeasurable] using hn

/-- The horizon found above is genuinely positive. -/
theorem exists_pos_horizon_stripEvent_measure_pos
    (hB : IsBrownianReal B P) {r : ℝ} (hr : 0 < r) :
    ∃ T : ℝ≥0, 0 < T ∧ 0 < P (stripEvent P B T r) := by
  obtain ⟨n, hn⟩ := exists_reciprocal_horizon_stripEvent_measure_pos hB hr
  refine ⟨1 / (n + 1 : ℝ≥0), ?_, hn⟩
  positivity

/-! ## Exact centered-Gaussian half-space probabilities -/

/-- A centered real Gaussian is symmetric across zero.  This statement does
not require positive variance; it is the pushforward identity under
reflection. -/
lemma gaussianReal_zero_Iio_eq_Ioi (v : ℝ≥0) :
    gaussianReal 0 v (Iio 0) = gaussianReal 0 v (Ioi 0) := by
  calc
    gaussianReal 0 v (Iio 0) =
        (gaussianReal 0 v).map (fun x : ℝ ↦ -x) (Iio 0) := by
      rw [gaussianReal_map_neg]
      simp
    _ = gaussianReal 0 v ((fun x : ℝ ↦ -x) ⁻¹' Iio 0) := by
      rw [MeasureTheory.Measure.map_apply_of_aemeasurable
        (by fun_prop) measurableSet_Iio]
    _ = gaussianReal 0 v (Ioi 0) := by
      congr 1
      ext x
      simp

/-- A nondegenerate centered Gaussian assigns exactly half its mass to the
strictly negative half-line. -/
lemma gaussianReal_zero_Iio (v : ℝ≥0) (hv : v ≠ 0) :
    gaussianReal 0 v (Iio 0) = (2 : ℝ≥0∞)⁻¹ := by
  let mu : Measure ℝ := gaussianReal 0 v
  let _ : IsProbabilityMeasure mu := inferInstance
  let _ : NullSingletonClass mu := nullSingletonClass_gaussianReal hv
  have hnull : mu ({0} : Set ℝ) = 0 := measure_singleton 0
  have hunion : Iio (0 : ℝ) ∪ Ioi 0 = ({0} : Set ℝ)ᶜ := by
    ext x
    change (x < 0 ∨ 0 < x) ↔ x ≠ 0
    exact ne_iff_lt_or_gt.symm
  have hsum : mu (Iio 0) + mu (Ioi 0) = 1 := by
    rw [← measure_union (by
      refine Set.disjoint_left.2 ?_
      intro x hx hy
      change x < 0 at hx
      change 0 < x at hy
      exact (not_lt_of_ge (le_of_lt hy)) hx) measurableSet_Ioi, hunion,
      measure_compl (measurableSet_singleton (0 : ℝ)) (measure_ne_top mu {0})]
    simp [hnull]
  have heq : mu (Iio 0) = mu (Ioi 0) := gaussianReal_zero_Iio_eq_Ioi v
  have hmul : mu (Iio 0) * 2 = 1 := by
    rw [mul_two]
    calc
      mu (Iio 0) + mu (Iio 0) = mu (Iio 0) + mu (Ioi 0) :=
        congrArg (mu (Iio 0) + ·) heq
      _ = 1 := hsum
  exact ENNReal.eq_inv_of_mul_eq_one_left hmul

/-- At every positive time, a Brownian evaluation is strictly negative with
probability exactly one half. -/
lemma IsPreBrownianReal.measure_eval_lt_zero
    (hB : IsPreBrownianReal B P) {t : ℝ≥0} (ht : 0 < t) :
    P {omega | B t omega < 0} = (2 : ℝ≥0∞)⁻¹ := by
  rw [(hB.hasLaw_eval t).measure_eq measurableSet_Iio]
  exact gaussianReal_zero_Iio t ht.ne'

/-- At every positive time, a Brownian evaluation is strictly positive with
probability exactly one half. -/
lemma IsPreBrownianReal.measure_eval_pos
    (hB : IsPreBrownianReal B P) {t : ℝ≥0} (ht : 0 < t) :
    P {omega | 0 < B t omega} = (2 : ℝ≥0∞)⁻¹ := by
  rw [(hB.hasLaw_eval t).measure_eq measurableSet_Ioi]
  change gaussianReal 0 t (Ioi 0) = _
  rw [← gaussianReal_zero_Iio_eq_Ioi]
  exact gaussianReal_zero_Iio t ht.ne'

end

end Erdos1165.BrownianReflection
