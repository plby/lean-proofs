import Mathlib

/-!
# Weak limits and logarithmic potentials on a bounded interval

This file isolates the analytic lemma used in the compactness step of the
proof of Erdős problem 1038.  The first part proves that the singular kernel
`x ↦ log |x - t|` is integrable on every bounded interval and depends
continuously on `t` as an element of `L¹` of that interval.
-/

open scoped ENNReal Real BoundedContinuousFunction
open MeasureTheory Set Filter

namespace Erdos1038

noncomputable section

local instance factOneNeTop : Fact ((1 : ℝ≥0∞) ≠ ∞) :=
  ⟨ENNReal.one_ne_top⟩

/-- The real-valued logarithmic kernel.  Recall that Mathlib sets
`Real.log 0 = 0`; changing its value at the one singular point has no effect
on any of the `L¹` statements below. -/
def logKernel (t x : ℝ) : ℝ := Real.log |x - t|

/-- The logarithmic kernel is integrable on a closed bounded interval. -/
theorem integrableOn_logKernel_Icc {a b t : ℝ} (hab : a ≤ b) :
    IntegrableOn (logKernel t) (Icc a b) volume := by
  have hlog : IntervalIntegrable Real.log volume (a - t) (b - t) :=
    intervalIntegral.intervalIntegrable_log'
  have htranslate := hlog.comp_sub_right t
  have hinterval : IntervalIntegrable (logKernel t) volume a b := by
    change IntervalIntegrable (fun x ↦ Real.log |x - t|) volume a b
    simpa only [Real.log_abs, sub_add_cancel] using! htranslate
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hinterval

/-- The logarithmic kernel as an element of `L¹` on a fixed interval. -/
def logKernelLp (a b t : ℝ) (hab : a ≤ b) :
    Lp ℝ 1 (volume.restrict (Icc a b)) :=
  (memLp_one_iff_integrable.mpr (integrableOn_logKernel_Icc hab)).toLp
    (logKernel t)

theorem logKernelLp_coeFn {a b t : ℝ} (hab : a ≤ b) :
    logKernelLp a b t hab =ᵐ[volume.restrict (Icc a b)] logKernel t :=
  MemLp.coeFn_toLp _

/-- A compactly supported version of `x ↦ log |x|`. -/
def truncatedLog (R : ℝ) : ℝ → ℝ :=
  (Icc (-R) R).indicator (logKernel 0)

theorem integrable_truncatedLog {R : ℝ} (hR : 0 ≤ R) :
    Integrable (truncatedLog R) volume := by
  have h := integrableOn_logKernel_Icc (t := 0) (a := -R) (b := R) (by linarith)
  have hi := h.integrable_indicator measurableSet_Icc
  simpa only [truncatedLog] using! hi

/-- The compactly supported logarithm as a global `L¹(ℝ)` function. -/
def truncatedLogLp (R : ℝ) (hR : 0 ≤ R) : Lp ℝ 1 (volume : Measure ℝ) :=
  (memLp_one_iff_integrable.mpr (integrable_truncatedLog hR)).toLp
    (truncatedLog R)

theorem truncatedLogLp_coeFn {R : ℝ} (hR : 0 ≤ R) :
    truncatedLogLp R hR =ᵐ[volume] truncatedLog R :=
  MemLp.coeFn_toLp _

/-- Translation of the compactly supported logarithm in global `L¹(ℝ)`. -/
def translatedTruncatedLogLp (R : ℝ) (hR : 0 ≤ R) (t : ℝ) :
    Lp ℝ 1 (volume : Measure ℝ) :=
  DomAddAct.mk (-t) +ᵥ truncatedLogLp R hR

/-- Translation is continuous in global `L¹(ℝ)`. -/
theorem continuous_translatedTruncatedLogLp {R : ℝ} (hR : 0 ≤ R) :
    Continuous (translatedTruncatedLogLp R hR) := by
  unfold translatedTruncatedLogLp
  exact continuous_vadd.comp
    ((DomAddAct.continuous_mk.comp continuous_neg).prodMk continuous_const)

/-- Restrict a translated truncation to a fixed interval. -/
def restrictedTranslatedLogLp (a b R : ℝ) (hR : 0 ≤ R) (t : ℝ) :
    Lp ℝ 1 (volume.restrict (Icc a b)) :=
  LpToLpRestrictCLM ℝ ℝ ℝ volume 1 (Icc a b)
    (translatedTruncatedLogLp R hR t)

theorem continuous_restrictedTranslatedLogLp {a b R : ℝ} (hR : 0 ≤ R) :
    Continuous (restrictedTranslatedLogLp a b R hR) :=
  (LpToLpRestrictCLM ℝ ℝ ℝ volume 1 (Icc a b)).continuous.comp
    (continuous_translatedTruncatedLogLp hR)

theorem translatedTruncatedLogLp_coeFn {R t : ℝ} (hR : 0 ≤ R) :
    translatedTruncatedLogLp R hR t =ᵐ[volume]
      fun x ↦ truncatedLog R (x - t) := by
  have haction :=
    DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk (-t)) (truncatedLogLp R hR)
  have hbase :=
    (measurePreserving_vadd (-t) (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp
      (truncatedLogLp_coeFn hR)
  filter_upwards [haction, hbase] with x hxaction hxbase
  calc
    translatedTruncatedLogLp R hR t x = truncatedLogLp R hR (-t + x) := by
      simpa only [translatedTruncatedLogLp, Equiv.symm_apply_apply, vadd_eq_add]
        using! hxaction
    _ = truncatedLog R (-t + x) := hxbase
    _ = truncatedLog R (x - t) := by rw [neg_add_eq_sub]

theorem restrictedTranslatedLogLp_coeFn {a b R t : ℝ} (hR : 0 ≤ R) :
    restrictedTranslatedLogLp a b R hR t =ᵐ[volume.restrict (Icc a b)]
      fun x ↦ truncatedLog R (x - t) := by
  exact (LpToLpRestrictCLM_coeFn ℝ (Icc a b)
    (translatedTruncatedLogLp R hR t)).trans
      (ae_restrict_of_ae (translatedTruncatedLogLp_coeFn hR))

theorem truncatedLog_sub_eq_logKernel {R t x : ℝ}
    (hxt : x - t ∈ Icc (-R) R) :
    truncatedLog R (x - t) = logKernel t x := by
  rw [truncatedLog, indicator_of_mem hxt]
  simp only [logKernel, sub_zero]

/-- On an interval where the truncation is inactive, the restricted global
translate is exactly the logarithmic kernel in `L¹`. -/
theorem restrictedTranslatedLogLp_eq_logKernelLp
    {a b R t : ℝ} (hab : a ≤ b) (hR : 0 ≤ R)
    (hbound : ∀ x ∈ Icc a b, x - t ∈ Icc (-R) R) :
    restrictedTranslatedLogLp a b R hR t = logKernelLp a b t hab := by
  rw [Lp.ext_iff]
  filter_upwards [restrictedTranslatedLogLp_coeFn hR,
    logKernelLp_coeFn hab, ae_restrict_mem measurableSet_Icc]
      with x htrunc hkernel hx
  calc
    restrictedTranslatedLogLp a b R hR t x = truncatedLog R (x - t) := htrunc
    _ = logKernel t x := truncatedLog_sub_eq_logKernel (hbound x hx)
    _ = logKernelLp a b t hab x := hkernel.symm

/-- A truncation radius that works uniformly for `t` in the unit
neighborhood of `t₀` and `x ∈ [a,b]`. -/
def localLogRadius (a b t₀ : ℝ) : ℝ :=
  |a| + |b| + |t₀| + 1

theorem localLogRadius_nonneg (a b t₀ : ℝ) :
    0 ≤ localLogRadius a b t₀ := by
  simp only [localLogRadius]
  positivity

theorem sub_mem_Icc_localLogRadius {a b t₀ t x : ℝ}
    (hx : x ∈ Icc a b) (ht : t ∈ Ioo (t₀ - 1) (t₀ + 1)) :
    x - t ∈ Icc (-localLogRadius a b t₀) (localLogRadius a b t₀) := by
  rw [localLogRadius]
  constructor
  · have ha : -|a| ≤ a := neg_abs_le a
    have ht₀ : t₀ ≤ |t₀| := le_abs_self t₀
    have hb : 0 ≤ |b| := abs_nonneg b
    linarith [hx.1, ht.2]
  · have hb : b ≤ |b| := le_abs_self b
    have ht₀ : -|t₀| ≤ t₀ := neg_abs_le t₀
    have ha : 0 ≤ |a| := abs_nonneg a
    linarith [hx.2, ht.1]

/-- The critical kernel fact: `t ↦ (x ↦ log |x-t|)` is continuous as a
map into `L¹` of every fixed bounded interval. -/
theorem continuous_logKernelLp {a b : ℝ} (hab : a ≤ b) :
    Continuous fun t ↦ logKernelLp a b t hab := by
  rw [continuous_iff_continuousAt]
  intro t₀
  let R := localLogRadius a b t₀
  have hR : 0 ≤ R := localLogRadius_nonneg a b t₀
  have hcont : ContinuousAt (restrictedTranslatedLogLp a b R hR) t₀ :=
    (continuous_restrictedTranslatedLogLp hR).continuousAt
  apply hcont.congr
  filter_upwards [Ioo_mem_nhds (sub_lt_self t₀ zero_lt_one)
    (lt_add_of_pos_right t₀ zero_lt_one)] with t ht
  exact restrictedTranslatedLogLp_eq_logKernelLp hab hR fun x hx ↦ by
    exact sub_mem_Icc_localLogRadius hx ht

/-! ## The finite-rank weak-convergence step -/

section FiniteRank

variable {X E ι κ : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

/-- Weak convergence of probability measures carries the integral of a
finite-rank bounded continuous function to the corresponding limit.  This is
the algebraic half of the standard partition-of-unity proof for
Banach-valued test functions. -/
theorem tendsto_integral_finset_smul_of_tendsto_probabilityMeasure
    {L : Filter ι} {P : ι → ProbabilityMeasure X} {P₀ : ProbabilityMeasure X}
    (hP : Tendsto P L (nhds P₀)) (s : Finset κ)
    (c : κ → (X →ᵇ ℝ)) (v : κ → E) :
    Tendsto
      (fun n ↦ ∫ x, ∑ i ∈ s, c i x • v i ∂(P n : Measure X)) L
      (nhds (∫ x, ∑ i ∈ s, c i x • v i ∂(P₀ : Measure X))) := by
  have hintegral (Q : ProbabilityMeasure X) :
      (∫ x, ∑ i ∈ s, c i x • v i ∂(Q : Measure X)) =
        ∑ i ∈ s, (∫ x, c i x ∂(Q : Measure X)) • v i := by
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i hi
      exact integral_smul_const (fun x ↦ c i x) (v i)
    · intro i hi
      exact ((c i).integrable (Q : Measure X)).smul_const (v i)
  simp_rw [hintegral]
  exact tendsto_finsetSum s fun i hi ↦
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hP (c i)).smul_const (v i)

/-- Uniform approximation of a bounded continuous Banach-valued function by
finite sums of scalar bounded continuous functions times fixed vectors. -/
def HasFiniteRankApproximation (K : X →ᵇ E) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ (m : ℕ) (c : Fin m → (X →ᵇ ℝ)) (v : Fin m → E),
      ∀ x, ‖K x - ∑ i, c i x • v i‖ ≤ ε

/-- The analytic finite-rank argument: once a bounded continuous
Banach-valued test function has uniform finite-rank approximations, its
Bochner integral is continuous for weak convergence of probability
measures. -/
theorem tendsto_integral_bcf_of_hasFiniteRankApproximation
    [SecondCountableTopology E]
    {L : Filter ι} {P : ι → ProbabilityMeasure X} {P₀ : ProbabilityMeasure X}
    (hP : Tendsto P L (nhds P₀)) (K : X →ᵇ E)
    (hK : HasFiniteRankApproximation K) :
    Tendsto (fun n ↦ ∫ x, K x ∂(P n : Measure X)) L
      (nhds (∫ x, K x ∂(P₀ : Measure X))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨m, c, v, happ⟩ := hK (ε / 3) (by linarith)
  let F : X → E := fun x ↦ ∑ i, c i x • v i
  have hKint (Q : ProbabilityMeasure X) : Integrable K (Q : Measure X) := by
    refine ⟨K.continuous.aestronglyMeasurable, (hasFiniteIntegral_def _ _).mp ?_⟩
    calc
      ∫⁻ x, ‖K x‖₊ ∂(Q : Measure X) ≤
          ‖K‖₊ * ((Q : Measure X) univ) := K.lintegral_nnnorm_le (Q : Measure X)
      _ < ∞ := ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top _ _)
  have hFint (Q : ProbabilityMeasure X) : Integrable F (Q : Measure X) := by
    dsimp only [F]
    apply integrable_finsetSum
    intro i hi
    exact ((c i).integrable (Q : Measure X)).smul_const (v i)
  have herror (Q : ProbabilityMeasure X) :
      dist (∫ x, K x ∂(Q : Measure X)) (∫ x, F x ∂(Q : Measure X)) ≤ ε / 3 := by
    rw [dist_eq_norm, ← integral_sub (hKint Q) (hFint Q)]
    calc
      ‖∫ x, K x - F x ∂(Q : Measure X)‖ ≤
          (ε / 3) * (Q : Measure X).real univ :=
        norm_integral_le_of_norm_le_const
          (Eventually.of_forall fun x ↦ by simpa only [F] using! happ x)
      _ = ε / 3 := by simp
  have hfin := tendsto_integral_finset_smul_of_tendsto_probabilityMeasure
    hP (Finset.univ : Finset (Fin m)) c v
  have hfin' :
      Tendsto (fun n ↦ ∫ x, F x ∂(P n : Measure X)) L
        (nhds (∫ x, F x ∂(P₀ : Measure X))) := by
    simpa only [F, Finset.sum_filter, Finset.mem_univ, ↓reduceIte] using! hfin
  filter_upwards [(Metric.tendsto_nhds.mp hfin') (ε / 3) (by linarith)] with n hn
  calc
    dist (∫ x, K x ∂(P n : Measure X)) (∫ x, K x ∂(P₀ : Measure X)) ≤
        dist (∫ x, K x ∂(P n : Measure X)) (∫ x, F x ∂(P n : Measure X)) +
          dist (∫ x, F x ∂(P n : Measure X)) (∫ x, K x ∂(P₀ : Measure X)) :=
      dist_triangle _ _ _
    _ ≤ dist (∫ x, K x ∂(P n : Measure X)) (∫ x, F x ∂(P n : Measure X)) +
          (dist (∫ x, F x ∂(P n : Measure X)) (∫ x, F x ∂(P₀ : Measure X)) +
            dist (∫ x, F x ∂(P₀ : Measure X)) (∫ x, K x ∂(P₀ : Measure X))) := by
      gcongr
      exact dist_triangle _ _ _
    _ < ε := by
      have hleft := herror (P n)
      have hright := herror P₀
      have hright' :
          dist (∫ x, F x ∂(P₀ : Measure X)) (∫ x, K x ∂(P₀ : Measure X)) ≤
            ε / 3 := by
        simpa only [dist_comm] using! hright
      linarith

end FiniteRank

section CompactFiniteRank

variable {Y F : Type*} [PseudoMetricSpace Y] [CompactSpace Y]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- On a compact pseudo-metric space, every bounded continuous
Banach-valued function admits uniform finite-rank approximations.  The proof
is the usual finite subcover plus partition-of-unity construction. -/
theorem hasFiniteRankApproximation_of_compact (K : Y →ᵇ F) :
    HasFiniteRankApproximation K := by
  intro ε hε
  let U : Y → Set Y := fun y ↦ {x | ‖K x - K y‖ < ε}
  have hUopen (y : Y) : IsOpen (U y) := by
    exact isOpen_lt
      (continuous_norm.comp (K.continuous.sub continuous_const)) continuous_const
  have hUcover : (univ : Set Y) ⊆ ⋃ y, U y := by
    intro x hx
    apply mem_iUnion.mpr
    refine ⟨x, ?_⟩
    simp only [U, mem_ofPred_eq, sub_self, norm_zero, hε]
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUopen hUcover
  let I := {y : Y // y ∈ t}
  let V : I → Set Y := fun y ↦ U y.1
  have hVopen (i : I) : IsOpen (V i) := hUopen i.1
  have hVcover : (univ : Set Y) ⊆ ⋃ i, V i := by
    intro x hx
    have hxt := ht hx
    simp only [mem_iUnion] at hxt ⊢
    obtain ⟨y, hy⟩ := hxt
    obtain ⟨hyt, hxy⟩ := hy
    exact ⟨⟨y, hyt⟩, hxy⟩
  obtain ⟨ρ, hρ⟩ :=
    PartitionOfUnity.exists_isSubordinate isClosed_univ V hVopen hVcover
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  refine ⟨Fintype.card I,
    fun j ↦ BoundedContinuousFunction.mkOfCompact (ρ (e j)),
    fun j ↦ K (e j).1, ?_⟩
  intro x
  have hsumI : ∑ i : I, ρ i x = 1 := by
    have h := ρ.sum_eq_one (show x ∈ (univ : Set Y) by simp)
    rw [finsum_eq_sum (fun i : I ↦ ρ i x)
      (Finite.subset finite_univ (subset_univ (Function.support fun i : I ↦ ρ i x)))] at h
    rwa [Fintype.sum_subset (by simp)] at h
  have hsume : ∑ j : Fin (Fintype.card I), ρ (e j) x = 1 := by
    exact (e.sum_comp (fun i : I ↦ ρ i x)).trans hsumI
  have hrearrange :
      K x - ∑ j : Fin (Fintype.card I), ρ (e j) x • K (e j).1 =
        ∑ j : Fin (Fintype.card I), ρ (e j) x • (K x - K (e j).1) := by
    calc
      K x - ∑ j : Fin (Fintype.card I), ρ (e j) x • K (e j).1 =
          (1 : ℝ) • K x - ∑ j : Fin (Fintype.card I), ρ (e j) x • K (e j).1 := by
        rw [one_smul]
      _ = (∑ j : Fin (Fintype.card I), ρ (e j) x) • K x -
          ∑ j : Fin (Fintype.card I), ρ (e j) x • K (e j).1 := by rw [hsume]
      _ = (∑ j : Fin (Fintype.card I), ρ (e j) x • K x) -
          ∑ j : Fin (Fintype.card I), ρ (e j) x • K (e j).1 := by
        rw [Finset.sum_smul]
      _ = ∑ j : Fin (Fintype.card I),
          (ρ (e j) x • K x - ρ (e j) x • K (e j).1) := by
        rw [Finset.sum_sub_distrib]
      _ = _ := by simp only [smul_sub]
  change ‖K x - ∑ j : Fin (Fintype.card I), ρ (e j) x • K (e j).1‖ ≤ ε
  rw [hrearrange]
  calc
    ‖∑ j : Fin (Fintype.card I), ρ (e j) x • (K x - K (e j).1)‖ ≤
        ∑ j : Fin (Fintype.card I), ‖ρ (e j) x • (K x - K (e j).1)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j : Fin (Fintype.card I), ρ (e j) x * ε := by
      apply Finset.sum_le_sum
      intro j hj
      have hnonneg : 0 ≤ ρ (e j) x := ρ.nonneg (e j) x
      by_cases hz : ρ (e j) x = 0
      · simp [hz]
      · have hxsupport : x ∈ Function.support (ρ (e j)) := by
          change ρ (e j) x ≠ 0
          exact hz
        have hxU : x ∈ U (e j).1 :=
          hρ (e j) (subset_closure hxsupport)
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hnonneg]
        exact mul_le_mul_of_nonneg_left (le_of_lt hxU) hnonneg
    _ = ε := by
      rw [← Finset.sum_mul, hsume, one_mul]

/-- Consequently, integration of a bounded continuous Banach-valued
function over a compact pseudo-metric space is continuous for the weak
topology on probability measures. -/
theorem tendsto_integral_bcf_of_tendsto_probabilityMeasure_compact
    [MeasurableSpace Y] [BorelSpace Y] [CompleteSpace F]
    [SecondCountableTopology F]
    {J : Type*} {L : Filter J} {P : J → ProbabilityMeasure Y}
    {P₀ : ProbabilityMeasure Y} (hP : Tendsto P L (nhds P₀))
    (K : Y →ᵇ F) :
    Tendsto (fun n ↦ ∫ y, K y ∂(P n : Measure Y)) L
      (nhds (∫ y, K y ∂(P₀ : Measure Y))) :=
  tendsto_integral_bcf_of_hasFiniteRankApproximation hP K
    (hasFiniteRankApproximation_of_compact K)

end CompactFiniteRank

/-! ## Logarithmic potentials of measures on the root interval -/

/-- The compact interval in which all roots lie, used as an intrinsic sample
space for supported probability measures. -/
abbrev RootInterval := Set.Icc (-1 : ℝ) 1

/-- The logarithmic kernel, restricted in its parameter to the compact root
interval and bundled as a bounded continuous `L¹`-valued function. -/
def logKernelRootIntervalBCF (a b : ℝ) (hab : a ≤ b) :
    RootInterval →ᵇ Lp ℝ 1 (volume.restrict (Icc a b)) :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun t ↦ logKernelLp a b t.1 hab,
      (continuous_logKernelLp hab).comp continuous_subtype_val⟩

theorem logKernelRootIntervalBCF_apply {a b : ℝ} (hab : a ≤ b)
    (t : RootInterval) :
    logKernelRootIntervalBCF a b hab t = logKernelLp a b t.1 hab :=
  rfl

/-- Weak convergence of probability measures intrinsically supported on
`[-1,1]` implies convergence of their logarithmic potentials in `L¹` on
every fixed bounded interval. -/
theorem tendsto_integral_logKernelLp_of_tendsto_rootInterval
    {J : Type*} {L : Filter J} {P : J → ProbabilityMeasure RootInterval}
    {P₀ : ProbabilityMeasure RootInterval} (hP : Tendsto P L (nhds P₀))
    {a b : ℝ} (hab : a ≤ b) :
    Tendsto
      (fun n ↦ ∫ t, logKernelLp a b t.1 hab ∂(P n : Measure RootInterval)) L
      (nhds (∫ t, logKernelLp a b t.1 hab ∂(P₀ : Measure RootInterval))) := by
  simpa only [logKernelRootIntervalBCF_apply] using!
    (tendsto_integral_bcf_of_tendsto_probabilityMeasure_compact hP
      (logKernelRootIntervalBCF a b hab))

/-- A probability measure on `ℝ` is supported on the permitted root
interval. -/
def IsRootIntervalSupported (P : ProbabilityMeasure ℝ) : Prop :=
  (P : Measure ℝ) RootInterval = 1

/-- Regard a probability measure supported on `[-1,1]` as a probability
measure on the subtype `RootInterval`. -/
def probabilityMeasureToRootInterval (P : ProbabilityMeasure ℝ)
    (hP : IsRootIntervalSupported P) : ProbabilityMeasure RootInterval := by
  refine ⟨Measure.comap ((↑) : RootInterval → ℝ) (P : Measure ℝ), ?_⟩
  apply (MeasurableEmbedding.subtype_coe measurableSet_Icc).isProbabilityMeasure_comap
  have hmem : ∀ᵐ x ∂(P : Measure ℝ), x ∈ RootInterval :=
    (mem_ae_iff_prob_eq_one measurableSet_Icc).2 hP
  filter_upwards [hmem] with x hx
  exact ⟨⟨x, hx⟩, rfl⟩

theorem toFiniteMeasure_probabilityMeasureToRootInterval
    (P : ProbabilityMeasure ℝ) (hP : IsRootIntervalSupported P) :
    (probabilityMeasureToRootInterval P hP).toFiniteMeasure =
      P.toFiniteMeasure.comap ((↑) : RootInterval → ℝ) := by
  rfl

theorem probabilityMeasure_toFinite_mem_comap_support
    (P : ProbabilityMeasure ℝ) (hP : IsRootIntervalSupported P) :
    P.toFiniteMeasure ∈
      {Q : FiniteMeasure ℝ |
        Q (range ((↑) : RootInterval → ℝ))ᶜ = 0} := by
  change P.toFiniteMeasure (range ((↑) : RootInterval → ℝ))ᶜ = 0
  rw [FiniteMeasure.null_iff_toMeasure_null]
  change (P : Measure ℝ) (range ((↑) : RootInterval → ℝ))ᶜ = 0
  have hcompl : (P : Measure ℝ) RootIntervalᶜ = 0 :=
    (prob_compl_eq_zero_iff measurableSet_Icc).2 hP
  simpa only [Subtype.range_val] using! hcompl

/-- Weak convergence is preserved when supported measures on `ℝ` are
viewed as measures on the closed subtype `[-1,1]`. -/
theorem tendsto_probabilityMeasure_toRootInterval
    {J : Type*} {L : Filter J} {P : J → ProbabilityMeasure ℝ}
    {P₀ : ProbabilityMeasure ℝ} (hP : Tendsto P L (nhds P₀))
    (hs : ∀ n, IsRootIntervalSupported (P n))
    (hs₀ : IsRootIntervalSupported P₀) :
    Tendsto (fun n ↦ probabilityMeasureToRootInterval (P n) (hs n)) L
      (nhds (probabilityMeasureToRootInterval P₀ hs₀)) := by
  refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr ?_
  intro f
  let proj : C(ℝ, RootInterval) :=
    ⟨projIcc (-1 : ℝ) 1 (by norm_num), continuous_projIcc⟩
  let F : ℝ →ᵇ ℝ := f.compContinuous proj
  have hF :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hP) F
  have hintegral (Q : ProbabilityMeasure ℝ)
      (hQ : IsRootIntervalSupported Q) :
      (∫ t, f t ∂(probabilityMeasureToRootInterval Q hQ :
        Measure RootInterval)) = ∫ x, F x ∂(Q : Measure ℝ) := by
    change (∫ t : RootInterval, f t ∂(Measure.comap
      ((↑) : RootInterval → ℝ) (Q : Measure ℝ))) = ∫ x, F x ∂(Q : Measure ℝ)
    have hfun : (fun t : RootInterval ↦ f t) =
        fun t : RootInterval ↦ F (t : ℝ) := by
      funext t
      simp only [F, proj, BoundedContinuousFunction.compContinuous_apply]
      simp [projIcc, t.2.1, t.2.2]
    rw [hfun, integral_subtype_comap measurableSet_Icc (fun x : ℝ ↦ F x)]
    have hmem : ∀ᵐ x ∂(Q : Measure ℝ), x ∈ RootInterval :=
      (mem_ae_iff_prob_eq_one measurableSet_Icc).2 hQ
    rw [Measure.restrict_eq_self_of_ae_mem hmem]
  simpa only [hintegral] using! hF

/-- The `L¹` logarithmic potential of a supported probability measure. -/
def logarithmicPotentialLp (a b : ℝ) (hab : a ≤ b)
    (P : ProbabilityMeasure ℝ) (hP : IsRootIntervalSupported P) :
    Lp ℝ 1 (volume.restrict (Icc a b)) :=
  ∫ t, logKernelLp a b t.1 hab ∂(probabilityMeasureToRootInterval P hP :
    Measure RootInterval)

/-- The subtype definition of `logarithmicPotentialLp` is the ordinary
Bochner integral of the kernel against the original supported measure on
`ℝ`. -/
theorem logarithmicPotentialLp_eq_integral
    {a b : ℝ} (hab : a ≤ b) (P : ProbabilityMeasure ℝ)
    (hP : IsRootIntervalSupported P) :
    logarithmicPotentialLp a b hab P hP =
      ∫ t : ℝ, logKernelLp a b t hab ∂(P : Measure ℝ) := by
  rw [logarithmicPotentialLp]
  change (∫ t : RootInterval, logKernelLp a b t.1 hab ∂(Measure.comap
    ((↑) : RootInterval → ℝ) (P : Measure ℝ))) =
      ∫ t : ℝ, logKernelLp a b t hab ∂(P : Measure ℝ)
  rw [integral_subtype_comap measurableSet_Icc
    (fun t : ℝ ↦ logKernelLp a b t hab)]
  have hmem : ∀ᵐ t ∂(P : Measure ℝ), t ∈ RootInterval :=
    (mem_ae_iff_prob_eq_one measurableSet_Icc).2 hP
  rw [Measure.restrict_eq_self_of_ae_mem hmem]

/-- Full weak-to-`L¹` convergence for probability measures on `ℝ`
supported on `[-1,1]`. -/
theorem tendsto_logarithmicPotentialLp_of_weak
    {J : Type*} {L : Filter J} {P : J → ProbabilityMeasure ℝ}
    {P₀ : ProbabilityMeasure ℝ} (hP : Tendsto P L (nhds P₀))
    (hs : ∀ n, IsRootIntervalSupported (P n))
    (hs₀ : IsRootIntervalSupported P₀) {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun n ↦ logarithmicPotentialLp a b hab (P n) (hs n)) L
      (nhds (logarithmicPotentialLp a b hab P₀ hs₀)) := by
  exact tendsto_integral_logKernelLp_of_tendsto_rootInterval
    (tendsto_probabilityMeasure_toRootInterval hP hs hs₀) hab

/-- The same result in the direct integral form used in the manuscript. -/
theorem tendsto_integral_logKernelLp_of_weak_of_supported
    {J : Type*} {L : Filter J} {P : J → ProbabilityMeasure ℝ}
    {P₀ : ProbabilityMeasure ℝ} (hP : Tendsto P L (nhds P₀))
    (hs : ∀ n, IsRootIntervalSupported (P n))
    (hs₀ : IsRootIntervalSupported P₀) {a b : ℝ} (hab : a ≤ b) :
    Tendsto
      (fun n ↦ ∫ t : ℝ, logKernelLp a b t hab ∂(P n : Measure ℝ)) L
      (nhds (∫ t : ℝ, logKernelLp a b t hab ∂(P₀ : Measure ℝ))) := by
  simpa only [logarithmicPotentialLp_eq_integral] using!
    (tendsto_logarithmicPotentialLp_of_weak hP hs hs₀ hab)

/-- An explicit norm formulation: the preceding convergence is exactly
convergence to zero of the `L¹` distance. -/
theorem tendsto_norm_logarithmicPotentialLp_sub_of_weak
    {J : Type*} {L : Filter J} {P : J → ProbabilityMeasure ℝ}
    {P₀ : ProbabilityMeasure ℝ} (hP : Tendsto P L (nhds P₀))
    (hs : ∀ n, IsRootIntervalSupported (P n))
    (hs₀ : IsRootIntervalSupported P₀) {a b : ℝ} (hab : a ≤ b) :
    Tendsto
      (fun n ↦ ‖logarithmicPotentialLp a b hab (P n) (hs n) -
        logarithmicPotentialLp a b hab P₀ hs₀‖) L (nhds 0) :=
  tendsto_iff_norm_sub_tendsto_zero.mp
    (tendsto_logarithmicPotentialLp_of_weak hP hs hs₀ hab)

end

end Erdos1038
