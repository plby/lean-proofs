import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite Stieltjes layer cake for the upper transition

This file isolates the exact finite-family identity used for the upper
transition in the minor-arc argument.  The convention is deliberately
explicit: `finiteSharpTail s a w t` includes a shot when `t ≤ a i`, and
`finiteTransitionSum` includes both endpoints.  The upper endpoint is
harmless because the identity assumes `h r₁ = 0`; a separate corollary
replaces the closed transition by the strict one when no shot lies at the
lower endpoint.

The final two results are the Bochner/Minkowski estimate and its uniform
vanishing consequence.  They apply in any real Banach space, in particular
to the `L²` space occurring in the manuscript.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

variable {ι E : Type*} [NormedAddCommGroup E]

/-- The finite sharp tail with the endpoint convention `t ≤ a i`. -/
def finiteSharpTail (s : Finset ι) (a : ι → ℝ) (w : ι → E) (t : ℝ) : E :=
  ∑ i ∈ s, if t ≤ a i then w i else 0

/-- A finite sharp tail is a strongly measurable step function of its
threshold.  This is the finite-family measurability input behind the
Bochner formulation. -/
theorem stronglyMeasurable_finiteSharpTail
    (s : Finset ι) (a : ι → ℝ) (w : ι → E) :
    StronglyMeasurable (finiteSharpTail s a w) := by
  unfold finiteSharpTail
  let f : ι → ℝ → E := fun i t ↦ if t ≤ a i then w i else 0
  have hsum : StronglyMeasurable (∑ i ∈ s, f i) := by
    apply Finset.stronglyMeasurable_sum s
    intro i _hi
    have hw : StronglyMeasurable (fun _t : ℝ ↦ w i) := stronglyMeasurable_const
    have hz : StronglyMeasurable (fun _t : ℝ ↦ (0 : E)) := stronglyMeasurable_const
    exact StronglyMeasurable.ite (p := fun t : ℝ ↦ t ≤ a i) measurableSet_Iic hw hz
  convert! hsum using 1
  funext t
  simp only [f, Finset.sum_apply]

variable [NormedSpace ℝ E]

/-- The transition-weighted sum, including both endpoints.

In applications `h r₁ = 0`, so the terms with `a i = r₁` vanish. -/
def finiteTransitionSum (s : Finset ι) (a : ι → ℝ) (w : ι → E)
    (h : ℝ → ℝ) (r₀ r₁ : ℝ) : E :=
  ∑ i ∈ s, if r₀ ≤ a i ∧ a i ≤ r₁ then h (a i) • w i else 0

/-- The strict transition-weighted sum used in the displayed manuscript
formula.  The distinction from `finiteTransitionSum` is solely at the two
endpoints. -/
def finiteStrictTransitionSum (s : Finset ι) (a : ι → ℝ) (w : ι → E)
    (h : ℝ → ℝ) (r₀ r₁ : ℝ) : E :=
  ∑ i ∈ s, if r₀ < a i ∧ a i < r₁ then h (a i) • w i else 0

private theorem intervalIntegrable_indicator_smul_const
    {h' : ℝ → ℝ} {r₀ r₁ c : ℝ} (w₀ : E)
    (hh' : IntervalIntegrable h' volume r₀ r₁) :
    IntervalIntegrable
      (fun t ↦ if t ≤ c then h' t • w₀ else 0) volume r₀ r₁ := by
  have hsmul : IntervalIntegrable (fun t ↦ h' t • w₀) volume r₀ r₁ :=
    ⟨hh'.1.smul_const w₀, hh'.2.smul_const w₀⟩
  have hmeas : MeasurableSet {t : ℝ | t ≤ c} := measurableSet_Iic
  constructor
  · simpa only [Set.indicator, Set.mem_setOf_eq] using! hsmul.1.indicator hmeas
  · simpa only [Set.indicator, Set.mem_setOf_eq] using! hsmul.2.indicator hmeas

/-- Multiplying a finite sharp tail by an interval-integrable scalar
derivative produces a genuine Bochner-integrable interval map. -/
theorem intervalIntegrable_smul_finiteSharpTail
    (s : Finset ι) (a : ι → ℝ) (w : ι → E)
    {h' : ℝ → ℝ} {r₀ r₁ : ℝ}
    (hh' : IntervalIntegrable h' volume r₀ r₁) :
    IntervalIntegrable
      (fun t ↦ h' t • finiteSharpTail s a w t) volume r₀ r₁ := by
  simp only [finiteSharpTail, Finset.smul_sum]
  have hEach : ∀ i ∈ s,
      IntervalIntegrable
        (fun t ↦ h' t • (if t ≤ a i then w i else 0)) volume r₀ r₁ := by
    intro i _hi
    simpa only [smul_ite, smul_zero] using!
      intervalIntegrable_indicator_smul_const (w i) hh'
  let f : ι → ℝ → E := fun i t ↦ h' t • (if t ≤ a i then w i else 0)
  have hsum : IntervalIntegrable (∑ i ∈ s, f i) volume r₀ r₁ :=
    IntervalIntegrable.sum s (by simpa only [f] using! hEach)
  exact hsum.congr fun t _ht ↦ by simp only [f, Finset.sum_apply]

private theorem single_shot_layerCake
    [CompleteSpace E]
    {h h' : ℝ → ℝ} {r₀ r₁ c : ℝ} (w₀ : E)
    (hr : r₀ ≤ r₁) (hr₁ : h r₁ = 0)
    (hderiv : ∀ t ∈ Icc r₀ r₁, HasDerivAt h (h' t) t)
    (hh' : IntervalIntegrable h' volume r₀ r₁) :
    h r₀ • (if r₀ ≤ c then w₀ else 0) +
        ∫ t in r₀..r₁, h' t • (if t ≤ c then w₀ else 0) =
      if r₀ ≤ c ∧ c ≤ r₁ then h c • w₀ else 0 := by
  have hbase :
      (∫ t in r₀..r₁, h' t) = h r₁ - h r₀ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht ↦ hderiv t (by simpa [uIcc_of_le hr] using! ht)) hh'
  rw [show (fun t ↦ h' t • (if t ≤ c then w₀ else 0)) =
      (fun t ↦ if t ≤ c then h' t • w₀ else 0) by
        funext t
        split_ifs <;> simp_all]
  rcases lt_or_ge c r₀ with hc₀ | hr₀c
  · have hzero :
        (∫ t in r₀..r₁, if t ≤ c then h' t • w₀ else 0) = 0 := by
      calc
        (∫ t in r₀..r₁, if t ≤ c then h' t • w₀ else 0) =
            ∫ _t in r₀..r₁, (0 : E) := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [uIcc_of_le hr] at ht
          simp [not_le.mpr (hc₀.trans_le ht.1)]
        _ = 0 := intervalIntegral.integral_zero
    rw [hzero]
    simp [not_le.mpr hc₀]
  rcases le_or_gt c r₁ with hc₁ | hr₁c
  · have hcMem : c ∈ Icc r₀ r₁ := ⟨hr₀c, hc₁⟩
    have hindicator :
        (∫ t in r₀..r₁, if t ≤ c then h' t • w₀ else 0) =
          ∫ t in r₀..c, h' t • w₀ := by
      simpa only [Set.indicator, Set.mem_setOf_eq] using!
        (intervalIntegral.integral_indicator
          (f := fun t ↦ h' t • w₀) (a₁ := r₀) (a₂ := c) (a₃ := r₁) hcMem)
    have hh'sub : IntervalIntegrable h' volume r₀ c :=
      hh'.mono_set (by
        rw [uIcc_of_le hr, uIcc_of_le hr₀c]
        exact Icc_subset_Icc_right hc₁)
    have hprimitive : (∫ t in r₀..c, h' t) = h c - h r₀ :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t ht ↦ hderiv t (by
          rw [uIcc_of_le hr₀c] at ht
          exact ⟨ht.1, ht.2.trans hc₁⟩)) hh'sub
    rw [hindicator, intervalIntegral.integral_smul_const, hprimitive]
    simp only [hr₀c, hc₁, and_self, if_true]
    module
  · have hall :
        (∫ t in r₀..r₁, if t ≤ c then h' t • w₀ else 0) =
          ∫ t in r₀..r₁, h' t • w₀ := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht₁ : t ≤ r₁ := by
        rw [uIcc_of_le hr] at ht
        exact ht.2
      simp [ht₁.trans hr₁c.le]
    rw [hall, intervalIntegral.integral_smul_const, hbase, hr₁]
    simp [hr₀c, not_le.mpr hr₁c]

/-- Exact finite Stieltjes layer-cake identity.

The sharp tail includes equality at its threshold.  Consequently the
transition sum includes the lower endpoint.  It also syntactically includes
the upper endpoint, but those terms are zero because `h r₁ = 0`. -/
theorem finite_stieltjes_layerCake
    [CompleteSpace E]
    (s : Finset ι) (a : ι → ℝ) (w : ι → E)
    {h h' : ℝ → ℝ} {r₀ r₁ : ℝ}
    (hr : r₀ ≤ r₁) (hr₁ : h r₁ = 0)
    (hderiv : ∀ t ∈ Icc r₀ r₁, HasDerivAt h (h' t) t)
    (hh' : IntervalIntegrable h' volume r₀ r₁) :
    h r₀ • finiteSharpTail s a w r₀ +
        ∫ t in r₀..r₁, h' t • finiteSharpTail s a w t =
      finiteTransitionSum s a w h r₀ r₁ := by
  simp only [finiteSharpTail, finiteTransitionSum, Finset.smul_sum]
  have hint : ∀ i ∈ s,
      IntervalIntegrable
        (fun t ↦ h' t • (if t ≤ a i then w i else 0)) volume r₀ r₁ := by
    intro i _hi
    simpa only [smul_ite, smul_zero] using!
      intervalIntegrable_indicator_smul_const (w i) hh'
  rw [intervalIntegral.integral_finset_sum hint, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i hi ↦
    single_shot_layerCake (w i) hr hr₁ hderiv hh'

/-- Under the no-lower-boundary hypothesis, the closed-endpoint identity is
exactly the manuscript's strict transition sum.  No condition at the upper
endpoint is needed, since `h r₁ = 0`. -/
theorem finiteTransitionSum_eq_strict
    (s : Finset ι) (a : ι → ℝ) (w : ι → E)
    (h : ℝ → ℝ) {r₀ r₁ : ℝ} (hr₁ : h r₁ = 0)
    (hnoLower : ∀ i ∈ s, a i ≠ r₀) :
    finiteTransitionSum s a w h r₀ r₁ =
      finiteStrictTransitionSum s a w h r₀ r₁ := by
  simp only [finiteTransitionSum, finiteStrictTransitionSum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h₀ : r₀ ≤ a i
  · have h₀' : r₀ < a i := lt_of_le_of_ne h₀ (Ne.symm (hnoLower i hi))
    by_cases h₁ : a i < r₁
    · rw [if_pos ⟨h₀, h₁.le⟩, if_pos ⟨h₀', h₁⟩]
    · have hr₁i : r₁ ≤ a i := le_of_not_gt h₁
      rcases hr₁i.eq_or_lt with hai | hai
      · have haeq : a i = r₁ := hai.symm
        rw [if_pos ⟨h₀, haeq.le⟩,
          if_neg (fun hs ↦ h₁ hs.2), haeq, hr₁, zero_smul]
      · rw [if_neg (fun hc ↦ (not_le.mpr hai) hc.2),
          if_neg (fun hs ↦ h₁ hs.2)]
  · have h₀' : ¬ r₀ < a i := fun hlt ↦ h₀ hlt.le
    rw [if_neg (fun hc ↦ h₀ hc.1), if_neg (fun hs ↦ h₀' hs.1)]

/-- Exact strict-endpoint version of the finite layer-cake identity. -/
theorem finite_stieltjes_layerCake_strict
    [CompleteSpace E]
    (s : Finset ι) (a : ι → ℝ) (w : ι → E)
    {h h' : ℝ → ℝ} {r₀ r₁ : ℝ}
    (hr : r₀ ≤ r₁) (hr₁ : h r₁ = 0)
    (hderiv : ∀ t ∈ Icc r₀ r₁, HasDerivAt h (h' t) t)
    (hh' : IntervalIntegrable h' volume r₀ r₁)
    (hnoLower : ∀ i ∈ s, a i ≠ r₀) :
    h r₀ • finiteSharpTail s a w r₀ +
        ∫ t in r₀..r₁, h' t • finiteSharpTail s a w t =
      finiteStrictTransitionSum s a w h r₀ r₁ := by
  rw [finite_stieltjes_layerCake s a w hr hr₁ hderiv hh',
    finiteTransitionSum_eq_strict s a w h hr₁ hnoLower]

/-! The following estimate no longer needs completeness: the integral is
already assumed to be Bochner integrable. -/

/-- Bochner/Minkowski estimate for a transition layer cake.

`M` is any uniform norm envelope for `F` on `[r₀,r₁]`. -/
theorem norm_layerCake_le_uniform
    (F : ℝ → E) {h h' : ℝ → ℝ} {r₀ r₁ M : ℝ}
    (hr : r₀ ≤ r₁)
    (hF : ∀ t ∈ Icc r₀ r₁, ‖F t‖ ≤ M)
    (hh' : IntervalIntegrable (fun t ↦ |h' t|) volume r₀ r₁)
    (hbochner : IntervalIntegrable (fun t ↦ h' t • F t) volume r₀ r₁) :
    ‖h r₀ • F r₀ + ∫ t in r₀..r₁, h' t • F t‖ ≤
      (|h r₀| + ∫ t in r₀..r₁, |h' t|) * M := by
  have hr₀mem : r₀ ∈ Icc r₀ r₁ := ⟨le_rfl, hr⟩
  have hcomparison : IntervalIntegrable (fun t ↦ |h' t| * M) volume r₀ r₁ :=
    hh'.mul_const M
  have hnorm : IntervalIntegrable (fun t ↦ ‖h' t • F t‖) volume r₀ r₁ :=
    hbochner.norm
  calc
    ‖h r₀ • F r₀ + ∫ t in r₀..r₁, h' t • F t‖
        ≤ ‖h r₀ • F r₀‖ + ‖∫ t in r₀..r₁, h' t • F t‖ := norm_add_le _ _
    _ ≤ |h r₀| * M + ∫ t in r₀..r₁, ‖h' t • F t‖ := by
      gcongr
      · simpa only [norm_smul, Real.norm_eq_abs] using!
          mul_le_mul_of_nonneg_left (hF r₀ hr₀mem) (abs_nonneg (h r₀))
      · exact intervalIntegral.norm_integral_le_integral_norm hr
    _ ≤ |h r₀| * M + ∫ t in r₀..r₁, |h' t| * M := by
      gcongr
      exact intervalIntegral.integral_mono_on hr hnorm hcomparison fun t ht ↦ by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hF t ht) (abs_nonneg (h' t))
    _ = (|h r₀| + ∫ t in r₀..r₁, |h' t|) * M := by
      rw [intervalIntegral.integral_mul_const]
      ring

/-- Uniformly vanishing sharp tails have a vanishing transition layer cake.

For the manuscript, take `E = L²(𝕋)`, replace `F N t` by
`F_N(t) / log N`, and let `M N` be the uniform `L²` envelope. -/
theorem tendsto_norm_layerCake_zero_of_uniform
    (F : ℕ → ℝ → E) (M : ℕ → ℝ)
    {h h' : ℝ → ℝ} {r₀ r₁ : ℝ}
    (hr : r₀ ≤ r₁)
    (hF : ∀ N t, t ∈ Icc r₀ r₁ → ‖F N t‖ ≤ M N)
    (hh' : IntervalIntegrable (fun t ↦ |h' t|) volume r₀ r₁)
    (hbochner : ∀ N,
      IntervalIntegrable (fun t ↦ h' t • F N t) volume r₀ r₁)
    (hMzero : Tendsto M atTop (nhds 0)) :
    Tendsto
      (fun N ↦ ‖h r₀ • F N r₀ + ∫ t in r₀..r₁, h' t • F N t‖)
      atTop (nhds 0) := by
  let C : ℝ := |h r₀| + ∫ t in r₀..r₁, |h' t|
  apply squeeze_zero
  · exact fun N ↦ norm_nonneg _
  · intro N
    exact norm_layerCake_le_uniform (F N) hr (hF N) hh' (hbochner N)
  · simpa [C] using! hMzero.const_mul C

/-- The normalized form used verbatim in the minor-arc argument.

The hypothesis says that `M N` dominates
`sup_{t ∈ [r₀,r₁]} ‖F N t‖ / L N`; if this envelope tends to zero,
then the transition layer cake divided by the same scale tends to zero. -/
theorem tendsto_norm_layerCake_div_zero_of_uniform
    (F : ℕ → ℝ → E) (L M : ℕ → ℝ)
    {h h' : ℝ → ℝ} {r₀ r₁ : ℝ}
    (hr : r₀ ≤ r₁)
    (hL : ∀ N, 0 < L N)
    (hF : ∀ N t, t ∈ Icc r₀ r₁ → ‖F N t‖ / L N ≤ M N)
    (hh' : IntervalIntegrable (fun t ↦ |h' t|) volume r₀ r₁)
    (hbochner : ∀ N,
      IntervalIntegrable (fun t ↦ h' t • F N t) volume r₀ r₁)
    (hMzero : Tendsto M atTop (nhds 0)) :
    Tendsto
      (fun N ↦
        ‖h r₀ • F N r₀ + ∫ t in r₀..r₁, h' t • F N t‖ / L N)
      atTop (nhds 0) := by
  let C : ℝ := |h r₀| + ∫ t in r₀..r₁, |h' t|
  apply squeeze_zero
  · intro N
    exact div_nonneg (norm_nonneg _) (hL N).le
  · intro N
    have hbound : ∀ t ∈ Icc r₀ r₁, ‖F N t‖ ≤ L N * M N := by
      intro t ht
      simpa only [mul_comm] using! (div_le_iff₀ (hL N)).mp (hF N t ht)
    have hraw := norm_layerCake_le_uniform (F N) (h := h) (h' := h')
      hr hbound hh' (hbochner N)
    calc
      ‖h r₀ • F N r₀ + ∫ t in r₀..r₁, h' t • F N t‖ / L N
          ≤ (C * (L N * M N)) / L N :=
        (div_le_div_iff_of_pos_right (hL N)).2 (by simpa [C] using! hraw)
      _ = C * M N := by
        field_simp [(hL N).ne']
  · simpa [C] using! hMzero.const_mul C

end

end Erdos1002
