/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.BrownianDyadic

/-!
# A Brownian strip block with endpoint recentering

The dyadic chaining estimate gives a short Brownian path which stays in a
small symmetric strip with probability greater than one half.  Centered
Gaussian symmetry then shows that imposing either strict sign on the final
endpoint still leaves positive probability.  Choosing the sign opposite to
the current location produces a uniform recentering block: a point in the
central half of a strip remains in the full strip and returns to the central
half.

This is the one-block probabilistic input for the deterministic-time Markov
iteration of strip survival carried out in `BrownianIteration`.  That module
factors the countable path event through the past/future process measurable
spaces in `IsPreBrownianReal.indepFun_shift`.
-/

open scoped ENNReal NNReal Topology

namespace Erdos1165.BrownianRecenter

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open BrownianDyadic BrownianReflection

variable {Omega : Type*} {mOmega : MeasurableSpace Omega}
    {P : Measure Omega} {B : ℝ≥0 → Omega → ℝ}

/-- The small radius used inside a full strip of radius `r`. -/
def innerRadius (r : ℝ≥0) : ℝ≥0 := r / 2

/-- Duration of one recentering block.  It is exactly
`(r/2)^2 / 2048 = r^2 / 8192`. -/
def recenterHorizon (r : ℝ≥0) : ℝ≥0 :=
  dyadicHorizon (innerRadius r)

/-- The short path obeys every dyadic increment cutoff and has a negative
endpoint. -/
def negativeRecenterEvent (B : ℝ≥0 → Omega → ℝ) (r : ℝ≥0) : Set Omega :=
  (dyadicBad B (recenterHorizon r) (geometricCutoff (innerRadius r)))ᶜ ∩
    {omega | B (recenterHorizon r) omega < 0}

/-- The reflected positive-endpoint version. -/
def positiveRecenterEvent (B : ℝ≥0 → Omega → ℝ) (r : ℝ≥0) : Set Omega :=
  (dyadicBad B (recenterHorizon r) (geometricCutoff (innerRadius r)))ᶜ ∩
    {omega | 0 < B (recenterHorizon r) omega}

lemma IsPreBrownianReal.nullMeasurableSet_negativeRecenterEvent
    (hB : IsPreBrownianReal B P) (r : ℝ≥0) :
    NullMeasurableSet (negativeRecenterEvent B r) P := by
  unfold negativeRecenterEvent
  exact (IsPreBrownianReal.nullMeasurableSet_dyadicBad hB _ _).compl.inter
    ((hB.aemeasurable _).nullMeasurableSet_preimage measurableSet_Iio)

lemma IsPreBrownianReal.nullMeasurableSet_positiveRecenterEvent
    (hB : IsPreBrownianReal B P) (r : ℝ≥0) :
    NullMeasurableSet (positiveRecenterEvent B r) P := by
  unfold positiveRecenterEvent
  exact (IsPreBrownianReal.nullMeasurableSet_dyadicBad hB _ _).compl.inter
    ((hB.aemeasurable _).nullMeasurableSet_preimage measurableSet_Ioi)

lemma innerRadius_pos {r : ℝ≥0} (hr : 0 < r) : 0 < innerRadius r := by
  unfold innerRadius
  positivity

lemma recenterHorizon_pos {r : ℝ≥0} (hr : 0 < r) :
    0 < recenterHorizon r := by
  unfold recenterHorizon dyadicHorizon
  unfold innerRadius
  positivity

lemma recenterHorizon_eq {r : ℝ≥0} :
    recenterHorizon r = r ^ 2 / 8192 := by
  apply NNReal.eq
  simp only [recenterHorizon, innerRadius, dyadicHorizon, NNReal.coe_div,
    NNReal.coe_pow, NNReal.coe_ofNat]
  ring

/-! ## A uniform numerical probability gap -/

lemma tsum_geometric_level_majorant_le_two_fifths :
    (∑' k : ℕ,
      2 * Real.exp (-16) * (2 * Real.exp (-2)) ^ k) ≤ (2 : ℝ) / 5 := by
  have hq_nonneg : 0 ≤ 2 * Real.exp (-2) := by positivity
  have hq_lt : ‖2 * Real.exp (-2)‖ < 1 := by
    rw [Real.norm_of_nonneg hq_nonneg]
    exact two_mul_exp_neg_two_le_two_thirds.trans_lt (by norm_num)
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hq_lt]
  rw [inv_eq_one_div, mul_one_div]
  have hden : 0 < 1 - 2 * Real.exp (-2) := by
    nlinarith [two_mul_exp_neg_two_le_two_thirds]
  rw [div_le_iff₀ hden]
  nlinarith [two_mul_exp_neg_two_le_two_thirds,
    two_mul_exp_neg_sixteen_le_two_seventeenths]

lemma tsum_ofReal_geometric_failure_le_two_fifths :
    (∑' k : ℕ, ENNReal.ofReal
      ((2 ^ k : ℝ) *
        (2 * Real.exp (-(16 * ((9 : ℝ) / 8) ^ k))))) ≤
      (2 : ℝ≥0∞) / 5 := by
  calc
    (∑' k : ℕ, ENNReal.ofReal
        ((2 ^ k : ℝ) *
          (2 * Real.exp (-(16 * ((9 : ℝ) / 8) ^ k)))))
        ≤ ∑' k : ℕ, ENNReal.ofReal
          (2 * Real.exp (-16) * (2 * Real.exp (-2)) ^ k) := by
            apply ENNReal.tsum_le_tsum
            intro k
            exact ENNReal.ofReal_le_ofReal (geometric_level_bound_le k)
    _ = ENNReal.ofReal
          (∑' k : ℕ, 2 * Real.exp (-16) * (2 * Real.exp (-2)) ^ k) := by
      symm
      exact ENNReal.ofReal_tsum_of_nonneg
        (fun _ ↦ by positivity) summable_geometric_level_majorant
    _ ≤ (2 : ℝ≥0∞) / 5 := by
      have hnonneg : 0 ≤
          ∑' k : ℕ, 2 * Real.exp (-16) * (2 * Real.exp (-2)) ^ k :=
        tsum_nonneg fun _ ↦ by positivity
      rw [ENNReal.ofReal_le_iff_le_toReal (by finiteness)]
      norm_num
      exact tsum_geometric_level_majorant_le_two_fifths

/-- The dyadic failure event has the uniform numerical bound `2/5`. -/
theorem IsPreBrownianReal.measure_dyadicBad_geometric_le_two_fifths
    (hB : IsPreBrownianReal B P) {r : ℝ≥0} (hr : 0 < r) :
    P (dyadicBad B (dyadicHorizon r) (geometricCutoff r)) ≤
      (2 : ℝ≥0∞) / 5 := by
  exact (IsPreBrownianReal.measure_dyadicBad_le_tsum hB
    (dyadicHorizon r) (geometricCutoff_nonneg r)).trans (by
      simpa only [geometricCutoff_exponent hr] using
        tsum_ofReal_geometric_failure_le_two_fifths)

/-- A set of measure strictly less than one half cannot cover a half-space;
the part of that half-space outside the set therefore has positive measure. -/
lemma measure_compl_inter_pos_of_lt_half
    {D S : Set Omega} (hD : P D < (1 : ℝ≥0∞) / 2)
    (hS : P S = (1 : ℝ≥0∞) / 2) :
    0 < P (Dᶜ ∩ S) := by
  have hsubset : S ⊆ D ∪ (Dᶜ ∩ S) := by
    intro omega homega
    by_cases hmem : omega ∈ D
    · exact Or.inl hmem
    · exact Or.inr ⟨hmem, homega⟩
  have hle : P S ≤ P D + P (Dᶜ ∩ S) :=
    (measure_mono hsubset).trans (measure_union_le _ _)
  by_contra hnot
  have hzero : P (Dᶜ ∩ S) = 0 := by
    exact nonpos_iff_eq_zero.mp (le_of_not_gt hnot)
  have hhalf_le : (1 : ℝ≥0∞) / 2 ≤ P D := by
    simpa [hS, hzero] using hle
  exact (not_le_of_gt hD) hhalf_le

/-- Quantitative form of the preceding covering argument. -/
lemma one_tenth_le_measure_compl_inter_of_le_two_fifths
    {D S : Set Omega} [IsProbabilityMeasure P]
    (hD : P D ≤ (2 : ℝ≥0∞) / 5)
    (hS : P S = (1 : ℝ≥0∞) / 2) :
    (1 : ℝ≥0∞) / 10 ≤ P (Dᶜ ∩ S) := by
  let G : Set Omega := Dᶜ ∩ S
  have hsubset : S ⊆ D ∪ G := by
    intro omega homega
    by_cases hmem : omega ∈ D
    · exact Or.inl hmem
    · exact Or.inr ⟨hmem, homega⟩
  have hle : P S ≤ P D + P G :=
    (measure_mono hsubset).trans (measure_union_le _ _)
  have hDtop : P D ≠ ∞ := measure_ne_top P D
  have hGtop : P G ≠ ∞ := measure_ne_top P G
  have hsumtop : P D + P G ≠ ∞ := ENNReal.add_ne_top.2 ⟨hDtop, hGtop⟩
  have hleReal : (1 : ℝ) / 2 ≤ (P D).toReal + (P G).toReal := by
    have h := (ENNReal.toReal_le_toReal (by finiteness) hsumtop).2 hle
    rw [hS, ENNReal.toReal_add hDtop hGtop] at h
    norm_num at h ⊢
    exact h
  have hDReal : (P D).toReal ≤ (2 : ℝ) / 5 := by
    have h := (ENNReal.toReal_le_toReal hDtop (by finiteness)).2 hD
    norm_num at h ⊢
    exact h
  have hreal : (1 : ℝ) / 10 ≤ (P G).toReal := by linarith
  have hofReal : ENNReal.ofReal ((1 : ℝ) / 10) ≤ P G :=
    (ENNReal.ofReal_le_iff_le_toReal hGtop).2 hreal
  simpa [G] using hofReal

/-- A Brownian block can stay in the small strip and finish on the negative
side with positive probability. -/
theorem IsBrownianReal.measure_negativeRecenterEvent_pos
    (hB : IsBrownianReal B P) {r : ℝ≥0} (hr : 0 < r) :
    0 < P (negativeRecenterEvent B r) := by
  unfold negativeRecenterEvent
  apply measure_compl_inter_pos_of_lt_half
  · exact IsPreBrownianReal.measure_dyadicBad_geometric_lt_half
      hB.toIsPreBrownianReal (innerRadius_pos hr)
  · simpa [div_eq_mul_inv] using
      (IsPreBrownianReal.measure_eval_lt_zero hB.toIsPreBrownianReal
        (recenterHorizon_pos hr))

/-- The positive-endpoint reflected block has positive probability as well. -/
theorem IsBrownianReal.measure_positiveRecenterEvent_pos
    (hB : IsBrownianReal B P) {r : ℝ≥0} (hr : 0 < r) :
    0 < P (positiveRecenterEvent B r) := by
  unfold positiveRecenterEvent
  apply measure_compl_inter_pos_of_lt_half
  · exact IsPreBrownianReal.measure_dyadicBad_geometric_lt_half
      hB.toIsPreBrownianReal (innerRadius_pos hr)
  · simpa [div_eq_mul_inv] using
      (IsPreBrownianReal.measure_eval_pos hB.toIsPreBrownianReal
        (recenterHorizon_pos hr))

/-- Uniform quantitative version: the negative recentering block has
probability at least `1/10`, independently of the radius. -/
theorem IsBrownianReal.one_tenth_le_measure_negativeRecenterEvent
    (hB : IsBrownianReal B P) {r : ℝ≥0} (hr : 0 < r) :
    (1 : ℝ≥0∞) / 10 ≤ P (negativeRecenterEvent B r) := by
  let _ : IsProbabilityMeasure P :=
    hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  unfold negativeRecenterEvent
  apply one_tenth_le_measure_compl_inter_of_le_two_fifths
  · exact IsPreBrownianReal.measure_dyadicBad_geometric_le_two_fifths
      hB.toIsPreBrownianReal (innerRadius_pos hr)
  · simpa [div_eq_mul_inv] using
      (IsPreBrownianReal.measure_eval_lt_zero hB.toIsPreBrownianReal
        (recenterHorizon_pos hr))

/-- Uniform quantitative version for the positive recentering block. -/
theorem IsBrownianReal.one_tenth_le_measure_positiveRecenterEvent
    (hB : IsBrownianReal B P) {r : ℝ≥0} (hr : 0 < r) :
    (1 : ℝ≥0∞) / 10 ≤ P (positiveRecenterEvent B r) := by
  let _ : IsProbabilityMeasure P :=
    hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  unfold positiveRecenterEvent
  apply one_tenth_le_measure_compl_inter_of_le_two_fifths
  · exact IsPreBrownianReal.measure_dyadicBad_geometric_le_two_fifths
      hB.toIsPreBrownianReal (innerRadius_pos hr)
  · simpa [div_eq_mul_inv] using
      (IsPreBrownianReal.measure_eval_pos hB.toIsPreBrownianReal
        (recenterHorizon_pos hr))

/-- Pathwise negative-endpoint recentering.  If the current point is in the
nonnegative half of the central interval, adding a negative recentering block
stays in `(-r,r)` and finishes in `(-r/2,r/2)`. -/
lemma negativeRecenterEvent_pathwise
    {omega : Omega} {r : ℝ≥0} (hr : 0 < r)
    (hcont : Continuous (B · omega)) (hzero : B 0 omega = 0)
    (homega : omega ∈ negativeRecenterEvent B r)
    {x : ℝ} (hx0 : 0 ≤ x) (hxr : |x| ≤ (r : ℝ) / 2) :
    (∀ t : ℝ≥0, t ≤ recenterHorizon r → |x + B t omega| < (r : ℝ)) ∧
      |x + B (recenterHorizon r) omega| < (r : ℝ) / 2 := by
  have hsmall : omega ∈
      rawStripEvent B (recenterHorizon r) (innerRadius r : ℝ) :=
    mem_rawStripEvent_of_continuous_of_mem_compl_dyadicBad
      (innerRadius_pos hr) hcont hzero homega.1
  have hxle : x ≤ (r : ℝ) / 2 := by
    exact (le_abs_self x).trans hxr
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  constructor
  · intro t ht
    have hBt := (abs_lt.mp (hsmall t ht))
    simp only [innerRadius, NNReal.coe_div, NNReal.coe_ofNat] at hBt
    apply abs_lt.mpr
    constructor <;> linarith
  · have hBt := abs_lt.mp (hsmall (recenterHorizon r) le_rfl)
    simp only [innerRadius, NNReal.coe_div, NNReal.coe_ofNat] at hBt
    have hend : B (recenterHorizon r) omega < 0 := homega.2
    apply abs_lt.mpr
    constructor <;> linarith

/-- Pathwise positive-endpoint recentering for a current point in the
nonpositive half of the central interval. -/
lemma positiveRecenterEvent_pathwise
    {omega : Omega} {r : ℝ≥0} (hr : 0 < r)
    (hcont : Continuous (B · omega)) (hzero : B 0 omega = 0)
    (homega : omega ∈ positiveRecenterEvent B r)
    {x : ℝ} (hx0 : x ≤ 0) (hxr : |x| ≤ (r : ℝ) / 2) :
    (∀ t : ℝ≥0, t ≤ recenterHorizon r → |x + B t omega| < (r : ℝ)) ∧
      |x + B (recenterHorizon r) omega| < (r : ℝ) / 2 := by
  have hsmall : omega ∈
      rawStripEvent B (recenterHorizon r) (innerRadius r : ℝ) :=
    mem_rawStripEvent_of_continuous_of_mem_compl_dyadicBad
      (innerRadius_pos hr) hcont hzero homega.1
  have hxge : -(r : ℝ) / 2 ≤ x := by
    simpa only [neg_div] using (neg_le_of_abs_le hxr)
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  constructor
  · intro t ht
    have hBt := (abs_lt.mp (hsmall t ht))
    simp only [innerRadius, NNReal.coe_div, NNReal.coe_ofNat] at hBt
    apply abs_lt.mpr
    constructor <;> linarith
  · have hBt := abs_lt.mp (hsmall (recenterHorizon r) le_rfl)
    simp only [innerRadius, NNReal.coe_div, NNReal.coe_ofNat] at hBt
    have hend : 0 < B (recenterHorizon r) omega := homega.2
    apply abs_lt.mpr
    constructor <;> linarith

end

end Erdos1165.BrownianRecenter
