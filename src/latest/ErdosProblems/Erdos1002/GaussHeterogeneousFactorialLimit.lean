import ErdosProblems.Erdos1002.GaussHeterogeneousTupleReplacement
import ErdosProblems.Erdos1002.GaussUnmarkedFactorialLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Factorial limits for heterogeneous Gauss approximation windows

The marked point-process argument produces, after fixing a chronological
order, one positive approximation window at each occurrence.  Those
windows need not have the same endpoints.  This module proves the exact
heterogeneous analogue of `tendsto_gaussApproximationTupleSum`.

There are no probabilistic assumptions in the final theorem.  The proof
uses the already proved exponential `psi`-mixing theorem for Gauss digits,
the quantitative one-digit window asymptotic, and the heterogeneous
exact-coordinate-to-digit replacement estimate.  The remaining hypotheses
are deterministic cardinality statements for the retained tuple family.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators ENNReal Topology symmDiff

namespace Erdos1002

noncomputable section

/-! ## Exact heterogeneous tuple sums -/

/-- Sum of exact approximation-coordinate tuple masses, with one fixed
positive window for each coordinate. -/
def gaussHeterogeneousApproximationTupleSum
    {r L : ℕ} (lower upper : Fin r → ℝ)
    (tuples : Finset (Fin r → Fin L)) : ℝ :=
  ∑ t ∈ tuples,
    gaussMeasure.real
      (gaussHeterogeneousApproximationTupleEvent
        (L : ℝ) lower upper (fun i ↦ (t i).1))

/-- Sum of the corresponding one-digit surrogate tuple masses. -/
def gaussHeterogeneousDigitTupleSum
    {r L : ℕ} (lower upper : Fin r → ℝ)
    (tuples : Finset (Fin r → Fin L)) : ℝ :=
  ∑ t ∈ tuples,
    gaussMeasure.real
      (gaussHeterogeneousDigitWindowTupleEvent
        (L : ℝ) lower upper (fun i ↦ (t i).1))

/-- Absolute difference between the two finite tuple sums is bounded by
the sum of the literal symmetric-difference masses. -/
theorem abs_gaussHeterogeneousApproximationTupleSum_sub_digit_le
    {r L : ℕ} (lower upper : Fin r → ℝ)
    (tuples : Finset (Fin r → Fin L)) :
    |gaussHeterogeneousApproximationTupleSum lower upper tuples -
        gaussHeterogeneousDigitTupleSum lower upper tuples| ≤
      ∑ t ∈ tuples,
        gaussMeasure.real
          (gaussHeterogeneousApproximationTupleEvent
              (L : ℝ) lower upper (fun i ↦ (t i).1) ∆
            gaussHeterogeneousDigitWindowTupleEvent
              (L : ℝ) lower upper (fun i ↦ (t i).1)) := by
  classical
  unfold gaussHeterogeneousApproximationTupleSum
    gaussHeterogeneousDigitTupleSum
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ t ∈ tuples,
        (gaussMeasure.real
            (gaussHeterogeneousApproximationTupleEvent
              (L : ℝ) lower upper (fun i ↦ (t i).1)) -
          gaussMeasure.real
            (gaussHeterogeneousDigitWindowTupleEvent
              (L : ℝ) lower upper (fun i ↦ (t i).1)))| ≤
        ∑ t ∈ tuples,
          |gaussMeasure.real
              (gaussHeterogeneousApproximationTupleEvent
                (L : ℝ) lower upper (fun i ↦ (t i).1)) -
            gaussMeasure.real
              (gaussHeterogeneousDigitWindowTupleEvent
                (L : ℝ) lower upper (fun i ↦ (t i).1))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro t _ht
      exact abs_measureReal_sub_le_measureReal_symmDiff
        (measurableSet_gaussHeterogeneousApproximationTupleEvent
          (L : ℝ) lower upper (fun i ↦ (t i).1)).nullMeasurableSet
        (measurableSet_gaussHeterogeneousDigitWindowTupleEvent
          (L : ℝ) lower upper (fun i ↦ (t i).1)).nullMeasurableSet

/-- The proved heterogeneous replacement theorem, specialized to
chronological tuples with the minimal positive gap. -/
theorem tendsto_gaussHeterogeneousApproximationTupleSum_sub_digit_zero
    {r : ℕ} (hr : 0 < r) {A : ℝ}
    (lower upper : Fin r → ℝ)
    (tuples : ∀ L : ℕ, Finset (Fin r → Fin L))
    (hA : 0 ≤ A)
    (hlower : ∀ i, 0 < lower i)
    (hupper : ∀ i, lower i < upper i)
    (hupperA : ∀ i, upper i ≤ A)
    (hlarge : ∀ᶠ L : ℕ in atTop,
      ∀ i, 16 * (upper i) ^ 2 ≤ lower i * (L : ℝ))
    (hchronological : ∀ L, ∀ t ∈ tuples L, IsChronologicalTuple t) :
    Tendsto
      (fun L : ℕ ↦
        gaussHeterogeneousApproximationTupleSum lower upper (tuples L) -
          gaussHeterogeneousDigitTupleSum lower upper (tuples L))
      atTop (𝓝 0) := by
  have hsymm :
      Tendsto
        (fun L : ℕ ↦
          ∑ t ∈ tuples L,
            gaussMeasure.real
              (gaussHeterogeneousApproximationTupleEvent
                  (L : ℝ) lower upper (fun i ↦ (t i).1) ∆
                gaussHeterogeneousDigitWindowTupleEvent
                  (L : ℝ) lower upper (fun i ↦ (t i).1)))
        atTop (𝓝 0) := by
    exact
      tendsto_sum_gaussMeasure_real_symmDiff_heterogeneousFinTuples_zero
        hr lower upper tuples 1 (by norm_num) hA hlower hupper hupperA
        hlarge (fun L t ht ↦ hchronological L t ht)
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero'
  · exact Eventually.of_forall fun _L ↦ abs_nonneg _
  · filter_upwards with L
    exact abs_gaussHeterogeneousApproximationTupleSum_sub_digit_le
      lower upper (tuples L)
  · exact hsymm

/-! ## One-point products and tuplewise mixing -/

/-- The factorial-scale product of the coordinate-dependent one-digit
window masses has the product of the individual limiting intensities. -/
theorem tendsto_gaussHeterogeneousRareDigitProduct
    {r : ℕ} (lower upper : Fin r → ℝ)
    (hlower : ∀ i, 0 < lower i)
    (hupper : ∀ i, lower i < upper i) :
    Tendsto
      (fun L : ℕ ↦
        ∏ i, (L : ℝ) *
          gaussMeasure.real
            (scaledGaussFirstDigitWindow
              (L : ℝ) (lower i) (upper i)))
      atTop
      (𝓝 (∏ i, (upper i - lower i) / Real.log 2)) := by
  apply tendsto_finset_prod Finset.univ
  intro i _hi
  exact tendsto_natCast_mul_gaussRareDigitWindow
    (hlower i) (hupper i)

/-- A deterministic tuple-cardinality density multiplied by the
heterogeneous independent rare-window product. -/
theorem tendsto_card_mul_gaussHeterogeneousRareDigitProduct_of_density
    {r : ℕ} {density : ℝ}
    (lower upper : Fin r → ℝ)
    (hlower : ∀ i, 0 < lower i)
    (hupper : ∀ i, lower i < upper i)
    (family : ∀ L : ℕ, Finset (Fin r → Fin L))
    (hdensity : Tendsto
      (fun L : ℕ ↦ ((family L).card : ℝ) / (L : ℝ) ^ r)
      atTop (𝓝 density)) :
    Tendsto
      (fun L : ℕ ↦ ((family L).card : ℝ) *
        ∏ i, gaussMeasure.real
          (scaledGaussFirstDigitWindow
            (L : ℝ) (lower i) (upper i)))
      atTop
      (𝓝 (density *
        ∏ i, (upper i - lower i) / Real.log 2)) := by
  have hproduct :=
    tendsto_gaussHeterogeneousRareDigitProduct
      lower upper hlower hupper
  have hmul := hdensity.mul hproduct
  apply hmul.congr'
  filter_upwards [eventually_gt_atTop 0] with L hL
  have hLne : (L : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hL)
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  field_simp [hLne]

/-- Long-gap relative product estimate for heterogeneous one-digit
windows. -/
theorem abs_gaussMeasure_real_heterogeneousDigitTupleEvent_sub_product_le
    {r : ℕ} (hr : 0 < r) {scale : ℝ}
    (lower upper : Fin r → ℝ) (times : Fin r → ℕ)
    (gap : ℕ) (hgap0 : 0 < gap)
    (hseparated : ∀ i k, i < k → times i + gap ≤ times k) :
    |gaussMeasure.real
        (gaussHeterogeneousDigitWindowTupleEvent
          scale lower upper times) -
      ∏ i, gaussMeasure.real
        (scaledGaussFirstDigitWindow scale (lower i) (upper i))| ≤
      ((1 + gaussDigitExponentialRate gap) ^ (r - 1) - 1) *
        ∏ i, gaussMeasure.real
          (scaledGaussFirstDigitWindow scale (lower i) (upper i)) := by
  rw [gaussMeasure_real_heterogeneousDigitWindowTupleEvent_eq_pure
    hr scale lower upper times]
  have hmix :=
    gaussMeasureReal_iInter_oneDigitEvents_factorization_error_le
      hr times
        (fun i ↦ scaledGaussFirstDigitWindow
          scale (lower i) (upper i))
        gap
        (fun i ↦ measurableSet_scaledGaussFirstDigitWindow
          scale (lower i) (upper i))
        (fun i ↦ isGaussOneDigitEvent_scaledGaussFirstDigitWindow
          scale (lower i) (upper i))
        hgap0 hseparated
  simpa only [gaussHeterogeneousDigitTupleEvent,
    orderedEventIntersection_ofFn] using! hmix

/-- Gap-one quasi-Bernoulli estimate for a heterogeneous tuple. -/
theorem gaussMeasure_real_heterogeneousDigitTupleEvent_le
    {r : ℕ} (hr : 0 < r) {scale : ℝ}
    (lower upper : Fin r → ℝ) (times : Fin r → ℕ)
    (hchronological : ∀ i k, i < k → times i + 1 ≤ times k) :
    gaussMeasure.real
        (gaussHeterogeneousDigitWindowTupleEvent
          scale lower upper times) ≤
      7 ^ (r - 1) *
        ∏ i, gaussMeasure.real
          (scaledGaussFirstDigitWindow scale (lower i) (upper i)) := by
  rw [gaussMeasure_real_heterogeneousDigitWindowTupleEvent_eq_pure
    hr scale lower upper times]
  have hbound :=
    gaussDigitPsiMixing_exponential.measure_heterogeneousDigitTupleEvent_le
      (scale := scale) hr lower upper times 1 (by norm_num) hchronological
        (gaussDigitExponentialRate_nonnegative 1)
  norm_num [gaussDigitExponentialRate] at hbound ⊢
  exact hbound

/-! ## Short/long decomposition -/

/-- Short chronological tuples have the uniform heterogeneous
gap-one rare-event bound. -/
theorem gaussHeterogeneousDigitTupleSum_short_le
    {r L gap : ℕ} (hr : 0 < r)
    (lower upper : Fin r → ℝ)
    (tuples : Finset (Fin r → Fin L))
    (hchronological : ∀ t ∈ tuples, IsChronologicalTuple t) :
    gaussHeterogeneousDigitTupleSum lower upper
        (shortTupleFamily gap tuples) ≤
      ((shortTupleFamily gap tuples).card : ℝ) *
        (7 ^ (r - 1) *
          ∏ i, gaussMeasure.real
            (scaledGaussFirstDigitWindow
              (L : ℝ) (lower i) (upper i))) := by
  classical
  unfold gaussHeterogeneousDigitTupleSum
  calc
    (∑ t ∈ shortTupleFamily gap tuples,
        gaussMeasure.real
          (gaussHeterogeneousDigitWindowTupleEvent
            (L : ℝ) lower upper (fun i ↦ (t i).1))) ≤
        ∑ _t ∈ shortTupleFamily gap tuples,
          (7 ^ (r - 1) *
            ∏ i, gaussMeasure.real
              (scaledGaussFirstDigitWindow
                (L : ℝ) (lower i) (upper i))) := by
      apply Finset.sum_le_sum
      intro t ht
      exact gaussMeasure_real_heterogeneousDigitTupleEvent_le
        hr lower upper _ (hchronological t
          (mem_shortTupleFamily_iff.mp ht).1)
    _ = ((shortTupleFamily gap tuples).card : ℝ) *
        (7 ^ (r - 1) *
          ∏ i, gaussMeasure.real
            (scaledGaussFirstDigitWindow
              (L : ℝ) (lower i) (upper i))) := by simp

/-- Aggregate relative-product error on the long-gap family. -/
theorem abs_gaussHeterogeneousDigitTupleSum_separated_sub_product_le
    {r L gap : ℕ} (hr : 0 < r) (hgap0 : 0 < gap)
    (lower upper : Fin r → ℝ)
    (tuples : Finset (Fin r → Fin L)) :
    |gaussHeterogeneousDigitTupleSum lower upper
          (separatedTupleFamily gap tuples) -
        ((separatedTupleFamily gap tuples).card : ℝ) *
          ∏ i, gaussMeasure.real
            (scaledGaussFirstDigitWindow
              (L : ℝ) (lower i) (upper i))| ≤
      ((separatedTupleFamily gap tuples).card : ℝ) *
        (((1 + gaussDigitExponentialRate gap) ^ (r - 1) - 1) *
          ∏ i, gaussMeasure.real
            (scaledGaussFirstDigitWindow
              (L : ℝ) (lower i) (upper i))) := by
  classical
  let p : ℝ :=
    ∏ i, gaussMeasure.real
      (scaledGaussFirstDigitWindow
        (L : ℝ) (lower i) (upper i))
  let q : ℝ :=
    (1 + gaussDigitExponentialRate gap) ^ (r - 1) - 1
  have hrearrange :
      gaussHeterogeneousDigitTupleSum lower upper
            (separatedTupleFamily gap tuples) -
          ((separatedTupleFamily gap tuples).card : ℝ) * p =
        ∑ t ∈ separatedTupleFamily gap tuples,
          (gaussMeasure.real
              (gaussHeterogeneousDigitWindowTupleEvent
                (L : ℝ) lower upper (fun i ↦ (t i).1)) - p) := by
    unfold gaussHeterogeneousDigitTupleSum
    simp
  rw [hrearrange]
  calc
    |∑ t ∈ separatedTupleFamily gap tuples,
        (gaussMeasure.real
            (gaussHeterogeneousDigitWindowTupleEvent
              (L : ℝ) lower upper (fun i ↦ (t i).1)) - p)| ≤
        ∑ t ∈ separatedTupleFamily gap tuples,
          |gaussMeasure.real
              (gaussHeterogeneousDigitWindowTupleEvent
                (L : ℝ) lower upper (fun i ↦ (t i).1)) - p| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ separatedTupleFamily gap tuples, q * p := by
      apply Finset.sum_le_sum
      intro t ht
      exact
        abs_gaussMeasure_real_heterogeneousDigitTupleEvent_sub_product_le
          hr lower upper _ gap hgap0
            (mem_separatedTupleFamily_iff.mp ht).2
    _ = ((separatedTupleFamily gap tuples).card : ℝ) * (q * p) := by
      simp

/-- The digit sum splits exactly into short- and long-gap families. -/
theorem gaussHeterogeneousDigitTupleSum_eq_short_add_separated
    {r L : ℕ} (gap : ℕ) (lower upper : Fin r → ℝ)
    (tuples : Finset (Fin r → Fin L)) :
    gaussHeterogeneousDigitTupleSum lower upper tuples =
      gaussHeterogeneousDigitTupleSum lower upper
          (shortTupleFamily gap tuples) +
        gaussHeterogeneousDigitTupleSum lower upper
          (separatedTupleFamily gap tuples) := by
  classical
  unfold gaussHeterogeneousDigitTupleSum
    shortTupleFamily separatedTupleFamily
  simpa [add_comm] using!
    (Finset.sum_filter_add_sum_filter_not tuples
      (IsSeparatedTuple gap)
      (fun t ↦ gaussMeasure.real
        (gaussHeterogeneousDigitWindowTupleEvent
          (L : ℝ) lower upper (fun i ↦ (t i).1)))).symm

/-! ## Factorial-scale convergence -/

/-- Removing a short-gap family of density `o(L^r)` costs `o(1)` in the
heterogeneous digit factorial sum. -/
theorem tendsto_gaussHeterogeneousDigitTupleSum_short_zero
    {r : ℕ} (hr : 0 < r)
    (lower upper : Fin r → ℝ)
    (hlower : ∀ i, 0 < lower i)
    (hupper : ∀ i, lower i < upper i)
    (gap : ℕ → ℕ)
    (tuples : ∀ L : ℕ, Finset (Fin r → Fin L))
    (hchronological : ∀ L, ∀ t ∈ tuples L, IsChronologicalTuple t)
    (hshortDensity : Tendsto
      (fun L : ℕ ↦
        ((shortTupleFamily (gap L) (tuples L)).card : ℝ) /
          (L : ℝ) ^ r)
      atTop (𝓝 0)) :
    Tendsto
      (fun L : ℕ ↦
        gaussHeterogeneousDigitTupleSum lower upper
          (shortTupleFamily (gap L) (tuples L)))
      atTop (𝓝 0) := by
  let short : ∀ L : ℕ, Finset (Fin r → Fin L) :=
    fun L ↦ shortTupleFamily (gap L) (tuples L)
  have hweight :=
    tendsto_card_mul_gaussHeterogeneousRareDigitProduct_of_density
      lower upper hlower hupper short
        (by simpa only [short] using! hshortDensity)
  have hweight0 :
      Tendsto
        (fun L : ℕ ↦ ((short L).card : ℝ) *
          ∏ i, gaussMeasure.real
            (scaledGaussFirstDigitWindow
              (L : ℝ) (lower i) (upper i)))
        atTop (𝓝 0) := by
    simpa only [zero_mul] using! hweight
  let C : ℝ := 7 ^ (r - 1)
  have hupperZero :
      Tendsto
        (fun L : ℕ ↦ ((short L).card : ℝ) *
          (C * ∏ i, gaussMeasure.real
            (scaledGaussFirstDigitWindow
              (L : ℝ) (lower i) (upper i))))
        atTop (𝓝 0) := by
    have hraw := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ ↦ C) atTop (𝓝 C)).mul hweight0
    have heq :
        (fun L : ℕ ↦ C * (((short L).card : ℝ) *
          ∏ i, gaussMeasure.real
            (scaledGaussFirstDigitWindow
              (L : ℝ) (lower i) (upper i)))) =ᶠ[atTop]
        (fun L : ℕ ↦ ((short L).card : ℝ) *
          (C * ∏ i, gaussMeasure.real
            (scaledGaussFirstDigitWindow
              (L : ℝ) (lower i) (upper i)))) := by
      filter_upwards with L
      ring
    have htarget := hraw.congr' heq
    simpa only [mul_zero] using! htarget
  apply squeeze_zero'
  · exact Eventually.of_forall fun L ↦
      Finset.sum_nonneg fun _t _ht ↦ measureReal_nonneg
  · filter_upwards with L
    simpa only [short, C] using!
      gaussHeterogeneousDigitTupleSum_short_le
        hr lower upper (tuples L) (hchronological L)
  · exact hupperZero

/-- On separated tuples, the aggregate heterogeneous factorization error
tends to zero. -/
theorem tendsto_gaussHeterogeneousDigitTupleSum_separated_sub_product_zero
    {r : ℕ} (hr : 0 < r) {density : ℝ}
    (lower upper : Fin r → ℝ)
    (hlower : ∀ i, 0 < lower i)
    (hupper : ∀ i, lower i < upper i)
    (gap : ℕ → ℕ) (hgapTop : Tendsto gap atTop atTop)
    (hgapPos : ∀ᶠ L : ℕ in atTop, 0 < gap L)
    (tuples : ∀ L : ℕ, Finset (Fin r → Fin L))
    (htotalDensity : Tendsto
      (fun L : ℕ ↦ ((tuples L).card : ℝ) / (L : ℝ) ^ r)
      atTop (𝓝 density))
    (hshortDensity : Tendsto
      (fun L : ℕ ↦
        ((shortTupleFamily (gap L) (tuples L)).card : ℝ) /
          (L : ℝ) ^ r)
      atTop (𝓝 0)) :
    Tendsto
      (fun L : ℕ ↦
        gaussHeterogeneousDigitTupleSum lower upper
            (separatedTupleFamily (gap L) (tuples L)) -
          ((separatedTupleFamily (gap L) (tuples L)).card : ℝ) *
            ∏ i, gaussMeasure.real
              (scaledGaussFirstDigitWindow
                (L : ℝ) (lower i) (upper i)))
      atTop (𝓝 0) := by
  let separated : ∀ L : ℕ, Finset (Fin r → Fin L) :=
    fun L ↦ separatedTupleFamily (gap L) (tuples L)
  have hseparatedDensity :=
    tendsto_separatedTupleFamily_density
      gap tuples htotalDensity hshortDensity
  have hmass :=
    tendsto_gaussHeterogeneousRareDigitProduct
      lower upper hlower hupper
  have hmix :=
    tendsto_gaussDigitRelativeMixingFactor (r := r) hgapTop
  have hupperRaw := hseparatedDensity.mul (hmix.mul hmass)
  have hupperZero :
      Tendsto
        (fun L : ℕ ↦ ((separated L).card : ℝ) *
          (((1 + gaussDigitExponentialRate (gap L)) ^ (r - 1) - 1) *
            ∏ i, gaussMeasure.real
              (scaledGaussFirstDigitWindow
                (L : ℝ) (lower i) (upper i))))
        atTop (𝓝 0) := by
    have hlimit :
        density * (0 *
          ∏ i, (upper i - lower i) / Real.log 2) = 0 := by
      ring
    rw [hlimit] at hupperRaw
    apply hupperRaw.congr'
    filter_upwards [eventually_gt_atTop 0] with L hL
    have hLne : (L : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hL)
    dsimp only [separated]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    field_simp [hLne]
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero'
  · exact Eventually.of_forall fun _L ↦ abs_nonneg _
  · filter_upwards [hgapPos] with L hgapL
    simpa only [separated] using!
      abs_gaussHeterogeneousDigitTupleSum_separated_sub_product_le
        hr hgapL lower upper (tuples L)
  · exact hupperZero

/-- The separated heterogeneous digit sum has the independent-product
limit. -/
theorem tendsto_gaussHeterogeneousDigitTupleSum_separated
    {r : ℕ} (hr : 0 < r) {density : ℝ}
    (lower upper : Fin r → ℝ)
    (hlower : ∀ i, 0 < lower i)
    (hupper : ∀ i, lower i < upper i)
    (gap : ℕ → ℕ) (hgapTop : Tendsto gap atTop atTop)
    (hgapPos : ∀ᶠ L : ℕ in atTop, 0 < gap L)
    (tuples : ∀ L : ℕ, Finset (Fin r → Fin L))
    (htotalDensity : Tendsto
      (fun L : ℕ ↦ ((tuples L).card : ℝ) / (L : ℝ) ^ r)
      atTop (𝓝 density))
    (hshortDensity : Tendsto
      (fun L : ℕ ↦
        ((shortTupleFamily (gap L) (tuples L)).card : ℝ) /
          (L : ℝ) ^ r)
      atTop (𝓝 0)) :
    Tendsto
      (fun L : ℕ ↦
        gaussHeterogeneousDigitTupleSum lower upper
          (separatedTupleFamily (gap L) (tuples L)))
      atTop
      (𝓝 (density *
        ∏ i, (upper i - lower i) / Real.log 2)) := by
  have herr :=
    tendsto_gaussHeterogeneousDigitTupleSum_separated_sub_product_zero
      hr lower upper hlower hupper gap hgapTop hgapPos tuples
        htotalDensity hshortDensity
  have hseparatedDensity :=
    tendsto_separatedTupleFamily_density
      gap tuples htotalDensity hshortDensity
  have hproduct :=
    tendsto_card_mul_gaussHeterogeneousRareDigitProduct_of_density
      lower upper hlower hupper
        (fun L ↦ separatedTupleFamily (gap L) (tuples L))
        hseparatedDensity
  have hadd := herr.add hproduct
  have heq :
      (fun L : ℕ ↦
        (gaussHeterogeneousDigitTupleSum lower upper
            (separatedTupleFamily (gap L) (tuples L)) -
          ((separatedTupleFamily (gap L) (tuples L)).card : ℝ) *
            ∏ i, gaussMeasure.real
              (scaledGaussFirstDigitWindow
                (L : ℝ) (lower i) (upper i))) +
          ((separatedTupleFamily (gap L) (tuples L)).card : ℝ) *
            ∏ i, gaussMeasure.real
              (scaledGaussFirstDigitWindow
                (L : ℝ) (lower i) (upper i))) =ᶠ[atTop]
        (fun L : ℕ ↦
          gaussHeterogeneousDigitTupleSum lower upper
            (separatedTupleFamily (gap L) (tuples L))) := by
    filter_upwards with L
    ring
  have htarget := hadd.congr' heq
  simpa only [zero_add] using! htarget

/-- Heterogeneous digit factorial limit for every deterministic
chronological tuple family with a limiting density and negligible short-gap
density. -/
theorem tendsto_gaussHeterogeneousDigitTupleSum
    {r : ℕ} (hr : 0 < r) {density : ℝ}
    (lower upper : Fin r → ℝ)
    (hlower : ∀ i, 0 < lower i)
    (hupper : ∀ i, lower i < upper i)
    (gap : ℕ → ℕ) (hgapTop : Tendsto gap atTop atTop)
    (hgapPos : ∀ᶠ L : ℕ in atTop, 0 < gap L)
    (tuples : ∀ L : ℕ, Finset (Fin r → Fin L))
    (hchronological : ∀ L, ∀ t ∈ tuples L, IsChronologicalTuple t)
    (htotalDensity : Tendsto
      (fun L : ℕ ↦ ((tuples L).card : ℝ) / (L : ℝ) ^ r)
      atTop (𝓝 density))
    (hshortDensity : Tendsto
      (fun L : ℕ ↦
        ((shortTupleFamily (gap L) (tuples L)).card : ℝ) /
          (L : ℝ) ^ r)
      atTop (𝓝 0)) :
    Tendsto
      (fun L : ℕ ↦
        gaussHeterogeneousDigitTupleSum lower upper (tuples L))
      atTop
      (𝓝 (density *
        ∏ i, (upper i - lower i) / Real.log 2)) := by
  have hshort :=
    tendsto_gaussHeterogeneousDigitTupleSum_short_zero
      hr lower upper hlower hupper gap tuples hchronological hshortDensity
  have hseparated :=
    tendsto_gaussHeterogeneousDigitTupleSum_separated
      hr lower upper hlower hupper gap hgapTop hgapPos tuples
        htotalDensity hshortDensity
  have hadd := hshort.add hseparated
  have heq :
      (fun L : ℕ ↦
        gaussHeterogeneousDigitTupleSum lower upper
            (shortTupleFamily (gap L) (tuples L)) +
          gaussHeterogeneousDigitTupleSum lower upper
            (separatedTupleFamily (gap L) (tuples L))) =ᶠ[atTop]
        (fun L : ℕ ↦
          gaussHeterogeneousDigitTupleSum lower upper (tuples L)) := by
    filter_upwards with L
    exact (gaussHeterogeneousDigitTupleSum_eq_short_add_separated
      (gap L) lower upper (tuples L)).symm
  have htarget := hadd.congr' heq
  simpa only [zero_add] using! htarget

/-! ## Exact-coordinate conclusion -/

/-- Fixed positive heterogeneous windows automatically satisfy the
large-scale condition required by the quantitative replacement theorem.
The universal quantifier is genuinely simultaneous over the finite
coordinate set. -/
theorem eventually_heterogeneousApproximationWindow_large
    {r : ℕ} (lower upper : Fin r → ℝ)
    (hlower : ∀ i, 0 < lower i) :
    ∀ᶠ L : ℕ in atTop,
      ∀ i, 16 * (upper i) ^ 2 ≤ lower i * (L : ℝ) := by
  have hall :
      ∀ᶠ L : ℕ in atTop,
        ∀ i ∈ (Finset.univ : Finset (Fin r)),
          16 * (upper i) ^ 2 ≤ lower i * (L : ℝ) := by
    rw [Finset.eventually_all]
    intro i _hi
    have hthreshold :
        ∀ᶠ L : ℕ in atTop,
          16 * (upper i) ^ 2 / lower i ≤ (L : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually
        (eventually_ge_atTop
          (16 * (upper i) ^ 2 / lower i : ℝ))
    filter_upwards [hthreshold] with L hL
    calc
      16 * (upper i) ^ 2 =
          lower i * (16 * (upper i) ^ 2 / lower i) := by
        field_simp [ne_of_gt (hlower i)]
      _ ≤ lower i * (L : ℝ) :=
        mul_le_mul_of_nonneg_left hL (hlower i).le
  filter_upwards [hall] with L hL
  intro i
  exact hL i (Finset.mem_univ i)

/-- Final exact-coordinate heterogeneous factorial limit.  All analytic
and dynamical estimates have been discharged; only deterministic tuple
counting remains.  The fixed-window scale condition is exposed in this
version for applications that have already proved it as part of a larger
eventuality. -/
theorem tendsto_gaussHeterogeneousApproximationTupleSum
    {r : ℕ} (hr : 0 < r) {A density : ℝ}
    (lower upper : Fin r → ℝ)
    (hA : 0 ≤ A)
    (hlower : ∀ i, 0 < lower i)
    (hupper : ∀ i, lower i < upper i)
    (hupperA : ∀ i, upper i ≤ A)
    (hlarge : ∀ᶠ L : ℕ in atTop,
      ∀ i, 16 * (upper i) ^ 2 ≤ lower i * (L : ℝ))
    (gap : ℕ → ℕ) (hgapTop : Tendsto gap atTop atTop)
    (hgapPos : ∀ᶠ L : ℕ in atTop, 0 < gap L)
    (tuples : ∀ L : ℕ, Finset (Fin r → Fin L))
    (hchronological : ∀ L, ∀ t ∈ tuples L, IsChronologicalTuple t)
    (htotalDensity : Tendsto
      (fun L : ℕ ↦ ((tuples L).card : ℝ) / (L : ℝ) ^ r)
      atTop (𝓝 density))
    (hshortDensity : Tendsto
      (fun L : ℕ ↦
        ((shortTupleFamily (gap L) (tuples L)).card : ℝ) /
          (L : ℝ) ^ r)
      atTop (𝓝 0)) :
    Tendsto
      (fun L : ℕ ↦
        gaussHeterogeneousApproximationTupleSum
          lower upper (tuples L))
      atTop
      (𝓝 (density *
        ∏ i, (upper i - lower i) / Real.log 2)) := by
  have hreplacement :=
    tendsto_gaussHeterogeneousApproximationTupleSum_sub_digit_zero
      hr lower upper tuples hA hlower hupper hupperA hlarge hchronological
  have hdigit :=
    tendsto_gaussHeterogeneousDigitTupleSum
      hr lower upper hlower hupper gap hgapTop hgapPos tuples
        hchronological htotalDensity hshortDensity
  have hadd := hreplacement.add hdigit
  have heq :
      (fun L : ℕ ↦
        (gaussHeterogeneousApproximationTupleSum
            lower upper (tuples L) -
          gaussHeterogeneousDigitTupleSum lower upper (tuples L)) +
          gaussHeterogeneousDigitTupleSum lower upper (tuples L)) =ᶠ[atTop]
        (fun L : ℕ ↦
          gaussHeterogeneousApproximationTupleSum lower upper (tuples L)) := by
    filter_upwards with L
    ring
  have htarget := hadd.congr' heq
  simpa only [zero_add] using! htarget

/-- Paper-facing form with the fixed-window scale condition discharged
internally. -/
theorem tendsto_gaussHeterogeneousApproximationTupleSum_fixedWindows
    {r : ℕ} (hr : 0 < r) {A density : ℝ}
    (lower upper : Fin r → ℝ)
    (hA : 0 ≤ A)
    (hlower : ∀ i, 0 < lower i)
    (hupper : ∀ i, lower i < upper i)
    (hupperA : ∀ i, upper i ≤ A)
    (gap : ℕ → ℕ) (hgapTop : Tendsto gap atTop atTop)
    (hgapPos : ∀ᶠ L : ℕ in atTop, 0 < gap L)
    (tuples : ∀ L : ℕ, Finset (Fin r → Fin L))
    (hchronological : ∀ L, ∀ t ∈ tuples L, IsChronologicalTuple t)
    (htotalDensity : Tendsto
      (fun L : ℕ ↦ ((tuples L).card : ℝ) / (L : ℝ) ^ r)
      atTop (𝓝 density))
    (hshortDensity : Tendsto
      (fun L : ℕ ↦
        ((shortTupleFamily (gap L) (tuples L)).card : ℝ) /
          (L : ℝ) ^ r)
      atTop (𝓝 0)) :
    Tendsto
      (fun L : ℕ ↦
        gaussHeterogeneousApproximationTupleSum
          lower upper (tuples L))
      atTop
      (𝓝 (density *
        ∏ i, (upper i - lower i) / Real.log 2)) := by
  exact tendsto_gaussHeterogeneousApproximationTupleSum
    hr lower upper hA hlower hupper hupperA
      (eventually_heterogeneousApproximationWindow_large
        lower upper hlower)
      gap hgapTop hgapPos tuples hchronological
      htotalDensity hshortDensity

/-- Fixed-order boundedness supplied by the preceding convergence theorem.
This is the exact uniform-integrability input needed later. -/
theorem exists_uniform_gaussHeterogeneousApproximationTupleSum_bound
    {r : ℕ} (hr : 0 < r) {A density : ℝ}
    (lower upper : Fin r → ℝ)
    (hA : 0 ≤ A)
    (hlower : ∀ i, 0 < lower i)
    (hupper : ∀ i, lower i < upper i)
    (hupperA : ∀ i, upper i ≤ A)
    (hlarge : ∀ᶠ L : ℕ in atTop,
      ∀ i, 16 * (upper i) ^ 2 ≤ lower i * (L : ℝ))
    (gap : ℕ → ℕ) (hgapTop : Tendsto gap atTop atTop)
    (hgapPos : ∀ᶠ L : ℕ in atTop, 0 < gap L)
    (tuples : ∀ L : ℕ, Finset (Fin r → Fin L))
    (hchronological : ∀ L, ∀ t ∈ tuples L, IsChronologicalTuple t)
    (htotalDensity : Tendsto
      (fun L : ℕ ↦ ((tuples L).card : ℝ) / (L : ℝ) ^ r)
      atTop (𝓝 density))
    (hshortDensity : Tendsto
      (fun L : ℕ ↦
        ((shortTupleFamily (gap L) (tuples L)).card : ℝ) /
          (L : ℝ) ^ r)
      atTop (𝓝 0)) :
    ∃ C : ℝ, ∀ L : ℕ,
      |gaussHeterogeneousApproximationTupleSum
        lower upper (tuples L)| ≤ C := by
  have hlimit :=
    tendsto_gaussHeterogeneousApproximationTupleSum
      hr lower upper hA hlower hupper hupperA hlarge
        gap hgapTop hgapPos tuples hchronological
        htotalDensity hshortDensity
  have hbounded := Metric.isBounded_range_of_tendsto
    (fun L : ℕ ↦
      gaussHeterogeneousApproximationTupleSum lower upper (tuples L))
    hlimit
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hbounded
  refine ⟨C, fun L ↦ ?_⟩
  simpa only [Real.norm_eq_abs] using! hC _ ⟨L, rfl⟩

/-! ## Signed chronological parity-box wrapper -/

/-- Sum of exact signed approximation-coordinate tuple masses. -/
def gaussSignedApproximationTupleSum
    {r L : ℕ} (lower upper : Fin r → ℝ)
    (tuples : Finset (Fin r → Fin L)) : ℝ :=
  ∑ t ∈ tuples,
    gaussMeasure.real
      (gaussSignedApproximationTupleEvent
        (L : ℝ) lower upper (fun i ↦ (t i).1))

/-- Positive lower endpoint obtained by orienting a signed window according
to a prescribed parity class. -/
def gaussPrescribedParityOrientedLower
    {r : ℕ} (parity : Fin r → Fin 2)
    (lower upper : Fin r → ℝ) (i : Fin r) : ℝ :=
  gaussParityOrientedLower (parity i).1 (lower i) (upper i)

/-- Positive upper endpoint obtained by orienting a signed window according
to a prescribed parity class. -/
def gaussPrescribedParityOrientedUpper
    {r : ℕ} (parity : Fin r → Fin 2)
    (lower upper : Fin r → ℝ) (i : Fin r) : ℝ :=
  gaussParityOrientedUpper (parity i).1 (lower i) (upper i)

/-- Orientation depends only on the parity class, not on the particular
natural representative. -/
theorem gaussParityOrientedLower_eq_of_mod_two_eq
    {n m : ℕ} (hmod : n % 2 = m % 2) (lower upper : ℝ) :
    gaussParityOrientedLower n lower upper =
      gaussParityOrientedLower m lower upper := by
  have heven : Even n ↔ Even m := by
    simp only [Nat.even_iff]
    rw [hmod]
  unfold gaussParityOrientedLower
  by_cases hn : Even n
  · rw [if_pos hn, if_pos (heven.mp hn)]
  · rw [if_neg hn, if_neg (fun hm ↦ hn (heven.mpr hm))]

theorem gaussParityOrientedUpper_eq_of_mod_two_eq
    {n m : ℕ} (hmod : n % 2 = m % 2) (lower upper : ℝ) :
    gaussParityOrientedUpper n lower upper =
      gaussParityOrientedUpper m lower upper := by
  have heven : Even n ↔ Even m := by
    simp only [Nat.even_iff]
    rw [hmod]
  unfold gaussParityOrientedUpper
  by_cases hn : Even n
  · rw [if_pos hn, if_pos (heven.mp hn)]
  · rw [if_neg hn, if_neg (fun hm ↦ hn (heven.mpr hm))]

/-- On a prescribed parity family, the signed tuple sum is literally the
heterogeneous positive-window tuple sum.  This is an exact finite identity,
not an asymptotic parity argument. -/
theorem gaussSignedApproximationTupleSum_chronologicalParityBoxes_eq
    {r L : ℕ} (parity : Fin r → Fin 2)
    (boxes : Fin r → Finset (Fin L))
    (lower upper : Fin r → ℝ) :
    gaussSignedApproximationTupleSum lower upper
        (chronologicalParityBoxTuples parity boxes) =
      gaussHeterogeneousApproximationTupleSum
        (gaussPrescribedParityOrientedLower parity lower upper)
        (gaussPrescribedParityOrientedUpper parity lower upper)
        (chronologicalParityBoxTuples parity boxes) := by
  classical
  unfold gaussSignedApproximationTupleSum
    gaussHeterogeneousApproximationTupleSum
  apply Finset.sum_congr rfl
  intro t ht
  have hparity :
      ∀ i, (t i).1 % 2 = (parity i).1 :=
    fun i ↦
      (mem_chronologicalParityBoxTuples_iff.mp ht).2 i |>.2
  have hlower :
      (fun i ↦ gaussParityOrientedLower
          (t i).1 (lower i) (upper i)) =
        gaussPrescribedParityOrientedLower parity lower upper := by
    funext i
    exact gaussParityOrientedLower_eq_of_mod_two_eq
      (by
        rw [Nat.mod_eq_of_lt (parity i).isLt]
        exact hparity i)
      (lower i) (upper i)
  have hupper :
      (fun i ↦ gaussParityOrientedUpper
          (t i).1 (lower i) (upper i)) =
        gaussPrescribedParityOrientedUpper parity lower upper := by
    funext i
    exact gaussParityOrientedUpper_eq_of_mod_two_eq
      (by
        rw [Nat.mod_eq_of_lt (parity i).isLt]
        exact hparity i)
      (lower i) (upper i)
  rw [gaussSignedApproximationTupleEvent_eq_oriented, hlower, hupper]

/-- Paper-facing finite-family theorem for chronological parity-restricted
index boxes.  Unlike the earlier homogeneous wrapper, every coordinate may
carry its own positive window.  The conclusion records both the exact
factorial limit and the fixed-order uniform bound used for uniform
integrability. -/
theorem
    gaussHeterogeneousApproximationTupleSum_chronologicalParityBoxes_limit_and_bound
    {r : ℕ} (hr : 0 < r) {A density : ℝ}
    (lower upper : Fin r → ℝ)
    (hA : 0 ≤ A)
    (hlower : ∀ i, 0 < lower i)
    (hupper : ∀ i, lower i < upper i)
    (hupperA : ∀ i, upper i ≤ A)
    (parity : Fin r → Fin 2)
    (boxes : ∀ L : ℕ, Fin r → Finset (Fin L))
    (gap : ℕ → ℕ) (hgapTop : Tendsto gap atTop atTop)
    (hgapPos : ∀ᶠ L : ℕ in atTop, 0 < gap L)
    (htotalDensity : Tendsto
      (fun L : ℕ ↦
        ((chronologicalParityBoxTuples parity (boxes L)).card : ℝ) /
          (L : ℝ) ^ r)
      atTop (𝓝 density))
    (hshortDensity : Tendsto
      (fun L : ℕ ↦
        ((shortTupleFamily (gap L)
            (chronologicalParityBoxTuples parity (boxes L))).card : ℝ) /
          (L : ℝ) ^ r)
      atTop (𝓝 0)) :
    Tendsto
        (fun L : ℕ ↦
          gaussHeterogeneousApproximationTupleSum lower upper
            (chronologicalParityBoxTuples parity (boxes L)))
        atTop
        (𝓝 (density *
          ∏ i, (upper i - lower i) / Real.log 2)) ∧
      ∃ C : ℝ, ∀ L : ℕ,
        |gaussHeterogeneousApproximationTupleSum lower upper
          (chronologicalParityBoxTuples parity (boxes L))| ≤ C := by
  let tuples : ∀ L : ℕ, Finset (Fin r → Fin L) :=
    fun L ↦ chronologicalParityBoxTuples parity (boxes L)
  have hchronological :
      ∀ L, ∀ t ∈ tuples L, IsChronologicalTuple t := by
    intro L t ht
    exact chronologicalParityBoxTuples_isChronological
      parity (boxes L) t ht
  have hlarge :=
    eventually_heterogeneousApproximationWindow_large
      lower upper hlower
  constructor
  · exact tendsto_gaussHeterogeneousApproximationTupleSum
      hr lower upper hA hlower hupper hupperA hlarge
        gap hgapTop hgapPos tuples hchronological
        (by simpa only [tuples] using! htotalDensity)
        (by simpa only [tuples] using! hshortDensity)
  · exact exists_uniform_gaussHeterogeneousApproximationTupleSum_bound
      hr lower upper hA hlower hupper hupperA hlarge
        gap hgapTop hgapPos tuples hchronological
        (by simpa only [tuples] using! htotalDensity)
        (by simpa only [tuples] using! hshortDensity)

/-- Signed parity-box factorial theorem.  Its positivity hypotheses are
stated only for the parity-oriented windows, so it applies uniformly to
positive signed cells at even depths and negative signed cells at odd
depths. -/
theorem
    gaussSignedApproximationTupleSum_chronologicalParityBoxes_limit_and_bound
    {r : ℕ} (hr : 0 < r) {A density : ℝ}
    (signedLower signedUpper : Fin r → ℝ)
    (parity : Fin r → Fin 2)
    (hA : 0 ≤ A)
    (hlower : ∀ i, 0 <
      gaussPrescribedParityOrientedLower
        parity signedLower signedUpper i)
    (hupper : ∀ i,
      gaussPrescribedParityOrientedLower
          parity signedLower signedUpper i <
        gaussPrescribedParityOrientedUpper
          parity signedLower signedUpper i)
    (hupperA : ∀ i,
      gaussPrescribedParityOrientedUpper
        parity signedLower signedUpper i ≤ A)
    (boxes : ∀ L : ℕ, Fin r → Finset (Fin L))
    (gap : ℕ → ℕ) (hgapTop : Tendsto gap atTop atTop)
    (hgapPos : ∀ᶠ L : ℕ in atTop, 0 < gap L)
    (htotalDensity : Tendsto
      (fun L : ℕ ↦
        ((chronologicalParityBoxTuples parity (boxes L)).card : ℝ) /
          (L : ℝ) ^ r)
      atTop (𝓝 density))
    (hshortDensity : Tendsto
      (fun L : ℕ ↦
        ((shortTupleFamily (gap L)
            (chronologicalParityBoxTuples parity (boxes L))).card : ℝ) /
          (L : ℝ) ^ r)
      atTop (𝓝 0)) :
    Tendsto
        (fun L : ℕ ↦
          gaussSignedApproximationTupleSum signedLower signedUpper
            (chronologicalParityBoxTuples parity (boxes L)))
        atTop
        (𝓝 (density *
          ∏ i,
            (gaussPrescribedParityOrientedUpper
                parity signedLower signedUpper i -
              gaussPrescribedParityOrientedLower
                parity signedLower signedUpper i) / Real.log 2)) ∧
      ∃ C : ℝ, ∀ L : ℕ,
        |gaussSignedApproximationTupleSum signedLower signedUpper
          (chronologicalParityBoxTuples parity (boxes L))| ≤ C := by
  have hpositive :=
    gaussHeterogeneousApproximationTupleSum_chronologicalParityBoxes_limit_and_bound
      hr
      (gaussPrescribedParityOrientedLower parity signedLower signedUpper)
      (gaussPrescribedParityOrientedUpper parity signedLower signedUpper)
      hA hlower hupper hupperA parity boxes gap hgapTop hgapPos
      htotalDensity hshortDensity
  constructor
  · apply hpositive.1.congr'
    filter_upwards with L
    exact
      (gaussSignedApproximationTupleSum_chronologicalParityBoxes_eq
        parity (boxes L) signedLower signedUpper).symm
  · obtain ⟨C, hC⟩ := hpositive.2
    refine ⟨C, fun L ↦ ?_⟩
    rw [gaussSignedApproximationTupleSum_chronologicalParityBoxes_eq]
    exact hC L

end

end Erdos1002
