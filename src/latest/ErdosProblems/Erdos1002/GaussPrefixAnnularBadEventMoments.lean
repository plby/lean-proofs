import ErdosProblems.Erdos1002.GaussPrefixCoarseDepthBound
import ErdosProblems.Erdos1002.GaussUnmarkedFactorialLimit
import ErdosProblems.Erdos1002.MarkedBadEventMomentDeletion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Uniform annular moments on the denominator bad event

This file supplies the unconditional moment bound needed when the literal
denominator clock is replaced by a deterministic continued-fraction depth
clock.  The key point is deterministic: a positive prefix whose terminal
denominator is at most `N` has depth less than
`gaussCoarseDepthAmbientSize N = O(log N)`.  Thus a fixed factorial moment
contains only `O((log N)^s)` depth tuples.  Each chronological exact
approximation tuple has mass `O((log N)^(-s))`, by the proved Gauss
quasi-Bernoulli and exact-to-digit replacement estimates.

No marked Poisson limit is used here.  In particular, the result is
available before the literal-to-canonical transfer is proved.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators Topology symmDiff

namespace Erdos1002

noncomputable section

local instance gaussPrefixAnnularBadEventMomentsPropDecidable (P : Prop) :
    Decidable P := Classical.propDecidable P

set_option maxHeartbeats 800000

/-! ## Sorting one injective depth tuple -/

/-- The finite set of natural depths occurring in an embedding. -/
def depthRangeOfEmbedding
    {s : ℕ} {S : Finset ℕ} (f : Fin s ↪ S) : Finset ℕ :=
  Finset.univ.image fun i : Fin s ↦ (f i : ℕ)

theorem card_depthRangeOfEmbedding
    {s : ℕ} {S : Finset ℕ} (f : Fin s ↪ S) :
    (depthRangeOfEmbedding f).card = s := by
  classical
  rw [depthRangeOfEmbedding, Finset.card_image_iff.mpr]
  · simp
  · intro i _hi j _hj hij
    apply f.injective
    apply Subtype.ext
    exact hij

/-- Increasing enumeration of the depths occurring in an embedding. -/
def sortedDepthsOfEmbedding
    {s : ℕ} {S : Finset ℕ} (f : Fin s ↪ S) : Fin s → ℕ :=
  (depthRangeOfEmbedding f).orderEmbOfFin
    (card_depthRangeOfEmbedding f)

theorem sortedDepthsOfEmbedding_chronological
    {s : ℕ} {S : Finset ℕ} (f : Fin s ↪ S) :
    IsChronologicalNatTuple (sortedDepthsOfEmbedding f) := by
  intro i j hij
  have hlt :
      sortedDepthsOfEmbedding f i <
        sortedDepthsOfEmbedding f j :=
    ((depthRangeOfEmbedding f).orderEmbOfFin
      (card_depthRangeOfEmbedding f)).strictMono hij
  omega

theorem sortedDepthsOfEmbedding_mem_range
    {s : ℕ} {S : Finset ℕ} (f : Fin s ↪ S) (j : Fin s) :
    sortedDepthsOfEmbedding f j ∈ depthRangeOfEmbedding f := by
  exact
    (depthRangeOfEmbedding f).orderEmbOfFin_mem
      (card_depthRangeOfEmbedding f) j

theorem exists_embedding_index_eq_sortedDepth
    {s : ℕ} {S : Finset ℕ} (f : Fin s ↪ S) (j : Fin s) :
    ∃ i : Fin s, (f i : ℕ) = sortedDepthsOfEmbedding f j := by
  have hj := sortedDepthsOfEmbedding_mem_range f j
  rw [depthRangeOfEmbedding, Finset.mem_image] at hj
  obtain ⟨i, _hi, hif⟩ := hj
  exact ⟨i, hif⟩

theorem exists_sortedDepth_eq_embedding_index
    {s : ℕ} {S : Finset ℕ} (f : Fin s ↪ S) (i : Fin s) :
    ∃ j : Fin s, sortedDepthsOfEmbedding f j = (f i : ℕ) := by
  have hi : (f i : ℕ) ∈ depthRangeOfEmbedding f := by
    unfold depthRangeOfEmbedding
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hi' :
      (f i : ℕ) ∈
        Set.range
          ((depthRangeOfEmbedding f).orderEmbOfFin
            (card_depthRangeOfEmbedding f)) := by
    simpa only [Finset.range_orderEmbOfFin] using! hi
  obtain ⟨j, hj⟩ := hi'
  exact ⟨j, hj⟩

/-- Reordering an embedding chronologically leaves its simultaneous event
unchanged. -/
theorem tupleEvent_eq_sortedDepths
    {s : ℕ} {S : Finset ℕ} (E : ℕ → Set ℝ)
    (f : Fin s ↪ S) :
    tupleEvent E f =
      ⋂ j : Fin s, E (sortedDepthsOfEmbedding f j) := by
  ext x
  simp only [tupleEvent, Set.mem_iInter]
  constructor
  · intro hx j
    obtain ⟨i, hi⟩ := exists_embedding_index_eq_sortedDepth f j
    simpa only [← hi] using! hx i
  · intro hx i
    obtain ⟨j, hj⟩ := exists_sortedDepth_eq_embedding_index f i
    simpa only [hj] using! hx j

/-! ## One exact tuple has the required inverse-power mass -/

/-- A convenient explicit upper envelope for one chronological exact
approximation tuple.  It is written without cancelling powers, so its
asymptotic behavior follows directly from the standard limit calculus. -/
def chronologicalApproximationTupleUpper
    (s : ℕ) (lower upper scale : ℝ) : ℝ :=
  7 ^ (s - 1) *
      ((((upper - lower) / scale +
          2 * (upper ^ 2 + lower ^ 2) / scale ^ 2) /
        Real.log 2) ^ s) +
    (s : ℝ) * 2 * 7 ^ (s - 1) *
      (((26 * upper ^ 2 / scale ^ 2) / Real.log 2) *
        ((((2 * upper + 10 * upper ^ 2) / scale) /
          Real.log 2) ^ (s - 1)))

/-- Scale-free constant obtained by multiplying the preceding envelope by
`scale^s` and harmlessly weakening its `scale^(-s-1)` replacement term. -/
def chronologicalApproximationTupleConstant
    (s : ℕ) (lower upper : ℝ) : ℝ :=
  let W := ((upper - lower) +
      2 * (upper ^ 2 + lower ^ 2)) / Real.log 2
  let B := 26 * upper ^ 2 / Real.log 2
  let D := (2 * upper + 10 * upper ^ 2) / Real.log 2
  7 ^ (s - 1) * W ^ s +
    (s : ℝ) * 2 * 7 ^ (s - 1) * (B * D ^ (s - 1))

theorem chronologicalApproximationTupleUpper_le_constant_div_pow
    {s : ℕ} (hs : 0 < s) {scale lower upper : ℝ}
    (hscale : 1 ≤ scale) (hlower : 0 < lower)
    (hupper : lower < upper) :
    chronologicalApproximationTupleUpper s lower upper scale ≤
      chronologicalApproximationTupleConstant s lower upper /
        scale ^ s := by
  have hscalePos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
  have hupperPos : 0 < upper := hlower.trans hupper
  let W : ℝ := ((upper - lower) +
      2 * (upper ^ 2 + lower ^ 2)) / Real.log 2
  let B : ℝ := 26 * upper ^ 2 / Real.log 2
  let D : ℝ := (2 * upper + 10 * upper ^ 2) / Real.log 2
  have hW : 0 ≤ W := by
    dsimp only [W]
    exact div_nonneg
      (add_nonneg (sub_nonneg.mpr hupper.le) (by positivity))
      (Real.log_pos one_lt_two).le
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hD : 0 ≤ D := by
    dsimp only [D]
    have hnum : 0 ≤ 2 * upper + 10 * upper ^ 2 := by
      nlinarith [sq_nonneg upper]
    exact div_nonneg hnum (Real.log_pos one_lt_two).le
  have hscaleSq : scale ≤ scale ^ 2 := by
    nlinarith [sq_nonneg (scale - 1)]
  have hsecond :
      2 * (upper ^ 2 + lower ^ 2) / scale ^ 2 ≤
        2 * (upper ^ 2 + lower ^ 2) / scale := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hscalePos) hscalePos).2
    have hq : 0 ≤ 2 * (upper ^ 2 + lower ^ 2) := by positivity
    exact mul_le_mul_of_nonneg_left hscaleSq hq
  have hbase :
      (((upper - lower) / scale +
          2 * (upper ^ 2 + lower ^ 2) / scale ^ 2) /
        Real.log 2) ≤ W / scale := by
    calc
      _ ≤ (((upper - lower) / scale +
          2 * (upper ^ 2 + lower ^ 2) / scale) /
            Real.log 2) := by
        exact div_le_div_of_nonneg_right
          (add_le_add le_rfl hsecond) (Real.log_pos one_lt_two).le
      _ = W / scale := by
        dsimp only [W]
        field_simp [ne_of_gt hscalePos,
          ne_of_gt (Real.log_pos one_lt_two)]
  have hbaseNonneg :
      0 ≤ (((upper - lower) / scale +
          2 * (upper ^ 2 + lower ^ 2) / scale ^ 2) /
        Real.log 2) := by
    apply div_nonneg _ (Real.log_pos one_lt_two).le
    exact add_nonneg
      (div_nonneg (sub_nonneg.mpr hupper.le) hscalePos.le)
      (by positivity)
  have hmain :
      7 ^ (s - 1) *
          ((((upper - lower) / scale +
              2 * (upper ^ 2 + lower ^ 2) / scale ^ 2) /
            Real.log 2) ^ s) ≤
        (7 ^ (s - 1) * W ^ s) / scale ^ s := by
    calc
      _ ≤ 7 ^ (s - 1) * (W / scale) ^ s := by
        gcongr
      _ = (7 ^ (s - 1) * W ^ s) / scale ^ s := by
        rw [div_pow]
        ring
  have hfactor1 :
      (26 * upper ^ 2 / scale ^ 2) / Real.log 2 ≤
        B / scale := by
    have heq :
        (26 * upper ^ 2 / scale ^ 2) / Real.log 2 =
          B / scale ^ 2 := by
      dsimp only [B]
      field_simp [ne_of_gt hscalePos,
        ne_of_gt (Real.log_pos one_lt_two)]
    rw [heq]
    apply (div_le_div_iff₀ (sq_pos_of_pos hscalePos) hscalePos).2
    exact mul_le_mul_of_nonneg_left hscaleSq hB
  have hfactor2 :
      ((2 * upper + 10 * upper ^ 2) / scale) / Real.log 2 =
        D / scale := by
    dsimp only [D]
    field_simp [ne_of_gt hscalePos,
      ne_of_gt (Real.log_pos one_lt_two)]
  have herr :
      (s : ℝ) * 2 * 7 ^ (s - 1) *
          (((26 * upper ^ 2 / scale ^ 2) / Real.log 2) *
            ((((2 * upper + 10 * upper ^ 2) / scale) /
              Real.log 2) ^ (s - 1))) ≤
        ((s : ℝ) * 2 * 7 ^ (s - 1) *
          (B * D ^ (s - 1))) / scale ^ s := by
    cases s with
    | zero => omega
    | succ m =>
        simp only [Nat.succ_sub_one] at hfactor2 ⊢
        rw [hfactor2]
        calc
          _ ≤ ((m + 1 : ℕ) : ℝ) * 2 * 7 ^ m *
              ((B / scale) * (D / scale) ^ m) := by
            gcongr
          _ = (((m + 1 : ℕ) : ℝ) * 2 * 7 ^ m *
              (B * D ^ m)) / scale ^ (m + 1) := by
            rw [div_pow]
            field_simp [ne_of_gt hscalePos]
            ring
  unfold chronologicalApproximationTupleUpper
    chronologicalApproximationTupleConstant
  dsimp only
  calc
    _ ≤ (7 ^ (s - 1) * W ^ s) / scale ^ s +
        ((s : ℝ) * 2 * 7 ^ (s - 1) *
          (B * D ^ (s - 1))) / scale ^ s :=
      add_le_add hmain herr
    _ = (7 ^ (s - 1) * W ^ s +
        (s : ℝ) * 2 * 7 ^ (s - 1) *
          (B * D ^ (s - 1))) / scale ^ s := by
      ring

theorem chronologicalApproximationTupleConstant_nonneg
    (s : ℕ) {lower upper : ℝ}
    (hlower : 0 < lower) (hupper : lower < upper) :
    0 ≤ chronologicalApproximationTupleConstant s lower upper := by
  let W : ℝ := ((upper - lower) +
      2 * (upper ^ 2 + lower ^ 2)) / Real.log 2
  let B : ℝ := 26 * upper ^ 2 / Real.log 2
  let D : ℝ := (2 * upper + 10 * upper ^ 2) / Real.log 2
  have hW : 0 ≤ W := by
    dsimp only [W]
    exact div_nonneg
      (add_nonneg (sub_nonneg.mpr hupper.le) (by positivity))
      (Real.log_pos one_lt_two).le
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hD : 0 ≤ D := by
    dsimp only [D]
    have hupperPos : 0 < upper := hlower.trans hupper
    have hnum : 0 ≤ 2 * upper + 10 * upper ^ 2 := by
      nlinarith [sq_nonneg upper]
    exact div_nonneg hnum (Real.log_pos one_lt_two).le
  unfold chronologicalApproximationTupleConstant
  dsimp only
  exact add_nonneg
    (mul_nonneg (by positivity) (pow_nonneg hW s))
    (mul_nonneg (by positivity)
      (mul_nonneg hB (pow_nonneg hD (s - 1))))

theorem gaussMeasure_real_gaussApproximationTupleEvent_le_upper
    {s : ℕ} (hs : 0 < s) {scale lower upper : ℝ}
    (hscale : 0 < scale) (hscaleOne : 1 ≤ scale)
    (hlower : 0 < lower) (hupper : lower < upper)
    (hlarge : 16 * upper ^ 2 ≤ lower * scale)
    (times : Fin s → ℕ)
    (hchronological : IsChronologicalNatTuple times) :
    gaussMeasure.real
        (gaussApproximationTupleEvent scale lower upper times) ≤
      chronologicalApproximationTupleUpper s lower upper scale := by
  have hdigit :=
    gaussMeasure_real_gaussDigitTupleEvent_le
      hs (scale := scale) (lower := lower) (upper := upper)
        times hchronological
  have hwindow :=
    gaussMeasure_real_scaledGaussFirstDigitWindow_le
      hscale hlower hupper
  have hdigit' :
      gaussMeasure.real
          (gaussDigitTupleEvent scale lower upper times) ≤
        7 ^ (s - 1) *
          ((((upper - lower) / scale +
              2 * (upper ^ 2 + lower ^ 2) / scale ^ 2) /
            Real.log 2) ^ s) := by
    exact hdigit.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (measureReal_nonneg) hwindow s) (by positivity))
  have herr :=
    gaussMeasure_real_symmDiff_approximation_digit_tuple_le_explicit
      gaussDigitPsiMixing_exponential hs times 1 (by norm_num)
      hscale hscaleOne hlower hupper hlarge hchronological
      (gaussDigitExponentialRate_nonnegative 1)
  have herr' := herr
  norm_num [gaussDigitExponentialRate] at herr'
  calc
    gaussMeasure.real
        (gaussApproximationTupleEvent scale lower upper times) ≤
      gaussMeasure.real
          (gaussDigitTupleEvent scale lower upper times) +
        gaussMeasure.real
          (gaussApproximationTupleEvent scale lower upper times ∆
            gaussDigitTupleEvent scale lower upper times) :=
      measureReal_le_add_measureReal_symmDiff gaussMeasure _ _
    _ ≤ chronologicalApproximationTupleUpper s lower upper scale := by
      unfold chronologicalApproximationTupleUpper
      exact add_le_add hdigit' (by
        simpa only [mul_assoc] using! herr')

/-! ## Compact marked prefix events lie in exact approximation windows -/

theorem ae_gaussPrefixMarkedEvent_compactAnnular_subset_approximationWindow
    {N n : ℕ} {ε A : ℝ} (hN : 2 ≤ N) (hε : 0 < ε)
    (_hεA : ε < A) :
    ∀ᵐ x ∂uniform01Measure,
      x ∈ gaussPrefixMarkedEvent N
          (compactAnnularMarkedRegion ε A) n →
        x ∈ gaussApproximationWindow
          (Real.log (N : ℝ)) n ε A := by
  filter_upwards [ae_nonterminating_uniform01] with x hx hevent
  obtain ⟨w, hw, _hden, _htheta, hpoint⟩ :=
    mem_gaussPrefixMarkedEvent_iff.mp hevent
  have hex : x ∉ gaussPrefixExceptional (n + 1) :=
    not_mem_gaussPrefixExceptional_of_nonterminating hx.1 hx.2 _
  have hthetaPos :
      0 < gaussApproximationCoordinate n x :=
    gaussApproximationCoordinate_pos_of_mem_positivePrefix
      w hx.1 hex hw
  have hlog :
      0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  have hscaledPos :
      0 < gaussScaledApproximationCoordinate
          (Real.log (N : ℝ)) n x := by
    unfold gaussScaledApproximationCoordinate
    positivity
  have hvalue :
      ε ≤
          |(gaussPrefixMarkedPoint N n w x).2.1| ∧
        |(gaussPrefixMarkedPoint N n w x).2.1| ≤ A := by
    exact
      (mem_signedAnnulus_iff_abs hε.le).mp hpoint.2.1
  have habs :
      |(gaussPrefixMarkedPoint N n w x).2.1| =
        gaussScaledApproximationCoordinate
          (Real.log (N : ℝ)) n x := by
    rw [gaussPrefixMarkedPoint_value_eq_signedScaledApproximation]
    unfold gaussSignedScaledApproximationCoordinate
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos hscaledPos]
  rw [habs] at hvalue
  exact mem_gaussApproximationWindow_iff.mpr
    ⟨⟨hx.1.1, hx.1.2.le⟩, hvalue⟩

theorem gaussPrefixMarkedEvent_compactAnnular_empty_above_coarseDepth
    {N n : ℕ} {ε A : ℝ}
    (hn : gaussCoarseDepthAmbientSize N ≤ n) :
    gaussPrefixMarkedEvent N (compactAnnularMarkedRegion ε A) n = ∅ := by
  ext x
  constructor
  · intro hx
    obtain ⟨w, _hw, hden, _htheta, _hpoint⟩ :=
      mem_gaussPrefixMarkedEvent_iff.mp hx
    have hdepth :=
      depth_lt_gaussCoarseDepthAmbientSize_of_denominator_le w hden
    omega
  · intro hx
    exact hx.elim

/-! ## Cardinality of the surviving embedding family -/

def boundedGaussPrefixDepthEmbeddings
    (N s : ℕ) : Finset (Fin s ↪ (Finset.Icc 0 N : Finset ℕ)) :=
  Finset.univ.filter fun f ↦
    ∀ i, (f i : ℕ) < gaussCoarseDepthAmbientSize N

theorem card_boundedGaussPrefixDepthEmbeddings_le
    (N s : ℕ) :
    (boundedGaussPrefixDepthEmbeddings N s).card ≤
      gaussCoarseDepthAmbientSize N ^ s := by
  let code :
      (↥(boundedGaussPrefixDepthEmbeddings N s)) →
        (Fin s → Fin (gaussCoarseDepthAmbientSize N)) :=
    fun f i ↦
      ⟨(f.1 i : ℕ), (Finset.mem_filter.mp f.2).2 i⟩
  have hcode : Function.Injective code := by
    intro f g hfg
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    apply Subtype.ext
    exact congrArg Fin.val (congrFun hfg i)
  calc
    (boundedGaussPrefixDepthEmbeddings N s).card =
        Fintype.card (↥(boundedGaussPrefixDepthEmbeddings N s)) := by
      symm
      exact Fintype.card_coe _
    _ ≤ Fintype.card
        (Fin s → Fin (gaussCoarseDepthAmbientSize N)) :=
      Fintype.card_le_of_injective code hcode
    _ = gaussCoarseDepthAmbientSize N ^ s := by simp

/-! ## Uniform mass of one compact marked tuple -/

theorem uniform01Measure_real_gaussPrefixCompactTuple_le
    {N s : ℕ} {ε A : ℝ}
    (hs : 0 < s) (hN : 2 ≤ N)
    (hε : 0 < ε) (hεA : ε < A)
    (hlogOne : 1 ≤ Real.log (N : ℝ))
    (hlarge : 16 * A ^ 2 ≤ ε * Real.log (N : ℝ))
    (f : Fin s ↪ (Finset.Icc 0 N : Finset ℕ)) :
    uniform01Measure.real
        (tupleEvent
          (gaussPrefixMarkedEvent N
            (compactAnnularMarkedRegion ε A)) f) ≤
      (2 * Real.log 2) *
        chronologicalApproximationTupleUpper
          s ε A (Real.log (N : ℝ)) := by
  let times : Fin s → ℕ := sortedDepthsOfEmbedding f
  let E : ℕ → Set ℝ := gaussPrefixMarkedEvent N
    (compactAnnularMarkedRegion ε A)
  let D : Set ℝ :=
    gaussApproximationTupleEvent (Real.log (N : ℝ)) ε A times
  have hsubsetAE :
      ∀ᵐ x ∂uniform01Measure,
        x ∈ tupleEvent E f → x ∈ D := by
    have hall : ∀ᵐ x ∂uniform01Measure, ∀ i : Fin s,
        x ∈ E (f i) →
          x ∈ gaussApproximationWindow
            (Real.log (N : ℝ)) (f i) ε A :=
      ae_all_iff.mpr fun i ↦
        ae_gaussPrefixMarkedEvent_compactAnnular_subset_approximationWindow
          hN hε hεA
    filter_upwards [hall] with x hx htuple
    have htupleAll : ∀ i : Fin s, x ∈ E (f i) := by
      simpa only [tupleEvent, Set.mem_iInter] using! htuple
    unfold D gaussApproximationTupleEvent
    rw [mem_orderedEventIntersection_ofFn_iff]
    intro j
    obtain ⟨i, hi⟩ := exists_embedding_index_eq_sortedDepth f j
    simpa only [times, ← hi] using! hx i (htupleAll i)
  have hmono :
      uniform01Measure.real (tupleEvent E f) ≤
        uniform01Measure.real D := by
    have hmeasure := measure_mono_ae hsubsetAE
    exact ENNReal.toReal_mono (by finiteness) hmeasure
  have hdom :
      uniform01Measure.real D ≤
        (2 * Real.log 2) * gaussMeasure.real D := by
    exact uniform01MeasureReal_le_gaussMeasureReal
      (measurableSet_gaussApproximationTupleEvent
        (Real.log (N : ℝ)) ε A times)
  have hgauss :
      gaussMeasure.real D ≤
        chronologicalApproximationTupleUpper
          s ε A (Real.log (N : ℝ)) := by
    exact
      gaussMeasure_real_gaussApproximationTupleEvent_le_upper
        hs (lt_of_lt_of_le zero_lt_one hlogOne) hlogOne hε hεA hlarge
        times (sortedDepthsOfEmbedding_chronological f)
  calc
    uniform01Measure.real (tupleEvent
        (gaussPrefixMarkedEvent N
          (compactAnnularMarkedRegion ε A)) f) =
        uniform01Measure.real (tupleEvent E f) := by rfl
    _ ≤ uniform01Measure.real D := hmono
    _ ≤ (2 * Real.log 2) * gaussMeasure.real D := hdom
    _ ≤ (2 * Real.log 2) *
        chronologicalApproximationTupleUpper
          s ε A (Real.log (N : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hgauss (by positivity)

/-! ## A denominator-free rare-window dominator -/

/-- Number of exact continued-fraction approximation windows occurring
strictly before depth `L`.  Unlike `markedResonanceCount`, this count has no
terminal-denominator restriction. -/
def gaussApproximationWindowCount
    (scale : ℝ) (L : ℕ) (lower upper : ℝ) (x : ℝ) : ℕ :=
  finiteEventCount (Finset.range L)
    (fun n ↦ gaussApproximationWindow scale n lower upper) x

theorem measurable_gaussApproximationWindowCount
    (scale : ℝ) (L : ℕ) (lower upper : ℝ) :
    Measurable (gaussApproximationWindowCount scale L lower upper) := by
  classical
  unfold gaussApproximationWindowCount finiteEventCount
  apply Finset.measurable_fun_sum
  intro n _hn
  apply Measurable.ite
  · exact measurableSet_gaussApproximationWindow scale n lower upper
  · exact measurable_const
  · exact measurable_const

theorem gaussApproximationWindowCount_le
    (scale : ℝ) (L : ℕ) (lower upper : ℝ) (x : ℝ) :
    gaussApproximationWindowCount scale L lower upper x ≤ L := by
  classical
  unfold gaussApproximationWindowCount finiteEventCount
  calc
    (∑ n ∈ Finset.range L,
        if x ∈ gaussApproximationWindow scale n lower upper then 1 else 0) ≤
      ∑ _n ∈ Finset.range L, 1 := by
        apply Finset.sum_le_sum
        intro n _hn
        split <;> omega
    _ = L := by simp

theorem integrable_gaussApproximationWindowCount_descFactorial
    (scale : ℝ) (L s : ℕ) (lower upper : ℝ) :
    Integrable
      (fun x ↦
        ((gaussApproximationWindowCount scale L lower upper x).descFactorial
          s : ℝ))
      uniform01Measure := by
  have hmeas : Measurable
      (fun x ↦
        ((gaussApproximationWindowCount scale L lower upper x).descFactorial
          s : ℝ)) :=
    (measurable_of_countable
      (fun n : ℕ ↦ (n.descFactorial s : ℝ))).comp
        (measurable_gaussApproximationWindowCount scale L lower upper)
  apply Integrable.of_bound hmeas.aestronglyMeasurable ((L : ℝ) ^ s)
  exact ae_of_all _ fun x ↦ by
    rw [Real.norm_of_nonneg (by positivity)]
    calc
      ((gaussApproximationWindowCount scale L lower upper x).descFactorial
          s : ℝ) ≤
        (gaussApproximationWindowCount scale L lower upper x : ℝ) ^ s := by
          exact_mod_cast Nat.descFactorial_le_pow
            (gaussApproximationWindowCount scale L lower upper x) s
      _ ≤ (L : ℝ) ^ s := by
        gcongr
        exact_mod_cast gaussApproximationWindowCount_le
          scale L lower upper x

theorem integrable_gaussApproximationWindowCount_pow
    (scale : ℝ) (L s : ℕ) (lower upper : ℝ) :
    Integrable
      (fun x ↦
        (gaussApproximationWindowCount scale L lower upper x : ℝ) ^ s)
      uniform01Measure := by
  have hmeas : Measurable
      (fun x ↦
        (gaussApproximationWindowCount scale L lower upper x : ℝ) ^ s) :=
    ((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp
      (measurable_gaussApproximationWindowCount scale L lower upper)).pow_const s
  apply Integrable.of_bound hmeas.aestronglyMeasurable ((L : ℝ) ^ s)
  exact ae_of_all _ fun x ↦ by
    rw [Real.norm_of_nonneg (by positivity)]
    have hle :
        (gaussApproximationWindowCount scale L lower upper x : ℝ) ≤
          (L : ℝ) := by
      exact_mod_cast
        (gaussApproximationWindowCount_le scale L lower upper x)
    exact pow_le_pow_left₀ (by positivity) hle s

/-- Every ordered distinct tuple of denominator-free approximation windows
has the same inverse-power mass bound, irrespective of its original
enumeration order. -/
theorem uniform01Measure_real_gaussApproximationWindowTuple_le
    {L s : ℕ} {scale lower upper : ℝ}
    (hs : 0 < s) (hscale : 0 < scale) (hscaleOne : 1 ≤ scale)
    (hlower : 0 < lower) (hupper : lower < upper)
    (hlarge : 16 * upper ^ 2 ≤ lower * scale)
    (f : Fin s ↪ (Finset.range L : Finset ℕ)) :
    uniform01Measure.real
        (tupleEvent
          (fun n ↦ gaussApproximationWindow scale n lower upper) f) ≤
      (2 * Real.log 2) *
        chronologicalApproximationTupleUpper
          s lower upper scale := by
  let times : Fin s → ℕ := sortedDepthsOfEmbedding f
  let E : ℕ → Set ℝ :=
    fun n ↦ gaussApproximationWindow scale n lower upper
  let D : Set ℝ :=
    gaussApproximationTupleEvent scale lower upper times
  have heq : tupleEvent E f = D := by
    rw [tupleEvent_eq_sortedDepths E f]
    unfold D gaussApproximationTupleEvent
    ext x
    simp only [Set.mem_iInter, mem_orderedEventIntersection_ofFn_iff]
    rfl
  have hdom :
      uniform01Measure.real D ≤
        (2 * Real.log 2) * gaussMeasure.real D := by
    exact uniform01MeasureReal_le_gaussMeasureReal
      (measurableSet_gaussApproximationTupleEvent
        scale lower upper times)
  have hgauss :
      gaussMeasure.real D ≤
        chronologicalApproximationTupleUpper
          s lower upper scale := by
    exact
      gaussMeasure_real_gaussApproximationTupleEvent_le_upper
        hs hscale hscaleOne hlower hupper hlarge times
        (sortedDepthsOfEmbedding_chronological f)
  rw [heq]
  exact hdom.trans
    (mul_le_mul_of_nonneg_left hgauss (by positivity))

/-- Explicit falling-factorial estimate for the denominator-free window
count. -/
theorem integral_gaussApproximationWindowCount_descFactorial_le
    {L s : ℕ} {scale lower upper : ℝ}
    (hs : 0 < s) (hscale : 0 < scale) (hscaleOne : 1 ≤ scale)
    (hlower : 0 < lower) (hupper : lower < upper)
    (hlarge : 16 * upper ^ 2 ≤ lower * scale) :
    ∫ x,
        ((gaussApproximationWindowCount scale L lower upper x).descFactorial
          s : ℝ)
        ∂uniform01Measure ≤
      (L : ℝ) ^ s *
        ((2 * Real.log 2) *
          chronologicalApproximationTupleUpper s lower upper scale) := by
  let E : ℕ → Set ℝ :=
    fun n ↦ gaussApproximationWindow scale n lower upper
  have hexpand :
      ∫ x,
          ((gaussApproximationWindowCount scale L lower upper x).descFactorial
            s : ℝ)
          ∂uniform01Measure =
        ∑ f : Fin s ↪ (Finset.range L : Finset ℕ),
          uniform01Measure.real (tupleEvent E f) := by
    simpa only [gaussApproximationWindowCount, E] using!
      (integral_finiteEventCount_descFactorial
        (Finset.range L) E s uniform01Measure
        (fun n _hn ↦
          measurableSet_gaussApproximationWindow scale n lower upper))
  have hterm : ∀ f : Fin s ↪ (Finset.range L : Finset ℕ),
      uniform01Measure.real (tupleEvent E f) ≤
        (2 * Real.log 2) *
          chronologicalApproximationTupleUpper s lower upper scale := by
    intro f
    exact uniform01Measure_real_gaussApproximationWindowTuple_le
      hs hscale hscaleOne hlower hupper hlarge f
  have hboundNonneg :
      0 ≤ (2 * Real.log 2) *
          chronologicalApproximationTupleUpper s lower upper scale := by
    have hupperPos : 0 < upper := hlower.trans hupper
    have hdiff : 0 ≤ upper - lower := sub_nonneg.mpr hupper.le
    have hbaseNum :
        0 ≤ (upper - lower) / scale +
          2 * (upper ^ 2 + lower ^ 2) / scale ^ 2 :=
      add_nonneg (div_nonneg hdiff hscale.le) (by positivity)
    have hbase :
        0 ≤ ((upper - lower) / scale +
          2 * (upper ^ 2 + lower ^ 2) / scale ^ 2) /
            Real.log 2 :=
      div_nonneg hbaseNum (Real.log_pos one_lt_two).le
    have hreplacement :
        0 ≤
          ((26 * upper ^ 2 / scale ^ 2) / Real.log 2) *
            ((((2 * upper + 10 * upper ^ 2) / scale) /
              Real.log 2) ^ (s - 1)) := by
      have hnum : 0 ≤ 2 * upper + 10 * upper ^ 2 := by
        nlinarith [sq_nonneg upper]
      exact mul_nonneg (by positivity)
        (pow_nonneg
          (div_nonneg (div_nonneg hnum hscale.le)
            (Real.log_pos one_lt_two).le) _)
    unfold chronologicalApproximationTupleUpper
    apply mul_nonneg (by positivity)
    exact add_nonneg (mul_nonneg (by positivity) (pow_nonneg hbase s))
      (mul_nonneg (by positivity) hreplacement)
  rw [hexpand]
  calc
    (∑ f : Fin s ↪ (Finset.range L : Finset ℕ),
        uniform01Measure.real (tupleEvent E f)) ≤
      ∑ _f : Fin s ↪ (Finset.range L : Finset ℕ),
        ((2 * Real.log 2) *
          chronologicalApproximationTupleUpper s lower upper scale) := by
            exact Finset.sum_le_sum fun f _hf ↦ hterm f
    _ = (Fintype.card
          (Fin s ↪ (Finset.range L : Finset ℕ)) : ℝ) *
        ((2 * Real.log 2) *
          chronologicalApproximationTupleUpper s lower upper scale) := by
            simp
    _ ≤ (L : ℝ) ^ s *
        ((2 * Real.log 2) *
          chronologicalApproximationTupleUpper s lower upper scale) := by
      apply mul_le_mul_of_nonneg_right _ hboundNonneg
      exact_mod_cast
        (Fintype.card_embedding_eq.trans_le
          (by
            simpa only [Fintype.card_fin, Fintype.card_coe,
              Finset.card_range] using! Nat.descFactorial_le_pow L s))

/-- The denominator-free factorial estimate in scale-invariant form. -/
theorem integral_gaussApproximationWindowCount_descFactorial_le_ratio
    {L s : ℕ} {scale lower upper : ℝ}
    (hs : 0 < s) (hscale : 0 < scale) (hscaleOne : 1 ≤ scale)
    (hlower : 0 < lower) (hupper : lower < upper)
    (hlarge : 16 * upper ^ 2 ≤ lower * scale) :
    ∫ x,
        ((gaussApproximationWindowCount scale L lower upper x).descFactorial
          s : ℝ)
        ∂uniform01Measure ≤
      (2 * Real.log 2) *
        chronologicalApproximationTupleConstant s lower upper *
          ((L : ℝ) / scale) ^ s := by
  have hraw :=
    integral_gaussApproximationWindowCount_descFactorial_le
      hs hscale hscaleOne hlower hupper hlarge (L := L)
  have hupperBound :=
    chronologicalApproximationTupleUpper_le_constant_div_pow
      hs hscaleOne hlower hupper
  have hLnonneg : 0 ≤ (L : ℝ) ^ s := by positivity
  calc
    (∫ x,
        ((gaussApproximationWindowCount scale L lower upper x).descFactorial
          s : ℝ)
        ∂uniform01Measure) ≤
      (L : ℝ) ^ s *
        ((2 * Real.log 2) *
          chronologicalApproximationTupleUpper s lower upper scale) := hraw
    _ ≤ (L : ℝ) ^ s *
        ((2 * Real.log 2) *
          (chronologicalApproximationTupleConstant s lower upper /
            scale ^ s)) := by
      apply mul_le_mul_of_nonneg_left _ hLnonneg
      exact mul_le_mul_of_nonneg_left hupperBound (by positivity)
    _ = (2 * Real.log 2) *
        chronologicalApproximationTupleConstant s lower upper *
          ((L : ℝ) / scale) ^ s := by
      rw [div_pow]
      field_simp [ne_of_gt hscale]

/-- If a deterministic depth horizon is eventually at most a constant
multiple of `log N`, then all fixed falling-factorial moments of the
denominator-free window count are uniformly bounded.  The finitely many
small values of `N` are included explicitly rather than hidden in an
asymptotic convention. -/
theorem exists_uniform_gaussApproximationWindowCount_descFactorial_bound
    (Ls : ℕ → ℕ) {s : ℕ} (hs : 0 < s)
    {lower upper : ℝ}
    (hlower : 0 < lower) (hupper : lower < upper)
    (hlinear :
      ∃ D : ℝ, 0 ≤ D ∧
        ∀ᶠ N : ℕ in atTop,
          (Ls N : ℝ) ≤ D * Real.log (N : ℝ)) :
    ∃ C : ℝ, ∀ N : ℕ,
      ∫ x,
          ((gaussApproximationWindowCount
            (Real.log (N : ℝ)) (Ls N) lower upper x).descFactorial s : ℝ)
          ∂uniform01Measure ≤ C := by
  obtain ⟨D, hD, hlinearD⟩ := hlinear
  let Ctail : ℝ :=
    (2 * Real.log 2) *
      chronologicalApproximationTupleConstant s lower upper * D ^ s
  have hbaseNonneg :
      0 ≤ (2 * Real.log 2) *
        chronologicalApproximationTupleConstant s lower upper := by
    exact mul_nonneg (by positivity)
      (chronologicalApproximationTupleConstant_nonneg
        s hlower hupper)
  have hlogOne :
      ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    tendsto_log_natCast_atTop.eventually_ge_atTop 1
  have hlarge :
      ∀ᶠ N : ℕ in atTop,
        16 * upper ^ 2 ≤ lower * Real.log (N : ℝ) := by
    have hscaled :
        Tendsto
          (fun N : ℕ ↦ lower * Real.log (N : ℝ))
          atTop atTop :=
      tendsto_log_natCast_atTop.const_mul_atTop hlower
    exact hscaled.eventually_ge_atTop (16 * upper ^ 2)
  have htail :
      ∀ᶠ N : ℕ in atTop,
        ∫ x,
            ((gaussApproximationWindowCount
              (Real.log (N : ℝ)) (Ls N) lower upper x).descFactorial
                s : ℝ)
            ∂uniform01Measure ≤ Ctail := by
    filter_upwards [hlogOne, hlarge, hlinearD] with
      N hlogOneN hlargeN hlinearN
    have hlogPos : 0 < Real.log (N : ℝ) :=
      lt_of_lt_of_le zero_lt_one hlogOneN
    have hratio : (Ls N : ℝ) / Real.log (N : ℝ) ≤ D :=
      (div_le_iff₀ hlogPos).2 hlinearN
    calc
      (∫ x,
          ((gaussApproximationWindowCount
            (Real.log (N : ℝ)) (Ls N) lower upper x).descFactorial
              s : ℝ)
          ∂uniform01Measure) ≤
        (2 * Real.log 2) *
          chronologicalApproximationTupleConstant s lower upper *
            ((Ls N : ℝ) / Real.log (N : ℝ)) ^ s :=
        integral_gaussApproximationWindowCount_descFactorial_le_ratio
          hs hlogPos hlogOneN hlower hupper hlargeN
      _ ≤ Ctail := by
        unfold Ctail
        apply mul_le_mul_of_nonneg_left _ hbaseNonneg
        exact pow_le_pow_left₀ (by positivity) hratio s
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 htail
  let Csmall : ℝ :=
    ∑ N ∈ Finset.range N₀, (Ls N : ℝ) ^ s
  refine ⟨max Ctail Csmall, fun N ↦ ?_⟩
  by_cases hlargeN : N₀ ≤ N
  · exact (hN₀ N hlargeN).trans (le_max_left _ _)
  · have hNlt : N < N₀ := Nat.lt_of_not_ge hlargeN
    have hpoint : ∀ x : ℝ,
        ((gaussApproximationWindowCount
          (Real.log (N : ℝ)) (Ls N) lower upper x).descFactorial s : ℝ) ≤
          (Ls N : ℝ) ^ s := by
      intro x
      calc
        ((gaussApproximationWindowCount
          (Real.log (N : ℝ)) (Ls N) lower upper x).descFactorial s : ℝ) ≤
            (gaussApproximationWindowCount
              (Real.log (N : ℝ)) (Ls N) lower upper x : ℝ) ^ s := by
          exact_mod_cast Nat.descFactorial_le_pow
            (gaussApproximationWindowCount
              (Real.log (N : ℝ)) (Ls N) lower upper x) s
        _ ≤ (Ls N : ℝ) ^ s := by
          gcongr
          exact_mod_cast gaussApproximationWindowCount_le
            (Real.log (N : ℝ)) (Ls N) lower upper x
    have hint :
        (∫ x,
          ((gaussApproximationWindowCount
            (Real.log (N : ℝ)) (Ls N) lower upper x).descFactorial s : ℝ)
          ∂uniform01Measure) ≤
            ∫ _x : ℝ, (Ls N : ℝ) ^ s ∂uniform01Measure := by
      apply integral_mono
      · exact integrable_gaussApproximationWindowCount_descFactorial
          (Real.log (N : ℝ)) (Ls N) s lower upper
      · exact integrable_const _
      · exact hpoint
    have hmoment :
        (∫ x,
          ((gaussApproximationWindowCount
            (Real.log (N : ℝ)) (Ls N) lower upper x).descFactorial s : ℝ)
          ∂uniform01Measure) ≤ (Ls N : ℝ) ^ s := by
      simpa using! hint
    have hsum : (Ls N : ℝ) ^ s ≤ Csmall := by
      unfold Csmall
      exact Finset.single_le_sum
        (f := fun n : ℕ ↦ (Ls n : ℝ) ^ s)
        (fun n _hn ↦ by positivity) (Finset.mem_range.mpr hNlt)
    exact (hmoment.trans hsum).trans (le_max_right _ _)

/-- The preceding factorial estimate implies a uniform ordinary moment
bound of the same order. -/
theorem exists_uniform_gaussApproximationWindowCount_pow_bound
    (Ls : ℕ → ℕ) {s : ℕ} (hs : 0 < s)
    {lower upper : ℝ}
    (hlower : 0 < lower) (hupper : lower < upper)
    (hlinear :
      ∃ D : ℝ, 0 ≤ D ∧
        ∀ᶠ N : ℕ in atTop,
          (Ls N : ℝ) ≤ D * Real.log (N : ℝ)) :
    ∃ C : ℝ, ∀ N : ℕ,
      ∫ x,
          (gaussApproximationWindowCount
            (Real.log (N : ℝ)) (Ls N) lower upper x : ℝ) ^ s
          ∂uniform01Measure ≤ C := by
  obtain ⟨Cfac, hCfac⟩ :=
    exists_uniform_gaussApproximationWindowCount_descFactorial_bound
      Ls hs hlower hupper hlinear
  refine
    ⟨(2 : ℝ) ^ s * Cfac + ((2 * s : ℕ) : ℝ) ^ s, fun N ↦ ?_⟩
  exact integral_natCast_pow_le_of_descFactorial_integral_le
    uniform01Measure
    (gaussApproximationWindowCount
      (Real.log (N : ℝ)) (Ls N) lower upper)
    (measurable_gaussApproximationWindowCount
      (Real.log (N : ℝ)) (Ls N) lower upper)
    s
    (integrable_gaussApproximationWindowCount_descFactorial
      (Real.log (N : ℝ)) (Ls N) s lower upper)
    (hCfac N)

/-- The denominator-free dominator has vanishing restricted moments on the
global denominator bad event.  The count horizon `Ds` and the horizon `Ls`
defining the bad event are deliberately independent. -/
theorem tendsto_gaussApproximationWindowCount_pow_on_denominatorBadEvent
    (Ds Ls : ℕ → ℕ) (r Cdepth : ℕ)
    {lower upper Delta : ℝ}
    (hr : 0 < r) (hlower : 0 < lower) (hupper : lower < upper)
    (hDsLinear :
      ∃ D : ℝ, 0 ≤ D ∧
        ∀ᶠ N : ℕ in atTop,
          (Ds N : ℝ) ≤ D * Real.log (N : ℝ))
    (hCdepth : 0 < Cdepth) (hDelta : 0 < Delta)
    (hLs : Tendsto Ls atTop atTop) :
    Tendsto
      (fun N ↦ ∫ x in
          gaussDenominatorLinearBadEvent Cdepth (Ls N) Delta,
        (gaussApproximationWindowCount
          (Real.log (N : ℝ)) (Ds N) lower upper x : ℝ) ^ r
          ∂uniform01Measure)
      atTop (nhds 0) := by
  obtain ⟨Cmoment, hCmoment⟩ :=
    exists_uniform_gaussApproximationWindowCount_pow_bound
      Ds (s := 2 * r) (by omega) hlower hupper hDsLinear
  let X : ℕ → ℝ → ℕ := fun N ↦
    gaussApproximationWindowCount
      (Real.log (N : ℝ)) (Ds N) lower upper
  let E : ℕ → Set ℝ := fun N ↦
    gaussDenominatorLinearBadEvent Cdepth (Ls N) Delta
  apply tendsto_setIntegral_natCast_pow_on_vanishing_events
    uniform01Measure X E r
  · intro N
    exact measurable_gaussApproximationWindowCount
      (Real.log (N : ℝ)) (Ds N) lower upper
  · intro N
    exact integrable_gaussApproximationWindowCount_pow
      (Real.log (N : ℝ)) (Ds N) (2 * r) lower upper
  · intro N
    exact measurableSet_gaussDenominatorLinearBadEvent
      Cdepth (Ls N) Delta
  · exact
      (tendsto_gaussDenominatorLinearBadEvent_uniform01MeasureReal_zero
        hCdepth hDelta).comp hLs
  · intro N
    exact hCmoment N

theorem tupleEvent_gaussPrefixCompact_eq_empty_of_not_bounded
    {N s : ℕ} {ε A : ℝ}
    (f : Fin s ↪ (Finset.Icc 0 N : Finset ℕ))
    (hf : ¬ ∀ i, (f i : ℕ) < gaussCoarseDepthAmbientSize N) :
    tupleEvent
        (gaussPrefixMarkedEvent N
          (compactAnnularMarkedRegion ε A)) f = ∅ := by
  push_neg at hf
  obtain ⟨i, hi⟩ := hf
  have hE :=
    gaussPrefixMarkedEvent_compactAnnular_empty_above_coarseDepth
      (ε := ε) (A := A) hi
  ext x
  constructor
  · intro hx
    have hxi :
        x ∈ gaussPrefixMarkedEvent N
          (compactAnnularMarkedRegion ε A) (f i) := by
      exact Set.mem_iInter.mp hx i
    rw [hE] at hxi
    exact hxi.elim
  · intro hx
    exact hx.elim

/-- The exact Gauss-prefix compact-annulus falling-factorial moment is
bounded by the coarse number of possible depth tuples times the one-tuple
mass envelope. -/
theorem integral_gaussPrefixMarkedCount_compactAnnular_descFactorial_le
    {N s : ℕ} {ε A : ℝ}
    (hs : 0 < s) (hN : 2 ≤ N)
    (hε : 0 < ε) (hεA : ε < A)
    (hlogOne : 1 ≤ Real.log (N : ℝ))
    (hlarge : 16 * A ^ 2 ≤ ε * Real.log (N : ℝ)) :
    ∫ x,
        ((gaussPrefixMarkedCount N
          (compactAnnularMarkedRegion ε A) x).descFactorial s : ℝ)
        ∂uniform01Measure ≤
      (gaussCoarseDepthAmbientSize N : ℝ) ^ s *
        ((2 * Real.log 2) *
          chronologicalApproximationTupleUpper
            s ε A (Real.log (N : ℝ))) := by
  let E : ℕ → Set ℝ := gaussPrefixMarkedEvent N
    (compactAnnularMarkedRegion ε A)
  let good :
      Finset (Fin s ↪ (Finset.Icc 0 N : Finset ℕ)) :=
    boundedGaussPrefixDepthEmbeddings N s
  have hexpand :
      ∫ x,
          ((gaussPrefixMarkedCount N
            (compactAnnularMarkedRegion ε A) x).descFactorial s : ℝ)
          ∂uniform01Measure =
        ∑ f : Fin s ↪ (Finset.Icc 0 N : Finset ℕ),
          uniform01Measure.real (tupleEvent E f) := by
    simpa only [gaussPrefixMarkedCount_eq_finiteEventCount, E] using!
      (integral_finiteEventCount_descFactorial
        (Finset.Icc 0 N) E s uniform01Measure
        (fun n _hn ↦
          measurableSet_gaussPrefixMarkedEvent N n
            (measurableSet_compactAnnularMarkedRegion ε A)))
  have hrestrict :
      (∑ f : Fin s ↪ (Finset.Icc 0 N : Finset ℕ),
          uniform01Measure.real (tupleEvent E f)) =
        ∑ f ∈ good,
          uniform01Measure.real (tupleEvent E f) := by
    rw [show (∑ f : Fin s ↪ (Finset.Icc 0 N : Finset ℕ),
          uniform01Measure.real (tupleEvent E f)) =
        ∑ f : Fin s ↪ (Finset.Icc 0 N : Finset ℕ),
          if (∀ i, (f i : ℕ) < gaussCoarseDepthAmbientSize N) then
            uniform01Measure.real (tupleEvent E f) else 0 by
      apply Finset.sum_congr rfl
      intro f _hf
      split
      · rfl
      · have hempty :=
          tupleEvent_gaussPrefixCompact_eq_empty_of_not_bounded
            (ε := ε) (A := A) f ‹_›
        rw [hempty]
        simp]
    simp only [good, boundedGaussPrefixDepthEmbeddings,
      Finset.sum_filter]
  have hterm : ∀ f ∈ good,
      uniform01Measure.real (tupleEvent E f) ≤
        (2 * Real.log 2) *
          chronologicalApproximationTupleUpper
            s ε A (Real.log (N : ℝ)) := by
    intro f _hf
    exact uniform01Measure_real_gaussPrefixCompactTuple_le
      hs hN hε hεA hlogOne hlarge f
  have hupperNonneg :
      0 ≤ (2 * Real.log 2) *
          chronologicalApproximationTupleUpper
            s ε A (Real.log (N : ℝ)) := by
    have hscale : 0 < Real.log (N : ℝ) :=
      lt_of_lt_of_le zero_lt_one hlogOne
    have hApos : 0 < A := hε.trans hεA
    have hdiff : 0 ≤ A - ε := sub_nonneg.mpr hεA.le
    have hbaseNum :
        0 ≤ (A - ε) / Real.log (N : ℝ) +
          2 * (A ^ 2 + ε ^ 2) / Real.log (N : ℝ) ^ 2 :=
      add_nonneg (div_nonneg hdiff hscale.le) (by positivity)
    have hbase :
        0 ≤ ((A - ε) / Real.log (N : ℝ) +
          2 * (A ^ 2 + ε ^ 2) / Real.log (N : ℝ) ^ 2) /
            Real.log 2 :=
      div_nonneg hbaseNum (Real.log_pos one_lt_two).le
    have hreplacement :
        0 ≤
          ((26 * A ^ 2 / Real.log (N : ℝ) ^ 2) / Real.log 2) *
            ((((2 * A + 10 * A ^ 2) / Real.log (N : ℝ)) /
              Real.log 2) ^ (s - 1)) := by
      have hnum : 0 ≤ 2 * A + 10 * A ^ 2 := by
        nlinarith [sq_nonneg A]
      exact mul_nonneg (by positivity)
        (pow_nonneg
          (div_nonneg (div_nonneg hnum hscale.le)
            (Real.log_pos one_lt_two).le) _)
    unfold chronologicalApproximationTupleUpper
    apply mul_nonneg (by positivity)
    exact add_nonneg (mul_nonneg (by positivity) (pow_nonneg hbase s))
      (mul_nonneg (by positivity) hreplacement)
  rw [hexpand, hrestrict]
  calc
    (∑ f ∈ good, uniform01Measure.real (tupleEvent E f)) ≤
        ∑ _f ∈ good,
          ((2 * Real.log 2) *
            chronologicalApproximationTupleUpper
              s ε A (Real.log (N : ℝ))) := by
      exact Finset.sum_le_sum hterm
    _ = (good.card : ℝ) *
        ((2 * Real.log 2) *
          chronologicalApproximationTupleUpper
            s ε A (Real.log (N : ℝ))) := by simp
    _ ≤ (gaussCoarseDepthAmbientSize N : ℝ) ^ s *
        ((2 * Real.log 2) *
          chronologicalApproximationTupleUpper
            s ε A (Real.log (N : ℝ))) := by
      apply mul_le_mul_of_nonneg_right _ hupperNonneg
      exact_mod_cast card_boundedGaussPrefixDepthEmbeddings_le N s

/-! ## A bounded sequence majorizing the complete factorial moment -/

def compactAnnularFactorialMajorant
    (s : ℕ) (ε A : ℝ) (N : ℕ) : ℝ :=
  (2 * Real.log 2) *
      chronologicalApproximationTupleConstant s ε A *
    ((gaussCoarseDepthAmbientSize N : ℝ) /
      Real.log (N : ℝ)) ^ s

theorem tendsto_compactAnnularFactorialMajorant
    (s : ℕ) (ε A : ℝ) :
    Tendsto
      (compactAnnularFactorialMajorant s ε A)
      atTop
      (nhds
        ((2 * Real.log 2) *
          chronologicalApproximationTupleConstant s ε A *
            4 ^ s)) := by
  have hpow :=
    tendsto_gaussCoarseDepthAmbientSize_div_log.pow s
  have hconst :
      Tendsto
        (fun _N : ℕ ↦
          (2 * Real.log 2) *
            chronologicalApproximationTupleConstant s ε A)
        atTop
        (nhds
          ((2 * Real.log 2) *
            chronologicalApproximationTupleConstant s ε A)) :=
    tendsto_const_nhds
  simpa only [compactAnnularFactorialMajorant] using! hconst.mul hpow

theorem integral_gaussPrefixMarkedCount_compactAnnular_descFactorial_le_majorant
    {N s : ℕ} {ε A : ℝ}
    (hs : 0 < s) (hN : 2 ≤ N)
    (hε : 0 < ε) (hεA : ε < A)
    (hlogOne : 1 ≤ Real.log (N : ℝ))
    (hlarge : 16 * A ^ 2 ≤ ε * Real.log (N : ℝ)) :
    ∫ x,
        ((gaussPrefixMarkedCount N
          (compactAnnularMarkedRegion ε A) x).descFactorial s : ℝ)
        ∂uniform01Measure ≤
      compactAnnularFactorialMajorant s ε A N := by
  have hraw :=
    integral_gaussPrefixMarkedCount_compactAnnular_descFactorial_le
      hs hN hε hεA hlogOne hlarge
  have hupper :=
    chronologicalApproximationTupleUpper_le_constant_div_pow
      hs hlogOne hε hεA
  have hHnonneg :
      0 ≤ (gaussCoarseDepthAmbientSize N : ℝ) ^ s := by positivity
  have hlogPos : 0 < Real.log (N : ℝ) :=
    lt_of_lt_of_le zero_lt_one hlogOne
  have hconstantNonneg :
      0 ≤ chronologicalApproximationTupleConstant s ε A :=
    chronologicalApproximationTupleConstant_nonneg s hε hεA
  calc
    (∫ x,
        ((gaussPrefixMarkedCount N
          (compactAnnularMarkedRegion ε A) x).descFactorial s : ℝ)
        ∂uniform01Measure) ≤
      (gaussCoarseDepthAmbientSize N : ℝ) ^ s *
        ((2 * Real.log 2) *
          chronologicalApproximationTupleUpper
            s ε A (Real.log (N : ℝ))) := hraw
    _ ≤ (gaussCoarseDepthAmbientSize N : ℝ) ^ s *
        ((2 * Real.log 2) *
          (chronologicalApproximationTupleConstant s ε A /
            Real.log (N : ℝ) ^ s)) := by
      gcongr
    _ = compactAnnularFactorialMajorant s ε A N := by
      unfold compactAnnularFactorialMajorant
      rw [div_pow]
      field_simp [ne_of_gt hlogPos]

theorem eventually_integral_markedResonanceCount_compactAnnular_descFactorial_le_majorant
    {s : ℕ} (hs : 0 < s) {ε A : ℝ}
    (hε : 0 < ε) (hεA : ε < A) :
    ∀ᶠ N : ℕ in atTop,
      ∫ x,
          ((markedResonanceCount N N
            (compactAnnularMarkedRegion ε A) x).descFactorial s : ℝ)
          ∂uniform01Measure ≤
        compactAnnularFactorialMajorant s ε A N := by
  have hlogOne :
      ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    tendsto_log_natCast_atTop.eventually_ge_atTop 1
  have hlarge :
      ∀ᶠ N : ℕ in atTop,
        16 * A ^ 2 ≤ ε * Real.log (N : ℝ) := by
    have hscaled :
        Tendsto
          (fun N : ℕ ↦ ε * Real.log (N : ℝ))
          atTop atTop :=
      tendsto_log_natCast_atTop.const_mul_atTop hε
    exact hscaled.eventually_ge_atTop (16 * A ^ 2)
  have hlogAnnular :
      ∀ᶠ N : ℕ in atTop,
        2 * A < Real.log (N : ℝ) :=
    tendsto_log_natCast_atTop.eventually_gt_atTop (2 * A)
  filter_upwards
    [eventually_ge_atTop 2, hlogOne, hlarge, hlogAnnular] with
      N hN hlogOneN hlargeN hlogAnnularN
  have hae :
      markedResonanceCount N N
          (compactAnnularMarkedRegion ε A) =ᵐ[uniform01Measure]
        gaussPrefixMarkedCount N
          (compactAnnularMarkedRegion ε A) :=
    ae_markedResonanceCount_eq_gaussPrefixMarkedCount
      hN hε.le hlogAnnularN (fun _ hx ↦ hx)
  have heq :
      (∫ x,
          ((markedResonanceCount N N
            (compactAnnularMarkedRegion ε A) x).descFactorial s : ℝ)
          ∂uniform01Measure) =
        ∫ x,
          ((gaussPrefixMarkedCount N
            (compactAnnularMarkedRegion ε A) x).descFactorial s : ℝ)
          ∂uniform01Measure := by
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    rw [hx]
  rw [heq]
  exact
    integral_gaussPrefixMarkedCount_compactAnnular_descFactorial_le_majorant
      hs hN hε hεA hlogOneN hlargeN

/-- Every fixed falling-factorial moment of the complete compact annular
resonance count is bounded uniformly in the denominator cutoff. -/
theorem exists_uniform_markedResonanceCount_compactAnnular_descFactorial_bound
    {s : ℕ} (hs : 0 < s) {ε A : ℝ}
    (hε : 0 < ε) (hεA : ε < A) :
    ∃ C : ℝ, ∀ N : ℕ,
      ∫ x,
          ((markedResonanceCount N N
            (compactAnnularMarkedRegion ε A) x).descFactorial s : ℝ)
          ∂uniform01Measure ≤ C := by
  have hmajorantTendsto :=
    tendsto_compactAnnularFactorialMajorant s ε A
  have hmajorantBounded :=
    Metric.isBounded_range_of_tendsto
      (compactAnnularFactorialMajorant s ε A)
      hmajorantTendsto
  obtain ⟨Ctail, hCtail⟩ :=
    isBounded_iff_forall_norm_le.mp hmajorantBounded
  have hmajorantLe : ∀ N,
      compactAnnularFactorialMajorant s ε A N ≤ Ctail := by
    intro N
    calc
      compactAnnularFactorialMajorant s ε A N ≤
          |compactAnnularFactorialMajorant s ε A N| :=
        le_abs_self _
      _ = ‖compactAnnularFactorialMajorant s ε A N‖ := by
        rw [Real.norm_eq_abs]
      _ ≤ Ctail := hCtail _
        ⟨N, rfl⟩
  have htail : ∀ᶠ N : ℕ in atTop,
      ∫ x,
          ((markedResonanceCount N N
            (compactAnnularMarkedRegion ε A) x).descFactorial s : ℝ)
          ∂uniform01Measure ≤ Ctail := by
    filter_upwards
      [eventually_integral_markedResonanceCount_compactAnnular_descFactorial_le_majorant
        hs hε hεA] with N hN
    exact hN.trans (hmajorantLe N)
  obtain ⟨N₀, hN₀⟩ := (eventually_atTop.1 htail)
  refine ⟨max Ctail ((N₀ : ℝ) ^ s), fun N ↦ ?_⟩
  by_cases hlargeN : N₀ ≤ N
  · exact (hN₀ N hlargeN).trans (le_max_left _ _)
  · have hNN₀ : N ≤ N₀ := (Nat.lt_of_not_ge hlargeN).le
    have hpoint : ∀ x : ℝ,
        ((markedResonanceCount N N
          (compactAnnularMarkedRegion ε A) x).descFactorial s : ℝ) ≤
          (N₀ : ℝ) ^ s := by
      intro x
      calc
        ((markedResonanceCount N N
          (compactAnnularMarkedRegion ε A) x).descFactorial s : ℝ) ≤
            (markedResonanceCount N N
              (compactAnnularMarkedRegion ε A) x : ℝ) ^ s := by
          exact_mod_cast Nat.descFactorial_le_pow
            (markedResonanceCount N N
              (compactAnnularMarkedRegion ε A) x) s
        _ ≤ (N : ℝ) ^ s := by
          gcongr
          exact_mod_cast markedResonanceCount_le N N
            (compactAnnularMarkedRegion ε A) x
        _ ≤ (N₀ : ℝ) ^ s := by
          gcongr
    have hint :
        (∫ x,
          ((markedResonanceCount N N
            (compactAnnularMarkedRegion ε A) x).descFactorial s : ℝ)
          ∂uniform01Measure) ≤
            ∫ _x : ℝ, (N₀ : ℝ) ^ s ∂uniform01Measure := by
      apply integral_mono
      · exact integrable_markedResonanceCount_descFactorial
          N N s (measurableSet_compactAnnularMarkedRegion ε A)
      · exact integrable_const _
      · exact hpoint
    have hsmall :
        (∫ x,
          ((markedResonanceCount N N
            (compactAnnularMarkedRegion ε A) x).descFactorial s : ℝ)
          ∂uniform01Measure) ≤ (N₀ : ℝ) ^ s := by
      simpa using! hint
    exact hsmall.trans (le_max_right _ _)

/-- Monotonicity of the literal marked count in its marked state set. -/
theorem markedResonanceCount_mono_set
    (N P : ℕ) {B K : Set (ℝ × ℝ × ℝ)}
    (hBK : B ⊆ K) (x : ℝ) :
    markedResonanceCount N P B x ≤
      markedResonanceCount N P K x := by
  unfold markedResonanceCount
  apply Finset.sum_le_sum
  intro p _hp
  by_cases hpB :
      IsPrimitiveResonance p x ∧ markedResonancePoint N p x ∈ B
  · have hpK :
        IsPrimitiveResonance p x ∧ markedResonancePoint N p x ∈ K :=
      ⟨hpB.1, hBK hpB.2⟩
    simp [hpB, hpK]
  · simp [hpB]

/-- The same uniform factorial bound holds for every measurable marked set
contained in the compact annulus. -/
theorem exists_uniform_markedResonanceCount_descFactorial_bound_of_subset_compactAnnular
    {s : ℕ} (hs : 0 < s) {ε A : ℝ}
    (hε : 0 < ε) (hεA : ε < A)
    {B : Set (ℝ × ℝ × ℝ)} (hB : MeasurableSet B)
    (hBsub : B ⊆ compactAnnularMarkedRegion ε A) :
    ∃ C : ℝ, ∀ N : ℕ,
      ∫ x,
          ((markedResonanceCount N N B x).descFactorial s : ℝ)
          ∂uniform01Measure ≤ C := by
  obtain ⟨C, hC⟩ :=
    exists_uniform_markedResonanceCount_compactAnnular_descFactorial_bound
      hs hε hεA
  refine ⟨C, fun N ↦ ?_⟩
  calc
    (∫ x,
        ((markedResonanceCount N N B x).descFactorial s : ℝ)
        ∂uniform01Measure) ≤
      ∫ x,
        ((markedResonanceCount N N
          (compactAnnularMarkedRegion ε A) x).descFactorial s : ℝ)
        ∂uniform01Measure := by
      apply integral_mono
      · exact integrable_markedResonanceCount_descFactorial N N s hB
      · exact integrable_markedResonanceCount_descFactorial N N s
          (measurableSet_compactAnnularMarkedRegion ε A)
      · intro x
        change
          ((markedResonanceCount N N B x).descFactorial s : ℝ) ≤
            ((markedResonanceCount N N
              (compactAnnularMarkedRegion ε A) x).descFactorial s : ℝ)
        exact_mod_cast Nat.descFactorial_le s
          (markedResonanceCount_mono_set N N hBsub x)
    _ ≤ C := hC N

/-! ## Deletion of the global denominator bad event -/

/-- The complete compact annular count has vanishing `r`-th moment on every
global denominator bad event whose depth horizon tends to infinity. -/
theorem tendsto_compactAnnularMarkedResonanceCount_pow_on_denominatorBadEvent
    (Ls : ℕ → ℕ) (r Cdepth : ℕ)
    {ε A Delta : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (hεA : ε < A)
    (hCdepth : 0 < Cdepth) (hDelta : 0 < Delta)
    (hLs : Tendsto Ls atTop atTop) :
    Tendsto
      (fun N ↦ ∫ x in
          gaussDenominatorLinearBadEvent Cdepth (Ls N) Delta,
        (markedResonanceCount N N
          (compactAnnularMarkedRegion ε A) x : ℝ) ^ r
          ∂uniform01Measure)
      atTop (nhds 0) := by
  obtain ⟨C, hC⟩ :=
    exists_uniform_markedResonanceCount_compactAnnular_descFactorial_bound
      (s := 2 * r) (by omega) hε hεA
  exact
    tendsto_markedResonanceCount_pow_on_denominatorBadEvent
      (fun N ↦ N) (fun N ↦ N) Ls r Cdepth
      (measurableSet_compactAnnularMarkedRegion ε A)
      hCdepth hDelta hLs hC

/-- Subsets of the compact annulus inherit the same bad-event deletion. -/
theorem tendsto_markedResonanceCount_pow_on_denominatorBadEvent_of_subset_compactAnnular
    (Ls : ℕ → ℕ) (r Cdepth : ℕ)
    {ε A Delta : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (hεA : ε < A)
    {B : Set (ℝ × ℝ × ℝ)} (hB : MeasurableSet B)
    (hBsub : B ⊆ compactAnnularMarkedRegion ε A)
    (hCdepth : 0 < Cdepth) (hDelta : 0 < Delta)
    (hLs : Tendsto Ls atTop atTop) :
    Tendsto
      (fun N ↦ ∫ x in
          gaussDenominatorLinearBadEvent Cdepth (Ls N) Delta,
        (markedResonanceCount N N B x : ℝ) ^ r
          ∂uniform01Measure)
      atTop (nhds 0) := by
  obtain ⟨C, hC⟩ :=
    exists_uniform_markedResonanceCount_descFactorial_bound_of_subset_compactAnnular
      (s := 2 * r) (by omega) hε hεA hB hBsub
  exact
    tendsto_markedResonanceCount_pow_on_denominatorBadEvent
      (fun N ↦ N) (fun N ↦ N) Ls r Cdepth hB
      hCdepth hDelta hLs hC

end

end Erdos1002
