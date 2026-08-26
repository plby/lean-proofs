import ErdosProblems.Erdos1002.GaussPrefixAnnularUniformZeroMode
import ErdosProblems.Erdos1002.EndpointDenominatorDeletion
import ErdosProblems.Erdos1002.VanishingEventMomentDeletion
import ErdosProblems.Erdos1002.UnitTorusContinuityBoxes
import Mathlib.Algebra.Order.Chebyshev

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Boundary cells and the literal denominator-time sandwich

The explicit annular grid has two kinds of boundary behavior which have
different mathematical meanings.

* The first time cell is the genuine interval `[0,1/grid)`.  It is not a
  terminal cell and must not be deleted.
* In each coordinate the index `grid` denotes a singleton at the right
  endpoint.  Such cells have zero limiting intensity.  In the torus
  coordinate they are in fact empty for every literal marked prefix,
  because `Int.fract` is always strictly smaller than one.

The final section gives the deterministic denominator-time comparison used
to replace literal cells by depth boxes.  It records both directions, with
contracted and expanded endpoints and all rounding terms explicit.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

local instance gaussPrefixAnnularBoundaryCellsPropDecidable (P : Prop) :
    Decidable P := Classical.propDecidable P

/-! ## Positive mass of genuine interval cells -/

/-- A nonterminal interval cell has positive mass under Lebesgue measure
restricted to any set containing the corresponding open ambient interval.
The proof inserts a strictly smaller open interval, so it also covers the
first cell whose left endpoint belongs to the boundary of the restriction. -/
theorem volume_restrict_intervalGridCell_pos_of_nonterminal
    {a b : ℝ} (hab : a < b) {grid : ℕ} (hgrid : 0 < grid)
    (i : IntervalGridIndex grid) (hi : i.1 < grid)
    {S : Set ℝ} (hS : Ioo a b ⊆ S) :
    0 < (volume.restrict S) (intervalGridCell a b grid i) := by
  let left : ℝ := intervalGridPoint a b grid i.1
  let right : ℝ := intervalGridPoint a b grid (i.1 + 1)
  let innerLeft : ℝ := (2 * left + right) / 3
  let innerRight : ℝ := (left + 2 * right) / 3
  have hstep : left < right := by
    exact intervalGridPoint_strictMono_step hab hgrid
  have hleftBounds : left ∈ Icc a b := by
    exact intervalGridPoint_mem_Icc hab.le hgrid (Nat.le_of_lt hi)
  have hrightBounds : right ∈ Icc a b := by
    exact intervalGridPoint_mem_Icc hab.le hgrid (by omega)
  have hleftInner : left < innerLeft := by
    dsimp [innerLeft]
    linarith
  have hinner : innerLeft < innerRight := by
    dsimp [innerLeft, innerRight]
    linarith
  have hinnerRight : innerRight < right := by
    dsimp [innerRight]
    linarith
  have hsubset :
      Ioo innerLeft innerRight ⊆
        intervalGridCell a b grid i ∩ S := by
    intro x hx
    constructor
    · unfold intervalGridCell
      rw [if_pos hi]
      change x ∈ Ico left right
      exact ⟨(hleftInner.trans hx.1).le, hx.2.trans hinnerRight⟩
    · apply hS
      exact ⟨hleftBounds.1.trans_lt (hleftInner.trans hx.1),
        (hx.2.trans hinnerRight).trans_le hrightBounds.2⟩
  rw [Measure.restrict_apply
    (measurableSet_intervalGridCell a b grid i)]
  have hopen : 0 < volume (Ioo innerLeft innerRight) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hinner)
  exact hopen.trans_le (measure_mono hsubset)

/-- Every genuine annular grid cell has positive raw limiting mass.  This
includes the first time cell `time = 0`; only right-endpoint singleton
indices are excluded. -/
theorem annularRawStateMeasure_annularGridCell_pos_of_nonterminal
    {ε A : ℝ} (hεA : ε < A) {grid : ℕ} (hgrid : 0 < grid)
    (i : AnnularGridIndex grid)
    (htime : i.time.1 < grid)
    (hsigned : i.signed.1 < grid)
    (htorus : i.torus.1 < grid) :
    0 < annularRawStateMeasure ε A (annularGridCell ε A grid i) := by
  have htimeMass :
      0 < uniform01Measure (intervalGridCell 0 1 grid i.time) := by
    exact volume_restrict_intervalGridCell_pos_of_nonterminal
      zero_lt_one hgrid i.time htime (by intro x hx; exact hx)
  have htorusMass :
      0 < uniform01Measure (intervalGridCell 0 1 grid i.torus) := by
    exact volume_restrict_intervalGridCell_pos_of_nonterminal
      zero_lt_one hgrid i.torus htorus (by intro x hx; exact hx)
  have hsignedMass :
      0 <
        (signedAnnulusFiniteMeasure ε A : Measure ℝ)
          (intervalGridCell
            (signedGridLower ε A i.sign)
            (signedGridUpper ε A i.sign) grid i.signed) := by
    rw [signedAnnulusFiniteMeasure_toMeasure]
    apply volume_restrict_intervalGridCell_pos_of_nonterminal
      (signedGridLower_lt_upper hεA i.sign) hgrid i.signed hsigned
    intro x hx
    cases hi : i.sign
    · exact Or.inl (by
        simpa [signedGridLower, signedGridUpper, signedAnnulusSet, hi]
          using! hx)
    · exact Or.inr (by
        simpa [signedGridLower, signedGridUpper, signedAnnulusSet, hi]
          using! hx)
  unfold annularRawStateMeasure annularGridCell
  rw [Measure.prod_prod, Measure.prod_prod]
  exact ENNReal.mul_pos htimeMass.ne'
    (ENNReal.mul_pos hsignedMass.ne' htorusMass.ne').ne'

/-- The limiting Poisson rate of every nonterminal cell is strictly
positive, including the time-zero interval. -/
theorem annularGridCellPoissonRate_pos_of_nonterminal
    {ε A : ℝ} (hεA : ε < A) {grid : ℕ} (hgrid : 0 < grid)
    (i : AnnularGridIndex grid)
    (htime : i.time.1 < grid)
    (hsigned : i.signed.1 < grid)
    (htorus : i.torus.1 < grid) :
    0 < annularGridCellPoissonRate ε A grid i := by
  rw [← NNReal.coe_pos, coe_annularGridCellPoissonRate]
  apply div_pos
  · exact ENNReal.toReal_pos
      (ne_of_gt
        (annularRawStateMeasure_annularGridCell_pos_of_nonterminal
          hεA hgrid i htime hsigned htorus))
      (measure_ne_top _ _)
  · positivity

/-- Explicitly, the first time-grid interval has positive rate whenever
the other two coordinates are nonterminal. -/
theorem annularGridCellPoissonRate_pos_of_time_zero
    {ε A : ℝ} (hεA : ε < A) {grid : ℕ} (hgrid : 0 < grid)
    (i : AnnularGridIndex grid)
    (htimeZero : i.time.1 = 0)
    (hsigned : i.signed.1 < grid)
    (htorus : i.torus.1 < grid) :
    0 < annularGridCellPoissonRate ε A grid i := by
  apply annularGridCellPoissonRate_pos_of_nonterminal
    hεA hgrid i (by omega) hsigned htorus

/-! ## Terminal singleton cells -/

/-- The last one-dimensional grid index is exactly the right-endpoint
singleton. -/
theorem intervalGridCell_eq_singleton_of_terminal
    (a b : ℝ) {grid : ℕ} (i : IntervalGridIndex grid)
    (hi : i.1 = grid) :
    intervalGridCell a b grid i = {b} := by
  unfold intervalGridCell
  rw [if_neg]
  omega

/-- A terminal one-dimensional cell has zero Lebesgue measure. -/
theorem volume_intervalGridCell_eq_zero_of_terminal
    (a b : ℝ) {grid : ℕ} (i : IntervalGridIndex grid)
    (hi : i.1 = grid) :
    volume (intervalGridCell a b grid i) = 0 := by
  rw [intervalGridCell_eq_singleton_of_terminal a b i hi,
    Real.volume_singleton]

/-- A terminal time coordinate makes the whole annular cell Lebesgue-null. -/
theorem volume_annularGridCell_eq_zero_of_time_terminal
    (ε A : ℝ) {grid : ℕ} (i : AnnularGridIndex grid)
    (hi : i.time.1 = grid) :
    volume (annularGridCell ε A grid i) = 0 := by
  unfold annularGridCell
  rw [Measure.volume_eq_prod, Measure.prod_prod,
    volume_intervalGridCell_eq_zero_of_terminal 0 1 i.time hi, zero_mul]

/-- A terminal signed-coordinate singleton makes the whole annular cell
Lebesgue-null. -/
theorem volume_annularGridCell_eq_zero_of_signed_terminal
    (ε A : ℝ) {grid : ℕ} (i : AnnularGridIndex grid)
    (hi : i.signed.1 = grid) :
    volume (annularGridCell ε A grid i) = 0 := by
  unfold annularGridCell
  rw [Measure.volume_eq_prod, Measure.prod_prod,
    Measure.volume_eq_prod, Measure.prod_prod,
    volume_intervalGridCell_eq_zero_of_terminal
      (signedGridLower ε A i.sign) (signedGridUpper ε A i.sign)
      i.signed hi,
    zero_mul, mul_zero]

/-- A terminal torus-coordinate singleton makes the whole annular cell
Lebesgue-null. -/
theorem volume_annularGridCell_eq_zero_of_torus_terminal
    (ε A : ℝ) {grid : ℕ} (i : AnnularGridIndex grid)
    (hi : i.torus.1 = grid) :
    volume (annularGridCell ε A grid i) = 0 := by
  unfold annularGridCell
  rw [Measure.volume_eq_prod, Measure.prod_prod,
    Measure.volume_eq_prod, Measure.prod_prod,
    volume_intervalGridCell_eq_zero_of_terminal 0 1 i.torus hi,
    mul_zero, mul_zero]

/-- Any terminal coordinate gives zero raw annular intensity. -/
theorem annularRawStateMeasure_annularGridCell_eq_zero_of_terminal
    (ε A : ℝ) {grid : ℕ} (i : AnnularGridIndex grid)
    (hi : i.time.1 = grid ∨ i.signed.1 = grid ∨ i.torus.1 = grid) :
    annularRawStateMeasure ε A (annularGridCell ε A grid i) = 0 := by
  apply annularRawStateMeasure_absolutelyContinuous_volume ε A
  rcases hi with htime | hsigned | htorus
  · exact volume_annularGridCell_eq_zero_of_time_terminal ε A i htime
  · exact volume_annularGridCell_eq_zero_of_signed_terminal ε A i hsigned
  · exact volume_annularGridCell_eq_zero_of_torus_terminal ε A i htorus

/-- Consequently every terminal coordinate has exactly zero Poisson rate. -/
theorem annularGridCellPoissonRate_eq_zero_of_terminal
    (ε A : ℝ) {grid : ℕ} (i : AnnularGridIndex grid)
    (hi : i.time.1 = grid ∨ i.signed.1 = grid ∨ i.torus.1 = grid) :
    annularGridCellPoissonRate ε A grid i = 0 := by
  apply NNReal.eq
  rw [coe_annularGridCellPoissonRate, measureReal_def,
    annularRawStateMeasure_annularGridCell_eq_zero_of_terminal
      ε A i hi]
  simp

/-- If a mixed factorial order uses a terminal cell positively, its target
Poisson product is exactly zero. -/
theorem prod_annularGridCellPoissonRate_pow_eq_zero_of_active_terminal
    (ε A : ℝ) {grid : ℕ} (k : AnnularGridIndex grid → ℕ)
    {i : AnnularGridIndex grid} (hki : 0 < k i)
    (hi : i.time.1 = grid ∨ i.signed.1 = grid ∨ i.torus.1 = grid) :
    (∏ j, (annularGridCellPoissonRate ε A grid j : ℝ) ^ k j) = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [annularGridCellPoissonRate_eq_zero_of_terminal ε A i hi]
  simp [Nat.ne_of_gt hki]

/-! ## The torus terminal cell is literally empty -/

/-- The torus coordinate of every concrete Gauss-prefix marked point is
strictly below one. -/
theorem gaussPrefixMarkedPoint_torus_lt_one
    (N n : ℕ) (w : PositiveDigitWord n) (x : ℝ) :
    (gaussPrefixMarkedPoint N n w x).2.2 < 1 := by
  unfold gaussPrefixMarkedPoint
  exact Int.fract_lt_one _

/-- No literal Gauss-prefix marked event can land in a terminal torus cell.
This is pointwise, not merely an almost-everywhere assertion. -/
theorem gaussPrefixMarkedEvent_annularGridCell_eq_empty_of_torus_terminal
    (N n : ℕ) (ε A : ℝ) {grid : ℕ} (i : AnnularGridIndex grid)
    (hi : i.torus.1 = grid) :
    gaussPrefixMarkedEvent N (annularGridCell ε A grid i) n = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  obtain ⟨w, _hw, _hden, _htheta, hpoint⟩ :=
    mem_gaussPrefixMarkedEvent_iff.mp hx
  have htorus :
      (gaussPrefixMarkedPoint N n w x).2.2 ∈
        intervalGridCell 0 1 grid i.torus :=
    hpoint.2.2
  rw [intervalGridCell_eq_singleton_of_terminal 0 1 i.torus hi] at htorus
  have hone : (gaussPrefixMarkedPoint N n w x).2.2 = 1 := by
    simpa only [Set.mem_singleton_iff] using! htorus
  exact (ne_of_lt (gaussPrefixMarkedPoint_torus_lt_one N n w x)) hone

/-- Hence the count in a terminal torus cell is identically zero. -/
theorem gaussPrefixMarkedCount_annularGridCell_eq_zero_of_torus_terminal
    (N : ℕ) (ε A : ℝ) {grid : ℕ} (i : AnnularGridIndex grid)
    (hi : i.torus.1 = grid) (x : ℝ) :
    gaussPrefixMarkedCount N (annularGridCell ε A grid i) x = 0 := by
  unfold gaussPrefixMarkedCount
  apply Finset.sum_eq_zero
  intro n hn
  rw [gaussPrefixMarkedEvent_annularGridCell_eq_empty_of_torus_terminal
    N n ε A i hi]
  simp

/-! ## The time terminal cell contains only the denominator `N` -/

/-- Equality to the right endpoint of logarithmic time forces equality of
the two positive natural denominators. -/
theorem eq_of_resonanceTimeCoordinate_eq_one
    {N p : ℕ} (hN : 0 < N) (hp : 0 < p)
    (htime : resonanceTimeCoordinate N p = 1) :
    p = N := by
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hpreal : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hlogN : Real.log (N : ℝ) ≠ 0 := by
    intro hzero
    have hNOne : (N : ℝ) = 1 := by
      have := congrArg Real.exp hzero
      simpa [Real.exp_log hNreal] using! this
    have htimeZero : resonanceTimeCoordinate N p = 0 := by
      unfold resonanceTimeCoordinate
      rw [hzero, div_zero]
    linarith
  have hlogEq : Real.log (p : ℝ) = Real.log (N : ℝ) := by
    unfold resonanceTimeCoordinate at htime
    apply (div_eq_one_iff_eq hlogN).mp htime
  have hcast : (p : ℝ) = (N : ℝ) := by
    have hexp := congrArg Real.exp hlogEq
    simpa [Real.exp_log hpreal, Real.exp_log hNreal] using! hexp
  exact_mod_cast hcast

/-- Membership in a terminal time cell forces the literal marked
denominator to be exactly `N`. -/
theorem eq_terminalDenominator_of_markedResonancePoint_mem_time_terminal
    {N p grid : ℕ} (hN : 0 < N) (hp : 0 < p)
    (ε A α : ℝ) (i : AnnularGridIndex grid)
    (hi : i.time.1 = grid)
    (hpoint : markedResonancePoint N p α ∈
      annularGridCell ε A grid i) :
    p = N := by
  have htime :
      resonanceTimeCoordinate N p ∈
        intervalGridCell 0 1 grid i.time :=
    hpoint.1
  rw [intervalGridCell_eq_singleton_of_terminal 0 1 i.time hi] at htime
  apply eq_of_resonanceTimeCoordinate_eq_one hN hp
  simpa only [Set.mem_singleton_iff] using! htime

/-- The actual marked count in a terminal time cell is at most one: only
the single denominator `p=N` can contribute. -/
theorem markedResonanceCount_annularGridCell_le_one_of_time_terminal
    {N grid : ℕ} (hN : 0 < N)
    (ε A α : ℝ) (i : AnnularGridIndex grid)
    (hi : i.time.1 = grid) :
    markedResonanceCount N N (annularGridCell ε A grid i) α ≤ 1 := by
  classical
  unfold markedResonanceCount
  calc
    (∑ p ∈ Finset.Icc 1 N,
        if IsPrimitiveResonance p α ∧
            markedResonancePoint N p α ∈
              annularGridCell ε A grid i then 1 else 0) ≤
      ∑ p ∈ Finset.Icc 1 N, if p = N then 1 else 0 := by
        apply Finset.sum_le_sum
        intro p hpIcc
        by_cases hevent :
            IsPrimitiveResonance p α ∧
              markedResonancePoint N p α ∈
                annularGridCell ε A grid i
        · have hpPos : 0 < p := by
            have := (Finset.mem_Icc.mp hpIcc).1
            omega
          have hpEq :=
            eq_terminalDenominator_of_markedResonancePoint_mem_time_terminal
              hN hpPos ε A α i hi hevent.2
          subst p
          rw [if_pos hevent]
          simp
        · simp [hevent]
    _ = 1 := by
      rw [Finset.sum_eq_single N]
      · simp
      · intro p hpIcc hpNe
        simp [hpNe]
      · intro hNnot
        exact (hNnot (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)).elim

/-- On the full-measure denominator/depth correspondence set, the same
one-point bound holds for the Gauss-prefix terminal-time count. -/
theorem ae_gaussPrefixMarkedCount_annularGridCell_le_one_of_time_terminal
    {N grid : ℕ} (hN : 2 ≤ N)
    {ε A : ℝ} (hε : 0 ≤ ε)
    (hlog : 2 * A < Real.log (N : ℝ))
    (i : AnnularGridIndex grid)
    (hi : i.time.1 = grid)
    (hcell :
      annularGridCell ε A grid i ⊆ compactAnnularMarkedRegion ε A) :
    ∀ᵐ α ∂uniform01Measure,
      gaussPrefixMarkedCount N (annularGridCell ε A grid i) α ≤ 1 := by
  filter_upwards
    [ae_markedResonanceCount_eq_gaussPrefixMarkedCount
      hN hε hlog hcell] with α hcount
  rw [← hcount]
  exact markedResonanceCount_annularGridCell_le_one_of_time_terminal
    (by omega) ε A α i hi

/-- A nonzero count in the terminal time cell is contained in the single
primitive resonance band with denominator `N`. -/
theorem markedResonanceCount_time_terminal_pos_subset_terminalBand
    {N grid : ℕ} (hN : 2 ≤ N)
    {ε A : ℝ} (hε : 0 ≤ ε) (hεA : ε < A)
    (hgrid : 0 < grid) (i : AnnularGridIndex grid)
    (hi : i.time.1 = grid) :
    Ioo (0 : ℝ) 1 ∩
        {α | 0 <
          markedResonanceCount N N
            (annularGridCell ε A grid i) α} ⊆
      scaledPrimitiveResonanceBand N N A := by
  intro α hα
  rcases hα with ⟨hunit, hcount⟩
  unfold markedResonanceCount at hcount
  change 0 <
    ∑ p ∈ Finset.Icc 1 N,
      if IsPrimitiveResonance p α ∧
          markedResonancePoint N p α ∈
            annularGridCell ε A grid i then 1 else 0 at hcount
  rw [Finset.sum_pos_iff] at hcount
  obtain ⟨p, hpIcc, hpTerm⟩ := hcount
  by_cases hevent :
      IsPrimitiveResonance p α ∧
        markedResonancePoint N p α ∈ annularGridCell ε A grid i
  · have hpPos : 0 < p := by
      have := (Finset.mem_Icc.mp hpIcc).1
      omega
    have hpEq :=
      eq_terminalDenominator_of_markedResonancePoint_mem_time_terminal
        (by omega) hpPos ε A α i hi hevent.2
    subst p
    have hcompact :=
      annularGridCell_subset_compactAnnularMarkedRegion
        hεA hgrid i hevent.2
    have hsigned :
        |(markedResonancePoint N N α).2.1| ≤ A := by
      exact
        ((mem_signedAnnulus_iff_abs hε).mp hcompact.2.1).2
    exact ⟨hunit, hevent.1, hsigned⟩
  · simp [hevent] at hpTerm

/-- Quantitative deletion bound for the terminal time singleton. -/
theorem uniform01Measure_real_markedResonanceCount_time_terminal_pos_le
    {N grid : ℕ} (hN : 2 ≤ N)
    {ε A : ℝ} (hε : 0 ≤ ε) (hεA : ε < A)
    (hgrid : 0 < grid) (i : AnnularGridIndex grid)
    (hi : i.time.1 = grid) :
    uniform01Measure.real
        {α | 0 <
          markedResonanceCount N N
            (annularGridCell ε A grid i) α} ≤
      2 * A / Real.log (N : ℝ) := by
  let E : Set ℝ :=
    {α | 0 <
      markedResonanceCount N N (annularGridCell ε A grid i) α}
  let B : Set ℝ := scaledPrimitiveResonanceBand N N A
  have hE : MeasurableSet E := by
    exact measurableSet_lt measurable_const
      (measurable_markedResonanceCount N N
        (measurableSet_annularGridCell ε A grid i))
  have hsub : Ioo (0 : ℝ) 1 ∩ E ⊆ B := by
    exact markedResonanceCount_time_terminal_pos_subset_terminalBand
      hN hε hεA hgrid i hi
  have hBsub : B ⊆ Icc (0 : ℝ) 1 := by
    intro α hα
    exact ⟨hα.1.1.le, hα.1.2.le⟩
  have hBne : volume B ≠ ⊤ := by
    apply measure_ne_top_of_subset hBsub
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  rw [uniform01Measure, measureReal_restrict_apply hE]
  calc
    volume.real (E ∩ Ioo (0 : ℝ) 1) =
        volume.real (Ioo (0 : ℝ) 1 ∩ E) := by rw [inter_comm]
    _ ≤ volume.real B := measureReal_mono hsub hBne
    _ ≤ (2 * A / Real.log (N : ℝ)) *
        ((Nat.totient N : ℝ) / (N : ℝ) ^ 2) := by
      exact volumeReal_scaledPrimitiveResonanceBand_le hN hN
        (hε.trans hεA.le)
    _ ≤ 2 * A / Real.log (N : ℝ) := by
      have hlog : 0 < Real.log (N : ℝ) :=
        Real.log_pos (by exact_mod_cast hN)
      have hNreal : (1 : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast (show 1 ≤ N by omega)
      have hphi : (Nat.totient N : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast totient_le_self N
      have hratio :
          (Nat.totient N : ℝ) / (N : ℝ) ^ 2 ≤ 1 := by
        apply (div_le_one (sq_pos_of_pos (by positivity))).mpr
        nlinarith [sq_nonneg ((N : ℝ) - 1)]
      have hfactor : 0 ≤ 2 * A / Real.log (N : ℝ) := by
        exact div_nonneg (mul_nonneg (by norm_num) (hε.trans hεA.le))
          hlog.le
      nlinarith

/-- The corresponding terminal-time event for the Gauss-prefix count has
the same quantitative bound once the exact denominator/depth bijection is
available. -/
theorem uniform01Measure_real_gaussPrefixMarkedCount_time_terminal_pos_le
    {N grid : ℕ} (hN : 2 ≤ N)
    {ε A : ℝ} (hε : 0 ≤ ε) (hεA : ε < A)
    (hgrid : 0 < grid)
    (hlog : 2 * A < Real.log (N : ℝ))
    (i : AnnularGridIndex grid)
    (hi : i.time.1 = grid) :
    uniform01Measure.real
        {α | 0 <
          gaussPrefixMarkedCount N
            (annularGridCell ε A grid i) α} ≤
      2 * A / Real.log (N : ℝ) := by
  have hcount :
      markedResonanceCount N N (annularGridCell ε A grid i) =ᵐ[
          uniform01Measure]
        gaussPrefixMarkedCount N (annularGridCell ε A grid i) :=
    ae_markedResonanceCount_eq_gaussPrefixMarkedCount
      hN hε hlog
        (annularGridCell_subset_compactAnnularMarkedRegion hεA hgrid i)
  have hsets :
      {α | 0 <
          gaussPrefixMarkedCount N (annularGridCell ε A grid i) α} =ᵐ[
            uniform01Measure]
        {α | 0 <
          markedResonanceCount N N (annularGridCell ε A grid i) α} := by
    filter_upwards [hcount] with α hα
    apply propext
    change
      (0 <
        gaussPrefixMarkedCount N (annularGridCell ε A grid i) α) ↔
      (0 <
        markedResonanceCount N N (annularGridCell ε A grid i) α)
    rw [hα]
  have hmeasure :
      uniform01Measure.real
          {α | 0 <
            gaussPrefixMarkedCount N
              (annularGridCell ε A grid i) α} =
        uniform01Measure.real
          {α | 0 <
            markedResonanceCount N N
              (annularGridCell ε A grid i) α} := by
    rw [measureReal_def, measureReal_def, measure_congr hsets]
  rw [hmeasure]
  exact uniform01Measure_real_markedResonanceCount_time_terminal_pos_le
    hN hε hεA hgrid i hi

/-- For every fixed annular grid, a terminal time singleton disappears in
probability under the literal Gauss-prefix law. -/
theorem tendsto_uniform01Measure_real_gaussPrefixMarkedCount_time_terminal_pos
    {ε A : ℝ} (hε : 0 ≤ ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (i : AnnularGridIndex grid) (hi : i.time.1 = grid) :
    Tendsto
      (fun N : ℕ ↦ uniform01Measure.real
        {α | 0 <
          gaussPrefixMarkedCount N
            (annularGridCell ε A grid i) α})
      atTop (nhds 0) := by
  have hlogTop := tendsto_log_natCast_atTop
  have hupper :
      Tendsto (fun N : ℕ ↦ 2 * A / Real.log (N : ℝ))
        atTop (nhds 0) :=
    hlogTop.const_div_atTop (2 * A)
  apply squeeze_zero'
  · exact Eventually.of_forall fun _N ↦ measureReal_nonneg
  · filter_upwards
      [eventually_ge_atTop 2,
        hlogTop.eventually_gt_atTop (2 * A)] with N hN hlog
    exact
      uniform01Measure_real_gaussPrefixMarkedCount_time_terminal_pos_le
        hN hε hεA hgrid hlog i hi
  · exact hupper

/-! ## Signed-coordinate terminal singletons are null -/

/-- A level set of one nondegenerate scaled resonance coordinate is
countable.  The nearest numerator maps it injectively into `ℤ`: within one
numerator cell the coordinate is a nonconstant affine function. -/
theorem countable_scaledResonanceCoordinate_levelSet
    {N p : ℕ} (hN : 2 ≤ N) (hp : 0 < p) (c : ℝ) :
    {α : ℝ | scaledResonanceCoordinate N p α = c}.Countable := by
  apply countable_of_injective_of_countable_image
    (f := resonanceNumerator p)
  · intro x hx y hy hnum
    have hlog : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast hN)
    have hpReal : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
    let scale : ℝ := Real.log (N : ℝ) * (p : ℝ)
    have hscale : 0 < scale := mul_pos hlog hpReal
    have hxEq :
        scale * resonanceDelta p x = c := by
      simpa only [scale, scaledResonanceCoordinate, mul_assoc] using! hx
    have hyEq :
        scale * resonanceDelta p y = c := by
      simpa only [scale, scaledResonanceCoordinate, mul_assoc] using! hy
    have hdelta : resonanceDelta p x = resonanceDelta p y := by
      apply mul_left_cancel₀ hscale.ne'
      exact hxEq.trans hyEq.symm
    unfold resonanceDelta at hdelta
    rw [hnum] at hdelta
    nlinarith
  · exact Set.to_countable _

/-- Hence every scaled-resonance level has zero Lebesgue measure. -/
theorem volume_scaledResonanceCoordinate_levelSet_eq_zero
    {N p : ℕ} (hN : 2 ≤ N) (hp : 0 < p) (c : ℝ) :
    volume {α : ℝ | scaledResonanceCoordinate N p α = c} = 0 :=
  (countable_scaledResonanceCoordinate_levelSet hN hp c).measure_zero
    volume

/-- The same level set is null under the uniform law. -/
theorem uniform01Measure_scaledResonanceCoordinate_levelSet_eq_zero
    {N p : ℕ} (hN : 2 ≤ N) (hp : 0 < p) (c : ℝ) :
    uniform01Measure
      {α : ℝ | scaledResonanceCoordinate N p α = c} = 0 := by
  rw [uniform01Measure, Measure.restrict_apply]
  · exact measure_mono_null inter_subset_left
      (volume_scaledResonanceCoordinate_levelSet_eq_zero hN hp c)
  · exact measurableSet_singleton c |>.preimage
      (measurable_scaledResonanceCoordinate N p)

/-- For a signed terminal singleton, the actual marked count is zero almost
everywhere for each fixed `N`. -/
theorem ae_markedResonanceCount_annularGridCell_eq_zero_of_signed_terminal
    {N grid : ℕ} (hN : 2 ≤ N)
    (ε A : ℝ) (i : AnnularGridIndex grid)
    (hi : i.signed.1 = grid) :
    markedResonanceCount N N (annularGridCell ε A grid i) =ᵐ[
      uniform01Measure] 0 := by
  have hnull (p : ℕ) (hpIcc : p ∈ Finset.Icc 1 N) :
      uniform01Measure
        {α |
          IsPrimitiveResonance p α ∧
            markedResonancePoint N p α ∈
              annularGridCell ε A grid i} = 0 := by
    have hp : 0 < p := by
      have := (Finset.mem_Icc.mp hpIcc).1
      omega
    apply measure_mono_null
      (t := {α |
        scaledResonanceCoordinate N p α =
          signedGridUpper ε A i.sign})
    · intro α hα
      have hsigned :
          (markedResonancePoint N p α).2.1 ∈
            intervalGridCell
              (signedGridLower ε A i.sign)
              (signedGridUpper ε A i.sign) grid i.signed :=
        hα.2.2.1
      rw [intervalGridCell_eq_singleton_of_terminal
        (signedGridLower ε A i.sign)
        (signedGridUpper ε A i.sign) i.signed hi] at hsigned
      simpa only [markedResonancePoint, Set.mem_singleton_iff] using!
        hsigned
    · exact
        uniform01Measure_scaledResonanceCoordinate_levelSet_eq_zero
          hN hp _
  have hall :
      ∀ᵐ α ∂uniform01Measure, ∀ p : ℕ,
        p ∈ Finset.Icc 1 N →
          ¬(IsPrimitiveResonance p α ∧
            markedResonancePoint N p α ∈
              annularGridCell ε A grid i) := by
    rw [ae_all_iff]
    intro p
    by_cases hpIcc : p ∈ Finset.Icc 1 N
    · exact (measure_eq_zero_iff_ae_notMem.mp (hnull p hpIcc)).mono
        fun α hα _hp ↦ hα
    · exact Eventually.of_forall fun _α hp ↦ (hpIcc hp).elim
  filter_upwards [hall] with α hα
  unfold markedResonanceCount
  apply Finset.sum_eq_zero
  intro p hpIcc
  rw [if_neg (hα p hpIcc)]

/-- Through the exact count bridge, the Gauss-prefix count in a signed
terminal singleton is also zero almost everywhere. -/
theorem ae_gaussPrefixMarkedCount_annularGridCell_eq_zero_of_signed_terminal
    {N grid : ℕ} (hN : 2 ≤ N)
    {ε A : ℝ} (hε : 0 ≤ ε) (hεA : ε < A)
    (hgrid : 0 < grid)
    (hlog : 2 * A < Real.log (N : ℝ))
    (i : AnnularGridIndex grid)
    (hi : i.signed.1 = grid) :
    gaussPrefixMarkedCount N (annularGridCell ε A grid i) =ᵐ[
      uniform01Measure] 0 := by
  filter_upwards
    [ae_markedResonanceCount_eq_gaussPrefixMarkedCount
      hN hε hlog
        (annularGridCell_subset_compactAnnularMarkedRegion hεA hgrid i),
      ae_markedResonanceCount_annularGridCell_eq_zero_of_signed_terminal
        hN ε A i hi] with α hbridge hzero
  rw [← hbridge, hzero]

/-! ## Factorial-moment consequences of zero boundary coordinates -/

open MultivariateFactorialMomentMethod

variable {ι : Type*} [Fintype ι]

/-- A positive falling-factorial order at a zero coordinate annihilates
the entire mixed monomial. -/
theorem mixedDescFactorial_eq_zero_of_coordinate_eq_zero
    (k x : ι → ℕ) {i : ι} (hki : 0 < k i) (hxi : x i = 0) :
    mixedDescFactorial k x = 0 := by
  unfold mixedDescFactorial
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [hxi, Nat.descFactorial_eq_zero_iff_lt.mpr hki]
  norm_num

/-- A common natural-valued dominator controls a complete mixed
falling-factorial monomial by the corresponding power of total order. -/
theorem mixedDescFactorial_le_dominator_pow
    (k x : ι → ℕ) (D : ℕ) (hdom : ∀ i, x i ≤ D) :
    mixedDescFactorial k x ≤ (D : ℝ) ^ (∑ i, k i) := by
  unfold mixedDescFactorial
  calc
    (∏ i, ((x i).descFactorial (k i) : ℝ)) ≤
        ∏ i, (D : ℝ) ^ k i := by
      apply Finset.prod_le_prod
      · intro i _hi
        positivity
      · intro i _hi
        calc
          ((x i).descFactorial (k i) : ℝ) ≤
              (x i : ℝ) ^ k i := by
            exact_mod_cast Nat.descFactorial_le_pow (x i) (k i)
          _ ≤ (D : ℝ) ^ k i := by
            gcongr
            exact_mod_cast hdom i
    _ = (D : ℝ) ^ (∑ i, k i) := by
      rw [Finset.prod_pow_eq_pow_sum]

/-- Measurability of a mixed falling-factorial monomial of finitely many
measurable natural-valued coordinates. -/
theorem measurable_mixedDescFactorial_comp
    {Ω : Type*} [MeasurableSpace Ω]
    (k : ι → ℕ) (X : Ω → ι → ℕ)
    (hX : ∀ i, Measurable (fun ω ↦ X ω i)) :
    Measurable (fun ω ↦ mixedDescFactorial k (X ω)) := by
  unfold mixedDescFactorial
  apply Finset.measurable_fun_prod
  intro i _hi
  exact
    (measurable_of_countable
      (fun n : ℕ ↦ (n.descFactorial (k i) : ℝ))).comp (hX i)

/-- Rare-coordinate deletion in the exact form used by terminal annular
cells.  A positive factorial order at coordinate `i` makes the mixed
monomial supported on `{X_i > 0}`.  If every coordinate is dominated by a
natural-valued `D` with a uniform moment of twice the total order, the full
mixed integral tends to zero as soon as that support probability does.

This lemma deliberately isolates the required higher-moment input: using
only convergence in probability here would be invalid. -/
theorem tendsto_integral_mixedDescFactorial_of_rare_coordinate
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ι → ℕ) (D : ℕ → Ω → ℕ)
    (k : ι → ℕ) {i : ι} (hki : 0 < k i)
    (hX : ∀ n j, Measurable (fun ω ↦ X n ω j))
    (hdom : ∀ n, ∀ᵐ ω ∂μ, ∀ j, X n ω j ≤ D n ω)
    (hrare :
      Tendsto
        (fun n ↦ μ.real {ω | 0 < X n ω i})
        atTop (nhds 0))
    (hDmoment : ∀ n,
      Integrable
        (fun ω ↦ (D n ω : ℝ) ^ (2 * (∑ j, k j))) μ)
    {C : ℝ}
    (hC : ∀ n,
      ∫ ω, (D n ω : ℝ) ^ (2 * (∑ j, k j)) ∂μ ≤ C) :
    Tendsto
      (fun n ↦ ∫ ω, mixedDescFactorial k (X n ω) ∂μ)
      atTop (nhds 0) := by
  let r : ℕ := ∑ j, k j
  let f : ℕ → Ω → ℝ :=
    fun n ω ↦ mixedDescFactorial k (X n ω)
  let E : ℕ → Set Ω := fun n ↦ {ω | 0 < X n ω i}
  have hf : ∀ n, Measurable (f n) := by
    intro n
    exact measurable_mixedDescFactorial_comp k (X n) (hX n)
  have hf_nonneg : ∀ n ω, 0 ≤ f n ω := by
    intro n ω
    dsimp only [f, mixedDescFactorial]
    exact Finset.prod_nonneg fun j _hj ↦ by positivity
  have hE : ∀ n, MeasurableSet (E n) := by
    intro n
    exact measurableSet_lt measurable_const (hX n i)
  have hf_le : ∀ n, ∀ᵐ ω ∂μ,
      f n ω ≤ (D n ω : ℝ) ^ r := by
    intro n
    filter_upwards [hdom n] with ω hω
    exact mixedDescFactorial_le_dominator_pow
      k (X n ω) (D n ω) hω
  have hf_sq : ∀ n, Integrable (fun ω ↦ f n ω ^ 2) μ := by
    intro n
    have hDint :
        Integrable (fun ω ↦ (D n ω : ℝ) ^ (2 * r)) μ := by
      simpa only [r] using! hDmoment n
    apply hDint.mono'
      ((hf n).pow_const 2).aestronglyMeasurable
    filter_upwards [hf_le n] with ω hω
    rw [Real.norm_of_nonneg (sq_nonneg (f n ω))]
    have hsq :
        f n ω ^ 2 ≤ ((D n ω : ℝ) ^ r) ^ 2 :=
      pow_le_pow_left₀ (hf_nonneg n ω) hω 2
    simpa only [r, two_mul, pow_add, pow_two] using! hsq
  have hf_sq_bound : ∀ n, ∫ ω, f n ω ^ 2 ∂μ ≤ C := by
    intro n
    calc
      (∫ ω, f n ω ^ 2 ∂μ) ≤
          ∫ ω, (D n ω : ℝ) ^ (2 * r) ∂μ := by
        apply integral_mono_ae (hf_sq n) (hDmoment n)
        filter_upwards [hf_le n] with ω hω
        have hsq :
            f n ω ^ 2 ≤ ((D n ω : ℝ) ^ r) ^ 2 :=
          pow_le_pow_left₀ (hf_nonneg n ω) hω 2
        simpa only [two_mul, pow_add, pow_two] using! hsq
      _ ≤ C := by simpa only [r] using! hC n
  have hset :
      Tendsto (fun n ↦ ∫ ω in E n, f n ω ∂μ)
        atTop (nhds 0) := by
    exact tendsto_setIntegral_zero_of_uniform_sq_integral
      μ f E hf hf_nonneg hf_sq hE (by simpa only [E] using! hrare)
        hf_sq_bound
  apply hset.congr'
  filter_upwards with n
  calc
    (∫ ω in E n, f n ω ∂μ) =
        ∫ ω, (E n).indicator (f n) ω ∂μ := by
      rw [integral_indicator (hE n)]
    _ = ∫ ω, f n ω ∂μ := by
      apply integral_congr_ae
      filter_upwards with ω
      by_cases hω : ω ∈ E n
      · simp [Set.indicator_of_mem hω]
      · have hzero : X n ω i = 0 := by
          dsimp only [E] at hω
          simp only [Set.mem_setOf_eq, not_lt] at hω
          omega
        have hfzero : f n ω = 0 := by
          exact mixedDescFactorial_eq_zero_of_coordinate_eq_zero
            k (X n ω) hki hzero
        simp [Set.indicator_of_notMem hω, hfzero]

/-- Coordinatewise uniform moments imply the dominator moment required by
the preceding rare-coordinate lemma.  The dominator is the sum of all
coordinates, and the finite-dimensional power-sum inequality controls its
moment. -/
theorem
    tendsto_integral_mixedDescFactorial_of_rare_coordinate_of_uniform_coordinate_moments
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ι → ℕ)
    (k : ι → ℕ) {i : ι} (hki : 0 < k i)
    (hX : ∀ n j, Measurable (fun ω ↦ X n ω j))
    (hrare :
      Tendsto
        (fun n ↦ μ.real {ω | 0 < X n ω i})
        atTop (nhds 0))
    (hXmoment : ∀ n j,
      Integrable
        (fun ω ↦ (X n ω j : ℝ) ^ (2 * (∑ q, k q))) μ)
    {Ccoord : ℝ}
    (hCcoord : ∀ n j,
      ∫ ω, (X n ω j : ℝ) ^ (2 * (∑ q, k q)) ∂μ ≤ Ccoord) :
    Tendsto
      (fun n ↦ ∫ ω, mixedDescFactorial k (X n ω) ∂μ)
      atTop (nhds 0) := by
  let r : ℕ := ∑ q, k q
  let s : ℕ := 2 * r
  let D : ℕ → Ω → ℕ := fun n ω ↦ ∑ j, X n ω j
  have hir : k i ≤ r := by
    dsimp only [r]
    exact Finset.single_le_sum
      (fun j _hj ↦ Nat.zero_le (k j)) (Finset.mem_univ i)
  have hr : 0 < r := hki.trans_le hir
  have hs : 0 < s := by
    dsimp only [s]
    omega
  have hsEq : s - 1 + 1 = s := by omega
  have hDdom : ∀ n, ∀ᵐ ω ∂μ, ∀ j, X n ω j ≤ D n ω := by
    intro n
    exact Eventually.of_forall fun ω j ↦ by
      dsimp only [D]
      exact Finset.single_le_sum
        (fun q _hq ↦ Nat.zero_le (X n ω q)) (Finset.mem_univ j)
  have hpow : ∀ n ω,
      (D n ω : ℝ) ^ s ≤
        (Fintype.card ι : ℝ) ^ (s - 1) *
          ∑ j, (X n ω j : ℝ) ^ s := by
    intro n ω
    have hraw :=
      pow_sum_le_card_mul_sum_pow
        (s := (Finset.univ : Finset ι))
        (f := fun j ↦ (X n ω j : ℝ))
        (fun j _hj ↦ by positivity) (s - 1)
    rw [hsEq] at hraw
    simpa only [D, Nat.cast_sum, Finset.card_univ] using! hraw
  have hDmoment : ∀ n,
      Integrable (fun ω ↦ (D n ω : ℝ) ^ s) μ := by
    intro n
    have hupper :
        Integrable
          (fun ω ↦
            (Fintype.card ι : ℝ) ^ (s - 1) *
              ∑ j, (X n ω j : ℝ) ^ s) μ := by
      apply Integrable.const_mul
      apply integrable_finset_sum
      intro j _hj
      simpa only [s, r] using! hXmoment n j
    have hmeas :
        StronglyMeasurable (fun ω ↦ (D n ω : ℝ) ^ s) := by
      exact
        (measurable_of_countable
          (fun q : ℕ ↦ (q : ℝ) ^ s)).comp
            (Finset.measurable_fun_sum _ fun j _hj ↦ hX n j)
          |>.stronglyMeasurable
    apply hupper.mono' hmeas.aestronglyMeasurable
    exact Eventually.of_forall fun ω ↦ by
      rw [Real.norm_of_nonneg (by positivity :
        0 ≤ (D n ω : ℝ) ^ s)]
      exact hpow n ω
  have hDbound : ∀ n,
      ∫ ω, (D n ω : ℝ) ^ s ∂μ ≤
        (Fintype.card ι : ℝ) ^ (s - 1) *
          ((Fintype.card ι : ℝ) * Ccoord) := by
    intro n
    have hupper :
        Integrable
          (fun ω ↦
            (Fintype.card ι : ℝ) ^ (s - 1) *
              ∑ j, (X n ω j : ℝ) ^ s) μ := by
      apply Integrable.const_mul
      apply integrable_finset_sum
      intro j _hj
      simpa only [s, r] using! hXmoment n j
    calc
      (∫ ω, (D n ω : ℝ) ^ s ∂μ) ≤
          ∫ ω,
            (Fintype.card ι : ℝ) ^ (s - 1) *
              ∑ j, (X n ω j : ℝ) ^ s ∂μ := by
        exact integral_mono (hDmoment n) hupper (hpow n)
      _ =
          (Fintype.card ι : ℝ) ^ (s - 1) *
            ∑ j, ∫ ω, (X n ω j : ℝ) ^ s ∂μ := by
        rw [integral_const_mul]
        congr 1
        rw [integral_finset_sum]
        intro j _hj
        simpa only [s, r] using! hXmoment n j
      _ ≤
          (Fintype.card ι : ℝ) ^ (s - 1) *
            ∑ _j : ι, Ccoord := by
        gcongr with j
        simpa only [s, r] using! hCcoord n j
      _ =
          (Fintype.card ι : ℝ) ^ (s - 1) *
            ((Fintype.card ι : ℝ) * Ccoord) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact
    tendsto_integral_mixedDescFactorial_of_rare_coordinate
      μ X D k hki hX hDdom hrare
      (by simpa only [s, r] using! hDmoment)
      (by simpa only [s, r] using! hDbound)

/-- An almost-everywhere zero count coordinate annihilates the corresponding
mixed factorial moment of the literal Gauss-prefix count law. -/
theorem mixedFactorialMoment_gaussPrefixMarkedCountVectorLaw_eq_zero_of_ae
    (N : ℕ) (B : ι → Set (ℝ × ℝ × ℝ))
    (hB : ∀ i, MeasurableSet (B i))
    (k : ι → ℕ) {i : ι} (hki : 0 < k i)
    (hzero : gaussPrefixMarkedCount N (B i) =ᵐ[uniform01Measure] 0) :
    mixedFactorialMoment
      (gaussPrefixMarkedCountVectorLaw N B hB) k = 0 := by
  rw [mixedFactorialMoment_gaussPrefixMarkedCountVectorLaw]
  apply integral_eq_zero_of_ae
  filter_upwards [hzero] with α hα
  apply mixedDescFactorial_eq_zero_of_coordinate_eq_zero k
    (gaussPrefixMarkedCountVector N B α) hki
  exact hα

/-- A terminal torus coordinate therefore gives an exactly zero mixed
factorial moment for every positive order at that coordinate. -/
theorem mixedFactorialMoment_gaussPrefixAnnular_eq_zero_of_active_torus_terminal
    (N : ℕ) (ε A : ℝ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    {i : AnnularGridIndex grid} (hki : 0 < k i)
    (hi : i.torus.1 = grid) :
    mixedFactorialMoment
      (gaussPrefixMarkedCountVectorLaw N
        (annularGridCell ε A grid)
        (fun j ↦ measurableSet_annularGridCell ε A grid j)) k = 0 := by
  apply
    mixedFactorialMoment_gaussPrefixMarkedCountVectorLaw_eq_zero_of_ae
      N (annularGridCell ε A grid)
        (fun j ↦ measurableSet_annularGridCell ε A grid j)
        k hki
  exact Eventually.of_forall fun α ↦
    gaussPrefixMarkedCount_annularGridCell_eq_zero_of_torus_terminal
      N ε A i hi α

/-- A terminal signed-coordinate singleton gives the same zero moment once
the exact denominator/depth bridge is valid. -/
theorem mixedFactorialMoment_gaussPrefixAnnular_eq_zero_of_active_signed_terminal
    {N grid : ℕ} (hN : 2 ≤ N)
    {ε A : ℝ} (hε : 0 ≤ ε) (hεA : ε < A)
    (hgrid : 0 < grid)
    (hlog : 2 * A < Real.log (N : ℝ))
    (k : AnnularGridIndex grid → ℕ)
    {i : AnnularGridIndex grid} (hki : 0 < k i)
    (hi : i.signed.1 = grid) :
    mixedFactorialMoment
      (gaussPrefixMarkedCountVectorLaw N
        (annularGridCell ε A grid)
        (fun j ↦ measurableSet_annularGridCell ε A grid j)) k = 0 := by
  apply
    mixedFactorialMoment_gaussPrefixMarkedCountVectorLaw_eq_zero_of_ae
      N (annularGridCell ε A grid)
        (fun j ↦ measurableSet_annularGridCell ε A grid j)
        k hki
  exact
    ae_gaussPrefixMarkedCount_annularGridCell_eq_zero_of_signed_terminal
      hN hε hεA hgrid hlog i hi

/-- If a terminal time coordinate occurs with factorial order at least two,
its mixed moment is already exactly zero because that coordinate count is
at most one.  The genuinely delicate terminal-time case is therefore only
order one. -/
theorem mixedFactorialMoment_gaussPrefixAnnular_eq_zero_of_time_terminal_order_two
    {N grid : ℕ} (hN : 2 ≤ N)
    {ε A : ℝ} (hε : 0 ≤ ε) (hεA : ε < A)
    (hgrid : 0 < grid)
    (hlog : 2 * A < Real.log (N : ℝ))
    (k : AnnularGridIndex grid → ℕ)
    {i : AnnularGridIndex grid} (hki : 2 ≤ k i)
    (hi : i.time.1 = grid) :
    mixedFactorialMoment
      (gaussPrefixMarkedCountVectorLaw N
        (annularGridCell ε A grid)
        (fun j ↦ measurableSet_annularGridCell ε A grid j)) k = 0 := by
  rw [mixedFactorialMoment_gaussPrefixMarkedCountVectorLaw]
  apply integral_eq_zero_of_ae
  filter_upwards
    [ae_gaussPrefixMarkedCount_annularGridCell_le_one_of_time_terminal
      hN hε hlog i hi
        (annularGridCell_subset_compactAnnularMarkedRegion hεA hgrid i)]
      with α hcount
  unfold mixedDescFactorial
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  have hdesc :
      (gaussPrefixMarkedCount N (annularGridCell ε A grid i) α).descFactorial
          (k i) = 0 :=
    Nat.descFactorial_eq_zero_iff_lt.mpr
      (lt_of_le_of_lt hcount (by omega))
  simp [gaussPrefixMarkedCountVector, hdesc]

/-- A Gauss-prefix marked count has the elementary deterministic bound
`N + 1`, since it is a sum of zero-one indicators over depths `0,...,N`. -/
theorem gaussPrefixMarkedCount_le_succ
    (N : ℕ) (B : Set (ℝ × ℝ × ℝ)) (α : ℝ) :
    gaussPrefixMarkedCount N B α ≤ N + 1 := by
  unfold gaussPrefixMarkedCount
  calc
    (∑ n ∈ Finset.Icc 0 N,
        if α ∈ gaussPrefixMarkedEvent N B n then 1 else 0) ≤
        ∑ _n ∈ Finset.Icc 0 N, 1 := by
      apply Finset.sum_le_sum
      intro n hn
      split <;> omega
    _ = N + 1 := by simp

/-- Consequently every fixed power of one finite Gauss-prefix marked count
is integrable.  This supplies the non-vacuous integrability side condition
for moment deletion; only the numerical uniform bound remains to be
proved by the factorial argument. -/
theorem integrable_gaussPrefixMarkedCount_pow
    (N s : ℕ) {B : Set (ℝ × ℝ × ℝ)} (hB : MeasurableSet B) :
    Integrable
      (fun α ↦ (gaussPrefixMarkedCount N B α : ℝ) ^ s)
      uniform01Measure := by
  have hmeas :
      Measurable
        (fun α ↦ (gaussPrefixMarkedCount N B α : ℝ) ^ s) :=
    ((measurable_of_countable (fun q : ℕ ↦ (q : ℝ))).comp
      (measurable_gaussPrefixMarkedCount N hB)).pow_const s
  apply Integrable.of_bound hmeas.aestronglyMeasurable
    (((N + 1 : ℕ) : ℝ) ^ s)
  exact ae_of_all _ fun α ↦ by
    rw [Real.norm_of_nonneg (by positivity)]
    gcongr
    exact_mod_cast gaussPrefixMarkedCount_le_succ N B α

/-- Terminal-time deletion at local order one (and, redundantly, at every
positive local order) under the exact higher-moment condition required by
Cauchy--Schwarz.  `D` may be any natural-valued dominator for the finite
count vector; thus the theorem can be fed either a total annular count or a
sum of already-controlled nonterminal cell counts.

The conclusion is the zero target dictated by the terminal singleton's
zero Poisson rate.  No assertion that convergence in probability alone
controls the remaining factorial factors is made. -/
theorem
    tendsto_mixedFactorialMoment_gaussPrefixAnnular_of_active_time_terminal_of_dominator
    {ε A : ℝ} (hε : 0 ≤ ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    {i : AnnularGridIndex grid} (hki : 0 < k i)
    (hi : i.time.1 = grid)
    (D : ℕ → ℝ → ℕ)
    (hdom : ∀ N, ∀ᵐ α ∂uniform01Measure,
      ∀ j : AnnularGridIndex grid,
        gaussPrefixMarkedCount N (annularGridCell ε A grid j) α ≤
          D N α)
    (hDmoment : ∀ N,
      Integrable
        (fun α ↦
          (D N α : ℝ) ^ (2 * (∑ j, k j)))
        uniform01Measure)
    {C : ℝ}
    (hC : ∀ N,
      ∫ α, (D N α : ℝ) ^ (2 * (∑ j, k j))
          ∂uniform01Measure ≤ C) :
    Tendsto
      (fun N ↦
        mixedFactorialMoment
          (gaussPrefixMarkedCountVectorLaw N
            (annularGridCell ε A grid)
            (fun j ↦ measurableSet_annularGridCell ε A grid j)) k)
      atTop (nhds 0) := by
  have hrare :=
    tendsto_uniform01Measure_real_gaussPrefixMarkedCount_time_terminal_pos
      hε hεA hgrid i hi
  have hdelete :=
    tendsto_integral_mixedDescFactorial_of_rare_coordinate
      uniform01Measure
      (fun N α ↦
        gaussPrefixMarkedCountVector N
          (annularGridCell ε A grid) α)
      D k hki
      (fun N j ↦ measurable_gaussPrefixMarkedCount N
        (measurableSet_annularGridCell ε A grid j))
      hdom hrare hDmoment hC
  apply hdelete.congr'
  filter_upwards with N
  rw [mixedFactorialMoment_gaussPrefixMarkedCountVectorLaw]

/-- A convenient specialization of terminal-time deletion: it suffices to
bound, uniformly in `N` and in the finitely many grid coordinates, the
ordinary moment of order twice the total mixed order of each individual
cell count.  The proof uses the sum of all coordinates as its dominator and
the finite-dimensional power-sum inequality. -/
theorem
    tendsto_mixedFactorialMoment_gaussPrefixAnnular_of_active_time_terminal_of_uniform_coordinate_moments
    {ε A : ℝ} (hε : 0 ≤ ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    {i : AnnularGridIndex grid} (hki : 0 < k i)
    (hi : i.time.1 = grid)
    {Ccoord : ℝ}
    (hCcoord : ∀ N (j : AnnularGridIndex grid),
      ∫ α,
        (gaussPrefixMarkedCount N
          (annularGridCell ε A grid j) α : ℝ) ^
            (2 * (∑ q, k q))
          ∂uniform01Measure ≤ Ccoord) :
    Tendsto
      (fun N ↦
        mixedFactorialMoment
          (gaussPrefixMarkedCountVectorLaw N
            (annularGridCell ε A grid)
            (fun j ↦ measurableSet_annularGridCell ε A grid j)) k)
      atTop (nhds 0) := by
  have hrare :=
    tendsto_uniform01Measure_real_gaussPrefixMarkedCount_time_terminal_pos
      hε hεA hgrid i hi
  have hdelete :=
    tendsto_integral_mixedDescFactorial_of_rare_coordinate_of_uniform_coordinate_moments
      uniform01Measure
      (fun N α ↦
        gaussPrefixMarkedCountVector N
          (annularGridCell ε A grid) α)
      k hki
      (fun N j ↦ measurable_gaussPrefixMarkedCount N
        (measurableSet_annularGridCell ε A grid j))
      hrare
      (fun N j ↦
        integrable_gaussPrefixMarkedCount_pow N
          (2 * (∑ q, k q))
          (measurableSet_annularGridCell ε A grid j))
      hCcoord
  apply hdelete.congr'
  filter_upwards with N
  rw [mixedFactorialMoment_gaussPrefixMarkedCountVectorLaw]

/-! ## Exact nonterminal target intensity -/

/-- Restricting Lebesgue measure to a set containing `(a,b)` does not
alter the mass of a half-open subinterval of `[a,b]`, apart from the null
left endpoint. -/
theorem volume_restrict_real_Ico_eq_sub_of_Ioo_subset
    {a b left right : ℝ}
    (haleft : a ≤ left) (hlr : left ≤ right) (hrightb : right ≤ b)
    {S : Set ℝ} (hS : Ioo a b ⊆ S) :
    (volume.restrict S).real (Ico left right) = right - left := by
  have hae :
      (Ico left right ∩ S : Set ℝ) =ᵐ[volume]
        (Ico left right : Set ℝ) := by
    filter_upwards [(volume : Measure ℝ).ae_ne a] with x hxa
    apply propext
    constructor
    · exact fun hx ↦ hx.1
    · intro hx
      refine ⟨hx, hS ⟨?_, ?_⟩⟩
      · exact lt_of_le_of_ne (haleft.trans hx.1) (Ne.symm hxa)
      · exact hx.2.trans_le hrightb
  rw [measureReal_def, Measure.restrict_apply measurableSet_Ico,
    measure_congr hae, Real.volume_Ico,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hlr)]

/-- Exact length of every nonterminal time or torus grid interval under
the uniform law. -/
theorem uniform01Measure_real_intervalGridCell_eq_width
    {grid : ℕ} (hgrid : 0 < grid)
    (i : IntervalGridIndex grid) (hi : i.1 < grid) :
    uniform01Measure.real (intervalGridCell 0 1 grid i) =
      intervalGridPoint 0 1 grid (i.1 + 1) -
        intervalGridPoint 0 1 grid i.1 := by
  have hleft :=
    intervalGridPoint_mem_Icc
      (a := (0 : ℝ)) (b := 1) zero_le_one hgrid
      (Nat.le_of_lt hi)
  have hright :=
    intervalGridPoint_mem_Icc
      (a := (0 : ℝ)) (b := 1) zero_le_one hgrid
      (show i.1 + 1 ≤ grid by omega)
  have hstep :=
    intervalGridPoint_strictMono_step
      (a := (0 : ℝ)) (b := 1) zero_lt_one hgrid
      (k := i.1)
  unfold uniform01Measure intervalGridCell
  rw [if_pos hi]
  exact volume_restrict_real_Ico_eq_sub_of_Ioo_subset
    hleft.1 hstep.le hright.2 (fun _x hx ↦ hx)

/-- Exact length of every nonterminal signed grid interval under the
signed-annulus measure. -/
theorem signedAnnulusFiniteMeasure_real_intervalGridCell_eq_width
    {ε A : ℝ} (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (i : AnnularGridIndex grid) (hi : i.signed.1 < grid) :
    (signedAnnulusFiniteMeasure ε A : Measure ℝ).real
        (intervalGridCell
          (signedGridLower ε A i.sign)
          (signedGridUpper ε A i.sign) grid i.signed) =
      intervalGridPoint
          (signedGridLower ε A i.sign)
          (signedGridUpper ε A i.sign) grid (i.signed.1 + 1) -
        intervalGridPoint
          (signedGridLower ε A i.sign)
          (signedGridUpper ε A i.sign) grid i.signed.1 := by
  have hleft :=
    intervalGridPoint_mem_Icc
      (signedGridLower_lt_upper hεA i.sign).le hgrid
      (Nat.le_of_lt hi)
  have hright :=
    intervalGridPoint_mem_Icc
      (signedGridLower_lt_upper hεA i.sign).le hgrid
      (show i.signed.1 + 1 ≤ grid by omega)
  have hstep :=
    intervalGridPoint_strictMono_step
      (signedGridLower_lt_upper hεA i.sign) hgrid
      (k := i.signed.1)
  rw [signedAnnulusFiniteMeasure_toMeasure]
  unfold intervalGridCell
  rw [if_pos hi]
  apply volume_restrict_real_Ico_eq_sub_of_Ioo_subset
    hleft.1 hstep.le hright.2
  intro x hx
  cases hs : i.sign
  · exact Or.inl (by
      simpa [signedGridLower, signedGridUpper, signedAnnulusSet, hs]
        using! hx)
  · exact Or.inr (by
      simpa [signedGridLower, signedGridUpper, signedAnnulusSet, hs]
        using! hx)

/-- For a fully nonterminal cell, the geometric Poisson rate is exactly
the product of its three coordinate widths divided by `π²/6`. -/
theorem annularGridCellPoissonRate_eq_width_product_of_nonterminal
    {ε A : ℝ} (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (i : AnnularGridIndex grid)
    (htime : i.time.1 < grid)
    (hsigned : i.signed.1 < grid)
    (htorus : i.torus.1 < grid) :
    (annularGridCellPoissonRate ε A grid i : ℝ) =
      ((intervalGridPoint 0 1 grid (i.time.1 + 1) -
          intervalGridPoint 0 1 grid i.time.1) *
        (intervalGridPoint
            (signedGridLower ε A i.sign)
            (signedGridUpper ε A i.sign) grid (i.signed.1 + 1) -
          intervalGridPoint
            (signedGridLower ε A i.sign)
            (signedGridUpper ε A i.sign) grid i.signed.1) *
        (intervalGridPoint 0 1 grid (i.torus.1 + 1) -
          intervalGridPoint 0 1 grid i.torus.1)) /
        (Real.pi ^ 2 / 6) := by
  rw [coe_annularGridCellPoissonRate]
  have htimeMass :=
    uniform01Measure_real_intervalGridCell_eq_width
      hgrid i.time htime
  have hsignedMass :=
    signedAnnulusFiniteMeasure_real_intervalGridCell_eq_width
      hεA hgrid i hsigned
  have htorusMass :=
    uniform01Measure_real_intervalGridCell_eq_width
      hgrid i.torus htorus
  unfold annularRawStateMeasure annularGridCell
  rw [measureReal_prod_prod, measureReal_prod_prod,
    htimeMass, hsignedMass, htorusMass]
  ring

/-- The product of the canonical time, signed, and literal torus-width
densities over all labeled occurrences is exactly the product of the
geometric Poisson cell rates.  This is where the Lévy roof mean
`π²/(12 log 2)` supplies the intensity constant `1/(π²/6)`. -/
theorem annularOccurrence_fullWidthDensity_eq_prod_poissonRate
    {ε A : ℝ} (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (htorus : ∀ i, 0 < k i → i.torus.1 < grid) :
    annularOccurrenceTimeDensity k *
        annularOccurrenceSignedDensity ε A k *
        (∏ z : GaussPrefixMixedOccurrence k,
          (intervalGridPoint 0 1 grid (z.1.torus.1 + 1) -
            intervalGridPoint 0 1 grid z.1.torus.1)) =
      ∏ i, (annularGridCellPoissonRate ε A grid i : ℝ) ^ k i := by
  have hfactor (z : GaussPrefixMixedOccurrence k) :
      ((intervalGridPoint 0 1 grid (z.1.time.1 + 1) -
            intervalGridPoint 0 1 grid z.1.time.1) /
          (2 * gaussRoofMean)) *
          ((intervalGridPoint
                (signedGridLower ε A z.1.sign)
                (signedGridUpper ε A z.1.sign)
                grid (z.1.signed.1 + 1) -
              intervalGridPoint
                (signedGridLower ε A z.1.sign)
                (signedGridUpper ε A z.1.sign)
                grid z.1.signed.1) /
            Real.log 2) *
          (intervalGridPoint 0 1 grid (z.1.torus.1 + 1) -
            intervalGridPoint 0 1 grid z.1.torus.1) =
        (annularGridCellPoissonRate ε A grid z.1 : ℝ) := by
    have hactive : 0 < k z.1 := by
      have hz := z.2.isLt
      omega
    rw [annularGridCellPoissonRate_eq_width_product_of_nonterminal
      hεA hgrid z.1 (htime z.1 hactive)
        (hsigned z.1 hactive) (htorus z.1 hactive)]
    rw [gaussRoofMean_eq_pi_sq_div_log_two]
    have hlogTwo : Real.log 2 ≠ 0 :=
      ne_of_gt (Real.log_pos (by norm_num))
    field_simp [hlogTwo, Real.pi_ne_zero]
    ring
  unfold annularOccurrenceTimeDensity annularOccurrenceSignedDensity
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  calc
    (∏ z : GaussPrefixMixedOccurrence k,
        ((intervalGridPoint 0 1 grid (z.1.time.1 + 1) -
              intervalGridPoint 0 1 grid z.1.time.1) /
            (2 * gaussRoofMean) *
          ((intervalGridPoint
                (signedGridLower ε A z.1.sign)
                (signedGridUpper ε A z.1.sign)
                grid (z.1.signed.1 + 1) -
              intervalGridPoint
                (signedGridLower ε A z.1.sign)
                (signedGridUpper ε A z.1.sign)
                grid z.1.signed.1) /
              Real.log 2) *
          (intervalGridPoint 0 1 grid (z.1.torus.1 + 1) -
            intervalGridPoint 0 1 grid z.1.torus.1))) =
        ∏ z : GaussPrefixMixedOccurrence k,
          (annularGridCellPoissonRate ε A grid z.1 : ℝ) := by
      apply Finset.prod_congr rfl
      intro z _hz
      exact hfactor z
    _ = ∏ i,
        (annularGridCellPoissonRate ε A grid i : ℝ) ^ k i := by
      rw [Fintype.prod_sigma]
      apply Finset.prod_congr rfl
      intro i _hi
      change
        (∏ _y : Fin (k i),
          (annularGridCellPoissonRate ε A grid i : ℝ)) =
          (annularGridCellPoissonRate ε A grid i : ℝ) ^ k i
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

local instance unitAddCircleMeasureSpaceBoundaryCells :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance unitAddCircleProbabilityBoundaryCells :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- A quotient-circle half-open arc of length strictly less than one is
Borel.  It is a compact closed arc with its right endpoint removed; strict
length prevents the two endpoint classes from coinciding. -/
theorem measurableSet_unitAddCircleHalfOpenArc_of_lt_one
    {a b : ℝ} (hab : a < b) (hwidth : b < a + 1) :
    MeasurableSet (unitAddCircleHalfOpenArc a b) := by
  let q : ℝ → UnitAddCircle := fun x ↦ (x : UnitAddCircle)
  have hset :
      unitAddCircleHalfOpenArc a b =
        q '' Icc a b \ {q b} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨x, ⟨hx.1, hx.2.le⟩, rfl⟩, ?_⟩
      simp only [Set.mem_singleton_iff]
      intro heq
      have hxFund : x ∈ Ico a (a + 1) :=
        ⟨hx.1, hx.2.trans hwidth⟩
      have hbFund : b ∈ Ico a (a + 1) :=
        ⟨hab.le, hwidth⟩
      have hxb :=
        (AddCircle.coe_eq_coe_iff_of_mem_Ico hxFund hbFund).mp heq
      exact hx.2.ne hxb
    · rintro ⟨⟨x, hx, rfl⟩, hne⟩
      refine ⟨x, ⟨hx.1, ?_⟩, rfl⟩
      apply lt_of_le_of_ne hx.2
      intro hxb
      apply hne
      simp only [Set.mem_singleton_iff]
      exact congrArg q hxb
  rw [hset]
  exact
    ((isCompact_Icc.image
      (AddCircle.continuous_mk' (1 : ℝ))).isClosed.measurableSet).diff
        (measurableSet_singleton (q b))

/-- Exact Haar mass of a quotient-circle half-open arc whose real lift has
length strictly between zero and one.  The proof uses the literal
measure-preserving fundamental domain `(b-1,b]` and checks its preimage,
rather than treating quotient endpoints informally. -/
theorem volume_real_unitAddCircleHalfOpenArc_eq_sub_of_lt_one
    {a b : ℝ} (hab : a < b) (hwidth : b < a + 1) :
    (volume : Measure UnitAddCircle).real
        (unitAddCircleHalfOpenArc a b) = b - a := by
  let q : ℝ → UnitAddCircle := fun x ↦ (x : UnitAddCircle)
  have hmeas :
      MeasurableSet (unitAddCircleHalfOpenArc a b) :=
    measurableSet_unitAddCircleHalfOpenArc_of_lt_one hab hwidth
  have hpre :
      q ⁻¹' unitAddCircleHalfOpenArc a b ∩ Ioc (b - 1) b =
        Ico a b := by
    have hend : (b - 1) + 1 = b := by ring
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := hx.1
      have hyDomain : y ∈ Ioc (b - 1) b := by
        constructor
        · linarith [hwidth, hy.1]
        · exact hy.2.le
      have heq :
          (AddCircle.equivIoc 1 (b - 1)) (q y) =
            (AddCircle.equivIoc 1 (b - 1)) (q x) :=
        congrArg (AddCircle.equivIoc 1 (b - 1)) hyx
      have hyDomain' : y ∈ Ioc (b - 1) ((b - 1) + 1) := by
        simpa only [hend] using! hyDomain
      have hxDomain' : x ∈ Ioc (b - 1) ((b - 1) + 1) := by
        simpa only [hend] using! hx.2
      rw [AddCircle.equivIoc_coe_eq hyDomain',
        AddCircle.equivIoc_coe_eq hxDomain'] at heq
      have hyEq : y = x := congrArg Subtype.val heq
      simpa only [hyEq] using! hy
    · intro hx
      constructor
      · exact ⟨x, hx, rfl⟩
      · exact ⟨by linarith [hwidth, hx.1], hx.2.le⟩
  have hpresApply :
      (volume : Measure UnitAddCircle)
          (unitAddCircleHalfOpenArc a b) =
        (volume : Measure ℝ)
          (q ⁻¹' unitAddCircleHalfOpenArc a b ∩ Ioc (b - 1) b) := by
    have hstandard :=
      AddCircle.add_projection_respects_measure
        (T := (1 : ℝ)) (b - 1) hmeas
    have hvolumeHaar :
        (@volume UnitAddCircle (AddCircle.measureSpace (1 : ℝ))) =
          AddCircle.haarAddCircle := by
      simpa using!
        (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
    rw [hvolumeHaar] at hstandard
    simpa only [q, sub_add_cancel,
      unitAddCircleMeasureSpaceBoundaryCells] using! hstandard
  rw [measureReal_def, hpresApply,
    hpre, Real.volume_Ico,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]

/-- Every genuine grid arc has Haar mass equal to its Euclidean grid
width, including the one-cell grid whose arc is the whole quotient
circle. -/
theorem volume_real_unitAddCircle_intervalGridArc_eq_width
    {grid : ℕ} (hgrid : 0 < grid)
    (i : IntervalGridIndex grid) (hi : i.1 < grid) :
    (volume : Measure UnitAddCircle).real
        (unitAddCircleHalfOpenArc
          (intervalGridPoint 0 1 grid i.1)
          (intervalGridPoint 0 1 grid (i.1 + 1))) =
      intervalGridPoint 0 1 grid (i.1 + 1) -
        intervalGridPoint 0 1 grid i.1 := by
  by_cases hgridOne : grid = 1
  · subst grid
    have hiZero : i.1 = 0 := by omega
    have harc :
        unitAddCircleHalfOpenArc
            (intervalGridPoint 0 1 1 i.1)
            (intervalGridPoint 0 1 1 (i.1 + 1)) =
          (Set.univ : Set UnitAddCircle) := by
      rw [hiZero]
      simpa [intervalGridPoint, unitAddCircleHalfOpenArc] using!
        (AddCircle.coe_image_Ico_eq (p := (1 : ℝ)) (a := (0 : ℝ)))
    rw [harc, probReal_univ]
    simp [intervalGridPoint, hiZero]
  · have hgridTwo : 2 ≤ grid := by omega
    have hgridTwoReal : (2 : ℝ) ≤ (grid : ℝ) := by
      exact_mod_cast hgridTwo
    have hstep :=
      intervalGridPoint_strictMono_step
        (a := (0 : ℝ)) (b := 1) zero_lt_one hgrid
        (k := i.1)
    have hgridReal : (0 : ℝ) < (grid : ℝ) := by exact_mod_cast hgrid
    have hwidth :
        intervalGridPoint 0 1 grid (i.1 + 1) <
          intervalGridPoint 0 1 grid i.1 + 1 := by
      unfold intervalGridPoint
      norm_num
      rw [div_lt_iff₀ hgridReal, add_mul,
        div_mul_cancel₀ _ hgridReal.ne', one_mul]
      nlinarith [hgridTwoReal]
    exact volume_real_unitAddCircleHalfOpenArc_eq_sub_of_lt_one
      hstep hwidth

/-- The normalized product-Haar mass of the flattened torus box is the
product of its literal coordinate widths.  The nonterminal hypothesis is
only needed for coordinates which actually occur in the mixed factorial
tuple. -/
theorem
    unitTorusHaarProbabilityMeasure_real_flattenedAnnularTorusBox_eq_width_prod
    {grid : ℕ} (hgrid : 0 < grid)
    {k : AnnularGridIndex grid → ℕ}
    (htorus : ∀ i : AnnularGridIndex grid,
      0 < k i → i.torus.1 < grid)
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k) :
    (unitTorusHaarProbabilityMeasure
        (r := MixedOccurrenceCount k) :
      Measure (UnitAddTorus (Fin (MixedOccurrenceCount k)))).real
        (unitTorusHalfOpenBox
          (flattenedAnnularTorusLower e)
          (flattenedAnnularTorusUpper e)) =
      ∏ z : GaussPrefixMixedOccurrence k,
        (intervalGridPoint 0 1 grid (z.1.torus.1 + 1) -
          intervalGridPoint 0 1 grid z.1.torus.1) := by
  have hbox :
      unitTorusHalfOpenBox
          (flattenedAnnularTorusLower e)
          (flattenedAnnularTorusUpper e) =
        Set.pi Set.univ
          (fun j : Fin (MixedOccurrenceCount k) ↦
            unitAddCircleHalfOpenArc
              (flattenedAnnularTorusLower e j)
              (flattenedAnnularTorusUpper e j)) := by
    ext z
    simp [unitTorusHalfOpenBox]
  rw [hbox, measureReal_def]
  change
    (volume
      (Set.pi Set.univ
        (fun j : Fin (MixedOccurrenceCount k) ↦
          unitAddCircleHalfOpenArc
            (flattenedAnnularTorusLower e j)
            (flattenedAnnularTorusUpper e j)))).toReal =
      _
  rw [volume_pi_pi, ENNReal.toReal_prod]
  calc
    (∏ j : Fin (MixedOccurrenceCount k),
        (volume
          (unitAddCircleHalfOpenArc
            (flattenedAnnularTorusLower e j)
            (flattenedAnnularTorusUpper e j))).toReal) =
        ∏ j : Fin (MixedOccurrenceCount k),
          (intervalGridPoint 0 1 grid ((e j).1.torus.1 + 1) -
            intervalGridPoint 0 1 grid (e j).1.torus.1) := by
      apply Finset.prod_congr rfl
      intro j _hj
      have hactive : 0 < k (e j).1 := by
        have hj := (e j).2.isLt
        omega
      simpa only [measureReal_def, flattenedAnnularTorusLower,
        flattenedAnnularTorusUpper] using!
        (volume_real_unitAddCircle_intervalGridArc_eq_width
          hgrid (e j).1.torus (htorus (e j).1 hactive))
    _ = ∏ z : GaussPrefixMixedOccurrence k,
        (intervalGridPoint 0 1 grid (z.1.torus.1 + 1) -
          intervalGridPoint 0 1 grid z.1.torus.1) := by
      exact e.prod_comp (fun z : GaussPrefixMixedOccurrence k ↦
        intervalGridPoint 0 1 grid (z.1.torus.1 + 1) -
          intervalGridPoint 0 1 grid z.1.torus.1)

/-- Evaluation of a nonnegative scalar multiple of product Haar measure,
stated at the level of real-valued set masses. -/
theorem scaledUnitTorusHaarFiniteMeasure_real_apply
    {r : ℕ} (mass : ℝ) (hmass : 0 ≤ mass)
    (S : Set (UnitAddTorus (Fin r))) :
    (scaledUnitTorusHaarFiniteMeasure (r := r) mass :
      Measure (UnitAddTorus (Fin r))).real S =
      mass *
        (unitTorusHaarProbabilityMeasure (r := r) :
          Measure (UnitAddTorus (Fin r))).real S := by
  unfold scaledUnitTorusHaarFiniteMeasure
  rw [FiniteMeasure.toMeasure_smul,
    measureReal_nnreal_smul_apply]
  simp only [Real.coe_toNNReal _ hmass]
  rfl

/-- Exact target mass of the flattened annular torus box: after inserting
the canonical time and signed densities, scaled Haar gives the product of
the independent Poisson cell rates, with each rate repeated according to
its factorial multiplicity. -/
theorem
    scaledUnitTorusHaarFiniteMeasure_real_flattenedAnnularTorusBox_eq_prod_poissonRate
    {ε A : ℝ} (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (htime : ∀ i : AnnularGridIndex grid,
      0 < k i → i.time.1 < grid)
    (hsigned : ∀ i : AnnularGridIndex grid,
      0 < k i → i.signed.1 < grid)
    (htorus : ∀ i : AnnularGridIndex grid,
      0 < k i → i.torus.1 < grid)
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k) :
    (scaledUnitTorusHaarFiniteMeasure
        (r := MixedOccurrenceCount k)
        (annularOccurrenceTimeDensity k *
          annularOccurrenceSignedDensity ε A k) :
      Measure (UnitAddTorus (Fin (MixedOccurrenceCount k)))).real
        (unitTorusHalfOpenBox
          (flattenedAnnularTorusLower e)
          (flattenedAnnularTorusUpper e)) =
      ∏ i,
        (annularGridCellPoissonRate ε A grid i : ℝ) ^ k i := by
  have htimeDensity :
      0 < annularOccurrenceTimeDensity k := by
    unfold annularOccurrenceTimeDensity
    apply Finset.prod_pos
    intro z _hz
    exact div_pos
      (sub_pos.mpr
        (intervalGridPoint_strictMono_step
          (a := (0 : ℝ)) (b := 1) (k := z.1.time.1)
          zero_lt_one hgrid))
      (mul_pos (by norm_num) gaussRoofMean_pos)
  have hsignedDensity :
      0 < annularOccurrenceSignedDensity ε A k := by
    unfold annularOccurrenceSignedDensity
    apply Finset.prod_pos
    intro z _hz
    exact div_pos
      (sub_pos.mpr
        (intervalGridPoint_strictMono_step
          (a := signedGridLower ε A z.1.sign)
          (b := signedGridUpper ε A z.1.sign)
          (k := z.1.signed.1)
          (signedGridLower_lt_upper hεA z.1.sign) hgrid))
      (Real.log_pos (by norm_num))
  rw [scaledUnitTorusHaarFiniteMeasure_real_apply
    _ (mul_nonneg htimeDensity.le hsignedDensity.le)]
  rw [
    unitTorusHaarProbabilityMeasure_real_flattenedAnnularTorusBox_eq_width_prod
      hgrid htorus e]
  exact annularOccurrence_fullWidthDensity_eq_prod_poissonRate
    hεA hgrid k htime hsigned htorus

/-! ## Literal denominator time versus deterministic depth boxes -/

/-- The actual logarithmic denominator coordinate of a selected prefix. -/
def gaussPrefixLogDenominatorTime (N n : ℕ) (x : ℝ) : ℝ :=
  Real.log (gaussPrefixDenominator n x : ℝ) / Real.log (N : ℝ)

/-- On the global denominator good event, a contracted deterministic depth
window is contained in the literal half-open logarithmic-time window. -/
theorem gaussPrefixLogDenominatorTime_mem_Ico_of_mem_contractedDepth
    {N L C n : ℕ} {Delta eta a b x : ℝ}
    (hlog : 0 < Real.log (N : ℝ))
    (hxGood : x ∈ gaussDenominatorLinearGoodEvent C L Delta)
    (hnBound : n ≤ C * L)
    (hmargin :
      Delta * (L : ℝ) ≤ eta * Real.log (N : ℝ))
    (hnLower :
      gaussLogDepthEndpoint N (a + eta) ≤ n)
    (hnUpper :
      n < gaussLogDepthEndpoint N (b - eta)) :
    gaussPrefixLogDenominatorTime N n x ∈ Ico a b := by
  have hgood := hxGood n hnBound
  change
    |Real.log (gaussPrefixDenominator n x : ℝ) -
        (n : ℝ) * gaussRoofMean| ≤ Delta * (L : ℝ) at hgood
  have hgoodBounds := (abs_le.mp hgood)
  have hlowerDepth :
      (a + eta) * Real.log (N : ℝ) ≤
        (n : ℝ) * gaussRoofMean := by
    have hceil :
        (a + eta) * Real.log (N : ℝ) / gaussRoofMean ≤ (n : ℝ) := by
      exact Nat.ceil_le.mp hnLower
    exact (div_le_iff₀ gaussRoofMean_pos).mp hceil
  have hupperDepth :
      (n : ℝ) * gaussRoofMean <
        (b - eta) * Real.log (N : ℝ) := by
    have hceil :
        (n : ℝ) <
          (b - eta) * Real.log (N : ℝ) / gaussRoofMean := by
      exact Nat.lt_ceil.mp hnUpper
    exact (lt_div_iff₀ gaussRoofMean_pos).mp hceil
  have hlowerLog :
      a * Real.log (N : ℝ) ≤
        Real.log (gaussPrefixDenominator n x : ℝ) := by
    nlinarith
  have hupperLog :
      Real.log (gaussPrefixDenominator n x : ℝ) <
        b * Real.log (N : ℝ) := by
    nlinarith
  exact ⟨(le_div_iff₀ hlog).2 hlowerLog,
    (div_lt_iff₀ hlog).2 hupperLog⟩

/-- Conversely, a literal half-open logarithmic-time membership lies in the
expanded deterministic depth window. -/
theorem mem_expandedDepth_of_gaussPrefixLogDenominatorTime_mem_Ico
    {N L C n : ℕ} {Delta eta a b x : ℝ}
    (hlog : 0 < Real.log (N : ℝ))
    (hxGood : x ∈ gaussDenominatorLinearGoodEvent C L Delta)
    (hnBound : n ≤ C * L)
    (hmargin :
      Delta * (L : ℝ) ≤ eta * Real.log (N : ℝ))
    (htime : gaussPrefixLogDenominatorTime N n x ∈ Ico a b) :
    n ∈ Finset.Ico
      (gaussLogDepthEndpoint N (a - eta))
      (gaussLogDepthEndpoint N (b + eta)) := by
  have hgood := hxGood n hnBound
  change
    |Real.log (gaussPrefixDenominator n x : ℝ) -
        (n : ℝ) * gaussRoofMean| ≤ Delta * (L : ℝ) at hgood
  have hgoodBounds := abs_le.mp hgood
  have hlowerLog :
      a * Real.log (N : ℝ) ≤
        Real.log (gaussPrefixDenominator n x : ℝ) :=
    (le_div_iff₀ hlog).mp htime.1
  have hupperLog :
      Real.log (gaussPrefixDenominator n x : ℝ) <
        b * Real.log (N : ℝ) :=
    (div_lt_iff₀ hlog).mp htime.2
  have hlowerDepth :
      (a - eta) * Real.log (N : ℝ) ≤
        (n : ℝ) * gaussRoofMean := by
    nlinarith
  have hupperDepth :
      (n : ℝ) * gaussRoofMean <
        (b + eta) * Real.log (N : ℝ) := by
    nlinarith
  rw [Finset.mem_Ico]
  constructor
  · exact Nat.ceil_le.mpr
      ((div_le_iff₀ gaussRoofMean_pos).2 hlowerDepth)
  · exact Nat.lt_ceil.mpr
      ((lt_div_iff₀ gaussRoofMean_pos).2 hupperDepth)

/-- A depth strictly below the contracted right endpoint at time one has
literal terminal denominator strictly smaller than `N`.  This is the
pointwise bridge needed before a selected prefix word may be used as a
bounded terminal cylinder; no asymptotic or almost-everywhere statement is
hidden in it. -/
theorem gaussPrefixDenominator_lt_of_depth_lt_contracted_one
    {N L C n : ℕ} {Delta eta x : ℝ}
    (hlog : 0 < Real.log (N : ℝ))
    (hxGood : x ∈ gaussDenominatorLinearGoodEvent C L Delta)
    (hnBound : n ≤ C * L)
    (hmargin :
      Delta * (L : ℝ) ≤ eta * Real.log (N : ℝ))
    (hnUpper :
      n < gaussLogDepthEndpoint N (1 - eta)) :
    gaussPrefixDenominator n x < N := by
  have hdepth :
      (n : ℝ) * gaussRoofMean <
        (1 - eta) * Real.log (N : ℝ) := by
    have hceil :
        (n : ℝ) <
          (1 - eta) * Real.log (N : ℝ) / gaussRoofMean :=
      Nat.lt_ceil.mp hnUpper
    exact (lt_div_iff₀ gaussRoofMean_pos).mp hceil
  have hdenUpper :
      (gaussPrefixDenominator n x : ℝ) ≤
        Real.exp
          ((n : ℝ) * gaussRoofMean + Delta * (L : ℝ)) := by
    simpa only [gaussPrefixDenominator] using!
      (gaussPrefixDenominator_exp_bounds_of_mem_linearGoodEvent
        hxGood hnBound).2
  have hexponent :
      (n : ℝ) * gaussRoofMean + Delta * (L : ℝ) <
        Real.log (N : ℝ) := by
    nlinarith
  have hNreal : (0 : ℝ) < (N : ℝ) := by
    have hone : (1 : ℝ) < (N : ℝ) :=
      (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ (N : ℝ))).mp hlog
    linarith
  have hcast :
      (gaussPrefixDenominator n x : ℝ) < (N : ℝ) := by
    calc
      (gaussPrefixDenominator n x : ℝ) ≤
          Real.exp
            ((n : ℝ) * gaussRoofMean + Delta * (L : ℝ)) :=
        hdenUpper
      _ < Real.exp (Real.log (N : ℝ)) :=
        Real.exp_lt_exp.mpr hexponent
      _ = (N : ℝ) := Real.exp_log hNreal
  exact_mod_cast hcast

/-- Cell-specialized contracted-to-literal implication.  In particular it
applies to the first time interval `i.time = 0`; no positive-time
assumption appears. -/
theorem gaussPrefixLogDenominatorTime_mem_timeCell_of_contractedDepth
    {N L C n grid : ℕ} {Delta eta x : ℝ}
    (i : AnnularGridIndex grid)
    (htime : i.time.1 < grid)
    (hlog : 0 < Real.log (N : ℝ))
    (hxGood : x ∈ gaussDenominatorLinearGoodEvent C L Delta)
    (hnBound : n ≤ C * L)
    (hmargin :
      Delta * (L : ℝ) ≤ eta * Real.log (N : ℝ))
    (hnLower :
      gaussLogDepthEndpoint N
          (intervalGridPoint 0 1 grid i.time.1 + eta) ≤ n)
    (hnUpper :
      n < gaussLogDepthEndpoint N
          (intervalGridPoint 0 1 grid (i.time.1 + 1) - eta)) :
    gaussPrefixLogDenominatorTime N n x ∈
      intervalGridCell 0 1 grid i.time := by
  unfold intervalGridCell
  rw [if_pos htime]
  exact gaussPrefixLogDenominatorTime_mem_Ico_of_mem_contractedDepth
    hlog hxGood hnBound hmargin hnLower hnUpper

/-- Cell-specialized literal-to-expanded implication, retaining both
half-open endpoints exactly. -/
theorem mem_expandedDepth_of_gaussPrefixLogDenominatorTime_mem_timeCell
    {N L C n grid : ℕ} {Delta eta x : ℝ}
    (i : AnnularGridIndex grid)
    (htime : i.time.1 < grid)
    (hlog : 0 < Real.log (N : ℝ))
    (hxGood : x ∈ gaussDenominatorLinearGoodEvent C L Delta)
    (hnBound : n ≤ C * L)
    (hmargin :
      Delta * (L : ℝ) ≤ eta * Real.log (N : ℝ))
    (hcell :
      gaussPrefixLogDenominatorTime N n x ∈
        intervalGridCell 0 1 grid i.time) :
    n ∈ Finset.Ico
      (gaussLogDepthEndpoint N
        (intervalGridPoint 0 1 grid i.time.1 - eta))
      (gaussLogDepthEndpoint N
        (intervalGridPoint 0 1 grid (i.time.1 + 1) + eta)) := by
  unfold intervalGridCell at hcell
  rw [if_pos htime] at hcell
  exact mem_expandedDepth_of_gaussPrefixLogDenominatorTime_mem_Ico
    hlog hxGood hnBound hmargin hcell

/-! ## Simultaneous fixed-order denominator-time replacement -/

/-- The contracted deterministic depth box attached to one nonterminal
time cell. -/
def contractedAnnularTimeDepthBox
    (N : ℕ) (eta : ℝ) {grid : ℕ}
    (i : AnnularGridIndex grid) : Finset ℕ :=
  Finset.Ico
    (gaussLogDepthEndpoint N
      (intervalGridPoint 0 1 grid i.time.1 + eta))
    (gaussLogDepthEndpoint N
      (intervalGridPoint 0 1 grid (i.time.1 + 1) - eta))

/-- The expanded deterministic depth box attached to one nonterminal time
cell. -/
def expandedAnnularTimeDepthBox
    (N : ℕ) (eta : ℝ) {grid : ℕ}
    (i : AnnularGridIndex grid) : Finset ℕ :=
  Finset.Ico
    (gaussLogDepthEndpoint N
      (intervalGridPoint 0 1 grid i.time.1 - eta))
    (gaussLogDepthEndpoint N
      (intervalGridPoint 0 1 grid (i.time.1 + 1) + eta))

/-- At every coordinate of a fixed mixed order, membership in the
contracted deterministic boxes implies membership of the literal
logarithmic denominators in the corresponding time cells.  The statement
is simultaneous over the finite occurrence type, so there is no
coordinate-dependent exceptional set or implicit loss with the order. -/
theorem forall_gaussPrefixLogDenominatorTime_mem_timeCell_of_contractedBoxes
    {N L C grid : ℕ} {Delta eta x : ℝ}
    {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (t : Fin (MixedOccurrenceCount k) → ℕ)
    (htime :
      ∀ i : AnnularGridIndex grid, 0 < k i → i.time.1 < grid)
    (hlog : 0 < Real.log (N : ℝ))
    (hxGood : x ∈ gaussDenominatorLinearGoodEvent C L Delta)
    (hbound : ∀ j, t j ≤ C * L)
    (hmargin :
      Delta * (L : ℝ) ≤ eta * Real.log (N : ℝ))
    (hboxes :
      ∀ j, t j ∈ contractedAnnularTimeDepthBox N eta (e j).1) :
    ∀ j,
      gaussPrefixLogDenominatorTime N (t j) x ∈
        intervalGridCell 0 1 grid (e j).1.time := by
  intro j
  have hactive : 0 < k (e j).1 := by
    have hj := (e j).2.isLt
    omega
  have hjbox := Finset.mem_Ico.mp (hboxes j)
  exact
    gaussPrefixLogDenominatorTime_mem_timeCell_of_contractedDepth
      (e j).1 (htime (e j).1 hactive) hlog hxGood
      (hbound j) hmargin hjbox.1 hjbox.2

/-- Conversely, simultaneous literal time-cell membership at a fixed
mixed order places every depth in the corresponding expanded deterministic
box. -/
theorem forall_mem_expandedBoxes_of_gaussPrefixLogDenominatorTime_mem_timeCell
    {N L C grid : ℕ} {Delta eta x : ℝ}
    {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (t : Fin (MixedOccurrenceCount k) → ℕ)
    (htime :
      ∀ i : AnnularGridIndex grid, 0 < k i → i.time.1 < grid)
    (hlog : 0 < Real.log (N : ℝ))
    (hxGood : x ∈ gaussDenominatorLinearGoodEvent C L Delta)
    (hbound : ∀ j, t j ≤ C * L)
    (hmargin :
      Delta * (L : ℝ) ≤ eta * Real.log (N : ℝ))
    (hcells :
      ∀ j,
        gaussPrefixLogDenominatorTime N (t j) x ∈
          intervalGridCell 0 1 grid (e j).1.time) :
    ∀ j, t j ∈ expandedAnnularTimeDepthBox N eta (e j).1 := by
  intro j
  have hactive : 0 < k (e j).1 := by
    have hj := (e j).2.isLt
    omega
  exact
    mem_expandedDepth_of_gaussPrefixLogDenominatorTime_mem_timeCell
      (e j).1 (htime (e j).1 hactive) hlog hxGood
      (hbound j) hmargin (hcells j)

end

end Erdos1002
