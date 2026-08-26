import ErdosProblems.Erdos1002.GaussPrefixMarkedMixedFourier
import ErdosProblems.Erdos1002.GaussPrefixFutureMixing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact decomposition over a deepest Gauss-prefix cylinder

The oscillatory-cylinder argument in the marked Poisson proof uses two
facts which must not be hidden in the phrase "sum over the deepest
cylinders".

* A positive word of a deeper level has a canonical positive prefix at
  every earlier level, and every point of its half-open cylinder selects
  precisely that prefix.
* If one component of a literal mixed tuple has positive depth, then the
  tuple character is supported on a *finite*, pairwise-disjoint family of
  denominator-bounded cylinders of exactly that depth.  Consequently its
  Lebesgue integral is exactly the sum of the corresponding set integrals.

The first fact also makes the signed terminal-denominator carrier constant
on a fixed deepest cylinder whenever all tuple depths are no larger than
the cylinder depth.  These statements supply the literal bridge from the
chronological mixed tuple to the deterministic cylinder-sum layer.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

local instance gaussPrefixDeepestCylinderPropDecidable (P : Prop) :
    Decidable P := Classical.propDecidable P

/-! ## Canonical truncation of a positive word -/

/-- The first `n` digits of a positive word of length `m`, packaged as a
positive word of length `n`. -/
def positiveDigitWordTake {m : ℕ} (n : ℕ) (hnm : n ≤ m)
    (w : PositiveDigitWord m) : PositiveDigitWord n :=
  ⟨w.1.take n, by simp [w.2.1, Nat.min_eq_left hnm], by
    intro q hq
    exact w.2.2 q (List.mem_of_mem_take hq)⟩

@[simp] theorem positiveDigitWordTake_val {m : ℕ} (n : ℕ)
    (hnm : n ≤ m) (w : PositiveDigitWord m) :
    (positiveDigitWordTake n hnm w).1 = w.1.take n := rfl

/-- Membership in a deeper half-open cylinder implies membership in its
canonical shallower cylinder.  The half-open endpoint convention is kept
throughout; no almost-everywhere replacement is used here. -/
theorem mem_positivePrefixCylinder_positiveDigitWordTake
    {n m : ℕ} (hnm : n ≤ m) (w : PositiveDigitWord m)
    {x : ℝ} (hxUnit : x ∈ Ico (0 : ℝ) 1)
    (hx : x ∈ positivePrefixCylinder m w) :
    x ∈ positivePrefixCylinder n (positiveDigitWordTake n hnm w) := by
  have hword : w.1.take n ++ w.1.drop n = w.1 :=
    List.take_append_drop n w.1
  have hsplit :=
    (mem_gaussHalfOpenPrefixCylinder_append_iff
      (w.1.take n) (w.1.drop n) hxUnit).1
  change x ∈ gaussHalfOpenPrefixCylinder (w.1.take n)
  exact (hsplit (by simpa only [hword] using! hx)).1

/-- On a deeper cylinder the word selected at every shallower depth is the
canonical truncation of the deeper word. -/
theorem selectedGaussPrefixWord_eq_positiveDigitWordTake
    {n m : ℕ} (hnm : n ≤ m) (w : PositiveDigitWord m)
    {x : ℝ} (hxUnit : x ∈ Ico (0 : ℝ) 1)
    (hx : x ∈ positivePrefixCylinder m w) :
    selectedGaussPrefixWord n x = positiveDigitWordTake n hnm w := by
  apply selectedGaussPrefixWord_eq_of_mem
  exact mem_positivePrefixCylinder_positiveDigitWordTake hnm w hxUnit hx

/-- Two points in one deeper cylinder select identical words at every
shallower depth. -/
theorem selectedGaussPrefixWord_eq_on_deeperCylinder
    {n m : ℕ} (hnm : n ≤ m) (w : PositiveDigitWord m)
    {x y : ℝ} (hxUnit : x ∈ Ico (0 : ℝ) 1)
    (hyUnit : y ∈ Ico (0 : ℝ) 1)
    (hx : x ∈ positivePrefixCylinder m w)
    (hy : y ∈ positivePrefixCylinder m w) :
    selectedGaussPrefixWord n x = selectedGaussPrefixWord n y := by
  rw [selectedGaussPrefixWord_eq_positiveDigitWordTake hnm w hxUnit hx,
    selectedGaussPrefixWord_eq_positiveDigitWordTake hnm w hyUnit hy]

/-- Appending one positive continued-fraction digit cannot decrease the
terminal denominator. -/
theorem cfTerminalDenominator_le_append_singleton
    (w : List ℕ) {q : ℕ} (hq : 0 < q) :
    cfTerminalDenominator w ≤ cfTerminalDenominator (w ++ [q]) := by
  rw [← gaussPrefixMobius_D_eq_terminalDenominator,
    ← gaussPrefixMobius_D_eq_terminalDenominator,
    gaussPrefixMobius_append_singleton]
  dsimp only
  have hmul : (gaussPrefixMobius w).D ≤
      q * (gaussPrefixMobius w).D :=
    Nat.le_mul_of_pos_left _ hq
  omega

/-- Appending an arbitrary positive suffix cannot decrease the terminal
denominator. -/
theorem cfTerminalDenominator_le_append
    (u : List ℕ) {v : List ℕ} (hv : IsPositiveCFWord v) :
    cfTerminalDenominator u ≤ cfTerminalDenominator (u ++ v) := by
  induction v using List.reverseRecOn with
  | nil => simp
  | append_singleton v q ih =>
      have hvpos : IsPositiveCFWord v := by
        intro a ha
        exact hv a (by simp [ha])
      have hq : 0 < q := hv q (by simp)
      calc
        cfTerminalDenominator u ≤ cfTerminalDenominator (u ++ v) :=
          ih hvpos
        _ ≤ cfTerminalDenominator ((u ++ v) ++ [q]) :=
          cfTerminalDenominator_le_append_singleton (u ++ v) hq
        _ = cfTerminalDenominator (u ++ (v ++ [q])) := by
          rw [List.append_assoc]

/-- In particular, the denominator of a canonical truncated word is at
most the denominator of the deepest word. -/
theorem cfTerminalDenominator_take_le
    {m : ℕ} (n : ℕ) (hnm : n ≤ m) (w : PositiveDigitWord m) :
    cfTerminalDenominator (positiveDigitWordTake n hnm w).1 ≤
      cfTerminalDenominator w.1 := by
  have hdrop : IsPositiveCFWord (w.1.drop n) := by
    intro q hq
    exact w.2.2 q (List.mem_of_mem_drop hq)
  have hle := cfTerminalDenominator_le_append (w.1.take n) hdrop
  simpa only [positiveDigitWordTake_val, List.take_append_drop] using! hle

/-! ## Quantitative growth under a separated suffix -/

/-- Two appended positive continued-fraction digits at least double the
terminal denominator.  This is the elementary deterministic separation
input behind the non-cancellation of a latest Fourier carrier. -/
theorem two_mul_cfTerminalDenominator_le_append_two
    (u : List ℕ) {q r : ℕ} (hq : 0 < q) (hr : 0 < r) :
    2 * cfTerminalDenominator u ≤
      cfTerminalDenominator (u ++ [q, r]) := by
  have hfirst : cfTerminalDenominator u ≤
      cfTerminalDenominator (u ++ [q]) :=
    cfTerminalDenominator_le_append_singleton u hq
  have hformula :
      cfTerminalDenominator (u ++ [q, r]) =
        cfTerminalDenominator u +
          r * cfTerminalDenominator (u ++ [q]) := by
    rw [show u ++ [q, r] = (u ++ [q]) ++ [r] by simp]
    rw [← gaussPrefixMobius_D_eq_terminalDenominator,
      gaussPrefixMobius_append_singleton]
    dsimp only
    rw [show (gaussPrefixMobius (u ++ [q])).C =
        (gaussPrefixMobius u).D by
      rw [gaussPrefixMobius_append_singleton]]
    rw [gaussPrefixMobius_D_eq_terminalDenominator,
      gaussPrefixMobius_D_eq_terminalDenominator]
  rw [hformula]
  have hmul : cfTerminalDenominator (u ++ [q]) ≤
      r * cfTerminalDenominator (u ++ [q]) :=
    Nat.le_mul_of_pos_left _ hr
  omega

/-- A positive suffix of length `d` increases the terminal denominator by
at least `2 ^ (d / 2)`.  Stating the estimate for an arbitrary initial word
makes it directly applicable to canonical earlier prefixes of one deepest
cylinder. -/
theorem pow_two_div_two_mul_cfTerminalDenominator_le_append
    (u : List ℕ) {v : List ℕ} (hv : IsPositiveCFWord v) :
    2 ^ (v.length / 2) * cfTerminalDenominator u ≤
      cfTerminalDenominator (u ++ v) := by
  induction v using List.twoStepInduction generalizing u with
  | nil => simp
  | singleton q =>
      have hq : 0 < q := hv q (by simp)
      simpa using! cfTerminalDenominator_le_append_singleton u hq
  | cons_cons q r v ih _ihOne =>
      have hq : 0 < q := hv q (by simp)
      have hr : 0 < r := hv r (by simp)
      have hvTail : IsPositiveCFWord v := by
        intro a ha
        exact hv a (by simp [ha])
      have hpair : 2 * cfTerminalDenominator u ≤
          cfTerminalDenominator (u ++ [q, r]) :=
        two_mul_cfTerminalDenominator_le_append_two u hq hr
      have htail := ih (u := u ++ [q, r]) hvTail
      have hpow :
          2 ^ ((q :: r :: v).length / 2) =
            2 ^ (v.length / 2) * 2 := by
        simp only [List.length_cons]
        rw [show (v.length + 1 + 1) / 2 = v.length / 2 + 1 by omega,
          pow_succ]
      rw [hpow]
      calc
        2 ^ (v.length / 2) * 2 * cfTerminalDenominator u =
            2 ^ (v.length / 2) *
              (2 * cfTerminalDenominator u) := by ring
        _ ≤ 2 ^ (v.length / 2) *
              cfTerminalDenominator (u ++ [q, r]) :=
          Nat.mul_le_mul_left _ hpair
        _ ≤ cfTerminalDenominator ((u ++ [q, r]) ++ v) := htail
        _ = cfTerminalDenominator (u ++ (q :: r :: v)) := by
          congr 1
          simp

/-- Quantitative form for two canonical prefixes of one positive word.
The exponent is half of the depth gap, rounded down. -/
theorem pow_two_depthGap_mul_cfTerminalDenominator_take_le
    {m : ℕ} (n : ℕ) (hnm : n ≤ m) (w : PositiveDigitWord m) :
    2 ^ ((m - n) / 2) *
        cfTerminalDenominator (positiveDigitWordTake n hnm w).1 ≤
      cfTerminalDenominator w.1 := by
  have hdrop : IsPositiveCFWord (w.1.drop n) := by
    intro q hq
    exact w.2.2 q (List.mem_of_mem_drop hq)
  have hgrowth :=
    pow_two_div_two_mul_cfTerminalDenominator_le_append
      (w.1.take n) hdrop
  have hlength : (w.1.drop n).length = m - n := by
    rw [List.length_drop, w.2.1]
  simpa only [positiveDigitWordTake_val, hlength,
    List.take_append_drop] using! hgrowth

/-! ## Constancy of the mixed carrier -/

variable {ι : Type*} [Fintype ι]

/-- If every selected time is no later than `m`, the complete signed
terminal-denominator carrier is constant on each depth-`m` cylinder. -/
theorem gaussPrefixMarkedMixedCarrier_eq_on_deeperCylinder
    (N : ℕ) (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k) {m : ℕ}
    (hF : ∀ i j, F i j ≤ m) (w : PositiveDigitWord m)
    {x y : ℝ} (hxUnit : x ∈ Ico (0 : ℝ) 1)
    (hyUnit : y ∈ Ico (0 : ℝ) 1)
    (hx : x ∈ positivePrefixCylinder m w)
    (hy : y ∈ positivePrefixCylinder m w) :
    gaussPrefixMarkedMixedCarrier N k h F x =
      gaussPrefixMarkedMixedCarrier N k h F y := by
  classical
  unfold gaussPrefixMarkedMixedCarrier
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  have hselected : selectedGaussPrefixWord (F i j) x =
      selectedGaussPrefixWord (F i j) y :=
    selectedGaussPrefixWord_eq_on_deeperCylinder
      (hF i j) w hxUnit hyUnit hx hy
  rw [hselected]

/-! ## Explicit affine signed-value coordinates on a cylinder -/

/-- Slope of the signed marked-value coordinate on the cylinder `w`. -/
def gaussPrefixMarkedValueSlope
    (N : ℕ) {n : ℕ} (w : PositiveDigitWord n) : ℝ :=
  Real.log (N : ℝ) * (cfTerminalDenominator w.1 : ℝ) ^ 2

/-- Intercept of the signed marked-value coordinate on the cylinder `w`. -/
def gaussPrefixMarkedValueIntercept
    (N : ℕ) {n : ℕ} (w : PositiveDigitWord n) : ℝ :=
  -(Real.log (N : ℝ) * (cfTerminalDenominator w.1 : ℝ) *
      (cfTerminalNumerator w.1 : ℝ))

/-- The signed value coordinate is literally affine on a fixed positive
prefix cylinder.  This is the determinant identity written in the exact
form consumed by the interval-intersection lemma. -/
theorem gaussPrefixMarkedPoint_value_eq_affine
    {N n : ℕ} (w : PositiveDigitWord n) {x : ℝ}
    (hxUnit : x ∈ Ioo (0 : ℝ) 1)
    (hxNonterm : ∀ r : ℕ, (gaussMap^[r]) x ≠ 0)
    (hx : x ∈ positivePrefixCylinder n w) :
    (gaussPrefixMarkedPoint N n w x).2.1 =
      gaussPrefixMarkedValueSlope N w * x +
        gaussPrefixMarkedValueIntercept N w := by
  have hex : x ∉ gaussPrefixExceptional (n + 1) :=
    not_mem_gaussPrefixExceptional_of_nonterminating
      hxUnit hxNonterm (n + 1)
  have herr := terminalDenominator_mul_sub_terminalNumerator_eq
    w.2.2 hxUnit (by simpa [w.2.1] using! hex) hx
  rw [gaussPrefixMobius_D_eq_terminalDenominator,
    gaussPrefixMobius_B_eq_terminalNumerator, w.2.1] at herr
  have hdenPos : (0 : ℝ) < cfTerminalDenominator w.1 := by
    exact_mod_cast cfTerminalDenominator_pos w.2.2
  have hdenNe : (cfTerminalDenominator w.1 : ℝ) ≠ 0 := hdenPos.ne'
  unfold gaussPrefixMarkedPoint
  change (-1 : ℝ) ^ n * Real.log (N : ℝ) *
      gaussApproximationCoordinate n x = _
  calc
    (-1 : ℝ) ^ n * Real.log (N : ℝ) *
        gaussApproximationCoordinate n x =
        Real.log (N : ℝ) * (cfTerminalDenominator w.1 : ℝ) *
          (((-1 : ℝ) ^ n * gaussApproximationCoordinate n x) /
            cfTerminalDenominator w.1) := by
      field_simp [hdenNe]
    _ = Real.log (N : ℝ) * (cfTerminalDenominator w.1 : ℝ) *
          ((cfTerminalDenominator w.1 : ℝ) * x -
            cfTerminalNumerator w.1) := by rw [← herr]
    _ = gaussPrefixMarkedValueSlope N w * x +
          gaussPrefixMarkedValueIntercept N w := by
      unfold gaussPrefixMarkedValueSlope gaussPrefixMarkedValueIntercept
      ring

/-- On a deeper cylinder, the signed value attached to a selected earlier
depth is the affine function determined by the canonical truncated word. -/
theorem selectedGaussPrefixMarkedPoint_value_eq_affine_on_deeperCylinder
    {N n m : ℕ} (hnm : n ≤ m) (w : PositiveDigitWord m)
    {x : ℝ} (hxUnit : x ∈ Ioo (0 : ℝ) 1)
    (hxNonterm : ∀ r : ℕ, (gaussMap^[r]) x ≠ 0)
    (hx : x ∈ positivePrefixCylinder m w) :
    (gaussPrefixMarkedPoint N n (selectedGaussPrefixWord n x) x).2.1 =
      gaussPrefixMarkedValueSlope N (positiveDigitWordTake n hnm w) * x +
        gaussPrefixMarkedValueIntercept N
          (positiveDigitWordTake n hnm w) := by
  have hxIco : x ∈ Ico (0 : ℝ) 1 := ⟨hxUnit.1.le, hxUnit.2⟩
  have hselected := selectedGaussPrefixWord_eq_positiveDigitWordTake
    hnm w hxIco hx
  rw [hselected]
  apply gaussPrefixMarkedPoint_value_eq_affine
    (positiveDigitWordTake n hnm w) hxUnit hxNonterm
  exact mem_positivePrefixCylinder_positiveDigitWordTake hnm w hxIco hx

/-! ## Closed-cylinder endpoints and finite affine window intersections -/

/-- A positive inverse word is continuous on the closed unit tail interval.
The proof records at every composition step that the inner inverse word
still takes values in `[0,1]`. -/
theorem continuousOn_gaussInverseWord_Icc
    {w : List ℕ} (hpos : IsPositiveCFWord w) :
    ContinuousOn (gaussInverseWord w) (Icc (0 : ℝ) 1) := by
  induction w with
  | nil => simpa [gaussInverseWord] using! (continuousOn_id :
      ContinuousOn (fun x : ℝ ↦ x) (Icc (0 : ℝ) 1))
  | cons q w ih =>
      have hq : 0 < q := hpos q (by simp)
      have htail : IsPositiveCFWord w := by
        intro a ha
        exact hpos a (by simp [ha])
      have hcomp := (continuousOn_gaussInverseBranch q hq).comp
        (ih htail) (fun x hx ↦ gaussInverseWord_mem_Icc htail hx)
      simpa only [gaussInverseWord, Function.comp_apply] using! hcomp

/-- Left endpoint of the closed cylinder, defined without choosing its
orientation (which alternates with the word length). -/
def closedGaussPrefixCylinderLeft (w : List ℕ) : ℝ :=
  sInf (closedGaussPrefixCylinder w)

/-- Right endpoint of the closed cylinder. -/
def closedGaussPrefixCylinderRight (w : List ℕ) : ℝ :=
  sSup (closedGaussPrefixCylinder w)

/-- Every positive closed Gauss cylinder is literally one closed interval.
The `sInf`/`sSup` definition automatically handles the parity-dependent
orientation of the inverse word. -/
theorem closedGaussPrefixCylinder_eq_Icc
    {w : List ℕ} (hpos : IsPositiveCFWord w) :
    closedGaussPrefixCylinder w =
      Icc (closedGaussPrefixCylinderLeft w)
        (closedGaussPrefixCylinderRight w) := by
  unfold closedGaussPrefixCylinder closedGaussPrefixCylinderLeft
    closedGaussPrefixCylinderRight
  exact (continuousOn_gaussInverseWord_Icc hpos).image_Icc (by norm_num)

/-- Replacing the recursive half-open prefix cylinder by its closed
inverse-word image adds at most the two terminating endpoint images. -/
theorem closedGaussPrefixCylinder_diff_halfOpen_subset_pair
    {w : List ℕ} (hpos : IsPositiveCFWord w) :
    closedGaussPrefixCylinder w \ gaussHalfOpenPrefixCylinder w ⊆
      {gaussInverseWord w 0, gaussInverseWord w 1} := by
  rintro x ⟨⟨y, hy, rfl⟩, hnotPrefix⟩
  by_cases hylt : y < 1
  · have hyIco : y ∈ Ico (0 : ℝ) 1 := ⟨hy.1, hylt⟩
    have hzero :=
      gaussInverseWord_image_Ico_diff_prefix_subset_singleton hpos
        ⟨⟨y, hyIco, rfl⟩, hnotPrefix⟩
    have heq : gaussInverseWord w y = gaussInverseWord w 0 := by
      simpa only [Set.mem_singleton_iff] using! hzero
    exact Set.mem_insert_iff.mpr (Or.inl heq)
  · have hyone : y = 1 := le_antisymm hy.2 (le_of_not_gt hylt)
    subst y
    exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _))

/-- The endpoint replacement is null for the uniform Lebesgue law. -/
theorem uniform01Measure_closedGaussPrefixCylinder_diff_halfOpen
    {w : List ℕ} (hpos : IsPositiveCFWord w) :
    uniform01Measure
        (closedGaussPrefixCylinder w \ gaussHalfOpenPrefixCylinder w) = 0 := by
  apply MeasureTheory.measure_mono_null
    (closedGaussPrefixCylinder_diff_halfOpen_subset_pair hpos)
  have hpairM : MeasurableSet
      ({gaussInverseWord w 0, gaussInverseWord w 1} : Set ℝ) := by
    measurability
  rw [uniform01Measure, Measure.restrict_apply hpairM]
  apply MeasureTheory.measure_mono_null inter_subset_left
  rw [show ({gaussInverseWord w 0, gaussInverseWord w 1} : Set ℝ) =
      {gaussInverseWord w 0} ∪ {gaussInverseWord w 1} by
        ext x
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
          Set.mem_union]]
  exact MeasureTheory.measure_union_null Real.volume_singleton
    Real.volume_singleton

/-- Intersection of one closed interval with finitely many affine closed
windows, indexed by an arbitrary finite type. -/
def finiteAffineWindowIntersection {α : Type*} [Fintype α]
    (cylinderLeft cylinderRight : ℝ)
    (windowLower windowUpper slope intercept : α → ℝ) : Set ℝ :=
  Icc cylinderLeft cylinderRight ∩
    ⋂ i, (fun x ↦ slope i * x + intercept i) ⁻¹'
      Icc (windowLower i) (windowUpper i)

/-- A finite family of affine closed value constraints cuts a closed real
interval down to either the empty set or one closed interval. -/
theorem finiteAffineWindowIntersection_eq_empty_or_Icc
    {α : Type*} [Fintype α]
    (cylinderLeft cylinderRight : ℝ)
    (windowLower windowUpper slope intercept : α → ℝ) :
    finiteAffineWindowIntersection cylinderLeft cylinderRight
        windowLower windowUpper slope intercept = ∅ ∨
      ∃ left right : ℝ, left ≤ right ∧
        finiteAffineWindowIntersection cylinderLeft cylinderRight
          windowLower windowUpper slope intercept = Icc left right := by
  classical
  let S : Set ℝ := finiteAffineWindowIntersection cylinderLeft cylinderRight
    windowLower windowUpper slope intercept
  by_cases hS : S = ∅
  · exact Or.inl hS
  · have hSne : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hS
    have hpre (i : α) : Set.OrdConnected
        ((fun x : ℝ ↦ slope i * x + intercept i) ⁻¹'
          Icc (windowLower i) (windowUpper i)) := by
      by_cases hslope : 0 ≤ slope i
      · apply Set.ordConnected_Icc.preimage_mono
        intro x y hxy
        simpa [add_comm] using!
          add_le_add_right (mul_le_mul_of_nonneg_left hxy hslope)
            (intercept i)
      · apply Set.ordConnected_Icc.preimage_anti
        intro x y hxy
        have hslope' : slope i ≤ 0 := le_of_not_ge hslope
        simpa [add_comm] using!
          add_le_add_right (mul_le_mul_of_nonpos_left hxy hslope')
            (intercept i)
    have hord : S.OrdConnected := by
      dsimp [S, finiteAffineWindowIntersection]
      exact Set.ordConnected_Icc.inter (Set.ordConnected_iInter hpre)
    have hclosed : IsClosed S := by
      dsimp [S, finiteAffineWindowIntersection]
      apply isClosed_Icc.inter
      apply isClosed_iInter
      intro i
      exact isClosed_Icc.preimage
        ((continuous_const.mul continuous_id).add continuous_const)
    have hsubset : S ⊆ Icc cylinderLeft cylinderRight := by
      intro x hx
      exact hx.1
    have hcompact : IsCompact S :=
      isCompact_Icc.of_isClosed_subset hclosed hsubset
    have hconnected : IsConnected S := ⟨hSne, hord.isPreconnected⟩
    have heq : S = Icc (sInf S) (sSup S) :=
      eq_Icc_of_connected_compact hconnected hcompact
    refine Or.inr ⟨sInf S, sSup S, ?_, heq⟩
    exact Set.nonempty_Icc.mp (heq ▸ hSne)

/-! ## The finite family of denominator-bounded cylinders at one depth -/

/-- Nonempty positive words of exact depth `n` whose terminal denominator
is at most `N`.  Finiteness follows from the already-proved injective
terminal-pair/parity code for `BoundedPositiveTerminalWord`. -/
def ExactDepthBoundedPositiveWord (N n : ℕ) :=
  {w : BoundedPositiveTerminalWord N // w.1.length = n}

noncomputable instance exactDepthBoundedPositiveWordFintype (N n : ℕ) :
    Fintype (ExactDepthBoundedPositiveWord N n) :=
  Fintype.ofInjective
    (fun w : ExactDepthBoundedPositiveWord N n ↦ w.1)
    (fun _w _v hwv ↦ Subtype.ext hwv)

/-- The exact-depth subfamily inherits the same proved quadratic
denominator-code bound as the ambient family of positive words. -/
theorem card_exactDepthBoundedPositiveWord_le (R n : ℕ) :
    Fintype.card (ExactDepthBoundedPositiveWord R n) ≤
      2 * (R + 1) ^ 2 := by
  calc
    Fintype.card (ExactDepthBoundedPositiveWord R n) ≤
        Fintype.card (BoundedPositiveTerminalWord R) :=
      Fintype.card_le_of_injective
        (fun w : ExactDepthBoundedPositiveWord R n ↦ w.1)
        (fun _w _v hwv ↦ Subtype.ext hwv)
    _ ≤ 2 * (R + 1) ^ 2 := card_boundedPositiveTerminalWord_le R

/-- Monotone embedding from a sharper terminal-denominator cutoff `R` into
a larger process cutoff `N`.  The underlying word and hence its cylinder,
all affine coordinates, and all carriers remain literally unchanged. -/
def ExactDepthBoundedPositiveWord.mono
    {R N n : ℕ} (hRN : R ≤ N)
    (w : ExactDepthBoundedPositiveWord R n) :
    ExactDepthBoundedPositiveWord N n :=
  ⟨⟨w.1.1, w.1.2.1, w.1.2.2.1, w.1.2.2.2.trans hRN⟩, w.2⟩

@[simp] theorem ExactDepthBoundedPositiveWord.mono_val
    {R N n : ℕ} (hRN : R ≤ N)
    (w : ExactDepthBoundedPositiveWord R n) :
    (w.mono hRN).1.1 = w.1.1 := rfl

/-- Forget the denominator bound while retaining the exact depth. -/
def ExactDepthBoundedPositiveWord.toPositive
    {N n : ℕ} (w : ExactDepthBoundedPositiveWord N n) :
    PositiveDigitWord n :=
  ⟨w.1.1, w.2, w.1.2.2.1⟩

@[simp] theorem ExactDepthBoundedPositiveWord.mono_toPositive
    {R N n : ℕ} (hRN : R ≤ N)
    (w : ExactDepthBoundedPositiveWord R n) :
    (w.mono hRN).toPositive = w.toPositive := by
  rfl

/-- The actual half-open cylinder belonging to an exact-depth bounded
word. -/
def exactDepthBoundedCylinder {N n : ℕ}
    (w : ExactDepthBoundedPositiveWord N n) : Set ℝ :=
  positivePrefixCylinder n w.toPositive

@[simp] theorem exactDepthBoundedCylinder_mono
    {R N n : ℕ} (hRN : R ≤ N)
    (w : ExactDepthBoundedPositiveWord R n) :
    exactDepthBoundedCylinder (w.mono hRN) =
      exactDepthBoundedCylinder w := rfl

theorem measurableSet_exactDepthBoundedCylinder
    {N n : ℕ} (w : ExactDepthBoundedPositiveWord N n) :
    MeasurableSet (exactDepthBoundedCylinder w) :=
  measurableSet_positivePrefixCylinder n w.toPositive

/-- Under the uniform law, the actual recursive half-open cylinder and its
closed inverse-word interval are the same set almost everywhere. -/
theorem exactDepthBoundedCylinder_ae_eq_closed
    {N n : ℕ} (w : ExactDepthBoundedPositiveWord N n) :
    exactDepthBoundedCylinder w =ᵐ[uniform01Measure]
      closedGaussPrefixCylinder w.1.1 := by
  apply ae_eq_set.mpr
  constructor
  · have hsub : exactDepthBoundedCylinder w ⊆
        closedGaussPrefixCylinder w.1.1 := by
      exact gaussHalfOpenPrefixCylinder_subset_closed w.1.2.2.1
    rw [diff_eq_empty.mpr hsub, measure_empty]
  · simpa only [exactDepthBoundedCylinder, positivePrefixCylinder] using!
      uniform01Measure_closedGaussPrefixCylinder_diff_halfOpen w.1.2.2.1

/-- Exact-depth bounded cylinders are pairwise disjoint. -/
theorem pairwise_disjoint_exactDepthBoundedCylinder (N n : ℕ) :
    Pairwise fun w v : ExactDepthBoundedPositiveWord N n ↦
      Disjoint (exactDepthBoundedCylinder w)
        (exactDepthBoundedCylinder v) := by
  intro w v hwv
  apply pairwise_disjoint_positivePrefixCylinder n
  intro hpositive
  apply hwv
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : PositiveDigitWord n ↦ z.1) hpositive

/-! ## Simultaneous value windows inside one deepest cylinder -/

/-- One labeled occurrence in a mixed falling-factorial tuple. -/
abbrev GaussPrefixMixedOccurrence (k : ι → ℕ) :=
  Σ i, Fin (k i)

/-- Reverse-triangle lemma in the precise finite-sum form used for carrier
separation.  If one summand has size at least `Q` and the sum of the
absolute values of all other summands is at most `Q / 2`, the full carrier
has size at least `Q / 2`. -/
theorem half_le_abs_sum_of_dominant_occurrence
    (k : ι → ℕ) (term : GaussPrefixMixedOccurrence k → ℝ)
    (z₀ : GaussPrefixMixedOccurrence k) {Q : ℝ}
    (hmain : Q ≤ |term z₀|)
    (hrest : (∑ z ∈ (Finset.univ :
        Finset (GaussPrefixMixedOccurrence k)).erase z₀, |term z|) ≤
      Q / 2) :
    Q / 2 ≤ |∑ z, term z| := by
  classical
  let rest : ℝ := ∑ z ∈ (Finset.univ :
    Finset (GaussPrefixMixedOccurrence k)).erase z₀, term z
  have hdecomp : term z₀ + rest = ∑ z, term z := by
    exact Finset.add_sum_erase Finset.univ term (Finset.mem_univ z₀)
  have hrestAbs : |rest| ≤ Q / 2 := by
    calc
      |rest| ≤ ∑ z ∈ (Finset.univ :
          Finset (GaussPrefixMixedOccurrence k)).erase z₀, |term z| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ Q / 2 := hrest
  have htriangle : |term z₀| ≤ |∑ z, term z| + |rest| := by
    calc
      |term z₀| = |(∑ z, term z) - rest| := by
        rw [← hdecomp]
        ring_nf
      _ ≤ |∑ z, term z| + |rest| := abs_sub _ _
  linarith

/-- Weighted common-scale estimate.  If every scale `q z` is at most
`Q / P`, and twice the total nonnegative weight is at most `P`, then the
whole weighted sum is at most `Q / 2`.  The multiplication-only statement
avoids any hidden division by an asymptotic parameter. -/
theorem two_mul_sum_weight_mul_le_of_common_scale
    { α : Type* } [Fintype α]
    (S : Finset α) (weight q : α → ℝ) {P Q : ℝ}
    (hP : 0 < P) (hQ : 0 ≤ Q)
    (hweight : ∀ z ∈ S, 0 ≤ weight z)
    (hscale : ∀ z ∈ S, weight z = 0 ∨ P * q z ≤ Q)
    (hbudget : 2 * (∑ z ∈ S, weight z) ≤ P) :
    2 * (∑ z ∈ S, weight z * q z) ≤ Q := by
  have hscaled :
      P * (∑ z ∈ S, weight z * q z) ≤
        (∑ z ∈ S, weight z) * Q := by
    calc
      P * (∑ z ∈ S, weight z * q z) =
          ∑ z ∈ S, weight z * (P * q z) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _hz
        ring
      _ ≤ ∑ z ∈ S, weight z * Q := by
        apply Finset.sum_le_sum
        intro z hz
        rcases hscale z hz with hzero | hzscale
        · simp only [hzero, zero_mul]
          exact le_rfl
        · exact mul_le_mul_of_nonneg_left hzscale (hweight z hz)
      _ = (∑ z ∈ S, weight z) * Q := by
        rw [Finset.sum_mul]
  have hcancel :
      P * (2 * (∑ z ∈ S, weight z * q z)) ≤ P * Q := by
    calc
      P * (2 * (∑ z ∈ S, weight z * q z)) =
          2 * (P * (∑ z ∈ S, weight z * q z)) := by ring
      _ ≤ 2 * ((∑ z ∈ S, weight z) * Q) := by
        exact mul_le_mul_of_nonneg_left hscaled (by norm_num)
      _ = (2 * (∑ z ∈ S, weight z)) * Q := by ring
      _ ≤ P * Q := mul_le_mul_of_nonneg_right hbudget hQ
  exact le_of_mul_le_mul_left hcancel hP

/-- The fixed earlier prefix word belonging to one occurrence after a
deepest cylinder has been selected. -/
def exactDepthCylinderOccurrenceWord
    (N : ℕ) (k : ι → ℕ) (F : GaussPrefixMixedDepthTuple N k)
    {m : ℕ} (hF : ∀ i j, (F i j : ℕ) ≤ m)
    (w : ExactDepthBoundedPositiveWord N m)
    (z : GaussPrefixMixedOccurrence k) :
    PositiveDigitWord (F z.1 z.2 : ℕ) :=
  positiveDigitWordTake (F z.1 z.2 : ℕ) (hF z.1 z.2) w.toPositive

/-- Closed-cylinder intersection with every signed-value window of a mixed
tuple.  All functions in this definition are explicit affine functions. -/
def exactDepthMixedValueWindowIntersection
    (N : ℕ) (k : ι → ℕ) (F : GaussPrefixMixedDepthTuple N k)
    {m : ℕ} (hF : ∀ i j, (F i j : ℕ) ≤ m)
    (w : ExactDepthBoundedPositiveWord N m)
    (lower upper : ∀ i, Fin (k i) → ℝ) : Set ℝ :=
  finiteAffineWindowIntersection
    (closedGaussPrefixCylinderLeft w.1.1)
    (closedGaussPrefixCylinderRight w.1.1)
    (fun z : GaussPrefixMixedOccurrence k ↦ lower z.1 z.2)
    (fun z : GaussPrefixMixedOccurrence k ↦ upper z.1 z.2)
    (fun z : GaussPrefixMixedOccurrence k ↦
      gaussPrefixMarkedValueSlope N
        (exactDepthCylinderOccurrenceWord N k F hF w z))
    (fun z : GaussPrefixMixedOccurrence k ↦
      gaussPrefixMarkedValueIntercept N
        (exactDepthCylinderOccurrenceWord N k F hF w z))

/-- The complete simultaneous signed-value constraint in one deepest
cylinder is empty or a single closed interval. -/
theorem exactDepthMixedValueWindowIntersection_eq_empty_or_Icc
    (N : ℕ) (k : ι → ℕ) (F : GaussPrefixMixedDepthTuple N k)
    {m : ℕ} (hF : ∀ i j, (F i j : ℕ) ≤ m)
    (w : ExactDepthBoundedPositiveWord N m)
    (lower upper : ∀ i, Fin (k i) → ℝ) :
    exactDepthMixedValueWindowIntersection N k F hF w lower upper = ∅ ∨
      ∃ left right : ℝ, left ≤ right ∧
        exactDepthMixedValueWindowIntersection N k F hF w lower upper =
          Icc left right := by
  unfold exactDepthMixedValueWindowIntersection
  exact finiteAffineWindowIntersection_eq_empty_or_Icc
    (closedGaussPrefixCylinderLeft w.1.1)
    (closedGaussPrefixCylinderRight w.1.1)
    (fun z : GaussPrefixMixedOccurrence k ↦ lower z.1 z.2)
    (fun z : GaussPrefixMixedOccurrence k ↦ upper z.1 z.2)
    (fun z : GaussPrefixMixedOccurrence k ↦
      gaussPrefixMarkedValueSlope N
        (exactDepthCylinderOccurrenceWord N k F hF w z))
    (fun z : GaussPrefixMixedOccurrence k ↦
      gaussPrefixMarkedValueIntercept N
        (exactDepthCylinderOccurrenceWord N k F hF w z))

/-- On an actual point of the deepest half-open cylinder, membership in the
explicit affine intersection is equivalent to all selected earlier signed
marked values lying in their prescribed windows. -/
theorem mem_exactDepthMixedValueWindowIntersection_iff
    (N : ℕ) (k : ι → ℕ) (F : GaussPrefixMixedDepthTuple N k)
    {m : ℕ} (hF : ∀ i j, (F i j : ℕ) ≤ m)
    (w : ExactDepthBoundedPositiveWord N m)
    (lower upper : ∀ i, Fin (k i) → ℝ)
    {x : ℝ} (hxUnit : x ∈ Ioo (0 : ℝ) 1)
    (hxNonterm : ∀ r : ℕ, (gaussMap^[r]) x ≠ 0)
    (hx : x ∈ exactDepthBoundedCylinder w) :
    x ∈ exactDepthMixedValueWindowIntersection N k F hF w lower upper ↔
      ∀ i j,
        (gaussPrefixMarkedPoint N (F i j)
          (selectedGaussPrefixWord (F i j) x) x).2.1 ∈
            Icc (lower i j) (upper i j) := by
  have hxClosed : x ∈ closedGaussPrefixCylinder w.1.1 :=
    gaussHalfOpenPrefixCylinder_subset_closed w.1.2.2.1 hx
  have hxBounds : x ∈ Icc (closedGaussPrefixCylinderLeft w.1.1)
      (closedGaussPrefixCylinderRight w.1.1) := by
    rw [← closedGaussPrefixCylinder_eq_Icc w.1.2.2.1]
    exact hxClosed
  constructor
  · intro hinter i j
    have hall := Set.mem_iInter.mp hinter.2
      (⟨i, j⟩ : GaussPrefixMixedOccurrence k)
    change
      gaussPrefixMarkedValueSlope N
          (exactDepthCylinderOccurrenceWord N k F hF w ⟨i, j⟩) * x +
        gaussPrefixMarkedValueIntercept N
          (exactDepthCylinderOccurrenceWord N k F hF w ⟨i, j⟩) ∈
        Icc (lower i j) (upper i j) at hall
    have hvalue :=
      selectedGaussPrefixMarkedPoint_value_eq_affine_on_deeperCylinder
        (N := N) (hF i j) w.toPositive hxUnit hxNonterm hx
    simpa only [exactDepthCylinderOccurrenceWord] using! hvalue.symm ▸ hall
  · intro hall
    refine ⟨hxBounds, Set.mem_iInter.mpr ?_⟩
    rintro ⟨i, j⟩
    have hvalue :=
      selectedGaussPrefixMarkedPoint_value_eq_affine_on_deeperCylinder
        (N := N) (hF i j) w.toPositive hxUnit hxNonterm hx
    change
      gaussPrefixMarkedValueSlope N
          (exactDepthCylinderOccurrenceWord N k F hF w ⟨i, j⟩) * x +
        gaussPrefixMarkedValueIntercept N
          (exactDepthCylinderOccurrenceWord N k F hF w ⟨i, j⟩) ∈
        Icc (lower i j) (upper i j)
    simpa only [exactDepthCylinderOccurrenceWord] using! hvalue ▸ hall i j

/-- On a fixed deeper cylinder and in the paper's compact value range, the
literal marked event at an earlier depth is equivalent to its one signed
value-window constraint.  Denominator admissibility follows from monotonicity
of prefix denominators; the Legendre cutoff follows from
`A / log N < 1/2`; time and torus membership are automatic. -/
theorem mem_gaussPrefixMarkedEvent_compactValue_iff_on_deeperCylinder
    {N n m : ℕ} (hN : 2 ≤ N) (hnm : n ≤ m)
    (w : PositiveDigitWord m) {a b A x : ℝ}
    (ha : |a| ≤ A) (hb : |b| ≤ A)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2)
    (hdeepDen : cfTerminalDenominator w.1 ≤ N)
    (hxUnit : x ∈ Ioo (0 : ℝ) 1)
    (hxNonterm : ∀ r : ℕ, (gaussMap^[r]) x ≠ 0)
    (hx : x ∈ positivePrefixCylinder m w) :
    x ∈ gaussPrefixMarkedEvent N (compactValueMarkedRegion a b) n ↔
      (gaussPrefixMarkedPoint N n (selectedGaussPrefixWord n x) x).2.1 ∈
        Icc a b := by
  let u : PositiveDigitWord n := positiveDigitWordTake n hnm w
  have hxIco : x ∈ Ico (0 : ℝ) 1 := ⟨hxUnit.1.le, hxUnit.2⟩
  have hu : x ∈ positivePrefixCylinder n u :=
    mem_positivePrefixCylinder_positiveDigitWordTake hnm w hxIco hx
  have hselected : selectedGaussPrefixWord n x = u :=
    selectedGaussPrefixWord_eq_of_mem u hu
  have hden : cfTerminalDenominator u.1 ≤ N := by
    exact (cfTerminalDenominator_take_le n hnm w).trans hdeepDen
  have hdenPos : 0 < cfTerminalDenominator u.1 :=
    cfTerminalDenominator_pos u.2.2
  constructor
  · intro hevent
    exact (selectedGaussPrefixWord_data_of_mem hevent).2.2.2.2.1
  · intro hvalue
    rw [hselected] at hvalue
    have hex : x ∉ gaussPrefixExceptional (n + 1) :=
      not_mem_gaussPrefixExceptional_of_nonterminating
        hxUnit hxNonterm (n + 1)
    have hthetaPos : 0 < gaussApproximationCoordinate n x :=
      gaussApproximationCoordinate_pos_of_mem_positivePrefix
        u hxUnit hex hu
    have hlogPos : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast hN)
    have hvalueAbs :
        |(gaussPrefixMarkedPoint N n u x).2.1| ≤ A := by
      apply abs_le.mpr
      exact ⟨(abs_le.mp ha).1.trans hvalue.1,
        hvalue.2.trans (abs_le.mp hb).2⟩
    have habsFormula :
        |(gaussPrefixMarkedPoint N n u x).2.1| =
          Real.log (N : ℝ) * gaussApproximationCoordinate n x := by
      unfold gaussPrefixMarkedPoint
      change |(-1 : ℝ) ^ n * Real.log (N : ℝ) *
        gaussApproximationCoordinate n x| = _
      rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
        one_mul, abs_of_pos hlogPos, abs_of_pos hthetaPos]
    have hscaled :
        Real.log (N : ℝ) * gaussApproximationCoordinate n x ≤ A := by
      rw [← habsFormula]
      exact hvalueAbs
    have hthetaLe : gaussApproximationCoordinate n x ≤
        A / Real.log (N : ℝ) := by
      apply (le_div_iff₀ hlogPos).2
      simpa only [mul_comm] using! hscaled
    have hthetaSmall : gaussApproximationCoordinate n x < (1 : ℝ) / 2 :=
      hthetaLe.trans_lt hsmall
    have hp : cfTerminalDenominator u.1 ∈ Finset.Icc 1 N :=
      Finset.mem_Icc.mpr ⟨Nat.succ_le_iff.mpr hdenPos, hden⟩
    have htime := resonanceTimeCoordinate_mem_Icc hN hp
    have htorus :
        (gaussPrefixMarkedPoint N n u x).2.2 ∈ Icc (0 : ℝ) 1 := by
      unfold gaussPrefixMarkedPoint
      exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
    have hpoint : gaussPrefixMarkedPoint N n u x ∈
        compactValueMarkedRegion a b := by
      exact ⟨htime, hvalue, htorus⟩
    exact mem_gaussPrefixMarkedEvent_iff.mpr
      ⟨u, hu, hden, hthetaSmall, hpoint⟩

/-- The same simultaneous value-window set written with the *actual*
selected Gauss-prefix marked points and the actual half-open deepest
cylinder. -/
def exactDepthActualMixedValueWindowSet
    (N : ℕ) (k : ι → ℕ) (F : GaussPrefixMixedDepthTuple N k)
    {m : ℕ} (w : ExactDepthBoundedPositiveWord N m)
    (lower upper : ∀ i, Fin (k i) → ℝ) : Set ℝ :=
  exactDepthBoundedCylinder w ∩
    ⋂ z : GaussPrefixMixedOccurrence k,
      {x | (gaussPrefixMarkedPoint N (F z.1 z.2)
        (selectedGaussPrefixWord (F z.1 z.2) x) x).2.1 ∈
          Icc (lower z.1 z.2) (upper z.1 z.2)}

/-- Endpoint choices and terminating continued fractions do not change the
simultaneous value-window set under Lebesgue measure: it is almost
everywhere the explicit finite affine intersection. -/
theorem exactDepthActualMixedValueWindowSet_ae_eq_affine
    (N : ℕ) (k : ι → ℕ) (F : GaussPrefixMixedDepthTuple N k)
    {m : ℕ} (hF : ∀ i j, (F i j : ℕ) ≤ m)
    (w : ExactDepthBoundedPositiveWord N m)
    (lower upper : ∀ i, Fin (k i) → ℝ) :
    exactDepthActualMixedValueWindowSet N k F w lower upper
        =ᵐ[uniform01Measure]
      exactDepthMixedValueWindowIntersection N k F hF w lower upper := by
  have hcell := exactDepthBoundedCylinder_ae_eq_closed w
  filter_upwards [hcell, ae_nonterminating_uniform01] with x hcellx hxgood
  apply propext
  change
    (x ∈ exactDepthActualMixedValueWindowSet N k F w lower upper) ↔
      x ∈ exactDepthMixedValueWindowIntersection
        N k F hF w lower upper
  unfold exactDepthActualMixedValueWindowSet
  simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hxCell, hall⟩
    apply (mem_exactDepthMixedValueWindowIntersection_iff
      N k F hF w lower upper hxgood.1 hxgood.2 hxCell).2
    intro i j
    exact hall ⟨i, j⟩
  · intro hinter
    have hxBounds := hinter.1
    have hxClosed : x ∈ closedGaussPrefixCylinder w.1.1 := by
      rw [closedGaussPrefixCylinder_eq_Icc w.1.2.2.1]
      exact hxBounds
    have hxCell : x ∈ exactDepthBoundedCylinder w := by
      exact hcellx.symm.mp hxClosed
    refine ⟨hxCell, ?_⟩
    have hall := (mem_exactDepthMixedValueWindowIntersection_iff
      N k F hF w lower upper hxgood.1 hxgood.2 hxCell).1 hinter
    rintro ⟨i, j⟩
    exact hall i j

/-- Therefore the actual simultaneous selected-prefix window set is, up to
a uniform-Lebesgue null set, either empty or one closed interval. -/
theorem exactDepthActualMixedValueWindowSet_ae_eq_empty_or_Icc
    (N : ℕ) (k : ι → ℕ) (F : GaussPrefixMixedDepthTuple N k)
    {m : ℕ} (hF : ∀ i j, (F i j : ℕ) ≤ m)
    (w : ExactDepthBoundedPositiveWord N m)
    (lower upper : ∀ i, Fin (k i) → ℝ) :
    exactDepthActualMixedValueWindowSet N k F w lower upper
        =ᵐ[uniform01Measure] (∅ : Set ℝ) ∨
      ∃ left right : ℝ, left ≤ right ∧
        exactDepthActualMixedValueWindowSet N k F w lower upper
          =ᵐ[uniform01Measure] Icc left right := by
  have hae := exactDepthActualMixedValueWindowSet_ae_eq_affine
    N k F hF w lower upper
  rcases exactDepthMixedValueWindowIntersection_eq_empty_or_Icc
      N k F hF w lower upper with hempty | ⟨left, right, hlr, heq⟩
  · left
    simpa only [hempty] using! hae
  · right
    refine ⟨left, right, hlr, ?_⟩
    simpa only [heq] using! hae

/-! ## Conversion to the ordinary interval integral -/

/-- On a closed interval contained in `[0,1]`, restricting the uniform law
is the same as restricting Lebesgue measure to the corresponding `Ioc`.
Only the endpoints `0`, `1`, and the interval endpoints can differ, all of
which are null. -/
theorem uniform01Measure_restrict_Icc_eq_volume_restrict_Ioc
    {a b : ℝ} (hsub : Icc a b ⊆ Icc (0 : ℝ) 1) :
    uniform01Measure.restrict (Icc a b) =
      volume.restrict (Ioc a b) := by
  have hinterAE : (Icc a b ∩ Ioo (0 : ℝ) 1 : Set ℝ)
      =ᵐ[volume] (Icc a b : Set ℝ) := by
    apply ae_eq_set.mpr
    constructor
    · rw [diff_eq_empty.mpr inter_subset_left, measure_empty]
    · refine MeasureTheory.measure_mono_null
        (t := ({0, 1} : Set ℝ)) ?_ ?_
      · intro x hx
        have hxUnit := hsub hx.1
        have hnotOpen : x ∉ Ioo (0 : ℝ) 1 := by
          intro hxOpen
          exact hx.2 ⟨hx.1, hxOpen⟩
        by_cases hxzero : x = 0
        · exact Set.mem_insert_iff.mpr (Or.inl hxzero)
        · have hxpos : 0 < x :=
            lt_of_le_of_ne hxUnit.1 (Ne.symm hxzero)
          have honeLe : (1 : ℝ) ≤ x := by
            apply le_of_not_gt
            intro hxlt
            exact hnotOpen ⟨hxpos, hxlt⟩
          have hxone : x = 1 := le_antisymm hxUnit.2 honeLe
          exact Set.mem_insert_iff.mpr
            (Or.inr (Set.mem_singleton_iff.mpr hxone))
      · exact ((Set.finite_singleton (1 : ℝ)).insert 0).measure_zero volume
  calc
    uniform01Measure.restrict (Icc a b) =
        (volume.restrict (Ioo (0 : ℝ) 1)).restrict (Icc a b) := rfl
    _ = volume.restrict (Icc a b ∩ Ioo (0 : ℝ) 1) :=
      Measure.restrict_restrict measurableSet_Icc
    _ = volume.restrict (Icc a b) :=
      Measure.restrict_congr_set hinterAE
    _ = volume.restrict (Ioc a b) :=
      (restrict_Ioc_eq_restrict_Icc (μ := volume)).symm

/-- Set integration over such a closed interval is exactly mathlib's
ordinary oriented interval integral when the endpoints are ordered. -/
theorem setIntegral_uniform01_Icc_eq_intervalIntegral
    {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ Icc (0 : ℝ) 1)
    (f : ℝ → ℂ) :
    (∫ x in Icc a b, f x ∂uniform01Measure) =
      ∫ x in a..b, f x := by
  rw [intervalIntegral.integral_of_le hab]
  change (∫ x, f x ∂uniform01Measure.restrict (Icc a b)) =
    ∫ x, f x ∂volume.restrict (Ioc a b)
  rw [uniform01Measure_restrict_Icc_eq_volume_restrict_Ioc hsub]

/-- For every deepest cylinder and every finite family of selected-prefix
value windows, the actual oscillatory set integral is exactly one ordinary
interval integral (the degenerate interval is used when the retained set is
empty).  This is the literal per-cylinder input required by the
deterministic cylinder-sum estimate. -/
theorem exists_intervalIntegral_eq_setIntegral_actualMixedValueWindows
    (N : ℕ) (k : ι → ℕ) (F : GaussPrefixMixedDepthTuple N k)
    {m : ℕ} (hF : ∀ i j, (F i j : ℕ) ≤ m)
    (w : ExactDepthBoundedPositiveWord N m)
    (lower upper : ∀ i, Fin (k i) → ℝ) (K : ℝ) :
    ∃ left right : ℝ, left ≤ right ∧
      (∫ x in exactDepthActualMixedValueWindowSet N k F w lower upper,
        oscillatoryPhase K x ∂uniform01Measure) =
        ∫ x in left..right, oscillatoryPhase K x := by
  have hae := exactDepthActualMixedValueWindowSet_ae_eq_affine
    N k F hF w lower upper
  rcases exactDepthMixedValueWindowIntersection_eq_empty_or_Icc
      N k F hF w lower upper with hempty | ⟨left, right, hlr, heq⟩
  · refine ⟨0, 0, le_rfl, ?_⟩
    have haeEmpty :
        exactDepthActualMixedValueWindowSet N k F w lower upper
          =ᵐ[uniform01Measure] (∅ : Set ℝ) := by
      simpa only [hempty] using! hae
    change
      (∫ x, oscillatoryPhase K x
        ∂uniform01Measure.restrict
          (exactDepthActualMixedValueWindowSet N k F w lower upper)) =
        ∫ x in (0 : ℝ)..0, oscillatoryPhase K x
    rw [Measure.restrict_congr_set haeEmpty]
    simp
  · have haeIcc :
        exactDepthActualMixedValueWindowSet N k F w lower upper
          =ᵐ[uniform01Measure] Icc left right := by
      simpa only [heq] using! hae
    have hsub : Icc left right ⊆ Icc (0 : ℝ) 1 := by
      rw [← heq]
      intro x hx
      have hxClosed : x ∈ closedGaussPrefixCylinder w.1.1 := by
        rw [closedGaussPrefixCylinder_eq_Icc w.1.2.2.1]
        exact hx.1
      exact closedGaussPrefixCylinder_subset_unit w.1.2.2.1 hxClosed
    refine ⟨left, right, hlr, ?_⟩
    calc
      (∫ x in exactDepthActualMixedValueWindowSet N k F w lower upper,
          oscillatoryPhase K x ∂uniform01Measure) =
          ∫ x in Icc left right,
            oscillatoryPhase K x ∂uniform01Measure := by
        rw [Measure.restrict_congr_set haeIcc]
      _ = ∫ x in left..right, oscillatoryPhase K x :=
        setIntegral_uniform01_Icc_eq_intervalIntegral hlr hsub
          (oscillatoryPhase K)

/-- A point in a positive-depth marked event lies in one member of the
finite exact-depth denominator-bounded family. -/
theorem exists_mem_exactDepthBoundedCylinder_of_mem_markedEvent
    {N n : ℕ} (hn : 0 < n) {B : Set (ℝ × ℝ × ℝ)} {x : ℝ}
    (hx : x ∈ gaussPrefixMarkedEvent N B n) :
    ∃ w : ExactDepthBoundedPositiveWord N n,
      x ∈ exactDepthBoundedCylinder w := by
  have hdata := selectedGaussPrefixWord_data_of_mem hx
  let selected : PositiveDigitWord n := selectedGaussPrefixWord n x
  have hnonempty : selected.1 ≠ [] := by
    intro hempty
    have : selected.1.length = 0 := by simp [hempty]
    rw [selected.2.1] at this
    omega
  let bounded : BoundedPositiveTerminalWord N :=
    ⟨selected.1, hnonempty, selected.2.2, hdata.2.1⟩
  let exact : ExactDepthBoundedPositiveWord N n :=
    ⟨bounded, selected.2.1⟩
  refine ⟨exact, ?_⟩
  exact hdata.1

/-- The union of all exact-depth, denominator-bounded cylinders. -/
def exactDepthBoundedCylinderUnion (N n : ℕ) : Set ℝ :=
  ⋃ w : ExactDepthBoundedPositiveWord N n,
    exactDepthBoundedCylinder w

theorem measurableSet_exactDepthBoundedCylinderUnion (N n : ℕ) :
    MeasurableSet (exactDepthBoundedCylinderUnion N n) := by
  unfold exactDepthBoundedCylinderUnion
  exact MeasurableSet.iUnion measurableSet_exactDepthBoundedCylinder

theorem gaussPrefixMarkedEvent_subset_exactDepthBoundedCylinderUnion
    {N n : ℕ} (hn : 0 < n) (B : Set (ℝ × ℝ × ℝ)) :
    gaussPrefixMarkedEvent N B n ⊆
      exactDepthBoundedCylinderUnion N n := by
  intro x hx
  obtain ⟨w, hw⟩ :=
    exists_mem_exactDepthBoundedCylinder_of_mem_markedEvent hn hx
  exact Set.mem_iUnion.mpr ⟨w, hw⟩

/-! ## Exact integral decomposition of one literal mixed tuple -/

/-- If one specified component has positive depth, the full mixed tuple
character vanishes outside the finite family of exact-depth bounded
cylinders belonging to that component. -/
theorem gaussPrefixMarkedMixedTupleCharacter_eq_zero_of_not_mem_depthUnion
    (N : ℕ) (B : ι → Set (ℝ × ℝ × ℝ)) (k : ι → ℕ)
    (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k)
    (i₀ : ι) (j₀ : Fin (k i₀))
    (hdepth : (0 : ℕ) < (F i₀ j₀ : ℕ))
    {x : ℝ}
    (hx : x ∉ exactDepthBoundedCylinderUnion N (F i₀ j₀ : ℕ)) :
    gaussPrefixMarkedMixedTupleCharacter N B k h F x = 0 := by
  classical
  have hnotEvent :
      x ∉ gaussPrefixMarkedEvent N (B i₀) (F i₀ j₀ : ℕ) := by
    intro hevent
    exact hx
      (gaussPrefixMarkedEvent_subset_exactDepthBoundedCylinderUnion
        hdepth (B i₀) hevent)
  unfold gaussPrefixMarkedMixedTupleCharacter
  apply Finset.prod_eq_zero (Finset.mem_univ i₀)
  apply Finset.prod_eq_zero (Finset.mem_univ j₀)
  unfold gaussPrefixMarkedDepthCharacter
  rw [if_neg hnotEvent]

/-- Literal deepest-cylinder decomposition.  The equality has no hidden
countable sum and no discarded boundary term: the support family is finite,
measurable and pairwise disjoint, and the original mixed tuple character is
integrable. -/
theorem integral_gaussPrefixMarkedMixedTupleCharacter_eq_sum_depthCylinders
    (N : ℕ) {B : ι → Set (ℝ × ℝ × ℝ)}
    (hB : ∀ i, MeasurableSet (B i)) (k : ι → ℕ)
    (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k)
    (i₀ : ι) (j₀ : Fin (k i₀))
    (hdepth : (0 : ℕ) < (F i₀ j₀ : ℕ)) :
    (∫ x, gaussPrefixMarkedMixedTupleCharacter N B k h F x
        ∂uniform01Measure) =
      ∑ w : ExactDepthBoundedPositiveWord N (F i₀ j₀ : ℕ),
        ∫ x in exactDepthBoundedCylinder w,
          gaussPrefixMarkedMixedTupleCharacter N B k h F x
            ∂uniform01Measure := by
  classical
  let f : ℝ → ℂ := gaussPrefixMarkedMixedTupleCharacter N B k h F
  let S : Set ℝ :=
    exactDepthBoundedCylinderUnion N (F i₀ j₀ : ℕ)
  have hS : MeasurableSet S :=
    measurableSet_exactDepthBoundedCylinderUnion N (F i₀ j₀ : ℕ)
  have hf : Integrable f uniform01Measure :=
    integrable_gaussPrefixMarkedMixedTupleCharacter
      N hB k h F uniform01Measure
  have hsupport : f = S.indicator f := by
    funext x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      exact gaussPrefixMarkedMixedTupleCharacter_eq_zero_of_not_mem_depthUnion
        N B k h F i₀ j₀ hdepth hx
  calc
    (∫ x, f x ∂uniform01Measure) =
        ∫ x, S.indicator f x ∂uniform01Measure := by
      exact congrArg (fun g : ℝ → ℂ ↦
        ∫ x, g x ∂uniform01Measure) hsupport
    _ = ∫ x in S, f x ∂uniform01Measure :=
      integral_indicator hS
    _ = ∑ w : ExactDepthBoundedPositiveWord N (F i₀ j₀ : ℕ),
        ∫ x in exactDepthBoundedCylinder w, f x
          ∂uniform01Measure := by
      exact integral_iUnion_fintype
        (fun w ↦ measurableSet_exactDepthBoundedCylinder w)
        (pairwise_disjoint_exactDepthBoundedCylinder
          N (F i₀ j₀ : ℕ))
        (fun _w ↦ hf.integrableOn)

/-! ## A named representative for the cylinderwise carrier -/

/-- The mixed carrier evaluated at the canonical interior representative
of an exact-depth bounded cylinder. -/
def exactDepthCylinderMixedCarrier
    (N : ℕ) (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k) {m : ℕ}
    (w : ExactDepthBoundedPositiveWord N m) : ℝ :=
  gaussPrefixMarkedMixedCarrier N k h F
    (gaussPrefixRepresentative w.1.1)

/-- Expanded form of the representative carrier: it is the finite sum over
all labeled occurrences of the coefficient times the terminal denominator
of the canonical prefix of the deepest word. -/
theorem exactDepthCylinderMixedCarrier_eq_sum_occurrences
    (N : ℕ) (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k) {m : ℕ}
    (hF : ∀ i j, (F i j : ℕ) ≤ m)
    (w : ExactDepthBoundedPositiveWord N m) :
    exactDepthCylinderMixedCarrier N k h F w =
      ∑ z : GaussPrefixMixedOccurrence k,
        (h z.1 z.2 : ℝ) *
          (cfTerminalDenominator
            (exactDepthCylinderOccurrenceWord N k F hF w z).1 : ℝ) := by
  classical
  unfold exactDepthCylinderMixedCarrier gaussPrefixMarkedMixedCarrier
  rw [← Fintype.sum_sigma']
  apply Finset.sum_congr rfl
  rintro ⟨i, j⟩ _hz
  have hrepMem : gaussPrefixRepresentative w.1.1 ∈
      positivePrefixCylinder m w.toPositive :=
    gaussPrefixRepresentative_mem w.1.2.2.1
  have hrepUnit : gaussPrefixRepresentative w.1.1 ∈ Ico (0 : ℝ) 1 := by
    have hrepIoo : gaussPrefixRepresentative w.1.1 ∈ Ioo (0 : ℝ) 1 := by
      unfold gaussPrefixRepresentative
      exact gaussInverseWord_mem_Ioo w.1.2.2.1 (by norm_num)
    exact ⟨hrepIoo.1.le, hrepIoo.2⟩
  have hselected :
      selectedGaussPrefixWord (F i j : ℕ)
          (gaussPrefixRepresentative w.1.1) =
        positiveDigitWordTake (F i j : ℕ) (hF i j) w.toPositive :=
    selectedGaussPrefixWord_eq_positiveDigitWordTake
      (hF i j) w.toPositive hrepUnit hrepMem
  rw [hselected]
  rfl

/-- Carrier separation with an explicit remainder budget.  This isolates
the only numerical input needed later: after choosing a unique latest
nonzero occurrence, all earlier weighted denominators must total at most
half of its denominator. -/
theorem half_terminalDenominator_le_abs_exactDepthCylinderMixedCarrier
    (N : ℕ) (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k) {m : ℕ}
    (hF : ∀ i j, (F i j : ℕ) ≤ m)
    (w : ExactDepthBoundedPositiveWord N m)
    (z₀ : GaussPrefixMixedOccurrence k)
    (hdepth : (F z₀.1 z₀.2 : ℕ) = m)
    (hcoeff : h z₀.1 z₀.2 ≠ 0)
    (hrest :
      (∑ z ∈ (Finset.univ :
          Finset (GaussPrefixMixedOccurrence k)).erase z₀,
        |(h z.1 z.2 : ℝ) *
          (cfTerminalDenominator
            (exactDepthCylinderOccurrenceWord N k F hF w z).1 : ℝ)|) ≤
        (cfTerminalDenominator w.1.1 : ℝ) / 2) :
    (cfTerminalDenominator w.1.1 : ℝ) / 2 ≤
      |exactDepthCylinderMixedCarrier N k h F w| := by
  let term : GaussPrefixMixedOccurrence k → ℝ := fun z ↦
    (h z.1 z.2 : ℝ) *
      (cfTerminalDenominator
        (exactDepthCylinderOccurrenceWord N k F hF w z).1 : ℝ)
  have hdenominator :
      cfTerminalDenominator
          (exactDepthCylinderOccurrenceWord N k F hF w z₀).1 =
        cfTerminalDenominator w.1.1 := by
    simp only [exactDepthCylinderOccurrenceWord, positiveDigitWordTake,
      hdepth]
    change cfTerminalDenominator (w.1.1.take m) =
      cfTerminalDenominator w.1.1
    have hlength : w.1.1.length ≤ m := by
      rw [w.2]
    rw [List.take_of_length_le hlength]
  have habsCoeff : (1 : ℝ) ≤ |(h z₀.1 z₀.2 : ℝ)| := by
    have hnat : 1 ≤ (h z₀.1 z₀.2).natAbs :=
      Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hcoeff)
    calc
      (1 : ℝ) ≤ ((h z₀.1 z₀.2).natAbs : ℝ) := by
        exact_mod_cast hnat
      _ = |(h z₀.1 z₀.2 : ℝ)| := by
        simp
  have hmain : (cfTerminalDenominator w.1.1 : ℝ) ≤ |term z₀| := by
    dsimp only [term]
    rw [hdenominator, abs_mul,
      abs_of_nonneg (show 0 ≤ (cfTerminalDenominator w.1.1 : ℝ) by
        positivity)]
    simpa only [one_mul] using!
      (mul_le_mul_of_nonneg_right habsCoeff
        (show 0 ≤ (cfTerminalDenominator w.1.1 : ℝ) by positivity))
  rw [exactDepthCylinderMixedCarrier_eq_sum_occurrences N k h F hF w]
  exact half_le_abs_sum_of_dominant_occurrence k term z₀ hmain hrest

/-- Fully explicit deterministic carrier separation for a chronologically
separated tuple.  All other occurrences lie at least `gap` depths before
the unique latest nonzero occurrence.  The fixed Fourier weights consume
at most half of the denominator-growth factor `2 ^ (gap / 2)`, so the
latest denominator dominates the signed sum by a factor two. -/
theorem half_terminalDenominator_le_abs_exactDepthCylinderMixedCarrier_of_gap
    (N : ℕ) (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k) {m gap : ℕ}
    (hF : ∀ i j, (F i j : ℕ) ≤ m)
    (w : ExactDepthBoundedPositiveWord N m)
    (z₀ : GaussPrefixMixedOccurrence k)
    (hdepth : (F z₀.1 z₀.2 : ℕ) = m)
    (hcoeff : h z₀.1 z₀.2 ≠ 0)
    (hgap : ∀ z : GaussPrefixMixedOccurrence k, z ≠ z₀ →
      h z.1 z.2 ≠ 0 → (F z.1 z.2 : ℕ) + gap ≤ m)
    (hweightBudget :
      2 * (∑ z ∈ (Finset.univ :
          Finset (GaussPrefixMixedOccurrence k)).erase z₀,
        |(h z.1 z.2 : ℝ)|) ≤ ((2 ^ (gap / 2) : ℕ) : ℝ)) :
    (cfTerminalDenominator w.1.1 : ℝ) / 2 ≤
      |exactDepthCylinderMixedCarrier N k h F w| := by
  classical
  let S : Finset (GaussPrefixMixedOccurrence k) :=
    (Finset.univ : Finset (GaussPrefixMixedOccurrence k)).erase z₀
  let weight : GaussPrefixMixedOccurrence k → ℝ :=
    fun z ↦ |(h z.1 z.2 : ℝ)|
  let q : GaussPrefixMixedOccurrence k → ℝ := fun z ↦
    (cfTerminalDenominator
      (exactDepthCylinderOccurrenceWord N k F hF w z).1 : ℝ)
  let P : ℝ := ((2 ^ (gap / 2) : ℕ) : ℝ)
  let Q : ℝ := (cfTerminalDenominator w.1.1 : ℝ)
  have hP : 0 < P := by
    dsimp only [P]
    positivity
  have hQ : 0 ≤ Q := by
    dsimp only [Q]
    positivity
  have hscale : ∀ z ∈ S, weight z = 0 ∨ P * q z ≤ Q := by
    intro z hz
    have hzne : z ≠ z₀ := (Finset.mem_erase.mp hz).1
    by_cases hzero : h z.1 z.2 = 0
    · left
      dsimp only [weight]
      simp only [hzero, Int.cast_zero, abs_zero]
    right
    have hgapz : (F z.1 z.2 : ℕ) + gap ≤ m := hgap z hzne hzero
    have hexponent : gap / 2 ≤ (m - (F z.1 z.2 : ℕ)) / 2 := by
      omega
    have hpow : 2 ^ (gap / 2) ≤
        2 ^ ((m - (F z.1 z.2 : ℕ)) / 2) :=
      Nat.pow_le_pow_right (by norm_num) hexponent
    have hgrowth :=
      pow_two_depthGap_mul_cfTerminalDenominator_take_le
        (F z.1 z.2 : ℕ) (hF z.1 z.2) w.toPositive
    have hmul :
        2 ^ (gap / 2) *
            cfTerminalDenominator
              (exactDepthCylinderOccurrenceWord N k F hF w z).1 ≤
          cfTerminalDenominator w.1.1 := by
      calc
        2 ^ (gap / 2) *
            cfTerminalDenominator
              (exactDepthCylinderOccurrenceWord N k F hF w z).1 ≤
            2 ^ ((m - (F z.1 z.2 : ℕ)) / 2) *
              cfTerminalDenominator
                (exactDepthCylinderOccurrenceWord N k F hF w z).1 :=
          Nat.mul_le_mul_right _ hpow
        _ ≤ cfTerminalDenominator w.1.1 := by
          simpa only [exactDepthCylinderOccurrenceWord] using! hgrowth
    dsimp only [P, q, Q]
    exact_mod_cast hmul
  have htwo :
      2 * (∑ z ∈ S, weight z * q z) ≤ Q :=
    two_mul_sum_weight_mul_le_of_common_scale S weight q hP hQ
      (fun z _hz ↦ abs_nonneg _) hscale (by
        simpa only [S, weight, P] using! hweightBudget)
  apply half_terminalDenominator_le_abs_exactDepthCylinderMixedCarrier
    N k h F hF w z₀ hdepth hcoeff
  have hrewrite :
      (∑ z ∈ S,
        |(h z.1 z.2 : ℝ) *
          (cfTerminalDenominator
            (exactDepthCylinderOccurrenceWord N k F hF w z).1 : ℝ)|) =
        ∑ z ∈ S, weight z * q z := by
    apply Finset.sum_congr rfl
    intro z _hz
    rw [abs_mul, abs_of_nonneg (show 0 ≤ q z by
      dsimp only [q]
      positivity)]
  change (∑ z ∈ S,
      |(h z.1 z.2 : ℝ) *
        (cfTerminalDenominator
          (exactDepthCylinderOccurrenceWord N k F hF w z).1 : ℝ)|) ≤
    Q / 2
  rw [hrewrite]
  linarith

/-- On the interior of a deepest cylinder, the actual carrier equals its
value at the named representative. -/
theorem gaussPrefixMarkedMixedCarrier_eq_exactDepthCylinderMixedCarrier
    (N : ℕ) (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k) {m : ℕ}
    (hF : ∀ i j, (F i j : ℕ) ≤ m)
    (w : ExactDepthBoundedPositiveWord N m)
    {x : ℝ} (hxUnit : x ∈ Ico (0 : ℝ) 1)
    (hx : x ∈ exactDepthBoundedCylinder w) :
    gaussPrefixMarkedMixedCarrier N k h F x =
      exactDepthCylinderMixedCarrier N k h F w := by
  have hrepMem : gaussPrefixRepresentative w.1.1 ∈
      positivePrefixCylinder m w.toPositive := by
    exact gaussPrefixRepresentative_mem w.1.2.2.1
  have hrepUnit : gaussPrefixRepresentative w.1.1 ∈ Ico (0 : ℝ) 1 := by
    have hrepIoo : gaussPrefixRepresentative w.1.1 ∈ Ioo (0 : ℝ) 1 := by
      unfold gaussPrefixRepresentative
      exact gaussInverseWord_mem_Ioo w.1.2.2.1 (by norm_num)
    exact ⟨hrepIoo.1.le, hrepIoo.2⟩
  exact gaussPrefixMarkedMixedCarrier_eq_on_deeperCylinder
    N k h F hF w.toPositive hxUnit hrepUnit hx hrepMem

/-! ## The tuple character as a fixed carrier on its simultaneous event -/

/-- Simultaneous literal marked event, additionally restricted to one
chosen deepest half-open cylinder. -/
def exactDepthMixedTupleEventSet
    (N : ℕ) (B : ι → Set (ℝ × ℝ × ℝ)) (k : ι → ℕ)
    (F : GaussPrefixMixedDepthTuple N k) {m : ℕ}
    (w : ExactDepthBoundedPositiveWord N m) : Set ℝ :=
  exactDepthBoundedCylinder w ∩
    mixedTupleEvent (fun i ↦ gaussPrefixMarkedEvent N (B i)) F

theorem measurableSet_exactDepthMixedTupleEventSet
    (N : ℕ) {B : ι → Set (ℝ × ℝ × ℝ)}
    (hB : ∀ i, MeasurableSet (B i)) (k : ι → ℕ)
    (F : GaussPrefixMixedDepthTuple N k) {m : ℕ}
    (w : ExactDepthBoundedPositiveWord N m) :
    MeasurableSet (exactDepthMixedTupleEventSet N B k F w) := by
  apply (measurableSet_exactDepthBoundedCylinder w).inter
  apply measurableSet_mixedTupleEvent
  intro i q _hq
  exact measurableSet_gaussPrefixMarkedEvent N q (hB i)

omit [Fintype ι] in
/-- For the compact signed-value windows used in the marked Fourier
criterion, the simultaneous literal marked event in a deepest cylinder is
almost everywhere exactly the actual selected-prefix value-window set. -/
theorem exactDepthMixedTupleEventSet_compactValue_ae_eq_valueWindows
    (N : ℕ) (hN : 2 ≤ N) (k : ι → ℕ)
    (F : GaussPrefixMixedDepthTuple N k) {m : ℕ}
    (hF : ∀ i j, (F i j : ℕ) ≤ m)
    (w : ExactDepthBoundedPositiveWord N m)
    (lower upper : ι → ℝ) {A : ℝ}
    (hlower : ∀ i, |lower i| ≤ A)
    (hupper : ∀ i, |upper i| ≤ A)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2) :
    exactDepthMixedTupleEventSet N
        (fun i ↦ compactValueMarkedRegion (lower i) (upper i)) k F w
        =ᵐ[uniform01Measure]
      exactDepthActualMixedValueWindowSet N k F w
        (fun i _j ↦ lower i) (fun i _j ↦ upper i) := by
  filter_upwards [ae_nonterminating_uniform01] with x hxgood
  apply propext
  change
    (x ∈ exactDepthMixedTupleEventSet N
        (fun i ↦ compactValueMarkedRegion (lower i) (upper i)) k F w) ↔
      x ∈ exactDepthActualMixedValueWindowSet N k F w
        (fun i _j ↦ lower i) (fun i _j ↦ upper i)
  constructor
  · intro hxEvent
    refine ⟨hxEvent.1, Set.mem_iInter.mpr ?_⟩
    rintro ⟨i, j⟩
    have hi := Set.mem_iInter.mp hxEvent.2 i
    have hij := Set.mem_iInter.mp hi j
    exact (mem_gaussPrefixMarkedEvent_compactValue_iff_on_deeperCylinder
      hN (hF i j) w.toPositive (hlower i) (hupper i) hsmall
      w.1.2.2.2 hxgood.1 hxgood.2 hxEvent.1).1 hij
  · intro hxValue
    refine ⟨hxValue.1, Set.mem_iInter.mpr ?_⟩
    intro i
    apply Set.mem_iInter.mpr
    intro j
    have hij := Set.mem_iInter.mp hxValue.2
      (⟨i, j⟩ : GaussPrefixMixedOccurrence k)
    exact (mem_gaussPrefixMarkedEvent_compactValue_iff_on_deeperCylinder
      hN (hF i j) w.toPositive (hlower i) (hupper i) hsmall
      w.1.2.2.2 hxgood.1 hxgood.2 hxValue.1).2 hij

/-- On a fixed deepest cylinder, the literal mixed tuple character is the
indicator of its simultaneous marked event times one ordinary phase with
the representative carrier.  The equality is stated at the level of set
integrals and therefore already discards the terminating null set. -/
theorem setIntegral_mixedTupleCharacter_eq_fixedCarrier_on_event
    (N : ℕ) {B : ι → Set (ℝ × ℝ × ℝ)}
    (hB : ∀ i, MeasurableSet (B i)) (k : ι → ℕ)
    (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k) {m : ℕ}
    (hF : ∀ i j, (F i j : ℕ) ≤ m)
    (w : ExactDepthBoundedPositiveWord N m) :
    (∫ x in exactDepthBoundedCylinder w,
        gaussPrefixMarkedMixedTupleCharacter N B k h F x
          ∂uniform01Measure) =
      ∫ x in exactDepthMixedTupleEventSet N B k F w,
        oscillatoryPhase
          ((N : ℝ) * exactDepthCylinderMixedCarrier N k h F w) x
            ∂uniform01Measure := by
  classical
  have hcellM := measurableSet_exactDepthBoundedCylinder w
  have heventM :=
    measurableSet_exactDepthMixedTupleEventSet N hB k F w
  rw [← integral_indicator hcellM, ← integral_indicator heventM]
  apply integral_congr_ae
  filter_upwards [ae_nonterminating_uniform01] with x hxgood
  by_cases hxCell : x ∈ exactDepthBoundedCylinder w
  · rw [Set.indicator_of_mem hxCell]
    by_cases hall : ∀ i j,
        x ∈ gaussPrefixMarkedEvent N (B i) (F i j)
    · have hxMixed :
          x ∈ mixedTupleEvent
            (fun i ↦ gaussPrefixMarkedEvent N (B i)) F := by
        exact Set.mem_iInter.mpr fun i ↦
          Set.mem_iInter.mpr (hall i)
      have hxEvent : x ∈ exactDepthMixedTupleEventSet N B k F w :=
        ⟨hxCell, hxMixed⟩
      rw [Set.indicator_of_mem hxEvent]
      have hcharacter :=
        gaussPrefixMarkedMixedTupleCharacter_eq_oscillatoryPhase
          (h := h) (F := F) hxgood.1 hxgood.2 hall
      rw [hcharacter]
      have hcarrier :=
        gaussPrefixMarkedMixedCarrier_eq_exactDepthCylinderMixedCarrier
          N k h F hF w ⟨hxgood.1.1.le, hxgood.1.2⟩ hxCell
      rw [hcarrier]
    · have hxNotEvent :
          x ∉ exactDepthMixedTupleEventSet N B k F w := by
        intro hxEvent
        apply hall
        intro i j
        have hi := Set.mem_iInter.mp hxEvent.2 i
        exact Set.mem_iInter.mp hi j
      rw [Set.indicator_of_notMem hxNotEvent]
      push_neg at hall
      obtain ⟨i, j, hnot⟩ := hall
      unfold gaussPrefixMarkedMixedTupleCharacter
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      unfold gaussPrefixMarkedDepthCharacter
      rw [if_neg hnot]
  · rw [Set.indicator_of_notMem hxCell]
    have hxNotEvent :
        x ∉ exactDepthMixedTupleEventSet N B k F w := by
      exact fun hxEvent ↦ hxCell hxEvent.1
    rw [Set.indicator_of_notMem hxNotEvent]

/-- Complete per-cylinder reduction for the compact value windows: a
literal mixed tuple character is exactly one ordinary oscillatory interval
integral with its fixed terminal-denominator carrier. -/
theorem exists_intervalIntegral_eq_setIntegral_mixedTupleCharacter_compactValue
    (N : ℕ) (hN : 2 ≤ N) (k : ι → ℕ)
    (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k) {m : ℕ}
    (hF : ∀ i j, (F i j : ℕ) ≤ m)
    (w : ExactDepthBoundedPositiveWord N m)
    (lower upper : ι → ℝ) {A : ℝ}
    (hlower : ∀ i, |lower i| ≤ A)
    (hupper : ∀ i, |upper i| ≤ A)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2) :
    ∃ left right : ℝ, left ≤ right ∧
      (∫ x in exactDepthBoundedCylinder w,
        gaussPrefixMarkedMixedTupleCharacter N
          (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
          k h F x ∂uniform01Measure) =
        ∫ x in left..right,
          oscillatoryPhase
            ((N : ℝ) * exactDepthCylinderMixedCarrier N k h F w) x := by
  let B : ι → Set (ℝ × ℝ × ℝ) :=
    fun i ↦ compactValueMarkedRegion (lower i) (upper i)
  let lower' : ∀ i, Fin (k i) → ℝ := fun i _j ↦ lower i
  let upper' : ∀ i, Fin (k i) → ℝ := fun i _j ↦ upper i
  let K : ℝ := (N : ℝ) * exactDepthCylinderMixedCarrier N k h F w
  have hfixed := setIntegral_mixedTupleCharacter_eq_fixedCarrier_on_event
    N (fun i ↦ measurableSet_compactValueMarkedRegion (lower i) (upper i))
      k h F hF w
  have hae := exactDepthMixedTupleEventSet_compactValue_ae_eq_valueWindows
    N hN k F hF w lower upper hlower hupper hsmall
  obtain ⟨left, right, hlr, hinterval⟩ :=
    exists_intervalIntegral_eq_setIntegral_actualMixedValueWindows
      N k F hF w lower' upper' K
  refine ⟨left, right, hlr, ?_⟩
  calc
    (∫ x in exactDepthBoundedCylinder w,
        gaussPrefixMarkedMixedTupleCharacter N B k h F x
          ∂uniform01Measure) =
        ∫ x in exactDepthMixedTupleEventSet N B k F w,
          oscillatoryPhase K x ∂uniform01Measure := by
      simpa only [B, K] using! hfixed
    _ = ∫ x in exactDepthActualMixedValueWindowSet
          N k F w lower' upper', oscillatoryPhase K x
            ∂uniform01Measure := by
      rw [Measure.restrict_congr_set (by simpa only [B, lower', upper'] using! hae)]
    _ = ∫ x in left..right, oscillatoryPhase K x := hinterval

end

end Erdos1002
