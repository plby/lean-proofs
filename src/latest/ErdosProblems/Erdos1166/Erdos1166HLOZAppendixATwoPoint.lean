/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1166.Erdos1166HLOZAppendixASecondMoment
import ErdosProblems.Erdos1166.Erdos1166HLOZLemma410

/-!
# The source-specific Appendix-A two-point reduction

This file provides two missing interfaces around HLOZ Proposition A.3(2).

* The source separation level `l(x,y)` is totalized and its shells are proved
  to lie in the radius-`2 r_{n,l-1}` lattice neighborhood.  Diagonal pairs,
  for which no separating scale exists, are deliberately assigned the level
  `n+2` and hence stay outside every usable two-point cutoff.
* The probability calculation (A.14)--(A.17) and Remark A.9 is reduced to
  precisely named Harnack/conditional-decoupling and truncated first-moment
  premises.  The finite fiber sum and all multiplicative/exponential algebra
  are checked here.
-/

namespace Erdos1166.HLOZAppendixATwoPoint

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

open HLOZAppendixASecondMoment

/-! ## Source separation levels and shell containment -/

/-- The source radius `r_{n,m}=e^{n-m}n^9`. -/
noncomputable def appendixDiskScale (n m : ℕ) : ℝ :=
  Real.exp ((n : ℝ) - (m : ℝ)) * (n : ℝ) ^ 9

theorem appendixDiskScale_pred {n l : ℕ} (hl : 1 ≤ l) :
    appendixDiskScale n (l - 1) = appendixShellScale n l := by
  rw [appendixDiskScale, appendixShellScale]
  have hcast : (((l - 1 : ℕ) : ℝ)) = (l : ℝ) - 1 := by
    rw [Nat.cast_sub hl]
    norm_num
  rw [hcast]
  congr 2
  ring

/-- Two equal-radius Euclidean disks are separated at scale `m` once their
center distance is strictly larger than twice the source radius. -/
def appendixDisksSeparated (n m : ℕ) (x y : Site) : Prop :=
  (2 * appendixDiskScale n m) ^ 2 < (siteSquaredDistance x y : ℝ)

/-- Totalized source separation level.  If no separating scale exists (in
particular for `x=y`), the value is `n+2`, beyond the range in which
Proposition A.3(2) is used. -/
noncomputable def appendixSeparationLevel (n : ℕ) (x y : Site) : ℕ :=
  by
    classical
    exact if h : ∃ m : ℕ, 1 ≤ m ∧ appendixDisksSeparated n m x y then
      Nat.find h
    else n + 2

theorem appendixSeparationLevel_spec_of_le
    {n : ℕ} {x y : Site} (hlevel : appendixSeparationLevel n x y ≤ n + 1) :
    1 ≤ appendixSeparationLevel n x y ∧
      appendixDisksSeparated n (appendixSeparationLevel n x y) x y := by
  classical
  by_cases h : ∃ m : ℕ, 1 ≤ m ∧ appendixDisksSeparated n m x y
  · simpa [appendixSeparationLevel, h] using Nat.find_spec h
  · simp [appendixSeparationLevel, h] at hlevel

theorem not_appendixDisksSeparated_pred_of_level
    {n l : ℕ} {x y : Site} (hl : 1 < l) (husable : l ≤ n + 1)
    (hlevel : appendixSeparationLevel n x y = l) :
    ¬ appendixDisksSeparated n (l - 1) x y := by
  classical
  have hspec := appendixSeparationLevel_spec_of_le
    (hlevel ▸ husable)
  unfold appendixSeparationLevel at hlevel
  split_ifs at hlevel with h
  · have hpredlt : l - 1 < Nat.find h := by omega
    exact fun hsep ↦ Nat.find_min h hpredlt ⟨by omega, hsep⟩
  · omega

theorem siteSquaredDistance_le_pred_radius_of_level
    {n l : ℕ} {x y : Site} (hl : 1 < l) (husable : l ≤ n + 1)
    (hlevel : appendixSeparationLevel n x y = l) :
    (siteSquaredDistance x y : ℝ) ≤ (2 * appendixShellScale n l) ^ 2 := by
  have hnot := not_appendixDisksSeparated_pred_of_level hl husable hlevel
  rw [appendixDisksSeparated, appendixDiskScale_pred (by omega)] at hnot
  exact le_of_not_gt hnot

private theorem mem_latticeSupBall_of_squaredDistance_le
    {x y : Site} {r : ℝ} {R : ℕ} (hr : 0 ≤ r) (hrR : r ≤ (R : ℝ))
    (hdist : (siteSquaredDistance x y : ℝ) ≤ r ^ 2) :
    y ∈ latticeSupBall x R := by
  have coordinate_le (z : ℤ)
      (hz : z.natAbs ^ 2 ≤ siteSquaredDistance x y) : z.natAbs ≤ R := by
    have hzsq : ((z.natAbs ^ 2 : ℕ) : ℝ) ≤ r ^ 2 := by
      exact (by exact_mod_cast hz : ((z.natAbs ^ 2 : ℕ) : ℝ) ≤
        (siteSquaredDistance x y : ℝ)) |>.trans hdist
    by_contra h
    have hRzNat : R < z.natAbs := Nat.lt_of_not_ge h
    have hRz : (R : ℝ) < z.natAbs := by exact_mod_cast hRzNat
    have hrz : r < (z.natAbs : ℝ) := hrR.trans_lt hRz
    have hz0 : 0 ≤ (z.natAbs : ℝ) := by positivity
    have hsquare : r ^ 2 < (z.natAbs : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (r + (z.natAbs : ℝ))]
    rw [Nat.cast_pow] at hzsq
    exact (not_lt_of_ge hzsq) hsquare
  have hxcoord : (x.1 - y.1).natAbs ≤ R := by
    apply coordinate_le
    rw [siteSquaredDistance]
    omega
  have hycoord : (x.2 - y.2).natAbs ≤ R := by
    apply coordinate_le
    rw [siteSquaredDistance]
    omega
  have hxabs : |x.1 - y.1| ≤ (R : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hxcoord
  have hyabs : |x.2 - y.2| ≤ (R : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hycoord
  rw [latticeSupBall]
  apply Finset.mem_product.mpr
  rcases abs_le.mp hxabs with ⟨hxlo, hxhi⟩
  rcases abs_le.mp hyabs with ⟨hylo, hyhi⟩
  constructor
  · apply Finset.mem_Icc.mpr
    constructor <;> omega
  · apply Finset.mem_Icc.mpr
    constructor <;> omega

theorem separation_level_gt_one_mem_rounded_ball
    {n l : ℕ} {x y : Site} (hl : 1 < l) (husable : l ≤ n + 1)
    (hlevel : appendixSeparationLevel n x y = l) :
    y ∈ latticeSupBall x (roundedAppendixShellRadius n l) := by
  apply mem_latticeSupBall_of_squaredDistance_le
    (r := 2 * appendixShellScale n l)
  · unfold appendixShellScale
    positivity
  · exact Nat.le_ceil _
  · exact siteSquaredDistance_le_pred_radius_of_level hl husable hlevel

/-- At the first shell, containment follows from the source box itself.
The only rounding premise says that its integer side length is at most
`2r_{n,0}`. -/
theorem separation_level_one_mem_rounded_ball
    {n R : ℕ} {x y : Site}
    (hx : x ∈ appendixSiteBox R) (hy : y ∈ appendixSiteBox R)
    (hR : (R : ℝ) ≤ 2 * appendixShellScale n 1) :
    y ∈ latticeSupBall x (roundedAppendixShellRadius n 1) := by
  have hRceilReal : (R : ℝ) ≤ (roundedAppendixShellRadius n 1 : ℝ) :=
    hR.trans (Nat.le_ceil _)
  have hRceil : R ≤ roundedAppendixShellRadius n 1 := by exact_mod_cast hRceilReal
  rw [appendixSiteBox] at hx hy
  have hxData := Finset.mem_product.mp hx
  have hyData := Finset.mem_product.mp hy
  simp only [Finset.mem_Icc] at hxData hyData
  rw [latticeSupBall]
  apply Finset.mem_product.mpr
  constructor
  · apply Finset.mem_Icc.mpr
    constructor <;> omega
  · apply Finset.mem_Icc.mpr
    constructor <;> omega

/-- Direct source shell containment for every usable separation level. -/
theorem separationShell_appendixSeparationLevel_subset
    {n R l : ℕ} {x : Site} (hx : x ∈ appendixSiteBox R)
    (hl : 1 ≤ l) (husable : l ≤ n + 1)
    (hR : (R : ℝ) ≤ 2 * appendixShellScale n 1) :
    ∀ y ∈ separationShell (appendixSiteBox R)
        (appendixSeparationLevel n) x l,
      y ∈ latticeSupBall x (roundedAppendixShellRadius n l) := by
  intro y hy
  have hyData := Finset.mem_filter.mp hy
  have hyU : y ∈ appendixSiteBox R := hyData.1
  have hlevel : appendixSeparationLevel n x y = l := hyData.2
  rcases hl.eq_or_lt with rfl | hlgt
  · exact separation_level_one_mem_rounded_ball hx hyU hR
  · exact separation_level_gt_one_mem_rounded_ball hlgt husable hlevel

/-- The checked source shell count used by the second-moment assembly. -/
theorem source_separationShell_card_le
    {n R l : ℕ} {x : Site} (hn : 1 ≤ n) (hx : x ∈ appendixSiteBox R)
    (hl : 1 ≤ l) (husable : l ≤ n + 1)
    (hR : (R : ℝ) ≤ 2 * appendixShellScale n 1) :
    ((separationShell (appendixSiteBox R)
      (appendixSeparationLevel n) x l).card : ℝ) ≤
      (49 * Real.exp 2) * appendixKScale n ^ 2 *
        Real.exp (-2 * (l : ℝ)) := by
  apply card_separationShell_real_le_exp
    (radius := roundedAppendixShellRadius n)
  · exact separationShell_appendixSeparationLevel_subset hx hl husable hR
  · simpa [mul_assoc] using roundedAppendixShellRadius_sq_le_exp hn husable

/-! ## The finite conditional-decoupling sum -/

variable {Ω ι : Type*} [MeasurableSpace Ω]

/-- Checked form of (A.16)--(A.17): cover a truncated pair event by its
finitely many excursion-count fibers, apply a uniform conditional Harnack
bound on each fiber, and sum the outer fiber masses. -/
theorem truncated_pair_le_of_fiber_decoupling
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (truncated : Set Ω) (innerFiber outerFiber : ℕ → Set Ω)
    (cutoff : ℕ) {harnack innerBound outerMass : ℝ}
    (hharnack0 : 0 ≤ harnack) (hinner0 : 0 ≤ innerBound)
    (hcover : truncated ⊆
      ⋃ m ∈ Finset.range (cutoff + 1), innerFiber m ∩ outerFiber m)
    (hconditionalHarnack : ∀ m ≤ cutoff,
      μ.real (innerFiber m ∩ outerFiber m) ≤
        harnack * innerBound * μ.real (outerFiber m))
    (houterFibers :
      (∑ m ∈ Finset.range (cutoff + 1), μ.real (outerFiber m)) ≤ outerMass) :
    μ.real truncated ≤ harnack * innerBound * outerMass := by
  have hfactor0 : 0 ≤ harnack * innerBound := mul_nonneg hharnack0 hinner0
  calc
    μ.real truncated ≤ μ.real
        (⋃ m ∈ Finset.range (cutoff + 1), innerFiber m ∩ outerFiber m) :=
      measureReal_mono hcover (measure_ne_top μ _)
    _ ≤ ∑ m ∈ Finset.range (cutoff + 1),
        μ.real (innerFiber m ∩ outerFiber m) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ m ∈ Finset.range (cutoff + 1),
        harnack * innerBound * μ.real (outerFiber m) := by
      apply Finset.sum_le_sum
      intro m hm
      exact hconditionalHarnack m (Nat.le_of_lt_succ (by simpa using hm))
    _ = (harnack * innerBound) *
        ∑ m ∈ Finset.range (cutoff + 1), μ.real (outerFiber m) := by
      rw [Finset.mul_sum]
    _ ≤ (harnack * innerBound) * outerMass :=
      mul_le_mul_of_nonneg_left houterFibers hfactor0
    _ = harnack * innerBound * outerMass := by ring

/-- The final tail step in (A.14): an absolute truncation-tail estimate and
the one-point lower estimates are logically separate.  Once the former is
small enough to be absorbed by the latter, it has the relative product form
needed by the two-point calculation. -/
theorem discarded_excursion_tail_absorbed_by_first_moments
    (μ : Measure Ω) (tail : Set Ω) (Ax Ay : Set Ω) (l : ℕ)
    {tailBound Et : ℝ}
    (hRawDiscardedExcursionTail : μ.real tail ≤ tailBound)
    (hTailAbsorbedByOnePointLowerBounds : tailBound ≤
      Real.exp (2 * (l : ℝ) + Et) * μ.real Ax * μ.real Ay) :
    μ.real tail ≤
      Real.exp (2 * (l : ℝ) + Et) * μ.real Ax * μ.real Ay :=
  hRawDiscardedExcursionTail.trans hTailAbsorbedByOnePointLowerBounds

/-- One-point form of the complete Proposition A.3(2) reduction.

The named premises correspond respectively to (A.14), (A.16), (A.17), and
the four comparisons in Remark A.9.  `Eh`, `Ei`, `Eo`, and `Et` record the
Harnack, inner-truncation, outer-profile, and discarded-tail errors. -/
theorem propA3_twoPoint_of_conditional_decoupling
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Ax Ay truncated tail : Set Ω)
    (innerFiber outerFiber : ℕ → Set Ω) (cutoff l : ℕ)
    {harnack innerBound outerMass Eh Ei Eo Et E : ℝ}
    (hharnack0 : 0 ≤ harnack) (hinner0 : 0 ≤ innerBound)
    (houter0 : 0 ≤ outerMass)
    (hpairSplit : Ax ∩ Ay ⊆ truncated ∪ tail)
    (htruncatedFiberCover : truncated ⊆
      ⋃ m ∈ Finset.range (cutoff + 1), innerFiber m ∩ outerFiber m)
    (hHarnackConditionalDecoupling : ∀ m ≤ cutoff,
      μ.real (innerFiber m ∩ outerFiber m) ≤
        harnack * innerBound * μ.real (outerFiber m))
    (hOuterFiberMass :
      (∑ m ∈ Finset.range (cutoff + 1), μ.real (outerFiber m)) ≤ outerMass)
    (hHarnackFactor : harnack ≤ Real.exp Eh)
    (hTruncatedInnerFirstMoment :
      innerBound ≤ Real.exp (2 * (l : ℝ) + Ei) * μ.real Ay)
    (hOuterProfileFirstMoment : outerMass ≤ Real.exp Eo * μ.real Ax)
    (hDiscardedExcursionTail : μ.real tail ≤
      Real.exp (2 * (l : ℝ) + Et) * μ.real Ax * μ.real Ay)
    (hErrorBudget : Real.exp (Eh + Ei + Eo) + Real.exp Et ≤ Real.exp E) :
    μ.real (Ax ∩ Ay) ≤
      Real.exp (2 * (l : ℝ) + E) * μ.real Ax * μ.real Ay := by
  have htruncated := truncated_pair_le_of_fiber_decoupling μ truncated
    innerFiber outerFiber cutoff hharnack0 hinner0 htruncatedFiberCover
    hHarnackConditionalDecoupling hOuterFiberMass
  have hAx0 : 0 ≤ μ.real Ax := measureReal_nonneg
  have hAy0 : 0 ≤ μ.real Ay := measureReal_nonneg
  have hinnerMajorant0 :
      0 ≤ Real.exp (2 * (l : ℝ) + Ei) * μ.real Ay := by positivity
  have houterMajorant0 : 0 ≤ Real.exp Eo * μ.real Ax := by positivity
  have htruncatedProduct :
      harnack * innerBound * outerMass ≤
        Real.exp Eh *
          (Real.exp (2 * (l : ℝ) + Ei) * μ.real Ay) *
            (Real.exp Eo * μ.real Ax) := by
    exact mul_le_mul
      (mul_le_mul hHarnackFactor hTruncatedInnerFirstMoment hinner0
        (Real.exp_pos _).le)
      hOuterProfileFirstMoment houter0
      (mul_nonneg (Real.exp_pos _).le hinnerMajorant0)
  have htruncatedExp : μ.real truncated ≤
      Real.exp (2 * (l : ℝ) + (Eh + Ei + Eo)) *
        μ.real Ax * μ.real Ay := by
    calc
      μ.real truncated ≤ harnack * innerBound * outerMass := htruncated
      _ ≤ Real.exp Eh *
          (Real.exp (2 * (l : ℝ) + Ei) * μ.real Ay) *
            (Real.exp Eo * μ.real Ax) := htruncatedProduct
      _ = Real.exp (2 * (l : ℝ) + (Eh + Ei + Eo)) *
          μ.real Ax * μ.real Ay := by
        simp only [Real.exp_add]
        ring
  have hproduct0 : 0 ≤ μ.real Ax * μ.real Ay := mul_nonneg hAx0 hAy0
  calc
    μ.real (Ax ∩ Ay) ≤ μ.real (truncated ∪ tail) :=
      measureReal_mono hpairSplit (measure_ne_top μ _)
    _ ≤ μ.real truncated + μ.real tail := measureReal_union_le _ _
    _ ≤ Real.exp (2 * (l : ℝ) + (Eh + Ei + Eo)) *
          μ.real Ax * μ.real Ay +
        Real.exp (2 * (l : ℝ) + Et) * μ.real Ax * μ.real Ay :=
      add_le_add htruncatedExp hDiscardedExcursionTail
    _ = Real.exp (2 * (l : ℝ)) *
        (Real.exp (Eh + Ei + Eo) + Real.exp Et) *
          (μ.real Ax * μ.real Ay) := by
      simp only [Real.exp_add]
      ring
    _ ≤ Real.exp (2 * (l : ℝ)) * Real.exp E *
        (μ.real Ax * μ.real Ay) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hErrorBudget (Real.exp_pos _).le) hproduct0
    _ = Real.exp (2 * (l : ℝ) + E) * μ.real Ax * μ.real Ay := by
      rw [Real.exp_add]
      ring

/-- Uniform form whose conclusion is definitionally the `htwoPoint` input
of `appendixA_success_lower_bound`. -/
theorem propA3_twoPoint_input_of_conditional_decoupling
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Finset ι) (A : ι → Set Ω) (level : ι → ι → ℕ) (L cutoff : ℕ)
    (truncated tail : ι → ι → Set Ω)
    (innerFiber outerFiber : ι → ι → ℕ → Set Ω)
    (harnack innerBound outerMass : ι → ι → ℝ)
    {Eh Ei Eo Et E : ℝ}
    (hharnack0 : ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L → 0 ≤ harnack x y)
    (hinner0 : ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L → 0 ≤ innerBound x y)
    (houter0 : ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L → 0 ≤ outerMass x y)
    (hpairSplit : ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L →
      A x ∩ A y ⊆ truncated x y ∪ tail x y)
    (htruncatedFiberCover : ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L →
      truncated x y ⊆ ⋃ m ∈ Finset.range (cutoff + 1),
        innerFiber x y m ∩ outerFiber x y m)
    (hHarnackConditionalDecoupling : ∀ x ∈ U, ∀ y ∈ U,
      level x y ≤ L → ∀ m ≤ cutoff,
      μ.real (innerFiber x y m ∩ outerFiber x y m) ≤
        harnack x y * innerBound x y * μ.real (outerFiber x y m))
    (hOuterFiberMass : ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L →
      (∑ m ∈ Finset.range (cutoff + 1), μ.real (outerFiber x y m)) ≤
        outerMass x y)
    (hHarnackFactor : ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L →
      harnack x y ≤ Real.exp Eh)
    (hTruncatedInnerFirstMoment : ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L →
      innerBound x y ≤
        Real.exp (2 * (level x y : ℝ) + Ei) * μ.real (A y))
    (hOuterProfileFirstMoment : ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L →
      outerMass x y ≤ Real.exp Eo * μ.real (A x))
    (hDiscardedExcursionTail : ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L →
      μ.real (tail x y) ≤
        Real.exp (2 * (level x y : ℝ) + Et) *
          μ.real (A x) * μ.real (A y))
    (hErrorBudget : Real.exp (Eh + Ei + Eo) + Real.exp Et ≤ Real.exp E) :
    ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L →
      μ.real (A x ∩ A y) ≤
        Real.exp (2 * (level x y : ℝ) + E) *
          μ.real (A x) * μ.real (A y) := by
  intro x hx y hy hxy
  exact propA3_twoPoint_of_conditional_decoupling μ
    (A x) (A y) (truncated x y) (tail x y)
    (innerFiber x y) (outerFiber x y) cutoff (level x y)
    (hharnack0 x hx y hy hxy) (hinner0 x hx y hy hxy)
    (houter0 x hx y hy hxy) (hpairSplit x hx y hy hxy)
    (htruncatedFiberCover x hx y hy hxy)
    (hHarnackConditionalDecoupling x hx y hy hxy)
    (hOuterFiberMass x hx y hy hxy) (hHarnackFactor x hx y hy hxy)
    (hTruncatedInnerFirstMoment x hx y hy hxy)
    (hOuterProfileFirstMoment x hx y hy hxy)
    (hDiscardedExcursionTail x hx y hy hxy) hErrorBudget

/-! ## The source `n^(3/5+o(1))` exponent -/

/-- At a fixed `n`, the paper's `n^(3/5+o(1))` error is represented by
`n^(3/5+η)`.  In the asymptotic application, `η=η n` and `η n → 0`.
Keeping `η` explicit makes the finite-`n` inequality exact. -/
noncomputable def appendixTwoPointError (n : ℕ) (η : ℝ) : ℝ :=
  Real.rpow (n : ℝ) ((3 : ℝ) / 5 + η)

/-- Source-exponent specialization of
`propA3_twoPoint_input_of_conditional_decoupling`.  Its conclusion is exactly
the `htwoPoint` input of `appendixA_success_lower_bound`, with the paper's
factor `exp(2l+n^(3/5+η))`. -/
theorem propA3_twoPoint_input_source_exponent
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (η : ℝ)
    (U : Finset ι) (A : ι → Set Ω) (level : ι → ι → ℕ) (L cutoff : ℕ)
    (truncated tail : ι → ι → Set Ω)
    (innerFiber outerFiber : ι → ι → ℕ → Set Ω)
    (harnack innerBound outerMass : ι → ι → ℝ)
    {Eh Ei Eo Et : ℝ}
    (hharnack0 : ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L → 0 ≤ harnack x y)
    (hinner0 : ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L → 0 ≤ innerBound x y)
    (houter0 : ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L → 0 ≤ outerMass x y)
    (hpairSplit : ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L →
      A x ∩ A y ⊆ truncated x y ∪ tail x y)
    (htruncatedFiberCover : ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L →
      truncated x y ⊆ ⋃ m ∈ Finset.range (cutoff + 1),
        innerFiber x y m ∩ outerFiber x y m)
    (hHarnackConditionalDecoupling : ∀ x ∈ U, ∀ y ∈ U,
      level x y ≤ L → ∀ m ≤ cutoff,
      μ.real (innerFiber x y m ∩ outerFiber x y m) ≤
        harnack x y * innerBound x y * μ.real (outerFiber x y m))
    (hOuterFiberMass : ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L →
      (∑ m ∈ Finset.range (cutoff + 1), μ.real (outerFiber x y m)) ≤
        outerMass x y)
    (hHarnackFactor : ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L →
      harnack x y ≤ Real.exp Eh)
    (hTruncatedInnerFirstMoment : ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L →
      innerBound x y ≤
        Real.exp (2 * (level x y : ℝ) + Ei) * μ.real (A y))
    (hOuterProfileFirstMoment : ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L →
      outerMass x y ≤ Real.exp Eo * μ.real (A x))
    (hDiscardedExcursionTail : ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L →
      μ.real (tail x y) ≤
        Real.exp (2 * (level x y : ℝ) + Et) *
          μ.real (A x) * μ.real (A y))
    (hSourceErrorBudget :
      Real.exp (Eh + Ei + Eo) + Real.exp Et ≤
        Real.exp (appendixTwoPointError n η)) :
    ∀ x ∈ U, ∀ y ∈ U, level x y ≤ L →
      μ.real (A x ∩ A y) ≤
        Real.exp (2 * (level x y : ℝ) + appendixTwoPointError n η) *
          μ.real (A x) * μ.real (A y) := by
  exact propA3_twoPoint_input_of_conditional_decoupling μ U A level L cutoff
    truncated tail innerFiber outerFiber harnack innerBound outerMass
    hharnack0 hinner0 houter0 hpairSplit htruncatedFiberCover
    hHarnackConditionalDecoupling hOuterFiberMass hHarnackFactor
    hTruncatedInnerFirstMoment hOuterProfileFirstMoment
    hDiscardedExcursionTail hSourceErrorBudget

end Erdos1166.HLOZAppendixATwoPoint
