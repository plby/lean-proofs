/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma54ThresholdNumerics
import ErdosProblems.Erdos547b.Section6EventualParameters

/-!
# Rounded source budgets for Zhao Lemma 5.4(1)/(2)

This file is deliberately graph-free.  It converts the real source-density
budgets in Zhao Lemma 5.4 to the natural budgets used by the dynamic regular
pair constructor, and proves the suffix estimate at the *actual* maximal
fitting cutoff.

The record `ClassifiedThresholdOwnerNumerics` is the exact remaining
source/numeric interface.  With `ratio = 0` it is the Part-1 row; with the
branch-ratio cutoff as `ratio` it is the Part-2 row.  Its `mass_display` is
the normalized form of display (5.2), while `class_upper` is precisely the
branch classification used to bound either forced suffix colour class.  No
host residual cardinality, embedding, copy, or continuation occurs here.
-/

open scoped BigOperators

noncomputable section

namespace Erdos547b.ZhaoLemma54ThresholdSourceNumerics

open Finset Fintype
open Erdos547b.RegularPair
open Erdos547b.ForestMatching
open Erdos547b.ZhaoRoundedScales
open Erdos547b.ZhaoSection6EventualParameters
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma54ThresholdOrientation
open Erdos547b.ZhaoLemma54ThresholdNumerics

/-! ## Canonical rounded budgets -/

/-- Downward-rounded low-endpoint occupancy budget. -/
def thresholdLowBudget (dx gamma N : ℝ) : ℕ :=
  lowerScale ((dx - gamma) * N)

/-- Downward-rounded high-endpoint occupancy budget. -/
def thresholdHighBudget (dy gamma N : ℝ) : ℕ :=
  lowerScale ((dy - gamma) * N)

/-- Upward-rounded regularity reserve for a raw set of the given order. -/
def thresholdReserve (rho : ℝ) (wholeCard : ℕ) : ℕ :=
  upperScale (rho * wholeCard)

theorem thresholdLowBudget_cast_le
    {dx gamma N : ℝ} (h : 0 ≤ (dx - gamma) * N) :
    (thresholdLowBudget dx gamma N : ℝ) ≤ (dx - gamma) * N := by
  exact lowerScale_cast_le h

/-- If the formal low-density target is nonpositive, its natural budget is
literally zero.  This is the source-faithful unbalanced case in which the
maximal fitting cutoff may be empty. -/
theorem thresholdLowBudget_eq_zero_of_nonpos
    {dx gamma N : ℝ} (h : (dx - gamma) * N ≤ 0) :
    thresholdLowBudget dx gamma N = 0 := by
  unfold thresholdLowBudget lowerScale
  exact Nat.floor_eq_zero.mpr (h.trans_lt (by norm_num))

theorem thresholdLowTarget_lt_budget_add_one (dx gamma N : ℝ) :
    (dx - gamma) * N < (thresholdLowBudget dx gamma N : ℝ) + 1 := by
  exact lt_lowerScale_cast_add_one _

theorem thresholdHighBudget_cast_le
    {dy gamma N : ℝ} (h : 0 ≤ (dy - gamma) * N) :
    (thresholdHighBudget dy gamma N : ℝ) ≤ (dy - gamma) * N := by
  exact lowerScale_cast_le h

theorem thresholdHighTarget_lt_budget_add_one (dy gamma N : ℝ) :
    (dy - gamma) * N < (thresholdHighBudget dy gamma N : ℝ) + 1 := by
  exact lt_lowerScale_cast_add_one _

theorem thresholdReserve_covers (rho : ℝ) (wholeCard : ℕ) :
    rho * wholeCard ≤ (thresholdReserve rho wholeCard : ℝ) := by
  exact le_upperScale_cast _

theorem thresholdReserve_lt_target_add_one
    {rho : ℝ} (hrho : 0 ≤ rho) (wholeCard : ℕ) :
    (thresholdReserve rho wholeCard : ℝ) < rho * wholeCard + 1 := by
  apply upperScale_cast_lt_add_one
  positivity

theorem thresholdLowBudget_le_thresholdHighBudget
    {dx dy gamma N : ℝ} (hxy : dx ≤ dy) (hN : 0 ≤ N) :
    thresholdLowBudget dx gamma N ≤ thresholdHighBudget dy gamma N := by
  exact Nat.floor_mono (mul_le_mul_of_nonneg_right (sub_le_sub_right hxy gamma) hN)

/-! The Section-6 specialization fixes `gamma` and `rho` rather than asking
downstream users to repeat those parameter choices. -/

def eventualThresholdLowBudget (β : ℚ) (dx : ℝ) (N : ℕ) : ℕ :=
  thresholdLowBudget dx (embeddingGamma β : ℝ) N

def eventualThresholdHighBudget (β : ℚ) (dy : ℝ) (N : ℕ) : ℕ :=
  thresholdHighBudget dy (embeddingGamma β : ℝ) N

def eventualThresholdReserve (β : ℚ) (wholeCard : ℕ) : ℕ :=
  thresholdReserve (regularityEpsilon β : ℝ) wholeCard

theorem eventualThresholdLowBudget_cast_le
    {β : ℚ} {dx : ℝ} {N : ℕ}
    (h : 0 ≤ (dx - (embeddingGamma β : ℝ)) * N) :
    (eventualThresholdLowBudget β dx N : ℝ) ≤
      (dx - (embeddingGamma β : ℝ)) * N := by
  exact thresholdLowBudget_cast_le h

theorem eventualThresholdHighBudget_cast_le
    {β : ℚ} {dy : ℝ} {N : ℕ}
    (h : 0 ≤ (dy - (embeddingGamma β : ℝ)) * N) :
    (eventualThresholdHighBudget β dy N : ℝ) ≤
      (dy - (embeddingGamma β : ℝ)) * N := by
  exact thresholdHighBudget_cast_le h

theorem eventualThresholdReserve_covers (β : ℚ) (wholeCard : ℕ) :
    (regularityEpsilon β : ℝ) * wholeCard ≤
      (eventualThresholdReserve β wholeCard : ℝ) := by
  exact thresholdReserve_covers _ _

/-! ## Source suffix arithmetic -/

/-- Total order of the branches at or after a cutoff. -/
def suffixOrder {b : ℕ} (F : OrderedRootedForest b)
    (cutoff : Fin (b + 1)) : ℕ :=
  ∑ i, if cutoff.val ≤ i.val then F.size i else 0

theorem prefixOrder_add_suffixOrder {b : ℕ}
    (F : OrderedRootedForest b) (cutoff : Fin (b + 1)) :
    prefixOrder F cutoff + suffixOrder F cutoff = F.order := by
  classical
  rw [prefixOrder, suffixOrder, OrderedRootedForest.order,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < cutoff.val
  · simp [hi, Nat.not_le.mpr hi]
  · simp [hi, Nat.le_of_not_gt hi]

/-- Adding the unique next branch increases a prefix by at most the branch
size bound.  This is the finite step used when maximality produces the first
non-fitting prefix. -/
theorem prefixOrder_next_le_add_slack {b : ℕ}
    (F : OrderedRootedForest b) (slack : ℕ)
    (hsmall : ∀ i, F.size i ≤ slack)
    {cutoff next : Fin (b + 1)}
    (hnext : next.val = cutoff.val + 1) :
    prefixOrder F next ≤ prefixOrder F cutoff + slack := by
  classical
  have hcut : cutoff.val < b := by omega
  let j : Fin b := ⟨cutoff.val, hcut⟩
  have hfilter :
      Finset.univ.filter (fun i : Fin b ↦ i.val < next.val) =
        insert j (Finset.univ.filter (fun i : Fin b ↦ i.val < cutoff.val)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    constructor
    · intro hi
      by_cases hic : i.val < cutoff.val
      · exact Or.inr hic
      · left
        apply Fin.ext
        simp only [j]
        omega
    · intro hi
      rcases hi with rfl | hi
      · simp only [j, hnext]
        omega
      · omega
  rw [prefixOrder, prefixOrder, ← Finset.sum_filter, ← Finset.sum_filter,
    hfilter, Finset.sum_insert]
  · calc
      F.size j + ∑ x with x.val < cutoff.val, F.size x ≤
          slack + ∑ x with x.val < cutoff.val, F.size x :=
        Nat.add_le_add_right (hsmall j) _
      _ = ∑ x with x.val < cutoff.val, F.size x + slack := Nat.add_comm _ _
  · simp [j]

/-- The exact source/numeric input shared by Parts 1 and 2.  The Part-1
specialization takes `ratio = 0`.  The Part-2 specialization takes Zhao's
classified ratio cutoff.  The rounding margin is exactly the two floor
units charged to the published `3 * epsilon * N` reserve. -/
structure ClassifiedThresholdOwnerNumerics {b : ℕ}
    (F : OrderedRootedForest b)
    (ratio dx dy gamma epsilon N : ℝ) (slack : ℕ) : Prop where
  ratio_nonneg : 0 ≤ ratio
  ratio_le_half : ratio ≤ 1 / 2
  ratio_lt_one : ratio < 1
  low_le_high : dx ≤ dy
  N_nonneg : 0 ≤ N
  high_target_nonneg : 0 ≤ (dy - gamma) * N
  epsilon_nonneg : 0 ≤ epsilon
  small : ∀ i, F.size i ≤ slack
  /-- Either canonical colour class can be the forced suffix class. -/
  class_upper : ∀ i c,
    (#(colourClass F i c) : ℝ) ≤ (1 - ratio) * F.size i
  /-- Display (5.2), normalized around the low budget and the density gap. -/
  mass_display : (F.order : ℝ) ≤
    2 * ((dx - gamma) * N) - 3 * (epsilon * N) +
      ((dy - dx) * N) / (1 - ratio)
  /-- The published `3 epsilon N` absorbs two floor units and three integral
  branch-slack units. -/
  rounding_margin : (2 : ℝ) + 3 * slack ≤ 3 * (epsilon * N)

namespace ClassifiedThresholdOwnerNumerics

/-- Zhao Lemma 5.4(1) is the `ratio = 0` specialization of the common
threshold record.  Its aggregate capacity display is exactly the normalized
mass bound after elementary algebra. -/
theorem of_partOneMass {b : ℕ} (F : OrderedRootedForest b)
    (dx dy gamma epsilon N : ℝ) (slack : ℕ)
    (hlowHigh : dx ≤ dy)
    (hN : 0 ≤ N)
    (hhigh : 0 ≤ (dy - gamma) * N)
    (hepsilon : 0 ≤ epsilon)
    (hsmall : ∀ i, F.size i ≤ slack)
    (hmass : (F.order : ℝ) ≤
      (dx + dy - 2 * gamma - 3 * epsilon) * N)
    (hround : (2 : ℝ) + 3 * slack ≤ 3 * (epsilon * N)) :
    ClassifiedThresholdOwnerNumerics
      F 0 dx dy gamma epsilon N slack := by
  refine {
    ratio_nonneg := by norm_num
    ratio_le_half := by norm_num
    ratio_lt_one := by norm_num
    low_le_high := hlowHigh
    N_nonneg := hN
    high_target_nonneg := hhigh
    epsilon_nonneg := hepsilon
    small := hsmall
    class_upper := ?_
    mass_display := ?_
    rounding_margin := hround
  }
  · intro i c
    have hcard : #(colourClass F i c) ≤ F.size i := by
      calc
        #(colourClass F i c) ≤
            #(Finset.univ : Finset (Fin (F.size i))) := by
          apply Finset.card_le_card
          exact Finset.filter_subset _ _
        _ = F.size i := by simp
    norm_num
    exact_mod_cast hcard
  · norm_num
    nlinarith [hmass]

/-- The existing Lemma-5.4(2) classification on the whole owner group gives
the two-sided class bound and the normalized source display.  Thus the only
additional inputs here are eventual-parameter scale facts (nonnegativity,
smallness, and the explicit two-unit rounding charge), not a new density or
embedding hypothesis. -/
theorem of_partTwoLocalData {b : ℕ} (F : OrderedRootedForest b)
    (ratio dx dy gamma epsilon N : ℝ) (slack : ℕ)
    (P : PartTwoLocalData F Finset.univ ratio dx dy gamma epsilon N)
    (hN : 0 ≤ N)
    (hhigh : 0 ≤ (dy - gamma) * N)
    (hepsilon : 0 ≤ epsilon)
    (hsmall : ∀ i, F.size i ≤ slack)
    (hround : (2 : ℝ) + 3 * slack ≤ 3 * (epsilon * N)) :
    ClassifiedThresholdOwnerNumerics
      F ratio dx dy gamma epsilon N slack := by
  have hratioOne : ratio < 1 :=
    lt_of_le_of_lt P.c_le_half (by norm_num)
  refine {
    ratio_nonneg := P.c_nonneg
    ratio_le_half := P.c_le_half
    ratio_lt_one := hratioOne
    low_le_high := P.low_le_high
    N_nonneg := hN
    high_target_nonneg := hhigh
    epsilon_nonneg := hepsilon
    small := hsmall
    class_upper := ?_
    mass_display := ?_
    rounding_margin := hround
  }
  · intro i side
    have hsizeNat : 0 < F.size i := Nat.zero_lt_of_lt (F.root i).isLt
    have hsize : (0 : ℝ) < F.size i := by exact_mod_cast hsizeNat
    have hsumNat := orientedClassSize_zero_add_one F
      (fun _ ↦ Equiv.refl (Fin 2)) i
    simp only [orientedClassSize_refl] at hsumNat
    have hsum :
        (#(colourClass F i 0) : ℝ) + #(colourClass F i 1) = F.size i := by
      exact_mod_cast hsumNat
    rcases OrderedRootedForest.fin_two_eq_zero_or_one side with rfl | rfl
    · exact (div_le_iff₀ hsize).mp (P.ratio_upper i (Finset.mem_univ i))
    · have hlower := P.ratio_lower i (Finset.mem_univ i)
      have hlowerMul :
          ratio * (F.size i : ℝ) ≤ #(colourClass F i 0) := by
        exact (le_div_iff₀ hsize).mp hlower
      nlinarith
  · have hden : 1 - ratio ≠ 0 := (sub_pos.mpr hratioOne).ne'
    have hnormalize :
        (dx + dy - 2 * gamma - 3 * epsilon) * N +
            ratio / (1 - ratio) * (dy - dx) * N =
          2 * ((dx - gamma) * N) - 3 * (epsilon * N) +
            ((dy - dx) * N) / (1 - ratio) := by
      field_simp [hden] <;> ring
    have hmass := P.mass_le
    have horder : ∑ i ∈ (Finset.univ : Finset (Fin b)), F.size i = F.order := by
      simp [OrderedRootedForest.order]
    rw [horder, hnormalize] at hmass
    exact hmass

theorem lowBudget_le_highBudget {b : ℕ} {F : OrderedRootedForest b}
    {ratio dx dy gamma epsilon N : ℝ} {slack : ℕ}
    (D : ClassifiedThresholdOwnerNumerics
      F ratio dx dy gamma epsilon N slack) :
    thresholdLowBudget dx gamma N ≤ thresholdHighBudget dy gamma N :=
  thresholdLowBudget_le_thresholdHighBudget D.low_le_high D.N_nonneg

theorem fixedSuffixLoad_cast_le {b : ℕ} {F : OrderedRootedForest b}
    {ratio dx dy gamma epsilon N : ℝ} {slack : ℕ}
    (D : ClassifiedThresholdOwnerNumerics
      F ratio dx dy gamma epsilon N slack)
    (cutoff : Fin (b + 1)) (highSide c : Fin 2) :
    (fixedSuffixLoad F cutoff highSide c : ℝ) ≤
      (1 - ratio) * suffixOrder F cutoff := by
  classical
  have horient (i : Fin b) :
      orientedClassSize F (fun _ ↦ rootToSide highSide) i c =
        #(colourClass F i ((rootToSide highSide).symm c)) := by
    unfold orientedClassSize colourClass
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (rootToSide highSide).apply_eq_iff_eq_symm_apply
  rw [fixedSuffixLoad, suffixOrder, Nat.cast_sum]
  simp_rw [Nat.cast_ite, Nat.cast_zero]
  calc
    ∑ i, (if cutoff.val ≤ i.val then
          (orientedClassSize F (fun _ ↦ rootToSide highSide) i c : ℝ)
        else 0) ≤
        ∑ i, (if cutoff.val ≤ i.val then
          (1 - ratio) * (F.size i : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : cutoff.val ≤ i.val
      · simp only [hi, if_true, horient]
        exact D.class_upper i _
      · simp [hi]
    _ = (1 - ratio) *
        ∑ i, (if cutoff.val ≤ i.val then (F.size i : ℝ) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : cutoff.val ≤ i.val <;> simp [hi]
    _ = (1 - ratio) *
        ((∑ i, if cutoff.val ≤ i.val then F.size i else 0 : ℕ) : ℝ) := by
      congr 1
      rw [Nat.cast_sum]
      simp_rw [Nat.cast_ite, Nat.cast_zero]

/-- The real display with the two rounding units charged to the epsilon
margin, now expressed using the literal downward-rounded low budget. -/
theorem mass_le_rounded_low_display {b : ℕ}
    {F : OrderedRootedForest b}
    {ratio dx dy gamma epsilon N : ℝ} {slack : ℕ}
    (D : ClassifiedThresholdOwnerNumerics
      F ratio dx dy gamma epsilon N slack) :
    (F.order : ℝ) ≤
      2 * (thresholdLowBudget dx gamma N : ℝ) - 3 * slack +
        ((dy - dx) * N) / (1 - ratio) := by
  have hround := thresholdLowTarget_lt_budget_add_one dx gamma N
  nlinarith [D.mass_display, D.rounding_margin]

/-- The source-faithful suffix display at Zhao's actual maximal fitting
cutoff.  This is exactly the graph-free field required by
`ActualThresholdStepData`; all live-set cardinality obligations remain in
the host specialization. -/
theorem suffix_display {b : ℕ} {F : OrderedRootedForest b}
    {ratio dx dy gamma epsilon N : ℝ} {slack : ℕ}
    (D : ClassifiedThresholdOwnerNumerics
      F ratio dx dy gamma epsilon N slack) (highSide : Fin 2) :
    ∀ (base : Fin b → Fin 2 ≃ Fin 2),
      (∀ t c, 2 * sideLoadPrefix F base t c ≤ prefixOrder F t + slack) →
      ∀ c,
        thresholdLowBudget dx gamma N + fixedSuffixLoad F
            (maximalFittingCutoff F base
              (thresholdLowBudget dx gamma N)) highSide c ≤
          thresholdHighBudget dy gamma N := by
  intro base hbase c
  let low := thresholdLowBudget dx gamma N
  let high := thresholdHighBudget dy gamma N
  let cutoff := maximalFittingCutoff F base low
  change low + fixedSuffixLoad F cutoff highSide c ≤ high
  have hlowHigh : low ≤ high := D.lowBudget_le_highBudget
  rcases maximalFittingCutoff_eq_last_or_next_overflow F base low with
      hlast | ⟨next, side, hnext, hover⟩
  · have hcutoff : cutoff = Fin.last b := by simpa [cutoff, low] using hlast
    simp only [hcutoff, fixedSuffixLoad_last, Nat.add_zero]
    exact hlowHigh
  · have hnextGrowth :
        prefixOrder F next ≤ prefixOrder F cutoff + slack := by
      apply prefixOrder_next_le_add_slack F slack D.small
      simpa [cutoff, low] using hnext
    have hoverNat : low + 1 ≤ sideLoadPrefix F base next side := by omega
    have hbalanced := hbase next side
    have hmaximalNat : 2 * low + 2 ≤ prefixOrder F cutoff + 2 * slack := by
      omega
    have hmaximal :
        2 * (low : ℝ) < (prefixOrder F cutoff : ℝ) + 2 * slack := by
      exact_mod_cast (Nat.lt_of_lt_of_le (by omega : 2 * low < 2 * low + 2)
        hmaximalNat)
    have hsuffixFraction :
        (fixedSuffixLoad F cutoff highSide c : ℝ) ≤
          (1 - ratio) *
            ((F.order : ℝ) - (prefixOrder F cutoff : ℝ)) := by
      have hsource := D.fixedSuffixLoad_cast_le cutoff highSide c
      have hpartition := prefixOrder_add_suffixOrder F cutoff
      have hpartitionReal :
          (prefixOrder F cutoff : ℝ) + (suffixOrder F cutoff : ℝ) =
            (F.order : ℝ) := by exact_mod_cast hpartition
      rw [show (suffixOrder F cutoff : ℝ) =
        (F.order : ℝ) - (prefixOrder F cutoff : ℝ) by linarith] at hsource
      exact hsource
    have hgap : 0 ≤ (dy - dx) * N :=
      mul_nonneg (sub_nonneg.mpr D.low_le_high) D.N_nonneg
    have hsuffixGap :
        (fixedSuffixLoad F cutoff highSide c : ℝ) ≤ (dy - dx) * N := by
      apply partTwo_threshold_suffix_load_le_gap ratio (F.order : ℝ)
        (prefixOrder F cutoff : ℝ) (low : ℝ) ((dy - dx) * N)
        (slack : ℝ) (fixedSuffixLoad F cutoff highSide c : ℝ)
      · exact D.ratio_nonneg
      · exact D.ratio_lt_one
      · exact hgap
      · positivity
      · simpa only [low] using D.mass_le_rounded_low_display
      · exact hmaximal
      · exact hsuffixFraction
    by_cases hlowTarget : 0 ≤ (dx - gamma) * N
    · have hlowCast : (low : ℝ) ≤ (dx - gamma) * N := by
        simpa only [low] using thresholdLowBudget_cast_le hlowTarget
      have hsum :
          ((low + fixedSuffixLoad F cutoff highSide c : ℕ) : ℝ) ≤
            (dy - gamma) * N := by
        norm_num only [Nat.cast_add]
        nlinarith
      change low + fixedSuffixLoad F cutoff highSide c ≤
        lowerScale ((dy - gamma) * N)
      exact Nat.le_floor hsum
    · have htargetNonpos : (dx - gamma) * N ≤ 0 :=
        le_of_not_ge hlowTarget
      have hlowZero : low = 0 := by
        simpa only [low] using
          thresholdLowBudget_eq_zero_of_nonpos htargetNonpos
      have hratioFactor : 0 ≤ 1 - ratio :=
        (sub_pos.mpr D.ratio_lt_one).le
      have hsuffixOrderLe : suffixOrder F cutoff ≤ F.order := by
        have hpartition := prefixOrder_add_suffixOrder F cutoff
        omega
      have hsuffixFull :
          (fixedSuffixLoad F cutoff highSide c : ℝ) ≤
            (1 - ratio) * F.order := by
        exact (D.fixedSuffixLoad_cast_le cutoff highSide c).trans
          (mul_le_mul_of_nonneg_left (by exact_mod_cast hsuffixOrderLe)
            hratioFactor)
      have hden : 1 - ratio ≠ 0 := (sub_pos.mpr D.ratio_lt_one).ne'
      have hscaledDisplay :
          (1 - ratio) * (F.order : ℝ) ≤
            2 * (1 - ratio) * ((dx - gamma) * N) -
              3 * (1 - ratio) * (epsilon * N) + (dy - dx) * N := by
        have hmul := mul_le_mul_of_nonneg_left D.mass_display hratioFactor
        calc
          (1 - ratio) * (F.order : ℝ) ≤
              (1 - ratio) *
                (2 * ((dx - gamma) * N) - 3 * (epsilon * N) +
                  ((dy - dx) * N) / (1 - ratio)) := hmul
          _ = 2 * (1 - ratio) * ((dx - gamma) * N) -
                3 * (1 - ratio) * (epsilon * N) + (dy - dx) * N := by
            field_simp [hden]
      have hepsilonN : 0 ≤ epsilon * N :=
        mul_nonneg D.epsilon_nonneg D.N_nonneg
      have hhalf : 0 ≤ 1 - 2 * ratio := by
        linarith [D.ratio_le_half]
      have hupper :
          (fixedSuffixLoad F cutoff highSide c : ℝ) ≤
            (dy - gamma) * N := by
        have hnonpos := mul_nonpos_of_nonneg_of_nonpos hhalf htargetNonpos
        have hepsLoss := mul_nonneg hratioFactor hepsilonN
        nlinarith [hsuffixFull.trans hscaledDisplay]
      rw [hlowZero, Nat.zero_add]
      change fixedSuffixLoad F cutoff highSide c ≤
        lowerScale ((dy - gamma) * N)
      exact Nat.le_floor hupper

end ClassifiedThresholdOwnerNumerics

#print axioms thresholdLowBudget_cast_le
#print axioms ClassifiedThresholdOwnerNumerics.of_partOneMass
#print axioms ClassifiedThresholdOwnerNumerics.suffix_display

end Erdos547b.ZhaoLemma54ThresholdSourceNumerics
