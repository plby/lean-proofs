/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfacePhysicalWindows
import ErdosProblems.Erdos1165.TilingAwayNegativeBinomial

/-!
# Local mass comparison for physical deficit-shell windows

The raw deficit label uses truncated natural subtraction.  Consequently its
shell-zero fibre also contains totals at or above `m`.  An accepted rank
creation only uses totals strictly below `m`; the definition below records
that necessary intersection explicitly.

For positive shells the accepted fibres are adjacent intervals of width
`width`.  Shell zero has width `width - 1`: deficit zero corresponds to the
excluded total `m`.  The final comparison therefore retains the exact
cardinality quotient instead of silently claiming that all rows have equal
cardinality.
-/

open scoped BigOperators

namespace Erdos1165.HLOZPositiveInterfacePhysicalWindowRatio

open HLOZPositiveInterfacePhysicalWindows
open NegativeBinomial NegativeBinomialLocalCLT ScreeningInstantiation
open SmallWindow

noncomputable section

/-- The physical shell window restricted to inserted totals for which the
retained count plus inserted count is strictly below level `m`. -/
def acceptedPhysicalDeficitFailureWindow
    (m width i shell : ℕ) : Finset ℕ :=
  physicalDeficitFailureWindow m width i shell ∩ Finset.range (m - i)

@[simp] theorem mem_acceptedPhysicalDeficitFailureWindow
    {m width i shell v : ℕ} :
    v ∈ acceptedPhysicalDeficitFailureWindow m width i shell ↔
      i + v < m ∧ (m - (i + v)) / width = shell := by
  simp only [acceptedPhysicalDeficitFailureWindow, Finset.mem_inter,
    mem_physicalDeficitFailureWindow, Finset.mem_range]
  omega

/-- On the first physical shell, accepted failure counts form the interval
`[m-width+1-i, m-i)`. -/
theorem acceptedPhysicalDeficitFailureWindow_zero_eq_Ico
    {m width i : ℕ} (hwidth : 0 < width) (hwidthm : width ≤ m)
    (hi : i ≤ m - width + 1) :
    acceptedPhysicalDeficitFailureWindow m width i 0 =
      Finset.Ico (m - width + 1 - i) (m - i) := by
  ext v
  simp only [mem_acceptedPhysicalDeficitFailureWindow, Finset.mem_Ico]
  constructor
  · rintro ⟨hlt, hlabel⟩
    have hdlt : m - (i + v) < width := by
      by_contra hnot
      have : 1 ≤ (m - (i + v)) / width :=
        (Nat.le_div_iff_mul_le hwidth).2 (by omega)
      omega
    omega
  · rintro ⟨hlo, hhi⟩
    refine ⟨by omega, ?_⟩
    apply Nat.div_eq_of_lt
    omega

/-- Every strictly positive physical shell is a full interval of the stated
width. -/
theorem acceptedPhysicalDeficitFailureWindow_succ_eq_Ico
    {m width i shell : ℕ} (hwidth : 0 < width)
    (hfit : (shell + 2) * width ≤ m)
    (hi : i ≤ m - (shell + 2) * width + 1) :
    acceptedPhysicalDeficitFailureWindow m width i (shell + 1) =
      Finset.Ico
        (m - (shell + 2) * width + 1 - i)
        (m - (shell + 1) * width + 1 - i) := by
  ext v
  have hstep : (shell + 2) * width =
      (shell + 1) * width + width := by ring
  have hpositive : 0 < (shell + 1) * width :=
    Nat.mul_pos (by omega) hwidth
  simp only [mem_acceptedPhysicalDeficitFailureWindow, Finset.mem_Ico]
  constructor
  · rintro ⟨hlt, hlabel⟩
    have hloDiv : (shell + 1) * width ≤ m - (i + v) := by
      rw [← Nat.le_div_iff_mul_le hwidth, hlabel]
    have hhiDiv : m - (i + v) < (shell + 2) * width := by
      rw [← Nat.div_lt_iff_lt_mul hwidth, hlabel]
      omega
    omega
  · rintro ⟨hlo, hhi⟩
    have hlt : i + v < m := by omega
    have hloDiv : (shell + 1) * width ≤ m - (i + v) := by omega
    have hhiDiv : m - (i + v) < (shell + 2) * width := by omega
    have hqlo : shell + 1 ≤ (m - (i + v)) / width :=
      (Nat.le_div_iff_mul_le hwidth).2 hloDiv
    have hqhi : (m - (i + v)) / width < shell + 2 :=
      (Nat.div_lt_iff_lt_mul hwidth).2 hhiDiv
    exact ⟨hlt, by omega⟩

/-- A balance cutoff which contains the whole accepted physical row does
not alter that row. -/
theorem physical_inter_range_eq_accepted_of_subset
    {m width i shell cut : ℕ}
    (hsubset : acceptedPhysicalDeficitFailureWindow m width i shell ⊆
      Finset.range cut) :
    physicalDeficitFailureWindow m width i shell ∩ Finset.range (m - i) ∩
        Finset.range cut =
      acceptedPhysicalDeficitFailureWindow m width i shell := by
  rw [← acceptedPhysicalDeficitFailureWindow]
  exact Finset.inter_eq_left.mpr hsubset

/-- Exact form used by the accepted stopped-product screen: the base window
both excludes the saturated at/above-level part of the raw physical fibre
and contains the complete below-level shell row. -/
theorem physical_inter_base_eq_accepted
    {m width i shell : ℕ} {base : Finset ℕ}
    (hbaseBelow : base ⊆ Finset.range (m - i))
    (hacceptedBase : acceptedPhysicalDeficitFailureWindow m width i shell ⊆
      base) :
    physicalDeficitFailureWindow m width i shell ∩ base =
      acceptedPhysicalDeficitFailureWindow m width i shell := by
  apply Finset.Subset.antisymm
  · intro v hv
    rw [Finset.mem_inter] at hv
    rw [mem_acceptedPhysicalDeficitFailureWindow]
    have hbelow := Finset.mem_range.mp (hbaseBelow hv.2)
    have hphysical := (mem_physicalDeficitFailureWindow.mp hv.1).2
    exact ⟨by omega, hphysical⟩
  · intro v hv
    rw [Finset.mem_inter]
    exact ⟨(Finset.mem_inter.mp hv).1, hacceptedBase hv⟩

/-- The first accepted physical row has the unavoidable missing deficit-zero
point. -/
theorem acceptedPhysicalDeficitFailureWindow_zero_card
    {m width i : ℕ} (hwidth : 0 < width) (hwidthm : width ≤ m)
    (hi : i ≤ m - width + 1) :
    (acceptedPhysicalDeficitFailureWindow m width i 0).card = width - 1 := by
  rw [acceptedPhysicalDeficitFailureWindow_zero_eq_Ico hwidth hwidthm hi]
  simp only [Nat.card_Ico]
  omega

/-- Every positive accepted physical row has exactly `width` points. -/
theorem acceptedPhysicalDeficitFailureWindow_succ_card
    {m width i shell : ℕ} (hwidth : 0 < width)
    (hfit : (shell + 2) * width ≤ m)
    (hi : i ≤ m - (shell + 2) * width + 1) :
    (acceptedPhysicalDeficitFailureWindow m width i (shell + 1)).card =
      width := by
  rw [acceptedPhysicalDeficitFailureWindow_succ_eq_Ico hwidth hfit hi]
  simp only [Nat.card_Ico]
  have hstep : (shell + 2) * width =
      (shell + 1) * width + width := by ring
  omega

/-- Radius covering two consecutive physical deficit rows once the retained
count is within `centerRadius` of its negative-binomial centre. -/
def physicalAdjacentDeviationRadius
    (width shell : ℕ) (centerRadius : ℝ) : ℝ :=
  centerRadius + (((shell + 2) * width : ℕ) : ℝ)

/-- Consecutive physical rows differ by fewer than two strip widths. -/
def physicalAdjacentWindowSeparation (width : ℕ) : ℝ :=
  2 * (width : ℝ)

lemma physicalAdjacentDeviationRadius_nonneg
    {width shell : ℕ} {centerRadius : ℝ} (hcenterRadius : 0 ≤ centerRadius) :
    0 ≤ physicalAdjacentDeviationRadius width shell centerRadius := by
  unfold physicalAdjacentDeviationRadius
  positivity

lemma physicalAdjacentWindowSeparation_nonneg (width : ℕ) :
    0 ≤ physicalAdjacentWindowSeparation width := by
  unfold physicalAdjacentWindowSeparation
  positivity

/-- Every accepted physical row lies in the corresponding deterministic
deviation radius. -/
theorem acceptedPhysicalFailure_deviation_le
    {m width i shell v : ℕ} {centerRadius : ℝ}
    (hwidth : 0 < width)
    (hcenter : |(m : ℝ) - (16 / 15 : ℝ) * (i : ℝ)| ≤ centerRadius)
    (hv : v ∈ acceptedPhysicalDeficitFailureWindow m width i shell) :
    |deviation i v| ≤
      centerRadius + (((shell + 1) * width : ℕ) : ℝ) := by
  rw [mem_acceptedPhysicalDeficitFailureWindow] at hv
  have hdlt : m - (i + v) < (shell + 1) * width := by
    rw [← Nat.div_lt_iff_lt_mul hwidth, hv.2]
    omega
  have htotal : i + v ≤ m := Nat.le_of_lt hv.1
  have hdltR : (m : ℝ) - ((i : ℝ) + (v : ℝ)) <
      ((shell : ℝ) + 1) * (width : ℝ) := by
    have hcast : ((m - (i + v) : ℕ) : ℝ) <
        (((shell + 1) * width : ℕ) : ℝ) := by exact_mod_cast hdlt
    rw [Nat.cast_sub htotal] at hcast
    push_cast at hcast
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hcast
  have htotalR : (i : ℝ) + (v : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast htotal
  have hdevEq : deviation i v =
      ((i : ℝ) + (v : ℝ)) - (16 / 15 : ℝ) * (i : ℝ) := by
    unfold deviation
    ring
  rw [hdevEq, abs_le]
  rw [abs_le] at hcenter
  push_cast
  constructor <;> linarith

/-- The two consecutive accepted physical rows are separated by at most two
strip widths in deviation coordinates. -/
theorem acceptedPhysicalFailure_deviation_sub_le
    {m width i shell upper lower : ℕ} (hwidth : 0 < width)
    (hupper : upper ∈
      acceptedPhysicalDeficitFailureWindow m width i (shell + 1))
    (hlower : lower ∈
      acceptedPhysicalDeficitFailureWindow m width i shell) :
    |deviation i upper - deviation i lower| ≤
      physicalAdjacentWindowSeparation width := by
  rw [mem_acceptedPhysicalDeficitFailureWindow] at hupper hlower
  have huLo : (shell + 1) * width ≤ m - (i + upper) := by
    rw [← Nat.le_div_iff_mul_le hwidth, hupper.2]
  have huHi : m - (i + upper) < (shell + 2) * width := by
    rw [← Nat.div_lt_iff_lt_mul hwidth, hupper.2]
    omega
  have hlLo : shell * width ≤ m - (i + lower) := by
    rw [← Nat.le_div_iff_mul_le hwidth, hlower.2]
  have hlHi : m - (i + lower) < (shell + 1) * width := by
    rw [← Nat.div_lt_iff_lt_mul hwidth, hlower.2]
    omega
  have hstep : (shell + 2) * width = shell * width + 2 * width := by ring
  have hupperLe : upper ≤ lower := by omega
  have hgap : lower - upper ≤ 2 * width := by omega
  have heq : deviation i upper - deviation i lower =
      (upper : ℝ) - (lower : ℝ) := by
    unfold deviation
    ring
  have hupperLeR : (upper : ℝ) ≤ lower := by exact_mod_cast hupperLe
  have hgapR : (lower : ℝ) - (upper : ℝ) ≤ 2 * (width : ℝ) := by
    have : ((lower - upper : ℕ) : ℝ) ≤ ((2 * width : ℕ) : ℝ) := by
      exact_mod_cast hgap
    rw [Nat.cast_sub hupperLe] at this
    push_cast at this
    exact this
  rw [heq, abs_of_nonpos (sub_nonpos.mpr hupperLeR)]
  unfold physicalAdjacentWindowSeparation
  linarith

/-- A point of shell `shell+1` is to the left of every point of shell
`shell` in failure-count coordinates. -/
theorem acceptedPhysicalFailure_upper_le_lower
    {m width i shell upper lower : ℕ} (hwidth : 0 < width)
    (hupper : upper ∈
      acceptedPhysicalDeficitFailureWindow m width i (shell + 1))
    (hlower : lower ∈
      acceptedPhysicalDeficitFailureWindow m width i shell) :
    upper ≤ lower := by
  rw [mem_acceptedPhysicalDeficitFailureWindow] at hupper hlower
  have huLo : (shell + 1) * width ≤ m - (i + upper) := by
    rw [← Nat.le_div_iff_mul_le hwidth, hupper.2]
  have hlHi : m - (i + lower) < (shell + 1) * width := by
    rw [← Nat.div_lt_iff_lt_mul hwidth, hlower.2]
    omega
  omega

/-- A single endpoint inequality places the entire current physical shell
on the rising side of the HLOZ negative-binomial mass. -/
theorem acceptedPhysicalFailure_below_mode_of_endpoint
    {m width i shell : ℕ}
    (hwidth : 0 < width)
    (hendpoint : 15 * (m - shell * width - i) + 1 ≤ i) :
    ∀ l ∈ acceptedPhysicalDeficitFailureWindow m width i shell,
      15 * l + 1 ≤ i := by
  intro l hl
  rw [mem_acceptedPhysicalDeficitFailureWindow] at hl
  have hdeficit : shell * width ≤ m - (i + l) := by
    rw [← Nat.le_div_iff_mul_le hwidth, hl.2]
  have hlEnd : l ≤ m - shell * width - i := by omega
  omega

/-- The HLOZ negative-binomial mass is increasing between two failure
counts which lie below its mode. -/
theorem hlozMass_mono_of_le_of_below_mode
    {i a b : ℕ} (hi : 0 < i) (hab : a ≤ b) (hmode : 15 * b + 1 ≤ i) :
    hlozMass i a ≤ hlozMass i b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
      exact ih (by omega) |>.trans
        ((hlozMass_le_succ_iff hi b).2 (by omega))

/-- If every point of one finite window has no more mass than every point
of a nonempty comparison window, the exact loss is only the cardinality
quotient. -/
theorem windowMass_le_cardRatio_of_pointwise
    {i : ℕ} (hi : 0 < i) {upper lower : Finset ℕ}
    (hlower : lower.Nonempty)
    (hpointwise : ∀ u ∈ upper, ∀ l ∈ lower, hlozMass i u ≤ hlozMass i l) :
    windowMass i upper ≤
      ((upper.card : ℝ) / (lower.card : ℝ)) * windowMass i lower := by
  obtain ⟨b, hb, hbmin⟩ := Finset.exists_min_image lower (hlozMass i) hlower
  simpa only [one_mul] using
    (windowMass_small_le_ratio_mul_large
      (i := i) (small := upper) (large := lower)
      (b := hlozMass i b) (C := 1)
      (g := (upper.card : ℝ)) (f := (lower.card : ℝ))
      (hlozMass_pos hi b) (by norm_num) (Nat.cast_nonneg _)
      (by exact_mod_cast hlower.card_pos) le_rfl le_rfl
      (fun u hu ↦ by simpa using hpointwise u hu b hb)
      (fun l hl ↦ hbmin l hl))

/-- The exact shell-zero cardinality correction is at most `4/3` once the
strip has width at least four.  All later physical rows have equal
cardinality, so the same constant works uniformly. -/
theorem acceptedPhysicalAdjacent_card_ratio_le_four_thirds
    {m width i shell : ℕ} (hwidth : 4 ≤ width)
    (hfit : (shell + 2) * width ≤ m)
    (hi : i ≤ m - (shell + 2) * width + 1) :
    ((acceptedPhysicalDeficitFailureWindow m width i (shell + 1)).card : ℝ) /
        ((acceptedPhysicalDeficitFailureWindow m width i shell).card : ℝ) ≤
      4 / 3 := by
  have hupperCard := acceptedPhysicalDeficitFailureWindow_succ_card
    (shell := shell) (by omega) hfit hi
  cases shell with
  | zero =>
      have hwidthm : width ≤ m := by omega
      have hi0 : i ≤ m - width + 1 := by omega
      have hlowerCard := acceptedPhysicalDeficitFailureWindow_zero_card
        (by omega) hwidthm hi0
      rw [hupperCard, hlowerCard]
      have hcast : ((width - 1 : ℕ) : ℝ) = (width : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      rw [hcast]
      have hwidthR : (4 : ℝ) ≤ (width : ℝ) := by exact_mod_cast hwidth
      have hden : (0 : ℝ) < (width : ℝ) - 1 := by linarith
      rw [div_le_iff₀ hden]
      norm_num
      linarith
  | succ shell =>
      have hstep : (shell + 1 + 2) * width =
          (shell + 2) * width + width := by ring
      have hfit' : (shell + 2) * width ≤ m := by omega
      have hi' : i ≤ m - (shell + 2) * width + 1 := by omega
      have hlowerCard := acceptedPhysicalDeficitFailureWindow_succ_card
        (shell := shell) (by omega) hfit' hi'
      rw [hupperCard, hlowerCard, div_self]
      · norm_num
      · exact_mod_cast (show width ≠ 0 by omega)

/-- Every accepted physical row has at most one strip width of points,
including when its left endpoint is clipped at failure count zero. -/
theorem acceptedPhysicalDeficitFailureWindow_card_le_width
    {m width i shell : ℕ} (hwidth : 0 < width) :
    (acceptedPhysicalDeficitFailureWindow m width i shell).card ≤ width := by
  let row := acceptedPhysicalDeficitFailureWindow m width i shell
  let deficits := row.image fun v ↦ m - (i + v)
  have hinj : Set.InjOn (fun v : ℕ ↦ m - (i + v)) row := by
    intro a ha b hb hab
    change a ∈ acceptedPhysicalDeficitFailureWindow m width i shell at ha
    change b ∈ acceptedPhysicalDeficitFailureWindow m width i shell at hb
    rw [mem_acceptedPhysicalDeficitFailureWindow] at ha hb
    change m - (i + a) = m - (i + b) at hab
    omega
  have hcard : deficits.card = row.card := by
    exact Finset.card_image_iff.mpr hinj
  have hsubset : deficits ⊆ Finset.Ico (shell * width) ((shell + 1) * width) := by
    intro d hd
    change d ∈ row.image (fun v ↦ m - (i + v)) at hd
    rw [Finset.mem_image] at hd
    rcases hd with ⟨v, hv, rfl⟩
    change v ∈ acceptedPhysicalDeficitFailureWindow m width i shell at hv
    rw [mem_acceptedPhysicalDeficitFailureWindow] at hv
    rw [Finset.mem_Ico]
    constructor
    · exact (Nat.le_div_iff_mul_le hwidth).mp (by rw [hv.2])
    · exact (Nat.div_lt_iff_lt_mul hwidth).mp (by rw [hv.2]; omega)
  calc
    row.card = deficits.card := hcard.symm
    _ ≤ (Finset.Ico (shell * width) ((shell + 1) * width)).card :=
      Finset.card_le_card hsubset
    _ = width := by simp [Nat.add_mul]

/-- The `4/3` cardinality correction does not require either adjacent row
to be a full interval.  If the farther row is nonempty, the nearer row is
full (apart from the single excluded deficit-zero point in shell zero); if
it is empty, the claim is immediate. -/
theorem acceptedPhysicalAdjacent_card_ratio_le_four_thirds_global
    {m width i shell : ℕ} (hwidth : 4 ≤ width) :
    ((acceptedPhysicalDeficitFailureWindow m width i (shell + 1)).card : ℝ) /
        ((acceptedPhysicalDeficitFailureWindow m width i shell).card : ℝ) ≤
      4 / 3 := by
  let upper := acceptedPhysicalDeficitFailureWindow m width i (shell + 1)
  let lower := acceptedPhysicalDeficitFailureWindow m width i shell
  by_cases hupper : upper.Nonempty
  · obtain ⟨u, hu⟩ := hupper
    have hu' := hu
    change u ∈ acceptedPhysicalDeficitFailureWindow m width i (shell + 1) at hu'
    rw [mem_acceptedPhysicalDeficitFailureWindow] at hu'
    have hstrip : (shell + 1) * width ≤ m - (i + u) := by
      rw [← Nat.le_div_iff_mul_le (by omega), hu'.2]
    have hupperCard : upper.card ≤ width := by
      exact acceptedPhysicalDeficitFailureWindow_card_le_width (by omega)
    have hlowerCard : lower.card = if shell = 0 then width - 1 else width := by
      cases shell with
      | zero =>
          simp only [if_pos rfl]
          have hwidthm : width ≤ m := by omega
          have hi0 : i ≤ m - width + 1 := by omega
          exact acceptedPhysicalDeficitFailureWindow_zero_card
            (by omega) hwidthm hi0
      | succ shell =>
          simp only [Nat.succ_ne_zero, if_false]
          have hstrip' : (shell + 2) * width ≤ m - (i + u) := by
            simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hstrip
          have htotal : i + u + (shell + 2) * width ≤ m := by omega
          have hfit : (shell + 2) * width ≤ m := by omega
          have hi : i ≤ m - (shell + 2) * width + 1 := by omega
          exact acceptedPhysicalDeficitFailureWindow_succ_card
            (by omega) hfit hi
    have hlowerPos : 0 < lower.card := by
      rw [hlowerCard]
      split_ifs <;> omega
    rw [div_le_iff₀ (by exact_mod_cast hlowerPos)]
    have hupperCardR : (upper.card : ℝ) ≤ width := by exact_mod_cast hupperCard
    rw [hlowerCard]
    split_ifs
    · have hcast : ((width - 1 : ℕ) : ℝ) = (width : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      rw [hcast]
      norm_num
      have hwidthR : (4 : ℝ) ≤ width := by exact_mod_cast hwidth
      linarith
    · norm_num
      nlinarith [hupperCardR]
  · change (upper.card : ℝ) / (lower.card : ℝ) ≤ 4 / 3
    rw [Finset.not_nonempty_iff_eq_empty.mp hupper]
    norm_num

/-- A nonempty farther-deficit accepted row forces the adjacent nearer row
to be nonempty. -/
theorem acceptedPhysicalDeficitFailureWindow_nonempty_of_succ_nonempty
    {m width i shell : ℕ} (hwidth : 2 ≤ width)
    (hupper : (acceptedPhysicalDeficitFailureWindow m width i (shell + 1)).Nonempty) :
    (acceptedPhysicalDeficitFailureWindow m width i shell).Nonempty := by
  obtain ⟨u, hu⟩ := hupper
  rw [mem_acceptedPhysicalDeficitFailureWindow] at hu
  have hstrip : (shell + 1) * width ≤ m - (i + u) := by
    rw [← Nat.le_div_iff_mul_le (by omega), hu.2]
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  have hcardZero :
      (acceptedPhysicalDeficitFailureWindow m width i shell).card = 0 := by
    rw [hempty]
    simp
  cases shell with
  | zero =>
      have hwidthm : width ≤ m := by omega
      have hi : i ≤ m - width + 1 := by omega
      rw [acceptedPhysicalDeficitFailureWindow_zero_card (by omega) hwidthm hi]
        at hcardZero
      omega
  | succ shell =>
      have hstrip' : (shell + 2) * width ≤ m - (i + u) := by
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hstrip
      have htotal : i + u + (shell + 2) * width ≤ m := by omega
      have hfit : (shell + 2) * width ≤ m := by omega
      have hi : i ≤ m - (shell + 2) * width + 1 := by omega
      rw [acceptedPhysicalDeficitFailureWindow_succ_card (by omega) hfit hi]
        at hcardZero
      omega

/-- Source-correct adjacent-shell comparison valid for clipped physical
rows as well as full rows. -/
theorem acceptedPhysicalAdjacentWindowMass_le_four_thirds_of_below_mode_global
    {m width i shell : ℕ} (hiPos : 0 < i) (hwidth : 4 ≤ width)
    (hmode : ∀ l ∈ acceptedPhysicalDeficitFailureWindow m width i shell,
      15 * l + 1 ≤ i) :
    windowMass i
        (acceptedPhysicalDeficitFailureWindow m width i (shell + 1)) ≤
      (4 / 3 : ℝ) * windowMass i
        (acceptedPhysicalDeficitFailureWindow m width i shell) := by
  let upper := acceptedPhysicalDeficitFailureWindow m width i (shell + 1)
  let lower := acceptedPhysicalDeficitFailureWindow m width i shell
  by_cases hupper : upper.Nonempty
  · have hlower : lower.Nonempty := by
      exact acceptedPhysicalDeficitFailureWindow_nonempty_of_succ_nonempty
        (by omega) hupper
    have hraw : windowMass i upper ≤
        ((upper.card : ℝ) / (lower.card : ℝ)) * windowMass i lower := by
      apply windowMass_le_cardRatio_of_pointwise hiPos hlower
      intro u hu l hl
      apply hlozMass_mono_of_le_of_below_mode hiPos
        (acceptedPhysicalFailure_upper_le_lower (by omega) hu hl)
      exact hmode l hl
    have hcard : (upper.card : ℝ) / (lower.card : ℝ) ≤ 4 / 3 :=
      acceptedPhysicalAdjacent_card_ratio_le_four_thirds_global hwidth
    exact hraw.trans
      (mul_le_mul_of_nonneg_right hcard (windowMass_nonneg i lower))
  · have hempty : upper = ∅ := Finset.not_nonempty_iff_eq_empty.mp hupper
    change windowMass i upper ≤ (4 / 3 : ℝ) * windowMass i lower
    rw [hempty]
    simp only [windowMass, Finset.sum_empty]
    exact mul_nonneg (by norm_num) (windowMass_nonneg i lower)

/-- Endpoint-condition wrapper for the clipped-row comparison. -/
theorem acceptedPhysicalAdjacentWindowMass_le_four_thirds_of_endpoint_global
    {m width i shell : ℕ} (hiPos : 0 < i) (hwidth : 4 ≤ width)
    (hendpoint : 15 * (m - shell * width - i) + 1 ≤ i) :
    windowMass i
        (acceptedPhysicalDeficitFailureWindow m width i (shell + 1)) ≤
      (4 / 3 : ℝ) * windowMass i
        (acceptedPhysicalDeficitFailureWindow m width i shell) := by
  exact acceptedPhysicalAdjacentWindowMass_le_four_thirds_of_below_mode_global
    hiPos hwidth
      (acceptedPhysicalFailure_below_mode_of_endpoint (by omega) hendpoint)

/-- Source-correct physical adjacent-shell comparison.  The balance
hypothesis is exactly that the current row remains on the rising side of the
negative-binomial mass; no mean-centred surrogate window and no large
deviation local-ratio constant is used. -/
theorem acceptedPhysicalAdjacentWindowMass_le_four_thirds_of_below_mode
    {m width i shell : ℕ} (hiPos : 0 < i) (hwidth : 4 ≤ width)
    (hfit : (shell + 2) * width ≤ m)
    (hi : i ≤ m - (shell + 2) * width + 1)
    (hmode : ∀ l ∈ acceptedPhysicalDeficitFailureWindow m width i shell,
      15 * l + 1 ≤ i) :
    windowMass i
        (acceptedPhysicalDeficitFailureWindow m width i (shell + 1)) ≤
      (4 / 3 : ℝ) * windowMass i
        (acceptedPhysicalDeficitFailureWindow m width i shell) := by
  let upper := acceptedPhysicalDeficitFailureWindow m width i (shell + 1)
  let lower := acceptedPhysicalDeficitFailureWindow m width i shell
  have hlower : lower.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hcardZero : lower.card = 0 := by rw [hempty]; simp
    cases shell with
    | zero =>
        have hwidthm : width ≤ m := by omega
        have hi0 : i ≤ m - width + 1 := by omega
        have hcard := acceptedPhysicalDeficitFailureWindow_zero_card
          (m := m) (i := i) (by omega) hwidthm hi0
        change (acceptedPhysicalDeficitFailureWindow m width i 0).card = 0 at hcardZero
        rw [hcard] at hcardZero
        omega
    | succ shell =>
        have hstep : (shell + 1 + 2) * width =
            (shell + 2) * width + width := by ring
        have hfit' : (shell + 2) * width ≤ m := by omega
        have hi' : i ≤ m - (shell + 2) * width + 1 := by omega
        have hcard := acceptedPhysicalDeficitFailureWindow_succ_card
          (m := m) (i := i) (shell := shell) (by omega) hfit' hi'
        change (acceptedPhysicalDeficitFailureWindow m width i
          (shell + 1)).card = 0 at hcardZero
        rw [hcard] at hcardZero
        omega
  have hraw : windowMass i upper ≤
      ((upper.card : ℝ) / (lower.card : ℝ)) * windowMass i lower := by
    apply windowMass_le_cardRatio_of_pointwise hiPos hlower
    intro u hu l hl
    apply hlozMass_mono_of_le_of_below_mode hiPos
      (acceptedPhysicalFailure_upper_le_lower (by omega) hu hl)
      (hmode l hl)
  have hcard : (upper.card : ℝ) / (lower.card : ℝ) ≤ 4 / 3 :=
    acceptedPhysicalAdjacent_card_ratio_le_four_thirds hwidth hfit hi
  exact hraw.trans (mul_le_mul_of_nonneg_right hcard (windowMass_nonneg i lower))

/-- Endpoint-condition wrapper for the source-correct physical comparison. -/
theorem acceptedPhysicalAdjacentWindowMass_le_four_thirds_of_endpoint
    {m width i shell : ℕ} (hiPos : 0 < i) (hwidth : 4 ≤ width)
    (hfit : (shell + 2) * width ≤ m)
    (hi : i ≤ m - (shell + 2) * width + 1)
    (hendpoint : 15 * (m - shell * width - i) + 1 ≤ i) :
    windowMass i
        (acceptedPhysicalDeficitFailureWindow m width i (shell + 1)) ≤
      (4 / 3 : ℝ) * windowMass i
        (acceptedPhysicalDeficitFailureWindow m width i shell) := by
  exact acceptedPhysicalAdjacentWindowMass_le_four_thirds_of_below_mode
    hiPos hwidth hfit hi
      (acceptedPhysicalFailure_below_mode_of_endpoint (by omega) hendpoint)

/-- Under the interior-shell arithmetic, the current accepted row is
nonempty. -/
theorem acceptedPhysicalDeficitFailureWindow_nonempty
    {m width i shell : ℕ} (hwidth : 2 ≤ width)
    (hfit : (shell + 2) * width ≤ m)
    (hi : i ≤ m - (shell + 2) * width + 1) :
    (acceptedPhysicalDeficitFailureWindow m width i shell).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  have hcardZero :
      (acceptedPhysicalDeficitFailureWindow m width i shell).card = 0 := by
    rw [hempty]
    simp
  cases shell with
  | zero =>
      have hwidthm : width ≤ m := by omega
      have hi0 : i ≤ m - width + 1 := by omega
      rw [acceptedPhysicalDeficitFailureWindow_zero_card (by omega)
        hwidthm hi0] at hcardZero
      omega
  | succ shell =>
      have hstep : (shell + 1 + 2) * width =
          (shell + 2) * width + width := by ring
      have hfit' : (shell + 2) * width ≤ m := by omega
      have hi' : i ≤ m - (shell + 2) * width + 1 := by omega
      have hcard := acceptedPhysicalDeficitFailureWindow_succ_card
        (shell := shell) (by omega) hfit' hi'
      rw [hcard] at hcardZero
      omega

/-- A version of the adjacent local-CLT estimate retaining the exact
cardinality quotient.  This is the form needed for the exceptional first
physical shell. -/
theorem adjacentWindowMass_le_adjacentLocalRatio_mul_cardRatio
    {i : ℕ} (hi : 0 < i) {upper lower : Finset ℕ} {D W : ℝ}
    (hD : 0 ≤ D) (hW : 0 ≤ W) (hmoderate : D ≤ (i : ℝ) / 30)
    (hlower : lower.Nonempty)
    (hupperDev : ∀ a ∈ upper, |deviation i a| ≤ D)
    (hlowerDev : ∀ a ∈ lower, |deviation i a| ≤ D)
    (hpair : ∀ a ∈ upper, ∀ b ∈ lower,
      |deviation i a - deviation i b| ≤ W) :
    windowMass i upper ≤
      (adjacentLocalRatio i D W * (upper.card : ℝ) /
        (lower.card : ℝ)) * windowMass i lower := by
  obtain ⟨b, hb, hbmin⟩ := Finset.exists_min_image lower (hlozMass i) hlower
  exact windowMass_small_le_ratio_mul_large
    (i := i) (small := upper) (large := lower)
    (b := hlozMass i b) (C := adjacentLocalRatio i D W)
    (g := (upper.card : ℝ)) (f := (lower.card : ℝ))
    (hlozMass_pos hi b) (adjacentLocalRatio_nonneg i D W)
    (Nat.cast_nonneg _) (by exact_mod_cast hlower.card_pos)
    le_rfl le_rfl
    (fun a ha ↦ hlozMass_le_adjacentLocalRatio_mul hi hD hW
      (hupperDev a ha) (hlowerDev b hb) (hpair a ha b hb) hmoderate)
    (fun a ha ↦ hbmin a ha)

/-- The checked local CLT for two consecutive accepted physical deficit
rows.  The explicit coefficient hypothesis includes the exceptional
`width/(width-1)` cardinality quotient of the shell-zero transition. -/
theorem acceptedPhysicalAdjacentWindowMass_le_four_thirds
    {m width i shell : ℕ} {centerRadius : ℝ}
    (hiPos : 0 < i) (hwidth : 2 ≤ width)
    (hfit : (shell + 2) * width ≤ m)
    (hi : i ≤ m - (shell + 2) * width + 1)
    (hcenterRadius : 0 ≤ centerRadius)
    (hcenter : |(m : ℝ) - (16 / 15 : ℝ) * (i : ℝ)| ≤ centerRadius)
    (hmoderate : physicalAdjacentDeviationRadius width shell centerRadius ≤
      (i : ℝ) / 30)
    (hcoefficient :
      adjacentLocalRatio i
          (physicalAdjacentDeviationRadius width shell centerRadius)
          (physicalAdjacentWindowSeparation width) *
          ((acceptedPhysicalDeficitFailureWindow m width i
            (shell + 1)).card : ℝ) /
          ((acceptedPhysicalDeficitFailureWindow m width i shell).card : ℝ) ≤
        4 / 3) :
    windowMass i
        (acceptedPhysicalDeficitFailureWindow m width i (shell + 1)) ≤
      (4 / 3 : ℝ) * windowMass i
        (acceptedPhysicalDeficitFailureWindow m width i shell) := by
  let D := physicalAdjacentDeviationRadius width shell centerRadius
  let W := physicalAdjacentWindowSeparation width
  let upper := acceptedPhysicalDeficitFailureWindow m width i (shell + 1)
  let lower := acceptedPhysicalDeficitFailureWindow m width i shell
  have hlower : lower.Nonempty :=
    acceptedPhysicalDeficitFailureWindow_nonempty hwidth hfit hi
  have hraw : windowMass i upper ≤
      (adjacentLocalRatio i D W * (upper.card : ℝ) /
        (lower.card : ℝ)) * windowMass i lower := by
    apply adjacentWindowMass_le_adjacentLocalRatio_mul_cardRatio hiPos
      (physicalAdjacentDeviationRadius_nonneg hcenterRadius)
      (physicalAdjacentWindowSeparation_nonneg width) hmoderate hlower
    · intro v hv
      have hdev := acceptedPhysicalFailure_deviation_le (by omega) hcenter hv
      simpa only [D, physicalAdjacentDeviationRadius, Nat.add_assoc] using hdev
    · intro v hv
      have hdev := acceptedPhysicalFailure_deviation_le (by omega) hcenter hv
      apply hdev.trans
      dsimp only [D, physicalAdjacentDeviationRadius]
      gcongr
      omega
    · intro u hu l hl
      exact acceptedPhysicalFailure_deviation_sub_le (by omega) hu hl
  have hmass : 0 ≤ windowMass i lower := windowMass_nonneg i lower
  exact hraw.trans (mul_le_mul_of_nonneg_right hcoefficient hmass)

end

end Erdos1165.HLOZPositiveInterfacePhysicalWindowRatio
