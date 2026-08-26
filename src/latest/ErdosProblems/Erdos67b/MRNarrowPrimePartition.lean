import ErdosProblems.Erdos67b.MRScheduledFrequencyClass
import ErdosProblems.Erdos67b.MRCombinedBoundary

/-!
# Actual narrow prime subblocks and their integer endpoints

Primes are partitioned by their logarithmic floor label. Rounded
enclosing intervals are used only for cofactor supports, so endpoint
overlap of those intervals cannot invalidate the prime partition.
-/

open scoped BigOperators Interval
open Finset MeasureTheory

namespace Erdos67b

noncomputable section

def mrLogPrimeInterval (p q : ℝ) : ℕ × ℕ :=
  (Nat.ceil (Real.exp p), Nat.floor (Real.exp q))

def mrPrimeSubblock (H : ℝ) (P : Finset ℕ) (r : ℕ) : Finset ℕ := by
  classical
  exact P.filter (fun p ↦ Nat.floor (H * Real.log p) = r)

def mrNarrowPrimeInterval (H : ℝ) (r : ℕ) : ℕ × ℕ :=
  (Nat.ceil (Real.exp ((r : ℝ) / H)), Nat.floor (Real.exp (((r + 1 : ℕ) : ℝ) / H)))

theorem mem_primesInBlock_mrLogPrimeInterval_bounds
    {p q : ℝ} {l : ℕ} (hl : l ∈ primesInBlock (mrLogPrimeInterval p q)) :
    p ≤ Real.log l ∧ Real.log l ≤ q := by
  have hdata := mem_primesInBlock.mp hl
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hdata.1.pos
  have hlo : Real.exp p ≤ l := (Nat.le_ceil _).trans (by exact_mod_cast hdata.2.1)
  have hhi : (l : ℝ) ≤ Real.exp q :=
    (show (l : ℝ) ≤ Nat.floor (Real.exp q) by exact_mod_cast hdata.2.2).trans
      (Nat.floor_le (Real.exp_pos _).le)
  constructor
  · have hh := Real.log_le_log (Real.exp_pos p) hlo
    simpa only [Real.log_exp] using hh
  · have hh := Real.log_le_log hl0 hhi
    simpa only [Real.log_exp] using hh

theorem mrPrimeSubblock_subset (H : ℝ) (P : Finset ℕ) (r : ℕ) :
    mrPrimeSubblock H P r ⊆ P := by
  classical
  exact Finset.filter_subset _ _

theorem mrPrimeSubblock_pairwiseDisjoint (H : ℝ) (P : Finset ℕ) (V : Finset ℕ) :
    Set.PairwiseDisjoint (↑V) (mrPrimeSubblock H P) := by
  classical
  intro r _ s _ hrs
  apply Finset.disjoint_left.mpr
  intro l hlr hls
  have hr := (Finset.mem_filter.mp hlr).2
  have hs := (Finset.mem_filter.mp hls).2
  exact hrs (hr.symm.trans hs)

theorem mrPrimeSubblock_biUnion_eq
    {H p q : ℝ} (hH : 0 ≤ H) (P : Finset ℕ)
    (hP : ∀ l ∈ P, p ≤ Real.log l ∧ Real.log l ≤ q) :
    (mrLogBlockIndices H p q).biUnion (mrPrimeSubblock H P) = P := by
  classical
  apply Finset.Subset.antisymm
  · intro l hl
    obtain ⟨r, hr, hlr⟩ := Finset.mem_biUnion.mp hl
    exact mrPrimeSubblock_subset H P r hlr
  · intro l hl
    apply Finset.mem_biUnion.mpr
    refine ⟨Nat.floor (H * Real.log l), ?_, ?_⟩
    · apply Finset.mem_Icc.mpr
      exact ⟨Nat.floor_le_floor (mul_le_mul_of_nonneg_left (hP l hl).1 hH),
        Nat.floor_le_floor (mul_le_mul_of_nonneg_left (hP l hl).2 hH)⟩
    · exact Finset.mem_filter.mpr ⟨hl, rfl⟩

theorem mrPrimeSubblock_real_bounds
    {H : ℝ} (hH : 0 < H) {P : Finset ℕ} (hP : ∀ l ∈ P, l.Prime)
    {r l : ℕ} (hl : l ∈ mrPrimeSubblock H P r) :
    Real.exp ((r : ℝ) / H) ≤ l ∧ (l : ℝ) ≤ Real.exp (((r + 1 : ℕ) : ℝ) / H) := by
  obtain ⟨hlP, hr⟩ := Finset.mem_filter.mp hl
  have hlprime := hP l hlP
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hlprime.pos
  have hlog0 : 0 ≤ Real.log (l : ℝ) := Real.log_nonneg (by exact_mod_cast hlprime.one_lt.le)
  have hlo := Nat.floor_le (mul_nonneg hH.le hlog0)
  have hhi := Nat.lt_floor_add_one (H * Real.log (l : ℝ))
  rw [hr] at hlo hhi
  constructor
  · calc
      Real.exp ((r : ℝ) / H) ≤ Real.exp (Real.log l) :=
        Real.exp_le_exp.mpr ((div_le_iff₀ hH).mpr (by nlinarith))
      _ = l := Real.exp_log hl0
  · calc
      (l : ℝ) = Real.exp (Real.log l) := (Real.exp_log hl0).symm
      _ ≤ Real.exp (((r + 1 : ℕ) : ℝ) / H) := by
        apply Real.exp_le_exp.mpr
        apply (le_div_iff₀ hH).mpr
        push_cast
        nlinarith

theorem mrPrimeSubblock_integer_bounds
    {H : ℝ} (hH : 0 < H) {P : Finset ℕ} (hP : ∀ l ∈ P, l.Prime)
    {r l : ℕ} (hl : l ∈ mrPrimeSubblock H P r) :
    (mrNarrowPrimeInterval H r).1 ≤ l ∧ l ≤ (mrNarrowPrimeInterval H r).2 := by
  have hh := mrPrimeSubblock_real_bounds hH hP hl
  exact ⟨Nat.ceil_le.mpr hh.1, Nat.le_floor hh.2⟩

theorem mrNarrowPrimeInterval_lower_pos (H : ℝ) (r : ℕ) :
    0 < (mrNarrowPrimeInterval H r).1 := by
  have hh := (Real.exp_pos ((r : ℝ) / H)).trans_le (Nat.le_ceil _)
  exact_mod_cast hh

theorem mrNarrowPrimeInterval_upper_pos {H : ℝ} (hH : 0 < H) (r : ℕ) :
    0 < (mrNarrowPrimeInterval H r).2 := by
  apply Nat.le_floor
  simp only [Nat.cast_succ, Nat.cast_zero, zero_add]
  exact Real.one_le_exp_iff.mpr (by positivity)

theorem mrNarrowPrimeInterval_relative_width {H : ℝ} (hH : 2 ≤ H) (r : ℕ) :
    ((mrNarrowPrimeInterval H r).2 : ℝ) ≤ (1 + 2 / H) * (mrNarrowPrimeInterval H r).1 := by
  have hH0 : 0 < H := by linarith
  calc
    _ ≤ Real.exp (((r + 1 : ℕ) : ℝ) / H) := Nat.floor_le (Real.exp_pos _).le
    _ = Real.exp ((r : ℝ) / H) * Real.exp (1 / H) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    _ ≤ Real.exp ((r : ℝ) / H) * (1 + 2 / H) :=
      mul_le_mul_of_nonneg_left (exp_inv_resolution_le_one_add hH) (Real.exp_pos _).le
    _ ≤ (mrNarrowPrimeInterval H r).1 * (1 + 2 / H) :=
      mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity)
    _ = _ := by ring

theorem mrNarrowPrimeInterval_dyadic_width {H : ℝ} (hH : 2 ≤ H) (r : ℕ) :
    (mrNarrowPrimeInterval H r).2 ≤ 2 * (mrNarrowPrimeInterval H r).1 := by
  have hH0 : 0 < H := by linarith
  have hratio : 2 / H ≤ (1 : ℝ) := (div_le_iff₀ hH0).mpr (by linarith)
  have hh := mrNarrowPrimeInterval_relative_width hH r
  have hm := mul_le_mul_of_nonneg_right hratio (Nat.cast_nonneg (mrNarrowPrimeInterval H r).1)
  have hbound : ((mrNarrowPrimeInterval H r).2 : ℝ) ≤ 2 * (mrNarrowPrimeInterval H r).1 := by nlinarith
  exact_mod_cast hbound

theorem mrNarrowPrimeInterval_upper_le_exp_shift {H : ℝ} (hH : 1 ≤ H) (r : ℕ) :
    ((mrNarrowPrimeInterval H r).2 : ℝ) ≤ Real.exp ((r : ℝ) / H + 1) := by
  have hH0 : 0 < H := by linarith
  have hinv : 1 / H ≤ (1 : ℝ) := (div_le_iff₀ hH0).mpr (by linarith)
  apply (Nat.floor_le (Real.exp_pos _).le).trans
  apply Real.exp_le_exp.mpr
  push_cast
  rw [add_div]
  linarith

theorem mrNarrowPrimeInterval_lower_le_scale
    {H p q : ℝ} (hH : 1 ≤ H) (hp : 0 ≤ p) (hq : 0 ≤ q)
    {r X : ℕ} (hr : r ∈ mrLogBlockIndices H p q) (hX : Real.exp q ≤ X) :
    (mrNarrowPrimeInterval H r).1 ≤ X := by
  apply Nat.ceil_le.mpr
  exact (Real.exp_le_exp.mpr (mrLogBlockIndices_parameter_bounds hH hp hq hr).2).trans hX

def mrScheduledPrimeInterval (p₁ q₁ : ℝ) (j : ℕ) : ℕ × ℕ :=
  mrLogPrimeInterval (mrLogScheduleLower p₁ q₁ j) (mrLogScheduleUpper q₁ j)

def mrScheduledPrimeSubblock (eta p₁ q₁ : ℝ) (j r : ℕ) : Finset ℕ :=
  mrPrimeSubblock (mrLogBlockResolution eta p₁ q₁ (j : ℝ))
    (primesInBlock (mrScheduledPrimeInterval p₁ q₁ j)) r

def mrScheduledNarrowInterval (eta p₁ q₁ : ℝ) (j r : ℕ) : ℕ × ℕ :=
  mrNarrowPrimeInterval (mrLogBlockResolution eta p₁ q₁ (j : ℝ)) r

def mrScheduledTypicalCofactor
    (blocks : Finset (ℕ × ℕ)) (eta p₁ q₁ : ℝ) (j r X : ℕ) : Finset ℕ :=
  mrTypicalCofactorRectangle blocks (mrScheduledPrimeInterval p₁ q₁ j)
    (mrScheduledNarrowInterval eta p₁ q₁ j r) X

def mrArithmeticSmallFrequencySet (eta p₁ q₁ : ℝ) (f : ℕ → ℂ) : ℕ → Set ℝ :=
  mrScheduledSmallFrequencySet eta p₁ q₁ (mrScheduledPrimeSubblock eta p₁ q₁)
    (fun _ _ ↦ mrFinitePrimeLineCoefficient f)

theorem mrScheduledPrimeSubblock_subset (eta p₁ q₁ : ℝ) (j r : ℕ) :
    mrScheduledPrimeSubblock eta p₁ q₁ j r ⊆ primesInBlock (mrScheduledPrimeInterval p₁ q₁ j) :=
  mrPrimeSubblock_subset _ _ _

theorem mrScheduledPrimeSubblock_prime (eta p₁ q₁ : ℝ) (j r : ℕ) :
    ∀ l ∈ mrScheduledPrimeSubblock eta p₁ q₁ j r, l.Prime := by
  intro l hl
  exact (mem_primesInBlock.mp (mrScheduledPrimeSubblock_subset eta p₁ q₁ j r hl)).1

theorem mrScheduledPrimeSubblock_integer_bounds
    {eta p₁ q₁ : ℝ} {j r : ℕ} (hH : 0 < mrLogBlockResolution eta p₁ q₁ (j : ℝ)) :
    ∀ l ∈ mrScheduledPrimeSubblock eta p₁ q₁ j r,
      (mrScheduledNarrowInterval eta p₁ q₁ j r).1 ≤ l ∧
        l ≤ (mrScheduledNarrowInterval eta p₁ q₁ j r).2 := by
  intro l hl
  exact mrPrimeSubblock_integer_bounds hH (fun p hp ↦ (mem_primesInBlock.mp hp).1) hl

theorem mrScheduledPrimeSubblock_dyadic_bounds
    {eta p₁ q₁ : ℝ} {j r : ℕ} (hH : 2 ≤ mrLogBlockResolution eta p₁ q₁ (j : ℝ)) :
    ∀ l ∈ mrScheduledPrimeSubblock eta p₁ q₁ j r,
      Real.exp (mrScheduledParameter eta p₁ q₁ j r) ≤ l ∧
        (l : ℝ) ≤ 2 * Real.exp (mrScheduledParameter eta p₁ q₁ j r) := by
  intro l hl
  have hh := mrPrimeSubblock_real_bounds (by linarith : 0 < mrLogBlockResolution eta p₁ q₁ (j : ℝ))
    (fun p hp ↦ (mem_primesInBlock.mp hp).1) hl
  exact ⟨hh.1, hh.2.trans (exp_next_subblock_le_double hH r)⟩

theorem mrScheduledPrimeSubblock_partition (eta p₁ q₁ : ℝ) (j : ℕ) :
    Set.PairwiseDisjoint (↑(mrScheduledSubblocks eta p₁ q₁ j)) (mrScheduledPrimeSubblock eta p₁ q₁ j) ∧
      (mrScheduledSubblocks eta p₁ q₁ j).biUnion (mrScheduledPrimeSubblock eta p₁ q₁ j) =
        primesInBlock (mrScheduledPrimeInterval p₁ q₁ j) := by
  constructor
  · exact mrPrimeSubblock_pairwiseDisjoint _ _ _
  · apply mrPrimeSubblock_biUnion_eq (by unfold mrLogBlockResolution; positivity)
    exact fun l hl ↦ mem_primesInBlock_mrLogPrimeInterval_bounds hl

theorem mrScheduledPrimeInterval_disjoint_of_lt
    {eta p₁ q₁ : ℝ} (heta : eta ≤ 1 / 12) (hp : 2 ≤ p₁)
    (hq : 1 ≤ q₁) (hpq : p₁ ≤ q₁) (hlogq : 1 ≤ Real.log q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁) {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) :
    Disjoint (primesInBlock (mrScheduledPrimeInterval p₁ q₁ i))
      (primesInBlock (mrScheduledPrimeInterval p₁ q₁ j)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro l hli hlj
  have hupper := (mem_primesInBlock_mrLogPrimeInterval_bounds hli).2
  have hlower := (mem_primesInBlock_mrLogPrimeInterval_bounds hlj).1
  have hgap := mrLogSchedule_separated_of_lt heta hp hq hpq hlogq hbudget hi hij
  linarith

theorem mrScheduledPrimeInterval_disjoint
    {eta p₁ q₁ : ℝ} (heta : eta ≤ 1 / 12) (hp : 2 ≤ p₁)
    (hq : 1 ≤ q₁) (hpq : p₁ ≤ q₁) (hlogq : 1 ≤ Real.log q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁) {i j : ℕ}
    (hi : 1 ≤ i) (hj : 1 ≤ j) (hij : i ≠ j) :
    Disjoint (primesInBlock (mrScheduledPrimeInterval p₁ q₁ i))
      (primesInBlock (mrScheduledPrimeInterval p₁ q₁ j)) := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact mrScheduledPrimeInterval_disjoint_of_lt heta hp hq hpq hlogq hbudget hi hlt
  · exact (mrScheduledPrimeInterval_disjoint_of_lt heta hp hq hpq hlogq hbudget hj hgt).symm

def mrScheduledBlocks (p₁ q₁ : ℝ) (J : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 J).image (mrScheduledPrimeInterval p₁ q₁)

theorem mrScheduledBlocks_other_disjoint
    {eta p₁ q₁ : ℝ} (heta : eta ≤ 1 / 12) (hp : 2 ≤ p₁)
    (hq : 1 ≤ q₁) (hpq : p₁ ≤ q₁) (hlogq : 1 ≤ Real.log q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁) (J : ℕ) {j : ℕ} (hj : 1 ≤ j) :
    ∀ K ∈ mrScheduledBlocks p₁ q₁ J, K ≠ mrScheduledPrimeInterval p₁ q₁ j →
      Disjoint (primesInBlock (mrScheduledPrimeInterval p₁ q₁ j)) (primesInBlock K) := by
  intro K hK hne
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hK
  have hij : j ≠ i := by
    intro hh
    subst i
    exact hne rfl
  exact mrScheduledPrimeInterval_disjoint heta hp hq hpq hlogq hbudget hj
    (Finset.mem_Icc.mp hi).1 hij

end

end Erdos67b
