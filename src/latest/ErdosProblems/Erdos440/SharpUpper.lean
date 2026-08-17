import Mathlib

open scoped BigOperators
open Filter

namespace Erdos440SharpUpper

/-- A positive strictly increasing sequence of natural numbers. -/
structure IncreasingSequence where
  val : ℕ → ℕ
  positive : ∀ i, 0 < val i
  strictMono : StrictMono val

namespace IncreasingSequence

variable (A : IncreasingSequence)

def gap (i : ℕ) : ℕ := A.val (i + 1) - A.val i

def edgeLcm (i : ℕ) : ℕ := Nat.lcm (A.val i) (A.val (i + 1))

def goodIndices (x : ℕ) : Finset ℕ :=
  (Finset.range x).filter fun i ↦ A.edgeLcm i ≤ x

def countingFunction (x : ℕ) : ℕ := (A.goodIndices x).card

def smallGapIndices (x j : ℕ) : Finset ℕ :=
  (A.goodIndices x).filter fun i ↦ A.gap i ≤ j

def partialGapSum (x j : ℕ) : ℕ :=
  ∑ i ∈ A.smallGapIndices x j, A.gap i

@[simp] theorem mem_goodIndices {i x : ℕ} :
    i ∈ A.goodIndices x ↔ i < x ∧ A.edgeLcm i ≤ x := by
  simp [goodIndices]

theorem val_lt_succ (i : ℕ) : A.val i < A.val (i + 1) :=
  A.strictMono (Nat.lt_succ_self i)

theorem gap_pos (i : ℕ) : 0 < A.gap i := by
  simpa [gap] using Nat.sub_pos_of_lt (A.val_lt_succ i)

theorem gap_add (i : ℕ) : A.val i + A.gap i = A.val (i + 1) := by
  simp [gap, Nat.add_sub_of_le (Nat.le_of_lt (A.val_lt_succ i))]

theorem gcd_le_gap (i : ℕ) : Nat.gcd (A.val i) (A.val (i + 1)) ≤ A.gap i := by
  have hdvd : Nat.gcd (A.val i) (A.val (i + 1)) ∣ A.gap i := by
    rw [gap]
    exact Nat.dvd_sub (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
  exact Nat.le_of_dvd (A.gap_pos i) hdvd

theorem product_le_gap_mul {i x j : ℕ} (hi : i ∈ A.goodIndices x)
    (hgap : A.gap i ≤ j) : A.val i * A.val (i + 1) ≤ j * x := by
  have hg := A.gcd_le_gap i
  have hl := (A.mem_goodIndices.mp hi).2
  calc
    A.val i * A.val (i + 1) =
        Nat.gcd (A.val i) (A.val (i + 1)) * Nat.lcm (A.val i) (A.val (i + 1)) := by
          rw [Nat.gcd_mul_lcm]
    _ ≤ A.gap i * x := Nat.mul_le_mul hg hl
    _ ≤ j * x := Nat.mul_le_mul_right x hgap

theorem val_sq_le {i x j : ℕ} (hi : i ∈ A.goodIndices x)
    (hgap : A.gap i ≤ j) : A.val i ^ 2 ≤ j * x := by
  have hp := A.product_le_gap_mul hi hgap
  have hv := Nat.le_of_lt (A.val_lt_succ i)
  nlinarith [Nat.mul_le_mul_left (A.val i) hv]

@[simp] theorem mem_smallGapIndices {i x j : ℕ} :
    i ∈ A.smallGapIndices x j ↔ i ∈ A.goodIndices x ∧ A.gap i ≤ j := by
  simp [smallGapIndices]

theorem val_le_sqrt_mul {i x j : ℕ} (hi : i ∈ A.smallGapIndices x j) :
    A.val i ≤ Nat.sqrt (j * x) := by
  rw [Nat.le_sqrt']
  exact A.val_sq_le (A.mem_smallGapIndices.mp hi).1 (A.mem_smallGapIndices.mp hi).2

theorem sum_gap_range (n : ℕ) :
    (∑ i ∈ Finset.range n, A.gap i) = A.val n - A.val 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have h0 : A.val 0 ≤ A.val n := A.strictMono.monotone (Nat.zero_le n)
      have hn : A.val n ≤ A.val (n + 1) := Nat.le_of_lt (A.val_lt_succ n)
      simp only [gap]
      omega

/-- The selected intervals `[a_i,a_{i+1})` have total length at most the
right endpoint of the last selected interval.  We express this without interval
unions: add the nonselected, nonnegative gaps up to the maximum selected index
and telescope. -/
theorem partialGapSum_le_sqrt_add (x j : ℕ) :
    A.partialGapSum x j ≤ Nat.sqrt (j * x) + j := by
  classical
  let s := A.smallGapIndices x j
  by_cases hs : s.Nonempty
  · let m := s.max' hs
    have hm : m ∈ s := s.max'_mem hs
    have hsubset : s ⊆ Finset.range (m + 1) := by
      intro i hi
      have him : i ≤ m := s.le_max' i hi
      simpa using Nat.lt_succ_of_le him
    have hsum_subset :
        (∑ i ∈ s, A.gap i) ≤ ∑ i ∈ Finset.range (m + 1), A.gap i := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by simp)
    have htel :
        (∑ i ∈ Finset.range (m + 1), A.gap i) = A.val (m + 1) - A.val 0 := by
      exact A.sum_gap_range (m + 1)
    have hendpoint : A.val (m + 1) ≤ Nat.sqrt (j * x) + j := by
      rw [← A.gap_add m]
      exact Nat.add_le_add (A.val_le_sqrt_mul hm) (A.mem_smallGapIndices.mp hm).2
    calc
      A.partialGapSum x j = ∑ i ∈ s, A.gap i := rfl
      _ ≤ ∑ i ∈ Finset.range (m + 1), A.gap i := hsum_subset
      _ = A.val (m + 1) - A.val 0 := htel
      _ ≤ A.val (m + 1) := Nat.sub_le _ _
      _ ≤ Nat.sqrt (j * x) + j := hendpoint
  · have : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [partialGapSum, s, this]

/-- At the full gap cutoff the intervals all end by `x`, so their total
length is at most `x`. -/
theorem partialGapSum_diagonal_le (x : ℕ) : A.partialGapSum x x ≤ x := by
  classical
  have hgap_of_good : ∀ {i}, i ∈ A.goodIndices x → A.gap i ≤ x := by
    intro i hi
    have hlcm_pos : 0 < A.edgeLcm i :=
      Nat.lcm_pos (A.positive i) (A.positive (i + 1))
    have hright : A.val (i + 1) ≤ A.edgeLcm i :=
      Nat.le_of_dvd hlcm_pos (Nat.dvd_lcm_right _ _)
    exact (Nat.sub_le _ _).trans (hright.trans (A.mem_goodIndices.mp hi).2)
  have hsmall : A.smallGapIndices x x = A.goodIndices x := by
    ext i
    simp only [mem_smallGapIndices]
    constructor
    · exact And.left
    · intro hi
      exact ⟨hi, hgap_of_good hi⟩
  let s := A.goodIndices x
  by_cases hs : s.Nonempty
  · let m := s.max' hs
    have hm : m ∈ s := s.max'_mem hs
    have hsubset : s ⊆ Finset.range (m + 1) := by
      intro i hi
      simpa using Nat.lt_succ_of_le (s.le_max' i hi)
    have hsum_subset :
        (∑ i ∈ s, A.gap i) ≤ ∑ i ∈ Finset.range (m + 1), A.gap i :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (by simp)
    have hendpoint : A.val (m + 1) ≤ x := by
      have hlcm_pos : 0 < A.edgeLcm m :=
        Nat.lcm_pos (A.positive m) (A.positive (m + 1))
      have hright : A.val (m + 1) ≤ A.edgeLcm m :=
        Nat.le_of_dvd hlcm_pos (Nat.dvd_lcm_right _ _)
      exact hright.trans (A.mem_goodIndices.mp hm).2
    calc
      A.partialGapSum x x = ∑ i ∈ s, A.gap i := by simp [partialGapSum, hsmall, s]
      _ ≤ ∑ i ∈ Finset.range (m + 1), A.gap i := hsum_subset
      _ = A.val (m + 1) - A.val 0 := A.sum_gap_range (m + 1)
      _ ≤ A.val (m + 1) := Nat.sub_le _ _
      _ ≤ x := hendpoint
  · have : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [partialGapSum, hsmall, s, this]

theorem gap_le_of_mem_goodIndices {i x : ℕ} (hi : i ∈ A.goodIndices x) :
    A.gap i ≤ x := by
  have hlcm_pos : 0 < A.edgeLcm i := by
    exact Nat.lcm_pos (A.positive i) (A.positive (i + 1))
  have hright : A.val (i + 1) ≤ A.edgeLcm i := by
    exact Nat.le_of_dvd hlcm_pos (Nat.dvd_lcm_right _ _)
  exact (Nat.sub_le _ _).trans (hright.trans (A.mem_goodIndices.mp hi).2)

/-- The finite telescoping identity behind Abel summation. -/
theorem one_eq_gap_div_add_sum (d x : ℕ) (hd : 0 < d) (hdx : d ≤ x) :
    (1 : ℝ) = (d : ℝ) / x +
      ∑ j ∈ Finset.Ico d x, (d : ℝ) / ((j : ℝ) * (j + 1)) := by
  induction x with
  | zero => omega
  | succ x ih =>
      by_cases heq : d = x + 1
      · subst d
        have hne : (↑(x + 1) : ℝ) ≠ 0 := by positivity
        rw [Finset.Ico_self, Finset.sum_empty, add_zero, div_self hne]
      · have hdx' : d ≤ x := by omega
        rw [Finset.sum_Ico_succ_top hdx']
        have hxnat : 0 < x := hd.trans_le hdx'
        have hx : (x : ℝ) ≠ 0 := by exact_mod_cast hxnat.ne'
        have hxs : ((x : ℝ) + 1) ≠ 0 := by positivity
        have halg :
            (d : ℝ) / (x + 1) + (d : ℝ) / ((x : ℝ) * (x + 1)) = (d : ℝ) / x := by
          field_simp
        calc
          (1 : ℝ) = (d : ℝ) / x +
              ∑ j ∈ Finset.Ico d x, (d : ℝ) / ((j : ℝ) * (j + 1)) := ih hdx'
          _ = (d : ℝ) / (x + 1) +
              (∑ j ∈ Finset.Ico d x, (d : ℝ) / ((j : ℝ) * (j + 1)) +
                (d : ℝ) / ((x : ℝ) * (x + 1))) := by
                  rw [← halg]
                  ring
          _ = (d : ℝ) / (↑(x + 1) : ℝ) +
              (∑ j ∈ Finset.Ico d x, (d : ℝ) / ((j : ℝ) * (j + 1)) +
                (d : ℝ) / ((x : ℝ) * (x + 1))) := by
                  norm_num

theorem filter_Ico_one_eq_Ico (d x : ℕ) (hd : 0 < d) :
    (Finset.Ico 1 x).filter (fun j ↦ d ≤ j) = Finset.Ico d x := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_Ico]
  omega

theorem one_eq_gap_div_add_sum_if (d x : ℕ) (hd : 0 < d) (hdx : d ≤ x) :
    (1 : ℝ) = (d : ℝ) / x +
      ∑ j ∈ Finset.Ico 1 x,
        if d ≤ j then (d : ℝ) / ((j : ℝ) * (j + 1)) else 0 := by
  rw [← Finset.sum_filter]
  rw [filter_Ico_one_eq_Ico d x hd]
  exact one_eq_gap_div_add_sum d x hd hdx

theorem sum_good_if_div (x j : ℕ) (D : ℝ) :
    (∑ i ∈ A.goodIndices x,
        if A.gap i ≤ j then (A.gap i : ℝ) / D else 0) =
      (A.partialGapSum x j : ℝ) / D := by
  rw [← Finset.sum_filter]
  change (∑ i ∈ A.smallGapIndices x j, (A.gap i : ℝ) / D) = _
  change (∑ i ∈ A.smallGapIndices x j, (A.gap i : ℝ) / D) =
    (↑(∑ i ∈ A.smallGapIndices x j, A.gap i) : ℝ) / D
  rw [Nat.cast_sum, Finset.sum_div]

/-- Exact finite Abel summation for the gap distribution of good edges. -/
theorem countingFunction_abel (x : ℕ) (hx : 0 < x) :
    (A.countingFunction x : ℝ) = (A.partialGapSum x x : ℝ) / x +
      ∑ j ∈ Finset.Ico 1 x,
        (A.partialGapSum x j : ℝ) / ((j : ℝ) * (j + 1)) := by
  classical
  calc
    (A.countingFunction x : ℝ) = ∑ i ∈ A.goodIndices x, (1 : ℝ) := by
      simp [countingFunction]
    _ = ∑ i ∈ A.goodIndices x,
        ((A.gap i : ℝ) / x +
          ∑ j ∈ Finset.Ico 1 x,
            if A.gap i ≤ j then
              (A.gap i : ℝ) / ((j : ℝ) * (j + 1)) else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact one_eq_gap_div_add_sum_if (A.gap i) x (A.gap_pos i)
        (A.gap_le_of_mem_goodIndices hi)
    _ = (∑ i ∈ A.goodIndices x, (A.gap i : ℝ) / x) +
        ∑ i ∈ A.goodIndices x,
          ∑ j ∈ Finset.Ico 1 x,
            if A.gap i ≤ j then
              (A.gap i : ℝ) / ((j : ℝ) * (j + 1)) else 0 := by
      rw [Finset.sum_add_distrib]
    _ = (A.partialGapSum x x : ℝ) / x +
        ∑ i ∈ A.goodIndices x,
          ∑ j ∈ Finset.Ico 1 x,
            if A.gap i ≤ j then
              (A.gap i : ℝ) / ((j : ℝ) * (j + 1)) else 0 := by
      congr 1
      calc
        (∑ i ∈ A.goodIndices x, (A.gap i : ℝ) / x) =
            ∑ i ∈ A.goodIndices x,
              if A.gap i ≤ x then (A.gap i : ℝ) / x else 0 := by
                apply Finset.sum_congr rfl
                intro i hi
                simp [A.gap_le_of_mem_goodIndices hi]
        _ = (A.partialGapSum x x : ℝ) / x := A.sum_good_if_div x x (x : ℝ)
    _ = (A.partialGapSum x x : ℝ) / x +
        ∑ j ∈ Finset.Ico 1 x,
          ∑ i ∈ A.goodIndices x,
            if A.gap i ≤ j then
              (A.gap i : ℝ) / ((j : ℝ) * (j + 1)) else 0 := by
      rw [Finset.sum_comm]
    _ = (A.partialGapSum x x : ℝ) / x +
        ∑ j ∈ Finset.Ico 1 x,
          (A.partialGapSum x j : ℝ) / ((j : ℝ) * (j + 1)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      exact A.sum_good_if_div x j ((j : ℝ) * (j + 1))

/-- The sharp finite upper estimate before replacing natural square roots by
real square roots. -/
theorem countingFunction_le_natSqrt_sum (x : ℕ) (hx : 0 < x) :
    (A.countingFunction x : ℝ) ≤ 1 +
      ∑ j ∈ Finset.Ico 1 x,
        ((Nat.sqrt (j * x) : ℕ) + j : ℝ) / ((j : ℝ) * (j + 1)) := by
  rw [A.countingFunction_abel x hx]
  have hfirst : (A.partialGapSum x x : ℝ) / x ≤ 1 := by
    rw [div_le_one (by positivity : (0 : ℝ) < x)]
    exact_mod_cast A.partialGapSum_diagonal_le x
  have hsum :
      (∑ j ∈ Finset.Ico 1 x,
          (A.partialGapSum x j : ℝ) / ((j : ℝ) * (j + 1))) ≤
        ∑ j ∈ Finset.Ico 1 x,
          ((Nat.sqrt (j * x) : ℕ) + j : ℝ) / ((j : ℝ) * (j + 1)) := by
    apply Finset.sum_le_sum
    intro j hj
    apply div_le_div_of_nonneg_right
    · exact_mod_cast A.partialGapSum_le_sqrt_add x j
    · positivity
  linarith

noncomputable def sharpKernel (j : ℕ) : ℝ :=
  1 / (Real.sqrt j * (j + 1))

noncomputable def harmonicKernel (j : ℕ) : ℝ :=
  1 / (j + 1 : ℕ)

theorem sharpKernel_nonneg (j : ℕ) : 0 ≤ sharpKernel j := by
  unfold sharpKernel
  positivity

theorem sharpKernel_le_pseries (j : ℕ) :
    sharpKernel j ≤ 1 / (j : ℝ) ^ (3 / 2 : ℝ) := by
  rcases j with _ | j
  · simp [sharpKernel]
  · have hj : (0 : ℝ) < (j + 1 : ℕ) := by positivity
    have hsqrt : 0 < Real.sqrt (j + 1 : ℕ) := Real.sqrt_pos.2 hj
    have hden :
        Real.sqrt (j + 1 : ℕ) * (j + 1 : ℕ) ≤
          Real.sqrt (j + 1 : ℕ) * ((j + 1 : ℕ) + 1) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hsqrt)
      norm_num
    have hpow :
        Real.sqrt (j + 1 : ℕ) * (j + 1 : ℕ) =
          ((j + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      convert (Real.rpow_add_one hj.ne' (1 / 2 : ℝ)).symm using 1 <;> norm_num
    rw [sharpKernel, ← hpow]
    exact one_div_le_one_div_of_le (mul_pos hsqrt hj) hden

theorem summable_sharpKernel : Summable sharpKernel := by
  apply Summable.of_nonneg_of_le sharpKernel_nonneg sharpKernel_le_pseries
  exact Real.summable_one_div_nat_rpow.mpr (by norm_num)

noncomputable def sharpConstant : ℝ := ∑' j : ℕ, sharpKernel j

theorem sharp_partial_le_constant (s : Finset ℕ) :
    (∑ j ∈ s, sharpKernel j) ≤ sharpConstant := by
  exact summable_sharpKernel.sum_le_tsum s (fun j _ ↦ sharpKernel_nonneg j)

theorem natSqrt_summand_le_kernel (x j : ℕ) (hj : 0 < j) :
    ((Nat.sqrt (j * x) : ℕ) + j : ℝ) / ((j : ℝ) * (j + 1)) ≤
      Real.sqrt x * sharpKernel j + harmonicKernel j := by
  have hsqrt : (Nat.sqrt (j * x) : ℝ) ≤ Real.sqrt j * Real.sqrt x := by
    calc
      (Nat.sqrt (j * x) : ℝ) ≤ Real.sqrt (↑(j * x) : ℝ) :=
        Real.nat_sqrt_le_real_sqrt
      _ = Real.sqrt ((j : ℝ) * (x : ℝ)) := by norm_num
      _ = Real.sqrt j * Real.sqrt x := Real.sqrt_mul (by positivity) _
  have hden : (0 : ℝ) ≤ (j : ℝ) * (j + 1) := by positivity
  calc
    ((Nat.sqrt (j * x) : ℕ) + j : ℝ) / ((j : ℝ) * (j + 1)) ≤
        (Real.sqrt j * Real.sqrt x + j) / ((j : ℝ) * (j + 1)) := by
      apply div_le_div_of_nonneg_right _ hden
      norm_num only [Nat.cast_add]
      simpa only [add_comm] using add_le_add_right hsqrt (j : ℝ)
    _ = Real.sqrt x * sharpKernel j + harmonicKernel j := by
      have hjr : (0 : ℝ) < j := by exact_mod_cast hj
      have hsr : 0 < Real.sqrt j := Real.sqrt_pos.2 hjr
      have hsq : Real.sqrt j * Real.sqrt j = (j : ℝ) := by
        nlinarith [Real.sq_sqrt (le_of_lt hjr)]
      simp only [sharpKernel, harmonicKernel]
      norm_num only [Nat.cast_add, Nat.cast_one]
      field_simp
      nlinarith

/-- Sharp finite upper bound with precisely the Erdős--Szemerédi series kernel
and a harmonic error. -/
theorem countingFunction_le_sharp_partial (x : ℕ) (hx : 0 < x) :
    (A.countingFunction x : ℝ) ≤ 1 +
      Real.sqrt x * (∑ j ∈ Finset.Ico 1 x, sharpKernel j) +
      ∑ j ∈ Finset.Ico 1 x, harmonicKernel j := by
  calc
    (A.countingFunction x : ℝ) ≤ 1 +
        ∑ j ∈ Finset.Ico 1 x,
          ((Nat.sqrt (j * x) : ℕ) + j : ℝ) / ((j : ℝ) * (j + 1)) :=
      A.countingFunction_le_natSqrt_sum x hx
    _ ≤ 1 + ∑ j ∈ Finset.Ico 1 x,
        (Real.sqrt x * sharpKernel j + harmonicKernel j) := by
      have hsum :
          (∑ j ∈ Finset.Ico 1 x,
            ((Nat.sqrt (j * x) : ℕ) + j : ℝ) / ((j : ℝ) * (j + 1))) ≤
          ∑ j ∈ Finset.Ico 1 x,
            (Real.sqrt x * sharpKernel j + harmonicKernel j) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjone : 1 ≤ j := (Finset.mem_Ico.mp hj).1
        exact natSqrt_summand_le_kernel x j (Nat.zero_lt_of_lt hjone)
      linarith
    _ = 1 + Real.sqrt x * (∑ j ∈ Finset.Ico 1 x, sharpKernel j) +
        ∑ j ∈ Finset.Ico 1 x, harmonicKernel j := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      ring

theorem harmonic_partial_le_one_add_log (x : ℕ) :
    (∑ j ∈ Finset.Ico 1 x, harmonicKernel j) ≤ 1 + Real.log x := by
  have hsubset : Finset.Ico 1 x ⊆ Finset.range x := by
    intro j hj
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2
  have hsum :
      (∑ j ∈ Finset.Ico 1 x, harmonicKernel j) ≤
        ∑ j ∈ Finset.range x, harmonicKernel j := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro j hj hnot
      unfold harmonicKernel
      positivity)
  have heq :
      (∑ j ∈ Finset.range x, harmonicKernel j) = (harmonic x : ℝ) := by
    simp only [harmonicKernel, harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    simp only [one_div]
  calc
    (∑ j ∈ Finset.Ico 1 x, harmonicKernel j) ≤
        ∑ j ∈ Finset.range x, harmonicKernel j := hsum
    _ = (harmonic x : ℝ) := heq
    _ ≤ 1 + Real.log x := harmonic_le_one_add_log x

theorem countingFunction_div_sqrt_le (x : ℕ) (hx : 0 < x) :
    (A.countingFunction x : ℝ) / Real.sqrt x ≤
      sharpConstant + (2 + Real.log x) / Real.sqrt x := by
  have hfinite := A.countingFunction_le_sharp_partial x hx
  have hpartial :
      (∑ j ∈ Finset.Ico 1 x, sharpKernel j) ≤ sharpConstant :=
    sharp_partial_le_constant _
  have hmul :
      Real.sqrt x * (∑ j ∈ Finset.Ico 1 x, sharpKernel j) ≤
        Real.sqrt x * sharpConstant :=
    mul_le_mul_of_nonneg_left hpartial (Real.sqrt_nonneg _)
  have hharm := harmonic_partial_le_one_add_log x
  have hnum :
      (A.countingFunction x : ℝ) ≤
        Real.sqrt x * sharpConstant + (2 + Real.log x) := by
    linarith
  have hsqrt : 0 < Real.sqrt x := Real.sqrt_pos.2 (by exact_mod_cast hx)
  calc
    (A.countingFunction x : ℝ) / Real.sqrt x ≤
        (Real.sqrt x * sharpConstant + (2 + Real.log x)) / Real.sqrt x :=
      div_le_div_of_nonneg_right hnum hsqrt.le
    _ = sharpConstant + (2 + Real.log x) / Real.sqrt x := by
      field_simp

theorem tendsto_harmonicError :
    Tendsto (fun x : ℕ ↦ (2 + Real.log x) / Real.sqrt x) atTop (nhds 0) := by
  have hcast : Tendsto (fun x : ℕ ↦ (x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hsqrt : Tendsto (fun x : ℕ ↦ Real.sqrt x) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hcast
  have hconst : Tendsto (fun x : ℕ ↦ (2 : ℝ) / Real.sqrt x) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hsqrt
  have hlogReal :
      Tendsto (fun y : ℝ ↦ Real.log y / Real.sqrt y) atTop (nhds 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).tendsto_div_nhds_zero
  have hlog : Tendsto (fun x : ℕ ↦ Real.log x / Real.sqrt x) atTop (nhds 0) :=
    hlogReal.comp hcast
  convert hconst.add hlog using 1
  · funext x
    ring_nf
  · norm_num

/-- Epsilon/eventual formulation of `limsup (A(x)/sqrt x) ≤ c`. -/
theorem eventually_countingFunction_div_sqrt_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop,
      (A.countingFunction x : ℝ) / Real.sqrt x ≤ sharpConstant + ε := by
  have herr : ∀ᶠ x : ℕ in atTop, (2 + Real.log x) / Real.sqrt x < ε :=
    (tendsto_order.1 tendsto_harmonicError).2 ε hε
  filter_upwards [herr, eventually_gt_atTop 0] with x hxerr hxpos
  have hmain := A.countingFunction_div_sqrt_le x hxpos
  linarith

end IncreasingSequence

end Erdos440SharpUpper
