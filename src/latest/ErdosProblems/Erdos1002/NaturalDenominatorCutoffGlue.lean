import ErdosProblems.Erdos1002.NaturalDenominatorCutoff

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Global glue for the natural-denominator cutoff

This file performs the two summations that remain after the one-block and
pointwise estimates in `NaturalDenominatorCutoff`:

* the high-frequency part of the all-`p` tail is partitioned into explicit
  dyadic intervals and dominated by a fixed summable fifth-moment geometric
  series;
* finitely many natural-denominator blocks are combined in coefficient
  `l^2`, with no informal appeal to Minkowski's inequality.

The definitions retain the endpoints used in the manuscript.  In particular,
the `j`-th frequency block is `(2^j M, 2^(j+1) M]`.
-/

open Finset
open scoped BigOperators

namespace Erdos1002

noncomputable section

/-! ## Dyadic frequency partition -/

/-- The `j`-th dyadic interval strictly above the base point `M`. -/
def dyadicFrequencyBlock (M j : ℕ) : Finset ℕ :=
  Ioc (2 ^ j * M) (2 ^ (j + 1) * M)

/-- Distinct dyadic frequency blocks are disjoint. -/
theorem pairwiseDisjoint_dyadicFrequencyBlock (M : ℕ) :
    (Set.univ : Set ℕ).PairwiseDisjoint (dyadicFrequencyBlock M) := by
  intro i _hi j _hj hij
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · apply Finset.Ioc_disjoint_Ioc_of_le
    exact Nat.mul_le_mul_right M
      (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : i + 1 ≤ j))
  · exact Disjoint.symm (Finset.Ioc_disjoint_Ioc_of_le
      (Nat.mul_le_mul_right M
        (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : j + 1 ≤ i))))

/-- Every integer strictly above `M` belongs to its unique dyadic frequency
block.  The proof chooses the block by the binary logarithm of
`(n-1)/M`; both endpoint inequalities are proved explicitly. -/
theorem mem_dyadicFrequencyBlock_of_lt
    {M n : ℕ} (hM : 0 < M) (hMn : M < n) :
    n ∈ dyadicFrequencyBlock M (Nat.log 2 ((n - 1) / M)) := by
  let q : ℕ := (n - 1) / M
  have hMle : M ≤ n - 1 := by omega
  have hq : 0 < q := by
    dsimp [q]
    exact Nat.div_pos hMle hM
  have hlowerPow : 2 ^ Nat.log 2 q ≤ q :=
    Nat.pow_log_le_self 2 hq.ne'
  have hlowerMul : 2 ^ Nat.log 2 q * M ≤ n - 1 := by
    exact (Nat.mul_le_mul_right M hlowerPow).trans (Nat.div_mul_le_self (n - 1) M)
  have hlower : 2 ^ Nat.log 2 q * M < n := by
    exact hlowerMul.trans_lt (Nat.sub_lt (by omega) (by omega))
  have hupperPow : q < 2 ^ (Nat.log 2 q + 1) := by
    simpa only [Nat.succ_eq_add_one] using! Nat.lt_pow_succ_log_self Nat.one_lt_two q
  have hnlt : n - 1 < M * (q + 1) := by
    simpa only [q] using! Nat.lt_mul_div_succ (n - 1) hM
  have hnle : n ≤ M * (q + 1) := by omega
  have hupperMul : n ≤ 2 ^ (Nat.log 2 q + 1) * M := by
    have hqSucc : q + 1 ≤ 2 ^ (Nat.log 2 q + 1) := hupperPow
    exact hnle.trans ((Nat.mul_le_mul_left M hqSucc).trans_eq (mul_comm _ _))
  rw [dyadicFrequencyBlock, mem_Ioc]
  exact ⟨by simpa only [q] using! hlower, by simpa only [q] using! hupperMul⟩

/-- A finite initial family of dyadic blocks already covers every frequency
`n < K` above `M`.  Taking `K` blocks is deliberately generous and avoids
any hidden limiting choice. -/
theorem Ioc_subset_biUnion_dyadicFrequencyBlock
    (M K : ℕ) (hM : 0 < M) :
    Ioc M (K - 1) ⊆
      (range K).biUnion (dyadicFrequencyBlock M) := by
  intro n hn
  rw [mem_Ioc] at hn
  rw [mem_biUnion]
  let j : ℕ := Nat.log 2 ((n - 1) / M)
  refine ⟨j, mem_range.mpr ?_, ?_⟩
  · have hjle : j ≤ (n - 1) / M := by
      dsimp [j]
      exact Nat.log_le_self 2 ((n - 1) / M)
    have hdivle : (n - 1) / M ≤ n - 1 := Nat.div_le_self _ _
    omega
  · exact mem_dyadicFrequencyBlock_of_lt hM hn.1

/-- The fixed geometric fifth moment used to sum the high-frequency dyadic
envelopes. -/
def dyadicFifthMoment : ℝ :=
  ∑' j : ℕ, (((j + 1 : ℕ) : ℝ) ^ 5) * ((1 / 2 : ℝ) ^ j)

theorem summable_dyadicFifthMoment :
    Summable fun j : ℕ ↦
      (((j + 1 : ℕ) : ℝ) ^ 5) * ((1 / 2 : ℝ) ^ j) := by
  have hbase : Summable fun n : ℕ ↦
      (n : ℝ) ^ 5 * ((1 / 2 : ℝ) ^ n) := by
    exact summable_pow_mul_geometric_of_norm_lt_one 5 (by norm_num)
  have hshift := hbase.comp_injective Nat.succ_injective
  have hscaled := hshift.mul_left (2 : ℝ)
  apply hscaled.congr
  intro j
  change 2 * (((Nat.succ j : ℕ) : ℝ) ^ 5 *
      ((1 / 2 : ℝ) ^ Nat.succ j)) =
    (((j + 1 : ℕ) : ℝ) ^ 5) * ((1 / 2 : ℝ) ^ j)
  simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, pow_succ]
  ring

theorem dyadicFifthMoment_nonneg : 0 ≤ dyadicFifthMoment := by
  unfold dyadicFifthMoment
  exact tsum_nonneg fun _ ↦ by positivity

/-! ## A summable high-frequency block envelope -/

/-- Harmonic numbers on a dyadic interval grow at most linearly in the
block index.  This is the only logarithmic input in the infinite summation. -/
theorem harmonic_dyadic_mul_le
    (M j : ℕ) (hM : 0 < M) :
    (harmonic (2 ^ (j + 1) * M) : ℝ) ≤
      (2 + Real.log (M : ℝ)) + j := by
  have hraw := harmonic_le_one_add_log (2 ^ (j + 1) * M)
  have hMReal : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hpowReal : ((2 : ℝ) ^ (j + 1)) ≠ 0 := by positivity
  have hlogExpand :
      Real.log (((2 ^ (j + 1) * M : ℕ) : ℝ)) =
        ((j : ℝ) + 1) * Real.log 2 + Real.log (M : ℝ) := by
    push_cast
    rw [Real.log_mul hpowReal hMReal, Real.log_pow]
    norm_num
  have hlogTwo : Real.log 2 ≤ (1 : ℝ) := by
    nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [hlogExpand] at hraw
  have hjNonneg : (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by positivity
  push_cast at hraw hjNonneg ⊢
  nlinarith [mul_le_mul_of_nonneg_left hlogTwo hjNonneg]

/-- The square sum on one high-frequency dyadic interval is bounded by a
fixed fifth-moment geometric envelope. -/
theorem sum_sq_crudeAllPTailCoefficient_dyadic_le
    (N P M j : ℕ) (hN : 0 < N) (hM : 0 < M) :
    (∑ n ∈ dyadicFrequencyBlock M j,
        crudeAllPTailCoefficient N P n ^ 2) ≤
      (32 * ((N : ℝ) ^ 2 / (M : ℝ)) *
          (6 + Real.log (M : ℝ)) ^ 5) *
        ((((j + 1 : ℕ) : ℝ) ^ 5) * ((1 / 2 : ℝ) ^ j)) := by
  let X : ℕ := 2 ^ (j + 1) * M
  let Mj : ℕ := 2 ^ j * M
  let D : ℝ := 6 + Real.log (M : ℝ)
  have hMj : 0 < Mj := Nat.mul_pos (pow_pos (by omega) _) hM
  have hMjX : Mj ≤ X := by
    dsimp [Mj, X]
    exact Nat.mul_le_mul_right M
      (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : j ≤ j + 1))
  have hbase := sum_sq_crudeAllPTailCoefficient_Ioc_le
    N P Mj X hN hMj hMjX
  have hblock : dyadicFrequencyBlock M j = Ioc Mj X := by
    rfl
  rw [hblock]
  refine hbase.trans ?_
  have hMReal : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hlogM : 0 ≤ Real.log (M : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast hM)
  have hD : 4 ≤ D := by dsimp [D]; linarith
  have hHnonneg : 0 ≤ (harmonic X : ℝ) := by
    simpa using! harmonic_cast_mono (A := 0) (B := X) (Nat.zero_le X)
  have hH : (harmonic X : ℝ) ≤ D + j := by
    dsimp [X, D]
    linarith [harmonic_dyadic_mul_le M j hM]
  have hjNonneg : (0 : ℝ) ≤ (j : ℝ) := by positivity
  have hDj : 0 ≤ D + (j : ℝ) := by linarith
  have hDjMul : D + (j : ℝ) ≤ D * ((j + 1 : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have hZeta : Real.pi ^ 2 / 6 ≤ (4 : ℝ) := by
    nlinarith [Real.pi_pos, Real.pi_le_four]
  have hB :
      4 * (harmonic X : ℝ) + 2 * (Real.pi ^ 2 / 6) ≤
        4 * (D + (j : ℝ)) := by
    dsimp [D, X]
    linarith [harmonic_dyadic_mul_le M j hM]
  have hBnonneg :
      0 ≤ 4 * (harmonic X : ℝ) + 2 * (Real.pi ^ 2 / 6) := by
    positivity
  have hBcoarse :
      4 * (harmonic X : ℝ) + 2 * (Real.pi ^ 2 / 6) ≤
        4 * (D * ((j + 1 : ℕ) : ℝ)) := by
    exact hB.trans (mul_le_mul_of_nonneg_left hDjMul (by norm_num))
  have hHcoarse :
      (harmonic X : ℝ) ≤ D * ((j + 1 : ℕ) : ℝ) :=
    hH.trans hDjMul
  have hscale :
      (((N : ℝ) / (Mj : ℝ)) ^ 2) * (X : ℝ) =
        (2 * ((N : ℝ) ^ 2 / (M : ℝ))) * ((1 / 2 : ℝ) ^ j) := by
    dsimp [Mj, X]
    push_cast
    rw [one_div_pow]
    field_simp [pow_ne_zero]
    ring
  calc
    ((((N : ℝ) / (Mj : ℝ)) *
          (4 * (harmonic X : ℝ) + 2 * (Real.pi ^ 2 / 6))) ^ 2 *
        ((X : ℝ) * (harmonic X : ℝ) ^ 3)) =
        ((((N : ℝ) / (Mj : ℝ)) ^ 2) * (X : ℝ)) *
          ((4 * (harmonic X : ℝ) + 2 * (Real.pi ^ 2 / 6)) ^ 2 *
            (harmonic X : ℝ) ^ 3) := by ring
    _ ≤ (((N : ℝ) / (Mj : ℝ)) ^ 2 * (X : ℝ)) *
          ((4 * (D * ((j + 1 : ℕ) : ℝ))) ^ 2 *
            (D * ((j + 1 : ℕ) : ℝ)) ^ 3) := by
      gcongr
    _ = (32 * ((N : ℝ) ^ 2 / (M : ℝ)) * D ^ 5) *
          ((((j + 1 : ℕ) : ℝ) ^ 5) * ((1 / 2 : ℝ) ^ j)) := by
      rw [hscale]
      ring
    _ = (32 * ((N : ℝ) ^ 2 / (M : ℝ)) *
          (6 + Real.log (M : ℝ)) ^ 5) *
        ((((j + 1 : ℕ) : ℝ) ^ 5) * ((1 / 2 : ℝ) ^ j)) := by rfl

/-- The square of the crude all-denominator tail, restricted to frequencies
strictly above `M`. -/
def crudeAllPTailHighSquare (N P M n : ℕ) : ℝ :=
  if M < n then crudeAllPTailCoefficient N P n ^ 2 else 0

theorem crudeAllPTailHighSquare_nonneg (N P M n : ℕ) :
    0 ≤ crudeAllPTailHighSquare N P M n := by
  unfold crudeAllPTailHighSquare
  split_ifs <;> positivity

/-- Every finite partial sum of the high-frequency tail is controlled by the
same geometric fifth moment.  The proof displays the covering finset and
uses pairwise disjointness before invoking the one-block estimate. -/
theorem sum_range_crudeAllPTailHighSquare_le
    (N P M K : ℕ) (hN : 0 < N) (hM : 0 < M) :
    (∑ n ∈ range K, crudeAllPTailHighSquare N P M n) ≤
      (32 * ((N : ℝ) ^ 2 / (M : ℝ)) *
        (6 + Real.log (M : ℝ)) ^ 5) * dyadicFifthMoment := by
  let C : ℝ := 32 * ((N : ℝ) ^ 2 / (M : ℝ)) *
    (6 + Real.log (M : ℝ)) ^ 5
  let g : ℕ → ℝ := fun j ↦
    (((j + 1 : ℕ) : ℝ) ^ 5) * ((1 / 2 : ℝ) ^ j)
  let S : Finset ℕ := (range K).filter (fun n ↦ M < n)
  let U : Finset ℕ := (range K).biUnion (dyadicFrequencyBlock M)
  have hC : 0 ≤ C := by
    dsimp [C]
    have hlogM : 0 ≤ Real.log (M : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hM)
    positivity
  have hSU : S ⊆ U := by
    intro n hn
    simp only [S, mem_filter] at hn
    apply Ioc_subset_biUnion_dyadicFrequencyBlock M K hM
    rw [mem_Ioc]
    have hnK := mem_range.mp hn.1
    exact ⟨hn.2, by omega⟩
  have hdis : ((range K : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (dyadicFrequencyBlock M) :=
    (pairwiseDisjoint_dyadicFrequencyBlock M).subset (Set.subset_univ _)
  have hgNonneg : ∀ j, 0 ≤ g j := by
    intro j
    dsimp [g]
    positivity
  calc
    (∑ n ∈ range K, crudeAllPTailHighSquare N P M n) =
        ∑ n ∈ S, crudeAllPTailCoefficient N P n ^ 2 := by
      simp only [S, Finset.sum_filter, crudeAllPTailHighSquare]
    _ ≤ ∑ n ∈ U, crudeAllPTailCoefficient N P n ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hSU
      intro n _hn _hnot
      positivity
    _ = ∑ j ∈ range K, ∑ n ∈ dyadicFrequencyBlock M j,
          crudeAllPTailCoefficient N P n ^ 2 := by
      exact Finset.sum_biUnion hdis
    _ ≤ ∑ j ∈ range K, C * g j := by
      apply Finset.sum_le_sum
      intro j _hj
      exact sum_sq_crudeAllPTailCoefficient_dyadic_le N P M j hN hM
    _ = C * ∑ j ∈ range K, g j := by
      rw [Finset.mul_sum]
    _ ≤ C * dyadicFifthMoment := by
      gcongr
      exact summable_dyadicFifthMoment.sum_le_tsum (range K)
        (fun j _hj ↦ hgNonneg j)
    _ = (32 * ((N : ℝ) ^ 2 / (M : ℝ)) *
        (6 + Real.log (M : ℝ)) ^ 5) * dyadicFifthMoment := by rfl

/-- The high-frequency square tail is summable. -/
theorem summable_crudeAllPTailHighSquare
    (N P M : ℕ) (hN : 0 < N) (hM : 0 < M) :
    Summable (crudeAllPTailHighSquare N P M) := by
  apply summable_of_sum_range_le (crudeAllPTailHighSquare_nonneg N P M)
  intro K
  exact sum_range_crudeAllPTailHighSquare_le N P M K hN hM

/-- Global high-frequency square-sum estimate obtained after the explicit
dyadic summation. -/
theorem tsum_crudeAllPTailHighSquare_le
    (N P M : ℕ) (hN : 0 < N) (hM : 0 < M) :
    (∑' n : ℕ, crudeAllPTailHighSquare N P M n) ≤
      (32 * ((N : ℝ) ^ 2 / (M : ℝ)) *
        (6 + Real.log (M : ℝ)) ^ 5) * dyadicFifthMoment := by
  apply Real.tsum_le_of_sum_range_le (crudeAllPTailHighSquare_nonneg N P M)
  intro K
  exact sum_range_crudeAllPTailHighSquare_le N P M K hN hM

/-! ## The complete positive-frequency all-`p` tail -/

theorem crudeAllPTailCoefficient_zero (N P : ℕ) :
    crudeAllPTailCoefficient N P 0 = 0 := by
  simp [crudeAllPTailCoefficient]

/-- The low-frequency square, extended by zero away from `1 <= n <= M`. -/
def crudeAllPTailLowSquare (N P M n : ℕ) : ℝ :=
  if n ∈ Icc 1 M then crudeAllPTailCoefficient N P n ^ 2 else 0

theorem summable_crudeAllPTailLowSquare (N P M : ℕ) :
    Summable (crudeAllPTailLowSquare N P M) := by
  apply summable_of_finite_support
  refine (Icc 1 M).finite_toSet.subset ?_
  intro n hn
  by_contra hmem
  have hmem' : n ∉ Icc 1 M := by simpa using! hmem
  have hz : crudeAllPTailLowSquare N P M n = 0 := by
    rw [crudeAllPTailLowSquare, if_neg hmem']
  exact hn hz

theorem tsum_crudeAllPTailLowSquare_eq (N P M : ℕ) :
    (∑' n : ℕ, crudeAllPTailLowSquare N P M n) =
      ∑ n ∈ Icc 1 M, crudeAllPTailCoefficient N P n ^ 2 := by
  calc
    (∑' n : ℕ, crudeAllPTailLowSquare N P M n) =
        ∑ n ∈ Icc 1 M, crudeAllPTailLowSquare N P M n := by
      apply tsum_eq_sum
      intro n hn
      simp [crudeAllPTailLowSquare, hn]
    _ = ∑ n ∈ Icc 1 M, crudeAllPTailCoefficient N P n ^ 2 := by
      apply Finset.sum_congr rfl
      intro n hn
      simp [crudeAllPTailLowSquare, hn]

/-- The low and high indicators form an exact partition of the full square
coefficient sequence, including the artificially totalized zero frequency. -/
theorem crudeAllPTailCoefficient_sq_eq_low_add_high
    (N P M n : ℕ) :
    crudeAllPTailCoefficient N P n ^ 2 =
      crudeAllPTailLowSquare N P M n +
        crudeAllPTailHighSquare N P M n := by
  by_cases hn0 : n = 0
  · subst n
    simp [crudeAllPTailCoefficient_zero, crudeAllPTailLowSquare,
      crudeAllPTailHighSquare]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    by_cases hnM : n ≤ M
    · have hnmem : n ∈ Icc 1 M := mem_Icc.mpr ⟨hnpos, hnM⟩
      have hnotHigh : ¬M < n := Nat.not_lt.mpr hnM
      simp [crudeAllPTailLowSquare, crudeAllPTailHighSquare, hnmem, hnotHigh]
    · have hhigh : M < n := Nat.lt_of_not_ge hnM
      have hnmem : n ∉ Icc 1 M := by
        intro hmem
        exact hnM (mem_Icc.mp hmem).2
      simp [crudeAllPTailLowSquare, crudeAllPTailHighSquare, hnmem, hhigh]

/-- Square summability of the complete positive-frequency crude tail.  This
is the analytic content needed to synthesize the `p > P` Fourier tail in
circle `L^2`. -/
theorem summable_sq_crudeAllPTailCoefficient
    (N P : ℕ) (hN : 0 < N) (hP : 0 < P) :
    Summable fun n : ℕ ↦ crudeAllPTailCoefficient N P n ^ 2 := by
  let M : ℕ := N * P
  have hM : 0 < M := Nat.mul_pos hN hP
  have hsum := (summable_crudeAllPTailLowSquare N P M).add
    (summable_crudeAllPTailHighSquare N P M hN hM)
  apply hsum.congr
  intro n
  exact (crudeAllPTailCoefficient_sq_eq_low_add_high N P M n).symm

/-- Fully summed positive-frequency estimate for the strict natural tail
`p > P`.  The first term is the low-frequency divisor-square mean; the
second is the rigorously summed high-frequency dyadic envelope. -/
theorem tsum_sq_crudeAllPTailCoefficient_le
    (N P : ℕ) (hN : 0 < N) (hP : 0 < P) :
    (∑' n : ℕ, crudeAllPTailCoefficient N P n ^ 2) ≤
      ((Real.pi ^ 2 / 6) * (2 / (P : ℝ))) ^ 2 *
          (((N * P : ℕ) : ℝ) * (harmonic (N * P) : ℝ) ^ 3) +
        (32 * ((N : ℝ) ^ 2 / ((N * P : ℕ) : ℝ)) *
          (6 + Real.log (((N * P : ℕ) : ℝ))) ^ 5 *
            dyadicFifthMoment) := by
  let M : ℕ := N * P
  have hM : 0 < M := Nat.mul_pos hN hP
  have hlow := summable_crudeAllPTailLowSquare N P M
  have hhigh := summable_crudeAllPTailHighSquare N P M hN hM
  have hdecomp : (fun n : ℕ ↦ crudeAllPTailCoefficient N P n ^ 2) =
      fun n ↦ crudeAllPTailLowSquare N P M n +
        crudeAllPTailHighSquare N P M n := by
    funext n
    exact crudeAllPTailCoefficient_sq_eq_low_add_high N P M n
  rw [hdecomp, hlow.tsum_add hhigh, tsum_crudeAllPTailLowSquare_eq]
  calc
    (∑ n ∈ Icc 1 M, crudeAllPTailCoefficient N P n ^ 2) +
        ∑' n : ℕ, crudeAllPTailHighSquare N P M n ≤
      ((Real.pi ^ 2 / 6) * (2 / (P : ℝ))) ^ 2 *
          ((M : ℝ) * (harmonic M : ℝ) ^ 3) +
        (32 * ((N : ℝ) ^ 2 / (M : ℝ)) *
          (6 + Real.log (M : ℝ)) ^ 5) * dyadicFifthMoment := by
      gcongr
      · simpa only [M] using! sum_sq_crudeAllPTailCoefficient_low_le N P hP
      · exact tsum_crudeAllPTailHighSquare_le N P M hN hM
    _ = ((Real.pi ^ 2 / 6) * (2 / (P : ℝ))) ^ 2 *
          (((N * P : ℕ) : ℝ) * (harmonic (N * P) : ℝ) ^ 3) +
        (32 * ((N : ℝ) ^ 2 / ((N * P : ℕ) : ℝ)) *
          (6 + Real.log (((N * P : ℕ) : ℝ))) ^ 5 *
            dyadicFifthMoment) := by simp only [M]

/-! ## Combining the finite denominator blocks -/

/-- Sum of the first `J` dyadic natural-denominator blocks, beginning just
above `N`. -/
def dyadicDenominatorBlockSumCoefficient (N J n : ℕ) : ℝ :=
  ∑ j ∈ range J,
    naturalDenominatorBlockCoefficient N (2 ^ j * N) n

/-- The dyadic block sum is exactly the natural-denominator interval
`N < p <= 2^J N`; there are neither gaps nor duplicated endpoints. -/
theorem dyadicDenominatorBlockSumCoefficient_eq_interval
    (N J n : ℕ) :
    dyadicDenominatorBlockSumCoefficient N J n =
      ∑ p ∈ Ioc N (2 ^ J * N), naturalDenominatorCoefficientTerm N n p := by
  induction J with
  | zero =>
      simp [dyadicDenominatorBlockSumCoefficient]
  | succ J ih =>
      rw [dyadicDenominatorBlockSumCoefficient, sum_range_succ]
      rw [show (∑ j ∈ range J,
          naturalDenominatorBlockCoefficient N (2 ^ j * N) n) =
          dyadicDenominatorBlockSumCoefficient N J n by rfl]
      rw [ih]
      unfold naturalDenominatorBlockCoefficient
      have hNmid : N ≤ 2 ^ J * N := by
        exact Nat.le_mul_of_pos_left N (pow_pos (by omega) _)
      have hmidUpper : 2 ^ J * N ≤ 2 * (2 ^ J * N) := by omega
      have hdis : Disjoint (Ioc N (2 ^ J * N))
          (Ioc (2 ^ J * N) (2 * (2 ^ J * N))) :=
        Finset.Ioc_disjoint_Ioc_of_le le_rfl
      rw [← Finset.sum_union hdis,
        Finset.Ioc_union_Ioc_eq_Ioc hNmid hmidUpper]
      congr 2
      rw [pow_succ]
      ring

/-- Every block beginning at `2^j N` has the same coarse square-sum bound
once `N > 0`. -/
theorem tsum_sq_dyadicDenominatorBlock_le
    (N j : ℕ) (hN : 0 < N) :
    (∑' n : ℕ,
      naturalDenominatorBlockCoefficient N (2 ^ j * N) n ^ 2) ≤
      80 + 64 * (Real.pi ^ 2 / 6) ^ 2 := by
  have hQ : 0 < 2 ^ j * N := Nat.mul_pos (pow_pos (by omega) _) hN
  have hNQ : (N : ℝ) ≤ ((2 ^ j * N : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_mul_of_pos_left N (pow_pos (by omega) j)
  have hQReal : (0 : ℝ) < ((2 ^ j * N : ℕ) : ℝ) := by
    exact_mod_cast hQ
  calc
    (∑' n : ℕ,
        naturalDenominatorBlockCoefficient N (2 ^ j * N) n ^ 2) ≤
        80 * (N : ℝ) / ((2 ^ j * N : ℕ) : ℝ) +
          64 * (Real.pi ^ 2 / 6) ^ 2 :=
      tsum_sq_naturalDenominatorBlockCoefficient_le N (2 ^ j * N) hN hQ
    _ ≤ 80 + 64 * (Real.pi ^ 2 / 6) ^ 2 := by
      have hratio : (N : ℝ) / ((2 ^ j * N : ℕ) : ℝ) ≤ 1 :=
        (div_le_one hQReal).mpr hNQ
      calc
        80 * (N : ℝ) / ((2 ^ j * N : ℕ) : ℝ) +
            64 * (Real.pi ^ 2 / 6) ^ 2 =
            80 * ((N : ℝ) / ((2 ^ j * N : ℕ) : ℝ)) +
              64 * (Real.pi ^ 2 / 6) ^ 2 := by ring
        _ ≤ 80 * 1 + 64 * (Real.pi ^ 2 / 6) ^ 2 := by gcongr
        _ = 80 + 64 * (Real.pi ^ 2 / 6) ^ 2 := by ring

/-- Finite partial-frequency version of the dyadic denominator Minkowski
bound.  Cauchy--Schwarz is applied pointwise in the block index, after which
the already proved one-block `tsum` estimates are used. -/
theorem sum_range_sq_dyadicDenominatorBlockSumCoefficient_le
    (N J K : ℕ) (hN : 0 < N) :
    (∑ n ∈ range K,
      dyadicDenominatorBlockSumCoefficient N J n ^ 2) ≤
      (J : ℝ) ^ 2 * (80 + 64 * (Real.pi ^ 2 / 6) ^ 2) := by
  let C : ℝ := 80 + 64 * (Real.pi ^ 2 / 6) ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    (∑ n ∈ range K,
        dyadicDenominatorBlockSumCoefficient N J n ^ 2) ≤
        ∑ n ∈ range K, (J : ℝ) *
          ∑ j ∈ range J,
            naturalDenominatorBlockCoefficient N (2 ^ j * N) n ^ 2 := by
      apply Finset.sum_le_sum
      intro n _hn
      simpa only [dyadicDenominatorBlockSumCoefficient, card_range,
        Nat.cast_id] using!
        (sq_sum_le_card_mul_sum_sq
          (s := range J)
          (f := fun j ↦ naturalDenominatorBlockCoefficient N (2 ^ j * N) n))
    _ = (J : ℝ) * ∑ j ∈ range J, ∑ n ∈ range K,
          naturalDenominatorBlockCoefficient N (2 ^ j * N) n ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (J : ℝ) * ∑ _j ∈ range J, C := by
      gcongr with j hj
      have hQ : 0 < 2 ^ j * N := Nat.mul_pos (pow_pos (by omega) _) hN
      calc
        (∑ n ∈ range K,
            naturalDenominatorBlockCoefficient N (2 ^ j * N) n ^ 2) ≤
            ∑' n : ℕ,
              naturalDenominatorBlockCoefficient N (2 ^ j * N) n ^ 2 := by
          exact (summable_sq_naturalDenominatorBlockCoefficient
            N (2 ^ j * N) hN hQ).sum_le_tsum (range K)
              (fun n _hn ↦ sq_nonneg _)
        _ ≤ C := by
          exact tsum_sq_dyadicDenominatorBlock_le N j hN
    _ = (J : ℝ) ^ 2 * (80 + 64 * (Real.pi ^ 2 / 6) ^ 2) := by
      simp only [sum_const, card_range, nsmul_eq_mul, C]
      ring

/-- Square summability of a finite family of dyadic denominator blocks. -/
theorem summable_sq_dyadicDenominatorBlockSumCoefficient
    (N J : ℕ) (hN : 0 < N) :
    Summable fun n : ℕ ↦
      dyadicDenominatorBlockSumCoefficient N J n ^ 2 := by
  apply summable_of_sum_range_le (fun n ↦ sq_nonneg _)
  intro K
  exact sum_range_sq_dyadicDenominatorBlockSumCoefficient_le N J K hN

/-- Fully summed coefficient-space form of the finite natural-denominator
cutoff estimate.  Its square-root is `O(J)`; in the manuscript one takes
`J = O(log log N)`. -/
theorem tsum_sq_dyadicDenominatorBlockSumCoefficient_le
    (N J : ℕ) (hN : 0 < N) :
    (∑' n : ℕ,
      dyadicDenominatorBlockSumCoefficient N J n ^ 2) ≤
      (J : ℝ) ^ 2 * (80 + 64 * (Real.pi ^ 2 / 6) ^ 2) := by
  apply Real.tsum_le_of_sum_range_le (fun n ↦ sq_nonneg _)
  intro K
  exact sum_range_sq_dyadicDenominatorBlockSumCoefficient_le N J K hN

/-! ## Literal circle `L²` synthesis -/

/-- Norm identity for a summable orthogonal family, stated in the form used
below.  It follows by taking limits in the finite Pythagorean identity. -/
theorem norm_sq_tsum_orthogonalFamily
    {ι E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {V : ι → ℂ →ₗᵢ[ℂ] E}
    (hV : OrthogonalFamily ℂ (fun _ : ι ↦ ℂ) V)
    (f : ι → ℂ) (hf : Summable fun i ↦ ‖f i‖ ^ 2) :
    ‖∑' i : ι, V i (f i)‖ ^ 2 = ∑' i : ι, ‖f i‖ ^ 2 := by
  have hs : Summable fun i ↦ V i (f i) :=
    (hV.summable_iff_norm_sq_summable f).mpr hf
  have hleft := hs.hasSum
  change Filter.Tendsto
      (fun s : Finset ι ↦ ∑ i ∈ s, V i (f i)) Filter.atTop
        (nhds (∑' i : ι, V i (f i))) at hleft
  have hleftNorm := hleft.norm.pow 2
  have hright := hf.hasSum
  change Filter.Tendsto
      (fun s : Finset ι ↦ ∑ i ∈ s, ‖f i‖ ^ 2) Filter.atTop
        (nhds (∑' i : ι, ‖f i‖ ^ 2)) at hright
  have hrightNorm : Filter.Tendsto
      (fun s : Finset ι ↦ ‖∑ i ∈ s, V i (f i)‖ ^ 2) Filter.atTop
        (nhds (∑' i : ι, ‖f i‖ ^ 2)) := by
    apply hright.congr
    intro s
    exact (hV.norm_sum f s).symm
  exact tendsto_nhds_unique hleftNorm hrightNorm

/-- Integer mode map containing every nonzero frequency exactly once. -/
def signedNonzeroMode : ℕ ⊕ ℕ → ℤ
  | Sum.inl n => (n + 1 : ℕ)
  | Sum.inr n => -((n + 1 : ℕ) : ℤ)

theorem signedNonzeroMode_injective : Function.Injective signedNonzeroMode := by
  intro a b hab
  rcases a with a | a <;> rcases b with b | b <;>
    simp only [signedNonzeroMode, Sum.inl.injEq, Sum.inr.injEq] at hab ⊢ <;>
    omega

/-- Universal normalization of a positive natural-denominator coefficient. -/
def naturalCoefficientNormalization : ℂ :=
  -Complex.I / (2 * (Real.pi : ℂ))

theorem norm_naturalCoefficientNormalization_le_one :
    ‖naturalCoefficientNormalization‖ ≤ 1 := by
  unfold naturalCoefficientNormalization
  rw [Complex.norm_div, norm_neg, Complex.norm_I, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  norm_num
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by
    linarith [Real.pi_gt_three]
  calc
    Real.pi⁻¹ * (1 / 2 : ℝ) = 1 / (2 * Real.pi) := by
      field_simp [Real.pi_ne_zero]
    _ ≤ 1 := (div_le_one (by positivity : (0 : ℝ) < 2 * Real.pi)).mpr hpi

/-- Signed normalized coefficient of the strict natural tail.  The negative
mode is the complex conjugate of the positive mode. -/
def strictNaturalTailScalar (N P : ℕ) : ℕ ⊕ ℕ → ℂ
  | Sum.inl n => naturalCoefficientNormalization *
      (crudeAllPTailCoefficient N P (n + 1) : ℂ)
  | Sum.inr n => starRingEnd ℂ
      (naturalCoefficientNormalization *
        (crudeAllPTailCoefficient N P (n + 1) : ℂ))

/-- The scalar square is dominated by the unnormalized real coefficient
square. -/
theorem norm_sq_strictNaturalTailScalar_le
    (N P : ℕ) (i : ℕ ⊕ ℕ) :
    ‖strictNaturalTailScalar N P i‖ ^ 2 ≤
      crudeAllPTailCoefficient N P (Sum.elim id id i + 1) ^ 2 := by
  rcases i with n | n <;>
    simp only [strictNaturalTailScalar, Sum.elim_inl, Sum.elim_inr,
      Complex.norm_conj, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  all_goals
    have hK := norm_naturalCoefficientNormalization_le_one
    have hA : 0 ≤ |crudeAllPTailCoefficient N P (n + 1)| := abs_nonneg _
    calc
      (‖naturalCoefficientNormalization‖ *
          |crudeAllPTailCoefficient N P (n + 1)|) ^ 2 ≤
          (1 * |crudeAllPTailCoefficient N P (n + 1)|) ^ 2 := by
        gcongr
      _ = crudeAllPTailCoefficient N P (n + 1) ^ 2 := by
        rw [one_mul, sq_abs]

/-- The real square majorant on the signed nonzero modes. -/
def strictNaturalTailSquareMajorant (N P : ℕ) : ℕ ⊕ ℕ → ℝ
  | Sum.inl n => crudeAllPTailCoefficient N P (n + 1) ^ 2
  | Sum.inr n => crudeAllPTailCoefficient N P (n + 1) ^ 2

theorem summable_strictNaturalTailSquareMajorant
    (N P : ℕ) (hN : 0 < N) (hP : 0 < P) :
    Summable (strictNaturalTailSquareMajorant N P) := by
  have hbase := summable_sq_crudeAllPTailCoefficient N P hN hP
  have hshift : Summable fun n : ℕ ↦
      crudeAllPTailCoefficient N P (n + 1) ^ 2 := by
    simpa only [Function.comp_apply] using!
      hbase.comp_injective Nat.succ_injective
  exact Summable.sum (strictNaturalTailSquareMajorant N P)
    (by simpa only [Function.comp_apply, strictNaturalTailSquareMajorant] using! hshift)
    (by simpa only [Function.comp_apply, strictNaturalTailSquareMajorant] using! hshift)

theorem summable_norm_sq_strictNaturalTailScalar
    (N P : ℕ) (hN : 0 < N) (hP : 0 < P) :
    Summable fun i : ℕ ⊕ ℕ ↦ ‖strictNaturalTailScalar N P i‖ ^ 2 := by
  have hmajor : Summable fun i : ℕ ⊕ ℕ ↦
      crudeAllPTailCoefficient N P (Sum.elim id id i + 1) ^ 2 := by
    apply (summable_strictNaturalTailSquareMajorant N P hN hP).congr
    intro i
    rcases i with n | n <;> rfl
  apply Summable.of_nonneg_of_le
    (fun i ↦ sq_nonneg ‖strictNaturalTailScalar N P i‖)
    (fun i ↦ norm_sq_strictNaturalTailScalar_le N P i)
    hmajor

theorem orthonormal_signedNonzeroFourier :
    Orthonormal ℂ
      (fun i : ℕ ⊕ ℕ ↦
        (fourierLp 2 (signedNonzeroMode i) : UnitCircleL2)) := by
  simpa only [Function.comp_apply] using!
    (orthonormal_fourier.comp signedNonzeroMode signedNonzeroMode_injective)

/-- One signed Fourier term of the strict natural-denominator tail. -/
def strictNaturalTailFourierTerm (N P : ℕ) (i : ℕ ⊕ ℕ) :
    UnitCircleL2 :=
  strictNaturalTailScalar N P i • fourierLp 2 (signedNonzeroMode i)

theorem summable_strictNaturalTailFourierTerm
    (N P : ℕ) (hN : 0 < N) (hP : 0 < P) :
    Summable (strictNaturalTailFourierTerm N P) := by
  let V : ∀ _i : ℕ ⊕ ℕ, ℂ →ₗᵢ[ℂ] UnitCircleL2 :=
    fun i ↦ LinearIsometry.toSpanSingleton ℂ UnitCircleL2
      (orthonormal_signedNonzeroFourier.1 i)
  have hV : OrthogonalFamily ℂ (fun _ : ℕ ⊕ ℕ ↦ ℂ) V :=
    orthonormal_signedNonzeroFourier.orthogonalFamily
  have hs : Summable fun i ↦ V i (strictNaturalTailScalar N P i) :=
    (hV.summable_iff_norm_sq_summable (strictNaturalTailScalar N P)).mpr
      (summable_norm_sq_strictNaturalTailScalar N P hN hP)
  apply hs.congr
  intro i
  rw [show V i (strictNaturalTailScalar N P i) =
      strictNaturalTailScalar N P i •
        (fourierLp 2 (signedNonzeroMode i) : UnitCircleL2) by
      exact LinearIsometry.toSpanSingleton_apply _ _]
  rfl

/-- Literal circle `L²` class synthesized from all positive and negative
Fourier modes of the strict tail `p > P`. -/
def strictNaturalTailL2 (N P : ℕ) : UnitCircleL2 :=
  ∑' i : ℕ ⊕ ℕ, strictNaturalTailFourierTerm N P i

/-- Parseval/Pythagoras identity for the synthesized strict tail. -/
theorem norm_sq_strictNaturalTailL2_eq
    (N P : ℕ) (hN : 0 < N) (hP : 0 < P) :
    ‖strictNaturalTailL2 N P‖ ^ 2 =
      ∑' i : ℕ ⊕ ℕ, ‖strictNaturalTailScalar N P i‖ ^ 2 := by
  let V : ∀ _i : ℕ ⊕ ℕ, ℂ →ₗᵢ[ℂ] UnitCircleL2 :=
    fun i ↦ LinearIsometry.toSpanSingleton ℂ UnitCircleL2
      (orthonormal_signedNonzeroFourier.1 i)
  have hV : OrthogonalFamily ℂ (fun _ : ℕ ⊕ ℕ ↦ ℂ) V :=
    orthonormal_signedNonzeroFourier.orthogonalFamily
  have hnorm := norm_sq_tsum_orthogonalFamily hV
    (strictNaturalTailScalar N P)
    (summable_norm_sq_strictNaturalTailScalar N P hN hP)
  have hterm : ∀ i : ℕ ⊕ ℕ,
      V i (strictNaturalTailScalar N P i) =
        strictNaturalTailFourierTerm N P i := by
    intro i
    rw [show V i (strictNaturalTailScalar N P i) =
        strictNaturalTailScalar N P i •
          (fourierLp 2 (signedNonzeroMode i) : UnitCircleL2) by
        exact LinearIsometry.toSpanSingleton_apply _ _]
    rfl
  rw [strictNaturalTailL2, ← tsum_congr hterm]
  exact hnorm

/-- The signed `L²` norm costs at most two copies of the positive-frequency
coefficient square sum. -/
theorem norm_sq_strictNaturalTailL2_le_positive_tsum
    (N P : ℕ) (hN : 0 < N) (hP : 0 < P) :
    ‖strictNaturalTailL2 N P‖ ^ 2 ≤
      2 * (∑' n : ℕ, crudeAllPTailCoefficient N P n ^ 2) := by
  have hbase := summable_sq_crudeAllPTailCoefficient N P hN hP
  have hshift : Summable fun n : ℕ ↦
      crudeAllPTailCoefficient N P (n + 1) ^ 2 := by
    simpa only [Function.comp_apply] using!
      hbase.comp_injective Nat.succ_injective
  have hmajor := summable_strictNaturalTailSquareMajorant N P hN hP
  have hscalar := summable_norm_sq_strictNaturalTailScalar N P hN hP
  have hpoint : ∀ i : ℕ ⊕ ℕ,
      ‖strictNaturalTailScalar N P i‖ ^ 2 ≤
        strictNaturalTailSquareMajorant N P i := by
    intro i
    rcases i with n | n
    · simpa only [strictNaturalTailSquareMajorant, Sum.elim_inl, id_eq]
        using! norm_sq_strictNaturalTailScalar_le N P (Sum.inl n)
    · simpa only [strictNaturalTailSquareMajorant, Sum.elim_inr, id_eq]
        using! norm_sq_strictNaturalTailScalar_le N P (Sum.inr n)
  have hscalarMajor :
      (∑' i : ℕ ⊕ ℕ, ‖strictNaturalTailScalar N P i‖ ^ 2) ≤
        ∑' i : ℕ ⊕ ℕ, strictNaturalTailSquareMajorant N P i :=
    Summable.tsum_le_tsum hpoint hscalar hmajor
  let T : ℝ := ∑' n : ℕ, crudeAllPTailCoefficient N P (n + 1) ^ 2
  have hleft : HasSum
      (strictNaturalTailSquareMajorant N P ∘ Sum.inl) T := by
    simpa only [strictNaturalTailSquareMajorant, Function.comp_apply, T] using!
      hshift.hasSum
  have hright : HasSum
      (strictNaturalTailSquareMajorant N P ∘ Sum.inr) T := by
    simpa only [strictNaturalTailSquareMajorant, Function.comp_apply, T] using!
      hshift.hasSum
  have hmajorEq :
      (∑' i : ℕ ⊕ ℕ, strictNaturalTailSquareMajorant N P i) = T + T :=
    (hleft.sum hright).tsum_eq
  have hshiftLe : T ≤
      ∑' n : ℕ, crudeAllPTailCoefficient N P n ^ 2 := by
    simpa only [Function.comp_apply, T] using!
      tsum_comp_le_tsum_of_inj hbase (fun n ↦ sq_nonneg _)
        Nat.succ_injective
  rw [norm_sq_strictNaturalTailL2_eq N P hN hP]
  rw [hmajorEq] at hscalarMajor
  linarith

/-- Explicit literal `L²` estimate for the strict natural-denominator tail,
obtained by combining Parseval with the low/high coefficient estimate. -/
theorem norm_sq_strictNaturalTailL2_le
    (N P : ℕ) (hN : 0 < N) (hP : 0 < P) :
    ‖strictNaturalTailL2 N P‖ ^ 2 ≤
      2 *
        (((Real.pi ^ 2 / 6) * (2 / (P : ℝ))) ^ 2 *
            (((N * P : ℕ) : ℝ) * (harmonic (N * P) : ℝ) ^ 3) +
          (32 * ((N : ℝ) ^ 2 / ((N * P : ℕ) : ℝ)) *
            (6 + Real.log (((N * P : ℕ) : ℝ))) ^ 5 *
              dyadicFifthMoment)) := by
  exact (norm_sq_strictNaturalTailL2_le_positive_tsum N P hN hP).trans
    (mul_le_mul_of_nonneg_left
      (tsum_sq_crudeAllPTailCoefficient_le N P hN hP) (by norm_num))

/-- At every positive frequency, the synthesized `L²` tail has exactly the
strict natural-denominator coefficient.  The proof maps the summable
orthogonal series through the continuous Fourier-coefficient functional and
then isolates the unique matching signed mode. -/
theorem fourierCoeff_strictNaturalTailL2_pos
    (N P n : ℕ) (hN : 0 < N) (hP : 0 < P) (hn : 0 < n) :
    fourierCoeff
        (strictNaturalTailL2 N P : AddCircle (1 : ℝ) → ℂ) (n : ℤ) =
      naturalCoefficientNormalization *
        (crudeAllPTailCoefficient N P n : ℂ) := by
  let i₀ : ℕ ⊕ ℕ := Sum.inl (n - 1)
  have hi₀mode : signedNonzeroMode i₀ = (n : ℤ) := by
    dsimp [i₀, signedNonzeroMode]
    exact_mod_cast Nat.sub_add_cancel hn
  have hi₀scalar : strictNaturalTailScalar N P i₀ =
      naturalCoefficientNormalization *
        (crudeAllPTailCoefficient N P n : ℂ) := by
    dsimp [i₀, strictNaturalTailScalar]
    rw [Nat.sub_add_cancel hn]
  let g : ℕ ⊕ ℕ → ℂ := fun i ↦
    fourierCoefficientCLM (n : ℤ) (strictNaturalTailFourierTerm N P i)
  have hg (i : ℕ ⊕ ℕ) :
      g i = if i = i₀ then strictNaturalTailScalar N P i₀ else 0 := by
    by_cases hi : i = i₀
    · subst i
      simp only [g, strictNaturalTailFourierTerm, map_smul,
        fourierCoefficientCLM_apply, fourierCoeff_fourierLp, smul_eq_mul]
      rw [hi₀mode]
      simp
    · have hmode : signedNonzeroMode i ≠ (n : ℤ) := by
        intro h
        apply hi
        apply signedNonzeroMode_injective
        exact h.trans hi₀mode.symm
      simp only [g, strictNaturalTailFourierTerm, map_smul,
        fourierCoefficientCLM_apply, fourierCoeff_fourierLp, smul_eq_mul]
      rw [if_neg hmode.symm, if_neg hi]
      ring
  have hmapped : HasSum g
      (fourierCoefficientCLM (n : ℤ) (strictNaturalTailL2 N P)) := by
    have h := (fourierCoefficientCLM (n : ℤ)).hasSum
      (summable_strictNaturalTailFourierTerm N P hN hP).hasSum
    simpa only [g, strictNaturalTailL2] using! h
  have hone : HasSum g (strictNaturalTailScalar N P i₀) := by
    exact (hasSum_ite_eq i₀ (strictNaturalTailScalar N P i₀)).congr_fun
      hg
  have hunique := hmapped.unique hone
  rw [fourierCoefficientCLM_apply] at hunique
  exact hunique.trans hi₀scalar

/-- The preceding coefficient is the original strict `p > P` natural sum,
not merely its divisor--Möbius rewrite. -/
theorem fourierCoeff_strictNaturalTailL2_pos_eq_naturalTail
    (N P n : ℕ) (hN : 0 < N) (hP : 0 < P) (hn : 0 < n) :
    fourierCoeff
        (strictNaturalTailL2 N P : AddCircle (1 : ℝ) → ℂ) (n : ℤ) =
      naturalCoefficientNormalization *
        (naturalDenominatorTailCoefficient N P n : ℂ) := by
  rw [fourierCoeff_strictNaturalTailL2_pos N P n hN hP hn,
    naturalDenominatorTailCoefficient_eq_crudeAllP N P n hn.ne']

/-- Raw coefficient contributed by the finite set of positive denominators
`p <= P`.  The subtype spelling makes the endpoint and positivity literal. -/
def naturalDenominatorPrefixCoefficient (N P n : ℕ) : ℝ :=
  ∑' p : {p : ℕ+ // (p : ℕ) ≤ P},
    naturalDenominatorCoefficientTerm N n (p : ℕ+)

/-- Normalized positive Fourier coefficient of the finite natural cutoff. -/
def finiteNaturalDenominatorPositiveCoefficient (N P n : ℕ) : ℂ :=
  naturalCoefficientNormalization *
    (naturalDenominatorPrefixCoefficient N P n : ℂ)

/-- The complementary subtype sum is exactly the strict-tail definition. -/
theorem tsum_naturalDenominator_compl_eq_tail
    (N P n : ℕ) :
    (∑' p : {p : ℕ+ // ¬((p : ℕ+) : ℕ) ≤ P},
      naturalDenominatorCoefficientTerm N n (p : ℕ+)) =
      naturalDenominatorTailCoefficient N P n := by
  let S : Set ℕ+ := {p | (p : ℕ) ≤ P}
  calc
    (∑' p : {p : ℕ+ // ¬((p : ℕ+) : ℕ) ≤ P},
        naturalDenominatorCoefficientTerm N n (p : ℕ+)) =
        ∑' p : ↥(Sᶜ),
          naturalDenominatorCoefficientTerm N n (p : ℕ+) := by rfl
    _ = ∑' p : ℕ+, Sᶜ.indicator
          (fun q ↦ naturalDenominatorCoefficientTerm N n (q : ℕ)) p :=
      tsum_subtype Sᶜ
        (fun q ↦ naturalDenominatorCoefficientTerm N n (q : ℕ))
    _ = naturalDenominatorTailCoefficient N P n := by
      unfold naturalDenominatorTailCoefficient
      apply tsum_congr
      intro p
      by_cases hp : P < (p : ℕ)
      · have hpS : p ∉ S := by simpa only [S, Set.mem_setOf_eq, not_le] using! hp
        have hpSc : p ∈ Sᶜ := hpS
        rw [Set.indicator_of_mem hpSc, if_pos hp]
      · have hpS : p ∈ S := by
          simpa only [S, Set.mem_setOf_eq] using! Nat.le_of_not_gt hp
        have hpSc : p ∉ Sᶜ := by simpa
        rw [Set.indicator_of_notMem hpSc, if_neg hp]

/-- Exact partition of the all-denominator coefficient into `p <= P` and
`p > P`. -/
theorem allDenominatorPositiveCoefficient_eq_finite_add_tail
    (N P n : ℕ) (hn : n ≠ 0) :
    allDenominatorPositiveCoefficient N n =
      finiteNaturalDenominatorPositiveCoefficient N P n +
        naturalCoefficientNormalization *
          (naturalDenominatorTailCoefficient N P n : ℂ) := by
  let f : ℕ+ → ℝ := fun p ↦
    naturalDenominatorCoefficientTerm N n (p : ℕ)
  let S : Set ℕ+ := {p | (p : ℕ) ≤ P}
  have hf : Summable f := by
    exact summable_naturalDenominatorCoefficientTerm N n hn
  have hs : Summable (f ∘ Subtype.val : S → ℝ) := hf.subtype S
  have hsc : Summable (f ∘ Subtype.val : ↥(Sᶜ) → ℝ) := hf.subtype Sᶜ
  have hsplit :
      naturalDenominatorPrefixCoefficient N P n +
        naturalDenominatorTailCoefficient N P n = ∑' p : ℕ+, f p := by
    have h := hs.tsum_add_tsum_compl hsc
    rw [show (∑' p : S, f p) =
        naturalDenominatorPrefixCoefficient N P n by rfl] at h
    rw [show (∑' p : ↥(Sᶜ), f p) =
        naturalDenominatorTailCoefficient N P n by
          simpa only [f, S] using! tsum_naturalDenominator_compl_eq_tail N P n] at h
    exact h
  have hraw :
      (∑' p : ℕ+,
        ((ramanujanSum (p : ℕ) (n : ℤ)).re / (p : ℝ) ^ 2) *
          hStarRatio n ((p : ℕ) * N) : ℝ) = ∑' p : ℕ+, f p := by
    apply tsum_congr
    intro p
    rfl
  have hsplitC := congrArg (fun x : ℝ ↦ (x : ℂ)) hsplit
  change
    ((naturalDenominatorPrefixCoefficient N P n +
      naturalDenominatorTailCoefficient N P n : ℝ) : ℂ) =
      ((∑' p : ℕ+, f p : ℝ) : ℂ) at hsplitC
  unfold allDenominatorPositiveCoefficient
  rw [hraw]
  unfold finiteNaturalDenominatorPositiveCoefficient
  rw [show naturalCoefficientNormalization =
      -Complex.I / (2 * (Real.pi : ℂ)) by rfl]
  rw [← hsplitC]
  push_cast
  ring

/-- The natural-denominator reconstruction truncated at `P`, defined as an
actual circle `L²` class. -/
def naturalCutoffReconstructionL2 (N : ℕ+) (P : ℕ) : UnitCircleL2 :=
  allDenominatorReconstructionL2 N - strictNaturalTailL2 (N : ℕ) P

/-- Positive Fourier coefficient of the literal finite-cutoff `L²` class. -/
theorem fourierCoeff_naturalCutoffReconstructionL2_pos
    (N : ℕ+) (P n : ℕ) (hP : 0 < P) (hn : 0 < n) :
    fourierCoeff
        (naturalCutoffReconstructionL2 N P : AddCircle (1 : ℝ) → ℂ)
          (n : ℤ) =
      allDenominatorPositiveCoefficient (N : ℕ) n -
        naturalCoefficientNormalization *
          (crudeAllPTailCoefficient (N : ℕ) P n : ℂ) := by
  rw [← fourierCoefficientCLM_apply]
  simp only [naturalCutoffReconstructionL2, map_sub,
    fourierCoefficientCLM_apply]
  rw [fourierCoeff_allDenominatorReconstructionL2 N n hn.ne',
    fourierCoeff_strictNaturalTailL2_pos (N : ℕ) P n N.pos hP hn]

/-- The positive Fourier coefficient of the literal cutoff is exactly the
finite natural-denominator sum `p <= P`. -/
theorem fourierCoeff_naturalCutoffReconstructionL2_pos_eq_finite
    (N : ℕ+) (P n : ℕ) (hP : 0 < P) (hn : 0 < n) :
    fourierCoeff
        (naturalCutoffReconstructionL2 N P : AddCircle (1 : ℝ) → ℂ)
          (n : ℤ) =
      finiteNaturalDenominatorPositiveCoefficient (N : ℕ) P n := by
  rw [fourierCoeff_naturalCutoffReconstructionL2_pos N P n hP hn]
  rw [← naturalDenominatorTailCoefficient_eq_crudeAllP
    (N : ℕ) P n hn.ne']
  rw [allDenominatorPositiveCoefficient_eq_finite_add_tail
    (N : ℕ) P n hn.ne']
  ring

/-- The finite-cutoff reconstruction differs from the exact all-denominator
reconstruction by precisely the synthesized strict tail. -/
theorem allDenominatorReconstructionL2_sub_naturalCutoffReconstructionL2
    (N : ℕ+) (P : ℕ) :
    allDenominatorReconstructionL2 N - naturalCutoffReconstructionL2 N P =
      strictNaturalTailL2 (N : ℕ) P := by
  unfold naturalCutoffReconstructionL2
  abel

/-- Literal `L²` natural-cutoff error bound. -/
theorem norm_sq_allDenominator_sub_naturalCutoffReconstructionL2_le
    (N : ℕ+) (P : ℕ) (hP : 0 < P) :
    ‖allDenominatorReconstructionL2 N - naturalCutoffReconstructionL2 N P‖ ^ 2 ≤
      2 *
        (((Real.pi ^ 2 / 6) * (2 / (P : ℝ))) ^ 2 *
            ((((N : ℕ) * P : ℕ) : ℝ) *
              (harmonic ((N : ℕ) * P) : ℝ) ^ 3) +
          (32 * (((N : ℕ) : ℝ) ^ 2 /
              (((N : ℕ) * P : ℕ) : ℝ)) *
            (6 + Real.log ((((N : ℕ) * P : ℕ) : ℝ))) ^ 5 *
              dyadicFifthMoment)) := by
  rw [allDenominatorReconstructionL2_sub_naturalCutoffReconstructionL2]
  exact norm_sq_strictNaturalTailL2_le (N : ℕ) P N.pos hP

end

end Erdos1002
