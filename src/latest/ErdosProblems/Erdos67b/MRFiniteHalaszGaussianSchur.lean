import ErdosProblems.Erdos67b.MRFiniteHalaszGaussianMean

/-!
# A Schur bound for the finite Gaussian Halasz majorant

The Gaussian mean-square identity retains the decay between distinct
logarithmic coefficient shells.  This file records a finite block Schur
test and then specializes it to dyadic logarithmic shells.  In contrast
to pointwise triangle inequality, the resulting loss is a universal row
sum, not the square of the number of shells.
-/

open scoped BigOperators
open Complex Finset

namespace Erdos67b.MRHalaszBands

noncomputable section

open Erdos67b

/-- A block form of the finite Gaussian pair majorant. -/
def finiteHalaszGaussianBlockPairMajorant
    {ι : Type*} [Fintype ι] {κ : ι → Type*} [(i : ι) → Fintype (κ i)]
    (freq : (i : ι) → κ i → ℝ) (a : (i : ι) → κ i → ℂ) (b : ℝ) : ℝ :=
  Real.sqrt (Real.pi / b) *
    ∑ i, ∑ x, ∑ j, ∑ y,
      ‖a i x‖ * ‖a j y‖ *
        finiteHalaszGaussianPairKernel b (freq j y - freq i x)

/-- Flattening a finite family of blocks does not alter the Gaussian pair
majorant. -/
theorem finiteHalaszGaussianPairMajorant_sigma_eq_block
    {ι : Type*} [Fintype ι] {κ : ι → Type*} [(i : ι) → Fintype (κ i)]
    (freq : (i : ι) → κ i → ℝ) (a : (i : ι) → κ i → ℂ) (b : ℝ) :
    finiteHalaszGaussianPairMajorant
        (fun z : Sigma κ ↦ freq z.1 z.2)
        (fun z : Sigma κ ↦ a z.1 z.2) b =
      finiteHalaszGaussianBlockPairMajorant freq a b := by
  unfold finiteHalaszGaussianPairMajorant finiteHalaszGaussianBlockPairMajorant
  congr 1
  rw [Fintype.sum_sigma]
  simp_rw [Fintype.sum_sigma]

/-- Purely finite Schur test.  `B i` bounds the squared `L¹` mass of block
`i`, while `K i j` bounds every Gaussian interaction between blocks `i`
and `j`. -/
theorem finiteHalaszGaussianBlockPairMajorant_le_schur
    {ι : Type*} [Fintype ι] {κ : ι → Type*} [(i : ι) → Fintype (κ i)]
    (freq : (i : ι) → κ i → ℝ) (a : (i : ι) → κ i → ℂ)
    {b C : ℝ} (K : ι → ι → ℝ) (B : ι → ℝ)
    (hK0 : ∀ i j, 0 ≤ K i j)
    (hKsymm : ∀ i j, K i j = K j i)
    (hkernel : ∀ i x j y,
      finiteHalaszGaussianPairKernel b (freq j y - freq i x) ≤ K i j)
    (hcross : ∀ i j,
      (∑ x, ‖a i x‖) * (∑ y, ‖a j y‖) ≤ (B i + B j) / 2)
    (hrow : ∀ i, ∑ j, K i j ≤ C) :
    finiteHalaszGaussianBlockPairMajorant freq a b ≤
      Real.sqrt (Real.pi / b) * (C * ∑ i, B i) := by
  unfold finiteHalaszGaussianBlockPairMajorant
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  calc
    (∑ i, ∑ x, ∑ j, ∑ y,
        ‖a i x‖ * ‖a j y‖ *
          finiteHalaszGaussianPairKernel b (freq j y - freq i x)) ≤
        ∑ i, ∑ j,
          ((∑ x, ‖a i x‖) * (∑ y, ‖a j y‖)) * K i j := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        (∑ x, ∑ j, ∑ y,
            ‖a i x‖ * ‖a j y‖ *
              finiteHalaszGaussianPairKernel b (freq j y - freq i x)) =
            ∑ j, ∑ x, ∑ y,
              ‖a i x‖ * ‖a j y‖ *
                finiteHalaszGaussianPairKernel b (freq j y - freq i x) := by
          rw [Finset.sum_comm]
        _ ≤ ∑ j, ((∑ x, ‖a i x‖) * (∑ y, ‖a j y‖)) * K i j := by
          apply Finset.sum_le_sum
          intro j hj
          calc
            (∑ x, ∑ y,
                ‖a i x‖ * ‖a j y‖ *
                  finiteHalaszGaussianPairKernel b (freq j y - freq i x)) ≤
                ∑ x, ∑ y, (‖a i x‖ * ‖a j y‖) * K i j := by
              apply Finset.sum_le_sum
              intro x hx
              apply Finset.sum_le_sum
              intro y hy
              exact mul_le_mul_of_nonneg_left (hkernel i x j y)
                (mul_nonneg (norm_nonneg _) (norm_nonneg _))
            _ = ((∑ x, ‖a i x‖) * (∑ y, ‖a j y‖)) * K i j := by
              rw [Finset.sum_mul_sum]
              simp_rw [mul_assoc]
              rw [Finset.sum_mul]
              simp_rw [Finset.sum_mul]
              simp only [mul_assoc]
    _ ≤ ∑ i, ∑ j, ((B i + B j) / 2) * K i j := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right (hcross i j) (hK0 i j)
    _ = ∑ i, B i * ∑ j, K i j := by
      have hfirst :
          (∑ i, ∑ j, B i * K i j) = ∑ i, B i * ∑ j, K i j := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (Finset.mul_sum Finset.univ (fun j ↦ K i j) (B i)).symm
      have hswap :
          (∑ i, ∑ j, B j * K i j) = ∑ i, B i * ∑ j, K i j := by
        calc
          (∑ i, ∑ j, B j * K i j) = ∑ j, ∑ i, B j * K i j := by
            rw [Finset.sum_comm]
          _ = ∑ j, B j * ∑ i, K i j := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.mul_sum]
          _ = ∑ j, B j * ∑ i, K j i := by
            apply Finset.sum_congr rfl
            intro j hj
            congr 1
            apply Finset.sum_congr rfl
            intro i hi
            exact hKsymm i j
          _ = ∑ i, B i * ∑ j, K i j := rfl
      have hpoint : ∀ i j,
          ((B i + B j) / 2) * K i j =
            (B i * K i j + B j * K i j) / 2 := by
        intro i j
        ring
      have hsum_div (F : ι → ι → ℝ) :
          (∑ i, ∑ j, F i j / 2) = (∑ i, ∑ j, F i j) / 2 := by
        calc
          (∑ i, ∑ j, F i j / 2) = ∑ i, (∑ j, F i j) / 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            exact (Finset.sum_div Finset.univ (fun j ↦ F i j) 2).symm
          _ = (∑ i, ∑ j, F i j) / 2 :=
            (Finset.sum_div Finset.univ (fun i ↦ ∑ j, F i j) 2).symm
      calc
        (∑ i, ∑ j, ((B i + B j) / 2) * K i j) =
            ∑ i, ∑ j, (B i * K i j + B j * K i j) / 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          exact hpoint i j
        _ = ((∑ i, ∑ j, B i * K i j) +
              (∑ i, ∑ j, B j * K i j)) / 2 := by
          rw [hsum_div]
          congr 1
          simp only [Finset.sum_add_distrib]
        _ = ∑ i, B i * ∑ j, K i j := by
          rw [hfirst, hswap]
          ring
    _ ≤ ∑ i, B i * C := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hrow i) (by
        have h := hcross i i
        have hsum0 : 0 ≤ ∑ x, ‖a i x‖ := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
        nlinarith [sq_nonneg (∑ x, ‖a i x‖)])
    _ = C * ∑ i, B i := by
      rw [← Finset.sum_mul]
      ring

/-! ## Dyadic logarithmic shell kernel -/

/-- The guaranteed logarithmic separation between dyadic shells.  The
subtraction by one accounts for their adjacent endpoints. -/
def finiteHalaszDyadicShellGap (j k : ℕ) : ℝ :=
  ((Nat.dist j k - 1 : ℕ) : ℝ) * Real.log 2

/-- Gaussian interaction assigned to a pair of dyadic shells. -/
def finiteHalaszDyadicShellKernel (T : ℝ) (j k : ℕ) : ℝ :=
  finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
    (finiteHalaszDyadicShellGap j k)

theorem finiteHalaszDyadicShellKernel_nonneg (T : ℝ) (j k : ℕ) :
    0 ≤ finiteHalaszDyadicShellKernel T j k :=
  finiteHalaszGaussianPairKernel_nonneg _ _

theorem finiteHalaszDyadicShellKernel_symm (T : ℝ) (j k : ℕ) :
    finiteHalaszDyadicShellKernel T j k =
      finiteHalaszDyadicShellKernel T k j := by
  unfold finiteHalaszDyadicShellKernel finiteHalaszDyadicShellGap
  rw [Nat.dist_comm]

/-- A finite geometric row centered at any natural number has uniformly
bounded mass. -/
theorem sum_pow_half_natDist_le_four {J j : ℕ} (hj : j < J) :
    (∑ k ∈ Finset.range J, (1 / 2 : ℝ) ^ Nat.dist j k) ≤ 4 := by
  have hj1 : j + 1 ≤ J := by omega
  have hJ : J = (j + 1) + (J - (j + 1)) := by omega
  rw [hJ, Finset.sum_range_add]
  have hleft :
      (∑ k ∈ Finset.range (j + 1),
          (1 / 2 : ℝ) ^ Nat.dist j k) =
        ∑ d ∈ Finset.range (j + 1), (1 / 2 : ℝ) ^ d := by
    calc
      (∑ k ∈ Finset.range (j + 1),
          (1 / 2 : ℝ) ^ Nat.dist j k) =
          ∑ k ∈ Finset.range (j + 1), (1 / 2 : ℝ) ^ (j - k) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkj := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hkj]
      _ = ∑ d ∈ Finset.range (j + 1), (1 / 2 : ℝ) ^ d := by
        simpa using Finset.sum_range_reflect
          (fun d ↦ (1 / 2 : ℝ) ^ d) (j + 1)
  have hright :
      (∑ d ∈ Finset.range (J - (j + 1)),
          (1 / 2 : ℝ) ^ Nat.dist j (j + 1 + d)) ≤
        ∑ d ∈ Finset.range (J - (j + 1)), (1 / 2 : ℝ) ^ d := by
    apply Finset.sum_le_sum
    intro d hd
    have hjd : j ≤ j + 1 + d := by omega
    rw [Nat.dist_eq_sub_of_le hjd]
    have hsub : j + 1 + d - j = d + 1 := by omega
    rw [hsub, pow_succ]
    have hpow0 : 0 ≤ (1 / 2 : ℝ) ^ d := by positivity
    nlinarith
  rw [hleft]
  calc
    (∑ d ∈ Finset.range (j + 1), (1 / 2 : ℝ) ^ d) +
        ∑ d ∈ Finset.range (J - (j + 1)),
          (1 / 2 : ℝ) ^ Nat.dist j (j + 1 + d) ≤
      (∑ d ∈ Finset.range (j + 1), (1 / 2 : ℝ) ^ d) +
        ∑ d ∈ Finset.range (J - (j + 1)), (1 / 2 : ℝ) ^ d :=
          add_le_add_right hright _
    _ ≤ 4 := by
      linarith [sum_geometric_two_le (j + 1),
        sum_geometric_two_le (J - (j + 1))]

/-- At frequency radius at least four, interaction between shells is
dominated by a geometric kernel in their dyadic distance. -/
theorem finiteHalaszDyadicShellKernel_le_geometric
    {T : ℝ} (hT : 4 ≤ T) (j k : ℕ) :
    finiteHalaszDyadicShellKernel T j k ≤
      2 * (1 / 2 : ℝ) ^ Nat.dist j k := by
  have hTpos : 0 < T := by linarith
  have hb : 0 < T⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr hTpos)
  have hone := finiteHalaszGaussianPairKernel_le_one hb
    (finiteHalaszDyadicShellGap j k)
  by_cases hd : Nat.dist j k ≤ 1
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd with hzero | honeDist
    · rw [hzero, pow_zero]
      have hshell : finiteHalaszDyadicShellKernel T j k ≤ 1 := by
        simpa only [finiteHalaszDyadicShellKernel] using hone
      linarith
    · rw [honeDist, pow_one]
      norm_num
      simpa only [finiteHalaszDyadicShellKernel] using hone
  · have hd2 : 2 ≤ Nat.dist j k := by omega
    let q : ℕ := Nat.dist j k - 1
    have hq : 1 ≤ q := by dsimp [q]; omega
    have hdist : Nat.dist j k = q + 1 := by dsimp [q]; omega
    have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlogHalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
      exact (by norm_num : (1 / 2 : ℝ) < 0.6931471803).le.trans
        Real.log_two_gt_d9.le
    have hTsq : (16 : ℝ) ≤ T ^ 2 := by nlinarith
    have hscaleMul : (8 : ℝ) ≤ T ^ 2 * Real.log 2 := by
      have hm := mul_le_mul hTsq hlogHalf (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (sq_nonneg T)
      norm_num at hm ⊢
      exact hm
    have hscale : (4 : ℝ) ≤ T ^ 2 * Real.log 2 := by linarith
    have hqreal : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hqsq : (q : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
    have hsecond : (q : ℝ) * Real.log 2 ≤
        (q : ℝ) ^ 2 * Real.log 2 :=
      mul_le_mul_of_nonneg_right hqsq hlog.le
    have hprod := mul_le_mul hscale hsecond
      (mul_nonneg (Nat.cast_nonneg q) hlog.le)
      (mul_nonneg (sq_nonneg T) hlog.le)
    have hquad :
        4 * ((q : ℝ) * Real.log 2) ≤
          T ^ 2 * (((q : ℝ) * Real.log 2) ^ 2) := by
      nlinarith [hprod]
    have hTne : T ≠ 0 := ne_of_gt hTpos
    have hexponent :
        -(finiteHalaszDyadicShellGap j k ^ 2) /
              (4 * (T⁻¹ ^ 2)) ≤
          -((q : ℝ) * Real.log 2) := by
      rw [show finiteHalaszDyadicShellGap j k =
          (q : ℝ) * Real.log 2 by
        unfold finiteHalaszDyadicShellGap
        simp only [q]]
      have heq :
          -(((q : ℝ) * Real.log 2) ^ 2) / (4 * (T⁻¹ ^ 2)) =
            -(T ^ 2 * (((q : ℝ) * Real.log 2) ^ 2)) / 4 := by
        field_simp
      rw [heq]
      linarith
    calc
      finiteHalaszDyadicShellKernel T j k =
          Real.exp (-(finiteHalaszDyadicShellGap j k ^ 2) /
            (4 * (T⁻¹ ^ 2))) := rfl
      _ ≤ Real.exp (-((q : ℝ) * Real.log 2)) :=
        Real.exp_le_exp.mpr hexponent
      _ = (1 / 2 : ℝ) ^ q := by
        rw [show -((q : ℝ) * Real.log 2) =
            (q : ℝ) * Real.log (1 / 2 : ℝ) by
          rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
            Real.log_inv]
          ring]
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 1 / 2)]
      _ = 2 * (1 / 2 : ℝ) ^ Nat.dist j k := by
        rw [hdist, pow_succ]
        ring

/-- The dyadic Gaussian interaction matrix has a universal Schur row
bound, independent of the number of shells. -/
theorem sum_dyadicShellKernel_le_eight
    {T : ℝ} (hT : 4 ≤ T) {J j : ℕ} (hj : j < J) :
    (∑ k ∈ Finset.range J, finiteHalaszDyadicShellKernel T j k) ≤ 8 := by
  calc
    (∑ k ∈ Finset.range J, finiteHalaszDyadicShellKernel T j k) ≤
        ∑ k ∈ Finset.range J,
          2 * (1 / 2 : ℝ) ^ Nat.dist j k := by
      apply Finset.sum_le_sum
      intro k hk
      exact finiteHalaszDyadicShellKernel_le_geometric hT j k
    _ = 2 * ∑ k ∈ Finset.range J,
          (1 / 2 : ℝ) ^ Nat.dist j k := by
      rw [Finset.mul_sum]
    _ ≤ 8 := by
      nlinarith [sum_pow_half_natDist_le_four hj]

/-- Integers in dyadic shells separated by `d` shell steps have
logarithmic distance at least `(d-1) log 2`. -/
theorem finiteHalaszDyadicShellGap_le_abs_log_sub
    {L j k n m : ℕ} (hL : 0 < L)
    (hn : n ∈ Finset.Ioc (2 ^ j * L) (2 ^ (j + 1) * L))
    (hm : m ∈ Finset.Ioc (2 ^ k * L) (2 ^ (k + 1) * L)) :
    finiteHalaszDyadicShellGap j k ≤
      |Real.log m - Real.log n| := by
  have hgap0 : 0 ≤ finiteHalaszDyadicShellGap j k := by
    unfold finiteHalaszDyadicShellGap
    positivity
  by_cases hd : Nat.dist j k ≤ 1
  · have hsub : Nat.dist j k - 1 = 0 := by omega
    rw [show finiteHalaszDyadicShellGap j k = 0 by
      unfold finiteHalaszDyadicShellGap
      rw [hsub]
      norm_num]
    exact abs_nonneg _
  · have hd2 : 2 ≤ Nat.dist j k := by omega
    have hlogPowMul : ∀ r : ℕ,
        Real.log (((2 ^ r * L : ℕ) : ℝ)) =
          (r : ℝ) * Real.log 2 + Real.log L := by
      intro r
      push_cast
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    rcases le_total j k with hjk | hkj
    · have hjk' : j < k := by
        by_contra hnot
        have : j = k := Nat.le_antisymm hjk (Nat.le_of_not_gt hnot)
        subst k
        simp at hd2
      have hnpos : (0 : ℝ) < n := by
        have hnposNat : 0 < n := by
          have hbase : 0 < 2 ^ j * L := mul_pos (pow_pos (by omega) j) hL
          exact hbase.trans (Finset.mem_Ioc.mp hn).1
        exact_mod_cast hnposNat
      have hmpos : (0 : ℝ) < m := by
        have hmposNat : 0 < m := by
          have hbase : 0 < 2 ^ k * L := mul_pos (pow_pos (by omega) k) hL
          exact hbase.trans (Finset.mem_Ioc.mp hm).1
        exact_mod_cast hmposNat
      have hUpperPos : (0 : ℝ) < ((2 ^ (j + 1) * L : ℕ) : ℝ) := by
        positivity
      have hLowerPos : (0 : ℝ) < ((2 ^ k * L : ℕ) : ℝ) := by
        positivity
      have hnlog : Real.log n ≤
          Real.log (((2 ^ (j + 1) * L : ℕ) : ℝ)) := by
        apply Real.strictMonoOn_log.monotoneOn
        · exact hnpos
        · exact hUpperPos
        · exact_mod_cast (Finset.mem_Ioc.mp hn).2
      have hmlog : Real.log (((2 ^ k * L : ℕ) : ℝ)) ≤ Real.log m := by
        apply Real.strictMonoOn_log.monotoneOn
        · exact hLowerPos
        · exact hmpos
        · exact_mod_cast (Finset.mem_Ioc.mp hm).1.le
      rw [hlogPowMul (j + 1)] at hnlog
      rw [hlogPowMul k] at hmlog
      have hdist : Nat.dist j k = k - j := Nat.dist_eq_sub_of_le hjk
      have hcast : ((Nat.dist j k - 1 : ℕ) : ℝ) =
          (k : ℝ) - (j : ℝ) - 1 := by
        rw [hdist]
        norm_num [Nat.cast_sub hjk, Nat.cast_sub (by omega : 1 ≤ k - j)]
      have hsep : finiteHalaszDyadicShellGap j k ≤
          Real.log m - Real.log n := by
        unfold finiteHalaszDyadicShellGap
        rw [hcast]
        push_cast at hnlog
        ring_nf at hnlog hmlog ⊢
        linarith
      exact hsep.trans (le_abs_self _)
    · have hkj' : k < j := by
        by_contra hnot
        have : j = k := Nat.le_antisymm (Nat.le_of_not_gt hnot) hkj
        subst k
        simp at hd2
      have hmpos : (0 : ℝ) < m := by
        have hmposNat : 0 < m := by
          have hbase : 0 < 2 ^ k * L := mul_pos (pow_pos (by omega) k) hL
          exact hbase.trans (Finset.mem_Ioc.mp hm).1
        exact_mod_cast hmposNat
      have hnpos : (0 : ℝ) < n := by
        have hnposNat : 0 < n := by
          have hbase : 0 < 2 ^ j * L := mul_pos (pow_pos (by omega) j) hL
          exact hbase.trans (Finset.mem_Ioc.mp hn).1
        exact_mod_cast hnposNat
      have hUpperPos : (0 : ℝ) < ((2 ^ (k + 1) * L : ℕ) : ℝ) := by
        positivity
      have hLowerPos : (0 : ℝ) < ((2 ^ j * L : ℕ) : ℝ) := by
        positivity
      have hmlog : Real.log m ≤
          Real.log (((2 ^ (k + 1) * L : ℕ) : ℝ)) := by
        apply Real.strictMonoOn_log.monotoneOn
        · exact hmpos
        · exact hUpperPos
        · exact_mod_cast (Finset.mem_Ioc.mp hm).2
      have hnlog : Real.log (((2 ^ j * L : ℕ) : ℝ)) ≤ Real.log n := by
        apply Real.strictMonoOn_log.monotoneOn
        · exact hLowerPos
        · exact hnpos
        · exact_mod_cast (Finset.mem_Ioc.mp hn).1.le
      rw [hlogPowMul (k + 1)] at hmlog
      rw [hlogPowMul j] at hnlog
      have hdist : Nat.dist j k = j - k := by
        rw [Nat.dist_comm]
        exact Nat.dist_eq_sub_of_le hkj
      have hcast : ((Nat.dist j k - 1 : ℕ) : ℝ) =
          (j : ℝ) - (k : ℝ) - 1 := by
        rw [hdist]
        norm_num [Nat.cast_sub hkj, Nat.cast_sub (by omega : 1 ≤ j - k)]
      have hsep : finiteHalaszDyadicShellGap j k ≤
          Real.log n - Real.log m := by
        unfold finiteHalaszDyadicShellGap
        rw [hcast]
        push_cast at hmlog
        ring_nf at hmlog hnlog ⊢
        linarith
      simpa only [abs_sub_comm] using
        hsep.trans (le_abs_self (Real.log n - Real.log m))

/-- The Gaussian kernel decreases when the absolute frequency separation
increases. -/
theorem finiteHalaszGaussianPairKernel_le_of_gap
    {b g x : ℝ} (hb : 0 < b) (hg : 0 ≤ g) (hgap : g ≤ |x|) :
    finiteHalaszGaussianPairKernel b x ≤
      finiteHalaszGaussianPairKernel b g := by
  unfold finiteHalaszGaussianPairKernel
  apply Real.exp_le_exp.mpr
  have hsq : g ^ 2 ≤ x ^ 2 := by
    rw [← sq_abs x]
    exact pow_le_pow_left₀ hg hgap 2
  have hden : 0 < 4 * b := by positivity
  exact div_le_div_of_nonneg_right (neg_le_neg hsq) hden.le

/-! ## Actual shell support -/

/-- The nonzero-support predicate of a prime-band coefficient, restricted
to one dyadic shell. -/
noncomputable def finiteHalaszPrimeBandDyadicSupport
    (Q : ℕ → Prop) [DecidablePred Q] (L j : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.Ioc (2 ^ j * L) (2 ^ (j + 1) * L)).filter
      (PrimeSupported Q)

@[simp]
theorem mem_finiteHalaszPrimeBandDyadicSupport
    {Q : ℕ → Prop} [DecidablePred Q] {L j n : ℕ} :
    n ∈ finiteHalaszPrimeBandDyadicSupport Q L j ↔
      n ∈ Finset.Ioc (2 ^ j * L) (2 ^ (j + 1) * L) ∧
        PrimeSupported Q n := by
  classical
  simp [finiteHalaszPrimeBandDyadicSupport]

/-- Restricting a shell polynomial to its actual prime-band support does
not change it. -/
theorem logarithmicDirichletPolynomial_primeBandSupport_eq
    (f : ℕ → ℂ) (Q : ℕ → Prop) [DecidablePred Q]
    (sigma : ℝ) (L j : ℕ) (t : ℝ) :
    logarithmicDirichletPolynomial
        (finiteHalaszPrimeBandDyadicSupport Q L j)
        (smoothedPrimeBandCoefficient f Q sigma) t =
      smoothedPrimeBandPolynomial f Q sigma
        (2 ^ j * L) (2 ^ (j + 1) * L) t := by
  classical
  unfold logarithmicDirichletPolynomial smoothedPrimeBandPolynomial
    finiteHalaszPrimeBandDyadicSupport
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hsupp : PrimeSupported Q n
  · simp [hsupp]
  · simp [hsupp, smoothedPrimeBandCoefficient, primeBandCoefficient]

/-- If `Q` avoids a prime block, every actual shell-support integer lies
in the corresponding missing-block set. -/
theorem finiteHalaszPrimeBandDyadicSupport_subset_missingPrimeBlockSet
    (I : ℕ × ℕ) (Q : ℕ → Prop) [DecidablePred Q]
    (hdisj : ∀ p ∈ primesInBlock I, ¬ Q p)
    {L j : ℕ} (hL : 0 < L) :
    finiteHalaszPrimeBandDyadicSupport Q L j ⊆
      missingPrimeBlockSet I (2 ^ (j + 1) * L) := by
  intro n hn
  rw [mem_finiteHalaszPrimeBandDyadicSupport] at hn
  rw [mem_missingPrimeBlockSet]
  have hLj : 0 < 2 ^ j * L := mul_pos (pow_pos (by omega) j) hL
  have hnpos : 0 < n := hLj.trans (Finset.mem_Ioc.mp hn.1).1
  refine ⟨hnpos, (Finset.mem_Ioc.mp hn.1).2, ?_⟩
  rintro ⟨p, hpI, hpn⟩
  have hpprime := (mem_primesInBlock.mp hpI).1
  have hpFactors : p ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hpprime, hpn, hnpos.ne'⟩
  exact hdisj p hpI (hn.2.2 p hpFactors)

theorem card_finiteHalaszPrimeBandDyadicSupport_le_missing
    (I : ℕ × ℕ) (Q : ℕ → Prop) [DecidablePred Q]
    (hdisj : ∀ p ∈ primesInBlock I, ¬ Q p)
    {L j : ℕ} (hL : 0 < L) :
    ((finiteHalaszPrimeBandDyadicSupport Q L j).card : ℝ) ≤
      ((missingPrimeBlockSet I (2 ^ (j + 1) * L)).card : ℝ) := by
  exact_mod_cast Finset.card_le_card
    (finiteHalaszPrimeBandDyadicSupport_subset_missingPrimeBlockSet
      I Q hdisj hL)

/-- Pointwise coefficient bound on the actual support of a shell. -/
theorem norm_smoothedPrimeBandCoefficient_le_shell
    {f : ℕ → ℂ} {Q : ℕ → Prop} [DecidablePred Q]
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {sigma : ℝ} (hsigma : 0 ≤ sigma)
    {L j n : ℕ} (hL : 0 < L)
    (hn : n ∈ finiteHalaszPrimeBandDyadicSupport Q L j) :
    ‖smoothedPrimeBandCoefficient f Q sigma n‖ ≤
      ((2 ^ j * L : ℕ) : ℝ) ^ (-sigma) := by
  rw [mem_finiteHalaszPrimeBandDyadicSupport] at hn
  have hLj : 0 < 2 ^ j * L := mul_pos (pow_pos (by omega) j) hL
  have hnpos : 0 < n := hLj.trans (Finset.mem_Ioc.mp hn.1).1
  have hbase : (((2 ^ j * L : ℕ) : ℝ)) ≤ (n : ℝ) := by
    exact_mod_cast (Finset.mem_Ioc.mp hn.1).1.le
  have hrpow : (n : ℝ) ^ (-sigma) ≤
      ((2 ^ j * L : ℕ) : ℝ) ^ (-sigma) := by
    exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hLj) hbase
      (neg_nonpos.mpr hsigma)
  unfold smoothedPrimeBandCoefficient
  rw [primeBandCoefficient_eq_of_supported f Q hn.2, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  exact (mul_le_mul (hbound n hnpos) hrpow
    (Real.rpow_nonneg (Nat.cast_nonneg n) _) zero_le_one).trans_eq
      (one_mul _)

/-- The `L¹` mass of an actual shell is bounded by its support
cardinality times the lower-endpoint weight. -/
theorem sum_norm_smoothedPrimeBandCoefficient_support_le
    {f : ℕ → ℂ} {Q : ℕ → Prop} [DecidablePred Q]
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {sigma : ℝ} (hsigma : 0 ≤ sigma)
    {L j : ℕ} (hL : 0 < L) :
    (∑ n ∈ finiteHalaszPrimeBandDyadicSupport Q L j,
        ‖smoothedPrimeBandCoefficient f Q sigma n‖) ≤
      ((finiteHalaszPrimeBandDyadicSupport Q L j).card : ℝ) *
        ((2 ^ j * L : ℕ) : ℝ) ^ (-sigma) := by
  calc
    (∑ n ∈ finiteHalaszPrimeBandDyadicSupport Q L j,
        ‖smoothedPrimeBandCoefficient f Q sigma n‖) ≤
        ∑ _n ∈ finiteHalaszPrimeBandDyadicSupport Q L j,
          ((2 ^ j * L : ℕ) : ℝ) ^ (-sigma) := by
      apply Finset.sum_le_sum
      intro n hn
      exact norm_smoothedPrimeBandCoefficient_le_shell hbound hsigma hL hn
    _ = ((finiteHalaszPrimeBandDyadicSupport Q L j).card : ℝ) *
        ((2 ^ j * L : ℕ) : ℝ) ^ (-sigma) := by simp

/-- The dependent finite index set obtained by flattening all actual
prime-band supports above a cutoff. -/
def finiteHalaszDyadicSupportIndex
    (Q : ℕ → Prop) [DecidablePred Q] (L J : ℕ) :=
  Sigma fun j : Fin J ↦
    ↥(finiteHalaszPrimeBandDyadicSupport Q L j.1)

instance finiteHalaszDyadicSupportIndexFintype
    (Q : ℕ → Prop) [DecidablePred Q] (L J : ℕ) :
    Fintype (finiteHalaszDyadicSupportIndex Q L J) := by
  unfold finiteHalaszDyadicSupportIndex
  infer_instance

/-- Flattening the actual supports recovers the full positive-band
prefix, because the coefficient vanishes off those supports. -/
theorem finiteFrequencyPolynomial_dyadicSupportIndex_eq
    (f : ℕ → ℂ) (Q : ℕ → Prop) [DecidablePred Q]
    (sigma : ℝ) {L : ℕ} (hL : 0 < L)
    (hQ : ∀ p, p.Prime → p ≤ L → ¬ Q p)
    (J : ℕ) (t : ℝ) :
    finiteFrequencyPolynomial
        (fun z : finiteHalaszDyadicSupportIndex Q L J ↦
          Real.log z.2.1)
        (fun z : finiteHalaszDyadicSupportIndex Q L J ↦
          smoothedPrimeBandCoefficient f Q sigma z.2.1) t =
      smoothedPrimeBandPolynomial f Q sigma 1 (2 ^ J * L) t := by
  classical
  calc
    finiteFrequencyPolynomial
        (fun z : finiteHalaszDyadicSupportIndex Q L J ↦
          Real.log z.2.1)
        (fun z : finiteHalaszDyadicSupportIndex Q L J ↦
          smoothedPrimeBandCoefficient f Q sigma z.2.1) t =
      ∑ j : Fin J,
        logarithmicDirichletPolynomial
          (finiteHalaszPrimeBandDyadicSupport Q L j.1)
          (smoothedPrimeBandCoefficient f Q sigma) t := by
      unfold finiteFrequencyPolynomial finiteHalaszDyadicSupportIndex
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro j hj
      exact finiteFrequencyPolynomial_subtype_eq_logarithmic
        (finiteHalaszPrimeBandDyadicSupport Q L j.1)
        (smoothedPrimeBandCoefficient f Q sigma) t
    _ = ∑ j ∈ Finset.range J,
        logarithmicDirichletPolynomial
          (finiteHalaszPrimeBandDyadicSupport Q L j)
          (smoothedPrimeBandCoefficient f Q sigma) t := by
      exact Fin.sum_univ_eq_sum_range
        (fun j ↦ logarithmicDirichletPolynomial
          (finiteHalaszPrimeBandDyadicSupport Q L j)
          (smoothedPrimeBandCoefficient f Q sigma) t) J
    _ = ∑ j ∈ Finset.range J,
        smoothedPrimeBandPolynomial f Q sigma
          (2 ^ j * L) (2 ^ (j + 1) * L) t := by
      apply Finset.sum_congr rfl
      intro j hj
      exact logarithmicDirichletPolynomial_primeBandSupport_eq
        f Q sigma L j t
    _ = smoothedPrimeBandPolynomial f Q sigma 1 (2 ^ J * L) t :=
      (smoothedPrimeBandPolynomial_one_mul_twoPow_eq_sum_dyadic_of_cutoff
        f Q sigma hL hQ J t).symm

/-- Direct full-band Gaussian/Schur estimate.  Its right side is a sum of
squared *actual-support* `L¹` bounds, so a missing-prime-block density is
squared.  The constant `8` is independent of the number of dyadic shells. -/
theorem intervalIntegral_normSq_smoothedPrimeBandPolynomial_le_gaussianSchurSupport
    (f : ℕ → ℂ) (Q : ℕ → Prop) [DecidablePred Q]
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {sigma : ℝ} (hsigma : 0 ≤ sigma)
    {L : ℕ} (hL : 0 < L) (J : ℕ)
    {T : ℝ} (hT : 4 ≤ T)
    (hQ : ∀ p, p.Prime → p ≤ L → ¬ Q p) :
    (∫ t in -T..T,
        Complex.normSq
          (smoothedPrimeBandPolynomial f Q sigma 1 (2 ^ J * L) t)) ≤
      Real.exp 1 *
        (Real.sqrt (Real.pi / (T⁻¹ ^ 2)) *
          (8 * ∑ j ∈ Finset.range J,
            (((finiteHalaszPrimeBandDyadicSupport Q L j).card : ℝ) *
              ((2 ^ j * L : ℕ) : ℝ) ^ (-sigma)) ^ 2)) := by
  classical
  let ι := finiteHalaszDyadicSupportIndex Q L J
  let freq : ι → ℝ := fun z ↦ Real.log z.2.1
  let a : ι → ℂ := fun z ↦ smoothedPrimeBandCoefficient f Q sigma z.2.1
  have hTpos : 0 < T := by linarith
  have hbase := intervalIntegral_normSq_finiteFrequencyPolynomial_le_gaussianPairMajorant
    freq a hTpos
  have hflat : finiteHalaszGaussianPairMajorant freq a (T⁻¹ ^ 2) =
      finiteHalaszGaussianBlockPairMajorant
        (fun j : Fin J ↦ fun n :
          ↥(finiteHalaszPrimeBandDyadicSupport Q L j.1) ↦ Real.log n.1)
        (fun j : Fin J ↦ fun n :
          ↥(finiteHalaszPrimeBandDyadicSupport Q L j.1) ↦
            smoothedPrimeBandCoefficient f Q sigma n.1)
        (T⁻¹ ^ 2) := by
    simpa only [ι, freq, a, finiteHalaszDyadicSupportIndex] using
      finiteHalaszGaussianPairMajorant_sigma_eq_block
        (fun j : Fin J ↦ fun n :
          ↥(finiteHalaszPrimeBandDyadicSupport Q L j.1) ↦ Real.log n.1)
        (fun j : Fin J ↦ fun n :
          ↥(finiteHalaszPrimeBandDyadicSupport Q L j.1) ↦
            smoothedPrimeBandCoefficient f Q sigma n.1)
        (T⁻¹ ^ 2)
  let B : Fin J → ℝ := fun j ↦
    (((finiteHalaszPrimeBandDyadicSupport Q L j.1).card : ℝ) *
      ((2 ^ j.1 * L : ℕ) : ℝ) ^ (-sigma)) ^ 2
  have hschur := finiteHalaszGaussianBlockPairMajorant_le_schur
    (fun j : Fin J ↦ fun n :
      ↥(finiteHalaszPrimeBandDyadicSupport Q L j.1) ↦ Real.log n.1)
    (fun j : Fin J ↦ fun n :
      ↥(finiteHalaszPrimeBandDyadicSupport Q L j.1) ↦
        smoothedPrimeBandCoefficient f Q sigma n.1)
    (fun j k ↦ finiteHalaszDyadicShellKernel T j.1 k.1) B
    (fun j k ↦ finiteHalaszDyadicShellKernel_nonneg T j.1 k.1)
    (fun j k ↦ finiteHalaszDyadicShellKernel_symm T j.1 k.1)
    (by
      intro j n k m
      unfold finiteHalaszDyadicShellKernel
      apply finiteHalaszGaussianPairKernel_le_of_gap
        (sq_pos_of_pos (inv_pos.mpr hTpos))
      · unfold finiteHalaszDyadicShellGap
        positivity
      · exact finiteHalaszDyadicShellGap_le_abs_log_sub hL
          (mem_finiteHalaszPrimeBandDyadicSupport.mp n.2).1
          (mem_finiteHalaszPrimeBandDyadicSupport.mp m.2).1)
    (by
      intro j k
      let Uj : ℝ :=
        ((finiteHalaszPrimeBandDyadicSupport Q L j.1).card : ℝ) *
          ((2 ^ j.1 * L : ℕ) : ℝ) ^ (-sigma)
      let Uk : ℝ :=
        ((finiteHalaszPrimeBandDyadicSupport Q L k.1).card : ℝ) *
          ((2 ^ k.1 * L : ℕ) : ℝ) ^ (-sigma)
      have hjmass :
          (∑ n : ↥(finiteHalaszPrimeBandDyadicSupport Q L j.1),
            ‖smoothedPrimeBandCoefficient f Q sigma n.1‖) ≤ Uj := by
        calc
          (∑ n : ↥(finiteHalaszPrimeBandDyadicSupport Q L j.1),
              ‖smoothedPrimeBandCoefficient f Q sigma n.1‖) =
              ∑ n ∈ finiteHalaszPrimeBandDyadicSupport Q L j.1,
                ‖smoothedPrimeBandCoefficient f Q sigma n‖ := by
            simpa only [Finset.univ_eq_attach] using
              (Finset.sum_attach
                (finiteHalaszPrimeBandDyadicSupport Q L j.1)
                (fun n ↦ ‖smoothedPrimeBandCoefficient f Q sigma n‖))
          _ ≤ Uj := by
            simpa only [Uj] using
              (sum_norm_smoothedPrimeBandCoefficient_support_le (Q := Q)
                hbound hsigma hL (j := j.1))
      have hkmass :
          (∑ n : ↥(finiteHalaszPrimeBandDyadicSupport Q L k.1),
            ‖smoothedPrimeBandCoefficient f Q sigma n.1‖) ≤ Uk := by
        calc
          (∑ n : ↥(finiteHalaszPrimeBandDyadicSupport Q L k.1),
              ‖smoothedPrimeBandCoefficient f Q sigma n.1‖) =
              ∑ n ∈ finiteHalaszPrimeBandDyadicSupport Q L k.1,
                ‖smoothedPrimeBandCoefficient f Q sigma n‖ := by
            simpa only [Finset.univ_eq_attach] using
              (Finset.sum_attach
                (finiteHalaszPrimeBandDyadicSupport Q L k.1)
                (fun n ↦ ‖smoothedPrimeBandCoefficient f Q sigma n‖))
          _ ≤ Uk := by
            simpa only [Uk] using
              (sum_norm_smoothedPrimeBandCoefficient_support_le (Q := Q)
                hbound hsigma hL (j := k.1))
      have hj0 : 0 ≤
          ∑ n : ↥(finiteHalaszPrimeBandDyadicSupport Q L j.1),
            ‖smoothedPrimeBandCoefficient f Q sigma n.1‖ := by positivity
      have hk0 : 0 ≤
          ∑ n : ↥(finiteHalaszPrimeBandDyadicSupport Q L k.1),
            ‖smoothedPrimeBandCoefficient f Q sigma n.1‖ := by positivity
      have hUj0 : 0 ≤ Uj := hj0.trans hjmass
      have hUk0 : 0 ≤ Uk := hk0.trans hkmass
      have hprod := mul_le_mul hjmass hkmass hk0 hUj0
      dsimp only [B]
      exact hprod.trans (by nlinarith [sq_nonneg (Uj - Uk)]))
    (by
      intro j
      rw [Fin.sum_univ_eq_sum_range]
      exact sum_dyadicShellKernel_le_eight hT j.isLt)
  have hpair : finiteHalaszGaussianPairMajorant freq a (T⁻¹ ^ 2) ≤
      Real.sqrt (Real.pi / (T⁻¹ ^ 2)) * (8 * ∑ j : Fin J, B j) := by
    rw [hflat]
    exact hschur
  have hpoly : ∀ t,
      finiteFrequencyPolynomial freq a t =
        smoothedPrimeBandPolynomial f Q sigma 1 (2 ^ J * L) t := by
    intro t
    simpa only [freq, a, ι] using
      finiteFrequencyPolynomial_dyadicSupportIndex_eq f Q sigma hL hQ J t
  calc
    (∫ t in -T..T,
        Complex.normSq
          (smoothedPrimeBandPolynomial f Q sigma 1 (2 ^ J * L) t)) =
      ∫ t in -T..T, Complex.normSq (finiteFrequencyPolynomial freq a t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact congrArg Complex.normSq (hpoly t).symm
    _ ≤ Real.exp 1 * finiteHalaszGaussianPairMajorant freq a (T⁻¹ ^ 2) :=
      hbase
    _ ≤ Real.exp 1 *
        (Real.sqrt (Real.pi / (T⁻¹ ^ 2)) * (8 * ∑ j : Fin J, B j)) := by
      exact mul_le_mul_of_nonneg_left hpair (Real.exp_pos 1).le
    _ = Real.exp 1 *
        (Real.sqrt (Real.pi / (T⁻¹ ^ 2)) *
          (8 * ∑ j ∈ Finset.range J,
            (((finiteHalaszPrimeBandDyadicSupport Q L j).card : ℝ) *
              ((2 ^ j * L : ℕ) : ℝ) ^ (-sigma)) ^ 2)) := by
      rw [show (∑ j : Fin J, B j) = ∑ j ∈ Finset.range J,
          (((finiteHalaszPrimeBandDyadicSupport Q L j).card : ℝ) *
            ((2 ^ j * L : ℕ) : ℝ) ^ (-sigma)) ^ 2 by
        exact Fin.sum_univ_eq_sum_range
          (fun j ↦ (((finiteHalaszPrimeBandDyadicSupport Q L j).card : ℝ) *
            ((2 ^ j * L : ℕ) : ℝ) ^ (-sigma)) ^ 2) J]

/-- Explicit beta-sieve scale for one actual-support dyadic shell. -/
def finiteHalaszGaussianSchurShellScale
    (Cβ : ℝ) (I : ℕ × ℕ) (S : ℕ) (sigma : ℝ) (L j : ℕ) : ℝ :=
  ((((2 ^ (j + 1) * L : ℕ) : ℝ) *
        finiteHalaszGaussianBetaDensity Cβ I S +
      finiteHalaszGaussianBetaRemainder I S) *
    ((2 ^ j * L : ℕ) : ℝ) ^ (-sigma)) ^ 2

/-- The full-band Schur estimate with every actual support cardinality
discharged by the concrete beta-sieve/Mertens theorem.  No factor
quadratic in the number of shells remains. -/
theorem exists_intervalIntegral_normSq_smoothedPrimeBandPolynomial_gaussianSchur_beta_bound :
    ∃ Cβ : ℝ, 1 ≤ Cβ ∧
      ∀ (I : ℕ × ℕ) (Q : ℕ → Prop) [DecidablePred Q]
        (f : ℕ → ℂ) (L J S : ℕ) {sigma T : ℝ},
        (∀ p ∈ primesInBlock I, ¬ Q p) →
        (∀ p, p.Prime → p ≤ L → ¬ Q p) →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) →
        0 < L → 0 ≤ sigma → 4 ≤ T →
        3 ≤ I.1 → I.1 ≤ I.2 → 101 ≤ S →
        Real.log Cβ ≤ 2 * (S - 100 : ℕ) / 99 →
        (∫ t in -T..T,
            Complex.normSq
              (smoothedPrimeBandPolynomial f Q sigma 1 (2 ^ J * L) t)) ≤
          Real.exp 1 *
            (Real.sqrt (Real.pi / (T⁻¹ ^ 2)) *
              (8 * ∑ j ∈ Finset.range J,
                finiteHalaszGaussianSchurShellScale
                  Cβ I S sigma L j)) := by
  obtain ⟨Cβ, hCβ, hbeta⟩ :=
    exists_card_missingPrimeBlockSet_mertens_beta_bound
  refine ⟨Cβ, hCβ, ?_⟩
  intro I Q _ f L J S sigma T hdisj hQ hbound hL hsigma hT
    hIlo hI hS hlog
  have hsupport :=
    intervalIntegral_normSq_smoothedPrimeBandPolynomial_le_gaussianSchurSupport
      f Q hbound hsigma hL J hT hQ
  apply hsupport.trans
  have hsum :
      (∑ j ∈ Finset.range J,
          (((finiteHalaszPrimeBandDyadicSupport Q L j).card : ℝ) *
            ((2 ^ j * L : ℕ) : ℝ) ^ (-sigma)) ^ 2) ≤
        ∑ j ∈ Finset.range J,
          finiteHalaszGaussianSchurShellScale Cβ I S sigma L j := by
    apply Finset.sum_le_sum
    intro j hj
    have hcardSupport :=
      card_finiteHalaszPrimeBandDyadicSupport_le_missing
        I Q hdisj (j := j) hL
    have hcardMissing := hbeta (2 ^ (j + 1) * L) I.1 I.2 S
      hIlo hI hS hlog
    have hcard :
        ((finiteHalaszPrimeBandDyadicSupport Q L j).card : ℝ) ≤
          (((2 ^ (j + 1) * L : ℕ) : ℝ) *
              finiteHalaszGaussianBetaDensity Cβ I S +
            finiteHalaszGaussianBetaRemainder I S) := by
      exact hcardSupport.trans (by
        simpa only [finiteHalaszGaussianBetaDensity,
          finiteHalaszGaussianBetaRemainder] using hcardMissing)
    have hw : 0 ≤ ((2 ^ j * L : ℕ) : ℝ) ^ (-sigma) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hmul := mul_le_mul_of_nonneg_right hcard hw
    unfold finiteHalaszGaussianSchurShellScale
    exact pow_le_pow_left₀
      (mul_nonneg (Nat.cast_nonneg _)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hmul 2
  gcongr

theorem finiteHalaszGaussianBetaDensity_nonneg
    {Cβ : ℝ} {I : ℕ × ℕ} {S : ℕ}
    (hCβ : 0 ≤ Cβ) (hIlo : 3 ≤ I.1) (hI : I.1 ≤ I.2) :
    0 ≤ finiteHalaszGaussianBetaDensity Cβ I S := by
  have hnum : 0 ≤ Real.log ((I.1 - 1 : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (by omega : 1 ≤ I.1 - 1)
  have hden : 0 < Real.log (I.2 : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < I.2)
  unfold finiteHalaszGaussianBetaDensity
  positivity

/-- Coarse source-scale form of one Schur shell.  For every line
`sigma ≥ 1`, the shell is bounded uniformly by the squared sieve density
plus the lower-cutoff remainder; the bound has no dependence on `j`. -/
theorem finiteHalaszGaussianSchurShellScale_le_uniform
    {Cβ : ℝ} {I : ℕ × ℕ} {S L j : ℕ} {sigma : ℝ}
    (hCβ : 0 ≤ Cβ) (hIlo : 3 ≤ I.1) (hI : I.1 ≤ I.2)
    (hL : 0 < L) (hsigma : 1 ≤ sigma) :
    finiteHalaszGaussianSchurShellScale Cβ I S sigma L j ≤
      8 * (finiteHalaszGaussianBetaDensity Cβ I S) ^ 2 +
        2 * (finiteHalaszGaussianBetaRemainder I S * (L : ℝ)⁻¹) ^ 2 := by
  let Lj : ℕ := 2 ^ j * L
  have hLj : 0 < Lj := mul_pos (pow_pos (by omega) j) hL
  have hLjone : (1 : ℝ) ≤ Lj := by exact_mod_cast hLj
  have hweight : (Lj : ℝ) ^ (-sigma) ≤ (Lj : ℝ)⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hLjone (by linarith)
  have hdelta : 0 ≤ finiteHalaszGaussianBetaDensity Cβ I S :=
    finiteHalaszGaussianBetaDensity_nonneg hCβ hIlo hI
  have hrem : 0 ≤ finiteHalaszGaussianBetaRemainder I S := by
    unfold finiteHalaszGaussianBetaRemainder
    positivity
  have hA : 0 ≤
      (((2 ^ (j + 1) * L : ℕ) : ℝ) *
          finiteHalaszGaussianBetaDensity Cβ I S +
        finiteHalaszGaussianBetaRemainder I S) := by positivity
  have hfirst := mul_le_mul_of_nonneg_left hweight hA
  have hU : 2 ^ (j + 1) * L = 2 * Lj := by
    dsimp only [Lj]
    rw [pow_succ]
    ring
  have hLjR : (0 : ℝ) < Lj := by exact_mod_cast hLj
  have hfirst' :
      ((((2 ^ (j + 1) * L : ℕ) : ℝ) *
          finiteHalaszGaussianBetaDensity Cβ I S +
        finiteHalaszGaussianBetaRemainder I S) *
          ((Lj : ℝ) ^ (-sigma))) ≤
        2 * finiteHalaszGaussianBetaDensity Cβ I S +
          finiteHalaszGaussianBetaRemainder I S * (Lj : ℝ)⁻¹ := by
    calc
      _ ≤ (((2 ^ (j + 1) * L : ℕ) : ℝ) *
          finiteHalaszGaussianBetaDensity Cβ I S +
        finiteHalaszGaussianBetaRemainder I S) * (Lj : ℝ)⁻¹ := hfirst
      _ = 2 * finiteHalaszGaussianBetaDensity Cβ I S +
          finiteHalaszGaussianBetaRemainder I S * (Lj : ℝ)⁻¹ := by
        rw [hU]
        push_cast
        field_simp
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hLleLj : (L : ℝ) ≤ Lj := by
    exact_mod_cast Nat.le_mul_of_pos_left L (pow_pos (by omega) j)
  have hinv : (Lj : ℝ)⁻¹ ≤ (L : ℝ)⁻¹ := inv_anti₀ hLreal hLleLj
  have hsecond :
      2 * finiteHalaszGaussianBetaDensity Cβ I S +
          finiteHalaszGaussianBetaRemainder I S * (Lj : ℝ)⁻¹ ≤
        2 * finiteHalaszGaussianBetaDensity Cβ I S +
          finiteHalaszGaussianBetaRemainder I S * (L : ℝ)⁻¹ := by
    gcongr
  have htotal := hfirst'.trans hsecond
  have hleft0 : 0 ≤
      (((2 ^ (j + 1) * L : ℕ) : ℝ) *
        finiteHalaszGaussianBetaDensity Cβ I S +
        finiteHalaszGaussianBetaRemainder I S) *
          ((Lj : ℝ) ^ (-sigma)) :=
    mul_nonneg hA (Real.rpow_nonneg (Nat.cast_nonneg Lj) _)
  unfold finiteHalaszGaussianSchurShellScale
  change (((((2 ^ (j + 1) * L : ℕ) : ℝ) *
          finiteHalaszGaussianBetaDensity Cβ I S +
        finiteHalaszGaussianBetaRemainder I S) *
          ((Lj : ℝ) ^ (-sigma))) ^ 2) ≤ _
  calc
    _ ≤ (2 * finiteHalaszGaussianBetaDensity Cβ I S +
          finiteHalaszGaussianBetaRemainder I S * (L : ℝ)⁻¹) ^ 2 :=
      pow_le_pow_left₀ hleft0 htotal 2
    _ ≤ 8 * (finiteHalaszGaussianBetaDensity Cβ I S) ^ 2 +
        2 * (finiteHalaszGaussianBetaRemainder I S * (L : ℝ)⁻¹) ^ 2 := by
      nlinarith [sq_nonneg
        (2 * finiteHalaszGaussianBetaDensity Cβ I S -
          finiteHalaszGaussianBetaRemainder I S * (L : ℝ)⁻¹)]

/-- Summing the source-scale shell estimate costs only one factor `J`,
not `J²`. -/
theorem sum_finiteHalaszGaussianSchurShellScale_le_uniform
    {Cβ : ℝ} {I : ℕ × ℕ} {S L J : ℕ} {sigma : ℝ}
    (hCβ : 0 ≤ Cβ) (hIlo : 3 ≤ I.1) (hI : I.1 ≤ I.2)
    (hL : 0 < L) (hsigma : 1 ≤ sigma) :
    (∑ j ∈ Finset.range J,
        finiteHalaszGaussianSchurShellScale Cβ I S sigma L j) ≤
      (J : ℝ) *
        (8 * (finiteHalaszGaussianBetaDensity Cβ I S) ^ 2 +
          2 * (finiteHalaszGaussianBetaRemainder I S * (L : ℝ)⁻¹) ^ 2) := by
  calc
    (∑ j ∈ Finset.range J,
        finiteHalaszGaussianSchurShellScale Cβ I S sigma L j) ≤
      ∑ _j ∈ Finset.range J,
        (8 * (finiteHalaszGaussianBetaDensity Cβ I S) ^ 2 +
          2 * (finiteHalaszGaussianBetaRemainder I S * (L : ℝ)⁻¹) ^ 2) := by
      apply Finset.sum_le_sum
      intro j hj
      exact finiteHalaszGaussianSchurShellScale_le_uniform
        hCβ hIlo hI hL hsigma
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end

end Erdos67b.MRHalaszBands
