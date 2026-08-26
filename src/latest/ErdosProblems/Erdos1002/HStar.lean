import Mathlib.NumberTheory.ZetaValues

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The half-weighted inverse-square tail

The Fourier reconstruction samples the function

`H₊(u) = ∑_{k>u} k⁻² + ½ u⁻² 1_{u∈ℕ}`

only at rational points `u = n / s`.  The arithmetic definition below avoids
any ambiguity at equality: for each positive integer `k` it assigns weight
one when `n < k*s`, weight one half when `n = k*s`, and zero afterward.
-/

open Filter

namespace Erdos1002

noncomputable section

/-- The inverse-square summand, with the harmless totalized value zero at
`k = 0`. -/
def inverseSquare (k : ℕ) : ℝ :=
  if k = 0 then 0 else 1 / (k : ℝ) ^ 2

/-- One summand in the half-weighted tail sampled at `n / s`. -/
def hStarRatioWeight (n s k : ℕ) : ℝ :=
  if n < k * s then inverseSquare k
  else if n = k * s then inverseSquare k / 2
  else 0

/-- The sampled half-weighted inverse-square tail. -/
def hStarRatio (n s : ℕ) : ℝ :=
  ∑' k : ℕ, hStarRatioWeight n s k

theorem inverseSquare_nonneg (k : ℕ) : 0 ≤ inverseSquare k := by
  unfold inverseSquare
  split_ifs <;> positivity

theorem inverseSquare_eq (k : ℕ) :
    inverseSquare k = 1 / (k : ℝ) ^ 2 := by
  by_cases hk : k = 0
  · simp [inverseSquare, hk]
  · simp [inverseSquare, hk]

theorem summable_inverseSquare : Summable inverseSquare := by
  exact (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).congr
    (fun k ↦ (inverseSquare_eq k).symm)

theorem hStarRatioWeight_nonneg (n s k : ℕ) :
    0 ≤ hStarRatioWeight n s k := by
  unfold hStarRatioWeight
  split_ifs
  · exact inverseSquare_nonneg k
  · exact div_nonneg (inverseSquare_nonneg k) (by norm_num)
  · exact le_rfl

theorem hStarRatioWeight_le_inverseSquare (n s k : ℕ) :
    hStarRatioWeight n s k ≤ inverseSquare k := by
  unfold hStarRatioWeight
  split_ifs
  · exact le_rfl
  · nlinarith [inverseSquare_nonneg k]
  · exact inverseSquare_nonneg k

theorem summable_hStarRatioWeight (n s : ℕ) :
    Summable (hStarRatioWeight n s) := by
  apply summable_inverseSquare.of_nonneg_of_le
  · exact fun k ↦ hStarRatioWeight_nonneg n s k
  · exact fun k ↦ hStarRatioWeight_le_inverseSquare n s k

theorem hStarRatio_nonneg (n s : ℕ) : 0 ≤ hStarRatio n s := by
  exact tsum_nonneg fun k ↦ hStarRatioWeight_nonneg n s k

theorem hStarRatio_le_zetaTwo (n s : ℕ) :
    hStarRatio n s ≤ Real.pi ^ 2 / 6 := by
  rw [hStarRatio, ← hasSum_zeta_two.tsum_eq]
  exact (summable_hStarRatioWeight n s).tsum_le_tsum
    (fun k ↦ (hStarRatioWeight_le_inverseSquare n s k).trans_eq (inverseSquare_eq k))
    hasSum_zeta_two.summable

theorem hStarRatioWeight_antitone (s k : ℕ) :
    Antitone fun n ↦ hStarRatioWeight n s k := by
  intro n m hnm
  by_cases hmlt : m < k * s
  · have hnlt : n < k * s := lt_of_le_of_lt hnm hmlt
    simp [hStarRatioWeight, hmlt, hnlt]
  · by_cases hmeq : m = k * s
    · subst m
      by_cases hneq : n = k * s
      · subst n
        rfl
      · have hnlt : n < k * s := by omega
        simp [hStarRatioWeight, hnlt]
        nlinarith [inverseSquare_nonneg k]
    · have hmgt : k * s < m := by omega
      have hmzero : hStarRatioWeight m s k = 0 := by
        simp [hStarRatioWeight, hmlt, hmeq]
      change hStarRatioWeight m s k ≤ hStarRatioWeight n s k
      rw [hmzero]
      exact hStarRatioWeight_nonneg n s k

/-- The midpoint convention preserves monotonicity in the sampled argument. -/
theorem hStarRatio_antitone (s : ℕ) : Antitone fun n ↦ hStarRatio n s := by
  intro n m hnm
  unfold hStarRatio
  exact (summable_hStarRatioWeight m s).tsum_le_tsum
    (fun k ↦ hStarRatioWeight_antitone s k hnm)
    (summable_hStarRatioWeight n s)

theorem hStarRatio_zero_scale (n : ℕ) :
    hStarRatio n 0 = if n = 0 then Real.pi ^ 2 / 12 else 0 := by
  by_cases hn : n = 0
  · subst n
    simp only [if_pos]
    rw [hStarRatio]
    simp only [hStarRatioWeight, Nat.mul_zero, lt_self_iff_false, ↓reduceIte,
      inverseSquare_eq]
    calc
      (∑' k : ℕ, 1 / (k : ℝ) ^ 2 / 2) =
          ∑' k : ℕ, (1 / 2 : ℝ) * (1 / (k : ℝ) ^ 2) := by
            congr 1
            funext k
            ring
      _ = (1 / 2 : ℝ) * (Real.pi ^ 2 / 6) :=
        (hasSum_zeta_two.mul_left (1 / 2 : ℝ)).tsum_eq
      _ = Real.pi ^ 2 / 12 := by ring
  · simp [hStarRatio, hStarRatioWeight, hn]

/-- A telescoping majorant for an inverse-square tail starting at a positive
integer. -/
theorem hasSum_two_mul_inverse_telescoping (M : ℕ) (hM : 0 < M) :
    HasSum
      (fun j : ℕ ↦ 2 *
        (1 / ((M + j : ℕ) : ℝ) - 1 / ((M + j + 1 : ℕ) : ℝ)))
      (2 / (M : ℝ)) := by
  have hbase : HasSum
      (fun j : ℕ ↦
        1 / ((M + j : ℕ) : ℝ) - 1 / ((M + j + 1 : ℕ) : ℝ))
      (1 / (M : ℝ)) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg]
    · have htail : Tendsto (fun n : ℕ ↦ 1 / ((M + n : ℕ) : ℝ))
          atTop (nhds 0) := by
        simpa only [Nat.add_comm] using!
          ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
            (Filter.tendsto_add_atTop_nat M))
      have htel :
          (fun n : ℕ ↦ ∑ i ∈ Finset.range n,
            (1 / ((M + i : ℕ) : ℝ) - 1 / ((M + i + 1 : ℕ) : ℝ))) =
          fun n : ℕ ↦ 1 / (M : ℝ) - 1 / ((M + n : ℕ) : ℝ) := by
        funext n
        simpa only [Nat.add_assoc, Nat.add_zero] using!
          Finset.sum_range_sub' (fun i : ℕ ↦ 1 / ((M + i : ℕ) : ℝ)) n
      rw [htel]
      have hc : Tendsto (fun _ : ℕ ↦ 1 / (M : ℝ)) atTop
          (nhds (1 / (M : ℝ))) := tendsto_const_nhds
      simpa only [sub_zero] using! hc.sub htail
    · intro j
      have hjpos : (0 : ℝ) < (M + j : ℕ) := by positivity
      have hjle : ((M + j : ℕ) : ℝ) ≤ (M + j + 1 : ℕ) := by
        exact_mod_cast Nat.le_succ (M + j)
      exact sub_nonneg.mpr (one_div_le_one_div_of_le hjpos hjle)
  simpa only [div_eq_mul_inv, one_mul] using! hbase.mul_left 2

theorem inverseSquare_nat_add_le_telescoping (M j : ℕ) (hM : 0 < M) :
    inverseSquare (M + j) ≤
      2 * (1 / ((M + j : ℕ) : ℝ) -
        1 / ((M + j + 1 : ℕ) : ℝ)) := by
  have hk : (0 : ℝ) < (M + j : ℕ) := by positivity
  have hk1 : (0 : ℝ) < (M + j + 1 : ℕ) := by positivity
  have hkge : (1 : ℝ) ≤ (M + j : ℕ) := by
    exact_mod_cast (show 1 ≤ M + j by omega)
  have hcast : ((M + j + 1 : ℕ) : ℝ) = ((M + j : ℕ) : ℝ) + 1 := by
    norm_num
  rw [inverseSquare_eq]
  rw [hcast]
  field_simp
  nlinarith

/-- Uniform inverse-square tail estimate with an explicit constant. -/
theorem tsum_inverseSquare_nat_add_le (M : ℕ) (hM : 0 < M) :
    (∑' j : ℕ, inverseSquare (M + j)) ≤ 2 / (M : ℝ) := by
  have hleft : Summable (fun j : ℕ ↦ inverseSquare (M + j)) := by
    have hinj : Function.Injective (fun j : ℕ ↦ M + j) :=
      fun _ _ h ↦ Nat.add_left_cancel h
    simpa only [Function.comp_apply] using!
      summable_inverseSquare.comp_injective hinj
  have hright := (hasSum_two_mul_inverse_telescoping M hM).summable
  calc
    (∑' j : ℕ, inverseSquare (M + j)) ≤
        ∑' j : ℕ, 2 *
          (1 / ((M + j : ℕ) : ℝ) -
            1 / ((M + j + 1 : ℕ) : ℝ)) :=
      hleft.tsum_le_tsum
        (fun j ↦ inverseSquare_nat_add_le_telescoping M j hM) hright
    _ = 2 / (M : ℝ) :=
      (hasSum_two_mul_inverse_telescoping M hM).tsum_eq

/-- The sampled half-weighted tail has the decay used throughout the
Ramanujan square-function argument.  The constant is intentionally explicit;
the manuscript only needs an absolute `O(s/n)` bound. -/
theorem hStarRatio_le_four_mul_scale_div (n s : ℕ)
    (hn : 0 < n) (hs : 0 < s) :
    hStarRatio n s ≤ 4 * (s : ℝ) / (n : ℝ) := by
  by_cases hns : n < s
  · have hpi : Real.pi ^ 2 / 6 ≤ (4 : ℝ) := by
      nlinarith [Real.pi_pos, Real.pi_le_four]
    have hsn : (n : ℝ) ≤ (s : ℝ) := by exact_mod_cast hns.le
    calc
      hStarRatio n s ≤ Real.pi ^ 2 / 6 := hStarRatio_le_zetaTwo n s
      _ ≤ 4 := hpi
      _ ≤ 4 * (s : ℝ) / (n : ℝ) := by
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ))]
        nlinarith
  · let M : ℕ := n / s
    have hsn : s ≤ n := le_of_not_gt hns
    have hM : 0 < M := by
      dsimp [M]
      exact Nat.div_pos hsn hs
    have hprefix :
        ∑ k ∈ Finset.range M, hStarRatioWeight n s k = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hklt : k < M := Finset.mem_range.mp hk
      have hsucc : k + 1 ≤ n / s := Nat.succ_le_iff.mpr hklt
      have hmul : (k + 1) * s ≤ n :=
        (Nat.le_div_iff_mul_le hs).mp hsucc
      have hks : k * s < n := by
        have hstep : k * s < (k + 1) * s := by
          exact Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self k) hs
        exact hstep.trans_le hmul
      simp [hStarRatioWeight, not_lt.mpr hks.le, ne_of_gt hks]
    have hshift : hStarRatio n s =
        ∑' j : ℕ, hStarRatioWeight n s (j + M) := by
      have hsplit :=
        (summable_hStarRatioWeight n s).sum_add_tsum_nat_add M
      rw [hprefix, zero_add] at hsplit
      simpa [hStarRatio, Nat.add_comm] using! hsplit.symm
    have htail : hStarRatio n s ≤
        ∑' j : ℕ, inverseSquare (M + j) := by
      rw [hshift]
      have hleft : Summable
          (fun j : ℕ ↦ hStarRatioWeight n s (j + M)) := by
        have hinj : Function.Injective (fun j : ℕ ↦ j + M) :=
          fun _ _ h ↦ Nat.add_right_cancel h
        simpa only [Function.comp_apply] using!
          (summable_hStarRatioWeight n s).comp_injective hinj
      have hright : Summable (fun j : ℕ ↦ inverseSquare (M + j)) := by
        have hinj : Function.Injective (fun j : ℕ ↦ M + j) :=
          fun _ _ h ↦ Nat.add_left_cancel h
        simpa only [Function.comp_apply] using!
          summable_inverseSquare.comp_injective hinj
      exact hleft.tsum_le_tsum
        (fun j ↦ (hStarRatioWeight_le_inverseSquare n s (j + M)).trans_eq
          (by rw [Nat.add_comm])) hright
    have hcoarse : n ≤ M * s + s - 1 := by
      exact (Nat.div_le_iff_le_mul hs).mp (le_refl M)
    have hsM : s ≤ M * s := by
      simpa using! Nat.mul_le_mul_right s hM
    have hn2 : n < 2 * (M * s) := by omega
    have hn2R : (2 : ℝ) * (n : ℝ) ≤
        (4 * (s : ℝ)) * (M : ℝ) := by
      have hnat : 2 * n ≤ (4 * s) * M := by
        calc
          2 * n ≤ 2 * (2 * (M * s)) := Nat.mul_le_mul_left 2 hn2.le
          _ = (4 * s) * M := by ring
      exact_mod_cast hnat
    calc
      hStarRatio n s ≤ ∑' j : ℕ, inverseSquare (M + j) := htail
      _ ≤ 2 / (M : ℝ) := tsum_inverseSquare_nat_add_le M hM
      _ ≤ 4 * (s : ℝ) / (n : ℝ) := by
        rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (M : ℝ))
          (by positivity : (0 : ℝ) < (n : ℝ))]
        exact hn2R

/-- The positive-frequency square sum has the linear-in-scale bound required
by the diagonal part of the Ramanujan square function.  The term `n = 0` is
explicitly removed, matching the manuscript's sum over `n ≥ 1`. -/
theorem summable_hStarRatio_positive_square (s : ℕ) (hs : 0 < s) :
    Summable (fun n : ℕ ↦ if n = 0 then 0 else hStarRatio n s ^ 2) := by
  let C : ℝ := 16 * (s : ℝ) ^ 2
  have hdom : Summable (fun n : ℕ ↦ C * inverseSquare n) :=
    summable_inverseSquare.mul_left C
  apply Summable.of_nonneg_of_le
    (g := fun n : ℕ ↦ if n = 0 then 0 else hStarRatio n s ^ 2)
    (f := fun n : ℕ ↦ C * inverseSquare n)
  · intro n
    split_ifs
    · exact le_rfl
    · positivity
  · intro n
    by_cases hn : n = 0
    · simp [hn, inverseSquare]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hbound := hStarRatio_le_four_mul_scale_div n s hnpos hs
      have hpow : hStarRatio n s ^ 2 ≤
          (4 * (s : ℝ) / (n : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (hStarRatio_nonneg n s) hbound 2
      rw [if_neg hn]
      calc
        hStarRatio n s ^ 2 ≤ (4 * (s : ℝ) / (n : ℝ)) ^ 2 := hpow
        _ = C * inverseSquare n := by
          dsimp [C]
          rw [inverseSquare_eq]
          ring
  · exact hdom

theorem tsum_hStarRatio_positive_square_le (s : ℕ) (hs : 0 < s) :
    (∑' n : ℕ, if n = 0 then 0 else hStarRatio n s ^ 2) ≤
      64 * (s : ℝ) := by
  let f : ℕ → ℝ := fun n ↦ if n = 0 then 0 else hStarRatio n s ^ 2
  let C : ℝ := 16 * (s : ℝ) ^ 2
  have hsum : Summable f := by
    simpa only [f] using! summable_hStarRatio_positive_square s hs
  have hsplit := hsum.sum_add_tsum_nat_add (s + 1)
  have hpi : Real.pi ^ 2 / 6 ≤ (4 : ℝ) := by
    nlinarith [Real.pi_pos, Real.pi_le_four]
  have hprefix : (∑ n ∈ Finset.range (s + 1), f n) ≤
      32 * (s : ℝ) := by
    calc
      (∑ n ∈ Finset.range (s + 1), f n) ≤
          ∑ _n ∈ Finset.range (s + 1), (16 : ℝ) := by
        apply Finset.sum_le_sum
        intro n _hnmem
        by_cases hn : n = 0
        · simp [f, hn]
        · have hz := hStarRatio_le_zetaTwo n s
          have hnonneg := hStarRatio_nonneg n s
          simp only [f, if_neg hn]
          nlinarith [sq_nonneg (hStarRatio n s)]
      _ = 16 * (s + 1 : ℕ) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
        ring
      _ ≤ 32 * (s : ℝ) := by
        have hcast : ((s + 1 : ℕ) : ℝ) ≤ 2 * (s : ℝ) := by
          exact_mod_cast (show s + 1 ≤ 2 * s by omega)
        nlinarith
  have htailSummable : Summable (fun j : ℕ ↦ f (j + (s + 1))) := by
    have hinj : Function.Injective (fun j : ℕ ↦ j + (s + 1)) :=
      fun _ _ h ↦ Nat.add_right_cancel h
    simpa only [Function.comp_apply] using! hsum.comp_injective hinj
  have hinvSummable : Summable
      (fun j : ℕ ↦ inverseSquare ((s + 1) + j)) := by
    have hinj : Function.Injective (fun j : ℕ ↦ (s + 1) + j) :=
      fun _ _ h ↦ Nat.add_left_cancel h
    simpa only [Function.comp_apply] using!
      summable_inverseSquare.comp_injective hinj
  have htailPoint (j : ℕ) :
      f (j + (s + 1)) ≤ C * inverseSquare ((s + 1) + j) := by
    have hnpos : 0 < (s + 1) + j := by omega
    have hbound :=
      hStarRatio_le_four_mul_scale_div ((s + 1) + j) s hnpos hs
    have hpow : hStarRatio ((s + 1) + j) s ^ 2 ≤
        (4 * (s : ℝ) / ((s + 1) + j : ℕ)) ^ 2 :=
      pow_le_pow_left₀ (hStarRatio_nonneg ((s + 1) + j) s) hbound 2
    rw [show f (j + (s + 1)) = hStarRatio ((s + 1) + j) s ^ 2 by
      simp [f, Nat.add_comm]]
    calc
      hStarRatio ((s + 1) + j) s ^ 2 ≤
          (4 * (s : ℝ) / ((s + 1) + j : ℕ)) ^ 2 := hpow
      _ = C * inverseSquare ((s + 1) + j) := by
        dsimp [C]
        rw [inverseSquare_eq]
        ring
  have htail : (∑' j : ℕ, f (j + (s + 1))) ≤ 32 * (s : ℝ) := by
    calc
      (∑' j : ℕ, f (j + (s + 1))) ≤
          ∑' j : ℕ, C * inverseSquare ((s + 1) + j) :=
        htailSummable.tsum_le_tsum htailPoint (hinvSummable.mul_left C)
      _ = C * (∑' j : ℕ, inverseSquare ((s + 1) + j)) :=
        tsum_mul_left
      _ ≤ C * (2 / ((s + 1 : ℕ) : ℝ)) := by
        gcongr
        exact tsum_inverseSquare_nat_add_le (s + 1) (by omega)
      _ ≤ 32 * (s : ℝ) := by
        dsimp [C]
        calc
          16 * (s : ℝ) ^ 2 * (2 / ((s + 1 : ℕ) : ℝ)) =
              32 * (s : ℝ) ^ 2 / ((s + 1 : ℕ) : ℝ) := by ring
          _ ≤ 32 * (s : ℝ) := by
            rw [div_le_iff₀ (by positivity : (0 : ℝ) < (s + 1 : ℕ))]
            norm_num [Nat.cast_add, Nat.cast_one]
            nlinarith [show (0 : ℝ) ≤ (s : ℝ) by positivity]
  calc
    (∑' n : ℕ, if n = 0 then 0 else hStarRatio n s ^ 2) =
        (∑' n : ℕ, f n) := by rfl
    _ = (∑ n ∈ Finset.range (s + 1), f n) +
        ∑' j : ℕ, f (j + (s + 1)) := hsplit.symm
    _ ≤ 32 * (s : ℝ) + 32 * (s : ℝ) := add_le_add hprefix htail
    _ = 64 * (s : ℝ) := by ring

/-- Products of two sampled midpoint tails remain nonnegative and antitone;
this is the precise weight property used by discrete Abel summation. -/
theorem hStarRatio_mul_antitone (s t : ℕ) :
    Antitone fun n ↦ hStarRatio n s * hStarRatio n t := by
  intro n m hnm
  exact mul_le_mul (hStarRatio_antitone s hnm) (hStarRatio_antitone t hnm)
    (hStarRatio_nonneg m t) (hStarRatio_nonneg n s)

theorem sum_Ico_abs_sub_antitone {f : ℕ → ℝ} (hf : Antitone f)
    {a b : ℕ} (hab : a ≤ b) :
    (∑ n ∈ Finset.Ico a b, |f (n + 1) - f n|) = f a - f b := by
  have hsign (n : ℕ) : f (n + 1) - f n ≤ 0 :=
    sub_nonpos.mpr (hf (Nat.le_succ n))
  simp_rw [abs_of_nonpos (hsign _), neg_sub]
  have htel := Finset.sum_Ico_sub f hab
  calc
    (∑ n ∈ Finset.Ico a b, (f n - f (n + 1))) =
        ∑ n ∈ Finset.Ico a b, -(f (n + 1) - f n) := by
      apply Finset.sum_congr rfl
      intro n _hn
      ring
    _ = -(∑ n ∈ Finset.Ico a b, (f (n + 1) - f n)) := by
      rw [Finset.sum_neg_distrib]
    _ = f a - f b := by rw [htel]; ring

/-- Explicit total-variation envelope for the product weights in the
off-diagonal Ramanujan estimate. -/
theorem hStarRatio_mul_totalVariation_le (s t a b : ℕ) (hab : a ≤ b) :
    (∑ n ∈ Finset.Ico a b,
      |hStarRatio (n + 1) s * hStarRatio (n + 1) t -
        hStarRatio n s * hStarRatio n t|) ≤
      (Real.pi ^ 2 / 6) ^ 2 := by
  let f : ℕ → ℝ := fun n ↦ hStarRatio n s * hStarRatio n t
  rw [show (∑ n ∈ Finset.Ico a b,
      |hStarRatio (n + 1) s * hStarRatio (n + 1) t -
        hStarRatio n s * hStarRatio n t|) =
      ∑ n ∈ Finset.Ico a b, |f (n + 1) - f n| by rfl]
  rw [sum_Ico_abs_sub_antitone (hStarRatio_mul_antitone s t) hab]
  have hfb : 0 ≤ f b := mul_nonneg
    (hStarRatio_nonneg b s) (hStarRatio_nonneg b t)
  have hfa : f a ≤ (Real.pi ^ 2 / 6) ^ 2 := by
    dsimp [f]
    nlinarith [hStarRatio_nonneg a s, hStarRatio_nonneg a t,
      hStarRatio_le_zetaTwo a s, hStarRatio_le_zetaTwo a t,
      sq_nonneg (hStarRatio a s - hStarRatio a t)]
  linarith

end

end Erdos1002
