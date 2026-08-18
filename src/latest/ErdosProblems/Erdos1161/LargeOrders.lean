import ErdosProblems.Erdos1161.CycleTail
import ErdosProblems.Erdos1161.PrimePowerAssignment
import ErdosProblems.Erdos1161.RestrictedCycles
import ErdosProblems.Erdos1161.SigmaBound

/-!
# Large-order anticoncentration for Erdős Problem 1161

This file proves the uniform estimate which is the first step in Beker's
structural argument.  The proof partitions an order fiber into three ranges
according to the total number of cycles.  The cutoffs are
`(log log n)^2` and a fixed multiple of `log n`; the three ranges are
controlled respectively by the prime-power, restricted-cycle, and
unrestricted-cycle estimates from `CycleBounds`.
-/

open Filter Finset Real
open scoped BigOperators Topology

namespace Erdos1161

noncomputable section

/-! ## Exact finite cycle-count decomposition -/

/-- The part of the order-`m` fiber consisting of permutations with exactly
`ell` cycles, fixed points included. -/
def orderExactCycleCount (n m ell : ℕ) : ℕ :=
  ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter fun σ ↦
    orderOf σ = m ∧ totalCycleCount σ = ell).card

/-- Its normalization by `n!`. -/
def orderExactCycleProbability (n m ell : ℕ) : ℝ :=
  (orderExactCycleCount n m ell : ℝ) / (n.factorial : ℝ)

@[simp] theorem orderExactCycleCount_zero_cycles_of_pos
    {n m : ℕ} (hn : 0 < n) : orderExactCycleCount n m 0 = 0 := by
  classical
  rw [orderExactCycleCount, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff]
  intro σ _ hσ
  have hcard : 0 < (fullCycleType σ).card := by
    by_contra h
    have hempty : fullCycleType σ = 0 := Multiset.card_eq_zero.mp (by omega)
    have hsum := sum_fullCycleType σ
    rw [hempty] at hsum
    simp at hsum
    omega
  exact hcard.ne' hσ.2

theorem orderExactCycleCount_eq_zero_of_lt {n m ell : ℕ} (h : n < ell) :
    orderExactCycleCount n m ell = 0 := by
  classical
  rw [orderExactCycleCount, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff]
  intro σ _ hσ
  exact (not_le_of_gt h) (hσ.2 ▸ totalCycleCount_le σ)

theorem sum_orderExactCycleCount (n m : ℕ) :
    ∑ ell ∈ Finset.range (n + 1), orderExactCycleCount n m ell = orderCount n m := by
  classical
  rw [orderCount_eq_card_filter]
  let S : Finset (Equiv.Perm (Fin n)) :=
    Finset.univ.filter fun σ ↦ orderOf σ = m
  calc
    ∑ ell ∈ Finset.range (n + 1), orderExactCycleCount n m ell =
        ∑ ell ∈ Finset.range (n + 1),
          ((S.filter fun σ ↦ totalCycleCount σ = ell).card) := by
            apply Finset.sum_congr rfl
            intro ell _
            apply congrArg Finset.card
            ext σ
            simp [orderExactCycleCount, S, and_assoc]
    _ = S.card := by
      have h := Finset.sum_card_fiberwise_eq_card_filter S
        (Finset.range (n + 1)) totalCycleCount
      rw [h]
      congr 1
      ext σ
      simp only [Finset.mem_filter, Finset.mem_range, S]
      constructor
      · rintro ⟨hσ, -⟩
        exact hσ
      · intro hσ
        exact ⟨hσ, Nat.lt_succ_of_le (totalCycleCount_le σ)⟩
    _ = ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
        (fun σ ↦ orderOf σ = m)).card := rfl

theorem sum_orderExactCycleProbability (n m : ℕ) :
    ∑ ell ∈ Finset.range (n + 1), orderExactCycleProbability n m ell =
      orderProbability n m := by
  simp_rw [orderExactCycleProbability, orderProbability]
  rw [← Finset.sum_div, ← Nat.cast_sum, sum_orderExactCycleCount]

theorem orderExactCycleProbability_nonneg (n m ell : ℕ) :
    0 ≤ orderExactCycleProbability n m ell := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem orderExactCycleCount_le_orderCount (n m ell : ℕ) :
    orderExactCycleCount n m ell ≤ orderCount n m := by
  rw [orderExactCycleCount, orderCount_eq_card_filter]
  apply Finset.card_le_card
  intro σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact And.left

theorem orderExactCycleCount_eq_zero_of_pow_lt
    {n m ell : ℕ} (h : n ^ ell < m) :
    orderExactCycleCount n m ell = 0 := by
  simpa [orderExactCycleCount, cycleOrderCount] using
    (cycleOrderCount_eq_zero_of_pow_lt h)

/-! ## The two cycle-count cutoffs -/

/-- The upper cutoff for the few-cycle regime.  A square is used so that it
dominates every fixed multiple of `log log n`, while its logarithm remains
`o(log log n)`. -/
def lowCycleCutoff (n : ℕ) : ℕ :=
  ⌈(Real.log (Real.log (n : ℝ))) ^ 2⌉₊

/-- The lower cutoff for the cycle-count tail. -/
def highCycleCutoff (n : ℕ) : ℕ :=
  ⌈16 * Real.log (n : ℝ)⌉₊

private theorem eventually_cycleCutoff_bounds :
    ∀ᶠ n : ℕ in atTop,
      let L := Real.log (Real.log (n : ℝ))
      10 < L ∧
      L ^ 2 ≤ (lowCycleCutoff n : ℝ) ∧
      (lowCycleCutoff n : ℝ) < L ^ 2 + 1 ∧
      Real.log (lowCycleCutoff n : ℝ) ≤ L / 48 ∧
      ((lowCycleCutoff n + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ (1 / 18 : ℝ) ∧
      lowCycleCutoff n ≤ highCycleCutoff n ∧
      16 * Real.log (n : ℝ) ≤ (highCycleCutoff n : ℝ) ∧
      (highCycleCutoff n : ℝ) ≤ 17 * Real.log (n : ℝ) := by
  have hL : Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
    tendsto_log_log_coe_at_top
  have hN : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hpoly48 : ∀ᶠ x : ℝ in atTop,
      |x ^ 2| ≤ (1 / 2 : ℝ) * |Real.exp ((1 / 48 : ℝ) * x)| :=
    (isLittleO_pow_exp_pos_mul_atTop 2 (by norm_num : (0 : ℝ) < 1 / 48)).bound
      (by norm_num)
  have hpoly1 : ∀ᶠ x : ℝ in atTop,
      |x ^ 2| ≤ (1 / 4 : ℝ) * |Real.exp x| := by
    simpa only [one_mul, Real.norm_eq_abs] using
      (isLittleO_pow_exp_pos_mul_atTop 2 (by norm_num : (0 : ℝ) < 1)).bound
        (by norm_num : (0 : ℝ) < 1 / 4)
  have hlogpow : ∀ᶠ x : ℝ in atTop,
      |Real.log x| ≤ (1 : ℝ) * |x ^ (1 / 18 : ℝ)| :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 18)).bound
      zero_lt_one
  filter_upwards [hL (eventually_gt_atTop (10 : ℝ)), hL hpoly48,
      hL hpoly1, hN hlogpow, eventually_ge_atTop (3 : ℕ)] with
      n hL10 hp48 hp1 hlogpowN hn3
  let L := Real.log (Real.log (n : ℝ))
  change 10 < L at hL10
  change |L ^ 2| ≤ (1 / 2 : ℝ) * |Real.exp ((1 / 48 : ℝ) * L)| at hp48
  change |L ^ 2| ≤ (1 / 4 : ℝ) * |Real.exp L| at hp1
  change |Real.log (n : ℝ)| ≤
    (1 : ℝ) * |(n : ℝ) ^ (1 / 18 : ℝ)| at hlogpowN
  have hLpos : 0 < L := by linarith
  have hlognpos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlogn_eq : Real.exp L = Real.log (n : ℝ) :=
    Real.exp_log hlognpos
  have hp48' : L ^ 2 ≤ (1 / 2 : ℝ) * Real.exp ((1 / 48 : ℝ) * L) := by
    simpa [abs_of_nonneg (sq_nonneg L), abs_of_pos (Real.exp_pos _), L] using hp48
  have hp1' : L ^ 2 ≤ (1 / 4 : ℝ) * Real.exp L := by
    simpa [abs_of_nonneg (sq_nonneg L), abs_of_pos (Real.exp_pos _), L] using hp1
  have hceilLow : L ^ 2 ≤ (lowCycleCutoff n : ℝ) := by
    exact Nat.le_ceil (L ^ 2)
  have hceilHigh : (lowCycleCutoff n : ℝ) < L ^ 2 + 1 := by
    exact Nat.ceil_lt_add_one (sq_nonneg L)
  have hlowExp : (lowCycleCutoff n : ℝ) ≤ Real.exp (L / 48) := by
    have hsq : L ^ 2 + 1 ≤ 2 * L ^ 2 := by nlinarith [sq_nonneg L]
    have hexp : 2 * L ^ 2 ≤ Real.exp ((1 / 48 : ℝ) * L) := by
      nlinarith [hp48']
    have heq : (1 / 48 : ℝ) * L = L / 48 := by
      simpa [div_eq_mul_inv] using mul_comm (1 / 48 : ℝ) L
    rw [heq] at hexp
    exact hceilHigh.le.trans (hsq.trans hexp)
  have hlogLow : Real.log (lowCycleCutoff n : ℝ) ≤ L / 48 := by
    rw [Real.log_le_iff_le_exp (lt_of_lt_of_le (sq_pos_of_pos hLpos) hceilLow)]
    simpa [div_eq_mul_inv, mul_comm] using hlowExp
  have hlowPlus : ((lowCycleCutoff n + 1 : ℕ) : ℝ) ≤ Real.log (n : ℝ) := by
    have hcast : ((lowCycleCutoff n + 1 : ℕ) : ℝ) =
        (lowCycleCutoff n : ℝ) + 1 := by push_cast; rfl
    rw [hcast]
    have hsq : L ^ 2 + 2 ≤ 4 * L ^ 2 := by nlinarith [sq_nonneg L]
    have hexp : 4 * L ^ 2 ≤ Real.exp L := by nlinarith [hp1']
    calc
      (lowCycleCutoff n : ℝ) + 1 ≤ (L ^ 2 + 1) + 1 := by linarith
      _ = L ^ 2 + 2 := by ring
      _ ≤ 4 * L ^ 2 := hsq
      _ ≤ Real.exp L := hexp
      _ = Real.log (n : ℝ) := hlogn_eq
  have hlogpowN' : Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 / 18 : ℝ) := by
    rw [abs_of_pos hlognpos, one_mul,
      abs_of_nonneg (Real.rpow_nonneg (by positivity) _)] at hlogpowN
    exact hlogpowN
  have hhighLower : 16 * Real.log (n : ℝ) ≤ (highCycleCutoff n : ℝ) :=
    Nat.le_ceil _
  have hhighUpper : (highCycleCutoff n : ℝ) ≤ 17 * Real.log (n : ℝ) := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ 16 * Real.log (n : ℝ) by positivity)
    dsimp [highCycleCutoff] at hc ⊢
    nlinarith
  have hlowHigh : lowCycleCutoff n ≤ highCycleCutoff n := by
    have hcast : (lowCycleCutoff n : ℝ) ≤ (highCycleCutoff n : ℝ) := calc
      (lowCycleCutoff n : ℝ) ≤ ((lowCycleCutoff n + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_add_right (lowCycleCutoff n) 1
      _ ≤ Real.log (n : ℝ) := hlowPlus
      _ ≤ (highCycleCutoff n : ℝ) := by nlinarith [hhighLower]
    exact_mod_cast hcast
  exact ⟨hL10, hceilLow, hceilHigh, hlogLow,
    hlowPlus.trans hlogpowN', hlowHigh, hhighLower, hhighUpper⟩

private theorem le_of_fourth_le_cube {n m : ℕ} (hn : 0 < n)
    (h : n ^ 4 ≤ m ^ 3) : n ≤ m := by
  by_contra hnm
  have hlt : m < n := Nat.lt_of_not_ge hnm
  have hcubes : m ^ 3 < n ^ 3 := Nat.pow_lt_pow_left hlt (by norm_num)
  have hcubefour : n ^ 3 ≤ n ^ 4 := Nat.pow_le_pow_right hn (by omega)
  omega

private theorem fewCyclePower_le_twelfth_rpow
    {n m ell : ℕ}
    (hnm : n ≤ m)
    (hL : 10 < Real.log (Real.log (n : ℝ)))
    (hcutlog : Real.log (lowCycleCutoff n : ℝ) ≤
      Real.log (Real.log (n : ℝ)) / 48)
    (hellpos : 0 < ell) (hell : ell ≤ lowCycleCutoff n)
    (homega : (distinctPrimeFactorCount m : ℝ) <
      4 * Real.log (m : ℝ) / Real.log (Real.log (m : ℝ))) :
    (ell : ℝ) ^ distinctPrimeFactorCount m ≤ (m : ℝ) ^ (1 / 12 : ℝ) := by
  have hnposNat : 0 < n := by
    by_contra hn
    have : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    norm_num at hL
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hnposNat
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le hnpos (by exact_mod_cast hnm)
  have hn2 : 2 ≤ n := by
    by_contra hn
    have : n = 1 := by omega
    subst n
    norm_num at hL
  have hnlogpos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlogmono : Real.log (n : ℝ) ≤ Real.log (m : ℝ) :=
    Real.log_le_log hnpos (by exact_mod_cast hnm)
  have hloglogmono : Real.log (Real.log (n : ℝ)) ≤
      Real.log (Real.log (m : ℝ)) :=
    Real.log_le_log hnlogpos hlogmono
  have hLLm : 0 < Real.log (Real.log (m : ℝ)) := by linarith
  have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast hellpos
  have hcutpos : (0 : ℝ) < lowCycleCutoff n := by
    have hellposR : (0 : ℝ) < ell := by exact_mod_cast hellpos
    have hellR' : (ell : ℝ) ≤ lowCycleCutoff n := by exact_mod_cast hell
    exact hellposR.trans_le hellR'
  have hlogell : Real.log (ell : ℝ) ≤
      Real.log (Real.log (m : ℝ)) / 48 := by
    calc
      Real.log (ell : ℝ) ≤ Real.log (lowCycleCutoff n : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hell)
      _ ≤ Real.log (Real.log (n : ℝ)) / 48 := hcutlog
      _ ≤ Real.log (Real.log (m : ℝ)) / 48 := by linarith
  have hlogell_nonneg : 0 ≤ Real.log (ell : ℝ) := Real.log_nonneg hellR
  have hlogmpos : 0 < Real.log (m : ℝ) := lt_of_lt_of_le hnlogpos hlogmono
  have hprod : (distinctPrimeFactorCount m : ℝ) * Real.log (ell : ℝ) ≤
      (1 / 12 : ℝ) * Real.log (m : ℝ) := by
    calc
      (distinctPrimeFactorCount m : ℝ) * Real.log (ell : ℝ) ≤
          (4 * Real.log (m : ℝ) / Real.log (Real.log (m : ℝ))) *
            Real.log (ell : ℝ) :=
        mul_le_mul_of_nonneg_right homega.le hlogell_nonneg
      _ ≤ (4 * Real.log (m : ℝ) / Real.log (Real.log (m : ℝ))) *
            (Real.log (Real.log (m : ℝ)) / 48) := by
        gcongr
      _ = (1 / 12 : ℝ) * Real.log (m : ℝ) := by
        field_simp
        ring
  rw [← Real.rpow_natCast]
  rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos hmpos]
  exact Real.exp_le_exp.mpr (by simpa [mul_comm] using hprod)

/-! ## The three cycle ranges -/

/-- Contribution of permutations with at most the lower cutoff many cycles. -/
def lowCyclePart (n m : ℕ) : ℝ :=
  ∑ ell ∈ Finset.range (n + 1),
    if ell ≤ lowCycleCutoff n then orderExactCycleProbability n m ell else 0

/-- Contribution of permutations between the two cycle cutoffs. -/
def middleCyclePart (n m : ℕ) : ℝ :=
  ∑ ell ∈ Finset.range (n + 1),
    if lowCycleCutoff n < ell ∧ ell ≤ highCycleCutoff n then
      orderExactCycleProbability n m ell else 0

/-- Contribution of permutations above the upper cycle cutoff. -/
def highCyclePart (n m : ℕ) : ℝ :=
  ∑ ell ∈ Finset.range (n + 1),
    if highCycleCutoff n < ell then orderExactCycleProbability n m ell else 0

theorem orderProbability_eq_three_cycle_parts {n m : ℕ}
    (hcut : lowCycleCutoff n ≤ highCycleCutoff n) :
    orderProbability n m =
      lowCyclePart n m + middleCyclePart n m + highCyclePart n m := by
  classical
  rw [← sum_orderExactCycleProbability]
  simp only [lowCyclePart, middleCyclePart, highCyclePart,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ell _
  by_cases hlo : ell ≤ lowCycleCutoff n
  · have hmid : ¬ (lowCycleCutoff n < ell ∧ ell ≤ highCycleCutoff n) := by
      omega
    have hhi : ¬ highCycleCutoff n < ell := by omega
    simp [hlo, hmid, hhi]
  · have hlo' : lowCycleCutoff n < ell := by omega
    by_cases hhi : ell ≤ highCycleCutoff n
    · simp [hlo, hlo', hhi]
    · have hhi' : highCycleCutoff n < ell := by omega
      simp [hlo, hhi, hhi']

theorem lowCyclePart_nonneg (n m : ℕ) : 0 ≤ lowCyclePart n m := by
  classical
  apply Finset.sum_nonneg
  intro ell _
  split_ifs
  · exact orderExactCycleProbability_nonneg n m ell
  · exact le_rfl

theorem middleCyclePart_nonneg (n m : ℕ) : 0 ≤ middleCyclePart n m := by
  classical
  apply Finset.sum_nonneg
  intro ell _
  split_ifs
  · exact orderExactCycleProbability_nonneg n m ell
  · exact le_rfl

theorem highCyclePart_nonneg (n m : ℕ) : 0 ≤ highCyclePart n m := by
  classical
  apply Finset.sum_nonneg
  intro ell _
  split_ifs
  · exact orderExactCycleProbability_nonneg n m ell
  · exact le_rfl

private theorem highCycleCountSum_le_tail (n m t : ℕ) :
    ∑ ell ∈ Finset.range (n + 1),
        (if t < ell then orderExactCycleCount n m ell else 0) ≤
      cycleCountTail n t := by
  have hpoint : ∀ ell : ℕ,
      orderExactCycleCount n m ell ≤ exactCycleCount n ell := by
    intro ell
    classical
    rw [orderExactCycleCount, exactCycleCount]
    exact Finset.card_le_card (by
      intro σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact And.right)
  calc
    ∑ ell ∈ Finset.range (n + 1),
        (if t < ell then orderExactCycleCount n m ell else 0) ≤
        ∑ ell ∈ Finset.range (n + 1),
          (if t < ell then exactCycleCount n ell else 0) := by
            apply Finset.sum_le_sum
            intro ell _
            split_ifs
            · exact hpoint ell
            · exact le_rfl
    _ = cycleCountTail n t := by
      rw [cycleCountTail_eq_stirlingCycleTail, stirlingCycleTail]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro ell _
      by_cases h : t < ell <;> simp [h, exactCycleCount_eq_stirlingFirst]

theorem highCyclePart_le (n m : ℕ) :
    highCyclePart n m ≤
      (n + 1 : ℝ) / (2 : ℝ) ^ highCycleCutoff n := by
  classical
  have hsum := highCycleCountSum_le_tail n m (highCycleCutoff n)
  have hfac : (0 : ℝ) < n.factorial := by positivity
  have hpow : (0 : ℝ) < (2 : ℝ) ^ highCycleCutoff n := by positivity
  have htail : (cycleCountTail n (highCycleCutoff n) : ℝ) /
        (n.factorial : ℝ) ≤
      (n + 1 : ℝ) / (2 : ℝ) ^ highCycleCutoff n := by
    rw [div_le_div_iff₀ hfac hpow]
    have h := two_pow_mul_cycleCountTail_le n (highCycleCutoff n)
    rw [Nat.factorial_succ] at h
    simpa [mul_comm] using (by exact_mod_cast h :
      ((2 ^ highCycleCutoff n * cycleCountTail n (highCycleCutoff n) : ℕ) : ℝ) ≤
        (((n + 1) * n.factorial : ℕ) : ℝ))
  calc
    highCyclePart n m = ∑ ell ∈ Finset.range (n + 1),
        (((if highCycleCutoff n < ell then orderExactCycleCount n m ell else 0 : ℕ) : ℝ) /
          (n.factorial : ℝ)) := by
            apply Finset.sum_congr rfl
            intro ell _
            by_cases h : highCycleCutoff n < ell <;>
              simp [highCyclePart, orderExactCycleProbability, h]
    _ =
        ((∑ ell ∈ Finset.range (n + 1),
          if highCycleCutoff n < ell then orderExactCycleCount n m ell else 0 : ℕ) : ℝ) /
          (n.factorial : ℝ) := by
            rw [← Finset.sum_div]
            congr 1
            push_cast
            rfl
    _ ≤ (cycleCountTail n (highCycleCutoff n) : ℝ) /
          (n.factorial : ℝ) := by
            exact div_le_div_of_nonneg_right (by exact_mod_cast hsum) hfac.le
    _ ≤ _ := htail

private theorem eventually_highCyclePart_lt_quarter_inv :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
      highCyclePart n m < 1 / (4 * (n : ℝ)) := by
  filter_upwards [eventually_cycleCutoff_bounds, eventually_ge_atTop (5 : ℕ)] with
      n hcut hn5
  intro m
  have hnpos : (0 : ℝ) < n := by positivity
  have hB := hcut.2.2.2.2.2.2.1
  have hlognpos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hexponent : (8 : ℝ) * Real.log (n : ℝ) ≤
      (highCycleCutoff n : ℝ) * Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hnPow : (n : ℝ) ^ 8 =
      Real.exp ((8 : ℝ) * Real.log (n : ℝ)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hnpos]
    congr 1
    ring
  have htwoPow : (2 : ℝ) ^ highCycleCutoff n =
      Real.exp ((highCycleCutoff n : ℝ) * Real.log 2) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hpowLower : (n : ℝ) ^ 8 ≤ (2 : ℝ) ^ highCycleCutoff n := by
    rw [hnPow, htwoPow]
    exact Real.exp_le_exp.mpr hexponent
  have hpoly : 4 * (n : ℝ) * ((n : ℝ) + 1) < (n : ℝ) ^ 8 := by
    have hn5R : (5 : ℝ) ≤ n := by exact_mod_cast hn5
    have hsmall : 4 * ((n : ℝ) + 1) < (n : ℝ) ^ 2 := by
      nlinarith
    have hmul := mul_lt_mul_of_pos_left hsmall hnpos
    have hnat : n ^ 3 ≤ n ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
    have hcast : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 8 := by exact_mod_cast hnat
    nlinarith
  calc
    highCyclePart n m ≤
        (n + 1 : ℝ) / (2 : ℝ) ^ highCycleCutoff n := highCyclePart_le n m
    _ ≤ (n + 1 : ℝ) / (n : ℝ) ^ 8 := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hpowLower
    _ < 1 / (4 * (n : ℝ)) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith

private theorem power_div_factorial_le_two_pow_neg {x : ℝ} {q : ℕ}
    (hx : 0 ≤ x) (hq : 0 < q) (hsmall : 2 * Real.exp 1 * x ≤ q) :
    x ^ q / (q.factorial : ℝ) ≤ 1 / (2 : ℝ) ^ q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hbasepos : (0 : ℝ) < (q : ℝ) / Real.exp 1 := by positivity
  have hbase : 0 ≤ (q : ℝ) / Real.exp 1 := hbasepos.le
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * (q : ℝ)) := by
    rw [Real.le_sqrt (by norm_num)]
    · have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
      nlinarith [Real.pi_gt_three]
    · positivity
  have hpow_nonneg : 0 ≤ ((q : ℝ) / Real.exp 1) ^ q := by positivity
  have hfactorial : ((q : ℝ) / Real.exp 1) ^ q ≤ (q.factorial : ℝ) :=
    (le_mul_of_one_le_left hpow_nonneg hsqrt).trans
      (Stirling.le_factorial_stirling q)
  have hratio : x / ((q : ℝ) / Real.exp 1) ≤ (1 / 2 : ℝ) := by
    rw [div_le_iff₀ hbasepos]
    have hexppos : 0 < Real.exp 1 := Real.exp_pos _
    rw [div_eq_mul_inv]
    field_simp
    nlinarith
  calc
    x ^ q / (q.factorial : ℝ) ≤
        x ^ q / (((q : ℝ) / Real.exp 1) ^ q) := by
          exact div_le_div_of_nonneg_left (by positivity) (by positivity) hfactorial
    _ = (x / ((q : ℝ) / Real.exp 1)) ^ q := by
      exact (div_pow x ((q : ℝ) / Real.exp 1) q).symm
    _ ≤ (1 / 2 : ℝ) ^ q := pow_le_pow_left₀ (by positivity) hratio q
    _ = 1 / (2 : ℝ) ^ q := by simp [div_pow]

private theorem loglog_le_four_mul_loglog_of_le_cutoff_pow
    {n m : ℕ}
    (hnm : n ≤ m)
    (hL : 10 < Real.log (Real.log (n : ℝ)))
    (hhigh : (highCycleCutoff n : ℝ) ≤ 17 * Real.log (n : ℝ))
    (hm : m ≤ n ^ highCycleCutoff n) :
    Real.log (Real.log (m : ℝ)) ≤
      4 * Real.log (Real.log (n : ℝ)) := by
  have hnposNat : 0 < n := by
    by_contra hn
    have : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    norm_num at hL
  have hn2 : 2 ≤ n := by
    by_contra hn
    have : n = 1 := by omega
    subst n
    norm_num at hL
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hnposNat
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le hnpos (by exact_mod_cast hnm)
  have hlognpos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlogmono : Real.log (n : ℝ) ≤ Real.log (m : ℝ) :=
    Real.log_le_log hnpos (by exact_mod_cast hnm)
  have hlogmpos : 0 < Real.log (m : ℝ) := hlognpos.trans_le hlogmono
  have hmcast : (m : ℝ) ≤ ((n ^ highCycleCutoff n : ℕ) : ℝ) := by
    exact_mod_cast hm
  have hlogpow := Real.log_le_log hmpos hmcast
  rw [Nat.cast_pow, Real.log_pow] at hlogpow
  have hlogm_upper : Real.log (m : ℝ) ≤
      17 * (Real.log (n : ℝ)) ^ 2 := by
    calc
      Real.log (m : ℝ) ≤
          (highCycleCutoff n : ℝ) * Real.log (n : ℝ) := hlogpow
      _ ≤ (17 * Real.log (n : ℝ)) * Real.log (n : ℝ) := by gcongr
      _ = 17 * (Real.log (n : ℝ)) ^ 2 := by ring
  calc
    Real.log (Real.log (m : ℝ)) ≤
        Real.log (17 * (Real.log (n : ℝ)) ^ 2) :=
      Real.log_le_log hlogmpos hlogm_upper
    _ = Real.log 17 + 2 * Real.log (Real.log (n : ℝ)) := by
      rw [Real.log_mul (by norm_num : (17 : ℝ) ≠ 0)
        (pow_ne_zero 2 hlognpos.ne'), Real.log_pow]
      ring
    _ ≤ 4 * Real.log (Real.log (n : ℝ)) := by
      have h17 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 17)
      norm_num at h17
      nlinarith

private theorem middleCyclePart_le_geometric
    {n m : ℕ} {K L : ℝ}
    (hn : 0 < n) (hm : 0 < m)
    (hLpos : 0 < L)
    (hlow : L ^ 2 ≤ (lowCycleCutoff n : ℝ))
    (hsigma : (divisorSum m : ℝ) / (m : ℝ) ≤ 4 * K * L)
    (hK : 0 < K)
    (hsmall : 8 * Real.exp 1 * K * L ≤ L ^ 2) :
    middleCyclePart n m ≤
      (highCycleCutoff n + 1 : ℝ) /
        ((n : ℝ) * (2 : ℝ) ^ lowCycleCutoff n) := by
  classical
  let S := (Finset.range (n + 1)).filter fun ell ↦
    lowCycleCutoff n < ell ∧ ell ≤ highCycleCutoff n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmne : m ≠ 0 := Nat.ne_of_gt hm
  have hS_card : (S.card : ℝ) ≤ highCycleCutoff n + 1 := by
    have hsub : S ⊆ Finset.range (highCycleCutoff n + 1) := by
      intro ell hell
      simp only [S, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff] at hell ⊢
      exact hell.2.2
    have hc : S.card ≤ highCycleCutoff n + 1 := by
      simpa using Finset.card_le_card hsub
    exact_mod_cast hc
  have hxnonneg : 0 ≤ 4 * K * L := by positivity
  have hpoint : ∀ ell ∈ S,
      orderExactCycleProbability n m ell ≤
        1 / ((n : ℝ) * (2 : ℝ) ^ lowCycleCutoff n) := by
    intro ell hell
    have hellbounds := (Finset.mem_filter.mp hell).2
    have hlowpos : (0 : ℝ) < lowCycleCutoff n :=
      lt_of_lt_of_le (sq_pos_of_pos hLpos) hlow
    have hlowposNat : 0 < lowCycleCutoff n := by exact_mod_cast hlowpos
    have hellpos : 0 < ell := by
      omega
    let q := ell - 1
    have hq : q = ell - 1 := rfl
    have hqpos : 0 < q := by dsimp [q]; omega
    have hAqNat : lowCycleCutoff n ≤ q := by dsimp [q]; omega
    have hAq : (lowCycleCutoff n : ℝ) ≤ q := by exact_mod_cast hAqNat
    have hsmallq : 2 * Real.exp 1 * (4 * K * L) ≤ (q : ℝ) := by
      calc
        2 * Real.exp 1 * (4 * K * L) = 8 * Real.exp 1 * K * L := by ring
        _ ≤ L ^ 2 := hsmall
        _ ≤ (lowCycleCutoff n : ℝ) := hlow
        _ ≤ (q : ℝ) := hAq
    have hgeom := power_div_factorial_le_two_pow_neg hxnonneg hqpos hsmallq
    have hsigma_nonneg : 0 ≤ (divisorSum m : ℝ) / (m : ℝ) := by positivity
    have hpowSigma :
        ((divisorSum m : ℝ) / (m : ℝ)) ^ q ≤ (4 * K * L) ^ q :=
      pow_le_pow_left₀ hsigma_nonneg hsigma q
    have hdivides := cycleOrderDividesCount_normalized_le_sigma hn hmne hellpos
    have horder : orderExactCycleProbability n m ell ≤
        ((divisorSum m : ℝ) / (m : ℝ)) ^ q /
          ((n : ℝ) * (q.factorial : ℝ)) := by
      calc
        orderExactCycleProbability n m ell =
            (cycleOrderCount n m ell : ℝ) / (n.factorial : ℝ) := rfl
        _ ≤ (cycleOrderDividesCount n m ell : ℝ) /
              (n.factorial : ℝ) := by
            exact div_le_div_of_nonneg_right
              (by exact_mod_cast cycleOrderCount_le_cycleOrderDividesCount n m ell)
              (by positivity)
        _ ≤ ((divisorSum m : ℝ) / (m : ℝ)) ^ (ell - 1) /
              ((n : ℝ) * ((ell - 1).factorial : ℝ)) := hdivides
        _ = ((divisorSum m : ℝ) / (m : ℝ)) ^ q /
              ((n : ℝ) * (q.factorial : ℝ)) := rfl
    calc
      orderExactCycleProbability n m ell ≤
          ((divisorSum m : ℝ) / (m : ℝ)) ^ q /
            ((n : ℝ) * (q.factorial : ℝ)) := horder
      _ ≤ (4 * K * L) ^ q / ((n : ℝ) * (q.factorial : ℝ)) := by
        exact div_le_div_of_nonneg_right hpowSigma (by positivity)
      _ = ((4 * K * L) ^ q / (q.factorial : ℝ)) / (n : ℝ) := by
        field_simp
      _ ≤ (1 / (2 : ℝ) ^ q) / (n : ℝ) := by
        exact div_le_div_of_nonneg_right hgeom hnR.le
      _ ≤ (1 / (2 : ℝ) ^ lowCycleCutoff n) / (n : ℝ) := by
        have hp : (2 : ℝ) ^ lowCycleCutoff n ≤ (2 : ℝ) ^ q := by
          exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hAqNat
        gcongr
      _ = 1 / ((n : ℝ) * (2 : ℝ) ^ lowCycleCutoff n) := by
        field_simp
  calc
    middleCyclePart n m = ∑ ell ∈ S, orderExactCycleProbability n m ell := by
      rw [Finset.sum_filter]
      rfl
    _ ≤ ∑ _ell ∈ S,
        (1 / ((n : ℝ) * (2 : ℝ) ^ lowCycleCutoff n)) := by
      exact Finset.sum_le_sum hpoint
    _ = (S.card : ℝ) *
        (1 / ((n : ℝ) * (2 : ℝ) ^ lowCycleCutoff n)) := by simp
    _ ≤ (highCycleCutoff n + 1 : ℝ) *
        (1 / ((n : ℝ) * (2 : ℝ) ^ lowCycleCutoff n)) := by
      gcongr
    _ = (highCycleCutoff n + 1 : ℝ) /
        ((n : ℝ) * (2 : ℝ) ^ lowCycleCutoff n) := by simp [div_eq_mul_inv]

private theorem cutoff_geometric_decay
    {n : ℕ}
    (hL : 20 < Real.log (Real.log (n : ℝ)))
    (hlow : (Real.log (Real.log (n : ℝ))) ^ 2 ≤
      (lowCycleCutoff n : ℝ))
    (hhigh : (highCycleCutoff n : ℝ) ≤ 17 * Real.log (n : ℝ)) :
    4 * (highCycleCutoff n + 1 : ℝ) <
      (2 : ℝ) ^ lowCycleCutoff n := by
  let L := Real.log (Real.log (n : ℝ))
  have hnposNat : 0 < n := by
    by_contra hn
    have : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    norm_num at hL
  have hn2 : 2 ≤ n := by
    by_contra hn
    have : n = 1 := by omega
    subst n
    norm_num at hL
  have hlognpos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hexpL : Real.exp L = Real.log (n : ℝ) := by
    dsimp [L]
    rw [Real.exp_log hlognpos]
  have hBplus : (highCycleCutoff n + 1 : ℝ) ≤ 18 * Real.exp L := by
    have hexpLone : 1 ≤ Real.exp L := (Real.one_le_exp_iff.mpr hLpos.le)
    push_cast
    rw [hexpL]
    nlinarith
  have hexp5 : (72 : ℝ) < Real.exp 5 := by
    have hb : (2.7 : ℝ) < Real.exp 1 :=
      lt_trans (by norm_num) Real.exp_one_gt_d9
    have hp := pow_lt_pow_left₀ hb (by norm_num : (0 : ℝ) ≤ 2.7)
      (by norm_num : (5 : ℕ) ≠ 0)
    rw [← Real.exp_nat_mul] at hp
    norm_num at hp ⊢
    linarith
  have hgap : L + 5 < L ^ 2 / 2 := by
    dsimp [L] at hL ⊢
    nlinarith [sq_nonneg (Real.log (Real.log (n : ℝ)) - 20)]
  have h72 : 72 * Real.exp L < Real.exp (L ^ 2 / 2) := by
    calc
      72 * Real.exp L < Real.exp 5 * Real.exp L := by
        exact mul_lt_mul_of_pos_right hexp5 (Real.exp_pos _)
      _ = Real.exp (L + 5) := by rw [← Real.exp_add]; ring_nf
      _ < Real.exp (L ^ 2 / 2) := Real.exp_lt_exp.mpr hgap
  have htwo : Real.exp (L ^ 2 / 2) ≤
      (2 : ℝ) ^ lowCycleCutoff n := by
    have hexponent : L ^ 2 / 2 ≤
        (lowCycleCutoff n : ℝ) * Real.log 2 := by
      have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
        nlinarith [Real.log_two_gt_d9]
      have hsq : 0 ≤ L ^ 2 := sq_nonneg L
      calc
        L ^ 2 / 2 ≤ L ^ 2 * Real.log 2 := by nlinarith
        _ ≤ (lowCycleCutoff n : ℝ) * Real.log 2 := by
          gcongr
    have htwoPow : (2 : ℝ) ^ lowCycleCutoff n =
        Real.exp ((lowCycleCutoff n : ℝ) * Real.log 2) := by
      rw [← Real.rpow_natCast,
        Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    rw [htwoPow]
    exact Real.exp_le_exp.mpr hexponent
  calc
    4 * (highCycleCutoff n + 1 : ℝ) ≤ 72 * Real.exp L := by nlinarith
    _ < Real.exp (L ^ 2 / 2) := h72
    _ ≤ (2 : ℝ) ^ lowCycleCutoff n := htwo

private theorem eventually_middleCyclePart_lt_quarter_inv :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, n ≤ m →
      middleCyclePart n m < 1 / (4 * (n : ℝ)) := by
  obtain ⟨K, hK, hsigmaEvent⟩ :=
    eventually_divisorSum_ratio_le_const_mul_loglog
  rw [eventually_atTop] at hsigmaEvent
  obtain ⟨M, hM⟩ := hsigmaEvent
  have hLL : Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
    tendsto_log_log_coe_at_top
  filter_upwards [eventually_cycleCutoff_bounds,
      hLL (eventually_gt_atTop (20 : ℝ)),
      hLL (eventually_ge_atTop (8 * Real.exp 1 * K)),
      eventually_ge_atTop M] with n hcut hL20 hLlarge hnM
  intro m hnm
  let L := Real.log (Real.log (n : ℝ))
  change 20 < L at hL20
  change 8 * Real.exp 1 * K ≤ L at hLlarge
  have hnpos : 0 < n := by
    by_contra hn
    have : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    dsimp [L] at hL20
    norm_num at hL20
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hrightpos : 0 < 1 / (4 * (n : ℝ)) := by positivity
  by_cases hmupper : m ≤ n ^ highCycleCutoff n
  · have hmpos : 0 < m := lt_of_lt_of_le hnpos hnm
    have hsigma0 := hM m (hnM.trans hnm)
    have hloglog := loglog_le_four_mul_loglog_of_le_cutoff_pow hnm
      hcut.1 hcut.2.2.2.2.2.2.2 hmupper
    have hsigma : (divisorSum m : ℝ) / (m : ℝ) ≤ 4 * K * L := by
      calc
        (divisorSum m : ℝ) / (m : ℝ) ≤
            K * Real.log (Real.log (m : ℝ)) := hsigma0
        _ ≤ K * (4 * L) := by
          exact mul_le_mul_of_nonneg_left hloglog hK.le
        _ = 4 * K * L := by ring
    have hLpos : 0 < L := by dsimp [L]; linarith
    have hsmall : 8 * Real.exp 1 * K * L ≤ L ^ 2 := by
      change 8 * Real.exp 1 * K ≤ L at hLlarge
      have := mul_le_mul_of_nonneg_right hLlarge hLpos.le
      nlinarith
    have hmiddle := middleCyclePart_le_geometric hnpos hmpos hLpos
      hcut.2.1 hsigma hK hsmall
    have hdecay := cutoff_geometric_decay hL20 hcut.2.1
      hcut.2.2.2.2.2.2.2
    calc
      middleCyclePart n m ≤
          (highCycleCutoff n + 1 : ℝ) /
            ((n : ℝ) * (2 : ℝ) ^ lowCycleCutoff n) := hmiddle
      _ < 1 / (4 * (n : ℝ)) := by
        rw [div_lt_div_iff₀ (by positivity) (by positivity)]
        nlinarith
  · have hmpow : n ^ highCycleCutoff n < m := Nat.lt_of_not_ge hmupper
    have hzero : middleCyclePart n m = 0 := by
      classical
      apply Finset.sum_eq_zero
      intro ell hell
      by_cases hellmid : lowCycleCutoff n < ell ∧ ell ≤ highCycleCutoff n
      · have hpown : n ^ ell ≤ n ^ highCycleCutoff n :=
          Nat.pow_le_pow_right hnpos hellmid.2
        have hz := orderExactCycleCount_eq_zero_of_pow_lt (hpown.trans_lt hmpow)
        simp [middleCyclePart, hellmid, orderExactCycleProbability, hz]
      · simp [middleCyclePart, hellmid]
    rw [hzero]
    exact hrightpos

private theorem lowCyclePart_le
    {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hnm : n ≤ m)
    (hL : 10 < Real.log (Real.log (n : ℝ)))
    (hcutlog : Real.log (lowCycleCutoff n : ℝ) ≤
      Real.log (Real.log (n : ℝ)) / 48)
    (homega : (distinctPrimeFactorCount m : ℝ) <
      4 * Real.log (m : ℝ) / Real.log (Real.log (m : ℝ))) :
    lowCyclePart n m ≤
      (lowCycleCutoff n + 1 : ℝ) *
        ((m : ℝ) ^ (1 / 12 : ℝ) / (m : ℝ)) := by
  classical
  let S := (Finset.range (n + 1)).filter fun ell ↦ ell ≤ lowCycleCutoff n
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hS_card : (S.card : ℝ) ≤ lowCycleCutoff n + 1 := by
    have hsub : S ⊆ Finset.range (lowCycleCutoff n + 1) := by
      intro ell hell
      simp only [S, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff] at hell ⊢
      exact hell.2
    have hc : S.card ≤ lowCycleCutoff n + 1 := by
      simpa using Finset.card_le_card hsub
    exact_mod_cast hc
  have hpoint : ∀ ell ∈ S, orderExactCycleProbability n m ell ≤
      (m : ℝ) ^ (1 / 12 : ℝ) / (m : ℝ) := by
    intro ell hell
    have hellcut : ell ≤ lowCycleCutoff n := (Finset.mem_filter.mp hell).2
    by_cases hellzero : ell = 0
    · subst ell
      rw [orderExactCycleProbability,
        orderExactCycleCount_zero_cycles_of_pos hn]
      simp only [Nat.cast_zero, zero_div]
      exact div_nonneg (Real.rpow_nonneg (by positivity) _) hmR.le
    · have hellpos : 0 < ell := Nat.pos_of_ne_zero hellzero
      have hq := cycleOrderProbability_le (n := n) (m := m) (ell := ell) hm
      have hreal : (cycleOrderCount n m ell : ℝ) / (n.factorial : ℝ) ≤
          (ell : ℝ) ^ distinctPrimeFactorCount m / (m : ℝ) := by
        have hcast := (Rat.cast_le (K := ℝ)).mpr hq
        norm_num only [Rat.cast_natCast, Rat.cast_div, Rat.cast_pow] at hcast
        exact hcast
      have hpower := fewCyclePower_le_twelfth_rpow hnm hL hcutlog
        hellpos hellcut homega
      calc
        orderExactCycleProbability n m ell =
            (cycleOrderCount n m ell : ℝ) / (n.factorial : ℝ) := rfl
        _ ≤ (ell : ℝ) ^ distinctPrimeFactorCount m / (m : ℝ) := hreal
        _ ≤ (m : ℝ) ^ (1 / 12 : ℝ) / (m : ℝ) :=
          div_le_div_of_nonneg_right hpower hmR.le
  have htermnonneg : 0 ≤ (m : ℝ) ^ (1 / 12 : ℝ) / (m : ℝ) := by
    positivity
  calc
    lowCyclePart n m = ∑ ell ∈ S, orderExactCycleProbability n m ell := by
      rw [Finset.sum_filter]
      rfl
    _ ≤ ∑ _ell ∈ S,
        ((m : ℝ) ^ (1 / 12 : ℝ) / (m : ℝ)) :=
      Finset.sum_le_sum hpoint
    _ = (S.card : ℝ) *
        ((m : ℝ) ^ (1 / 12 : ℝ) / (m : ℝ)) := by simp
    _ ≤ (lowCycleCutoff n + 1 : ℝ) *
        ((m : ℝ) ^ (1 / 12 : ℝ) / (m : ℝ)) := by
      exact mul_le_mul_of_nonneg_right hS_card htermnonneg

private theorem low_rpow_product_lt_quarter_inv
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hlarge : 6 * Real.log 4 < Real.log (n : ℝ))
    (horder : n ^ 4 ≤ m ^ 3) :
    (n : ℝ) ^ (1 / 18 : ℝ) *
        ((m : ℝ) ^ (1 / 12 : ℝ) / (m : ℝ)) <
      1 / (4 * (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hpowR : (n : ℝ) ^ 4 ≤ (m : ℝ) ^ 3 := by exact_mod_cast horder
  have hlogpow := Real.log_le_log (by positivity : (0 : ℝ) < (n : ℝ) ^ 4) hpowR
  rw [Real.log_pow, Real.log_pow] at hlogpow
  have hexponent : Real.log 4 + (19 / 18 : ℝ) * Real.log (n : ℝ) +
      (1 / 12 : ℝ) * Real.log (m : ℝ) < Real.log (m : ℝ) := by
    have hfour : Real.log 4 < (1 / 6 : ℝ) * Real.log (n : ℝ) := by
      nlinarith
    have hmLower : (4 / 3 : ℝ) * Real.log (n : ℝ) ≤
        Real.log (m : ℝ) := by
      norm_num only [Nat.cast_ofNat] at hlogpow
      nlinarith
    have hscaled := mul_le_mul_of_nonneg_left hmLower
      (by norm_num : (0 : ℝ) ≤ 11 / 12)
    norm_num [div_eq_mul_inv] at hscaled hfour ⊢
    linarith
  have h4exp : (4 : ℝ) = Real.exp (Real.log 4) := by
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  have hnexp : (n : ℝ) = Real.exp (Real.log (n : ℝ)) := by
    rw [Real.exp_log hnR]
  have hmexp : (m : ℝ) = Real.exp (Real.log (m : ℝ)) := by
    rw [Real.exp_log hmR]
  have hnRpow : (n : ℝ) ^ (1 / 18 : ℝ) =
      Real.exp (Real.log (n : ℝ) * (1 / 18 : ℝ)) := by
    rw [Real.rpow_def_of_pos hnR]
  have hmRpow : (m : ℝ) ^ (1 / 12 : ℝ) =
      Real.exp (Real.log (m : ℝ) * (1 / 12 : ℝ)) := by
    rw [Real.rpow_def_of_pos hmR]
  have hproduct : 4 * (n : ℝ) * (n : ℝ) ^ (1 / 18 : ℝ) *
      (m : ℝ) ^ (1 / 12 : ℝ) < (m : ℝ) := by
    rw [h4exp, hnRpow, hmRpow, hnexp, hmexp]
    simp only [Real.log_exp]
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_lt_exp.mpr
    convert hexponent using 1 <;> ring
  calc
    (n : ℝ) ^ (1 / 18 : ℝ) *
          ((m : ℝ) ^ (1 / 12 : ℝ) / (m : ℝ)) =
        ((n : ℝ) ^ (1 / 18 : ℝ) * (m : ℝ) ^ (1 / 12 : ℝ)) /
          (m : ℝ) := by ring
    _ < 1 / (4 * (n : ℝ)) := by
      rw [div_lt_div_iff₀ hmR (by positivity)]
      nlinarith

private theorem eventually_lowCyclePart_lt_quarter_inv :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, n ^ 4 ≤ m ^ 3 →
      lowCyclePart n m < 1 / (4 * (n : ℝ)) := by
  have homegaEvent :=
    eventually_distinctPrimeFactorCount_lt_four_log_div_loglog_self
  rw [eventually_atTop] at homegaEvent
  obtain ⟨M, hM⟩ := homegaEvent
  have hLL : Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
    tendsto_log_log_coe_at_top
  filter_upwards [eventually_cycleCutoff_bounds,
      hLL (eventually_gt_atTop (20 : ℝ)), eventually_ge_atTop M] with
      n hcut hL20 hnM
  intro m horder
  have hnpos : 0 < n := by
    by_contra hn
    have : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    norm_num at hL20
  have hnm : n ≤ m := le_of_fourth_le_cube hnpos horder
  have hmpos : 0 < m := lt_of_lt_of_le hnpos hnm
  have homega := hM m (hnM.trans hnm)
  have hlow := lowCyclePart_le hnpos hmpos hnm hcut.1 hcut.2.2.2.1 homega
  have hcutplus : (lowCycleCutoff n : ℝ) + 1 ≤
      (n : ℝ) ^ (1 / 18 : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hcut.2.2.2.2.1
  have hL20' : 20 < Real.log (Real.log (n : ℝ)) := by exact hL20
  have hlognpos : 0 < Real.log (n : ℝ) := by
    have hn2 : 2 ≤ n := by
      by_contra hn2
      have : n = 1 := by omega
      subst n
      norm_num at hL20'
    exact Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hloglarge : 6 * Real.log 4 < Real.log (n : ℝ) := by
    have hexpLL : Real.exp (Real.log (Real.log (n : ℝ))) =
        Real.log (n : ℝ) := Real.exp_log hlognpos
    have hexplower := Real.add_one_le_exp (Real.log (Real.log (n : ℝ)))
    have hlog4 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    rw [hexpLL] at hexplower
    norm_num at hlog4
    nlinarith
  calc
    lowCyclePart n m ≤
        (lowCycleCutoff n + 1 : ℝ) *
          ((m : ℝ) ^ (1 / 12 : ℝ) / (m : ℝ)) := hlow
    _ ≤ (n : ℝ) ^ (1 / 18 : ℝ) *
          ((m : ℝ) ^ (1 / 12 : ℝ) / (m : ℝ)) := by
      exact mul_le_mul_of_nonneg_right hcutplus (by positivity)
    _ < 1 / (4 * (n : ℝ)) :=
      low_rpow_product_lt_quarter_inv hnpos hmpos hloglarge horder

/-! ## Uniform large-order anticoncentration -/

/-- Uniformly for `m ≥ n^(4/3)` (written without rounding as `n^4 ≤ m^3`),
an order fiber has probability strictly smaller than `1/n`, once `n` is
large enough. -/
theorem eventually_orderProbability_lt_inv_of_fourth_le_cube :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, n ^ 4 ≤ m ^ 3 →
      orderProbability n m < (1 : ℝ) / (n : ℝ) := by
  filter_upwards [eventually_cycleCutoff_bounds,
      eventually_lowCyclePart_lt_quarter_inv,
      eventually_middleCyclePart_lt_quarter_inv,
      eventually_highCyclePart_lt_quarter_inv] with
      n hcut hlow hmiddle hhigh
  intro m horder
  have hnpos : 0 < n := by
    by_contra hn
    have : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    norm_num at hcut
  have hnm : n ≤ m := le_of_fourth_le_cube hnpos horder
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hlow' := hlow m horder
  have hmiddle' := hmiddle m hnm
  have hhigh' := hhigh m
  have hthree : (3 : ℝ) / (4 * (n : ℝ)) < (1 : ℝ) / (n : ℝ) := by
    rw [div_lt_div_iff₀ (by positivity) hnR]
    nlinarith
  rw [orderProbability_eq_three_cycle_parts hcut.2.2.2.2.2.1]
  have hsum : lowCyclePart n m + middleCyclePart n m + highCyclePart n m <
      3 * (1 / (4 * (n : ℝ))) := by linarith
  calc
    lowCyclePart n m + middleCyclePart n m + highCyclePart n m <
        3 * (1 / (4 * (n : ℝ))) := hsum
    _ = (3 : ℝ) / (4 * (n : ℝ)) := by ring
    _ < (1 : ℝ) / (n : ℝ) := hthree

end

end Erdos1161
