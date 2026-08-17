/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Ford.Defs

/-!
# Finite objects for Ford's dyadic lower bound

This file contains the elementary finite layer of the isolated-divisor
argument in Ford's lower bound.  The parameter is kept explicit in the core
definitions, while `dyadicSigma` specializes it to the ratio `2` used for
Erdos Problem 896.

For a divisor `d | a`, Ford calls `d` `sigma`-isolated when it is the unique
divisor of `a` in

`(d * exp (-sigma), d * exp sigma]`.

The quantity `I a sigma` counts isolated divisors.  The quantity `W a sigma`
counts ordered pairs of divisors whose logarithms are at distance at most
`sigma`.  The main elementary fact proved here is

`2 * divisorCount a <= W a sigma + I a sigma`.

This is the natural-number form of Ford's
`I(a;sigma) >= 2 * tau(a) - W(a;sigma)`.
-/

namespace Erdos896.Ford

open scoped BigOperators

/-! ## The fixed dyadic ratio -/

/-- The logarithmic width corresponding to the fixed ratio `2`. -/
noncomputable def dyadicSigma : ℝ := Real.log 2

theorem dyadicSigma_pos : 0 < dyadicSigma := by
  exact Real.log_pos one_lt_two

@[simp]
theorem exp_dyadicSigma : Real.exp dyadicSigma = 2 := by
  rw [dyadicSigma, Real.exp_log]
  norm_num

@[simp]
theorem exp_neg_dyadicSigma : Real.exp (-dyadicSigma) = (2 : ℝ)⁻¹ := by
  rw [Real.exp_neg, exp_dyadicSigma]

/-! ## Isolated divisors and close divisor pairs -/

/-- The ordinary number of positive divisors, with the convention that zero
has no divisors inherited from `Nat.divisors`. -/
def divisorCount (a : ℕ) : ℕ := a.divisors.card

/-- A divisor is `sigma`-isolated if it is the unique divisor in the
multiplicatively symmetric window
`(d * exp (-sigma), d * exp sigma]`. -/
noncomputable def IsolatedDivisor (a d : ℕ) (sigma : ℝ) : Prop :=
  d ∈ a.divisors ∧
    tauR a ((d : ℝ) * Real.exp (-sigma))
      ((d : ℝ) * Real.exp sigma) = 1

/-- The finite set of `sigma`-isolated divisors of `a`. -/
noncomputable def isolatedDivisors (a : ℕ) (sigma : ℝ) : Finset ℕ :=
  by
    classical
    exact a.divisors.filter fun d ↦ IsolatedDivisor a d sigma

/-- Ford--Tenenbaum's `I(a;sigma)`, the number of isolated divisors. -/
noncomputable def I (a : ℕ) (sigma : ℝ) : ℕ :=
  (isolatedDivisors a sigma).card

/-- Divisors of `a` whose logarithms are within `sigma` of `log d`. -/
noncomputable def nearDivisors (a d : ℕ) (sigma : ℝ) : Finset ℕ :=
  a.divisors.filter fun e ↦
    |Real.log d - Real.log e| ≤ sigma

/-- Ordered pairs of divisors whose logarithms are within `sigma`. -/
noncomputable def nearDivisorPairs (a : ℕ) (sigma : ℝ) : Finset (ℕ × ℕ) :=
  (a.divisors.product a.divisors).filter fun de ↦
    |Real.log de.1 - Real.log de.2| ≤ sigma

/-- Hall's close-divisor-pair count `W(a;sigma)`. -/
noncomputable def W (a : ℕ) (sigma : ℝ) : ℕ :=
  (nearDivisorPairs a sigma).card

@[simp]
theorem mem_isolatedDivisors {a d : ℕ} {sigma : ℝ} :
    d ∈ isolatedDivisors a sigma ↔ IsolatedDivisor a d sigma := by
  classical
  rw [isolatedDivisors, Finset.mem_filter]
  unfold IsolatedDivisor
  tauto

theorem isolatedDivisor_dvd {a d : ℕ} {sigma : ℝ}
    (hd : IsolatedDivisor a d sigma) : d ∣ a := by
  exact (Nat.mem_divisors.mp hd.1).1

theorem isolatedDivisor_ne_zero {a d : ℕ} {sigma : ℝ}
    (hd : IsolatedDivisor a d sigma) : a ≠ 0 := by
  exact (Nat.mem_divisors.mp hd.1).2

@[simp]
theorem mem_nearDivisors {a d e : ℕ} {sigma : ℝ} :
    e ∈ nearDivisors a d sigma ↔
      e ∈ a.divisors ∧ |Real.log d - Real.log e| ≤ sigma := by
  simp [nearDivisors]

@[simp]
theorem mem_nearDivisorPairs {a d e : ℕ} {sigma : ℝ} :
    (d, e) ∈ nearDivisorPairs a sigma ↔
      d ∈ a.divisors ∧ e ∈ a.divisors ∧
        |Real.log d - Real.log e| ≤ sigma := by
  simp [nearDivisorPairs, and_assoc]

@[simp]
theorem I_zero (sigma : ℝ) : I 0 sigma = 0 := by
  classical
  simp [I, isolatedDivisors]

@[simp]
theorem W_zero (sigma : ℝ) : W 0 sigma = 0 := by
  simp [W, nearDivisorPairs]

theorem I_le_divisorCount (a : ℕ) (sigma : ℝ) :
    I a sigma ≤ divisorCount a := by
  classical
  simpa [I, isolatedDivisors, divisorCount] using
    (Finset.card_le_card (Finset.filter_subset
      (fun d ↦ IsolatedDivisor a d sigma) a.divisors))

private theorem divisor_mem_own_window {a d : ℕ} {sigma : ℝ}
    (hsigma : 0 < sigma) (hd : d ∈ a.divisors) :
    d ∈ divisorWindowR a ((d : ℝ) * Real.exp (-sigma))
      ((d : ℝ) * Real.exp sigma) := by
  obtain ⟨hda, ha0⟩ := Nat.mem_divisors.mp hd
  have ha : 0 < a := Nat.pos_of_ne_zero ha0
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hda ha
  have hdposR : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hexpNeg : Real.exp (-sigma) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hexp : 1 < Real.exp sigma := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hsigma
  apply mem_divisorWindowR.mpr
  refine ⟨hda, ha0, ?_, ?_⟩
  · nlinarith [mul_lt_mul_of_pos_left hexpNeg hdposR]
  · nlinarith [mul_lt_mul_of_pos_left hexp hdposR]

private theorem near_of_mem_centered_window {a d e : ℕ} {sigma : ℝ}
    (hd : d ∈ a.divisors)
    (he : e ∈ divisorWindowR a ((d : ℝ) * Real.exp (-sigma))
      ((d : ℝ) * Real.exp sigma)) :
    |Real.log d - Real.log e| ≤ sigma := by
  obtain ⟨hda, ha0⟩ := Nat.mem_divisors.mp hd
  obtain ⟨hea, -, hLower, hUpper⟩ := mem_divisorWindowR.mp he
  have ha : 0 < a := Nat.pos_of_ne_zero ha0
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hda ha
  have hepos : 0 < e := Nat.pos_of_dvd_of_pos hea ha
  have hdposR : (0 : ℝ) < d := by exact_mod_cast hdpos
  have heposR : (0 : ℝ) < e := by exact_mod_cast hepos
  have hlogUpper : Real.log e ≤ Real.log d + sigma := by
    rw [← Real.exp_le_exp, Real.exp_log heposR, Real.exp_add,
      Real.exp_log hdposR]
    exact hUpper
  have hlogLower : Real.log d - sigma < Real.log e := by
    rw [← Real.exp_lt_exp, Real.exp_log heposR, Real.exp_sub,
      Real.exp_log hdposR]
    simpa [div_eq_mul_inv, Real.exp_neg] using hLower
  rw [abs_le]
  constructor <;> linarith

private theorem exists_other_near_divisor_of_not_isolated
    {a d : ℕ} {sigma : ℝ} (hsigma : 0 < sigma)
    (hd : d ∈ a.divisors) (hnot : ¬ IsolatedDivisor a d sigma) :
    ∃ e ∈ a.divisors, e ≠ d ∧
      |Real.log d - Real.log e| ≤ sigma := by
  let y : ℝ := (d : ℝ) * Real.exp (-sigma)
  let z : ℝ := (d : ℝ) * Real.exp sigma
  have hdWindow : d ∈ divisorWindowR a y z := by
    simpa [y, z] using divisor_mem_own_window hsigma hd
  have hpos : 0 < tauR a y z := by
    rw [tauR, Finset.card_pos]
    exact ⟨d, hdWindow⟩
  have hne : tauR a y z ≠ 1 := by
    intro hone
    apply hnot
    exact ⟨hd, by simpa [y, z] using hone⟩
  have hcard : 1 < (divisorWindowR a y z).card := by
    rw [← tauR]
    omega
  obtain ⟨e, he, hed⟩ := Finset.exists_mem_ne hcard d
  refine ⟨e, Nat.mem_divisors.mpr
    ⟨(mem_divisorWindowR.mp he).1, (mem_divisorWindowR.mp he).2.1⟩, hed, ?_⟩
  exact near_of_mem_centered_window hd (by simpa [y, z] using he)

private theorem one_le_card_nearDivisors {a d : ℕ} {sigma : ℝ}
    (hsigma : 0 ≤ sigma) (hd : d ∈ a.divisors) :
    1 ≤ (nearDivisors a d sigma).card := by
  rw [Finset.one_le_card]
  exact ⟨d, mem_nearDivisors.mpr ⟨hd, by simpa using hsigma⟩⟩

private theorem two_le_card_nearDivisors_of_not_isolated
    {a d : ℕ} {sigma : ℝ} (hsigma : 0 < sigma)
    (hd : d ∈ a.divisors) (hnot : ¬ IsolatedDivisor a d sigma) :
    2 ≤ (nearDivisors a d sigma).card := by
  obtain ⟨e, hea, hed, hnear⟩ :=
    exists_other_near_divisor_of_not_isolated hsigma hd hnot
  rw [Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨d, e, mem_nearDivisors.mpr ⟨hd, by simpa using hsigma.le⟩,
    mem_nearDivisors.mpr ⟨hea, hnear⟩, hed.symm⟩

private theorem card_nearDivisorPairs_eq_sum (a : ℕ) (sigma : ℝ) :
    (nearDivisorPairs a sigma).card =
      ∑ d ∈ a.divisors, (nearDivisors a d sigma).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (s := nearDivisorPairs a sigma) (t := a.divisors)
    (f := Prod.fst) (by
      intro de hde
      exact (mem_nearDivisorPairs.mp hde).1)]
  apply Finset.sum_congr rfl
  intro d hd
  have hfiber :
      (nearDivisorPairs a sigma).filter (fun de ↦ de.1 = d) =
        (({d} : Finset ℕ) ×ˢ nearDivisors a d sigma) := by
    ext de
    rcases de with ⟨e, f⟩
    simp only [Finset.mem_filter, mem_nearDivisorPairs,
      Finset.mem_product, Finset.mem_singleton, mem_nearDivisors]
    constructor
    · rintro ⟨⟨hea, hfa, hnear⟩, rfl⟩
      exact ⟨rfl, hfa, hnear⟩
    · rintro ⟨rfl, hfa, hnear⟩
      exact ⟨⟨hd, hfa, hnear⟩, rfl⟩
  simp [hfiber]

theorem W_eq_sum_card_nearDivisors (a : ℕ) (sigma : ℝ) :
    W a sigma = ∑ d ∈ a.divisors, (nearDivisors a d sigma).card := by
  exact card_nearDivisorPairs_eq_sum a sigma

/-- Ford's elementary close-pair inequality.  Each divisor contributes its
diagonal pair.  Every non-isolated divisor contributes at least one further
ordered close pair. -/
theorem two_mul_divisorCount_le_W_add_I {a : ℕ} {sigma : ℝ}
    (hsigma : 0 < sigma) :
    2 * divisorCount a ≤ W a sigma + I a sigma := by
  classical
  let bad := a.divisors.filter fun d ↦ ¬ IsolatedDivisor a d sigma
  have hpartition : I a sigma + bad.card = divisorCount a := by
    simpa [I, isolatedDivisors, bad, divisorCount, add_comm] using
      (Finset.card_filter_add_card_filter_not
        (s := a.divisors) (fun d ↦ IsolatedDivisor a d sigma))
  have hsplit :
      (a.divisors.filter fun d ↦ IsolatedDivisor a d sigma).card +
          2 * (a.divisors.filter fun d ↦ ¬ IsolatedDivisor a d sigma).card =
        ∑ d ∈ a.divisors,
          if IsolatedDivisor a d sigma then 1 else 2 := by
    let f : ℕ → ℕ := fun d ↦
      if IsolatedDivisor a d sigma then 1 else 2
    have hisoSum :
        ∑ d ∈ a.divisors.filter
            (fun d ↦ IsolatedDivisor a d sigma), f d =
          (a.divisors.filter fun d ↦ IsolatedDivisor a d sigma).card := by
      simpa using (Finset.sum_const_nat
        (s := a.divisors.filter fun d ↦ IsolatedDivisor a d sigma)
        (m := 1) (f := f) (by
          intro d hd
          simp [f, (Finset.mem_filter.mp hd).2]))
    have hbadSum :
        ∑ d ∈ a.divisors.filter
            (fun d ↦ ¬ IsolatedDivisor a d sigma), f d =
          (a.divisors.filter fun d ↦ ¬ IsolatedDivisor a d sigma).card * 2 := by
      apply Finset.sum_const_nat
      intro d hd
      simp [f, (Finset.mem_filter.mp hd).2]
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := a.divisors) (f := f)
      (p := fun d ↦ IsolatedDivisor a d sigma), hisoSum, hbadSum]
    simp [Nat.mul_comm]
  have hsum : I a sigma + 2 * bad.card ≤ W a sigma := by
    rw [W_eq_sum_card_nearDivisors]
    calc
      I a sigma + 2 * bad.card =
          ∑ d ∈ a.divisors,
            if IsolatedDivisor a d sigma then 1 else 2 := by
        simpa [I, isolatedDivisors, bad] using hsplit
      _ ≤ ∑ d ∈ a.divisors, (nearDivisors a d sigma).card := by
        apply Finset.sum_le_sum
        intro d hd
        split_ifs with hiso
        · exact one_le_card_nearDivisors hsigma.le hd
        · exact two_le_card_nearDivisors_of_not_isolated hsigma hd hiso
  omega

/-- The truncated-natural form of `I >= 2*tau-W`. -/
theorem two_mul_divisorCount_tsub_W_le_I {a : ℕ} {sigma : ℝ}
    (hsigma : 0 < sigma) :
    2 * divisorCount a - W a sigma ≤ I a sigma := by
  have h := two_mul_divisorCount_le_W_add_I (a := a) hsigma
  omega

/-- The same inequality over the integers, with literal subtraction. -/
theorem two_mul_divisorCount_sub_W_le_I_int {a : ℕ} {sigma : ℝ}
    (hsigma : 0 < sigma) :
    (2 : ℤ) * (divisorCount a : ℤ) - (W a sigma : ℤ) ≤ (I a sigma : ℤ) := by
  have h : (2 : ℤ) * (divisorCount a : ℤ) ≤
      (W a sigma : ℤ) + (I a sigma : ℤ) := by
    exact_mod_cast two_mul_divisorCount_le_W_add_I hsigma
  linarith

/-! ## Disjoint logarithmic intervals -/

/-- The log interval belonging to an isolated divisor is disjoint from the
log interval belonging to every different divisor. -/
theorem disjoint_logDivisorInterval_of_isolated
    {a d e : ℕ} {sigma : ℝ}
    (hd : IsolatedDivisor a d sigma) (he : e ∈ a.divisors) (hed : e ≠ d) :
    Disjoint (logDivisorInterval d sigma) (logDivisorInterval e sigma) := by
  rw [Set.disjoint_left]
  intro x hxd hxe
  have hclose : |Real.log d - Real.log e| < sigma := by
    rw [abs_lt]
    constructor <;> linarith [hxd.1, hxd.2, hxe.1, hxe.2]
  have hdWindow := hd.2
  have heWindow :
      e ∈ divisorWindowR a ((d : ℝ) * Real.exp (-sigma))
        ((d : ℝ) * Real.exp sigma) := by
    apply mem_divisorWindowR.mpr
    obtain ⟨hea, ha0⟩ := Nat.mem_divisors.mp he
    obtain ⟨hda, -⟩ := Nat.mem_divisors.mp hd.1
    have ha : 0 < a := Nat.pos_of_ne_zero ha0
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hda ha
    have hepos : 0 < e := Nat.pos_of_dvd_of_pos hea ha
    have hdposR : (0 : ℝ) < d := by exact_mod_cast hdpos
    have heposR : (0 : ℝ) < e := by exact_mod_cast hepos
    refine ⟨hea, ha0, ?_, ?_⟩
    · have hlogLower : Real.log d - sigma < Real.log e := by
        rw [abs_lt] at hclose
        linarith
      calc
        (d : ℝ) * Real.exp (-sigma) =
            Real.exp (Real.log d - sigma) := by
          rw [Real.exp_sub, Real.exp_log hdposR, Real.exp_neg]
          simp [div_eq_mul_inv]
        _ < Real.exp (Real.log e) := Real.exp_lt_exp.mpr hlogLower
        _ = e := Real.exp_log heposR
    · have hlogUpper : Real.log e < Real.log d + sigma := by
        rw [abs_lt] at hclose
        linarith
      calc
        (e : ℝ) = Real.exp (Real.log e) := (Real.exp_log heposR).symm
        _ ≤ Real.exp (Real.log d + sigma) :=
          Real.exp_le_exp.mpr hlogUpper.le
        _ = (d : ℝ) * Real.exp sigma := by
          rw [Real.exp_add, Real.exp_log hdposR]
  have htwo : 2 ≤ tauR a ((d : ℝ) * Real.exp (-sigma))
      ((d : ℝ) * Real.exp sigma) := by
    rw [tauR]
    have hone : 1 < (divisorWindowR a ((d : ℝ) * Real.exp (-sigma))
        ((d : ℝ) * Real.exp sigma)).card :=
      Finset.one_lt_card_iff.mpr ⟨d, e, ?_, heWindow, hed.symm⟩
    · omega
    · exact divisor_mem_own_window (by
      rw [abs_lt] at hclose
      linarith) hd.1
  omega

/-- The logarithmic intervals centered at isolated divisors are pairwise
disjoint. -/
theorem isolated_logDivisorIntervals_pairwiseDisjoint
    (a : ℕ) (sigma : ℝ) :
    (isolatedDivisors a sigma : Set ℕ).PairwiseDisjoint
      (fun d ↦ logDivisorInterval d sigma) := by
  intro d hd e he hde
  exact disjoint_logDivisorInterval_of_isolated
    (mem_isolatedDivisors.mp hd) (mem_isolatedDivisors.mp he).1 hde.symm

/-! ## Dyadic specializations -/

/-- At the fixed width `log 2`, the real centered window is exactly the
natural ratio-two window. -/
theorem isolatedDivisor_dyadic_iff {a d : ℕ} :
    IsolatedDivisor a d dyadicSigma ↔
      d ∣ a ∧ a ≠ 0 ∧
        ∃! e : ℕ, e ∣ a ∧ d < 2 * e ∧ e ≤ 2 * d := by
  rw [IsolatedDivisor, tauR_eq_one_iff]
  simp only [Nat.mem_divisors, exp_neg_dyadicSigma, exp_dyadicSigma]
  norm_num
  constructor
  · rintro ⟨⟨hda, ha0⟩, e, ⟨hea, -, hLower, hUpper⟩, hunique⟩
    refine ⟨hda, ha0, e, ⟨hea, ?_, ?_⟩, ?_⟩
    · have hLower' : (d : ℝ) < 2 * e := by linarith
      exact_mod_cast hLower'
    · have hUpper' : (e : ℝ) ≤ 2 * d := by simpa [mul_comm] using hUpper
      exact_mod_cast hUpper'
    · intro f hf
      apply hunique f
      refine ⟨hf.1, ha0, ?_, ?_⟩
      · have hLower' : (d : ℝ) < 2 * f := by exact_mod_cast hf.2.1
        linarith
      · have hUpper' : (f : ℝ) ≤ 2 * d := by exact_mod_cast hf.2.2
        simpa [mul_comm] using hUpper'
  · rintro ⟨hda, ha0, e, ⟨hea, hLower, hUpper⟩, hunique⟩
    refine ⟨⟨hda, ha0⟩, e, ⟨hea, ha0, ?_, ?_⟩, ?_⟩
    · have hLower' : (d : ℝ) < 2 * e := by exact_mod_cast hLower
      linarith
    · have hUpper' : (e : ℝ) ≤ 2 * d := by exact_mod_cast hUpper
      simpa [mul_comm] using hUpper'
    · intro f hf
      apply hunique f
      refine ⟨hf.1, ?_, ?_⟩
      · have hLower' : (d : ℝ) < 2 * f := by linarith [hf.2.2.1]
        exact_mod_cast hLower'
      · have hUpper' : (f : ℝ) ≤ 2 * d := by
          simpa [mul_comm] using hf.2.2.2
        exact_mod_cast hUpper'

/-- Isolated divisors for the fixed ratio `2`. -/
noncomputable abbrev dyadicIsolatedDivisors (a : ℕ) : Finset ℕ :=
  isolatedDivisors a dyadicSigma

/-- `I(a; log 2)`. -/
noncomputable abbrev dyadicI (a : ℕ) : ℕ := I a dyadicSigma

/-- `W(a; log 2)`. -/
noncomputable abbrev dyadicW (a : ℕ) : ℕ := W a dyadicSigma

theorem two_mul_divisorCount_le_dyadicW_add_dyadicI (a : ℕ) :
    2 * divisorCount a ≤ dyadicW a + dyadicI a := by
  exact two_mul_divisorCount_le_W_add_I dyadicSigma_pos

end Erdos896.Ford
