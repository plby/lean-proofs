import Mathlib
import UnitFractions.AuxiliaryLemmas
import UnitFractions.Fourier

/-!
# Prime-power infrastructure for Erdős Problem 285

Martin's denominator-elimination argument measures an integer by its largest
*exact* prime-power part: if `p ^ e ∣ n` but `p ^ (e + 1) ∤ n`, the relevant
part is `p ^ e`.  Equivalently, it is a prime power `q ∣ n` for which
`q` is coprime to `n / q`.

This file packages that notion, the counting function `π⋆`, elementary linear
bounds for `π⋆`, reduced-rational denominator descent, and the exponential LCM
bound already available in the unit-fractions development.
-/

namespace Erdos285.PrimePowers

open Filter Finset
open scoped BigOperators Topology

noncomputable section

/-- The exact prime-power parts of `n`.  For example, the parts of
`12 = 2^2 * 3` are `4` and `3`, rather than `2`, `4`, and `3`. -/
def primePowerParts (n : ℕ) : Finset ℕ :=
  n.divisors.filter fun q ↦ IsPrimePow q ∧ Nat.Coprime q (n / q)

/-- Martin's `P*(n)`, with the harmless convention `P*(0) = P*(1) = 0`. -/
def largestPrimePowerPart (n : ℕ) : ℕ :=
  (primePowerParts n).sup id

/-- A natural-number formulation of smoothness in terms of exact prime-power
parts. -/
def PrimePowerSmooth (y n : ℕ) : Prop :=
  ∀ q ∈ primePowerParts n, q ≤ y

/-- The finite set of prime powers in `[2,y]`. -/
def primePowersUpTo (y : ℕ) : Finset ℕ :=
  (Icc 2 y).filter IsPrimePow

/-- Martin's prime-power counting function `π*(y)`. -/
def piStar (y : ℕ) : ℕ :=
  (primePowersUpTo y).card

/-- `lcm(1,2,...,y)`. -/
def initialLcm (y : ℕ) : ℕ :=
  (Icc 1 y).lcm id

lemma mem_primePowerParts {n q : ℕ} (hn : n ≠ 0) :
    q ∈ primePowerParts n ↔
      IsPrimePow q ∧ q ∣ n ∧ Nat.Coprime q (n / q) := by
  simp [primePowerParts, Nat.mem_divisors, hn, and_left_comm]

lemma primePowerParts_eq_ppowers_in_singleton (n : ℕ) :
    primePowerParts n = UnitFractions.ppowers_in_set {n} := by
  ext q
  by_cases hn : n = 0
  · subst n
    have hzero : UnitFractions.ppowers_in_set ({0} : Finset ℕ) = ∅ := by
      simpa using UnitFractions.ppowers_in_set_insert_zero (∅ : Finset ℕ)
    rw [hzero]
    simp [primePowerParts]
  · constructor
    · intro hq
      rcases (mem_primePowerParts hn).mp hq with ⟨hqpp, hqdiv, hqcop⟩
      rw [UnitFractions.mem_ppowers_in_set]
      refine ⟨hqpp, ⟨n, ?_⟩⟩
      exact (UnitFractions.mem_local_part n).mpr ⟨by simp, hqdiv, hqcop⟩
    · intro hq
      rcases UnitFractions.mem_ppowers_in_set.mp hq with ⟨hqpp, ⟨m, hm⟩⟩
      rcases (UnitFractions.mem_local_part m).mp hm with ⟨hm, hqdiv, hqcop⟩
      simp only [Finset.mem_singleton] at hm
      subst m
      exact (mem_primePowerParts hn).mpr ⟨hqpp, hqdiv, hqcop⟩

lemma primePowerParts_nonempty {n : ℕ} (hn : 2 ≤ n) :
    (primePowerParts n).Nonempty := by
  rw [primePowerParts_eq_ppowers_in_singleton]
  exact UnitFractions.ppowers_in_set_nonempty ⟨n, by simp, hn⟩

lemma primePowerParts_empty_iff {n : ℕ} :
    primePowerParts n = ∅ ↔ n < 2 := by
  constructor
  · intro h
    by_contra hn
    exact (primePowerParts_nonempty (Nat.le_of_not_gt hn)).ne_empty h
  · intro hn
    interval_cases n <;> simp [primePowerParts, not_isPrimePow_one]

lemma le_largestPrimePowerPart {n q : ℕ} (hq : q ∈ primePowerParts n) :
    q ≤ largestPrimePowerPart n := by
  exact Finset.le_sup (f := id) hq

lemma largestPrimePowerPart_le_iff {n y : ℕ} :
    largestPrimePowerPart n ≤ y ↔ PrimePowerSmooth y n := by
  simp [largestPrimePowerPart, PrimePowerSmooth, Finset.sup_le_iff]

lemma largestPrimePowerPart_mem {n : ℕ} (hn : 2 ≤ n) :
    largestPrimePowerPart n ∈ primePowerParts n := by
  have hs : (primePowerParts n).sup id ∈ id '' (primePowerParts n : Set ℕ) :=
    Finset.sup_mem_of_nonempty (f := id) (primePowerParts_nonempty hn)
  rcases hs with ⟨q, hq, hqeq⟩
  simpa [largestPrimePowerPart] using hqeq ▸ hq

lemma largestPrimePowerPart_spec {n : ℕ} (hn : 2 ≤ n) :
    IsPrimePow (largestPrimePowerPart n) ∧
      largestPrimePowerPart n ∣ n ∧
      Nat.Coprime (largestPrimePowerPart n) (n / largestPrimePowerPart n) := by
  exact (mem_primePowerParts (by omega)).mp (largestPrimePowerPart_mem hn)

lemma one_lt_largestPrimePowerPart {n : ℕ} (hn : 2 ≤ n) :
    1 < largestPrimePowerPart n :=
  (largestPrimePowerPart_spec hn).1.one_lt

lemma largestPrimePowerPart_le {n : ℕ} : largestPrimePowerPart n ≤ n := by
  rw [largestPrimePowerPart_le_iff]
  intro q hq
  by_cases hn : n = 0
  · subst n
    simp [primePowerParts] at hq
  · exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn) ((mem_primePowerParts hn).mp hq).2.1

lemma primePowerSmooth_mono {x y n : ℕ} (hxy : x ≤ y)
    (h : PrimePowerSmooth x n) : PrimePowerSmooth y n := by
  intro q hq
  exact (h q hq).trans hxy

lemma primePowerSmooth_self (n : ℕ) : PrimePowerSmooth n n := by
  rw [← largestPrimePowerPart_le_iff]
  exact largestPrimePowerPart_le

@[simp] lemma mem_primePowersUpTo {y q : ℕ} :
    q ∈ primePowersUpTo y ↔ IsPrimePow q ∧ q ≤ y := by
  constructor
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hqIcc, hqpp⟩
    exact ⟨hqpp, (Finset.mem_Icc.mp hqIcc).2⟩
  · rintro ⟨hqpp, hqy⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hqpp.one_lt, hqy⟩, hqpp⟩

lemma primePowersUpTo_mono : Monotone primePowersUpTo := by
  intro x y hxy q hq
  rw [mem_primePowersUpTo] at hq ⊢
  exact ⟨hq.1, hq.2.trans hxy⟩

lemma piStar_mono : Monotone piStar := by
  intro x y hxy
  exact Finset.card_le_card (primePowersUpTo_mono hxy)

lemma piStar_le (y : ℕ) : piStar y ≤ y := by
  calc
    piStar y ≤ (Icc 2 y).card := by
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ y := by simp

/-- The elementary estimate `π*(y) = O(y)`.  Martin only needs that the exact
correction consumes a sublinear number of terms for a much smaller argument;
this coarse bound is a convenient universally valid API. -/
lemma piStar_isBigO :
    (fun y : ℕ ↦ (piStar y : ℝ)) =O[atTop] (fun y : ℕ ↦ (y : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun y ↦ ?_)
  simpa only [Real.norm_natCast, norm_one, one_mul] using
    (show (piStar y : ℝ) ≤ y by exact_mod_cast piStar_le y)

lemma den_pos (r : ℚ) : 0 < r.den := r.den_pos

/-- A proper divisor of a reduced denominator is strictly smaller. -/
lemma den_lt_of_dvd_of_ne {r s : ℚ} (hdiv : s.den ∣ r.den)
    (hne : s.den ≠ r.den) : s.den < r.den :=
  Nat.lt_of_le_of_ne (Nat.le_of_dvd r.den_pos hdiv) hne

/-- Once a prime-power part `q` of a denominator has been eliminated, any new
reduced denominator dividing `r.den / q` is strictly smaller. -/
lemma den_lt_of_primePower_elimination {r s : ℚ} {q : ℕ}
    (hq : q ∈ primePowerParts r.den) (hdiv : s.den ∣ r.den / q) :
    s.den < r.den := by
  have hr0 : r.den ≠ 0 := r.den_ne_zero
  have hqspec := (mem_primePowerParts hr0).mp hq
  have hquot : r.den / q < r.den := Nat.div_lt_self r.den_pos hqspec.1.one_lt
  exact (Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd r.den_pos hqspec.2.1)
    hqspec.1.pos) hdiv).trans_lt hquot

lemma den_eq_one_iff_primePowerParts_empty (r : ℚ) :
    r.den = 1 ↔ primePowerParts r.den = ∅ := by
  rw [primePowerParts_empty_iff]
  have := r.den_pos
  omega

lemma exists_primePowerPart_of_den_ne_one {r : ℚ} (hr : r.den ≠ 1) :
    ∃ q ∈ primePowerParts r.den, IsPrimePow q ∧ q ∣ r.den := by
  have hden : 2 ≤ r.den := by
    have := r.den_pos
    omega
  obtain ⟨q, hq⟩ := primePowerParts_nonempty hden
  exact ⟨q, hq, (mem_primePowerParts r.den_ne_zero).mp hq |>.1,
    (mem_primePowerParts r.den_ne_zero).mp hq |>.2.1⟩

/-- If no exact prime-power part remains, the reduced rational is an integer. -/
lemma isInt_of_primePowerParts_empty {r : ℚ}
    (h : primePowerParts r.den = ∅) : ∃ z : ℤ, r = z := by
  have hden : r.den = 1 := (den_eq_one_iff_primePowerParts_empty r).2 h
  exact ⟨r.num, (Rat.den_eq_one_iff r).mp hden |>.symm⟩

/-- The reduced denominator of a finite unit-fraction sum divides the LCM of
its displayed denominators. -/
lemma recSum_den_dvd_lcm (A : Finset ℕ) :
    (UnitFractions.rec_sum A).den ∣ A.lcm id := by
  refine (Rat.den_sum_dvd_lcm_den A (fun n ↦ (1 : ℚ) / n)).trans ?_
  apply Finset.lcm_dvd
  intro n hn
  have hden : ((1 : ℚ) / n).den ∣ n := by
    have hdenZ : ((Rat.divInt 1 (n : ℤ)).den : ℤ) ∣ (n : ℤ) :=
      Rat.den_dvd 1 (n : ℤ)
    have heq : Rat.divInt 1 (n : ℤ) = (1 : ℚ) / n := by
      rw [Rat.divInt_eq_div]
      norm_num
    rw [heq] at hdenZ
    exact_mod_cast hdenZ
  exact hden.trans (Finset.dvd_lcm hn)

lemma primePowerPart_of_recSum_den_dvd_lcm {A : Finset ℕ} {q : ℕ}
    (hq : q ∈ primePowerParts (UnitFractions.rec_sum A).den) :
    q ∣ A.lcm id := by
  exact ((mem_primePowerParts (UnitFractions.rec_sum A).den_ne_zero).mp hq).2.1.trans
    (recSum_den_dvd_lcm A)

lemma zero_not_mem_Icc_one (y : ℕ) : 0 ∉ Icc 1 y := by simp

lemma ppowers_in_initial_interval_le (y : ℕ) {q : ℕ}
    (hq : q ∈ UnitFractions.ppowers_in_set (Icc 1 y)) : q ≤ y := by
  rw [UnitFractions.mem_ppowers_in_set] at hq
  obtain ⟨n, hn⟩ := hq.2
  rcases (UnitFractions.mem_local_part n).mp hn with ⟨hnIcc, hqdiv, _⟩
  exact (Nat.le_of_dvd (Finset.mem_Icc.mp hnIcc).1 hqdiv).trans
    (Finset.mem_Icc.mp hnIcc).2

/-- A reusable exponential bound for `lcm(1,...,y)`. -/
lemma exists_initialLcm_le_exp :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ,
      (initialLcm y : ℝ) ≤ Real.exp (C * y) := by
  obtain ⟨C, hC, hbound⟩ := UnitFractions.smooth_lcm
  refine ⟨C, hC, fun y ↦ ?_⟩
  change (↑((Icc 1 y).lcm (id : ℕ → ℕ)) : ℝ) ≤ Real.exp (C * y)
  apply hbound y (by positivity) (Icc 1 y) (zero_not_mem_Icc_one y)
  intro q hq
  exact_mod_cast ppowers_in_initial_interval_le y hq

end

end Erdos285.PrimePowers
