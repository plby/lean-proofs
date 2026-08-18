/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Erdős Problem 1161: finite counting and the Beker candidates

This file fixes the exact finite model used in the formalization.  We count
permutations of `Fin n` by their group-theoretic order, package the finite
maximum of those fiber cardinalities, and prove the elementary equivalence
between Beker's two parametrizations of the eventual maximizing order.
-/

open scoped BigOperators

namespace Erdos1161

/-- The number of permutations of `Fin n` having order exactly `m`. -/
noncomputable def orderCount (n m : ℕ) : ℕ :=
  Fintype.card {σ : Equiv.Perm (Fin n) // orderOf σ = m}

/-- The finite set of orders which actually occur in `Equiv.Perm (Fin n)`. -/
noncomputable def possibleOrders (n : ℕ) : Finset ℕ :=
  Finset.univ.image (fun σ : Equiv.Perm (Fin n) ↦ orderOf σ)

/-- The largest order-fiber cardinality. -/
noncomputable def maxOrderCount (n : ℕ) : ℕ :=
  (possibleOrders n).sup (orderCount n)

/-- An order is a mode when its fiber is at least as large as every other
order fiber.  Quantifying over all naturals is harmless: impossible orders
have empty fibers. -/
def IsMode (n m : ℕ) : Prop :=
  ∀ j : ℕ, orderCount n j ≤ orderCount n m

/-- The probability of a given order under the uniform distribution, written
as a real normalization of the finite count. -/
noncomputable def orderProbability (n m : ℕ) : ℝ :=
  (orderCount n m : ℝ) / (n.factorial : ℝ)

/-- The normalized largest fiber cardinality. -/
noncomputable def maxOrderProbability (n : ℕ) : ℝ :=
  (maxOrderCount n : ℝ) / (n.factorial : ℝ)

theorem card_perm_fin (n : ℕ) :
    Fintype.card (Equiv.Perm (Fin n)) = n.factorial := by
  simp [Fintype.card_perm]

theorem orderCount_eq_card_filter (n m : ℕ) :
    orderCount n m =
      ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
        (fun σ ↦ orderOf σ = m)).card := by
  rw [orderCount, Fintype.card_subtype]

@[simp]
theorem mem_possibleOrders_iff {n m : ℕ} :
    m ∈ possibleOrders n ↔
      ∃ σ : Equiv.Perm (Fin n), orderOf σ = m := by
  simp [possibleOrders]

theorem possibleOrders_nonempty (n : ℕ) : (possibleOrders n).Nonempty := by
  refine ⟨orderOf (1 : Equiv.Perm (Fin n)), ?_⟩
  simp [possibleOrders]

theorem possibleOrder_pos {n m : ℕ} (hm : m ∈ possibleOrders n) : 0 < m := by
  obtain ⟨σ, rfl⟩ := mem_possibleOrders_iff.mp hm
  exact orderOf_pos σ

theorem possibleOrder_dvd_factorial {n m : ℕ} (hm : m ∈ possibleOrders n) :
    m ∣ n.factorial := by
  obtain ⟨σ, rfl⟩ := mem_possibleOrders_iff.mp hm
  simpa only [card_perm_fin] using (orderOf_dvd_card (x := σ))

theorem possibleOrder_le_factorial {n m : ℕ} (hm : m ∈ possibleOrders n) :
    m ≤ n.factorial :=
  Nat.le_of_dvd n.factorial_pos (possibleOrder_dvd_factorial hm)

@[simp]
theorem orderCount_pos_iff_mem_possibleOrders {n m : ℕ} :
    0 < orderCount n m ↔ m ∈ possibleOrders n := by
  rw [orderCount, Fintype.card_pos_iff]
  constructor
  · rintro ⟨⟨σ, hσ⟩⟩
    exact mem_possibleOrders_iff.mpr ⟨σ, hσ⟩
  · rw [mem_possibleOrders_iff]
    rintro ⟨σ, hσ⟩
    exact ⟨⟨σ, hσ⟩⟩

@[simp]
theorem orderCount_eq_zero_iff_not_mem_possibleOrders {n m : ℕ} :
    orderCount n m = 0 ↔ m ∉ possibleOrders n := by
  constructor
  · intro hzero hmem
    have hpos := orderCount_pos_iff_mem_possibleOrders.mpr hmem
    omega
  · intro hnot
    exact Nat.eq_zero_of_not_pos fun hpos ↦
      hnot (orderCount_pos_iff_mem_possibleOrders.mp hpos)

theorem sum_possibleOrders_orderCount (n : ℕ) :
    ∑ m ∈ possibleOrders n, orderCount n m = n.factorial := by
  rw [possibleOrders]
  simpa only [orderCount_eq_card_filter, Finset.card_univ, card_perm_fin] using
    (Finset.card_eq_sum_card_image
      (fun σ : Equiv.Perm (Fin n) ↦ orderOf σ) Finset.univ).symm

theorem orderCount_le_factorial (n m : ℕ) :
    orderCount n m ≤ n.factorial := by
  rw [orderCount]
  simpa only [card_perm_fin] using
    (Fintype.card_subtype_le (fun σ : Equiv.Perm (Fin n) ↦ orderOf σ = m))

@[simp]
theorem orderCount_one (n : ℕ) : orderCount n 1 = 1 := by
  rw [orderCount_eq_card_filter]
  rw [show ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
      (fun σ ↦ orderOf σ = 1)) = {1} by
    ext σ
    simp]
  simp

theorem orderCount_le_maxOrderCount (n m : ℕ) :
    orderCount n m ≤ maxOrderCount n := by
  by_cases hm : m ∈ possibleOrders n
  · exact Finset.le_sup hm
  · rw [(orderCount_eq_zero_iff_not_mem_possibleOrders.mpr hm)]
    exact Nat.zero_le _

theorem exists_orderCount_eq_maxOrderCount (n : ℕ) :
    ∃ m ∈ possibleOrders n, orderCount n m = maxOrderCount n := by
  have h := Finset.sup_mem_of_nonempty (possibleOrders_nonempty n)
    (f := orderCount n)
  rcases h with ⟨m, hm, hvalue⟩
  exact ⟨m, hm, hvalue⟩

theorem maxOrderCount_pos (n : ℕ) : 0 < maxOrderCount n := by
  obtain ⟨m, hm, hmax⟩ := exists_orderCount_eq_maxOrderCount n
  rw [← hmax]
  exact orderCount_pos_iff_mem_possibleOrders.mpr hm

theorem maxOrderCount_le_factorial (n : ℕ) :
    maxOrderCount n ≤ n.factorial := by
  apply Finset.sup_le
  intro m _
  exact orderCount_le_factorial n m

theorem isMode_iff_orderCount_eq_maxOrderCount {n m : ℕ} :
    IsMode n m ↔ orderCount n m = maxOrderCount n := by
  constructor
  · intro hmode
    apply Nat.le_antisymm (orderCount_le_maxOrderCount n m)
    apply Finset.sup_le
    intro j hj
    exact hmode j
  · intro hmax j
    rw [hmax]
    exact orderCount_le_maxOrderCount n j

theorem exists_isMode (n : ℕ) : ∃ m, IsMode n m := by
  obtain ⟨m, _, hm⟩ := exists_orderCount_eq_maxOrderCount n
  exact ⟨m, isMode_iff_orderCount_eq_maxOrderCount.mpr hm⟩

theorem orderProbability_nonneg (n m : ℕ) : 0 ≤ orderProbability n m := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

@[simp]
theorem orderProbability_pos_iff {n m : ℕ} :
    0 < orderProbability n m ↔ m ∈ possibleOrders n := by
  rw [orderProbability, div_pos_iff]
  constructor
  · rintro (hpos | hneg)
    · exact orderCount_pos_iff_mem_possibleOrders.mp (by exact_mod_cast hpos.1)
    · exact False.elim (not_lt_of_ge
        (Nat.cast_nonneg (α := ℝ) (orderCount n m)) hneg.1)
  · intro hm
    exact Or.inl ⟨by exact_mod_cast orderCount_pos_iff_mem_possibleOrders.mpr hm,
      by positivity⟩

theorem orderProbability_le_one (n m : ℕ) : orderProbability n m ≤ 1 := by
  rw [orderProbability, div_le_one (by positivity)]
  exact_mod_cast orderCount_le_factorial n m

theorem maxOrderProbability_nonneg (n : ℕ) : 0 ≤ maxOrderProbability n := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem maxOrderProbability_le_one (n : ℕ) : maxOrderProbability n ≤ 1 := by
  rw [maxOrderProbability, div_le_one (by positivity)]
  exact_mod_cast maxOrderCount_le_factorial n

theorem orderProbability_le_maxOrderProbability (n m : ℕ) :
    orderProbability n m ≤ maxOrderProbability n := by
  unfold orderProbability maxOrderProbability
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast orderCount_le_maxOrderCount n m) (Nat.cast_nonneg _)

theorem sum_possibleOrders_orderProbability (n : ℕ) :
    ∑ m ∈ possibleOrders n, orderProbability n m = 1 := by
  simp_rw [orderProbability]
  rw [← Finset.sum_div, ← Nat.cast_sum,
    sum_possibleOrders_orderCount]
  exact div_self (by exact_mod_cast n.factorial_ne_zero)

theorem maxOrderProbability_eq_orderProbability_of_isMode {n m : ℕ}
    (hm : IsMode n m) :
    maxOrderProbability n = orderProbability n m := by
  rw [maxOrderProbability, orderProbability,
    ← isMode_iff_orderCount_eq_maxOrderCount.mp hm]

theorem isMode_iff_orderProbability_eq_maxOrderProbability {n m : ℕ} :
    IsMode n m ↔ orderProbability n m = maxOrderProbability n := by
  rw [isMode_iff_orderCount_eq_maxOrderCount]
  unfold orderProbability maxOrderProbability
  rw [div_left_inj' (by positivity : (n.factorial : ℝ) ≠ 0)]
  norm_cast

theorem factorial_eq_mul_pred_factorial {n : ℕ} (hn : 0 < n) :
    n.factorial = n * (n - 1).factorial := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp [Nat.factorial_succ]

/-- For `n > 0`, Beker's factorial count threshold is exactly the
probability threshold `1 / n`. -/
theorem factorial_le_orderCount_iff_inv_le_orderProbability
    {n m : ℕ} (hn : 0 < n) :
    (n - 1).factorial ≤ orderCount n m ↔
      (1 : ℝ) / n ≤ orderProbability n m := by
  rw [orderProbability, div_le_div_iff₀ (by exact_mod_cast hn)
    (by positivity : (0 : ℝ) < n.factorial)]
  simp only [one_mul]
  rw [factorial_eq_mul_pred_factorial hn, Nat.cast_mul]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · intro h
    have hR : ((n - 1).factorial : ℝ) ≤ orderCount n m := by
      exact_mod_cast h
    nlinarith
  · intro h
    have hR : ((n - 1).factorial : ℝ) ≤ orderCount n m := by
      nlinarith
    exact_mod_cast hR

theorem orderCount_ge_factorial_iff_orderProbability_ge_inv
    {n m : ℕ} (hn : 0 < n) :
    orderCount n m ≥ (n - 1).factorial ↔
      orderProbability n m ≥ (1 : ℝ) / n :=
  factorial_le_orderCount_iff_inv_le_orderProbability hn

/-! ## Beker's candidate and remainder parametrizations -/

/-- A positive integer satisfying Beker's least-common-multiple condition. -/
def BekerCandidate (n m : ℕ) : Prop :=
  0 < m ∧ Nat.lcmUpto (n - m) ∣ m

instance (n m : ℕ) : Decidable (BekerCandidate n m) := by
  unfold BekerCandidate
  infer_instance

/-- The admissible remainders `r < n` for which `lcm(1,…,r) ∣ n-r`. -/
def admissibleRemainders (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun r ↦ Nat.lcmUpto r ∣ n - r)

/-- The largest admissible remainder.  `Finset.sup` gives the harmless value
zero at `n = 0`; all substantive uses assume `0 < n`. -/
def largestAdmissibleRemainder (n : ℕ) : ℕ :=
  (admissibleRemainders n).sup id

theorem exists_bekerCandidate (n : ℕ) : ∃ m, BekerCandidate n m := by
  refine ⟨n + 1, ?_⟩
  simp [BekerCandidate, Nat.lcmUpto]

/-- The least positive integer satisfying Beker's condition. -/
def leastBekerCandidate (n : ℕ) : ℕ :=
  Nat.find (exists_bekerCandidate n)

theorem leastBekerCandidate_spec (n : ℕ) :
    BekerCandidate n (leastBekerCandidate n) := by
  exact Nat.find_spec (exists_bekerCandidate n)

theorem leastBekerCandidate_minimal {n m : ℕ} (hm : BekerCandidate n m) :
    leastBekerCandidate n ≤ m := by
  exact Nat.find_min' (exists_bekerCandidate n) hm

theorem isLeast_leastBekerCandidate (n : ℕ) :
    IsLeast {m : ℕ | BekerCandidate n m} (leastBekerCandidate n) := by
  exact ⟨leastBekerCandidate_spec n, fun _ hm ↦ leastBekerCandidate_minimal hm⟩

theorem bekerCandidate_self {n : ℕ} (hn : 0 < n) : BekerCandidate n n := by
  simp [BekerCandidate, hn, Nat.lcmUpto]

theorem leastBekerCandidate_le_self {n : ℕ} (hn : 0 < n) :
    leastBekerCandidate n ≤ n :=
  leastBekerCandidate_minimal (bekerCandidate_self hn)

@[simp]
theorem mem_admissibleRemainders_iff {n r : ℕ} :
    r ∈ admissibleRemainders n ↔
      r < n ∧ Nat.lcmUpto r ∣ n - r := by
  simp [admissibleRemainders]

theorem zero_mem_admissibleRemainders {n : ℕ} (hn : 0 < n) :
    0 ∈ admissibleRemainders n := by
  simp [mem_admissibleRemainders_iff, hn, Nat.lcmUpto]

theorem admissibleRemainders_nonempty {n : ℕ} (hn : 0 < n) :
    (admissibleRemainders n).Nonempty :=
  ⟨0, zero_mem_admissibleRemainders hn⟩

theorem bekerCandidate_iff_sub_mem_admissibleRemainders {n m : ℕ}
    (hmn : m ≤ n) :
    BekerCandidate n m ↔ n - m ∈ admissibleRemainders n := by
  constructor
  · rintro ⟨hmpos, hdvd⟩
    rw [mem_admissibleRemainders_iff]
    refine ⟨by omega, ?_⟩
    simpa [Nat.sub_sub_self hmn] using hdvd
  · rw [mem_admissibleRemainders_iff]
    rintro ⟨hlt, hdvd⟩
    refine ⟨by omega, ?_⟩
    simpa [Nat.sub_sub_self hmn] using hdvd

theorem bekerCandidate_compl_iff_mem_admissibleRemainders {n r : ℕ}
    (hrn : r < n) :
    BekerCandidate n (n - r) ↔ r ∈ admissibleRemainders n := by
  rw [bekerCandidate_iff_sub_mem_admissibleRemainders (Nat.sub_le n r)]
  simp [Nat.sub_sub_self (Nat.le_of_lt hrn), hrn]

/-- Complementation in `n` reverses the order, carrying the least Beker
candidate to the greatest admissible remainder. -/
theorem isLeast_bekerCandidate_compl_iff_isGreatest_admissibleRemainder
    {n r : ℕ} (_hn : 0 < n) :
    IsLeast {m : ℕ | BekerCandidate n m} (n - r) ↔
      IsGreatest (↑(admissibleRemainders n) : Set ℕ) r := by
  constructor
  · intro hleast
    have hrn : r < n := by
      have hpos : 0 < n - r := hleast.1.1
      omega
    have hrmem : r ∈ admissibleRemainders n :=
      (bekerCandidate_compl_iff_mem_admissibleRemainders hrn).mp hleast.1
    refine ⟨hrmem, ?_⟩
    intro s hs
    have hsn : s < n := (mem_admissibleRemainders_iff.mp hs).1
    have hcandidate : BekerCandidate n (n - s) :=
      (bekerCandidate_compl_iff_mem_admissibleRemainders hsn).mpr hs
    have hle := hleast.2 hcandidate
    omega
  · intro hgreat
    have hrmem : r ∈ admissibleRemainders n := hgreat.1
    have hrn : r < n := (mem_admissibleRemainders_iff.mp hrmem).1
    have hcandidate : BekerCandidate n (n - r) :=
      (bekerCandidate_compl_iff_mem_admissibleRemainders hrn).mpr hrmem
    refine ⟨hcandidate, ?_⟩
    intro m hm
    by_cases hmn : m ≤ n
    · have hrem : n - m ∈ admissibleRemainders n :=
        (bekerCandidate_iff_sub_mem_admissibleRemainders hmn).mp hm
      have hle := hgreat.2 hrem
      omega
    · omega

theorem largestAdmissibleRemainder_mem {n : ℕ} (hn : 0 < n) :
    largestAdmissibleRemainder n ∈ admissibleRemainders n := by
  have h := Finset.sup_mem_of_nonempty (admissibleRemainders_nonempty hn)
    (f := id)
  rcases h with ⟨r, hr, hvalue⟩
  unfold largestAdmissibleRemainder
  rw [← hvalue]
  exact hr

theorem admissibleRemainder_le_largest {n r : ℕ}
    (hr : r ∈ admissibleRemainders n) :
    r ≤ largestAdmissibleRemainder n := by
  exact Finset.le_sup (f := id) hr

theorem largestAdmissibleRemainder_isGreatest {n : ℕ} (hn : 0 < n) :
    IsGreatest (↑(admissibleRemainders n) : Set ℕ)
      (largestAdmissibleRemainder n) := by
  exact ⟨largestAdmissibleRemainder_mem hn,
    fun _ hr ↦ admissibleRemainder_le_largest hr⟩

theorem largestAdmissibleRemainder_lt {n : ℕ} (hn : 0 < n) :
    largestAdmissibleRemainder n < n :=
  (mem_admissibleRemainders_iff.mp
    (largestAdmissibleRemainder_mem hn)).1

theorem leastBekerCandidate_eq_sub_largestAdmissibleRemainder
    {n : ℕ} (hn : 0 < n) :
    leastBekerCandidate n = n - largestAdmissibleRemainder n := by
  have hleast : IsLeast {m : ℕ | BekerCandidate n m}
      (n - largestAdmissibleRemainder n) :=
    (isLeast_bekerCandidate_compl_iff_isGreatest_admissibleRemainder hn).mpr
      (largestAdmissibleRemainder_isGreatest hn)
  exact (isLeast_leastBekerCandidate n).unique hleast

theorem isLeast_bekerCandidate_iff_eq_leastBekerCandidate {n m : ℕ} :
    IsLeast {k : ℕ | BekerCandidate n k} m ↔
      m = leastBekerCandidate n := by
  constructor
  · intro hm
    exact hm.unique (isLeast_leastBekerCandidate n)
  · rintro rfl
    exact isLeast_leastBekerCandidate n

theorem isLeast_bekerCandidate_iff_eq_sub_largestAdmissibleRemainder
    {n m : ℕ} (hn : 0 < n) :
    IsLeast {k : ℕ | BekerCandidate n k} m ↔
      m = n - largestAdmissibleRemainder n := by
  rw [isLeast_bekerCandidate_iff_eq_leastBekerCandidate,
    leastBekerCandidate_eq_sub_largestAdmissibleRemainder hn]

end Erdos1161
