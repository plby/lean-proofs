import Mathlib

/-!
# The Erdős–Hooley Delta function

The arithmetic foundation for the log-log improvement of Erdős 587.
`hooleyDelta n` is the largest number of positive divisors of `n` in
an interval `(exp u, exp (u + 1)]`. Its definition uses a bounded
natural-number supremum, and the supremum is attained.

No mean-value estimate is assumed in this file.
-/

open scoped BigOperators

namespace Erdos587

/-- Positive divisors in one logarithmic interval. -/
noncomputable def deltaDivisors (n : ℕ) (u : ℝ) : Finset ℕ := by
  classical
  exact n.divisors.filter fun d => Real.exp u < d ∧ (d : ℝ) ≤ Real.exp (u + 1)

lemma mem_deltaDivisors {n d : ℕ} {u : ℝ} :
    d ∈ deltaDivisors n u ↔
      d ∣ n ∧ n ≠ 0 ∧ Real.exp u < d ∧ (d : ℝ) ≤ Real.exp (u + 1) := by
  classical
  simp only [deltaDivisors, Finset.mem_filter, Nat.mem_divisors, and_assoc]

lemma deltaDivisors_card_le (n : ℕ) (u : ℝ) :
    (deltaDivisors n u).card ≤ n.divisors.card := by
  classical
  exact Finset.card_filter_le _ _

lemma deltaDivisors_card_range_bddAbove (n : ℕ) :
    BddAbove (Set.range fun u : ℝ => (deltaDivisors n u).card) := by
  refine ⟨n.divisors.card, ?_⟩
  rintro k ⟨u, rfl⟩
  exact deltaDivisors_card_le n u

lemma deltaDivisors_card_range_finite (n : ℕ) :
    (Set.range fun u : ℝ => (deltaDivisors n u).card).Finite := by
  apply (Set.finite_Iic n.divisors.card).subset
  rintro k ⟨u, rfl⟩
  exact deltaDivisors_card_le n u

/-- The Erdős–Hooley concentration function. It is zero at zero. -/
noncomputable def hooleyDelta (n : ℕ) : ℕ :=
  sSup (Set.range fun u : ℝ => (deltaDivisors n u).card)

lemma card_deltaDivisors_le_hooleyDelta (n : ℕ) (u : ℝ) :
    (deltaDivisors n u).card ≤ hooleyDelta n :=
  le_csSup (deltaDivisors_card_range_bddAbove n) ⟨u, rfl⟩

lemma hooleyDelta_le_card_divisors (n : ℕ) : hooleyDelta n ≤ n.divisors.card := by
  apply csSup_le (Set.range_nonempty _)
  rintro k ⟨u, rfl⟩
  exact deltaDivisors_card_le n u

lemma exists_deltaDivisors_card_eq (n : ℕ) :
    ∃ u : ℝ, (deltaDivisors n u).card = hooleyDelta n := by
  exact (Set.range_nonempty (fun u : ℝ => (deltaDivisors n u).card)).csSup_mem
    (deltaDivisors_card_range_finite n)

@[simp] lemma hooleyDelta_zero : hooleyDelta 0 = 0 := by
  have h := hooleyDelta_le_card_divisors 0
  simpa using h

lemma one_le_hooleyDelta {n : ℕ} (hn : n ≠ 0) : 1 ≤ hooleyDelta n := by
  have hmem : 1 ∈ deltaDivisors n (-1) := by
    apply mem_deltaDivisors.mpr
    refine ⟨one_dvd n, hn, ?_, ?_⟩
    · have h := Real.exp_lt_exp.mpr (show (-1 : ℝ) < 0 by norm_num)
      rw [Real.exp_zero] at h
      simpa only [Nat.cast_one] using h
    · norm_num
  exact (Finset.one_le_card.mpr ⟨1, hmem⟩).trans
    (card_deltaDivisors_le_hooleyDelta n (-1))

@[simp] lemma hooleyDelta_one : hooleyDelta 1 = 1 := by
  apply Nat.le_antisymm
  · simpa using hooleyDelta_le_card_divisors 1
  · exact one_le_hooleyDelta (by norm_num)

lemma deltaDivisors_subset_of_dvd {m n : ℕ} (hmn : m ∣ n) (hn : n ≠ 0)
    (u : ℝ) : deltaDivisors m u ⊆ deltaDivisors n u := by
  intro d hd
  obtain ⟨hdm, _, hlow, hupp⟩ := mem_deltaDivisors.mp hd
  exact mem_deltaDivisors.mpr ⟨hdm.trans hmn, hn, hlow, hupp⟩

lemma hooleyDelta_le_of_dvd {m n : ℕ} (hmn : m ∣ n) (hn : n ≠ 0) :
    hooleyDelta m ≤ hooleyDelta n := by
  obtain ⟨u, hu⟩ := exists_deltaDivisors_card_eq m
  rw [← hu]
  exact (Finset.card_le_card (deltaDivisors_subset_of_dvd hmn hn u)).trans
    (card_deltaDivisors_le_hooleyDelta n u)

/-- Divisors in a ratio-two interval are counted by one Delta window. -/
lemma card_dyadic_divisors_le_hooleyDelta (n : ℕ) {R : ℝ} (hR : 0 < R) :
    (n.divisors.filter fun d : ℕ => R < (d : ℝ) ∧ (d : ℝ) ≤ 2 * R).card ≤
      hooleyDelta n := by
  classical
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    linarith only [Real.add_one_le_exp (1 : ℝ)]
  apply le_trans (Finset.card_le_card (t := deltaDivisors n (Real.log R)) ?_)
    (card_deltaDivisors_le_hooleyDelta n (Real.log R))
  intro d hd
  obtain ⟨hddiv, hdlow, hdupp⟩ := Finset.mem_filter.mp hd
  obtain ⟨hdn, hn⟩ := Nat.mem_divisors.mp hddiv
  apply mem_deltaDivisors.mpr
  refine ⟨hdn, hn, ?_, ?_⟩
  · simpa only [Real.exp_log hR] using hdlow
  · rw [Real.exp_add, Real.exp_log hR]
    exact hdupp.trans (by nlinarith [mul_nonneg hR.le (sub_nonneg.mpr he)])

/-- Count an arbitrary injectively encoded family of divisors in a dyadic
interval. The nonzero condition on the encoded integer is essential. -/
lemma card_le_hooleyDelta_of_divisor_encoding {α : Type*}
    (S : Finset α) (f : α → ℕ) {n : ℕ} (hn : n ≠ 0)
    {R : ℝ} (hR : 0 < R)
    (hdiv : ∀ x ∈ S, f x ∣ n)
    (hlow : ∀ x ∈ S, R < f x)
    (hupp : ∀ x ∈ S, (f x : ℝ) ≤ 2 * R)
    (hinj : Set.InjOn f (S : Set α)) : S.card ≤ hooleyDelta n := by
  classical
  apply le_trans (Finset.card_le_card_of_injOn f
    (t := n.divisors.filter fun d : ℕ => R < (d : ℝ) ∧ (d : ℝ) ≤ 2 * R) ?_ hinj)
    (card_dyadic_divisors_le_hooleyDelta n hR)
  intro x hx
  exact Finset.mem_filter.mpr
    ⟨Nat.mem_divisors.mpr ⟨hdiv x hx, hn⟩, hlow x hx, hupp x hx⟩

/-- Multiplication by a positive factor translates a logarithmic window. -/
lemma exp_window_mul_iff {x y u : ℝ} (hx : 0 < x) :
    (Real.exp u < x * y ∧ x * y ≤ Real.exp (u + 1)) ↔
      (Real.exp (u - Real.log x) < y ∧
        y ≤ Real.exp (u - Real.log x + 1)) := by
  have hshift : u - Real.log x + 1 = (u + 1) - Real.log x := by ring
  rw [hshift, Real.exp_sub, Real.exp_sub, Real.exp_log hx]
  rw [div_lt_iff₀ hx, le_div_iff₀ hx]
  rw [mul_comm y x]

/-- All divisors of a product can be covered by translated divisor windows
of the second factor. Coprimality is not needed. -/
lemma deltaDivisors_mul_subset (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (u : ℝ) :
    deltaDivisors (a * b) u ⊆
      a.divisors.biUnion (fun e =>
        (deltaDivisors b (u - Real.log e)).image (fun f => e * f)) := by
  classical
  intro d hd
  obtain ⟨hdab, _, hdlow, hdupp⟩ := mem_deltaDivisors.mp hd
  obtain ⟨e, f, hea, hfb, hef⟩ := exists_dvd_and_dvd_of_dvd_mul hdab
  have hepos : 0 < e := Nat.pos_of_dvd_of_pos hea (Nat.pos_of_ne_zero ha)
  have heR : (0 : ℝ) < e := by exact_mod_cast hepos
  have hwindow :
      Real.exp (u - Real.log e) < (f : ℝ) ∧
        (f : ℝ) ≤ Real.exp (u - Real.log e + 1) := by
    apply (exp_window_mul_iff heR).mp
    simpa only [hef, Nat.cast_mul] using And.intro hdlow hdupp
  apply Finset.mem_biUnion.mpr
  refine ⟨e, Nat.mem_divisors.mpr ⟨hea, ha⟩, ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨f, mem_deltaDivisors.mpr ⟨hfb, hb, hwindow.1, hwindow.2⟩, hef.symm⟩

/-- The divisor-multiplier bound used in both the mean-value theorem and
the nonprimitive arithmetic-progression reduction. -/
theorem hooleyDelta_mul_le (a b : ℕ) :
    hooleyDelta (a * b) ≤ a.divisors.card * hooleyDelta b := by
  classical
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  obtain ⟨u, hu⟩ := exists_deltaDivisors_card_eq (a * b)
  rw [← hu]
  calc
    (deltaDivisors (a * b) u).card ≤
        (a.divisors.biUnion (fun e =>
          (deltaDivisors b (u - Real.log e)).image (fun f => e * f))).card :=
      Finset.card_le_card (deltaDivisors_mul_subset a b ha hb u)
    _ ≤ ∑ e ∈ a.divisors,
        ((deltaDivisors b (u - Real.log e)).image (fun f => e * f)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ a.divisors, hooleyDelta b := by
      apply Finset.sum_le_sum
      intro e he
      exact (Finset.card_image_le).trans
        (card_deltaDivisors_le_hooleyDelta b (u - Real.log e))
    _ = a.divisors.card * hooleyDelta b := by simp

end Erdos587
