import Mathlib

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Elementary-symmetric bounds for truncated Euler products
-/

open Nat Finset

namespace Erdos394

/-- The `j`th elementary symmetric sum of the nonnegative weights `x` on `s`. -/
noncomputable def elementarySum (s : Finset α) (x : α → ℝ) (j : ℕ) : ℝ :=
  ∑ t ∈ s.powersetCard j, ∏ i ∈ t, x i

@[simp]
theorem elementarySum_zero (s : Finset α) (x : α → ℝ) :
    elementarySum s x 0 = 1 := by
  classical
  simp [elementarySum]

/-- The standard insertion recurrence for elementary symmetric sums. -/
theorem elementarySum_insert_succ [DecidableEq α] {s : Finset α} {a : α}
    (ha : a ∉ s) (x : α → ℝ) (j : ℕ) :
    elementarySum (insert a s) x (j + 1) =
      elementarySum s x (j + 1) + x a * elementarySum s x j := by
  unfold elementarySum
  rw [Finset.powersetCard_succ_insert ha]
  have hd : Disjoint (s.powersetCard (j + 1))
      ((s.powersetCard j).image (insert a)) := by
    rw [Finset.disjoint_left]
    intro t ht htimg
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp htimg
    have hsub : insert a u ⊆ s := (Finset.mem_powersetCard.mp ht).1
    exact ha (hsub (Finset.mem_insert_self a u))
  rw [Finset.sum_union hd]
  have hinj : Set.InjOn (insert a)
      (↑(s.powersetCard j) : Set (Finset α)) := by
    intro u hu v hv huv
    have hua : a ∉ u := by
      intro hau
      exact ha ((Finset.mem_powersetCard.mp hu).1 hau)
    have hva : a ∉ v := by
      intro hav
      exact ha ((Finset.mem_powersetCard.mp hv).1 hav)
    calc
      u = (insert a u).erase a := (Finset.erase_insert hua).symm
      _ = (insert a v).erase a := by rw [huv]
      _ = v := Finset.erase_insert hva
  rw [Finset.sum_image hinj, mul_sum]
  apply congrArg (elementarySum s x (j + 1) + ·)
  apply Finset.sum_congr rfl
  intro u hu
  have hua : a ∉ u := by
    intro hau
    exact ha ((Finset.mem_powersetCard.mp hu).1 hau)
  rw [Finset.prod_insert hua]

/-- Elementary symmetric sums of nonnegative weights are nonnegative. -/
theorem elementarySum_nonneg {s : Finset α} {x : α → ℝ}
    (hx : ∀ i ∈ s, 0 ≤ x i) (j : ℕ) : 0 ≤ elementarySum s x j := by
  classical
  unfold elementarySum
  apply Finset.sum_nonneg
  intro t ht
  apply Finset.prod_nonneg
  intro i hi
  exact hx i ((Finset.mem_powersetCard.mp ht).1 hi)

/-- Consecutive elementary symmetric sums satisfy
`(j+1)e_{j+1} ≤ (Σx_i)e_j` for nonnegative weights. -/
theorem succ_mul_elementarySum_le_sum_mul (s : Finset α) (x : α → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (j : ℕ) :
    (j + 1 : ℝ) * elementarySum s x (j + 1) ≤
      (∑ i ∈ s, x i) * elementarySum s x j := by
  classical
  induction s using Finset.induction_on generalizing j with
  | empty =>
      have hempty : (∅ : Finset α).powersetCard (j + 1) = ∅ :=
        Finset.powersetCard_eq_empty.mpr (by simp)
      simp [elementarySum, hempty]
  | @insert a s ha ih =>
      have hxa : 0 ≤ x a := hx a (Finset.mem_insert_self a s)
      have hxs : ∀ i ∈ s, 0 ≤ x i := by
        intro i hi
        exact hx i (Finset.mem_insert_of_mem hi)
      cases j with
      | zero =>
          have hih := ih hxs 0
          rw [elementarySum_insert_succ ha x 0, elementarySum_zero,
            Finset.sum_insert ha, elementarySum_zero]
          norm_num at hih ⊢
          linarith
      | succ k =>
          have hih1 := ih hxs (k + 1)
          have hih0 := ih hxs k
          have hmul := mul_le_mul_of_nonneg_left hih0 hxa
          have hC : 0 ≤ elementarySum s x k := elementarySum_nonneg hxs k
          rw [elementarySum_insert_succ ha x (k + 1),
            elementarySum_insert_succ ha x k, Finset.sum_insert ha]
          push_cast at hih1 hih0 hmul ⊢
          nlinarith [mul_nonneg (mul_nonneg hxa hxa) hC]

/-- The standard factorial bound `j! e_j ≤ (Σx_i)^j`. -/
theorem factorial_mul_elementarySum_le_pow_sum (s : Finset α) (x : α → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (j : ℕ) :
    (j.factorial : ℝ) * elementarySum s x j ≤ (∑ i ∈ s, x i) ^ j := by
  let Λ : ℝ := ∑ i ∈ s, x i
  have hΛ : 0 ≤ Λ := by
    dsimp [Λ]
    exact Finset.sum_nonneg fun i hi ↦ hx i hi
  induction j with
  | zero => simp [Λ]
  | succ j ih =>
      have hrec := succ_mul_elementarySum_le_sum_mul s x hx j
      have hfac : 0 ≤ (j.factorial : ℝ) := by positivity
      calc
        ((j + 1).factorial : ℝ) * elementarySum s x (j + 1) =
            (j.factorial : ℝ) *
              ((j + 1 : ℝ) * elementarySum s x (j + 1)) := by
                rw [Nat.factorial_succ]
                push_cast
                ring
        _ ≤ (j.factorial : ℝ) * (Λ * elementarySum s x j) := by
              apply mul_le_mul_of_nonneg_left
              simpa [Λ] using hrec
              exact hfac
        _ = Λ * ((j.factorial : ℝ) * elementarySum s x j) := by ring
        _ ≤ Λ * Λ ^ j := mul_le_mul_of_nonneg_left ih hΛ
        _ = Λ ^ (j + 1) := by ring

/-- Alternating elementary-symmetric sum truncated after degree `R`. -/
noncomputable def alternatingPartial (s : Finset α) (x : α → ℝ) (R : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (R + 1), (-1 : ℝ) ^ j * elementarySum s x j

@[simp]
theorem alternatingPartial_zero (s : Finset α) (x : α → ℝ) :
    alternatingPartial s x 0 = 1 := by
  simp [alternatingPartial]

/-- Add the final degree to an alternating partial sum. -/
theorem alternatingPartial_succ (s : Finset α) (x : α → ℝ) (R : ℕ) :
    alternatingPartial s x (R + 1) = alternatingPartial s x R +
      (-1 : ℝ) ^ (R + 1) * elementarySum s x (R + 1) := by
  unfold alternatingPartial
  rw [Finset.sum_range_succ]

/-- Inserting one variable gives the usual recurrence for truncated products. -/
theorem alternatingPartial_insert_succ [DecidableEq α] {s : Finset α} {a : α}
    (ha : a ∉ s) (x : α → ℝ) (R : ℕ) :
    alternatingPartial (insert a s) x (R + 1) =
      alternatingPartial s x (R + 1) - x a * alternatingPartial s x R := by
  induction R with
  | zero =>
      rw [alternatingPartial_succ, alternatingPartial_succ,
        alternatingPartial_zero, alternatingPartial_zero,
        elementarySum_insert_succ ha x 0, elementarySum_zero]
      norm_num
      ring
  | succ R ih =>
      rw [alternatingPartial_succ (insert a s) x (R + 1),
        alternatingPartial_succ s x (R + 1), ih,
        elementarySum_insert_succ ha x (R + 1),
        alternatingPartial_succ s x R]
      rw [pow_succ]
      ring

/-- The full local Euler product. -/
noncomputable def localEulerProduct (s : Finset α) (x : α → ℝ) : ℝ :=
  ∏ i ∈ s, (1 - x i)

/-- An even successor has odd predecessor. -/
theorem odd_of_even_succ {k : ℕ} (h : Even (k + 1)) : Odd k := by
  rcases h with ⟨a, ha⟩
  refine ⟨a - 1, ?_⟩
  omega

/-- An odd successor has even predecessor. -/
theorem even_of_odd_succ {k : ℕ} (h : Odd (k + 1)) : Even k := by
  rcases h with ⟨a, ha⟩
  exact ⟨a, by omega⟩

/-- Every alternating partial sum for the empty family equals one. -/
theorem alternatingPartial_empty (x : α → ℝ) (R : ℕ) :
    alternatingPartial (∅ : Finset α) x R = 1 := by
  induction R with
  | zero => simp
  | succ R ih =>
      rw [alternatingPartial_succ, ih]
      have he : elementarySum (∅ : Finset α) x (R + 1) = 0 := by
        unfold elementarySum
        rw [Finset.powersetCard_eq_empty.mpr (by simp)]
        simp
      rw [he]
      ring

/-- Weighted Bonferroni inequalities: even truncations lie above the full
product and odd truncations lie below it. -/
theorem alternatingPartial_bonferroni (s : Finset α) (x : α → ℝ)
    (hx0 : ∀ i ∈ s, 0 ≤ x i) (hx1 : ∀ i ∈ s, x i ≤ 1) (R : ℕ) :
    (Even R → localEulerProduct s x ≤ alternatingPartial s x R) ∧
      (Odd R → alternatingPartial s x R ≤ localEulerProduct s x) := by
  classical
  induction s using Finset.induction_on generalizing R with
  | empty =>
      rw [alternatingPartial_empty, localEulerProduct]
      simp
  | @insert a s ha ih =>
      have hxa0 : 0 ≤ x a := hx0 a (Finset.mem_insert_self a s)
      have hxa1 : x a ≤ 1 := hx1 a (Finset.mem_insert_self a s)
      have hxs0 : ∀ i ∈ s, 0 ≤ x i := by
        intro i hi
        exact hx0 i (Finset.mem_insert_of_mem hi)
      have hxs1 : ∀ i ∈ s, x i ≤ 1 := by
        intro i hi
        exact hx1 i (Finset.mem_insert_of_mem hi)
      cases R with
      | zero =>
          constructor
          · intro _
            rw [alternatingPartial_zero, localEulerProduct,
              Finset.prod_insert ha]
            have hV0 : 0 ≤ localEulerProduct s x := by
              unfold localEulerProduct
              apply Finset.prod_nonneg
              intro i hi
              linarith [hxs1 i hi]
            have hV1 : localEulerProduct s x ≤ 1 := by
              unfold localEulerProduct
              apply Finset.prod_le_one
              · intro i hi
                linarith [hxs1 i hi]
              · intro i hi
                linarith [hxs0 i hi]
            change (1 - x a) * localEulerProduct s x ≤ 1
            nlinarith [mul_nonneg (sub_nonneg.mpr hxa1) hV0,
              mul_nonneg hxa0 hV0]
          · intro hodd
            exfalso
            rcases hodd with ⟨k, hk⟩
            omega
      | succ k =>
          have ihR := ih hxs0 hxs1 (k + 1)
          have ihK := ih hxs0 hxs1 k
          rw [alternatingPartial_insert_succ ha x k, localEulerProduct,
            Finset.prod_insert ha]
          change
            (Even (k + 1) →
              (1 - x a) * localEulerProduct s x ≤
                alternatingPartial s x (k + 1) - x a * alternatingPartial s x k) ∧
            (Odd (k + 1) →
              alternatingPartial s x (k + 1) - x a * alternatingPartial s x k ≤
                (1 - x a) * localEulerProduct s x)
          constructor
          · intro heven
            have hodd : Odd k := odd_of_even_succ heven
            have hupper := ihR.1 heven
            have hlower := ihK.2 hodd
            have hp : 0 ≤ x a *
                (localEulerProduct s x - alternatingPartial s x k) :=
              mul_nonneg hxa0 (sub_nonneg.mpr hlower)
            nlinarith
          · intro hodd
            have heven : Even k := even_of_odd_succ hodd
            have hlower := ihR.2 hodd
            have hupper := ihK.1 heven
            have hp : 0 ≤ x a *
                (alternatingPartial s x k - localEulerProduct s x) :=
              mul_nonneg hxa0 (sub_nonneg.mpr hupper)
            nlinarith

/-- An even partial sum exceeds the full product by at most its first omitted
symmetric term. -/
theorem alternatingPartial_le_product_add_next (s : Finset α) (x : α → ℝ)
    (hx0 : ∀ i ∈ s, 0 ≤ x i) (hx1 : ∀ i ∈ s, x i ≤ 1)
    (R : ℕ) (hR : Even R) :
    alternatingPartial s x R ≤
      localEulerProduct s x + elementarySum s x (R + 1) := by
  have hodd : Odd (R + 1) := hR.add_one
  have hbonf := (alternatingPartial_bonferroni s x hx0 hx1 (R + 1)).2 hodd
  rw [alternatingPartial_succ, hodd.neg_one_pow] at hbonf
  linarith

/-- Quantitative alternating-tail estimate
`B_R ≤ V + (Σx)^(R+1)/(R+1)!`. -/
theorem alternatingPartial_le_product_add_pow_div_factorial
    (s : Finset α) (x : α → ℝ)
    (hx0 : ∀ i ∈ s, 0 ≤ x i) (hx1 : ∀ i ∈ s, x i ≤ 1)
    (R : ℕ) (hR : Even R) :
    alternatingPartial s x R ≤ localEulerProduct s x +
      (∑ i ∈ s, x i) ^ (R + 1) / ((R + 1).factorial : ℝ) := by
  have hfirst := alternatingPartial_le_product_add_next s x hx0 hx1 R hR
  have hfac := factorial_mul_elementarySum_le_pow_sum s x hx0 (R + 1)
  have hfacpos : 0 < ((R + 1).factorial : ℝ) := by positivity
  have he : elementarySum s x (R + 1) ≤
      (∑ i ∈ s, x i) ^ (R + 1) / ((R + 1).factorial : ℝ) := by
    apply (le_div_iff₀ hfacpos).2
    nlinarith
  linarith

/-- If the factorial tail is no larger than the full product, the even
truncation is at most twice that product. -/
theorem alternatingPartial_le_two_mul_product_of_tail_le
    (s : Finset α) (x : α → ℝ)
    (hx0 : ∀ i ∈ s, 0 ≤ x i) (hx1 : ∀ i ∈ s, x i ≤ 1)
    (R : ℕ) (hR : Even R)
    (htail : (∑ i ∈ s, x i) ^ (R + 1) / ((R + 1).factorial : ℝ) ≤
      localEulerProduct s x) :
    alternatingPartial s x R ≤ 2 * localEulerProduct s x := by
  have h := alternatingPartial_le_product_add_pow_div_factorial
    s x hx0 hx1 R hR
  linarith

end Erdos394
